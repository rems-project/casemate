#![cfg(feature = "alloc")]

//! A very simple `no_std` allocator
//!
//! [`HeapAllocator`] is a simple allocator

use crate::shim::alloc::Layout;
use crate::shim::mem;
use crate::shim::ptr;

mod impls;

pub const MAX_ORDER: usize = 20;
pub const MIN_ORDER: usize = 6;

/// Internal allocator
///
/// Based on the [ghost_allocator] written by David Kaloper Meršinjak
///
/// Keeps an array of free lists, each one containing blocks with capacity of successive powers of 2.
/// If a request can not be satisfied from the corresponding list `i`,
/// take a chunk from the smallest non-empty list `j > i`
/// and split it into two to populate `j - 1`; repeat until `i` is non-empty.
/// Freed memory is **not** merged.
/// Smallest list contains chunks with size 2^MIN_ORDER, largest with size 2^MAX_ORDER.
///
/// [ghost_allocator]: https://github.com/rems-project/linux/blob/31d53dc446cbbec2702e522038cb8d14ab929ae4/arch/arm64/kvm/hyp/ghost_alloc.c
///
#[derive(Clone, Debug)]
pub struct HeapAllocator {
    free_lists: [*mut FreeChunk; MAX_ORDER - MIN_ORDER + 1],
}

/// Allocated area for the allocator
///
/// Not all of the arena is free.
#[derive(Clone, Debug)]
pub struct Arena {
    pub start: *mut u8,
    pub size: usize,
}

/// The header for an entry which has been allocated away
///
/// The header stores information
/// The data must be aligned to the minimum requirement.
/// The header needs to know the size
/// The size and so on are computable directly from that.
///
/// The header is padded into the region enough
///
/// ## Anatomy of a chunk
///
/// Every chunk starts with a u8 with the padding up to the header proper.
/// Each
///
/// ```
/// +---------------------+-- --- --+----------+---------- --- -----+
/// |    header: Chunk    | padding | npad: u8 |   data    ...      |
/// +---------------------+-- --- --+----------+---------- --- -----+
/// ^                                          ^
/// |                                          |
/// +- start of chunk                          |
///    : *raw Chunk                            |
///                                            +- aligned alloc ptr
///                                               : *mut u8
/// ```
///
#[repr(C)]
struct Chunk {
    /// The order of the chunk (i.e. the size)
    order: u8,

    /// The size in bytes of `padding`
    ///
    /// Note: this means that `size_of::<Chunk>() + padding` only goes up to `npad`, not the data
    padding: u8,
}

/// A chunk in a freelist waiting to be allocated
///
/// # Anatomy of a FreeChunk
///
/// ```
/// +-------------------------+----------------- --- --------------+
/// |    header: FreeChunk    |                  ...               |
/// +-------------------------+----------------- --- --------------+
/// ^
/// |
/// +- start of chunk
///    : *raw FreeChunk
/// ```
///
#[repr(C)]
struct FreeChunk {
    /// The order of the freelist this belongs to
    order: u8,

    /// The pointer to the next header
    ///
    /// Is null if this is the last in the list
    next_chunk: *mut FreeChunk,

    /// The pointer to the previous header
    ///
    /// Is null if the first element in the list
    prev_chunk: *mut FreeChunk,
}

/// A chunk which is dangling, not in a freelist nor allocated away.
///
/// # Anatomy of a BareChunk
///
/// ```
/// +-------------------------+----------------- --- --------------+
/// |    header: BareChunk    |                  ...               |
/// +-------------------------+----------------- --- --------------+
/// ^
/// |
/// +- start of chunk
///    : *raw BareChunk
/// ```
///
#[repr(C)]
struct BareChunk {
    order: u8,
}

unsafe impl Send for HeapAllocator {}
unsafe impl Sync for HeapAllocator {}

/// Compute the padding required for an allocation
///
/// If the amount of padding required is more than 255 bytes,
/// or if the padding is more than would fit in the order,
/// returns error.
fn try_compute_required_padding(order: u8, align: usize) -> Result<u8, ()> {
    let total = 1usize << order;
    let header_size = mem::size_of::<Chunk>();
    let npad_size = mem::size_of::<u8>();

    // assuming zero padding, the smallest header would be exactly the header + `npad`
    let smallest = header_size + npad_size;

    // align is always a power of 2
    let mask = align - 1;

    // how far above the previous alignment boundry we are
    let offset_from_previous_alignment = smallest & mask;

    // we must always _add_ bytes of padding to make the alignment
    // so we must add bytes up to the next align
    let required_padding = align - offset_from_previous_alignment;

    if required_padding > 255 {
        Err(())
    } else if smallest + required_padding > total {
        Err(())
    } else {
        Ok(required_padding as u8)
    }
}

/// Calculate the amount of space available for the `data` part of a Chunk
///
fn usable_space_for_data(order: u8, align: usize) -> Option<usize> {
    let total = 1usize << order;
    let header_size = mem::size_of::<Chunk>();
    let npad_size = mem::size_of::<u8>();
    let padding = try_compute_required_padding(order, align);
    match padding {
        Ok(pad) => Some(total - header_size - (pad as usize) - npad_size),
        Err(()) => None,
    }
}

fn order_of(size: usize, align: usize) -> Option<u8> {
    for order in MIN_ORDER..=MAX_ORDER {
        let order = order as u8;
        let usable_space = usable_space_for_data(order, align);
        match usable_space {
            Some(space) if space >= size => return Some(order as u8),
            _ => (),
        }
    }

    None
}

impl HeapAllocator {
    pub const fn new() -> Self {
        Self {
            free_lists: [ptr::null_mut(); MAX_ORDER - MIN_ORDER + 1],
        }
    }

    pub fn init(&mut self, start: *mut u8, size: usize) {
        let arena = Arena { start, size };
        unsafe {
            self.populate_freelists(arena);
        }
    }

    pub fn alloc(&mut self, layout: Layout) -> *mut u8 {
        let size = layout.size();
        let align = layout.align();
        let order = order_of(size, align).expect("allocation request too large");
        unsafe {
            let freechunk: Option<*mut BareChunk> = self.get_free_chunk(order);
            match freechunk {
                None => {
                    // Return a nullptr on OOM
                    //
                    // According to [trait.GlobalAlloc.alloc]:
                    // > Implementations are encouraged to return null on memory exhaustion rather than aborting.
                    //
                    // [trait.GlobalAlloc.alloc]: https://doc.rust-lang.org/alloc/alloc/trait.GlobalAlloc.html#tymethod.alloc
                    ptr::null_mut()
                }
                Some(freechunk) => {
                    let chunkptr = Chunk::raw_new(freechunk, align);
                    let chunk = chunkptr.as_mut().unwrap();
                    chunk.npadptr().write(chunk.padding);
                    chunk.dataptr()
                }
            }
        }
    }

    pub fn dealloc(&mut self, ptr: *mut u8, _layout: Layout) {
        unsafe {
            let chunkptr = Chunk::raw_from_alloc(ptr);
            let chunk = chunkptr.as_mut().unwrap();
            let bareptr = chunk.downgrade();
            self.push_freelist(bareptr);
        }
    }
}
