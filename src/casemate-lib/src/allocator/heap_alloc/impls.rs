#![cfg(feature = "alloc")]

use crate::shim::mem;
use crate::shim::ptr;

use super::{Arena, BareChunk, Chunk, FreeChunk, HeapAllocator};

impl HeapAllocator {
    /// Retrieve the freelist for a given order
    ///
    /// Panics if `order` not in `(MIN_ORDER..=MAX_ORDER)`
    ///
    pub(super) fn get_freelist(&mut self, order: u8) -> &mut *mut FreeChunk {
        let i = order as usize - super::MIN_ORDER;
        let freelist: &mut *mut FreeChunk = self.free_lists.get_mut(i).unwrap();
        freelist
    }

    pub(super) unsafe fn populate_freelists(&mut self, arena: Arena) {
        let mut addr: *mut u8 = arena.start;
        let end = addr.byte_add(arena.size);

        for order in (super::MIN_ORDER..=super::MAX_ORDER).rev() {
            addr = addr.add(addr.align_offset(1usize << order));
            let order_end = end.sub(1 << order);
            while addr < order_end {
                // create a chunk at `addr`
                let bareptr = BareChunk::raw_new(addr, order as u8);
                self.push_freelist(bareptr);
                addr = addr.byte_add(1 << order);
            }
        }
    }

    /// Add a new bare chunk to the start of its respective freelist
    ///
    pub(super) unsafe fn push_freelist(&mut self, bareptr: *mut BareChunk) {
        let bare = bareptr.as_mut().unwrap();
        let order = bare.order;

        let chunkptr: *mut FreeChunk = bareptr.cast();
        let chunk = chunkptr.as_mut().unwrap();
        chunk.init(order);

        // find the freelist this chunk belongs to based on the order
        let freelist = self.get_freelist(chunk.order);

        // cons onto freelist
        let head = *freelist;
        chunk.next_chunk = head;
        chunk.prev_chunk = ptr::null_mut();
        *freelist = chunkptr;
    }

    /// Consume the first element from the freelist for a given order
    ///
    /// Panics if `order` not in `(MIN_ORDER..=MAX_ORDER)`
    ///
    pub(super) unsafe fn pop_freelist(&mut self, order: u8) -> Option<*mut BareChunk> {
        let freelist: &mut *mut FreeChunk = self.get_freelist(order);

        if freelist.is_null() {
            return None;
        }

        let head: *mut FreeChunk = *freelist;
        let chunk = head.as_mut().unwrap();
        let nextptr = chunk.next_chunk;

        // adjust linked pointers:
        // previous does not exist as this is the head
        // so only need to adjust `next.prev_chunk`
        if !nextptr.is_null() {
            let next = nextptr.as_mut().unwrap();
            next.prev_chunk = ptr::null_mut();
        }

        *freelist = nextptr;

        let bareptr: *mut BareChunk = head.cast();
        Some(bareptr)
    }

    /// Remove the chunk from its freelist
    ///
    /// Returns the now-unbound bare chunk
    ///
    #[allow(dead_code)]
    unsafe fn remove_from_freelist(&mut self, chunkptr: *mut FreeChunk) -> *mut BareChunk {
        let chunk = chunkptr.as_mut().unwrap();
        let order = chunk.order;
        let prev = chunk.prev_chunk;
        let next = chunk.next_chunk;

        if !next.is_null() {
            chunk.next_chunk.as_mut().unwrap().prev_chunk = prev;
        }

        if !prev.is_null() {
            prev.as_mut().unwrap().next_chunk = next;
        } else {
            // was head of the freelist, make it point to the new next
            let freelist = self.get_freelist(order);
            *freelist = next;
        }

        // hygeine: zero pointers
        chunk.next_chunk = ptr::null_mut();
        chunk.prev_chunk = ptr::null_mut();

        chunkptr.cast()
    }

    /// Return a free unbound chunk for some order
    ///
    pub(super) unsafe fn get_free_chunk(&mut self, order: u8) -> Option<*mut BareChunk> {
        let freechunk = self.pop_freelist(order);

        match freechunk {
            Some(ptr) => Some(ptr),
            None => {
                if order as usize == super::MAX_ORDER {
                    // out-of-memory
                    None
                } else {
                    match self.get_free_chunk(order + 1) {
                        None => {
                            // out-of-memory
                            return None;
                        }
                        Some(bare) => {
                            let bare = self
                                .try_crack_bare_chunk(bare)
                                .expect("tried to crack MIN_ORDER chunk");
                            Some(bare)
                        }
                    }
                }
            }
        }
    }

    /// Try split a free chunk in half
    ///
    /// For a chunk c in a freelist of order i
    /// Split into (c1, c2); push c2 onto the freelist of order i-1; and return c1.
    ///
    /// Returns None if the chunk cannot be cracked
    /// (e.g. because it is already a MIN_ORDER-sized chunk)
    ///
    #[allow(dead_code)]
    unsafe fn try_crack_free_chunk(&mut self, chunkptr: *mut FreeChunk) -> Option<*mut BareChunk> {
        let chunk = chunkptr.as_mut().unwrap();
        let order = chunk.order;

        // Cannot crack an already-minimum-sized chunk
        if order == super::MIN_ORDER as u8 {
            return None;
        }

        // remove it from list
        let bare = self.remove_from_freelist(chunkptr);
        self.try_crack_bare_chunk(bare)
    }

    /// Try split a free chunk in half
    ///
    /// For a chunk c in a freelist of order i split into (c1, c2) of order i-1
    /// and place c2 onto the freelist, returning c1
    ///
    /// Returns None if the chunk cannot be cracked
    /// (e.g. because it is already a MIN_ORDER-sized chunk)
    ///
    unsafe fn try_crack_bare_chunk(&mut self, bareptr: *mut BareChunk) -> Option<*mut BareChunk> {
        let bare = bareptr.as_mut().unwrap();
        let order = bare.order;

        // Cannot crack an already-minimum-sized chunk
        if order == super::MIN_ORDER as u8 {
            return None;
        }

        // remove it from list
        let new_order: u8 = order - 1;
        let new_size: usize = 1usize << new_order;
        bare.order = new_order;

        let buddyptr = BareChunk::raw_new(bareptr.byte_add(new_size).cast(), new_order);
        self.push_freelist(buddyptr);

        Some(bareptr)
    }
}

impl Chunk {
    /// Promote a bare chunk into an allocated one
    /// with all the right padding
    ///
    pub unsafe fn raw_new(bareptr: *mut BareChunk, align: usize) -> *mut Self {
        let bare = bareptr.as_mut().unwrap();
        let order = bare.order;
        let padding = super::try_compute_required_padding(order, align)
            .expect("allocator could not create Chunk: bad padding calc");

        let chunkptr: *mut Self = bareptr.cast();
        let chunk = chunkptr.as_mut().unwrap();
        chunk.order = order;
        chunk.padding = padding;

        chunkptr
    }

    pub unsafe fn raw_from_alloc(ptr: *mut u8) -> *mut Self {
        let npadptr = ptr.sub(mem::size_of::<u8>());
        let padding = npadptr.read() as usize;
        let npad_size = mem::size_of::<u8>();
        let header_size = mem::size_of::<Self>();
        let offset = npad_size + padding + header_size;
        let chunkptr: *mut Self = ptr.sub(offset).cast();
        chunkptr
    }

    pub unsafe fn downgrade(&mut self) -> *mut BareChunk {
        let bareptr: *mut BareChunk = self.raw().cast();
        bareptr
    }

    pub fn raw(&mut self) -> *mut Self {
        // this is, technically, not unsafe;
        // only using it is.
        self as *mut Self
    }

    /// Return a pointer to the `npad` byte
    ///
    pub unsafe fn npadptr(&mut self) -> *mut u8 {
        let offset = mem::size_of::<Chunk>() + self.padding as usize;
        let selfptr = self.raw();
        selfptr.cast::<u8>().add(offset)
    }

    /// Return the start of the `data` part of the chunk
    ///
    pub unsafe fn dataptr(&mut self) -> *mut u8 {
        let offset = mem::size_of::<Chunk>() + self.padding as usize + mem::size_of::<u8>();
        let selfptr = self.raw();
        selfptr.cast::<u8>().add(offset)
    }
}

impl BareChunk {
    /// Install the new unbound chunk metadata at a location
    ///
    unsafe fn raw_new(inner: *mut u8, order: u8) -> *mut Self {
        let bareptr: *mut BareChunk = inner.cast();
        let bare = bareptr.as_mut().unwrap();
        bare.order = order;
        bareptr
    }
}

impl FreeChunk {
    fn init(&mut self, order: u8) {
        self.order = order;
        self.next_chunk = ptr::null_mut();
        self.prev_chunk = ptr::null_mut();
    }
}
