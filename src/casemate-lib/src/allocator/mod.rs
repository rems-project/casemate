//! `no_std` allocation
//!
//! [`heap_alloc:HeapAllocator`] is a samll `no-std` allocator which starts out empty
//! it must be filled with calls to [`init_heap_alloc`]

#![cfg(feature = "alloc")]

// the allocator itself
mod heap_alloc;

// [global_allocator] management
mod global;
use self::global::ALLOCATOR;

/// Initialise the global allocator state
///
/// The global allocator is installed from the beginning
/// but has no memory to allocate from. This provides the
/// allocator with some arena to use.
pub fn init_heap_alloc(start: *mut u8, size: usize) {
    let allocator = &ALLOCATOR.alloc.get();
    if let Some(halloc) = unsafe { allocator.as_mut() } {
        halloc.init(start, size)
    }
}
