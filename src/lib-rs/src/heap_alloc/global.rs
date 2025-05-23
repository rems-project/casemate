//! Installs a global allocator in `no_std` mode
//!
//! Uses the allocator from the [`allocator`] module

#![cfg(not(feature = "std"))]

// we can use ::core not the agnostic shim as we are in nostd mode here anyway.
use core::alloc::{GlobalAlloc, Layout};
use core::cell::UnsafeCell;
use core::ptr;

use super::allocator;

pub struct CasemateAllocator {
    pub alloc: UnsafeCell<allocator::HeapAllocator>,
}

#[global_allocator]
pub static ALLOCATOR: CasemateAllocator = CasemateAllocator {
    alloc: UnsafeCell::new(allocator::HeapAllocator::new()),
};

unsafe impl Sync for CasemateAllocator {}

unsafe impl GlobalAlloc for CasemateAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        if let Some(halloc) = self.alloc.get().as_mut() {
            halloc.alloc(layout)
        } else {
            ptr::null_mut()
        }
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        if let Some(halloc) = self.alloc.get().as_mut() {
            halloc.dealloc(ptr, layout)
        }
    }
}
