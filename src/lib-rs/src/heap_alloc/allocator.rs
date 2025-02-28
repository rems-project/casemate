#![cfg(not(feature = "std"))]

//! A very simple `no_std` allocator
//!
//! [`HeapAllocator`] is a simple bump allocator (for now),
//! not thread-safe.

use crate::shim::alloc::Layout;
use crate::shim::ptr;
use crate::shim::sync::atomic::{AtomicUsize, Ordering::SeqCst};

pub struct HeapAllocator {
    start: *mut u8,
    size: usize,
    cur: AtomicUsize,
}

unsafe impl Send for HeapAllocator {}
unsafe impl Sync for HeapAllocator {}

impl HeapAllocator {
    pub const fn new() -> Self {
        Self {
            start: 0 as *mut u8,
            size: 0,
            cur: AtomicUsize::new(0),
        }
    }

    pub fn alloc(&mut self, layout: Layout) -> *mut u8 {
        let size = layout.size();
        let align = layout.align();

        let mask = !(align - 1);
        let mut allocp: *mut u8 = ptr::null_mut();

        let allocated = self.cur.fetch_update(SeqCst, SeqCst, |mut cur| {
            cur -= size;
            cur &= mask;

            if cur < self.start as usize {
                None
            } else {
                allocp = cur as *mut u8;
                Some(cur)
            }
        });

        match allocated {
            Err(_) => ptr::null_mut(),
            Ok(_) => allocp,
        }
    }

    pub fn dealloc(&self, _ptr: *mut u8, _layout: Layout) {
        ()
    }

    pub fn init(&mut self, start: *mut u8, size: usize) {
        self.start = start;
        self.size = size;
        self.cur.store((start as usize) + size, SeqCst);
    }
}
