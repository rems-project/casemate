//! casemate-lib
//!
//! The static library portion of Casemate.
//! This provides the actual model and stepper functions.
//!
//! [log]: https://crates.io/crates/log
//! [serde_json]: https://serde.rs
//! [trace-format]: ./doc/asciidoc/sections/trace-format.adoc

#![feature(macro_metavar_expr)]
#![feature(macro_metavar_expr_concat)]
// conditional no_std;
// if we are linking into a Rust executable with std, we can use std
// otherwise we exclude it.
#![cfg_attr(not(feature = "std"), no_std)]

// in no_std we still can use alloc, and we have our own allocator in [`heap_alloc`]
#[cfg(feature = "alloc")]
extern crate alloc as ealloc;
#[cfg(feature = "alloc")]
pub mod allocator;

/// A wrapper around the `std`/`no_std` types
/// gives a uniform Prelude that can be used everywhere
/// which looks the same from both `std` and `no_std`
#[allow(unused_imports)]
mod shim {
    mod core {
        #[cfg(not(feature = "std"))]
        pub use core::*;
        #[cfg(feature = "std")]
        pub use std::*;
    }

    // re-export subset of std::prelude we need
    pub use self::core::alloc;
    pub use self::core::cell;
    pub use self::core::cmp;
    pub use self::core::error::Error as StdError;
    pub use self::core::fmt::{self, Debug, Display, Write};
    pub use self::core::iter;
    pub use self::core::mem;
    pub use self::core::num;
    pub use self::core::ops;
    pub use self::core::ops::FnOnce;
    pub use self::core::ptr;
    pub use self::core::result;
    pub use self::core::slice;
    pub use self::core::str;
    pub use self::core::sync;
    pub use core::ffi::{self, CStr};

    pub use self::core::{write, writeln};

    #[cfg(not(feature = "std"))]
    pub use ealloc::alloc::alloc as malloc;
    #[cfg(feature = "std")]
    pub use std::alloc::alloc as malloc;

    #[cfg(feature = "std")]
    pub use self::core::{print, println};
    #[cfg(not(feature = "std"))]
    pub use crate::{print, println};

    #[cfg(not(feature = "std"))]
    pub use ealloc::format;
    #[cfg(feature = "std")]
    pub use std::format;

    #[cfg(not(feature = "std"))]
    pub use ealloc::{vec, vec::Vec};
    #[cfg(feature = "std")]
    pub use std::{vec, vec::Vec};

    #[cfg(not(feature = "std"))]
    pub use ealloc::collections;
    #[cfg(feature = "std")]
    pub use std::collections;

    #[cfg(not(feature = "std"))]
    pub use ealloc::string::{self, String, ToString};
    #[cfg(feature = "std")]
    pub use std::string::{self, String, ToString};

    #[cfg(not(feature = "std"))]
    pub use ealloc::boxed::{self, Box};
    #[cfg(feature = "std")]
    pub use std::boxed::{self, Box};

    #[cfg(not(feature = "std"))]
    pub use ealloc::ffi::CString;
    #[cfg(feature = "std")]
    pub use std::ffi::CString;
}

mod c_api;
mod hooks;

#[cfg(not(feature = "std"))]
mod ghost_driver;

#[macro_use]
mod collections;

#[macro_use]
extern crate log;
pub mod loggers;

#[macro_use]
mod bits;

// mod output;
mod errors;
mod model;
mod output;
mod state;
mod steppable;
mod tracefmt;

// re-exports

pub mod config;
#[macro_use]
pub mod transitions;

pub use crate::state::{configure, init_model, step_model, step_model_traceevent};
pub use errors::CasemateError;

/// Casemate library version
pub const VERSION: &'static str = env!("CARGO_PKG_VERSION");

#[cfg(panic = "abort")]
use core::panic::PanicInfo;

#[cfg(panic = "abort")]
#[panic_handler]
fn panic(_info: &PanicInfo) -> ! {
    ghost_driver::abort("panic!");
}
