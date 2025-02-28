//! The Casemate model layers
//!
//! As described, the Casemate model is constructed from layers of [`Layer`]s.
//! This module provides those layers.
//! - [`Machine`] is the base layer containing registers and memory etc.
//! - ...

// base layer
pub mod machine;
pub use self::machine::Machine;

pub mod pgtable;
pub use self::pgtable::Pgtables;
