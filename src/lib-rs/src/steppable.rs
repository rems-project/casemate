//! Infrastructure for the layering of the Model
//!
//! The Casemate model is stratified into layers.
//! [`Steppable`] provides the generic interface for a Layer, namely:
//! **an object which can take a step, maybe returning a Casemate [`Error`]**
//!
//! See [`layers`] for the actual Model layers.

use crate::shim::*;

use crate::base_model::Ctx;
use crate::errors;

pub type Result<'t> = result::Result<(), errors::Error<'t>>;

pub trait Steppable {
    fn step<'t>(&mut self, t: &Ctx<'t>) -> Result<'t>;
}

pub trait Layer
where
    Self: fmt::Debug,
    Self: Clone,
    Self: Steppable,
{
    #[allow(dead_code)]
    fn label() -> &'static str;

    #[allow(dead_code)]
    fn parents() -> Vec<&'static str>;
}
