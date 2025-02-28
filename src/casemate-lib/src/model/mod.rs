//! The Casemate Model
//!
//! [`Model`] is an entire model state, composed
//! from layers of [`Steppable`] implementations.
//!
//! See [`layers`] for the various layers within the model

use crate::shim::*;

use diffable::Diffable;

use crate::config::Config;
use crate::output::{LayerFormat, LayerFormatter};
use crate::transitions::Transition;

pub mod layers;
mod step;

#[derive(Clone, Debug, Diffable)]
pub struct Model {
    mach: Option<layers::Machine>,
    pgt: Option<layers::Pgtables>,
}

pub struct VisitedLayers {
    pub mach: Option<layers::Machine>,
    pub pgt: Option<layers::Pgtables>,
}

impl VisitedLayers {
    pub const fn empty() -> Self {
        Self {
            mach: None,
            pgt: None,
        }
    }
}

pub struct Ctx<'t> {
    /// The current Casemate configuration options
    pub config: &'t Config,

    /// The previous whole-machine snapshot
    ///
    /// Only exists if diffing mode is enabled.
    pub snapshot: Option<Model>,

    /// The layers below the current one which have been computed already
    pub below: VisitedLayers,

    /// The current step
    pub t: Transition<'t>,
}

impl Model {
    pub fn new() -> Self {
        let mach = layers::Machine::new();
        let pgt = layers::Pgtables::new();

        Self {
            mach: Some(mach),
            pgt: Some(pgt),
        }
    }
}

impl LayerFormat for Model {
    fn fmt_layer(&self, f: &mut LayerFormatter<'_, '_>) -> fmt::Result {
        let mach = self
            .mach
            .as_ref()
            .expect("cannot format Machine layer while not owned");
        let pgt = self
            .pgt
            .as_ref()
            .expect("cannot format Pgtable ayer while not owned");

        f.write_str("mach:\n")?;
        f.indented(mach)?;

        f.write_str("pgtables:\n")?;
        f.indented(pgt)?;
        Ok(())
    }
}
