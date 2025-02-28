//! The Casemate model skeleton
//!
//! [`Model`] is an entire model state, composed
//! from layers of [`Overlay`] implementations.

use crate::shim::*;

use crate::collections::diff::Diffable;

use crate::config::Config;
use crate::layers::{Machine, Pgtables};
use crate::steppable::{self, Steppable};
use crate::transitions::Transition;

use crate::tracefmt;

#[derive(Clone, Debug)]
pub struct Model {
    mach: Option<Machine>,
    pgt: Option<Pgtables>,
}

make_diffable_struct!(Model, ModelDiff; mach: Option<Machine>, pgt: Option<Pgtables>);

pub struct VisitedLayers {
    pub mach: Option<Machine>,
    pub pgt: Option<Pgtables>,
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
    pub snapshot: &'t Model,

    /// The layers below the current one which have been computed already
    pub below: VisitedLayers,

    /// The current step
    pub t: Transition<'t>,
}

macro_rules! do_step {
    ($self:ident, $ctx:ident, $field:ident) => {
        let mut $field = $self.$field.take().expect("bad topology");
        $field.step($ctx)?;
        $ctx.below.$field = Some($field);
    };
}

impl Model {
    pub fn new() -> Self {
        let mach = Machine::new();
        let pgt = Pgtables::new();

        Self {
            mach: Some(mach),
            pgt: Some(pgt),
        }
    }

    fn restore_back(&mut self, layers: &mut VisitedLayers) {
        self.mach = layers.mach.take();
        self.pgt = layers.pgt.take();
    }

    pub fn step<'t>(&mut self, ctx: &'t mut Ctx<'t>) -> steppable::Result<'t> {
        if ctx.config.tracing.on {
            info!("step: {}!", tracefmt::to_sexpr(&ctx.t));
        }

        // step the layers
        do_step!(self, ctx, mach);
        do_step!(self, ctx, pgt);

        self.restore_back(&mut ctx.below);

        if ctx.config.printing.on {
            if ctx.config.printing.dump {
                info!("new state = {self:#?}");
            }

            if ctx.config.printing.diff {
                let diff = self.diff(ctx.snapshot);
                info!("diff from previous = {diff:#?}");
            }
        }

        Ok(())
    }
}
