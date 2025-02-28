#[allow(unused_imports)]
use crate::shim::*;

use diffable::Diffable;

use crate::output;
use crate::steppable::{self, Steppable};
use crate::tracefmt;

use super::{Ctx, Model, VisitedLayers};

macro_rules! do_step {
    ($self:ident, $ctx:ident, $field:ident) => {
        let mut $field = $self.$field.take().expect("bad topology");
        $field.step($ctx)?;
        $ctx.below.$field = Some($field);
    };
}

impl Model {
    fn restore_back(&mut self, layers: &mut VisitedLayers) {
        self.mach = layers.mach.take();
        self.pgt = layers.pgt.take();
    }

    pub fn step<'t>(&mut self, ctx: &'t mut Ctx<'t>) -> steppable::Result<'t> {
        if ctx.config.tracing.on {
            info!("step: {}!", tracefmt::emit_trace_event(&ctx.t));
        }

        if !ctx.config.model.on {
            return Ok(());
        }

        if ctx.config.printing.diff {
            ctx.snapshot = Some(self.clone());
        }

        // step the layers!
        // note the careful ownership juggling:
        // after we step we move the part of the state into the ctx
        // -- so later layers can inspect it --
        // and then move them all back at the end
        do_step!(self, ctx, mach);
        do_step!(self, ctx, pgt);

        self.restore_back(&mut ctx.below);

        if ctx.config.printing.on {
            if ctx.config.printing.dump {
                info!("new state =\n{}", output::format_layer(ctx, self));
            }

            if ctx.config.printing.diff {
                let diff = self.diff(
                    ctx.snapshot
                        .as_ref()
                        .expect("unable to unwrap snapshot on printing diff"),
                );
                info!("diff from previous =\n{diff:#}");
            }
        }

        Ok(())
    }
}
