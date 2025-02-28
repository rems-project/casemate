use crate::collections::region_map::DWordSpan;
use crate::errors;
use crate::model::layers::pgtable::pgtable::{is_ttbr, ArchContext};
use crate::model::layers::Machine;
use crate::shim::*;

use crate::model::Ctx;
use crate::CasemateError;

use crate::steppable::{self, Steppable};
use crate::transitions::{self, Arm_DxB_Kind, BarrierKind, MemOrder, RegName, TLBIKind};

use super::pgtable::{
    read_ttbr, regime_of_ttbr, traverse_all_unclean, traverse_pgtable, Context, DecodedTTB,
    Descriptor, Stage, TranslationRegime, WalkData, WALKER_FLAGS_ALLOW_UNINIT,
};
use super::pte::*;
use super::{PgtableError, Pgtables};

struct PgtableStepContext<'t, 'ctx, 'st> {
    /// The transition context
    ctx: &'ctx Ctx<'t>,

    /// The underlying [`Pgtables`] state we're updating
    st: &'st mut Pgtables,

    /// The previously-visited [`Machine`]
    mach: &'st Machine,
}

fn dsb_visitor(data: WalkData) -> Result<(), PgtableError> {
    Ok(())
}

fn init_visitor(data: WalkData) -> Result<(), PgtableError> {
    let loc = &mut data.st.ptmem[data.ptep];

    log::debug!("init_visitor {}", data.ptep);

    if loc.owner.is_some() {
        return Err(PgtableError::BadContextSwitch("double-use pte"));
    }

    // location unknown to the Pgtable layer
    // so create and initialise a new PTE
    let raw_desc = data
        .ctx
        .below
        .mach
        .as_ref()
        .unwrap()
        .read_mem(data.ptep)
        .map_err(PgtableError::FailedPgtableWalk)?;
    let desc = Descriptor::parse(&data.trans_ctx, data.level, raw_desc)?;
    let loc = PTE::init_child(data.trans_ctx.clone(), desc, data.level);
    data.st
        .ptmem
        .insert_range(DWordSpan::new(data.ptep, 64), loc);

    Ok(())
}

impl<'t, 'ctx, 'st> PgtableStepContext<'t, 'ctx, 'st> {
    fn assert_has_write_authority(
        &mut self,
        _caddr: u64,
        _mo: MemOrder,
    ) -> Result<(), PgtableError> {
        // TODO
        Ok(())
    }

    fn register_new_context(&mut self, ctx: Context) -> Result<(), PgtableError> {
        traverse_pgtable(
            self.ctx,
            &ctx,
            self.st,
            init_visitor,
            WALKER_FLAGS_ALLOW_UNINIT,
        )?;
        self.st.live_contexts.insert(ctx);
        Ok(())
    }

    fn step_write_on_clean(&mut self, addr: u64, v: u64) -> Result<(), PgtableError> {
        let old_desc = self
            .mach
            .try_read_mem(addr)
            .ok_or(PgtableError::UntrackedLocation(addr))?;
        let pte = &mut self.st.ptmem[addr];
        pte.tlb_state = TLBState::from_write(self.ctx.t.info.tid, old_desc);
        pte.descriptor = Descriptor::parse(&pte.context, pte.level, v)?;
        self.st.unclean_locs.insert(addr);
        Ok(())
    }

    fn step_write(&mut self, addr: u64, mo: MemOrder, v: u64) -> Result<(), PgtableError> {
        if !self.st.ptmem.contains(&addr) {
            return Ok(());
        }

        // check we are allowed to write at all
        self.assert_has_write_authority(addr, mo)?;

        // we can write, but what we do depends on whether the location is clean or not
        let pte = &mut self.st.ptmem[addr];

        if pte.frozen {
            return Err(PgtableError::WriteFrozen);
        }

        match pte.tlb_state {
            TLBState::Init | TLBState::Clean(_) => self.step_write_on_clean(addr, v),
            TLBState::Unclean(_) => {
                // not allowed to write an unclean location at all
                Err(PgtableError::WriteUnclean)
            }
        }
    }

    fn step_barrier(&mut self, k: &BarrierKind) -> Result<(), PgtableError> {
        // TODO
        match k {
            BarrierKind::Arm_DSB(Arm_DxB_Kind::Arm_DxB_ISH) => {
                traverse_all_unclean(
                    self.ctx,
                    self.st,
                    TranslationRegime::EL10,
                    Stage::Stage2,
                    dsb_visitor,
                    0,
                )?;
                traverse_all_unclean(
                    self.ctx,
                    self.st,
                    TranslationRegime::EL2,
                    Stage::Stage1,
                    dsb_visitor,
                    0,
                )?;
                Ok(())
            }
            _ => Ok(()),
        }
    }

    fn step_tlbi(&mut self, t: &TLBIKind) -> Result<(), PgtableError> {
        // TODO
        Ok(())
    }

    fn step_reg_write(&mut self, reg: &RegName<'_>, val: u64) -> Result<(), PgtableError> {
        log::debug!("step_reg_write {}", reg.0);

        if is_ttbr(reg.0) {
            let (regime, stage) = regime_of_ttbr(reg.0);
            let DecodedTTB { id, base } = read_ttbr(val);

            // in non-VHE mode, TTBR0_EL2 has ASID Res0
            if regime == TranslationRegime::EL2 && id != 0 {
                return Err(PgtableError::ReservedASID);
            }

            // check if the id or baddr is already registered for a different root
            let id_ctx = self.st.context_for_id(regime, stage, id);
            let base_ctx = self.st.context_for_base_addr(base);

            if let Some(ctx) = id_ctx {
                if ctx.base != base {
                    return Err(PgtableError::BadContextSwitch("duplicate AS/VMIDs"));
                }
            } else if let Some(ctx) = base_ctx {
                if ctx.id != id {
                    return Err(PgtableError::BadContextSwitch(
                        "root already registered for a different AS/VMID",
                    ));
                }
            } else {
                // no known registered context for either that address or AS/VMID
                // so register a new one
                let ctx = Context {
                    base,
                    id,
                    regime,
                    stage,
                    arch: ArchContext::for_regime(self.mach, regime, stage)
                        .map_err(PgtableError::Inner)?,
                };

                self.register_new_context(ctx)?;
            }

            // TODO ctx switch
            todo!();
        }

        Ok(())
    }

    fn step(&mut self) -> Result<(), PgtableError> {
        use transitions::Operation::*;

        match &self.ctx.t.op {
            Write(a, mo, v) => {
                self.step_write(a.0, *mo, *v)?;
            }
            Barrier(barrier_kind) => {
                self.step_barrier(barrier_kind)?;
            }
            TLBInval(tlbi_kind) => {
                self.step_tlbi(tlbi_kind)?;
            }
            RegWrite(reg, val) => {
                self.step_reg_write(reg, *val)?;
            }
            _ => (),
        }

        Ok(())
    }
}

impl Steppable for Pgtables {
    fn step<'t>(&mut self, ctx: &Ctx<'t>) -> steppable::Result<'t> {
        let mut pstate = PgtableStepContext {
            ctx,
            st: self,
            mach: ctx.below.mach.as_ref().unwrap(),
        };
        pstate
            .step()
            .map_err(errors::CasemateError::from_pgtable_err)
    }
}
