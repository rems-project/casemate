use crate::shim::*;

#[allow(unused_imports)]
use log;

use diffable::Diffable;
use pgtable::{Context, Stage, TranslationRegime};
use pte::PTE;

use crate::collections::region_map::{DWordSpan, RegionMap};
use crate::errors::CodedError;
use crate::output::{LayerFormat, LayerFormatter};
use crate::steppable::Layer;

use super::machine::{Machine, MachineError};

mod pgtable;
mod pte;
mod step;

#[derive(Debug, Clone, Default, Diffable)]
pub struct Pgtables {
    live_contexts: ContextSet,
    ptmem: RegionMap<DWordSpan, pte::PTE>,
    unclean_locs: collections::BTreeSet<u64>,
}

#[derive(Debug, Clone, Default, Diffable)]
pub struct ContextSet {
    inner: collections::BTreeMap<Context, u64>,
}

impl ContextSet {
    fn find_root(&self, base: u64) -> Option<&Context> {
        self.inner.keys().find(|ctx| ctx.base == base)
    }

    fn find_id(&self, regime: TranslationRegime, stage: Stage, id: u8) -> Option<&Context> {
        self.inner
            .keys()
            .find(|ctx| ctx.regime == regime && ctx.stage == stage && ctx.id == id)
    }

    pub fn insert(&mut self, ctx: Context) {
        self.inner.insert(ctx, 0);
    }

    pub fn inc_ref(&mut self, ctx: &Context) {
        if let Some(v) = self.inner.get_mut(ctx) {
            *v += 1;
        }
    }

    pub fn dec_ref(&mut self, ctx: &Context) {
        // TODO: report error on non-existent context?
        if let Some(v) = self.inner.get_mut(ctx) {
            // TODO: check underflow + report error?
            *v -= 1;
        }
    }
}

impl LayerFormat for ContextSet {
    fn fmt_layer(&self, f: &mut LayerFormatter<'_, '_>) -> fmt::Result {
        write!(f, "{:?}", self.inner)
    }
}

/// Errors from stepping the pagetable layer
#[derive(Debug, Clone)]
pub enum PgtableError {
    Inner(MachineError),
    WriteUnclean,
    WriteFrozen,
    UntrackedLocation(u64),
    FailedPgtableWalk(MachineError),
    ReservedASID,
    BadContextSwitch(&'static str),
    BadPTEEncoding(&'static str),
}

impl fmt::Display for PgtableError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Inner(e) => write!(f, "{}", e),
            Self::WriteUnclean => write!(f, "attempted write to unclean location"),
            Self::WriteFrozen => write!(f, "attempted write to read-only location"),
            Self::UntrackedLocation(l) => {
                write!(f, "attempted access to untracked location {l:#16x}")
            }
            Self::FailedPgtableWalk(e) => write!(f, "error during pgtable walk: {e}"),
            Self::ReservedASID => write!(f, "attempted to use reserved ASID"),
            Self::BadContextSwitch(s) => write!(f, "error in context switch: {s}"),
            Self::BadPTEEncoding(s) => write!(f, "bad encoding of page table entry: {s}"),
        }
    }
}

impl StdError for PgtableError {}

impl CodedError for PgtableError {
    fn error_code(&self) -> &'static str {
        match self {
            Self::Inner(e) => e.error_code(),
            Self::WriteUnclean => "E120010",
            Self::WriteFrozen => "E120015",
            Self::UntrackedLocation(_) => "E120020",
            Self::FailedPgtableWalk(err) => err.error_code(),
            Self::ReservedASID => "E120025",
            Self::BadContextSwitch(_) => "E120028",
            Self::BadPTEEncoding(_) => "E120100",
        }
    }
}

// #[derive(Debug)]
// #[allow(dead_code)]
// pub struct DiffPgtables<'diffl> {
//     // roots: diffable::InnerDiff<'diffl, Vec<Root>>,
//     ptmem: diffable::InnerDiff<'diffl, RegionMap<DWordSpan, PTE>>,
//     inner: &'diffl u64,
// }

// impl<'diffl> diffable::DisplayDiff for DiffPgtables<'diffl> {
//     fn fmt(&self, _f: &mut diffable::display::DisplayWrapper<'_>) -> ::core::fmt::Result {
//         Ok(())
//     }
// }

// impl<'diffl> diffable::Diffable<'diffl> for Pgtables {
//     type Diff = DiffPgtables<'diffl>;
//     fn diff(&'diffl self, _other: &'diffl Self) -> diffable::Difference<&'diffl Self, Self::Diff> {
//         diffable::Difference::NoChange
//     }
// }

impl Pgtables {
    pub fn new() -> Self {
        Self::default()
    }

    /// Try find the [`Context`] associated with a given root base address
    ///
    /// Returns `None` if there is no such context
    pub fn context_for_base_addr(&self, addr: u64) -> Option<&Context> {
        self.live_contexts.find_root(addr)
    }

    /// Try find the [`Context`] associated with a particular Regime + Stage + (VM/AS)ID
    ///
    /// Returns `None` if there is no such context
    pub fn context_for_id(
        &self,
        regime: TranslationRegime,
        stage: Stage,
        id: u8,
    ) -> Option<&Context> {
        self.live_contexts.find_id(regime, stage, id)
    }
}

impl LayerFormat for Pgtables {
    fn fmt_layer(&self, f: &mut LayerFormatter<'_, '_>) -> fmt::Result {
        f.write_str("contexts:\n")?;
        f.indented(&self.live_contexts)?;
        f.write_str("mem:\n")?;
        f.indented(&self.ptmem)
    }
}

impl Layer for Pgtables {
    fn label() -> &'static str {
        "pgtable"
    }

    fn parents() -> Vec<&'static str> {
        vec![Machine::label()]
    }
}
