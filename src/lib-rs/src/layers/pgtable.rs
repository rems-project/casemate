use crate::shim::*;

#[allow(unused_imports)]
use log;

use crate::collections::RegionMap;
use crate::errors;
use crate::steppable::{self, Layer, Steppable};
use crate::transitions;

use crate::base_model::Ctx;

use super::machine::Machine;

#[derive(Debug, Clone, Default)]
pub struct Pgtables {
    roots: Vec<Root>,
    ptmem: RegionMap<u64>,
}

make_diffable_struct!(Pgtables, PgtablesDiff; roots: Vec<Root>, ptmem: RegionMap<u64>);

#[derive(Debug, Clone)]
struct Root {
    root: u64,
    id: u8,
}

make_diffable_struct!(Root, RootDiff; root: u64, id: u8);

impl Pgtables {
    pub fn new() -> Self {
        Self::default()
    }
}

impl Steppable for Pgtables {
    fn step<'t>(&mut self, ctx: &Ctx<'t>) -> steppable::Result<'t> {
        #[allow(unused_imports)]
        use errors::Error::*;
        use transitions::Operation::*;

        match &ctx.t.op {
            Write(a, _mo, _v) => {
                debug!(
                    "step pgt, me={:?} below={:?}",
                    self.ptmem.get(&a.0),
                    ctx.below.mach.as_ref().unwrap().read_mem(a.0)
                );
            }
            _ => (),
        }
        Ok(())
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

#[derive(Clone, Debug)]
enum LocalCleanState {
    Unsynchronised,
    GloballyVisible,
    LocallySynchronised,
}

#[derive(Clone, Debug)]
struct CleanState {
    local_st: LocalCleanState,
    old_desc: u64,
}

#[derive(Clone, Debug)]
enum UncleanCleaningProgress {
    MadeVisibleToMMU,
    CleanedSecondStageUnsychronised,
    CleanedSecondStage,
    CleanedUnsychronised,
    Cleaned,
}

#[derive(Clone, Debug)]
enum LocalUncleanState {
    Unsynchronised,
    CleaningInProgress(UncleanCleaningProgress),
    Cleaned,
}

#[derive(Clone, Debug)]
struct UncleanState {
    tid: u8,
    old_desc: u64,
    local_st: LocalUncleanState,
}

#[derive(Clone, Debug)]
enum BBMState {
    Clean(CleanState),
    Unclean(UncleanState),
    Frozen,
}

#[derive(Clone, Debug)]
struct PTE {
    cleanliness: BBMState,
}
