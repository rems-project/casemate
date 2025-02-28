#![allow(dead_code, unused_imports)]
/// This module defines the break-before-make states of a PTE
use crate::shim::*;

use diffable::display::DisplayDiffBuilder;
#[allow(unused_imports)]
use log;

use diffable::{self, Diffable, DisplayDiff};

use crate::collections::region_map::{ByteSpan, RegionMap};
use crate::errors;
use crate::output::{LayerFormat, LayerFormatter};
use crate::steppable::{self, Layer, Steppable};
use crate::transitions;

use super::pgtable::{Context, Descriptor, Stage};

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum LocalCleanState {
    Unsynchronised,
    GloballyVisible,
    LocallySynchronised,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct CleanState {
    pub local_st: LocalCleanState,
    pub old_desc: u64,
}

/// Thread-local state machine following the architecture-mandated cleaning process
///
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum UncleanCleaningProgress {
    /// No progress has been made
    Unsychronized,

    /// The write has been made visible to the MMU.
    /// e.g. via an Arm `DSB` instruction.
    MadeVisibleToMMU,

    /// All required TLB maintenance has been issued
    /// but not yet necessarily completed.
    CleanedUnsychronised,

    /// Partial TLB maintenance has been issued (i.e. second-stage only)
    /// but not yet completed.
    CleanedSecondStageUnsychronised,

    /// Partial (second-stage only) TLB maintenance has completed.
    CleanedSecondStage,

    /// All required TLB maintenance has completed.
    Cleaned,
}

/// A Globally-unclean PTE with some in-progress cleaning on one thread
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct UncleanState {
    /// Thread that is responsible for doing the cleaning
    pub tid: u64,

    /// The previous descriptor
    pub old_raw_desc: u64,

    /// Progress of thread `tid` cleaning the PTE
    pub local_st: UncleanCleaningProgress,
}

impl UncleanState {
    pub fn from_write(tid: u64, old_desc: u64) -> Self {
        Self {
            tid,
            old_raw_desc: old_desc,
            local_st: UncleanCleaningProgress::Unsychronized,
        }
    }
}

/// The global TLB state of a PTE.
///
/// This state is hierarchical with a thread-local state contained within.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum TLBState {
    /// Not written to yet, since becoming pgt
    Init,

    /// Written to, but not yet cleaned
    Unclean(UncleanState),

    /// Written to, and now cleaned.
    Clean(CleanState),
}

impl TLBState {
    pub fn from_write(tid: u64, old_desc: u64) -> Self {
        Self::Unclean(UncleanState::from_write(tid, old_desc))
    }

    pub fn init(old_desc: u64) -> Self {
        Self::Clean(CleanState {
            local_st: LocalCleanState::GloballyVisible,
            old_desc,
        })
    }
}

impl<'l> Diffable<'l> for TLBState {
    type Diff = TLBState;

    fn diff(&'l self, _other: &'l Self) -> diffable::Difference<&'l Self, Self::Diff> {
        diffable::Difference::NoChange
    }
}

impl DisplayDiff for TLBState {
    fn fmt(&self, f: &mut diffable::display::DisplayWrapper<'_>) -> core::fmt::Result {
        match self {
            TLBState::Init => write!(f, "init"),
            TLBState::Clean(_) => write!(f, "clean"),
            TLBState::Unclean(_) => write!(f, "unclean"),
        }
    }
}

#[derive(Copy, Clone, Debug, Diffable, PartialEq, Eq)]
#[diff_derive(Copy, Clone, Debug)]
pub struct PTE {
    /// true when the PTE is unable to be modified
    pub frozen: bool,

    /// A cached decoded descriptor
    pub descriptor: Descriptor,

    // /// The raw 64-bit descriptor
    // /// (should be identical to `Machine.read_mem(addr)`)
    // pub raw_desc: u64,
    /// The context this PTE is associated with
    pub context: Context,

    /// The level of this PTE
    ///
    /// typically 0 = at root level, but beware that in Arm trees
    /// can start from levels >0 or even level -1
    pub level: u8,

    /// Current TLB cleanliness
    pub tlb_state: TLBState,

    /// Base of the [`Context`] which this PTE belongs to
    pub owner: Option<u64>,
}

impl fmt::Display for PTE {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl PTE {
    pub fn init_child(context: Context, descriptor: Descriptor, level: u8) -> Self {
        Self {
            frozen: false,
            descriptor,
            context,
            level,
            tlb_state: TLBState::Init,
            owner: Some(context.base),
        }
    }
}
