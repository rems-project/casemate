//! Configuration datatypes
//!
//! [`Config`] holds all the runtime configuration for Casemate

use serde::{Deserialize, Serialize};

use crate::shim::Vec;

pub mod de;
pub use de::{make_config_builder, ConfigBuilder};

/// Global Casemate configuration
#[derive(Clone, Debug, Default, Serialize)]
pub struct Config {
    pub model: ModelOpts,
    pub tracing: TraceOpts,
    pub printing: PrintOpts,
    pub watchpoints: Vec<u64>,
}

impl Config {
    pub const fn new() -> Self {
        Self {
            model: ModelOpts {
                on: true,
                promote_non_shareable: false,
                ignore_vmid: false,
                allow_races: false,
            },
            tracing: TraceOpts {
                on: true,
                tracefmt_version: TracefmtVersion::V0,
            },
            printing: PrintOpts {
                on: false,
                dump: false,
                diff: false,
                condense: true,
            },
            watchpoints: Vec::new(),
        }
    }
}

/// Format to output event traces in
#[derive(Copy, Clone, Debug, Default, Serialize, Deserialize)]
pub enum TracefmtVersion {
    /// The default format
    ///
    /// As s-exprs with all the transition data
    #[default]
    V0,

    /// A variant of the v0 format, but without explicit keywords
    V0Condensed,
}

/// Configuration to control when/how to produce event traces
#[derive(Clone, Debug, Default, Serialize)]
pub struct TraceOpts {
    /// Enable/disable printing of event traces
    pub on: bool,

    /// Format of the event traces to use
    pub tracefmt_version: TracefmtVersion,
}

/// Configuration controls for the model and layers
#[derive(Clone, Debug, Default, Serialize)]
pub struct ModelOpts {
    /// Enable/disable model checking
    pub on: bool,

    /// Promote non-shareable instructions to full-system
    pub promote_non_shareable: bool,

    /// Treat all TLBI-by-VMID instructions as global
    pub ignore_vmid: bool,

    /// Disable race detection
    pub allow_races: bool,
}

/// Configuration controls for debug/informational prints
#[derive(Clone, Debug, Default, Serialize)]
pub struct PrintOpts {
    /// Enable/disable non-event-trace output
    pub on: bool,

    /// Print out the state on each step
    pub dump: bool,

    /// Print diffs to the state on each step
    pub diff: bool,

    /// Use a more condensed format
    pub condense: bool,
}
