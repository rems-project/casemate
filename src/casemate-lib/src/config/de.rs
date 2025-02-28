//! Partial Deserialization for a Config
//!
//! # Example
//!
//! ```edition2021
//! use casemate::config::{Config, make_config_builder};
//! let mut config = Config::default();
//! let builder = make_config_builder("{\"model\": {\"on\": false}}").unwrap();
//! builder.apply(&mut config); // sets config.model.on to false
//! ```

use serde::Deserialize;

use super::*;

use crate::shim::Vec;

/// Partial builder for a [`Config`]
///
/// Mimics the structure of a real [`Config`],
/// but where the fields are lifted to options.
///
/// Can then use a partial [`ConfigBuilder`] to update an existing Config object
/// with the supplied fields.
/// [serde_json] can deserialize JSON into a `ConfigBuilder` to be applied
///
#[derive(Clone, Debug, Default, Deserialize)]
pub struct ConfigBuilder {
    pub model: Option<ModelOptsBuilder>,
    pub tracing: Option<TraceOptsBuilder>,
    pub printing: Option<PrintOptsBuilder>,
    pub watchpoints: Option<Vec<u64>>,
}

macro_rules! apply_optional {
    ($self:ident, $base:ident, recurse:$field:ident) => {
        if let Some(b) = &$self.$field {
            b.apply(&mut $base.$field);
        }
    };
    ($self:ident, $base:ident, field:$field:ident) => {
        if let Some(b) = &$self.$field {
            $base.$field = *b;
        }
    };
}

impl ConfigBuilder {
    pub fn apply(&self, base: &mut Config) {
        apply_optional!(self, base, recurse:model);
        apply_optional!(self, base, recurse:tracing);
        apply_optional!(self, base, recurse:printing);

        if let Some(ws) = &self.watchpoints {
            base.watchpoints.extend(ws);
        }
    }
}

#[derive(Clone, Debug, Default, Deserialize)]
pub struct TraceOptsBuilder {
    pub on: Option<bool>,
    pub tracefmt_version: Option<TracefmtVersion>,
}

impl TraceOptsBuilder {
    pub fn apply(&self, base: &mut TraceOpts) {
        apply_optional!(self, base, field:on);
        apply_optional!(self, base, field:tracefmt_version);
    }
}

#[derive(Clone, Debug, Default, Deserialize)]
pub struct ModelOptsBuilder {
    pub on: Option<bool>,
    pub promote_non_shareable: Option<bool>,
    pub ignore_vmid: Option<bool>,
    pub allow_races: Option<bool>,
}

impl ModelOptsBuilder {
    pub fn apply(&self, base: &mut ModelOpts) {
        apply_optional!(self, base, field:on);
        apply_optional!(self, base, field:promote_non_shareable);
        apply_optional!(self, base, field:ignore_vmid);
        apply_optional!(self, base, field:allow_races);
    }
}

#[derive(Clone, Debug, Default, Deserialize)]
pub struct PrintOptsBuilder {
    pub on: Option<bool>,
    pub dump: Option<bool>,
    pub diff: Option<bool>,
    pub condense: Option<bool>,
}

impl PrintOptsBuilder {
    pub fn apply(&self, base: &mut PrintOpts) {
        apply_optional!(self, base, field:on);
        apply_optional!(self, base, field:dump);
        apply_optional!(self, base, field:diff);
        apply_optional!(self, base, field:condense);
    }
}

/// Create a `ConfigBuilder` out of a partial JSON
pub fn make_config_builder(config: &str) -> serde_json::Result<ConfigBuilder> {
    serde_json::from_str::<ConfigBuilder>(config)
}
