//! Defines the structured-output [`LayerFormat`] trait
//! and utilities for pretty-printing the model and its layers.
//!
//! See [`format_layer`] for the top-level formatting function

use crate::shim::*;

use crate::config::Config;
use crate::model::Ctx;

mod impls;

#[derive(Copy, Clone, Debug, Default)]
pub struct LayerFormatterLayout {
    indent: bool,
}

impl LayerFormatterLayout {
    pub fn new(indent: bool) -> Self {
        Self { indent }
    }
}

/// Running state
#[derive(Copy, Clone, Debug, Default)]
struct LayerFormatterState {
    at_newline: bool,
}

pub struct LayerFormatter<'cfg, 'f> {
    /// Reference back to Casemate configuration
    pub cfg: &'cfg Config,

    /// Inner formatter
    fmt: &'f mut (dyn fmt::Write + 'f),

    /// Running state of this and parents' layoutting
    /// (at newline, current indent, etc.)
    state: LayerFormatterState,

    /// Layouting to perform for this [`LayerFormatter`]
    layout: LayerFormatterLayout,
}

impl<'cfg, 'f> fmt::Debug for LayerFormatter<'cfg, 'f> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("LayerFormatter")
            .field("cfg", self.cfg)
            .field("state", &self.state)
            .field("layout", &self.layout)
            .finish()
    }
}

impl<'cfg, 'f> LayerFormatter<'cfg, 'f> {
    pub fn new(cfg: &'cfg Config, fmt: &'f mut (dyn fmt::Write + 'f)) -> Self {
        Self {
            cfg,
            fmt,
            state: LayerFormatterState::default(),
            layout: LayerFormatterLayout::default(),
        }
    }

    #[allow(dead_code)]
    pub fn wrap_fmt<'a, 'b, F>(&'a mut self, wrapper: F) -> LayerFormatter<'cfg, 'b>
    where
        'a: 'b,
        F: FnOnce(&'a mut (dyn fmt::Write + 'a)) -> &'b mut (dyn fmt::Write + 'b),
    {
        LayerFormatter {
            cfg: self.cfg,
            fmt: wrapper(self.fmt),
            state: self.state,
            layout: self.layout,
        }
    }

    pub fn wrap_layout<'a>(&'a mut self, layout: LayerFormatterLayout) -> LayerFormatter<'cfg, 'a> {
        let st = self.state.clone();
        LayerFormatter {
            cfg: self.cfg,
            fmt: self,
            state: st,
            layout,
        }
    }

    pub fn indented<'a, L>(&'a mut self, inner: &L) -> fmt::Result
    where
        L: LayerFormat,
    {
        let mut wrapper: LayerFormatter<'cfg, '_> =
            self.wrap_layout(LayerFormatterLayout::new(true));
        inner.fmt_layer(&mut wrapper)?;
        Ok(())
    }
}

impl<'cfg, 'f> fmt::Write for LayerFormatter<'cfg, 'f> {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        for line in s.split_inclusive('\n') {
            if self.state.at_newline && self.layout.indent {
                self.fmt.write_str("    ")?;
            }
            self.fmt.write_str(line)?;
            self.state.at_newline = line.ends_with('\n');
        }
        Ok(())
    }
}

/// A trait for a structured Display-like output
pub trait LayerFormat {
    fn fmt_layer(&self, f: &mut LayerFormatter<'_, '_>) -> fmt::Result;
}

pub fn format_layer<L>(ctx: &Ctx, layer: &L) -> String
where
    L: LayerFormat,
{
    let mut buf = String::new();
    let mut fmt = LayerFormatter::new(ctx.config, &mut buf);
    LayerFormat::fmt_layer(layer, &mut fmt).expect("???");
    buf
}
