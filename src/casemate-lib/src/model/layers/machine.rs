use crate::{shim::*, CasemateError};

#[allow(unused_imports)]
use log;

use diffable::Diffable;

use crate::collections::region_map::{ByteSpan, RegionMap};
use crate::errors::CodedError;
use crate::model::Ctx;
use crate::output::{LayerFormat, LayerFormatter};
use crate::steppable::{self, Layer, Steppable};
use crate::transitions;

#[derive(Debug, Clone, Default, Diffable)]
pub struct RegMap {
    vttbr: u64,
    ttbr0_el2: u64,
}

impl LayerFormat for RegMap {
    fn fmt_layer(&self, f: &mut LayerFormatter<'_, '_>) -> fmt::Result {
        write!(f, "vttbr:.....0x{:016x}\n", self.vttbr)?;
        write!(f, "ttbr0_el2: 0x{:016x}\n", self.ttbr0_el2)?;
        Ok(())
    }
}

impl RegMap {
    fn get(&self, r: &str) -> Option<&u64> {
        if r.eq_ignore_ascii_case("vttbr_el2") {
            Some(&self.vttbr)
        } else if r.eq_ignore_ascii_case("ttbr0_el2") {
            Some(&self.ttbr0_el2)
        } else {
            None
        }
    }

    fn get_mut(&mut self, r: &str) -> Option<&mut u64> {
        if r.eq_ignore_ascii_case("vttbr_el2") {
            Some(&mut self.vttbr)
        } else if r.eq_ignore_ascii_case("ttbr0_el2") {
            Some(&mut self.ttbr0_el2)
        } else {
            None
        }
    }

    fn read(&self, r: &str) -> Option<u64> {
        self.get(r).cloned()
    }
}

#[derive(Clone, Debug, Default, Diffable)]
pub struct Machine {
    regs: RegMap,
    mem: RegionMap<ByteSpan, u64>,
}

#[derive(Debug, Clone)]
pub enum MachineError {
    /// E11010: BadRead
    BadRead {
        address: u64,
        expected: u64,
        actual: u64,
    },

    /// E11020: UninitialisedAccess
    UninitialisedAccess { address: u64 },

    /// E11030: UnknownRegister
    UnknownRegister { regname: String },

    /// E11040: BadMemSetArguments
    BadMemSetArguments,
}

impl fmt::Display for MachineError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::BadRead {
                address: _,
                expected: _,
                actual: _,
            } => write!(f, "read mismatch"),
            Self::UninitialisedAccess { address: _ } => {
                write!(f, "attempted access to uninitialised location")
            }
            Self::UnknownRegister { regname } => {
                write!(f, "attempted access to uninitialised register ({regname})")
            }
            Self::BadMemSetArguments => write!(f, "incorrect memset arguments"),
        }
    }
}

impl StdError for MachineError {}

impl CodedError for MachineError {
    fn error_code(&self) -> &'static str {
        match self {
            Self::BadRead {
                address: _,
                expected: _,
                actual: _,
            } => "E11010",
            Self::UninitialisedAccess { address: _ } => "E11020",
            Self::UnknownRegister { regname: _ } => "E11030",
            Self::BadMemSetArguments => "E11040",
        }
    }
}

impl Machine {
    pub fn new() -> Self {
        Self::default()
    }

    #[allow(dead_code)]
    pub fn try_read_mem(&self, a: u64) -> Option<u64> {
        self.mem.get(&a).cloned()
    }

    #[allow(dead_code)]
    pub fn read_mem(&self, a: u64) -> Result<u64, MachineError> {
        self.try_read_mem(a).ok_or_else(|| MachineError::BadRead {
            address: a,
            expected: 0,
            actual: 0,
        })
    }

    #[allow(dead_code)]
    pub fn try_read_reg(&self, r: &str) -> Option<u64> {
        self.regs.read(r)
    }

    #[allow(dead_code)]
    pub fn read_reg(&self, r: &str) -> Result<u64, MachineError> {
        self.try_read_reg(r)
            .ok_or_else(|| MachineError::UnknownRegister {
                regname: r.to_string(),
            })
    }
}

impl Steppable for Machine {
    fn step<'t>(&mut self, ctx: &Ctx<'t>) -> steppable::Result<'t> {
        use transitions::Operation::*;
        use MachineError::*;

        match &ctx.t.op {
            Write(a, _mo, v) => match self.mem.get_mut(&a.0) {
                Some(l) => {
                    *l = *v;
                }
                None => {
                    return Err(UninitialisedAccess { address: a.0 })
                        .map_err(CasemateError::from_mach_err);
                }
            },
            Read(a, v) => match self.mem.get(&a.0) {
                Some(expected) => {
                    if *v != *expected {
                        return Err(BadRead {
                            address: a.0,
                            expected: *expected,
                            actual: *v,
                        })
                        .map_err(CasemateError::from_mach_err);
                    }
                }
                None => {
                    return Err(UninitialisedAccess { address: a.0 })
                        .map_err(CasemateError::from_mach_err);
                }
            },
            RegWrite(r, v) => {
                match self.regs.get_mut(r.0) {
                    Some(reg) => {
                        *reg = *v;
                    }
                    None => {
                        return Err(UnknownRegister {
                            regname: r.0.to_string(),
                        })
                        .map_err(CasemateError::from_mach_err);
                    }
                };
            }
            InitMem(a, size) => {
                let start = a.0;
                self.mem.insert_range(ByteSpan::new(start, *size), 0);
            }
            MemSet { loc, size, val } => {
                let start = loc.0;
                let byte: u8 = {
                    let v = (*val).try_into();
                    if v.is_err() {
                        return Err(BadMemSetArguments).map_err(CasemateError::from_mach_err);
                    }
                    v.unwrap()
                };
                self.mem
                    .insert_range(ByteSpan::new(start, *size), byte as u64);
            }
            _ => (),
        }
        Ok(())
    }
}

impl LayerFormat for Machine {
    fn fmt_layer(&self, f: &mut LayerFormatter<'_, '_>) -> fmt::Result {
        f.write_str("regs:\n")?;
        f.indented(&self.regs)?;
        f.write_str("mem:\n")?;
        f.indented(&self.mem)?;
        Ok(())
    }
}

impl Layer for Machine {
    fn label() -> &'static str {
        "machine"
    }

    fn parents() -> Vec<&'static str> {
        vec![]
    }
}
