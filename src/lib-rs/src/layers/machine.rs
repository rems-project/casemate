use crate::shim::*;

#[allow(unused_imports)]
use log;

use crate::base_model::Ctx;
use crate::collections::RegionMap;
use crate::errors;
use crate::steppable::{self, Layer, Steppable};
use crate::transitions;

#[derive(Debug, Clone, Default)]
pub struct RegMap {
    vttbr: u64,
    ttbr0_el2: u64,
}

impl fmt::Display for RegMap {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "")
    }
}

impl RegMap {
    fn get(&self, r: &str) -> Option<&u64> {
        match r {
            "vttbr_el2" => Some(&self.vttbr),
            "ttbr0_el2" => Some(&self.ttbr0_el2),
            _ => None,
        }
    }

    fn get_mut(&mut self, r: &str) -> Option<&mut u64> {
        match r {
            "vttbr_el2" => Some(&mut self.vttbr),
            "ttbr0_el2" => Some(&mut self.ttbr0_el2),
            _ => None,
        }
    }

    fn read(&self, r: &str) -> Option<u64> {
        self.get(r).cloned()
    }
}

make_diffable_struct!(RegMap, RegMapDiff; vttbr: u64, ttbr0_el2: u64);

#[derive(Debug, Clone, Default)]
pub struct Machine {
    regs: RegMap,
    mem: RegionMap<u64>,
}

impl Machine {
    pub fn new() -> Self {
        Self::default()
    }

    #[allow(dead_code)]
    pub fn read_mem(&self, a: u64) -> Option<u64> {
        self.mem.get(&a).cloned()
    }

    #[allow(dead_code)]
    pub fn read_reg(&self, r: &str) -> Option<u64> {
        self.regs.read(r)
    }
}

make_diffable_struct!(Machine, MachineDiff; regs: RegMap, mem: RegionMap<u64>);

impl Steppable for Machine {
    fn step<'t>(&mut self, ctx: &Ctx<'t>) -> steppable::Result<'t> {
        use errors::Error::*;
        use transitions::Operation::*;

        match &ctx.t.op {
            Write(a, _mo, v) => match self.mem.get_mut(&a.0) {
                Some(l) => {
                    *l = *v;
                }
                None => {
                    return Err(E11001_UninitialisedAccess { address: a.0 });
                }
            },
            Read(a, v) => match self.mem.get(&a.0) {
                Some(expected) => {
                    if *v != *expected {
                        return Err(E11000_BadRead {
                            address: a.0,
                            expected: *expected,
                            actual: *v,
                        });
                    }
                }
                None => {
                    return Err(E11001_UninitialisedAccess { address: a.0 });
                }
            },
            RegWrite(r, v) => {
                match self.regs.get_mut(r.0) {
                    Some(reg) => {
                        *reg = *v;
                    }
                    None => {
                        return Err(E11002_UnknownRegister { regname: r.0 });
                    }
                };
            }
            InitMem(a, size) => {
                let start = a.0;
                let nr_dwords = *size / 8;
                for i in 0..nr_dwords {
                    self.mem.insert(start + i * 8, 0);
                }
            }
            MemSet { loc, size, val } => {
                let start = loc.0;
                let nr_dwords = *size / 8;
                let byte: u8 = {
                    let v = (*val).try_into();
                    if v.is_err() {
                        return Err(E11003_BadMemSetArguments);
                    }
                    v.unwrap()
                };
                let dword: u64 = { iter::repeat_n(byte, 8).fold(0, |r, v| (r << 8) | (v as u64)) };
                for i in 0..nr_dwords {
                    self.mem.insert(start + i * 8, dword);
                }
            }
            _ => (),
        }
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
