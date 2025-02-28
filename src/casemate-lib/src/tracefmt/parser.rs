use crate::shim::*;

use crate::transitions::*;

use crate::tracefmt::sexp::{Sexp, SexpParseError};

#[derive(Clone, Debug)]
pub enum TraceParseError {
    /// Inner error from badly formatted sexprs
    BadSexp(SexpParseError),

    /// Failed to parse an integer
    BadNum(num::ParseIntError),

    /// Expected a keyword (kw EXPR)
    /// but got (other_kw EXPR)
    UnexpectedKw(&'static str, String),

    BadEventFormat,
}

impl fmt::Display for TraceParseError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::BadSexp(e) => {
                write!(f, "bad s-exp: {e}")
            }
            Self::BadNum(e) => {
                write!(f, "bad numeric literal: {e}")
            }
            Self::UnexpectedKw(expected, got) => {
                write!(
                    f,
                    "unexpected keyword, expected '{expected}', but got '{got}'"
                )
            }
            Self::BadEventFormat => {
                write!(f, "bad event format")
            }
        }
    }
}

impl StdError for TraceParseError {}

fn expect_item<'t>(elems: &mut slice::Iter<'t, Sexp>) -> Result<&'t Sexp, TraceParseError> {
    elems.next().ok_or(TraceParseError::BadEventFormat)
}

fn expect_item_value<'t>(elems: &mut slice::Iter<'t, Sexp>) -> Result<&'t String, TraceParseError> {
    let s = expect_item(elems)?;
    s.expect_value().ok_or(TraceParseError::BadEventFormat)
}

fn expect_item_keyword<'t>(
    elems: &mut slice::Iter<'t, Sexp>,
    kw: &'static str,
) -> Result<&'t Sexp, TraceParseError> {
    let s = expect_item(elems)?;
    match s {
        Sexp::Val(_) => Ok(s),
        Sexp::List(vs) => {
            if vs.len() == 2 {
                let mut drain = vs.iter();
                let first = expect_item_value(&mut drain)?;
                let second = expect_item(&mut drain)?;

                if first == kw {
                    Ok(second)
                } else {
                    Err(TraceParseError::UnexpectedKw(kw, first.to_string()))
                }
            } else {
                Err(TraceParseError::BadEventFormat)
            }
        }
    }
}

fn try_parse_u64<'t>(s: &'t str) -> Result<u64, TraceParseError> {
    if s.starts_with("0x") {
        u64::from_str_radix(&s[2..], 16).map_err(|e| TraceParseError::BadNum(e))
    } else {
        s.parse().map_err(|e| TraceParseError::BadNum(e))
    }
}

fn expect_u64<'t>(s: &'t Sexp) -> Result<u64, TraceParseError> {
    let v = s.expect_value().ok_or(TraceParseError::BadEventFormat)?;
    try_parse_u64(v)
}

mod converters {
    use super::TraceParseError;
    use crate::shim::*;
    use crate::transitions::*;

    pub(super) fn memorder<'t>(s: &String) -> Result<MemOrder, TraceParseError> {
        match s.to_ascii_lowercase().as_str() {
            "plain" => Ok(MemOrder::Plain),
            "release" => Ok(MemOrder::Release),
            _ => Err(TraceParseError::BadEventFormat),
        }
    }

    pub(super) fn dxb_kind<'t>(s: &String) -> Result<Arm_DxB_Kind, TraceParseError> {
        match s.to_ascii_lowercase().as_str() {
            "ish" => Ok(Arm_DxB_Kind::Arm_DxB_ISH),
            "nsh" => Ok(Arm_DxB_Kind::Arm_DxB_NSH),
            "ishst" => Ok(Arm_DxB_Kind::Arm_DxB_ISHST),
            _ => Err(TraceParseError::BadEventFormat),
        }
    }

    pub(super) fn hint_kind_cont<'t>(
        s: &'t String,
    ) -> Result<impl Fn(u64, u64) -> Result<HintKind, TraceParseError> + use<'t>, TraceParseError>
    {
        Ok(|loc: u64, val: u64| {
            let kind = match s.to_ascii_lowercase().as_str() {
                "set_root_lock" => HintKind::Set_Root_Lock {
                    root: loc.into(),
                    lock: val.into(),
                },
                "set_owner_root" => HintKind::Associate_With_Root {
                    loc: loc.into(),
                    root: val.into(),
                },
                "release_table" => HintKind::Release_Tree { root: loc.into() },
                "set_pte_thread_owner" => HintKind::Set_Thread_Owner {
                    loc: loc.into(),
                    tid: val as u8,
                },
                _ => return Err(TraceParseError::BadEventFormat),
            };
            Ok(kind)
        })
    }

    pub(super) fn _u64<'t>(s: &'t String) -> Result<u64, TraceParseError> {
        super::try_parse_u64(s)
    }

    pub(super) fn _u8<'t>(s: &'t String) -> Result<u8, TraceParseError> {
        // u8s in src cannot be hex so just use parse()
        s.parse().map_err(|_err| TraceParseError::BadEventFormat)
    }
}

#[allow(dead_code)]
fn expect_item_value_conv<'t, F, T>(
    elems: &mut slice::Iter<'t, Sexp>,
    f: F,
) -> Result<T, TraceParseError>
where
    F: FnOnce(&'t String) -> Result<T, TraceParseError>,
{
    let s = expect_item_value(elems)?;
    f(s)
}

fn expect_item_kw_value_conv<'t, F, T>(
    elems: &mut slice::Iter<'t, Sexp>,
    kw: &'static str,
    f: F,
) -> Result<T, TraceParseError>
where
    F: FnOnce(&'t String) -> Result<T, TraceParseError>,
{
    let sexp = expect_item_keyword(elems, kw)?;
    let s = sexp.expect_value().ok_or(TraceParseError::BadEventFormat)?;
    f(s)
}

fn parse_operation<'t>(
    name: &'t String,
    args: &mut slice::Iter<'t, Sexp>,
) -> Result<Operation<'t>, TraceParseError> {
    let op = {
        match name.to_ascii_lowercase().as_str() {
            "mem-write" => {
                let mo = expect_item_kw_value_conv(args, "mem-order", converters::memorder)?;
                let addr = expect_item_kw_value_conv(args, "address", converters::_u64)?;
                let val = expect_item_kw_value_conv(args, "value", converters::_u64)?;
                Operation::Write(addr.into(), mo, val)
            }
            "mem-read" => {
                let addr = expect_item_kw_value_conv(args, "address", converters::_u64)?;
                let val = expect_item_kw_value_conv(args, "value", converters::_u64)?;
                Operation::Read(addr.into(), val)
            }
            "mem-init" => {
                let addr = expect_item_kw_value_conv(args, "address", converters::_u64)?;
                let size: u64 = expect_item_kw_value_conv(args, "size", converters::_u64)?;
                Operation::InitMem(addr.into(), size)
            }
            "mem-set" => {
                let addr = expect_item_kw_value_conv(args, "address", converters::_u64)?;
                let size: u64 = expect_item_kw_value_conv(args, "size", converters::_u64)?;
                let val: u64 = expect_item_kw_value_conv(args, "value", converters::_u8)? as u64;
                Operation::MemSet {
                    loc: addr.into(),
                    size,
                    val,
                }
            }
            "barrier" => {
                let name = expect_item_value(args)?;
                match name.to_ascii_lowercase().as_str() {
                    "isb" => Operation::Barrier(BarrierKind::Arm_ISB),
                    "dsb" => {
                        let kind = expect_item_kw_value_conv(args, "kind", converters::dxb_kind)?;
                        Operation::Barrier(BarrierKind::Arm_DSB(kind))
                    }
                    _ => return Err(TraceParseError::BadEventFormat),
                }
            }
            "tlbi" => {
                let name = expect_item_value(args)?;
                let tlbi = {
                    use TLBIKind::*;
                    match name.to_ascii_lowercase().as_str() {
                        "vmalls12e1" => Arm_TLBI_vmalls12e1,
                        "vmalls12e1is" => Arm_TLBI_vmalls12e1is,
                        "vmalle1is" => Arm_TLBI_vmalle1is,
                        "alle1is" => Arm_TLBI_alle1is,
                        "vmalle1" => Arm_TLBI_vmalle1,
                        "vale2is" => Arm_TLBI_vale2is(expect_item_kw_value_conv(
                            args,
                            "value",
                            converters::_u64,
                        )?),
                        "vae2is" => Arm_TLBI_vae2is(expect_item_kw_value_conv(
                            args,
                            "value",
                            converters::_u64,
                        )?),
                        "ipas2e1is" => Arm_TLBI_ipas2e1is(expect_item_kw_value_conv(
                            args,
                            "value",
                            converters::_u64,
                        )?),
                        _ => return Err(TraceParseError::BadEventFormat),
                    }
                };
                Operation::TLBInval(tlbi)
            }
            "sysreg-write" => {
                let reg: RegName<'t> =
                    expect_item_kw_value_conv(args, "sysreg", |s| Ok(RegName(s.as_str())))?;
                let val = expect_item_kw_value_conv(args, "value", converters::_u64)?;
                Operation::RegWrite(reg, val)
            }
            "hint" => {
                let cont = expect_item_kw_value_conv(args, "kind", converters::hint_kind_cont)?;
                let loc = expect_item_kw_value_conv(args, "location", converters::_u64)?;
                let val = expect_item_kw_value_conv(args, "value", converters::_u64)?;
                Operation::Hint(cont(loc, val)?)
            }
            "lock" => {
                let addr = expect_item_kw_value_conv(args, "address", converters::_u64)?;
                Operation::LockAcquire(addr.into())
            }
            "unlock" => {
                let addr = expect_item_kw_value_conv(args, "address", converters::_u64)?;
                Operation::LockRelease(addr.into())
            }
            _ => return Err(TraceParseError::BadEventFormat),
        }
    };
    Ok(op)
}

pub fn parse_trace_sexpevent<'t>(sexp: &'t Sexp) -> Result<Transition<'t>, TraceParseError> {
    match sexp {
        Sexp::List(elems) => {
            let mut elems: slice::Iter<'t, Sexp> = elems.iter();
            let name = expect_item_value(&mut elems)?;
            let seq_id = expect_item_keyword(&mut elems, "id")?;
            let tid = expect_item_keyword(&mut elems, "tid")?;
            let op = parse_operation(name, &mut elems)?;
            let src_loc = expect_item_keyword(&mut elems, "src")?
                .expect_value()
                .ok_or(TraceParseError::BadEventFormat)?;

            // any remaining?
            if elems.count() > 0 {
                return Err(TraceParseError::BadEventFormat);
            }

            let info = TransitionInfo {
                tid: expect_u64(tid)?,
                seq_id: expect_u64(seq_id)?,
                src_loc: SrcLoc::from_str(src_loc),
            };

            Ok(Transition { info, op })
        }
        Sexp::Val(_) => Err(TraceParseError::BadEventFormat),
    }
}
