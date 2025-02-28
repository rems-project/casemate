#![allow(non_camel_case_types, dead_code)]
use crate::shim::*;

#[derive(Debug, Clone)]
pub struct PhysAddr(pub u64);

impl fmt::Display for PhysAddr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(Debug, Clone)]
pub struct RegName<'t>(pub &'t str);

impl<'t> fmt::Display for RegName<'t> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(Debug, Clone)]
pub struct Lock(pub u64);

#[derive(Debug, Clone)]
pub struct SrcLoc<'t> {
    pub file: Option<&'t str>,
    pub func: Option<&'t str>,
    pub lineno: Option<u64>,
}

impl<'t> SrcLoc<'t> {
    pub fn new(file: &'t str, func: &'t str, lineno: u64) -> Self {
        let file = Some(file);
        let func = Some(func);
        let lineno = Some(lineno);
        Self { file, func, lineno }
    }

    /// Parse a string encoding a [`SrcLoc`]
    ///
    /// For a format "file name:lineno"
    /// `func` is always None
    pub fn from_str(s: &'t str) -> Self {
        let (file, func, lineno) = {
            if let Some(i) = s.find(':') {
                let (f, n): (&str, &str) = s.split_at(i);
                (Some(f), None, n.parse().ok())
            } else {
                (Some(s), None, None)
            }
        };

        Self { file, func, lineno }
    }
}

impl<'t> fmt::Display for SrcLoc<'t> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:", self.file.unwrap_or("???"))?;
        if let Some(n) = self.lineno {
            write!(f, "{}", n)
        } else {
            write!(f, "???")
        }
    }
}

#[derive(Debug, Clone)]
pub struct TransitionInfo<'t> {
    pub tid: u64,
    pub seq_id: u64,
    pub src_loc: SrcLoc<'t>,
}

#[derive(Debug, Copy, Clone)]
pub enum MemOrder {
    Plain,
    Release,
}

impl fmt::Display for MemOrder {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Plain => write!(f, "plain"),
            Self::Release => write!(f, "release"),
        }
    }
}

#[derive(Debug, Clone)]
pub enum Arm_DxB_Kind {
    Arm_DxB_ISH,
    Arm_DxB_ISHST,
    Arm_DxB_NSH,
}

impl fmt::Display for Arm_DxB_Kind {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Arm_DxB_Kind::Arm_DxB_ISH => write!(f, "ish"),
            Arm_DxB_Kind::Arm_DxB_ISHST => write!(f, "ishst"),
            Arm_DxB_Kind::Arm_DxB_NSH => write!(f, "nsh"),
        }
    }
}

#[derive(Debug, Clone)]
pub enum BarrierKind {
    Arm_DMB(Arm_DxB_Kind),
    Arm_DSB(Arm_DxB_Kind),
    Arm_ISB,
}

impl fmt::Display for BarrierKind {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            BarrierKind::Arm_DMB(_) => write!(f, "dmb"),
            BarrierKind::Arm_DSB(_) => write!(f, "dsb"),
            BarrierKind::Arm_ISB => write!(f, "isb"),
        }
    }
}

#[derive(Debug, Clone)]
pub enum TLBIKind {
    Arm_TLBI_vmalls12e1,
    Arm_TLBI_vmalls12e1is,
    Arm_TLBI_vmalle1is,
    Arm_TLBI_alle1is,
    Arm_TLBI_vmalle1,
    Arm_TLBI_vale2is(u64),
    Arm_TLBI_vae2is(u64),
    Arm_TLBI_ipas2e1is(u64),
}

impl fmt::Display for TLBIKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use TLBIKind::*;
        match self {
            Arm_TLBI_vmalls12e1 => write!(f, "TLBI_vmalls12e1"),
            Arm_TLBI_vmalls12e1is => write!(f, "TLBI_vmalls12e1is"),
            Arm_TLBI_vmalle1is => write!(f, "TLBI_vmalle1is"),
            Arm_TLBI_alle1is => write!(f, "TLBI_alle1is"),
            Arm_TLBI_vmalle1 => write!(f, "TLBI_vmalle1"),
            Arm_TLBI_vale2is(_) => write!(f, "TLBI_vale2is"),
            Arm_TLBI_vae2is(_) => write!(f, "TLBI_vae2is"),
            Arm_TLBI_ipas2e1is(_) => write!(f, "TLBI_ipas2e1is"),
        }
    }
}

#[derive(Debug, Clone)]
pub enum HintKind {
    Set_Root_Lock { root: PhysAddr, lock: Lock },
    Associate_With_Root { loc: PhysAddr, root: PhysAddr },
    Release_Tree { root: PhysAddr },
    Set_Thread_Owner { loc: PhysAddr, tid: u8 },
}

impl fmt::Display for HintKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use HintKind::*;
        match self {
            Set_Root_Lock { root: _, lock: _ } => write!(f, "set_root_lock"),
            Associate_With_Root { loc: _, root: _ } => write!(f, "set_owner_root"),
            Release_Tree { root: _ } => write!(f, "release_table"),
            Set_Thread_Owner { loc: _, tid: _ } => write!(f, "set_pte_thread_owner"),
        }
    }
}

#[derive(Debug, Clone)]
pub enum Operation<'t> {
    // h/w operations
    Write(PhysAddr, MemOrder, u64),
    Read(PhysAddr, u64),
    Barrier(BarrierKind),
    TLBInval(TLBIKind),
    RegWrite(RegName<'t>, u64),
    RegRead(RegName<'t>, u64),

    // abstract steps
    InitMem(PhysAddr, u64),
    MemSet { loc: PhysAddr, size: u64, val: u64 },
    LockAcquire(PhysAddr),
    LockRelease(PhysAddr),

    // Overlay-specific hints
    Hint(HintKind),
}

#[derive(Debug, Clone)]
pub struct Transition<'t> {
    pub info: TransitionInfo<'t>,
    pub op: Operation<'t>,
}

#[macro_export]
macro_rules! make_transition {
    ($tid:expr,$src_loc:expr,$op:expr) => {
        $crate::transitions::Transition {
            info: $crate::transitions::TransitionInfo {
                tid: $tid,
                seq_id: 0,
                src_loc: (&$src_loc).into(),
            },
            op: $op,
        }
    };
}

macro_rules! make_trans_builder {
    ($tid:expr,$src_loc:expr,$op:expr) => {
        || $crate::transitions::make_transition!($tid, $src_loc, $op)
    };
}

pub(crate) use make_trans_builder;
pub(crate) use make_transition;
