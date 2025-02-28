use crate::shim::*;

use crate::c_api;

#[cfg(not(feature = "std"))]
use crate::ghost_driver;

use crate::state::{configure, init_model, update_model_with_step};
use crate::transitions::{Operation::*, *};

#[cfg(feature = "alloc")]
use crate::allocator::init_heap_alloc;

/// Converters between bindgen c_api types and transition data
mod c_api_translation {
    use crate::shim::*;

    use crate::c_api;
    use crate::transitions::*;

    impl<'t> Into<SrcLoc<'t>> for &'t SrcLoc<'t> {
        fn into(self) -> SrcLoc<'t> {
            SrcLoc {
                file: self.file,
                func: self.func,
                lineno: self.lineno,
            }
        }
    }

    impl<'t> Into<SrcLoc<'t>> for &'t c_api::src_loc {
        fn into(self) -> SrcLoc<'t> {
            unsafe {
                SrcLoc::new(
                    CStr::from_ptr(self.file).to_str().unwrap(),
                    CStr::from_ptr(self.func).to_str().unwrap(),
                    self.lineno as u64,
                )
            }
        }
    }

    impl Into<MemOrder> for c_api::memory_order_t {
        fn into(self) -> MemOrder {
            match self {
                c_api::WMO_plain => MemOrder::Plain,
                c_api::WMO_release => MemOrder::Release,
                _ => panic!("bad mem_order_t"),
            }
        }
    }

    impl Into<Arm_DxB_Kind> for c_api::dxb_kind {
        fn into(self) -> Arm_DxB_Kind {
            match self {
                c_api::DxB_ish => Arm_DxB_Kind::Arm_DxB_ISH,
                c_api::DxB_ishst => Arm_DxB_Kind::Arm_DxB_ISHST,
                c_api::DxB_nsh => Arm_DxB_Kind::Arm_DxB_ISHST,
                _ => panic!("bad dxb_kind"),
            }
        }
    }

    impl Into<PhysAddr> for u64 {
        fn into(self) -> PhysAddr {
            PhysAddr(self)
        }
    }

    impl Into<Lock> for u64 {
        fn into(self) -> Lock {
            Lock(self)
        }
    }

    impl<'t> Into<RegName<'t>> for &'t str {
        fn into(self) -> RegName<'t> {
            RegName(self)
        }
    }
}

/// Configure Casemate via JSON-encoded config
///
/// The default serves as a good example config:
/// {
///     "model": {
///         "on":true,
///         "promote_non_shareable":false,
///         "ignore_vmid":false,
///         "allow_races":false
///     },
///     "tracing": {
///         "on":true,
///         "tracefmt_version":"V0"
///     },
///     "printing": {
///         "on":true,
///         "dump":false,
///         "diff":false,
///         "condense":true
///     },
///     "watchpoints":[]
/// }
#[no_mangle]
pub fn casemate_config(config: *const ::core::ffi::c_char) -> ::core::ffi::c_int {
    let s = unsafe { CStr::from_ptr(config) }
        .to_str()
        .expect("malformed config string");
    match configure(s) {
        Ok(()) => 0,
        Err(e) => {
            warn!("{}", e);
            -1
        }
    }
}

/// Initialise the Casemate internal state
///
/// This sets up both the initial Model state and its layers
/// but also the allocator
///
/// `sm_virt` and `sm_size` are the start and size-in-bytes
/// of the area to initialise the allocator
#[no_mangle]
pub fn casemate_initialize_model(
    phys: u64,
    size: u64,
    #[cfg_attr(not(feature = "alloc"), allow(unused_variables))] sm_virt: *mut ::core::ffi::c_void,
    #[cfg_attr(not(feature = "alloc"), allow(unused_variables))] sm_size: u64,
) -> ::core::ffi::c_int {
    #[cfg(feature = "alloc")]
    init_heap_alloc(sm_virt as *mut u8, sm_size as usize);
    init_model(phys, size);
    0
}

#[no_mangle]
pub fn casemate_watch_location(_loc: u64) -> ::core::ffi::c_int {
    0
}

#[no_mangle]
pub fn casemate_initialize_driver(#[allow(unused_variables)] driver: *mut c_api::ghost_driver) {
    #[cfg(not(feature = "std"))]
    ghost_driver::sync_ghost_driver(driver);
}

#[no_mangle]
pub fn __casemate_model_step_write(
    tid: u64,
    src_loc: c_api::src_loc,
    mo: c_api::memory_order_t,
    phys: u64,
    val: u64,
) {
    update_model_with_step(make_trans_builder!(
        tid,
        src_loc,
        Write(phys.into(), mo.into(), val)
    ))
}

#[no_mangle]
pub fn __casemate_model_step_read(tid: u64, src_loc: c_api::src_loc, phys: u64, val: u64) {
    update_model_with_step(make_trans_builder!(tid, src_loc, Read(phys.into(), val)))
}

#[no_mangle]
pub fn __casemate_model_step_dsb(tid: u64, src_loc: c_api::src_loc, kind: c_api::dxb_kind) {
    update_model_with_step(make_trans_builder!(
        tid,
        src_loc,
        Barrier(BarrierKind::Arm_DSB(kind.into()))
    ))
}

#[no_mangle]
pub fn __casemate_model_step_isb(tid: u64, src_loc: c_api::src_loc) {
    update_model_with_step(make_trans_builder!(
        tid,
        src_loc,
        Barrier(BarrierKind::Arm_ISB)
    ))
}

#[no_mangle]
pub fn __casemate_model_step_tlbi_reg(
    tid: u64,
    src_loc: c_api::src_loc,
    kind: c_api::tlbi_kind,
    value: u64,
) {
    let tlbi = {
        use TLBIKind::*;
        match kind {
            c_api::TLBI_vale2is => Arm_TLBI_vale2is(value),
            c_api::TLBI_vae2is => Arm_TLBI_vae2is(value),
            c_api::TLBI_ipas2e1is => Arm_TLBI_ipas2e1is(value),
            c_api::TLBI_vmalls12e1
            | c_api::TLBI_vmalls12e1is
            | c_api::TLBI_vmalle1is
            | c_api::TLBI_alle1is
            | c_api::TLBI_vmalle1 => panic!("bad tlbi_kind: used non-reg TLBI in tlbi_reg"),
            _ => panic!("bad tlbi_kind: unknown kind"),
        }
    };
    update_model_with_step(make_trans_builder!(tid, src_loc, TLBInval(tlbi)))
}

#[no_mangle]
pub fn __casemate_model_step_tlbi(tid: u64, src_loc: c_api::src_loc, kind: c_api::tlbi_kind) {
    let tlbi = {
        use TLBIKind::*;
        match kind {
            c_api::TLBI_vmalls12e1 => Arm_TLBI_vmalls12e1,
            c_api::TLBI_vmalls12e1is => Arm_TLBI_vmalls12e1is,
            c_api::TLBI_vmalle1is => Arm_TLBI_vmalle1is,
            c_api::TLBI_alle1is => Arm_TLBI_alle1is,
            c_api::TLBI_vmalle1 => Arm_TLBI_vmalle1,

            c_api::TLBI_vale2is | c_api::TLBI_vae2is | c_api::TLBI_ipas2e1is => {
                panic!("bad tlbi_kind: register TLBI used in non-reg tlbi")
            }

            _ => panic!("bad tlbi_kind: unknown kind"),
        }
    };
    update_model_with_step(make_trans_builder!(tid, src_loc, TLBInval(tlbi)))
}

#[no_mangle]
pub fn __casemate_model_step_msr(
    tid: u64,
    src_loc: c_api::src_loc,
    sysreg: *const ::core::ffi::c_char,
    val: u64,
) {
    let s = unsafe { CStr::from_ptr(sysreg) }
        .to_str()
        .expect("malformed register name");
    update_model_with_step(make_trans_builder!(tid, src_loc, RegWrite(s.into(), val)))
}

#[no_mangle]
pub fn __casemate_model_step_hint(
    tid: u64,
    src_loc: c_api::src_loc,
    kind: c_api::ghost_hint_kind,
    location: u64,
    value: u64,
) {
    let hint = {
        use HintKind::*;
        match kind {
            c_api::GHOST_HINT_SET_ROOT_LOCK => Set_Root_Lock {
                root: location.into(),
                lock: value.into(),
            },
            c_api::GHOST_HINT_SET_OWNER_ROOT => Associate_With_Root {
                loc: location.into(),
                root: value.into(),
            },
            c_api::GHOST_HINT_RELEASE_TABLE => Release_Tree {
                root: location.into(),
            },
            c_api::GHOST_HINT_SET_PTE_THREAD_OWNER => Set_Thread_Owner {
                loc: location.into(),
                tid: value as u8,
            },
            _ => panic!("bad hint kind: unknown kind"),
        }
    };
    update_model_with_step(make_trans_builder!(tid, src_loc, Hint(hint)))
}

#[no_mangle]
pub fn __casemate_model_step_init(tid: u64, src_loc: c_api::src_loc, location: u64, size: u64) {
    update_model_with_step(make_trans_builder!(
        tid,
        src_loc,
        InitMem(location.into(), size)
    ))
}

#[no_mangle]
pub fn __casemate_model_step_memset(
    tid: u64,
    src_loc: c_api::src_loc,
    location: u64,
    value: u64,
    size: u64,
) {
    update_model_with_step(make_trans_builder!(
        tid,
        src_loc,
        MemSet {
            loc: location.into(),
            size: size,
            val: value
        }
    ))
}

#[no_mangle]
pub fn __casemate_model_step_lock(tid: u64, src_loc: c_api::src_loc, address: u64) {
    update_model_with_step(make_trans_builder!(
        tid,
        src_loc,
        LockAcquire(address.into())
    ))
}

#[no_mangle]
pub fn __casemate_model_step_unlock(tid: u64, src_loc: c_api::src_loc, address: u64) {
    update_model_with_step(make_trans_builder!(
        tid,
        src_loc,
        LockRelease(address.into())
    ))
}
