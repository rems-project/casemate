#![allow(warnings)]

pub const CASEMATE_VERSION: &[u8; 6] = b"2.1.0\0";
pub type write_byte_cb = ::core::option::Option<unsafe extern "C" fn(b: u8) -> ::core::ffi::c_int>;
pub type abort_cb = ::core::option::Option<unsafe extern "C" fn(msg: *const ::core::ffi::c_char)>;
pub type trace_cb =
    ::core::option::Option<unsafe extern "C" fn(record: *const ::core::ffi::c_char)>;
#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct ghost_driver {
    pub writeb: write_byte_cb,
    pub abort: abort_cb,
    pub trace: trace_cb,
}
pub const WMO_plain: memory_order_t = 0;
pub const WMO_release: memory_order_t = 1;
pub type memory_order_t = ::core::ffi::c_uint;
pub const TLBI_OP_STAGE1: sm_tlbi_op_stage = 1;
pub const TLBI_OP_STAGE2: sm_tlbi_op_stage = 2;
pub const TLBI_OP_BOTH_STAGES: sm_tlbi_op_stage = 3;
pub type sm_tlbi_op_stage = ::core::ffi::c_uint;
pub const TLBI_OP_BY_ALL: sm_tlbi_op_method_kind = 0;
pub const TLBI_OP_BY_INPUT_ADDR: sm_tlbi_op_method_kind = 1;
pub const TLBI_OP_BY_ADDR_SPACE: sm_tlbi_op_method_kind = 2;
pub const TLBI_OP_BY_VA: sm_tlbi_op_method_kind = 1;
pub const TLBI_OP_BY_IPA: sm_tlbi_op_method_kind = 1;
pub const TLBI_OP_BY_VMID: sm_tlbi_op_method_kind = 2;
pub const TLBI_OP_BY_ASID: sm_tlbi_op_method_kind = 2;
pub type sm_tlbi_op_method_kind = ::core::ffi::c_uint;
pub const TLBI_REGIME_EL10: sm_tlbi_op_regime_kind = 1;
pub const TLBI_REGIME_EL2: sm_tlbi_op_regime_kind = 2;
pub type sm_tlbi_op_regime_kind = ::core::ffi::c_uint;
pub const TLBI_vmalls12e1: tlbi_kind = 0;
pub const TLBI_vmalls12e1is: tlbi_kind = 1;
pub const TLBI_vmalle1is: tlbi_kind = 2;
pub const TLBI_alle1is: tlbi_kind = 3;
pub const TLBI_vmalle1: tlbi_kind = 4;
pub const TLBI_vale2is: tlbi_kind = 5;
pub const TLBI_vae2is: tlbi_kind = 6;
pub const TLBI_ipas2e1is: tlbi_kind = 7;
pub type tlbi_kind = ::core::ffi::c_uint;
pub const DxB_ish: dxb_kind = 0;
pub const DxB_ishst: dxb_kind = 1;
pub const DxB_nsh: dxb_kind = 2;
pub type dxb_kind = ::core::ffi::c_uint;
pub const BARRIER_DSB: barrier_kind = 0;
pub const BARRIER_ISB: barrier_kind = 1;
pub type barrier_kind = ::core::ffi::c_uint;
pub const GHOST_HINT_SET_ROOT_LOCK: ghost_hint_kind = 0;
pub const GHOST_HINT_SET_OWNER_ROOT: ghost_hint_kind = 1;
pub const GHOST_HINT_RELEASE_TABLE: ghost_hint_kind = 2;
pub const GHOST_HINT_SET_PTE_THREAD_OWNER: ghost_hint_kind = 3;
pub type ghost_hint_kind = ::core::ffi::c_uint;
#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct src_loc {
    pub file: *const ::core::ffi::c_char,
    pub func: *const ::core::ffi::c_char,
    pub lineno: ::core::ffi::c_int,
}
unsafe extern "C" {
    pub fn casemate_config(config: *const ::core::ffi::c_char) -> ::core::ffi::c_int;
    pub fn casemate_watch_location(loc: u64) -> ::core::ffi::c_int;
    pub fn casemate_initialize_driver(driver: *mut ghost_driver);
    pub fn casemate_initialize_model(
        phys: u64,
        size: u64,
        sm_virt: *mut ::core::ffi::c_void,
        sm_size: u64,
    ) -> ::core::ffi::c_int;
    pub fn casemate_cpu_id() -> u64;
    pub fn __casemate_model_step_write(
        tid: u64,
        src_loc: src_loc,
        mo: memory_order_t,
        phys: u64,
        val: u64,
    );
    pub fn __casemate_model_step_read(tid: u64, src_loc: src_loc, phys: u64, val: u64);
    pub fn __casemate_model_step_dsb(tid: u64, src_loc: src_loc, kind: dxb_kind);
    pub fn __casemate_model_step_isb(tid: u64, src_loc: src_loc);
    pub fn __casemate_model_step_tlbi_reg(tid: u64, src_loc: src_loc, kind: tlbi_kind, value: u64);
    pub fn __casemate_model_step_tlbi(tid: u64, src_loc: src_loc, kind: tlbi_kind);
    pub fn __casemate_model_step_msr(
        tid: u64,
        src_loc: src_loc,
        sysreg: *const ::core::ffi::c_char,
        val: u64,
    );
    pub fn __casemate_model_step_hint(
        tid: u64,
        src_loc: src_loc,
        kind: ghost_hint_kind,
        location: u64,
        value: u64,
    );
    pub fn __casemate_model_step_init(tid: u64, src_loc: src_loc, location: u64, size: u64);
    pub fn __casemate_model_step_memset(
        tid: u64,
        src_loc: src_loc,
        location: u64,
        value: u64,
        size: u64,
    );
    pub fn __casemate_model_step_lock(tid: u64, src_loc: src_loc, address: u64);
    pub fn __casemate_model_step_unlock(tid: u64, src_loc: src_loc, address: u64);
}
