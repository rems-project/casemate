module Z0 = Z
open Sexplib0.Sexp
open Coq_executable_sm

let of_sexp_error = Sexplib0.Sexp_conv.of_sexp_error

let int_of = Sexplib0.Sexp_conv.int_of_sexp
let u64_of sexp =
  match sexp with
  | Atom s ->
      (try Z0.of_string s with Invalid_argument _ ->
         of_sexp_error "bad u64" sexp)
  | _ -> of_sexp_error "bad u64" sexp

let mem_write_order = function
  | Atom "PLAIN"   -> WMO_plain
  | Atom "PAGE"    -> WMO_page
  | Atom "RELEASE" -> WMO_release
  | sexp -> of_sexp_error "bad mem-write mem-order" sexp

let tlbi_op = function
  | Atom "DALL"     -> TLBIOp_DALL
  | Atom "DASID"    -> TLBIOp_DASID
  | Atom "DVA"      -> TLBIOp_DVA
  | Atom "IALL"     -> TLBIOp_IALL
  | Atom "IASID"    -> TLBIOp_IASID
  | Atom "IVA"      -> TLBIOp_IVA
  | Atom "ALL"      -> TLBIOp_ALL
  | Atom "ASID"     -> TLBIOp_ASID
  | Atom "IPAS2"    -> TLBIOp_IPAS2
  | Atom "VAA"      -> TLBIOp_VAA
  | Atom "VA"       -> TLBIOp_VA
  | Atom "VMALL"    -> TLBIOp_VMALL
  | Atom "VMALLS12" -> TLBIOp_VMALLS12
  | Atom "RIPAS2"   -> TLBIOp_RIPAS2
  | Atom "RVAA"     -> TLBIOp_RVAA
  | Atom "RVA"      -> TLBIOp_RVA
  | Atom "RPA"      -> TLBIOp_RPA
  | Atom "PAALL"    -> TLBIOp_PAALL
  | sexp -> of_sexp_error "bad tlbi op" sexp

let tlbi_regime = function
  | Atom "EL3"  -> Regime_EL3
  | Atom "EL30" -> Regime_EL30
  | Atom "EL2"  -> Regime_EL2
  | Atom "EL20" -> Regime_EL20
  | Atom "EL10" -> Regime_EL10
  | sexp -> of_sexp_error "bad tlbi regime" sexp

let tlbi_level = function
  | Atom "ANY"  -> TLBILevel_Any 
  | Atom "LAST" -> TLBILevel_Last
  | sexp -> of_sexp_error "bad tlbi level" sexp

let tlbi_shareability = function
  | Atom "NSH" -> Shareability_NSH
  | Atom "ISH" -> Shareability_ISH
  | Atom "OSH" -> Shareability_OSH
  | sexp -> of_sexp_error "bad tlbi shareability" sexp

let msr_sysreg = function
  | Atom "VTTBR"    -> SYSREG_VTTBR
  | Atom "TTBR_EL2" -> SYSREG_TTBR_EL2
  | sexp -> of_sexp_error "bad msr sysreg" sexp

let hint_kind = function
  | Atom "SET_ROOT_LOCK"        -> GHOST_HINT_SET_ROOT_LOCK
  | Atom "SET_OWNER_ROOT"       -> GHOST_HINT_SET_OWNER_ROOT
  | Atom "RELEASE"              -> GHOST_HINT_RELEASE
  | Atom "SET_PTE_THREAD_OWNER" -> GHOST_HINT_SET_PTE_THREAD_OWNER
  | sexp -> of_sexp_error "bad lock hint kind" sexp

let lock_kind = function
  | Atom "LOCK"   -> LOCK
  | Atom "UNLOCK" -> UNLOCK
  | sexp -> of_sexp_error "bad lock kind" sexp

let dxb_of = function
  | Atom "NON_SHAREABLE"   -> MBReqDomain_Nonshareable
  | Atom "INNER_SHAREABLE" -> MBReqDomain_InnerShareable
  | Atom "OUTER_SHAREABLE" -> MBReqDomain_OuterShareable
  | Atom "FULL_SYSTEM"     -> MBReqDomain_FullSystem
  | sexp -> of_sexp_error "bad DxB domain" sexp

let barrier_of = function
  | List [Atom "DSB"; dxb] -> Barrier_DSB (dxb_of dxb)
  | List [Atom "DMB"; dxb] -> Barrier_DMB (dxb_of dxb)
  | Atom "ISB"   -> Barrier_ISB ()
  | Atom "SSBB"  -> Barrier_SSBB ()
  | Atom "PSSBB" -> Barrier_PSSBB ()
  | Atom "SB"    -> Barrier_SB ()
  | sexp -> of_sexp_error "bad BARRIER" sexp

let transition sexp =
  let id, thread, data = match sexp with
    | List [Atom "mem-write"; id; thread;
            List [Atom "mem-order"; order];
            List [Atom "address"; addr];
            List [Atom "value"; value]] ->
      id, thread, GSMDT_TRANS_MEM_WRITE {
        twd_mo = mem_write_order order;
        twd_phys_addr = u64_of addr;
        twd_val = u64_of value;
      }
    | List [Atom "mem-zalloc"; id; thread;
            List [Atom "address"; addr];
            List [Atom "size"; size]] ->
      id, thread, GSMDT_TRANS_MEM_ZALLOC {
        tzd_addr = u64_of addr;
        tzd_size = u64_of size
      }
    | List [Atom "mem-read"; id; thread;
            List [Atom "address"; addr];
            List [Atom "value"; value]] ->
      id, thread, GSMDT_TRANS_MEM_READ {
        trd_phys_addr = u64_of addr;
        trd_val = u64_of value
      }
    | List [Atom "barrier"; id; thread; barrier] ->
      id, thread, GSMDT_TRANS_BARRIER (barrier_of barrier)
    | List [Atom "tlbi"; id; thread;
         List [Atom "op"; op];
         List [Atom "regime"; regime];
         List [Atom "level"; level];
         List [Atom "address"; addr];
         List [Atom "share"; share] ] ->
      id, thread, GSMDT_TRANS_TLBI {
        tLBI_rec = {
          tLBIRecord_op = tlbi_op op;
          tLBIRecord_regime = tlbi_regime regime;
          tLBIRecord_level = tlbi_level level;
          tLBIRecord_address = u64_of addr
        };
        tLBI_shareability = tlbi_shareability share;
      }
    | List [Atom "msr"; id; thread;
            List [Atom "sysreg"; sysreg];
            List [Atom "value"; value]] ->
      id, thread, GSMDT_TRANS_MSR {
        tmd_sysreg = msr_sysreg sysreg;
        tmd_val = u64_of value;
      }
    | List [Atom "hint"; id; thread;
            List [Atom "kind"; kind];
            List [Atom "location"; loc];
            List [Atom "value"; value]] ->
      id, thread, GSMDT_TRANS_HINT {
        thd_hint_kind = hint_kind kind;
        thd_location = u64_of loc;
        thd_value = u64_of value;
      }
    | List [Atom "lock"; id; thread;
            List [Atom "kind"; kind];
            List [Atom "address"; addr]] ->
      id, thread, GSMDT_TRANS_LOCK {
        tld_kind = lock_kind kind;
        tld_addr = u64_of addr;
      }
    | sexp -> of_sexp_error "bad event" sexp
  in
  Some {
    gsmt_src_loc = None;
    gsmt_id = int_of id;
    gsmt_thread_identifier = int_of thread;
    gsmt_data = data
  }

let of_line line = Sexplib.Sexp.of_string_conv_exn line transition
