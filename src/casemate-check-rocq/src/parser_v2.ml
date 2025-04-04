module Z0 = Z
open Sexplib0.Sexp
open Sexplib0.Sexp_conv
open Coq_executable_sm

let (~$) = Z0.(~$)

let int = Sexplib0.Sexp_conv.int_of_sexp
let u64 sexp = match sexp with
| List _ -> of_sexp_error "bad u64" sexp
| Atom s ->
    let n = String.length s in
    try (
      if n > 2 && s.[0] == '0' && s.[1] == 'x' then
        Z0.of_substring_base 16 s ~pos:2 ~len:(n - 2)
      else Z0.of_string s
    ) with Invalid_argument _ -> of_sexp_error "bad u64" sexp

let mem_write_order = function
  | Atom "plain"   -> WMO_plain
  | Atom "page"    -> WMO_page
  | Atom "release" -> WMO_release
  | sexp -> of_sexp_error "bad mem-write mem-order" sexp

let msr_sysreg = function
  | Atom "vttbr_el2" -> SYSREG_VTTBR
  | Atom "ttbr0_el2" -> SYSREG_TTBR_EL2
  | sexp -> of_sexp_error "bad msr sysreg" sexp

let hint_kind = function
  | Atom "set_root_lock"        -> GHOST_HINT_SET_ROOT_LOCK
  | Atom "set_owner_root"       -> GHOST_HINT_SET_OWNER_ROOT
  | Atom "release_table"        -> GHOST_HINT_RELEASE
  | Atom "set_pte_thread_owner" -> GHOST_HINT_SET_PTE_THREAD_OWNER
  | sexp -> of_sexp_error "bad lock hint kind" sexp

let barrier_kind = function
  | Atom "ish"   -> MBReqDomain_InnerShareable
  | Atom "ishst" -> MBReqDomain_InnerShareable
  | Atom "nsh"   -> MBReqDomain_Nonshareable
  | Atom "sy"    -> MBReqDomain_FullSystem
  | sexp         -> of_sexp_error "bad barrier kind" sexp

let tlbi_op = function
| `DALL     -> TLBIOp_DALL        
| `DASID    -> TLBIOp_DASID       
| `DVA      -> TLBIOp_DVA         
| `IALL     -> TLBIOp_IALL        
| `IASID    -> TLBIOp_IASID       
| `IVA      -> TLBIOp_IVA         
| `ALL      -> TLBIOp_ALL         
| `ASID     -> TLBIOp_ASID        
| `IPAS2    -> TLBIOp_IPAS2       
| `VAA      -> TLBIOp_VAA         
| `VA       -> TLBIOp_VA          
| `VMALL    -> TLBIOp_VMALL       
| `VMALLS12 -> TLBIOp_VMALLS12    
| `RIPAS2   -> TLBIOp_RIPAS2      
| `RVAA     -> TLBIOp_RVAA        
| `RVA      -> TLBIOp_RVA         
| `RPA      -> TLBIOp_RPA         
| `PAALL    -> TLBIOp_PAALL       
and regime_of = function
| `EL3  -> Regime_EL3   
| `EL30 -> Regime_EL30  
| `EL2  -> Regime_EL2   
| `EL20 -> Regime_EL20  
| `EL10 -> Regime_EL10
and shareability = function
| `NSH -> Shareability_NSH
| `ISH -> Shareability_ISH
| `OSH -> Shareability_OSH
and of_level sexp = match int sexp with
| 0 | 1 | 2 -> TLBILevel_Any
| 3 -> TLBILevel_Last
| _ -> of_sexp_error "bad level" sexp

let tlbi ?level ?addr ~regime ~shr op =
  let level = match level with Some i -> of_level i | _ -> TLBILevel_Any
  and address = match addr with Some a -> u64 a | _ -> Z0.zero
  in {
    tLBI_shareability = shareability shr;
    tLBI_rec = {
      tLBIRecord_op      = tlbi_op op;
      tLBIRecord_regime  = regime_of regime;
      tLBIRecord_level   = level;
      tLBIRecord_address = address };
  }

let tlbi_of kind addr level sexp0 = match kind, addr, level with
| "vmalls12e1",   None,      None -> tlbi `VMALLS12 ~regime:`EL10 ~shr:`NSH
| "vmalls12e1is", None,      None -> tlbi `VMALLS12 ~regime:`EL10 ~shr:`ISH
| "vmalle1is",    None,      None -> tlbi `VMALL    ~regime:`EL10 ~shr:`ISH
| "alle1is",      None,      None -> tlbi `ALL      ~regime:`EL10 ~shr:`ISH
| "vmalle1",      None,      None -> tlbi `VMALL    ~regime:`EL10 ~shr:`NSH (* XXX ? *)
| "vae2is",       Some addr, Some level -> tlbi `VA ~regime:`EL2 ~shr:`ISH ~addr ~level
| "ipas2e1is",    Some addr, Some level -> tlbi `IPAS2 ~regime:`EL10 ~shr:`NSH ~addr ~level
| "vale2is",      Some addr, Some level -> tlbi `VA ~regime:`EL2 ~shr:`ISH ~addr ~level
| _ -> of_sexp_error "bad tlbi" sexp0

let transition sexp =
  let data, id, tid, tl = match sexp with
  | List (Atom "mem-write" :: id :: tid ::
        List [Atom "mem-order"; o] :: List [Atom "address"; a] :: List [Atom "value"; v] :: tl) ->
      GSMDT_TRANS_MEM_WRITE { twd_mo = mem_write_order o; twd_phys_addr = u64 a; twd_val = u64 v },
      id, tid, tl
  | List (Atom "mem-set" :: id :: tid::
        List [Atom "address"; a] :: List [Atom "size"; s] :: List [Atom "value"; v] :: tl) ->
      if u64 s <> ~$4096 then of_sexp_error "bad mem-set size" sexp else
      GSMDT_TRANS_MEM_WRITE { twd_mo = WMO_page; twd_phys_addr = u64 a; twd_val = u64 v },
      id, tid, tl
  | List (Atom "mem-read" :: id :: tid::
        List [Atom "address"; a] :: List [Atom "value"; v] :: tl) ->
      GSMDT_TRANS_MEM_READ { trd_phys_addr = u64 a; trd_val = u64 v },
      id, tid, tl
  | List (Atom "mem-init" :: id :: tid::
        List [Atom "address"; a] :: List [Atom "size"; s] :: tl) ->
      GSMDT_TRANS_MEM_ZALLOC { tzd_addr = u64 a; tzd_size = u64 s },
      id, tid, tl
  | List (Atom "barrier" :: id :: tid :: Atom "isb" :: tl) ->
      GSMDT_TRANS_BARRIER (Barrier_ISB ()), id, tid, tl
  | List (Atom "barrier" :: id :: tid :: Atom "dsb" :: List [Atom "kind"; kind] :: tl) ->
      GSMDT_TRANS_BARRIER (Barrier_DSB (barrier_kind kind)), id, tid, tl
  | List (Atom "tlbi" :: id :: tid::
        Atom kind :: List [Atom "addr"; a] :: List [Atom "level"; level] :: tl) ->
      GSMDT_TRANS_TLBI (tlbi_of kind (Some a) (Some level) sexp), id, tid, tl
  | List (Atom "tlbi" :: id :: tid:: Atom kind :: tl) ->
      GSMDT_TRANS_TLBI (tlbi_of kind None None sexp), id, tid, tl
  | List (Atom "sysreg-write" :: id :: tid::
        List [Atom "sysreg"; sysreg] :: List [Atom "value"; v] :: tl) ->
      GSMDT_TRANS_MSR { tmd_sysreg = msr_sysreg sysreg; tmd_val = u64 v },
      id, tid, tl
  | List (Atom "hint" :: id :: tid::
        List [Atom "kind"; kind] :: List [Atom "location"; loc] :: List [Atom "value"; v] :: tl) ->
      GSMDT_TRANS_HINT { thd_hint_kind = hint_kind kind; thd_location = u64 loc; thd_value = u64 v },
      id, tid, tl
  | List (Atom "lock" :: id :: tid :: List [Atom "address"; a] :: tl) ->
      GSMDT_TRANS_LOCK { tld_kind = LOCK; tld_addr = u64 a }, id, tid, tl
  | List (Atom "unlock" :: id :: tid :: List [Atom "address"; a] :: tl) ->
      GSMDT_TRANS_LOCK { tld_kind = UNLOCK; tld_addr = u64 a }, id, tid, tl
  | sexp -> of_sexp_error "bad event" sexp
  in
  let id = match id with
    | List [Atom "id"; id] -> int id
    | sexp -> of_sexp_error "bad id" sexp
  and tid = match tid with
    | List [Atom "tid"; tid] -> int tid
    | sexp -> of_sexp_error "bad tid" sexp
  and loc = match tl with
    | [List [Atom "src"; Atom _loc]] -> None
    | [] -> None
    | sexp -> of_sexp_error "bad location or extra data" (List sexp)
  in
  Some {
    gsmt_src_loc = loc;
    gsmt_id = id;
    gsmt_thread_identifier = tid;
    gsmt_data = data
  }

let of_line line = Sexplib.Sexp.of_string_conv_exn line transition
