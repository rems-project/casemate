module Z0 = Z
open Sexplib0.Sexp
open Sexplib0.Sexp_conv
open Coq_executable_casemate

let ( ~$ ) = Z0.( ~$ )
let int = Sexplib0.Sexp_conv.int_of_sexp

let u64 sexp =
  match sexp with
  | List _ -> of_sexp_error "bad u64" sexp
  | Atom s -> (
      let n = String.length s in
      try
        if n > 2 && s.[0] == '0' && s.[1] == 'x' then
          Z0.of_substring_base 16 s ~pos:2 ~len:(n - 2)
        else Z0.of_string s
      with Invalid_argument _ -> of_sexp_error "bad u64" sexp)

let mem_write_order = function
  | Atom "plain" -> WMO_plain
  | Atom "page" -> WMO_page
  | Atom "release" -> WMO_release
  | sexp -> of_sexp_error "bad mem-write mem-order" sexp

let msr_sysreg = function
  | Atom "vttbr_el2" -> SYSREG_VTTBR
  | Atom "ttbr0_el2" -> SYSREG_TTBR_EL2
  | sexp -> of_sexp_error "bad msr sysreg" sexp

let hint_kind = function
  | Atom "set_root_lock" -> GHOST_HINT_SET_ROOT_LOCK
  | Atom "set_owner_root" -> GHOST_HINT_SET_OWNER_ROOT
  | Atom "release" -> GHOST_HINT_RELEASE_TABLE
  | Atom "set_pte_thread_owner" -> GHOST_HINT_SET_PTE_THREAD_OWNER
  | sexp -> of_sexp_error "bad lock hint kind" sexp

let barrier_kind = function
  | Atom "ish" -> MBReqDomain_InnerShareable
  | Atom "ishst" -> MBReqDomain_InnerShareable
  | Atom "nsh" -> MBReqDomain_Nonshareable
  | Atom "sy" -> MBReqDomain_FullSystem
  | sexp -> of_sexp_error "bad barrier kind" sexp

let barrier_of = function
  | List [ Atom "dsb"; List [ Atom "kind"; kind ] ] ->
      Barrier_DSB (barrier_kind kind)
  | Atom "isb" -> Barrier_ISB ()
  | sexp -> of_sexp_error "bad barrier" sexp

let tlbi_op = function
  | `DALL -> TLBIOp_DALL
  | `DASID -> TLBIOp_DASID
  | `DVA -> TLBIOp_DVA
  | `IALL -> TLBIOp_IALL
  | `IASID -> TLBIOp_IASID
  | `IVA -> TLBIOp_IVA
  | `ALL -> TLBIOp_ALL
  | `ASID -> TLBIOp_ASID
  | `IPAS2 -> TLBIOp_IPAS2
  | `VAA -> TLBIOp_VAA
  | `VA -> TLBIOp_VA
  | `VMALL -> TLBIOp_VMALL
  | `VMALLS12 -> TLBIOp_VMALLS12
  | `RIPAS2 -> TLBIOp_RIPAS2
  | `RVAA -> TLBIOp_RVAA
  | `RVA -> TLBIOp_RVA
  | `RPA -> TLBIOp_RPA
  | `PAALL -> TLBIOp_PAALL

and regime_of = function
  | `EL3 -> Regime_EL3
  | `EL30 -> Regime_EL30
  | `EL2 -> Regime_EL2
  | `EL20 -> Regime_EL20
  | `EL10 -> Regime_EL10

and shareability = function
  | `NSH -> Shareability_NSH
  | `ISH -> Shareability_ISH
  | `OSH -> Shareability_OSH

let tlbi ?level ?addr ~regime ~shr op =
  let level =
    match level with
    | None -> TLBILevel_Any
    | Some (Atom "any") -> TLBILevel_Any
    | Some (Atom "last") -> TLBILevel_Last
    | Some sexp -> of_sexp_error "bad tlbi level" sexp
  and address = match addr with Some a -> u64 a | _ -> Z0.zero in
  {
    tLBI_shareability = shareability shr;
    tLBI_rec =
      {
        tLBIRecord_op = tlbi_op op;
        tLBIRecord_regime = regime_of regime;
        tLBIRecord_level = level;
        tLBIRecord_address = address;
      };
  }

let tlbi_of = function
  | Atom "vmalls12e1" -> tlbi `VMALLS12 ~regime:`EL10 ~shr:`NSH
  | Atom "vmalls12e1is" -> tlbi `VMALLS12 ~regime:`EL10 ~shr:`ISH
  | Atom "vmalle1is" -> tlbi `VMALL ~regime:`EL10 ~shr:`ISH
  | Atom "alle1is" -> tlbi `ALL ~regime:`EL10 ~shr:`ISH
  | List
      [ Atom "vae2"; List [ Atom "addr"; addr ]; List [ Atom "level"; level ] ]
    ->
      tlbi `VA ~regime:`EL2 ~shr:`NSH ~addr ~level
  | List
      [
        Atom "vae2is"; List [ Atom "addr"; addr ]; List [ Atom "level"; level ];
      ] ->
      tlbi `VA ~regime:`EL2 ~shr:`ISH ~addr ~level
  | List
      [
        Atom "ipas2e1is";
        List [ Atom "addr"; addr ];
        List [ Atom "level"; level ];
      ] ->
      tlbi `IPAS2 ~regime:`EL10 ~shr:`NSH ~addr ~level
  | sexp -> of_sexp_error "bad tlbi" sexp

let transition sexp =
  let data, id, tid, tl =
    match sexp with
    | List
        (Atom "mem-write"
        :: List [ Atom "id"; id ]
        :: List [ Atom "tid"; tid ]
        :: List [ Atom "mem-order"; order ]
        :: List [ Atom "address"; addr ]
        :: List [ Atom "value"; value ]
        :: tl) ->
        ( CMSD_TRANS_HW_MEM_WRITE
            {
              twd_mo = mem_write_order order;
              twd_phys_addr = u64 addr;
              twd_val = u64 value;
            },
          id,
          tid,
          tl )
    (*| List*)
    (*    (Atom "mem-set"*)
    (* :: List [ Atom "id"; id ]
       :: List [ Atom "tid"; tid ]*)
    (*    :: List [ Atom "address"; addr ]*)
    (*    :: List [ Atom "size"; size ]*)
    (*    :: List [ Atom "value"; value ]*)
    (*    :: tl) ->*)
    (*    if u64 size <> ~$4096 then of_sexp_error "bad mem-set size" sexp*)
    (*    else*)
    (*      ( CMSD_TRANS_HW_MEM_WRITE*)
    (*          {*)
    (*            twd_mo = WMO_page;*)
    (*            twd_phys_addr = u64 addr;*)
    (*            twd_val = u64 value;*)
    (*          },*)
    (*        id,*)
    (*        tid,*)
    (*        tl )*)
    | List
        (Atom "mem-read"
        :: List [ Atom "id"; id ]
        :: List [ Atom "tid"; tid ]
        :: List [ Atom "address"; addr ]
        :: List [ Atom "value"; value ]
        :: tl) ->
        ( CMSD_TRANS_HW_MEM_READ
            { trd_phys_addr = u64 addr; trd_val = u64 value },
          id,
          tid,
          tl )
    | List
        (Atom "barrier"
        :: List [ Atom "id"; id ]
        :: List [ Atom "tid"; tid ]
        :: barrier :: tl) ->
        (CMSD_TRANS_HW_BARRIER (barrier_of barrier), id, tid, tl)
    | List
        (Atom "tlbi"
        :: List [ Atom "id"; id ]
        :: List [ Atom "tid"; tid ]
        :: tlbi :: tl) ->
        (CMSD_TRANS_HW_TLBI (tlbi_of tlbi), id, tid, tl)
    | List
        (Atom "sysreg-write"
        :: List [ Atom "id"; id ]
        :: List [ Atom "tid"; tid ]
        :: List [ Atom "sysreg"; sysreg ]
        :: List [ Atom "value"; value ]
        :: tl) ->
        ( CMSD_TRANS_HW_MSR
            { tmd_sysreg = msr_sysreg sysreg; tmd_val = u64 value },
          id,
          tid,
          tl )
    | List
        (Atom "mem-init"
        :: List [ Atom "id"; id ]
        :: List [ Atom "tid"; tid ]
        :: List [ Atom "address"; addr ]
        :: List [ Atom "size"; size ]
        :: tl) ->
        ( CMSD_TRANS_ABS_MEM_INIT { tid_addr = u64 addr; tid_size = u64 size },
          id,
          tid,
          tl )
    | List
        (Atom "mem-set"
        :: List [ Atom "id"; id ]
        :: List [ Atom "tid"; tid ]
        :: List [ Atom "address"; addr ]
        :: List [ Atom "size"; size ]
        :: List [ Atom "value"; value ]
        :: tl) ->
        ( CMSD_TRANS_ABS_MEMSET
            { tmd_addr = u64 addr; tmd_size = u64 size; tmd_value = u64 value },
          id,
          tid,
          tl )
    | List
        (Atom "lock"
        :: List [ Atom "id"; id ]
        :: List [ Atom "tid"; tid ]
        :: List [ Atom "address"; addr ]
        :: tl) ->
        (CMSD_TRANS_ABS_LOCK (u64 addr), id, tid, tl)
    | List
        (Atom "unlock"
        :: List [ Atom "id"; id ]
        :: List [ Atom "tid"; tid ]
        :: List [ Atom "address"; addr ]
        :: tl) ->
        (CMSD_TRANS_ABS_UNLOCK (u64 addr), id, tid, tl)
    | List
        (Atom "hint"
        :: List [ Atom "id"; id ]
        :: List [ Atom "tid"; tid ]
        :: List [ Atom "kind"; kind ]
        :: List [ Atom "location"; loc ]
        :: List [ Atom "value"; value ]
        :: tl) ->
        ( CMSD_TRANS_HINT
            {
              thd_hint_kind = hint_kind kind;
              thd_location = u64 loc;
              thd_value = u64 value;
            },
          id,
          tid,
          tl )
    | sexp -> of_sexp_error "bad event" sexp
  in
  let loc =
    match tl with
    | List [ Atom "src"; Atom loc_str ] :: _ -> (
        (* Now loc_str is a string like "file.c:123" *)
        match String.split_on_char ':' loc_str with
        | [ file; lineno ] ->
            Some
              { sl_file = file; sl_lineno = int_of_string lineno; sl_func = "" }
        | _ ->
            of_sexp_error "Malformed src format (expected file:line)"
              (List [ Atom "src"; Atom loc_str ]))
    | [] -> None
    | sexp -> of_sexp_error "bad location or extra data" (List sexp)
  in
  Some
    {
      cms_src_loc = loc;
      cms_id = int id;
      cms_thread_identifier = int tid;
      cms_data = data;
    }

let of_line line = Sexplib.Sexp.of_string_conv_exn line transition
