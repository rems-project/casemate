module Z0 = Z
open Sexplib0.Sexp
open Sexplib0.Sexp_conv
open Rocq_casemate

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
  | Atom "release_table"        -> GHOST_HINT_RELEASE_TABLE
  | Atom "set_pte_thread_owner" -> GHOST_HINT_SET_PTE_THREAD_OWNER
  | sexp -> of_sexp_error "bad lock hint kind" sexp

let barrier_kind = function
  | Atom "ish"   -> MBReqDomain_InnerShareable
  | Atom "ishst" -> MBReqDomain_InnerShareable
  | Atom "nsh"   -> MBReqDomain_Nonshareable
  | Atom "sy"    -> MBReqDomain_FullSystem
  | sexp         -> of_sexp_error "bad barrier kind" sexp

let barrier_of barrier_name tl =
  match barrier_name with
  | Atom "dsb" -> (
      match tl with
      | List [ Atom "kind"; kind ] :: tl -> (Barrier_DSB (barrier_kind kind), tl)
      | sexpr -> of_sexp_error "Bad barrier kind" (List sexpr))
  | Atom "isb" -> (Barrier_ISB (), tl)
  | sexpr -> of_sexp_error "Bad barrier name" sexpr

let tlbi_of tlbi_name tl =
  match tlbi_name with
  | Atom "vmalls12e1" ->
      ( CMSD_TRANS_HW_TLBI { ttd_tlbi_kind = TLBI_vmalls12e1; ttd_value = b0 },
        tl )
  | Atom "vmalls12e1is" ->
      ( CMSD_TRANS_HW_TLBI { ttd_tlbi_kind = TLBI_vmalls12e1is; ttd_value = b0 },
        tl )
  | Atom "vmalle1is" ->
      (CMSD_TRANS_HW_TLBI { ttd_tlbi_kind = TLBI_vmalle1is; ttd_value = b0 }, tl)
  | Atom "alle1is" ->
      (CMSD_TRANS_HW_TLBI { ttd_tlbi_kind = TLBI_alle1is; ttd_value = b0 }, tl)
  | Atom "vae2" -> (
      match tl with
      | List [ Atom "value"; value ] :: tl ->
          ( CMSD_TRANS_HW_TLBI
              { ttd_tlbi_kind = TLBI_vae2; ttd_value = u64 value },
            tl )
      | sexpr -> of_sexp_error "Bad tlbi data" (List sexpr))
  | Atom "vale2is" -> (
      match tl with
      | List [ Atom "value"; value ] :: tl ->
          ( CMSD_TRANS_HW_TLBI
              { ttd_tlbi_kind = TLBI_vale2is; ttd_value = u64 value },
            tl )
      | sexpr -> of_sexp_error "Bad tlbi data" (List sexpr))
  | Atom "vae2is" -> (
      match tl with
      | List [ Atom "value"; value ] :: tl ->
          ( CMSD_TRANS_HW_TLBI
              { ttd_tlbi_kind = TLBI_vae2is; ttd_value = u64 value },
            tl )
      | sexpr -> of_sexp_error "Bad tlbi data" (List sexpr))
  | Atom "ipas2e1is" -> (
      match tl with
      | List [ Atom "value"; value ] :: tl ->
          ( CMSD_TRANS_HW_TLBI
              { ttd_tlbi_kind = TLBI_ipas2e1is; ttd_value = u64 value },
            tl )
      | sexpr -> of_sexp_error "Bad tlbi data" (List sexpr))
  | sexp -> of_sexp_error "Bad tlbi" sexp

let transition sexp =
  let data, id, tid, tl = match sexp with
  | List
      (Atom "mem-write"
      :: List [ Atom "id"; id ]
      :: List [ Atom "tid"; tid ]
      :: List [ Atom "mem-order"; order ]
      :: List [ Atom "address"; addr ]
      :: List [ Atom "value"; value ]
      :: tl) ->
        CMSD_TRANS_HW_MEM_WRITE { twd_mo = mem_write_order order; twd_phys_addr = u64 addr; twd_val = u64 value },
        id, tid, tl
  | List
      (Atom "mem-read"
      :: List [ Atom "id"; id ]
      :: List [ Atom "tid"; tid ]
      :: List [ Atom "address"; addr ]
      :: List [ Atom "value"; value ]
      :: tl) ->
        CMSD_TRANS_HW_MEM_WRITE { twd_mo = WMO_page; twd_phys_addr = u64 addr; twd_val = u64 value },
        id, tid, tl
  | List
      (Atom "barrier"
      :: List [ Atom "id"; id ]
      :: List [ Atom "tid"; tid ]
      :: barrier_name :: tl) ->
      let barrier, tl = barrier_of barrier_name tl in
      (CMSD_TRANS_HW_BARRIER barrier, id, tid, tl)
  | List
      (Atom "tlbi"
      :: List [ Atom "id"; id ]
      :: List [ Atom "tid"; tid ]
      :: tlbi_name :: tl) ->
      let tlbi, tl = tlbi_of tlbi_name tl in
      (tlbi, id, tid, tl)
  | List
      (Atom "sysreg-write"
      :: List [ Atom "id"; id ]
      :: List [ Atom "tid"; tid ]
      :: List [ Atom "sysreg"; sysreg ]
      :: List [ Atom "value"; value ]
      :: tl) ->
        CMSD_TRANS_HW_MSR { tmd_sysreg = msr_sysreg sysreg; tmd_val = u64 value },
        id, tid, tl
  | List
      (Atom "mem-init"
      :: List [ Atom "id"; id ]
      :: List [ Atom "tid"; tid ]
      :: List [ Atom "address"; addr ]
      :: List [ Atom "size"; size ]
      :: tl) ->
        CMSD_TRANS_ABS_MEM_INIT { tid_addr = u64 addr; tid_size = u64 size },
        id, tid, tl
  | List
      (Atom "mem-set"
      :: List [ Atom "id"; id ]
      :: List [ Atom "tid"; tid ]
      :: List [ Atom "address"; addr ]
      :: List [ Atom "size"; size ]
      :: List [ Atom "value"; value ]
      :: tl) ->
        CMSD_TRANS_ABS_MEMSET { tmd_addr = u64 addr; tmd_size = u64 size; tmd_value = u64 value },
        id, tid, tl
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
        CMSD_TRANS_HINT { thd_hint_kind = hint_kind kind; thd_location = u64 loc; thd_value = u64 value; },
        id, tid, tl
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
  Some {
    cms_src_loc = loc;
    cms_id = int id;
    cms_thread_identifier = u64 tid;
    cms_data = data;
  }

let of_line line = Sexplib.Sexp.of_string_conv_exn line transition
