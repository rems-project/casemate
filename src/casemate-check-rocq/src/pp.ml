open Rocq_casemate

let p0xZ ppf z = Fmt.pf ppf "0x%Lx" (Big_int_Z.int64_of_big_int z)
let pp_u64 = p0xZ
let pp_phys_addr_t = p0xZ

type regime = [%import: Rocq_casemate.regime] [@@deriving show]

let pp_transition_data ppf = function
  | CMSD_TRANS_HW_MEM_WRITE
      { twd_mo = typ; twd_phys_addr = addr; twd_val = value } ->
      Fmt.pf ppf "W%s %a %a"
        (match typ with
        | WMO_release -> "rel"
        | WMO_page -> "page"
        | WMO_plain -> "")
        p0xZ addr p0xZ value
  | CMSD_TRANS_HW_MEM_READ { trd_phys_addr = addr; trd_val = value } ->
      Fmt.pf ppf "R %a (=%a)" p0xZ addr p0xZ value
  | CMSD_TRANS_HW_BARRIER barrier ->
    Fmt.pf ppf "%s"
      (match barrier with
      | Barrier_DSB _ -> "dsb"
      | Barrier_DMB _ -> "dmb"
      | Barrier_ISB _ -> "isb"
      (* Speculative barriers *)
      | Barrier_SSBB _ -> "ssbb"
      | Barrier_PSSBB _ -> "pssbb"
      | Barrier_SB _ -> "sb")
  | CMSD_TRANS_HW_MSR { tmd_sysreg = reg; tmd_val = value } ->
      Fmt.pf ppf "MSR %s %a"
        (match reg with
        | SYSREG_TTBR_EL2 -> "SYSREG_TTBR_EL2"
        | SYSREG_VTTBR -> "SYSREG_VTTBR")
        p0xZ value
  | CMSD_TRANS_HW_TLBI { ttd_tlbi_kind = tlbi_kind; ttd_value = value } ->
    Fmt.pf ppf "TLBI %s %a"
      (match tlbi_kind with
      | TLBI_vmalls12e1 -> "vmalls12e1"
      | TLBI_vmalls12e1is -> "vmalls12e1is"
      | TLBI_vmalle1is -> "vmalle1is"
      | TLBI_alle1is -> "alle1is"
      | TLBI_vae2 -> "vae2"
      | TLBI_vmalle1 -> "vmalle1"
      | TLBI_vale2is -> "vale2is"
      | TLBI_vae2is -> "vae2is"
      | TLBI_ipas2e1is -> "ipas2e1is")
      p0xZ value
  | CMSD_TRANS_ABS_MEM_INIT { tid_addr = addr; tid_size = size } ->
      Fmt.pf ppf "INIT %a size %a" p0xZ addr p0xZ size
  | CMSD_TRANS_ABS_MEMSET
      { tmd_addr = addr; tmd_size = size; tmd_value = value } ->
      Fmt.pf ppf "SET %a size %a as %a" p0xZ addr p0xZ size p0xZ value
  | CMSD_TRANS_ABS_LOCK addr -> Fmt.pf ppf "LOCK %a" p0xZ addr
  | CMSD_TRANS_ABS_UNLOCK addr -> Fmt.pf ppf "UNLOCK %a" p0xZ addr
  | CMSD_TRANS_HINT _ -> Fmt.pf ppf "Hint"

let pp_location ppf = function
  | Some loc ->
      Fmt.pf ppf "@[%s:%d@ in@ %s@]" loc.sl_file loc.sl_lineno loc.sl_func
  | None -> Fmt.pf ppf "unknown location"

let pp_transition ppf trans =
  Fmt.pf ppf "@[ID: %d;@ CPU: %a;@ %a@ at@ %a@]" trans.cms_id
    p0xZ trans.cms_thread_identifier pp_transition_data trans.cms_data pp_location
    trans.cms_src_loc

let pp_error ppf = function
  | CME_bbm_violation (violation, addr) ->
      Fmt.pf ppf "@[BBM violation:@ %s %a@]"
        (match violation with
        | BBM_valid_on_invalid_unclean -> "Wrote valid on invalid unclean"
        | BBM_valid_on_valid -> "Wrote valid on another valid descriptor"
        | BBM_release_unclean -> "Tried to release a page that was still unclean")
        p0xZ addr
  | CME_not_a_pte (str, addr) ->
      Fmt.pf ppf "Address %a was expected to be a PTE in function %s" p0xZ addr
        str
  | CME_inconsistent_read -> Fmt.pf ppf "CME_inconsistent_read"
  | CME_uninitialised (str, addr) ->
      Fmt.pf ppf "Address %a was uninitialized in function %s" p0xZ addr str
  | CME_unclean_child loc ->
      Fmt.pf ppf "An unclean child has been encountered at address: %a" p0xZ loc
  | CME_write_on_not_writable loc ->
      Fmt.pf ppf "Tried to write while a parent is unclean at address %a" p0xZ
        loc
  | CME_double_use_of_pte loc ->
      Fmt.pf ppf "PTE at address %a is used in two page-tables" p0xZ loc
  | CME_root_already_exists -> Fmt.pf ppf "CME_root_already_exists"
  | CME_unaligned_write -> Fmt.pf ppf "unaligned write"
  | CME_double_lock_acquire (i, j) ->
      Fmt.pf ppf "locking error, locked owned by %a, used by %a" p0xZ i p0xZ j
  | CME_transition_without_lock i ->
      Fmt.pf ppf
        "Tried to take make a step without owning the lock at address: %a" p0xZ
        i
  | CME_unimplemented -> Fmt.pf ppf "CME_unimplemented"
  | CME_internal_error e ->
      Fmt.pf ppf "@[CME_internal_error:@ %s@]"
        (match e with
        | IET_infinite_loop -> "the maximum number of iterations was reached."
        | IET_unexpected_none -> "a None was found where it was unexpected."
        | IET_no_write_authorization -> "no write authorization was found.")
  | CME_write_without_authorization addr ->
      Fmt.pf ppf "Wrote plain without being authorized to at address %a" p0xZ
        addr
  | CME_parent_invalidated addr ->
      Fmt.pf ppf "Address %a's parent was invalidated" p0xZ addr
  | CME_owned_pte_accessed_by_other_thread addr ->
      Fmt.pf ppf "Location %a owned by a thread but accessed by another" p0xZ addr
  | CME_addr_id_error violation ->
    Fmt.pf ppf "@[(VM/AS)ID violation:@ %s@]"
      (match violation with
      | AID_root_already_associated ->
          "root already associated with an (VM/AS)ID"
      | AID_TTBR0_EL2_reserved_zero -> "TTBR0_EL2 ASID is reserved 0"
      | AID_duplicate_addr_id -> "duplicate (VM/AS)ID")
  | CME_owner_not_associated_with_a_root ->
     Fmt.pf ppf "must have associated owner with a root"

let pp_log ppf = function
  | Inconsistent_read (a, b, c) ->
      Fmt.pf ppf "Inconsistent read, expected %a, got %a at address %a" p0xZ a
        p0xZ b p0xZ c
  | Warning_read_write_non_allocd x ->
      Fmt.pf ppf "Read/wrote a non-alloc'd location at address %a" p0xZ x
  | Warning_unsupported_TLBI ->
      Fmt.pf ppf
        "Warning: unsupported TLBI, defaulting to TLBI VMALLS12E1IS;TLBI ALLE2."
  | Log (a, x) -> Fmt.pf ppf "%s: %a" a p0xZ x

let pp_logs ppf log = (Fmt.list ~sep:Fmt.comma pp_log) ppf log

let pp_step_result :
    ( Rocq_casemate.casemate_model_state,
      Rocq_casemate.casemate_model_error )
    result
    Fmt.t =
  Fmt.(
    result ~ok:(const string "Success!\n") ~error:(fun ppf ->
        Fmt.pf ppf "@[<v>@[<2>Error:@ @[%a@]@]@]" pp_error))

(* Automatically derive printers using pretty evil metaprogramming, with
   ppx_import and ppx_deriving.show.

   Each `type foo = [%import: foo] [@@deriving show]` creates the function
   `pp_foo` and can be replaced with a custom `pp_foo` to control the
   printing.

   Dear future reader: when ppx_import finally totally breaks, please rewrite
   the printers by hand.
*)

type sm_owner_t = [%import: Rocq_casemate.sm_owner_t] [@@deriving show]

let pp_sm_pte_state ppf state =
  Fmt.pf ppf
    (match state with
    | SPS_STATE_PTE_VALID _ -> "valid"
    | SPS_STATE_PTE_INVALID_CLEAN _ -> "invalid clean"
    | SPS_STATE_PTE_INVALID_UNCLEAN unclean_state -> (
        "unclean "
        ^^
        match unclean_state.ai_lis with
        | LIS_unguarded -> "unguarded"
        | LIS_dsbed -> "dsbed"
        | LIS_dsb_tlbi_all -> "dsb_tlbi_all"
        | LIS_dsb_tlbi_ipa -> "dsb_tlbi_ipa"
        | LIS_dsb_tlbied -> "dsb_tlbied"
        | LIS_dsb_tlbi_ipa_dsb -> "dsb_tlbi_ipa_dsb")
    | SPS_STATE_PTE_NOT_WRITABLE -> "Clean, Not writable")

let pp_pte_rec ppf = function
  | PTER_PTE_KIND_TABLE t -> Fmt.pf ppf "Table: %a" p0xZ t
  | PTER_PTE_KIND_MAP t ->
      Fmt.pf ppf "Table: %a-%a" p0xZ t.range_start p0xZ
        (Z.add t.range_start t.range_size)
  | PTER_PTE_KIND_INVALID -> Fmt.pf ppf "Invalid"

let pp_entry_stage_t ppf = function S1 -> Fmt.pf ppf "1" | S2 -> Fmt.pf ppf "2"

let pp_level_t ppf = function
  | L0 -> Fmt.pf ppf "0"
  | L1 -> Fmt.pf ppf "1"
  | L2 -> Fmt.pf ppf "2"
  | L3 -> Fmt.pf ppf "3"
  | Lerror -> Fmt.pf ppf "error"

let pp_entry_exploded_descriptor ppf desc =
  Fmt.pf ppf
    "{@[<2>@ region: %a-%a;@ level: %a;@ stage: %a;@ owner: %a@ pte kind: %a;@ \
     state: %a;@ @]}"
    p0xZ desc.eed_ia_region.range_start p0xZ
    (Z.add desc.eed_ia_region.range_start desc.eed_ia_region.range_size)
    pp_level_t desc.eed_level pp_entry_stage_t desc.eed_stage p0xZ desc.eed_owner
    pp_pte_rec desc.eed_pte_kind pp_sm_pte_state desc.eed_state

let pp_sm_location ppf sl =
  Fmt.pf ppf "@[val: %a@ %a@]" p0xZ sl.sl_val
    (fun ppf -> function
      | Some pte -> Fmt.pf ppf "@ %a" pp_entry_exploded_descriptor pte
      | _ -> ())
    sl.sl_pte

(* TODO: update format *)
let pp_cm_root ppf root =
  Fmt.pf ppf "[<v>{ baddr: %a;@ id: %a;@ refcount: %d }@]" p0xZ root.r_baddr
    p0xZ root.r_id root.r_refcount

let pp_casemate_model_roots ppf _ = Fmt.pf ppf ""

let pp_casemate_model_memory ppf m =
  let pp_k_v =
    Fmt.pair p0xZ pp_sm_location ~sep:(fun ppf () -> Fmt.pf ppf "@ ->@ ")
    |> Fmt.box
  in
  Fmt.pf ppf "@[<2>{ %a }@]"
    Fmt.(list ~sep:comma pp_k_v)
    (Cmap.fold
       (fun k v xs ->
         match v.sl_pte with
         | Some _ -> (Big_int_Z.shift_left_big_int k 3, v) :: xs
         | None -> xs)
       m [])

let pp_casemate_model_initialised ppf m =
  Fmt.pf ppf "@[<2>{ %a }@]"
    Fmt.(list ~sep:comma p0xZ)
    (Zmap.fold (fun x () xs -> Big_int_Z.shift_left_big_int x 12 :: xs) m [])

let pp_lock_entry ppf (root, addr, state) =
  match state with
  | None -> Fmt.pf ppf "%a -> %a unlocked" p0xZ root p0xZ addr
  | Some x ->
      Fmt.pf ppf "%a -> %a locked by %a%s" p0xZ root p0xZ addr p0xZ x.ls_tid
      (match x.ls_write_authorization with
      | Write_authorized -> "; authorized to write"
      | Write_unauthorized -> "; unauthorized to write")

let pp_casemate_model_locks ppf m =
  Fmt.pf ppf "@[<2>{ %a }@]"
    Fmt.(list ~sep:comma pp_lock_entry)
    (Zmap.fold
       (fun root addr xs ->
         ( root,
           addr,
           Zmap.find_opt addr m.cms_lock_state)
         :: xs)
       m.cms_lock_addr [])

let pp_casemate_model_state ppf m =
  Fmt.pf ppf
    "roots:@ @[<2>%a@]@. memory:@ @[<2>%a@]@. zalloc'd:@ @[<2>%a@]@. locks:@ \
     @[<2>%a@]@."
    pp_casemate_model_roots m.cms_roots pp_casemate_model_memory m.cms_memory
    pp_casemate_model_initialised m.cms_initialised
    pp_casemate_model_locks m

let pp_state state =
  Fmt.(result ~ok:pp_casemate_model_state ~error:pp_error) state

let pp_tr ppf tr =
  Fmt.pf ppf "%a: @[%a@]" Fmt.(styled `Red string) "TRANS" pp_transition tr
