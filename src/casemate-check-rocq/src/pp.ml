open Rocq_casemate

let p0xZ ppf z = Fmt.pf ppf "0x%Lx" (Big_int_Z.int64_of_big_int z)
let pp_u64 = p0xZ
let pp_phys_addr_t = p0xZ

type regime = [%import: Rocq_casemate.regime] [@@deriving show]

let pp_transition_data ppf = function
  | StepData_HwMemWrite
      { twd_mo = typ; twd_phys_addr = addr; twd_val = value } ->
      Fmt.pf ppf "W%s %a %a"
        (match Transition_names.string_of_write_order typ with
        | "release" -> "rel"
        | "page" -> "page"
        | "plain" -> ""
        | order -> ":" ^ order)
        p0xZ addr p0xZ value
  | StepData_HwMemRead { trd_phys_addr = addr; trd_val = value } ->
      Fmt.pf ppf "R %a (=%a)" p0xZ addr p0xZ value
  | StepData_HwBarrier barrier ->
    Fmt.pf ppf "%s"
      (match barrier with
      | Barrier_DSB _ -> "dsb"
      | Barrier_DMB _ -> "dmb"
      | Barrier_ISB _ -> "isb"
      (* Speculative barriers *)
      | Barrier_SSBB _ -> "ssbb"
      | Barrier_PSSBB _ -> "pssbb"
      | Barrier_SB _ -> "sb")
  | StepData_HwMsr { tmd_sysreg = reg; tmd_val = value } ->
      Fmt.pf ppf "MSR %s %a" (Transition_names.string_of_sysreg reg) p0xZ
        value
  | StepData_HwTlbi { ttd_tlbi_kind = tlbi_kind; ttd_value = value } ->
    if Transition_names.tlbi_needs_value tlbi_kind then
      Fmt.pf ppf "TLBI %s %a" (Transition_names.string_of_tlbi tlbi_kind)
        p0xZ value
    else
      Fmt.pf ppf "TLBI %s" (Transition_names.string_of_tlbi tlbi_kind)
  | StepData_AbsMemInit { tmrd_addr = addr; tmrd_size = size } ->
      Fmt.pf ppf "INIT %a size %a" p0xZ addr p0xZ size
  | StepData_AbsMemFree { tmrd_addr = addr; tmrd_size = size } ->
      Fmt.pf ppf "FREE %a size %a" p0xZ addr p0xZ size
  | StepData_AbsMemset
      { tmd_addr = addr; tmd_size = size; tmd_value = value } ->
      Fmt.pf ppf "SET %a size %a as %a" p0xZ addr p0xZ size p0xZ value
  | StepData_AbsLock addr -> Fmt.pf ppf "LOCK %a" p0xZ addr
  | StepData_AbsTryLock addr -> Fmt.pf ppf "TRYLOCK %a" p0xZ addr
  | StepData_AbsUnlock addr -> Fmt.pf ppf "UNLOCK %a" p0xZ addr
  | StepData_Hint { thd_hint_kind = hint; thd_location = loc; thd_value = value } ->
      Fmt.pf ppf "Hint %s %a %a" (Transition_names.string_of_hint hint) p0xZ
        loc p0xZ value

let pp_location ppf = function
  | Some loc ->
      Fmt.pf ppf "@[%s:%d@ in@ %s@]" loc.sl_file loc.sl_lineno loc.sl_func
  | None -> Fmt.pf ppf "unknown location"

let pp_transition ppf trans =
  Fmt.pf ppf "@[ID: %d;@ CPU: %a;@ %a@ at@ %a@]" trans.cms_id
    p0xZ trans.cms_thread_identifier pp_transition_data trans.cms_data pp_location
    trans.cms_src_loc

let pp_error ppf = function
  | ModelError_BBMViolation (violation, addr) ->
      Fmt.pf ppf "@[%s at %a@]"
        (match violation with
        | BBMViolation_ValidOnInvalidUnclean -> "BBM invalid unclean->valid"
        | BBMViolation_ValidOnValid -> "BBM valid->valid"
        | BBMViolation_ReleaseUnclean ->
            "cannot release table where children are still unclean")
        p0xZ addr
  | ModelError_NotPte (str, addr) ->
      Fmt.pf ppf "Address %a was expected to be a PTE in function %s" p0xZ addr
        str
  | ModelError_InconsistentRead -> Fmt.pf ppf "inconsistent read"
  | ModelError_Uninitialised (str, addr) ->
      Fmt.pf ppf "Address %a was uninitialized in function %s" p0xZ addr str
  | ModelError_UncleanChild loc ->
      Fmt.pf ppf "An unclean child has been encountered at address: %a" p0xZ loc
  | ModelError_WriteOnNotWritable loc ->
      Fmt.pf ppf "Wrote on a page with an unclean parent at %a" p0xZ loc
  | ModelError_DoubleUseOfPte loc ->
      Fmt.pf ppf "double-use pte at %a" p0xZ loc
  | ModelError_RootAlreadyExists -> Fmt.pf ppf "root already exists"
  | ModelError_UnalignedWrite -> Fmt.pf ppf "unaligned write"
  | ModelError_DoubleLockAcquire (i, j) ->
      Fmt.pf ppf "locking error, locked owned by %a, used by %a" p0xZ i p0xZ j
  | ModelError_TransitionWithoutLock i ->
      Fmt.pf ppf "must write to pte while holding owner lock at %a" p0xZ i
  | ModelError_Unimplemented -> Fmt.pf ppf "unsupported operation in Rocq model"
  | ModelError_Internal e ->
      Fmt.pf ppf "@[internal model error:@ %s@]"
        (match e with
        | InternalError_IterationLimit -> "the maximum number of iterations was reached."
        | InternalError_UnexpectedNone -> "a None was found where it was unexpected."
        | InternalError_NoWriteAuthorization -> "no write authorization was found.")
  | ModelError_WriteWithoutAuthorization addr ->
      Fmt.pf ppf "Wrote plain without authorization at %a" p0xZ addr
  | ModelError_ParentInvalidated addr ->
      Fmt.pf ppf "Address %a's parent was invalidated" p0xZ addr
  | ModelError_OwnedPteAccessedByOtherThread addr ->
      Fmt.pf ppf "Location %a owned by a thread but accessed by another" p0xZ addr
  | ModelError_AddressIdentifier violation ->
    Fmt.pf ppf "@[(VM/AS)ID violation:@ %s@]"
      (match violation with
      | AddressIdViolation_RootAlreadyAssociated ->
          "root already associated with an (VM/AS)ID"
      | AddressIdViolation_TTBR0_EL2ReservedZero -> "TTBR0_EL2 ASID is reserved 0"
      | AddressIdViolation_Duplicate -> "duplicate (VM/AS)ID")
  | ModelError_OwnerNotAssociatedWithLock ->
      Fmt.pf ppf "must have associated root with a lock"

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

let pp_step_error ppf (trans, err) =
  Fmt.pf ppf "@[<v2>Error while checking transition:@,%a@,@[<2>Reason:@ %a@]@]"
    pp_transition trans pp_error err

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

let pp_cm_root ppf root =
  Fmt.pf ppf "@[{ baddr: %a;@ id: %a;@ refcount: %d }@]" p0xZ root.r_baddr
    p0xZ root.r_id root.r_refcount

let pp_root_list label ppf roots =
  Fmt.pf ppf "@[%s: @[<2>[%a]@]@]" label
    Fmt.(list ~sep:comma pp_cm_root)
    roots

let pp_casemate_model_roots ppf roots =
  Fmt.pf ppf "@[<v>%a@,%a@]" (pp_root_list "S1") roots.cmr_s1
    (pp_root_list "S2") roots.cmr_s2

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
      Fmt.pf ppf "%a -> %a locked by %a count %d%s" p0xZ root p0xZ addr p0xZ x.ls_tid
      x.ls_count
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
