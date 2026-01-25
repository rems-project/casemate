Require Import utils.

Inductive LVS :=
  | LVS_unguarded
  | LVS_dsbed
  | LVS_dsb_csed
.

Record aut_valid := {
  lvs : list LVS;
}.

Inductive LIS :=
  | LIS_unguarded
  | LIS_dsbed
  | LIS_dsb_tlbi_all
  | LIS_dsb_tlbi_ipa
  | LIS_dsb_tlbied
  | LIS_dsb_tlbi_ipa_dsb
.

Record aut_invalid_unclean := mk_aut_invalid_unclean {
  ai_invalidator_tid : thread_identifier;
  ai_old_valid_desc : u64;
  ai_lis : LIS;
}.
#[export] Instance eta_aut_invalid_unclean : Settable _ :=
  settable! mk_aut_invalid_unclean <ai_invalidator_tid; ai_old_valid_desc; ai_lis>.


Record aut_invalid_clean := {
  aic_invalidator_tid : thread_identifier;
}.

Inductive sm_pte_state :=
  | SPS_STATE_PTE_VALID (valid_state : aut_valid)
  | SPS_STATE_PTE_INVALID_UNCLEAN (invalid_unclean_state : aut_invalid_unclean)
  | SPS_STATE_PTE_INVALID_CLEAN (invalid_clean_state : aut_invalid_clean)
  | SPS_STATE_PTE_NOT_WRITABLE
.

Record addr_range := {
  range_start : phys_addr_t;
  range_size : phys_addr_t;
}.

Record map_data_t := {
  oa_region : addr_range;
}.

Inductive level_t :=
  | l0
  | l1
  | l2
  | l3
  | lerror
.

Definition next_level (l : level_t) : level_t :=
  match l with
  | l0 => l1
  | l1 => l2
  | l2 => l3
  | l3 => lerror
  | lerror => lerror
  end
.

Definition is_l3 (l : level_t) : bool :=
  match l with
  | l3 => true
  | _ => false
  end
.

Global Instance level_t_eq_decision : EqDecision level_t.
  Proof. solve_decision. Qed.

Record table_data_t := {
  next_level_table_addr : phys_addr_t;
}.

Inductive pte_rec :=
  | PTER_PTE_KIND_TABLE (table_data : table_data_t)
  | PTER_PTE_KIND_MAP (map_data : map_data_t)
  | PTER_PTE_KIND_INVALID
.

Record entry_exploded_descriptor := mk_entry_exploded_descriptor {
  eed_ia_region : addr_range;
  eed_level : level_t;
  eed_stage : entry_stage_t;
  eed_pte_kind : pte_rec;
  eed_state : sm_pte_state;
  (* address of the root of the PTE *)
  eed_owner : sm_owner_t;
}.
#[export] Instance eta_entry_exploded_descriptor : Settable _ :=
  settable! mk_entry_exploded_descriptor <eed_ia_region; eed_level; eed_stage; eed_pte_kind; eed_state; eed_owner>.


Record sm_location := mk_sm_location {
  (* sl_initialised : bool; *)
  sl_phys_addr : phys_addr_t;
  sl_val : u64;
  sl_pte : option entry_exploded_descriptor;
  sl_thread_owner : option thread_identifier;
}.
#[export] Instance eta_sm_location : Settable _ :=
  settable! mk_sm_location <sl_phys_addr; sl_val; sl_pte; sl_thread_owner>.

Record owner_locks := {
  ol_len : u64;
  ol_owner_ids : list sm_owner_t;
  ol_locks : unit;
}.

Record cm_root := {
  r_baddr : sm_owner_t;
  r_id : addr_id_t;
  r_refcount : nat;
}.

Record cm_thrd_ctxt := {
  current_s1 : sm_owner_t;
  current_s2 : sm_owner_t;
}.

(* The memory state is a map from address to casemate model location *)
Definition casemate_model_memory := cmap sm_location.

(* The initialised memory is stored here *)
Definition casemate_model_initialised := zmap unit.

(* per-CPU thread-local context *)
Definition casemate_model_thrd_ctxt := cmap cm_thrd_ctxt.

(* Map of pgtable root to lock that owns it *)
Definition casemate_model_lock_owner_map := zmap u64.

Inductive write_authorization :=
  | write_authorized
  | write_unauthorized
.

(* the map from lock address to the thread that acquired it and the lock authorization if any *)
Record lock_state := {
  ls_tid : thread_identifier;
  ls_write_authorization : write_authorization;
}.

Definition casemate_model_lock_state_map := zmap lock_state.

(* Storing roots for PTE walkthrough (we might need to distinguish S1 and S2 roots) *)
Record casemate_model_roots := mk_pte_roots {
  cmr_s1 : list cm_root;
  cmr_s2 : list cm_root;
}.
#[export] Instance eta_pte_roots : Settable _ := settable! mk_pte_roots <cmr_s1; cmr_s2>.

Definition retrieve_root_for_baddr
  (stage : entry_stage_t)
  (cm_roots : casemate_model_roots)
  (root_addr : sm_owner_t) : option cm_root :=
  let roots :=
    match stage with
    | S1 => cm_roots.(cmr_s1)
    | S2 => cm_roots.(cmr_s2)
    end in
  find (fun elem => bool_decide (elem.(r_baddr) = root_addr)) roots.

Definition retrieve_root_for_id
  (stage : entry_stage_t)
  (cm_roots : casemate_model_roots)
  (addr_id : addr_id_t) : option cm_root :=
  let roots :=
    match stage with
    | S1 => cm_roots.(cmr_s1)
    | S2 => cm_roots.(cmr_s2)
    end in
  find (fun elem => bool_decide (elem.(r_id) = addr_id)) roots.

Definition update_root_for_baddr
  (root_addr : sm_owner_t)
  (new_root : cm_root)
  (roots : list cm_root) : list cm_root :=
  let idx := index_of (fun elem => bool_decide (elem.(r_baddr) = root_addr)) roots in
  list_insert idx new_root roots.

Definition update_root_for_id
  (addr_id : addr_id_t)
  (new_root : cm_root)
  (roots : list cm_root) : list cm_root :=
  let idx := index_of (fun elem => bool_decide (elem.(r_id) = addr_id)) roots in
  list_insert idx new_root roots.

Definition update_cms_root_for_baddr
  (stage : entry_stage_t)
  (root_addr : sm_owner_t)
  (new_root : cm_root)
  (cms_roots : casemate_model_roots) :
  casemate_model_roots :=
  match stage with
  | S1 => let new_roots := update_root_for_baddr root_addr new_root cms_roots.(cmr_s1) in
    cms_roots <| cmr_s1 := new_roots |>
  | S2 => let new_roots := update_root_for_baddr root_addr new_root cms_roots.(cmr_s2) in
    cms_roots <| cmr_s2 := new_roots |>
  end.

Definition update_cms_root_for_id
  (stage : entry_stage_t)
  (addr_id : addr_id_t)
  (new_root : cm_root)
  (cms_roots : casemate_model_roots) :
  casemate_model_roots :=
  match stage with
  | S1 => let new_roots := update_root_for_id addr_id new_root cms_roots.(cmr_s1) in
    cms_roots <| cmr_s1 := new_roots |>
  | S2 => let new_roots := update_root_for_id addr_id new_root cms_roots.(cmr_s2) in
    cms_roots <| cmr_s2 := new_roots |>
  end.

Definition insert_cms_root
  (stage : entry_stage_t)
  (root : cm_root)
  (cms_roots : casemate_model_roots) : casemate_model_roots :=
  match stage with
  | S2 => cms_roots <| cmr_s2 := root :: cms_roots.(cmr_s2) |>
  | S1 => cms_roots <| cmr_s1 := root :: cms_roots.(cmr_s1) |>
  end.

Record casemate_model_state := mk_casemate_model_state {
  cms_roots : casemate_model_roots;
  cms_memory : casemate_model_memory;
  cms_initialised : casemate_model_initialised;
  cms_thrd_ctxt : casemate_model_thrd_ctxt;
  cms_lock_addr : casemate_model_lock_owner_map;
  cms_lock_state : casemate_model_lock_state_map
}.
#[export] Instance eta_casemate_model_state : Settable _ :=
  settable! mk_casemate_model_state
    <cms_roots; cms_memory; cms_initialised; cms_thrd_ctxt; cms_lock_addr; cms_lock_state>.

Definition cms_init := {|
  cms_roots := {| cmr_s1 := []; cmr_s2 := []; |};
  cms_memory := ∅;
  cms_initialised := ∅;
  cms_thrd_ctxt := ∅;
  cms_lock_addr := ∅;
  cms_lock_state := ∅;
|}.

Definition is_initialised (st : casemate_model_state) (addr : phys_addr_t) : bool :=
  match st.(cms_initialised) !! ((bv_shiftr_64 (phys_addr_val addr) b12)) with
    | Some _ => true
    | None => false
  end
.

Definition get_location
  (st : casemate_model_state)
  (addr : phys_addr_t) : option sm_location :=
  match st.(cms_memory) !! bv_shiftr_64 (phys_addr_val addr) b3 with
  | Some loc => Some loc
  | None =>
    match is_initialised st addr with
    | true => Some {| sl_phys_addr := addr; sl_val := b0; sl_pte := None; sl_thread_owner := None |}
    | false => None
    end
  end
.

Definition get_lock_of_owner
  (owner : sm_owner_t)
  (cms : casemate_model_state) : option u64 :=
  lookup (phys_addr_val (owner_val owner)) cms.(cms_lock_addr).


Infix "!!" := get_location (at level 20).

Definition is_loc_thread_owned
  (cpu : thread_identifier)
  (location : sm_location)
  (cms : casemate_model_state) : bool :=
  match location.(sl_pte), location.(sl_thread_owner) with
  | Some _, Some thread_owner =>
    bool_decide (thread_owner = cpu)
  | _, _ => false
  end
.

Definition is_pte_well_locked
  (cpu : thread_identifier)
  (pte : entry_exploded_descriptor)
  (cms : casemate_model_state) : bool :=
  match get_lock_of_owner pte.(eed_owner) cms with
  | None => false
  | Some addr =>
    match lookup addr cms.(cms_lock_state) with
    | Some {| ls_tid := lock_owner; ls_write_authorization := _ |} => bool_decide (lock_owner = cpu)
    | None => false
    end
  end
.

Definition cm_roots_for_other_stage (stage : entry_stage_t) (cms : casemate_model_state) :=
  match stage with
  | S1 => cms.(cms_roots).(cmr_s2)
  | S2 => cms.(cms_roots).(cmr_s1)
  end.

Definition should_visit
  (cpu : thread_identifier)
  (addr : phys_addr_t)
  (cms : casemate_model_state) : bool :=
  match cms !! addr with
  | None => true
  | Some location =>
    match location.(sl_pte) with
    | None => true
    | Some pte =>
      orb (is_loc_thread_owned cpu location cms) (is_pte_well_locked cpu pte cms)
    end
  end.

  Definition current_thread_context
  (tid : thread_identifier)
  (cms : casemate_model_state) :
  option cm_thrd_ctxt :=
  let val := thread_identifier_to_val tid in
  lookup val cms.(cms_thrd_ctxt).

Definition update_current_thread_context
  (tid : thread_identifier)
  (stage : entry_stage_t)
  (assoc_root_baddr : sm_owner_t)
  (cms : casemate_model_state) :
  casemate_model_state :=
  let idx := thread_identifier_to_val tid in
  let new_thrd_ctxt :=
    match current_thread_context tid cms with
    | Some thrd_ctxt =>
      match stage with
      | S1 => {| current_s1 := assoc_root_baddr; current_s2 := thrd_ctxt.(current_s2) |}
      | S2 => {| current_s1 := thrd_ctxt.(current_s2); current_s2 := assoc_root_baddr|}
      end
    | None =>
      match stage with (* TODO: pa0 to None? *)
      | S1 => {| current_s1 := assoc_root_baddr; current_s2 := Root pa0 |}
      | S2 => {| current_s1 := Root pa0; current_s2 := assoc_root_baddr|}
      end
    end in
  let val := thread_identifier_to_val tid in
  let new_cms_thrd_ctxt := insert val new_thrd_ctxt cms.(cms_thrd_ctxt) in
  cms <| cms_thrd_ctxt := new_cms_thrd_ctxt |>.

Definition current_thread_context_root
  (tid : thread_identifier)
  (stage : entry_stage_t)
  (cms : casemate_model_state) : option cm_root :=
  match current_thread_context tid cms with
  | Some thrd_ctxt =>
    let root_addr :=
      match stage with
      | S1 => thrd_ctxt.(current_s1)
      | S2 => thrd_ctxt.(current_s2)
      end in
    retrieve_root_for_baddr stage cms.(cms_roots) root_addr
  | None => None
  end.

Definition get_current_ttbr
  (tid : thread_identifier)
  (cms : casemate_model_state) : option cm_root :=
  current_thread_context_root tid S1 cms.

Definition get_current_vttbr
  (tid : thread_identifier)
  (cms : casemate_model_state) : option cm_root :=
  current_thread_context_root tid S2 cms.

Inductive violation_type :=
  | BBM_valid_on_invalid_unclean
  | BBM_valid_on_valid
  | BBM_release_unclean
.

Inductive addr_id_violation :=
  | AID_root_already_associated
  | AID_TTBR0_EL2_reserved_zero
  | AID_duplicate_addr_id
.

Inductive casemate_model_error :=
  | CME_bbm_violation : violation_type -> phys_addr_t -> casemate_model_error
  | CME_not_a_pte : string -> phys_addr_t -> casemate_model_error
  | CME_inconsistent_read
  | CME_uninitialised : string -> phys_addr_t -> casemate_model_error
  | CME_unclean_child : phys_addr_t -> casemate_model_error
  | CME_write_on_not_writable : phys_addr_t -> casemate_model_error
  | CME_double_use_of_pte : phys_addr_t -> casemate_model_error
  | CME_root_already_exists
  | CME_unaligned_write
  | CME_double_lock_acquire : thread_identifier -> thread_identifier -> casemate_model_error
  | CME_transition_without_lock : phys_addr_t -> casemate_model_error
  | CME_write_without_authorization : phys_addr_t -> casemate_model_error
  | CME_unimplemented
  | CME_internal_error : internal_error_type -> casemate_model_error
  | CME_parent_invalidated : phys_addr_t -> casemate_model_error
  | CME_owned_pte_accessed_by_other_thread : phys_addr_t -> casemate_model_error
  | CME_addr_id_error : addr_id_violation -> casemate_model_error (* TODO: add error cases as inductive types *)
  | CME_owner_not_associated_with_a_root
.

Record casemate_model_result := mk_casemate_model_result {
  cmr_log : list log_element;
  cmr_data : result casemate_model_state casemate_model_error
}.

#[export] Instance eta_casemate_model_result : Settable _ :=
  settable! mk_casemate_model_result <cmr_log; cmr_data>.

Definition Mreturn (cms : casemate_model_state) : casemate_model_result :=
  {| cmr_log := nil; cmr_data := Ok _ _ cms |}.

Definition Mbind
  (r : casemate_model_result)
  (f : casemate_model_state -> casemate_model_result) :
  casemate_model_result :=
  match r.(cmr_data) with
  | Error _ _ e => r
  | Ok _ _ cms =>
    let s' := f cms in
    {| cmr_log := app s'.(cmr_log) r.(cmr_log);
       cmr_data := s'.(cmr_data); |}
  end.

Definition Merror (gse : casemate_model_error) : casemate_model_result :=
  {| cmr_log := nil; cmr_data := Error _ _ gse |}.

Definition Mlog
  (s : log_element)
  (r : casemate_model_result) : casemate_model_result :=
  r <|cmr_log := s :: r.(cmr_log) |>.

Definition Mupdate_state
  (updater : casemate_model_state -> casemate_model_result)
  (st : casemate_model_result) :
  casemate_model_result :=
  match st with
  | {| cmr_log := logs; cmr_data := Ok _ _ cms |} =>
    let new_st := updater cms in
    new_st <| cmr_log := new_st.(cmr_log) ++ logs |>
  | e => e
  end
.

Definition insert_location
  (loc : sm_location)
  (cms : casemate_model_state) :
  casemate_model_state :=
  (cms <| cms_memory := <[ loc.(sl_phys_addr) := loc ]> cms.(cms_memory) |>)
.

Definition Minsert_location
  (loc : sm_location)
  (mon : casemate_model_result) :
  casemate_model_result :=
  match mon with
  | {| cmr_log := logs; cmr_data := Ok _ _ cms |} =>
    {|
      cmr_log := logs;
      cmr_data := Ok _ _ (insert_location loc cms)
    |}
  | e => e
  end
.
