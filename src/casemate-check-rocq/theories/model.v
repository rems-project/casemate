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

(* The memory state is a map from address to casemate model location *)
Definition casemate_model_memory := cmap sm_location.

(* The initialised memory is stored here *)
Definition casemate_model_initialised := zmap unit.

(* the map from root to lock address *)
Definition casemate_model_lock_addr := zmap u64.

(* the map from lock address to thread that acquired it if any *)
Definition casemate_model_lock_state := zmap thread_identifier.

Inductive write_authorization :=
  | write_authorized
  | write_unauthorized
.

Definition casemate_model_lock_write_authorization := zmap write_authorization.

(* Storing roots for PTE walkthrough (we might need to distinguish S1 and S2 roots) *)
Record casemate_model_roots := mk_pte_roots {
  cmr_s1 : list sm_owner_t;
  cmr_s2 : list sm_owner_t;
}.
#[export] Instance eta_pte_roots : Settable _ := settable! mk_pte_roots <cmr_s1; cmr_s2>.

Record casemate_model_state := mk_casemate_model_state {
  cms_roots : casemate_model_roots;
  cms_memory : casemate_model_memory;
  cms_initialised : casemate_model_initialised;
  cms_lock_addr : casemate_model_lock_addr;
  cms_lock_state : casemate_model_lock_state;
  cms_lock_authorization : casemate_model_lock_write_authorization
}.
#[export] Instance eta_casemate_model_state : Settable _ := 
  settable! mk_casemate_model_state 
    <cms_roots; cms_memory; cms_initialised; cms_lock_addr; cms_lock_state; cms_lock_authorization>.

Definition cms_init := {|
  cms_roots := {| cmr_s1 := []; cmr_s2 := []; |};
  cms_memory := ∅;
  cms_initialised := ∅;
  cms_lock_addr := ∅;
  cms_lock_state := ∅;
  cms_lock_authorization := ∅;
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
  lookup (phys_addr_val (root_val owner)) cms.(cms_lock_addr).
 

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
    | Some lock_owner => bool_decide (lock_owner = cpu)
    | None => false
    end
  end
.

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
  end
.

Inductive violation_type :=
  | VT_valid_on_invalid_unclean
  | VT_valid_on_valid
  | VT_release_unclean
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
  | CME_owned_pte_accessed_by_other_thread : string -> phys_addr_t -> casemate_model_error
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

(** States about page tables *)

(* Type used as input of the page table visitor function  *)
Record pgtable_traverse_context := mk_page_table_context {
  ptc_state: casemate_model_state;
  ptc_loc: option sm_location;
  ptc_partial_ia: phys_addr_t;
  ptc_addr: phys_addr_t;
  ptc_root: sm_owner_t;
  ptc_level: level_t;
  ptc_stage: entry_stage_t;
}.
#[export] Instance eta_page_table_context : Settable _ :=
  settable! mk_page_table_context <ptc_state; ptc_loc; ptc_partial_ia; ptc_addr; ptc_root; ptc_level; ptc_stage>.


