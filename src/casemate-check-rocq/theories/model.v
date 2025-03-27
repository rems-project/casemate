Require Import String.
Require stdpp.bitvector.bitvector.
Require Import Cmap.cmap.
Require Import Zmap.zmap.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.
Require Import stdpp.gmap.
Require Import Recdef.

Require Export utils.

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

Record ghost_addr_range := {
  range_start : phys_addr_t;
  range_size : phys_addr_t;
}.

Record map_data_t := {
  oa_region : ghost_addr_range;
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

Record ghost_exploded_descriptor := mk_ghost_exploded_descriptor {
  ged_ia_region : ghost_addr_range;
  ged_level : level_t;
  ged_stage : entry_stage_t;
  ged_pte_kind : pte_rec;
  ged_state : sm_pte_state;
  (* address of the root of the PTE *)
  ged_owner : sm_owner_t;
}.
#[export] Instance eta_ghost_exploded_descriptor : Settable _ :=
  settable! mk_ghost_exploded_descriptor <ged_ia_region; ged_level; ged_stage; ged_pte_kind; ged_state; ged_owner>.


Record sm_location := mk_sm_location {
  (* sl_initialised : bool; *)
  sl_phys_addr : phys_addr_t;
  sl_val : u64;
  sl_pte : option ghost_exploded_descriptor;
  sl_thread_owner : option thread_identifier;
}.
#[export] Instance eta_sm_location : Settable _ :=
  settable! mk_sm_location <sl_phys_addr; sl_val; sl_pte; sl_thread_owner>.

Record owner_locks := {
  ol_len : u64;
  ol_owner_ids : list sm_owner_t;
  ol_locks : unit;
}.

(* The memory state is a map from address to simplified model location *)
Definition casemate_model_memory := cmap sm_location.

(* The memory initialised is stored here *)
Definition casemate_model_initialised := zmap unit.

(* per-CPU thread-local context *)
Record thrd_ctxt := {
  current_s1 : sm_owner_t;
  current_s2 : sm_owner_t;
}.

Definition casemate_model_thrd_ctxt := list thrd_ctxt.

(* Map of pgtable root to lock that owns it *)
Definition casemate_model_lock_owner_map := zmap u64.

(* Map from the locks to the lock state *)
Inductive write_authorization :=
  | WA_AUTHORIZED
  | WA_UNAUTHORIZED
.

Record lock_state := {
  ls_tid : thread_identifier;
  ls_write_authorization : write_authorization;
}.

Definition casemate_model_lock_state_map := zmap lock_state.


(* Storing roots for PTE walkthrough (we might need to distinguish S1 and S2 roots) *)

Record cm_root := {
  r_baddr : sm_owner_t;
  r_id : addr_id_t;
  r_refcount : u64;
}.

Record casemate_model_roots := mk_cm_roots {
  pr_s1 : list cm_root;
  pr_s2 : list cm_root;
}.
#[export] Instance eta_casemate_model_roots : Settable _ := settable! mk_cm_roots <pr_s1; pr_s2>.

Record casemate_model_state := mk_casemate_model_state {
  cm_roots : casemate_model_roots;
  cm_memory : casemate_model_memory;
  cm_initialised : casemate_model_initialised;
  cm_thrd_ctxt : casemate_model_thrd_ctxt;
  cm_lock_addr : casemate_model_lock_owner_map;
  cm_lock_state : casemate_model_lock_state_map;
}.
#[export] Instance eta_casemate_model_state : Settable _ :=
  settable! mk_casemate_model_state
    <cm_roots; cm_memory; cm_initialised; cm_thrd_ctxt; cm_lock_addr; cm_lock_state>.

Definition is_initialised (st : casemate_model_state) (addr : phys_addr_t) : bool :=
  match st.(cm_initialised) !! ((bv_shiftr_64 (phys_addr_val addr) b12)) with
  | Some _ => true
  | None => false
  end
.

Definition get_location
  (st : casemate_model_state)
  (addr : phys_addr_t) : option sm_location :=
  match st.(cm_memory) !! bv_shiftr_64 (phys_addr_val addr) b3 with
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
  (cm : casemate_model_state) : option u64 :=
  lookup (phys_addr_val (root_val owner)) cm.(cm_lock_addr).


Infix "!!" := get_location (at level 20).

Definition is_loc_thread_owned
  (cpu : thread_identifier)
  (location : sm_location)
  (cm : casemate_model_state) : bool :=
  match location.(sl_pte), location.(sl_thread_owner) with
  | Some _, Some thread_owner =>
    bool_decide (thread_owner = cpu)
  | _, _ => false
  end
.

Definition is_pte_well_locked
  (cpu : thread_identifier)
  (pte : ghost_exploded_descriptor)
  (cm : casemate_model_state) : bool :=
  match get_lock_of_owner pte.(ged_owner) cm with
  | None => false
  | Some addr =>
    match lookup addr cm.(cm_lock_state) with
    | Some {| ls_tid := lock_owner; ls_write_authorization := _ |} => bool_decide (lock_owner = cpu)
    | None => false
    end
  end
.

Definition should_visit
  (cpu : thread_identifier)
  (addr : phys_addr_t)
  (cm : casemate_model_state) : bool :=
  match cm !! addr with
  | None => true
  | Some location =>
      match location.(sl_pte) with
      | None => true
      | Some pte =>
        orb (is_loc_thread_owned cpu location cm) (is_pte_well_locked cpu pte cm)
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

Definition Mreturn (cm : casemate_model_state) : casemate_model_result :=
  {| cmr_log := nil; cmr_data := Ok _ _ cm |}.

Definition Mbind
  (r : casemate_model_result)
  (f : casemate_model_state -> casemate_model_result) :
  casemate_model_result :=
  match r.(cmr_data) with
  | Error _ _ e => r
  | Ok _ _ cm =>
    let s' := f cm in
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
  | {| cmr_log := logs; cmr_data := Ok _ _ cm |} =>
    let new_st := updater cm in
    new_st <| cmr_log := new_st.(cmr_log) ++ logs |>
  | e => e
  end
.

Definition insert_location
  (loc : sm_location)
  (cm : casemate_model_state) : casemate_model_state :=
  (cm <| cm_memory := <[ loc.(sl_phys_addr) := loc ]> cm.(cm_memory) |>)
.

Definition Minsert_location
  (loc : sm_location)
  (mon : casemate_model_result) :
  casemate_model_result :=
  match mon with
  | {| cmr_log := logs; cmr_data := Ok _ _ cm |} =>
    {| cmr_log := logs; cmr_data := Ok _ _ (insert_location loc cm) |}
  | e => e
  end
.

