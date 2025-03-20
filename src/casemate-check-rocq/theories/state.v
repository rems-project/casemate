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
  ged_stage : stage_t;
  ged_pte_kind : pte_rec;
  ged_state : sm_pte_state;
  (* address of the root of the PTE *)
  ged_owner : owner_t;
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
  ol_owner_ids : list owner_t;
  ol_locks : unit;
}.

(* The memory state is a map from address to simplified model location *)
Definition casemate_model_state := cmap sm_location.

(* The zalloc'd memory is stored here *)
Definition casemate_model_zallocd := zmap unit.

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
Record pte_roots := mk_pte_roots {
  pr_s1 : list owner_t;
  pr_s2 : list owner_t;
}.
#[export] Instance eta_pte_roots : Settable _ := settable! mk_pte_roots <pr_s1; pr_s2>.

Record casemate_model := mk_casemate_model {
  gsm_roots : pte_roots;
  gsm_memory : casemate_model_state;
  gsm_zalloc : casemate_model_zallocd;
  gsm_lock_addr : casemate_model_lock_addr;
  gsm_lock_state : casemate_model_lock_state;
  gsm_lock_authorization : casemate_model_lock_write_authorization
}.
#[export] Instance eta_casemate_model : Settable _ :=
  settable! mk_casemate_model
    <gsm_roots; gsm_memory; gsm_zalloc; gsm_lock_addr; gsm_lock_state; gsm_lock_authorization>.

Definition is_zallocd (st : casemate_model) (addr : phys_addr_t) : bool :=
  match st.(gsm_zalloc) !! ((bv_shiftr_64 (phys_addr_val addr) b12)) with
    | Some _ => true
    | None => false
  end
.

Definition get_location
  (st : casemate_model)
  (addr : phys_addr_t) : option sm_location :=
  match st.(gsm_memory) !! bv_shiftr_64 (phys_addr_val addr) b3 with
  | Some loc => Some loc
  | None =>
    match is_zallocd st addr with
    | true => Some {| sl_phys_addr := addr; sl_val := b0; sl_pte := None; sl_thread_owner := None |}
    | false => None
    end
  end
.

Definition get_lock_of_owner
  (owner : owner_t)
  (gsm : casemate_model) : option u64 :=
  lookup (phys_addr_val (root_val owner)) gsm.(gsm_lock_addr).


Infix "!!" := get_location (at level 20).

Definition is_loc_thread_owned
  (cpu : thread_identifier)
  (location : sm_location)
  (gsm : casemate_model) : bool :=
  match location.(sl_pte), location.(sl_thread_owner) with
  | Some _, Some thread_owner =>
    bool_decide (thread_owner = cpu)
  | _, _ => false
  end
.

Definition is_pte_well_locked
  (cpu : thread_identifier)
  (pte : ghost_exploded_descriptor)
  (gsm : casemate_model) : bool :=
  match get_lock_of_owner pte.(ged_owner) gsm with
  | None => false
  | Some addr =>
    match lookup addr gsm.(gsm_lock_state) with
    | Some lock_owner => bool_decide (lock_owner = cpu)
    | None => false
    end
  end
.

Definition should_visit
  (cpu : thread_identifier)
  (addr : phys_addr_t)
  (gsm : casemate_model) : bool :=
  match gsm !! addr with
  | None => true
  | Some location =>
      match location.(sl_pte) with
      | None => true
      | Some pte =>
        orb (is_loc_thread_owned cpu location gsm) (is_pte_well_locked cpu pte gsm)
      end
  end
.

Inductive violation_type :=
  | VT_valid_on_invalid_unclean
  | VT_valid_on_valid
  | VT_release_unclean
.

Inductive casemate_model_error :=
  | GSME_bbm_violation : violation_type -> phys_addr_t -> casemate_model_error
  | GSME_not_a_pte : string -> phys_addr_t -> casemate_model_error
  | GSME_inconsistent_read
  | GSME_uninitialised : string -> phys_addr_t -> casemate_model_error
  | GSME_unclean_child : phys_addr_t -> casemate_model_error
  | GSME_write_on_not_writable : phys_addr_t -> casemate_model_error
  | GSME_double_use_of_pte : phys_addr_t -> casemate_model_error
  | GSME_root_already_exists
  | GSME_unaligned_write
  | GSME_double_lock_acquire : thread_identifier -> thread_identifier -> casemate_model_error
  | GSME_transition_without_lock : phys_addr_t -> casemate_model_error
  | GSME_write_without_authorization : phys_addr_t -> casemate_model_error
  | GSME_unimplemented
  | GSME_internal_error : internal_error_type -> casemate_model_error
  | GSME_parent_invalidated : phys_addr_t -> casemate_model_error
  | GSME_owned_pte_accessed_by_other_thread : string -> phys_addr_t -> casemate_model_error
.

Record casemate_model_result := mk_casemate_model_result {
  gsmsr_log : list log_element;
  gsmsr_data : result casemate_model casemate_model_error
}.

#[export] Instance eta_casemate_model_result : Settable _ :=
  settable! mk_casemate_model_result <gsmsr_log; gsmsr_data>.

Definition Mreturn (gsm : casemate_model) : casemate_model_result :=
  {| gsmsr_log := nil; gsmsr_data := Ok _ _ gsm |}.

Definition Mbind
  (r : casemate_model_result)
  (f : casemate_model -> casemate_model_result) :
  casemate_model_result :=
  match r.(gsmsr_data) with
  | Error _ _ e => r
  | Ok _ _ gsm =>
    let s' := f gsm in
    {| gsmsr_log := app s'.(gsmsr_log) r.(gsmsr_log);
       gsmsr_data := s'.(gsmsr_data); |}
  end.

Definition Merror (gse : casemate_model_error) : casemate_model_result :=
  {| gsmsr_log := nil; gsmsr_data := Error _ _ gse |}.

Definition Mlog
  (s : log_element)
  (r : casemate_model_result) : casemate_model_result :=
  r <|gsmsr_log := s :: r.(gsmsr_log) |>.

Definition Mupdate_state
  (updater : casemate_model -> casemate_model_result)
  (st : casemate_model_result) :
  casemate_model_result :=
  match st with
  | {| gsmsr_log := logs; gsmsr_data := Ok _ _ gsm |} =>
    let new_st := updater gsm in
    new_st <| gsmsr_log := new_st.(gsmsr_log) ++ logs |>
  | e => e
  end
.

Definition insert_location
  (loc : sm_location)
  (gsm : casemate_model) : casemate_model :=
  (gsm <| gsm_memory := <[ loc.(sl_phys_addr) := loc ]> gsm.(gsm_memory) |>)
.

Definition Minsert_location
  (loc : sm_location)
  (mon : casemate_model_result) :
  casemate_model_result :=
  match mon with
  | {| gsmsr_log := logs; gsmsr_data := Ok _ _ gsm |} =>
    {|
      gsmsr_log := logs;
      gsmsr_data := Ok _ _ (insert_location loc gsm)
    |}
  | e => e
  end
.

(** States about page tables *)

(* Type used as input of the page table visitor function  *)
Record page_table_context := mk_page_table_context {
  ptc_state: casemate_model;
  ptc_loc: option sm_location;
  ptc_partial_ia: phys_addr_t;
  ptc_addr: phys_addr_t;
  ptc_root: owner_t;
  ptc_level: level_t;
  ptc_stage: stage_t;
}.
#[export] Instance eta_page_table_context : Settable _ :=
  settable! mk_page_table_context <ptc_state; ptc_loc; ptc_partial_ia; ptc_addr; ptc_root; ptc_level; ptc_stage>.


