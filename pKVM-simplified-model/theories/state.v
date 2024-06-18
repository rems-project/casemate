Require Import String.
Require stdpp.bitvector.bitvector.
Require Import Cmap.cmap.
Require Import Zmap.zmap.
(* uses https://github.com/tchajed/coq-record-update *)
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
#[export] Instance eta_aut_invalid_unclean : Settable _ := settable! mk_aut_invalid_unclean <ai_invalidator_tid; ai_old_valid_desc; ai_lis>.


Record aut_invalid_clean := {
  aic_invalidator_tid : thread_identifier;
}.

Inductive sm_pte_state :=
  | SPS_STATE_PTE_VALID (valid_state:aut_valid)
  | SPS_STATE_PTE_INVALID_UNCLEAN (invalid_unclean_state:aut_invalid_unclean)
  | SPS_STATE_PTE_INVALID_CLEAN (invalid_clean_state:aut_invalid_clean)
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
  | PTER_PTE_KIND_TABLE (table_data:table_data_t)
  | PTER_PTE_KIND_MAP (map_data:map_data_t)
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
#[export] Instance eta_ghost_exploded_descriptor : Settable _ := settable! mk_ghost_exploded_descriptor <ged_ia_region; ged_level; ged_stage; ged_pte_kind; ged_state; ged_owner>.


Record sm_location := mk_sm_location {
  (* sl_initialised : bool; *)
  sl_phys_addr : phys_addr_t;
  sl_val : u64;
  sl_pte : option ghost_exploded_descriptor;
}.
#[export] Instance eta_sm_location : Settable _ := settable! mk_sm_location < sl_phys_addr; sl_val; sl_pte>.

(* Do we need locks? *)
Record owner_locks := {
  ol_len : u64;
  ol_owner_ids : list owner_t;
  ol_locks : unit (* TODO??? *);
}.

(* The memory state is a map from address to simplified model location *)
Definition ghost_simplified_model_state := cmap sm_location.

(* The zalloc'd memory is stored here *)
Definition ghost_simplified_model_zallocd := zmap unit.

(* the map from root to lock address *)
Definition ghost_simplified_model_lock_addr := zmap u64.

(* the map from lock address to thread that acquired it if any *)
Definition ghost_simplified_model_lock_state := zmap thread_identifier.

(* Storing roots for PTE walkthrough (we might need to distinguish S1 and S2 roots) *)
Record pte_roots := mk_pte_roots {
  pr_s1 : list owner_t;
  pr_s2 : list owner_t;
}.
#[export] Instance eta_pte_roots : Settable _ := settable! mk_pte_roots <pr_s1; pr_s2>.

Record ghost_simplified_memory := mk_ghost_simplified_model {
  gsm_roots : pte_roots;
  gsm_memory : ghost_simplified_model_state;
  gsm_zalloc : ghost_simplified_model_zallocd;
  gsm_lock_addr : ghost_simplified_model_lock_addr;
  gsm_lock_state : ghost_simplified_model_lock_state;
}.
#[export] Instance eta_ghost_simplified_memory : Settable _ := settable! mk_ghost_simplified_model <gsm_roots; gsm_memory; gsm_zalloc; gsm_lock_addr; gsm_lock_state>.

Definition is_zallocd (st : ghost_simplified_memory) (addr : phys_addr_t) : bool :=
  match st.(gsm_zalloc) !! ((bv_shiftr_64 (phys_addr_val addr) b12)) with
    | Some _ => true
    | None => false
  end
.

Definition get_location (st : ghost_simplified_memory) (addr : phys_addr_t) : option sm_location :=
  match st.(gsm_memory) !! bv_shiftr_64 (phys_addr_val addr) b3 with
    | Some loc => Some loc
    | None =>
      match is_zallocd st addr with
        | true => Some {| sl_phys_addr := addr; sl_val := b0; sl_pte := None; |}
        | false => None
      end
  end
.

Infix "!!" := get_location (at level 20) .


Definition is_well_locked (cpu : thread_identifier) (location : phys_addr_t) (st : ghost_simplified_memory) : bool :=
  match st !! location with
    | None => true
    | Some location =>
      match location.(sl_pte) with
        | None => true
        | Some pte =>
          match lookup (phys_addr_val (root_val pte.(ged_owner))) st.(gsm_lock_addr) with
            | None => false
            | Some addr =>
              match lookup addr st.(gsm_lock_state) with
                | Some lock_owner => bool_decide (lock_owner = cpu)
                | None => false
              end
          end
      end
  end
.

Inductive violation_type :=
  | VT_valid_on_invalid_unclean
  | VT_valid_on_valid
  | VT_release_unclean
.

Inductive ghost_simplified_model_error :=
  | GSME_bbm_violation : violation_type -> phys_addr_t -> ghost_simplified_model_error
  | GSME_not_a_pte : string -> phys_addr_t -> ghost_simplified_model_error
  | GSME_inconsistent_read
  | GSME_uninitialised : string -> phys_addr_t -> ghost_simplified_model_error
  | GSME_unclean_child : phys_addr_t -> ghost_simplified_model_error
  | GSME_double_use_of_pte
  | GSME_root_already_exists
  | GSME_unaligned_write
  | GSME_double_lock_acquire : thread_identifier -> thread_identifier -> ghost_simplified_model_error
  | GSME_transition_without_lock : phys_addr_t -> ghost_simplified_model_error
  | GSME_unimplemented
  | GSME_internal_error : internal_error_type -> ghost_simplified_model_error
.

Record ghost_simplified_model_result := mk_ghost_simplified_model_result {
  gsmsr_log : list log_element;
  gsmsr_data : result ghost_simplified_memory ghost_simplified_model_error
}.
#[export] Instance eta_ghost_simplified_model_result : Settable _ := settable! mk_ghost_simplified_model_result <gsmsr_log; gsmsr_data>.

Definition Mreturn (st : ghost_simplified_memory) : ghost_simplified_model_result :=
  {| gsmsr_log := nil;
    gsmsr_data := Ok _ _ st |}.

Definition Mbind (r : ghost_simplified_model_result) (f : ghost_simplified_memory -> ghost_simplified_model_result) : ghost_simplified_model_result :=
  match r.(gsmsr_data) with
  | Error _ _ s => r
  | Ok _ _ st =>
    let st' := f st in
    {| gsmsr_log := app st'.(gsmsr_log) r.(gsmsr_log);
      gsmsr_data := st'.(gsmsr_data);
    |}
  end.

Definition Merror (s : ghost_simplified_model_error) : ghost_simplified_model_result :=
  {| gsmsr_log := nil;
    gsmsr_data := Error _ _ s |}.

Definition Mlog (s : log_element) (r : ghost_simplified_model_result) : ghost_simplified_model_result :=
  r <|gsmsr_log := s :: r.(gsmsr_log) |>.


Definition Mupdate_state (updater : ghost_simplified_memory -> ghost_simplified_model_result) (st : ghost_simplified_model_result) : ghost_simplified_model_result :=
  match st with
    | {| gsmsr_log := logs; gsmsr_data := Ok _ _ st |} =>
      let new_st := updater st in
      new_st <| gsmsr_log := new_st.(gsmsr_log) ++ logs |>
    | e => e
  end
.

Definition insert_location (loc : sm_location) (st : ghost_simplified_memory) : ghost_simplified_memory :=
  (st <| gsm_memory := <[ loc.(sl_phys_addr) := loc ]> st.(gsm_memory) |>)
.

Definition Minsert_location (loc : sm_location) (mon : ghost_simplified_model_result) : ghost_simplified_model_result :=
  match mon with
    | {| gsmsr_log := logs; gsmsr_data := Ok _ _ st |} =>
      {|
        gsmsr_log := logs;
        gsmsr_data := Ok _ _ (insert_location loc st)
      |}
    | e => e
  end
.



(** States about page tables *)

(* Type used as input of the page table visitor function  *)
Record page_table_context := mk_page_table_context {
  ptc_state: ghost_simplified_memory;
  ptc_loc: option sm_location;
  ptc_partial_ia: phys_addr_t;
  ptc_addr: phys_addr_t;
  ptc_root: owner_t;
  ptc_level: level_t;
  ptc_stage: stage_t;
}.
#[export] Instance eta_page_table_context : Settable _ := settable! mk_page_table_context <ptc_state; ptc_loc; ptc_partial_ia; ptc_addr; ptc_root; ptc_level; ptc_stage>.

Definition PTE_BIT_VALID : u64 := b1. (* binary: 0001 *)

Definition PTE_BIT_TABLE : u64 := b2. (* binary: 0010 *)

Definition GENMASK (l r : u64) : u64 :=
(bv_and_64
  ((bv_not_64 b0) ≪ r)
  ((bv_not_64 b0) ≫ (bv_sub_64 (BV64 63) l))
).
(**  0......0  1....1  0....0
  *  i zeros          j zeros
  *)

(* Definition PTE_BITS_ADDRESS : u64 := GENMASK b47 b12. *)
Definition PTE_BITS_ADDRESS : u64 := BV64 0xfffffffff000%Z.

(* Definition PTE_FIELD_UPPER_ATTRS_SW_MASK : u64 := GENMASK (BV 64 58) (BV 64 55). *)
Definition NOT_PTE_FIELD_UPPER_ATTRS_SW_MASK : u64 := BV64 0x7fffffffffffff%Z.

Definition is_desc_valid (descriptor : u64) : bool :=
  negb ((bv_and_64 descriptor PTE_BIT_VALID) b=? b0)
.

Definition OA_shift (level : level_t) : u64 :=
match level with
  | l1 => BV64 (12 + 9 + 9)
  | l2 => BV64 (12 + 9 )
  | l3 => b12
  | _ => b0  (* Should not happen*)
end
.

Definition _mask_OA_shift_l1 := BV64 0xffffc0000000%Z.
Definition _mask_OA_shift_l2 := BV64 0xffffffe00000%Z.
Definition _mask_OA_shift_l3 := BV64 0xfffffffff000%Z.

Definition mask_OA_shift (level : level_t) : u64 :=
  match level with
    | l1 => _mask_OA_shift_l1
    | l2 => _mask_OA_shift_l2
    | l3 => _mask_OA_shift_l3
    | _ => b0 (* Should not happen*)
  end
.


Definition _map_size_l0 := BV64 0x8000000000%Z. (* bv_shiftl b512     (BV64 30) *) (* 512 Go *) 
Definition _map_size_l1 := BV64 0x0040000000%Z. (* bv_shiftl (b1)     (BV64 30) *) (* 1 Go *)   
Definition _map_size_l2 := BV64 0x0000200000%Z. (* bv_shiftl (b2)     (BV64 20) *) (* 2 Mo *)   
Definition _map_size_l3 := BV64 0x0000001000%Z. (* bv_shiftl (BV64 4) (BV64 10) *) (* 4 Ko *)   

Definition map_size (level : level_t) : phys_addr_t :=
match level with
  | l0 => Phys_addr _map_size_l0 (* bv_shiftl b512     (BV64 30) *) (* 512 Go *)
  | l1 => Phys_addr _map_size_l1 (* bv_shiftl (b1)     (BV64 30) *) (* 1 Go *)
  | l2 => Phys_addr _map_size_l2 (* bv_shiftl (b2)     (BV64 20) *) (* 2 Mo *)
  | l3 => Phys_addr _map_size_l3 (* bv_shiftl (BV64 4) (BV64 10) *) (* 4 Ko *)
  | _ => pa0  (* Should not happen*)
end
.

Definition _align_4k_big_bv := BV64 0xfffffffffffffc00%Z. (* bv_not b1023 *)
Definition align_4k (addr : phys_addr_t) : phys_addr_t :=
  Phys_addr (bv_and_64 (phys_addr_val addr) _align_4k_big_bv)
.

Definition is_desc_table (descriptor : u64) (level : level_t) :=
  match level with
    | l3 => false
    | _ => (bv_and_64 descriptor PTE_BIT_TABLE) b=? PTE_BIT_TABLE
  end
.

Definition extract_table_address (pte_val : u64) : phys_addr_t :=
Phys_addr (bv_and_64 pte_val PTE_BITS_ADDRESS).

Definition extract_output_address (pte_val : u64) (level : level_t) :=
bv_and_64 pte_val (mask_OA_shift level)
.

Definition initial_state (partial_ia : phys_addr_t) (desc : u64) (level : level_t) (cpu_id : thread_identifier) (pte_kind : pte_rec) (stage : stage_t) : sm_pte_state :=
  match pte_kind with
    | PTER_PTE_KIND_INVALID =>
      SPS_STATE_PTE_INVALID_CLEAN ({|aic_invalidator_tid := cpu_id |})
    | PTER_PTE_KIND_MAP _ | PTER_PTE_KIND_TABLE _ =>
      SPS_STATE_PTE_VALID {|lvs := [] |}
  end
.

Definition deconstruct_pte (cpu_id : thread_identifier) (partial_ia : phys_addr_t) (desc : u64) (level : level_t) (root : owner_t) (stage : stage_t) : ghost_exploded_descriptor :=
  let pte_kind :=
    if is_desc_valid desc then
      if is_desc_table desc level then
        PTER_PTE_KIND_TABLE (
          {|
            next_level_table_addr := extract_table_address desc;
          |}
        )
      else
        PTER_PTE_KIND_MAP (
          {|
            oa_region := {| range_start := extract_table_address desc; range_size := map_size level |}
          |}
        )
    else
      PTER_PTE_KIND_INVALID
  in
  {|
    ged_ia_region :=
      {|
        range_start := partial_ia; (* It is already conveniently aligned *)
        range_size := map_size level (* The mapped (or partially mapped) region only depends on the level *)
      |};
    ged_level := level;
    ged_stage := stage;
    ged_pte_kind := pte_kind;
    ged_state := initial_state partial_ia desc level cpu_id pte_kind stage;
    ged_owner := root;
  |}.

Fixpoint traverse_pgt_from_aux (root : owner_t) (table_start partial_ia : phys_addr_t) (level : level_t) (stage : stage_t) (visitor_cb : page_table_context -> ghost_simplified_model_result)  (max_call_number : nat) (mon : ghost_simplified_model_result) : ghost_simplified_model_result :=
  match max_call_number with
   | S max_call_number => traverse_pgt_from_offs root table_start partial_ia level stage visitor_cb b0 max_call_number mon
   | O => (* Coq typechecking needs a guarantee that the function terminates, that is why the max_call_number nat exists,
            the number of recursive calls is bounded. *)
   {| gsmsr_log := [] ; gsmsr_data := Error _ _ (GSME_internal_error IET_infinite_loop) |}
  end
  (* This is the for loop that iterates over all the entries of a page table *)
with traverse_pgt_from_offs (root : owner_t) (table_start partial_ia : phys_addr_t) (level : level_t) (stage : stage_t) (visitor_cb : page_table_context -> ghost_simplified_model_result) (i : u64) (max_call_number : nat) (mon : ghost_simplified_model_result) : ghost_simplified_model_result :=
  match max_call_number with
    | S max_call_number =>
      if i b=? b512 then
        (* We are done with this page table *)
        mon
      else
        match mon with
          | {| gsmsr_log := _; gsmsr_data := Error _ _ _ |}  => mon (* If it fails, it fails *)
          | {| gsmsr_log := _; gsmsr_data := Ok _ _ st |} as mon =>
            let addr := table_start pa+ (Phys_addr (b8 b* i)) in
            let location := st !! addr in
            let visitor_state_updater s := (* We construct the context, we don't know if the location exists but the visitor might create it *)
              visitor_cb
              {|
                ptc_state := s;
                ptc_loc := location;
                ptc_addr := addr;
                ptc_partial_ia := partial_ia;
                ptc_root := root;
                ptc_level:= level;
                ptc_stage := stage;
              |}
            in
            let mon := Mupdate_state visitor_state_updater mon in
            match mon.(gsmsr_data) with (* The visitor can edit the state and write logs *)
              | Error _ _ r  => mon (* If it fails, it fails *)
              | Ok _ _ updated_state =>
                let location := updated_state !! addr in
                match location with
                  | None => mon (* If the page table was not initialised, we cannot continue (or we could ignore this and continue.) *)
                  | Some location =>
                    let exploded_desc :=
                      match location.(sl_pte) with
                        | Some pte => pte
                        | None => (* 0 is a placeholder, we do not use it afterwards *)
                          deconstruct_pte (Thread_identifier 0) partial_ia location.(sl_val) level root stage
                      end
                    in
                    let mon :=
                      (* if it is a valid descriptor, recursively call pgt_traversal_from, otherwise, continue *)
                      match exploded_desc.(ged_pte_kind) with
                        | PTER_PTE_KIND_TABLE table_data =>
                          (* If it is a page table descriptor, we we traverse the sub-page table *)
                          let rec_table_start := table_data.(next_level_table_addr) in
                          let next_partial_ia := exploded_desc.(ged_ia_region).(range_start) pa+ (((Phys_addr i) pa* exploded_desc.(ged_ia_region).(range_size))) in
                          (* recursive call: explore sub-pgt *)
                          traverse_pgt_from_aux root rec_table_start next_partial_ia (next_level level) stage visitor_cb max_call_number mon
                        | _ => mon
                      end
                    in
                    traverse_pgt_from_offs root table_start partial_ia level stage visitor_cb (bv_add_64 i b1)  max_call_number mon
                end
            end
        end
    | O => {| gsmsr_log := []; gsmsr_data := Error _ _ (GSME_internal_error IET_infinite_loop) |}
  end
.

Definition traverse_pgt_from (root : owner_t) (table_start partial_ia : phys_addr_t) (level : level_t) (stage : stage_t) (visitor_cb : page_table_context -> ghost_simplified_model_result) (st : ghost_simplified_memory) : ghost_simplified_model_result :=
  traverse_pgt_from_aux root table_start partial_ia level stage visitor_cb (4*n512) (Mreturn st)
.

Definition traverse_pgt_from_root (root : owner_t) (stage : stage_t) (visitor_cb : page_table_context -> ghost_simplified_model_result) (st : ghost_simplified_memory) : ghost_simplified_model_result :=
  traverse_pgt_from root (root_val root) pa0 l0 stage visitor_cb st
.

(* Generic function (for s1 and s2) to traverse all page tables starting with root in roots *)
Fixpoint traverse_si_pgt_aux (th : option thread_identifier) (visitor_cb : page_table_context -> ghost_simplified_model_result) (stage : stage_t) (roots : list owner_t) (st : ghost_simplified_model_result) : ghost_simplified_model_result :=
  match roots with
    | r :: q =>
      (* If the state is failed, there is no point in going on *)
      match st.(gsmsr_data) with
        | Error _ _ _ => st
        | _ =>
          let updater s := 
            let should_update :=
            match th with
              | None => true
              | Some tid => is_well_locked tid (root_val r) s
            end
            in
            if should_update then traverse_pgt_from r (root_val r) pa0 l0 stage visitor_cb s else Mreturn s
          in
          let st :=  Mupdate_state updater st in
          traverse_si_pgt_aux th visitor_cb stage q st
      end
    | [] => st
  end
.

(* Generic function to traverse all S1 or S2 roots *)
Definition traverse_si_pgt (th : option thread_identifier) (st : ghost_simplified_memory) (visitor_cb : page_table_context -> ghost_simplified_model_result) (stage : stage_t) : ghost_simplified_model_result :=
  let roots :=
    match stage with
      | S2 => st.(gsm_roots).(pr_s2)
      | S1 => st.(gsm_roots).(pr_s1)
    end
  in
  traverse_si_pgt_aux th visitor_cb stage roots {| gsmsr_log := nil; gsmsr_data := Ok _ _ st |}
.

Definition traverse_all_pgt (th : option thread_identifier) (st: ghost_simplified_memory) (visitor_cb : page_table_context -> ghost_simplified_model_result) :=
  match traverse_si_pgt th st visitor_cb S1 with
    | {|gsmsr_log := logs; gsmsr_data := Ok _ _ st|} =>
      let res := traverse_si_pgt th st visitor_cb S2 in
      res <| gsmsr_log := res.(gsmsr_log) ++ logs |>
    | err => err
  end
.

(*******************************************************************)
(* Some generic walker functions to mark and unmark entries as PTE *)

Definition mark_cb (cpu_id : thread_identifier) (ctx : page_table_context) : ghost_simplified_model_result :=
  match ctx.(ptc_loc) with
    | Some location =>
      match location.(sl_pte) with
        | Some _ =>
          {| gsmsr_log := []; gsmsr_data := Error _ _ GSME_double_use_of_pte |}
        | None =>
          let new_descriptor := deconstruct_pte cpu_id ctx.(ptc_partial_ia) location.(sl_val) ctx.(ptc_level) ctx.(ptc_root) ctx.(ptc_stage) in
          let new_location :=  (location <| sl_pte := (Some new_descriptor) |>) in
          let new_state := ctx.(ptc_state) <| gsm_memory := <[ location.(sl_phys_addr) := new_location]> ctx.(ptc_state).(gsm_memory) |> in
          Mreturn new_state
      end
    | None =>  (* In the C model, it is not an issue memory can be read, here we cannot continue because we don't have the value at that memory location *)
        {|
          gsmsr_log := [];
          gsmsr_data := Error _ _ (GSME_uninitialised "mark_cb" ctx.(ptc_addr))
        |}
  end
.

Definition unmark_cb (cpu_id : thread_identifier) (ctx : page_table_context) : ghost_simplified_model_result :=
  match ctx.(ptc_loc) with
    | Some location =>
      match location.(sl_pte) with
        | Some desc =>
          let new_loc := location <|sl_pte := None |> in
          let new_st := <[ location.(sl_phys_addr) := new_loc ]> ctx.(ptc_state).(gsm_memory) in
          {| gsmsr_log := nil; gsmsr_data := Ok _ _ (ctx.(ptc_state) <| gsm_memory := new_st |>) |}
        | None =>
          {| gsmsr_log := []; gsmsr_data := Error _ _ (GSME_not_a_pte "unmark_cb"%string ctx.(ptc_addr)) |}
      end
    | None =>  (* In the C model, it is not an issue memory can be read, here we cannot continue because we don't have the value at that memory location *)
        {|
          gsmsr_log := [];
          gsmsr_data := Error _ _ (GSME_uninitialised "unmark_cb" ctx.(ptc_addr))
        |}
  end
.

