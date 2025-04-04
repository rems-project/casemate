Require Import String.
Require stdpp.bitvector.bitvector.
Require Import Cmap.cmap.
Require Import Zmap.zmap.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.
Require Import stdpp.gmap.
Require Import Recdef.

Require Import state.
Require Export utils.


Definition PTE_BIT_VALID : u64 := b1. (* binary: 0001 *)
Definition PTE_BIT_TABLE : u64 := b2. (* binary: 0010 *)

(**  0......0  1....1  0....0
  *  i zeros          j zeros
  *)
Definition GENMASK (l r : u64) : u64 :=
  (bv_and_64
    ((bv_not_64 b0) ≪ r)
    ((bv_not_64 b0) ≫ (bv_sub_64 (BV64 63) l))).

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
  | l2 => BV64 (12 + 9)
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
  bv_and_64 pte_val (mask_OA_shift level).

Definition initial_state
  (cpu_id : thread_identifier)
  (pte_kind : pte_rec) :
  sm_pte_state :=
  match pte_kind with
  | PTER_PTE_KIND_INVALID =>
    SPS_STATE_PTE_INVALID_CLEAN ({| aic_invalidator_tid := cpu_id |})
  | PTER_PTE_KIND_MAP _
  | PTER_PTE_KIND_TABLE _ =>
    SPS_STATE_PTE_VALID {| lvs := [] |}
  end
.

Definition deconstruct_pte_kind (desc : u64) (level : level_t) :=
  if is_desc_valid desc then
    if is_desc_table desc level then
      PTER_PTE_KIND_TABLE ({| next_level_table_addr := extract_table_address desc; |})
    else
      PTER_PTE_KIND_MAP (
        {| oa_region := {|
                range_start := extract_table_address desc;
                range_size := map_size level |} |})
  else
    PTER_PTE_KIND_INVALID
.

Definition deconstruct_pte
  (cpu_id : thread_identifier)
  (partial_ia : phys_addr_t)
  (desc : u64)
  (level : level_t)
  (root : owner_t)
  (stage : stage_t) :
  ghost_exploded_descriptor :=
  let pte_kind := deconstruct_pte_kind desc level in
  {|
    ged_ia_region :=
      {|
        range_start := partial_ia; (* It is already aligned *)
        range_size := map_size level (* The mapped (or partially mapped) region only depends on the level *)
      |};
    ged_level := level;
    ged_stage := stage;
    ged_pte_kind := pte_kind;
    ged_state := initial_state cpu_id pte_kind;
    ged_owner := root;
  |}
.

(* Coq typechecking needs a guarantee that the function terminates, that is why the max_call_number nat exists,
          the number of recursive calls is bounded. *)
Fixpoint traverse_pgt_from_aux
  (root : owner_t)
  (table_start partial_ia : phys_addr_t)
  (level : level_t)
  (stage : stage_t)
  (visitor_cb : page_table_context -> ghost_simplified_model_result)
  (max_call_number : nat)
  (mon : ghost_simplified_model_result) : 
  ghost_simplified_model_result :=
  match max_call_number with
  | S max_call_number => traverse_pgt_from_offs 
                            root 
                            table_start partial_ia 
                            level 
                            stage 
                            visitor_cb 
                            b0 
                            max_call_number 
                            mon
  | O => Merror (GSME_internal_error IET_infinite_loop)
  end
  (* This is the for loop that iterates over all the entries of a page table *)
with traverse_pgt_from_offs
      (root : owner_t)
      (table_start partial_ia : phys_addr_t)
      (level : level_t)
      (stage : stage_t)
      (visitor_cb : page_table_context -> ghost_simplified_model_result)
      (i : u64)
      (max_call_number : nat)
      (mon : ghost_simplified_model_result):
      ghost_simplified_model_result :=
  match max_call_number with
  | S max_call_number =>
    if i b=? b512 then mon (* We are done with this page table *)
    else
      match mon with
      | {| gsmsr_log := _; gsmsr_data := Error _ _ _ |} => mon (* If it fails, it fails *)
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
                let next_partial_ia := exploded_desc.(ged_ia_region).(range_start) pa+
                    (((Phys_addr i) pa* exploded_desc.(ged_ia_region).(range_size))) in
                (* recursive call: explore sub-pgt *)
                traverse_pgt_from_aux
                  root 
                  rec_table_start next_partial_ia 
                  (next_level level) 
                  stage 
                  visitor_cb 
                  max_call_number 
                  mon
              | _ => mon
              end
            in
            traverse_pgt_from_offs 
              root 
              table_start partial_ia 
              level stage 
              visitor_cb 
              (bv_add_64 i b1)  
              max_call_number 
              mon
          end
        end
      end
  | O => Merror (GSME_internal_error IET_infinite_loop)
  end
.

Definition traverse_pgt_from
  (root : owner_t)
  (table_start partial_ia : phys_addr_t)
  (level : level_t)
  (stage : stage_t)
  (visitor_cb : page_table_context -> ghost_simplified_model_result)
  (gsm : ghost_simplified_model) :
  ghost_simplified_model_result :=
  traverse_pgt_from_aux
    root
    table_start
    partial_ia
    level stage
    visitor_cb
    (4*n512)
    (Mreturn gsm)
.

Definition traverse_pgt_from_root
  (root : owner_t)
  (stage : stage_t)
  (visitor_cb : page_table_context -> ghost_simplified_model_result)
  (gsm : ghost_simplified_model) :
  ghost_simplified_model_result :=
  traverse_pgt_from 
    root 
    (root_val root) 
    pa0 
    l0 
    stage 
    visitor_cb
    gsm
.

(* Generic function (for s1 and s2) to traverse all page tables starting with root in roots *)
Fixpoint traverse_si_pgt_aux
  (th : option thread_identifier)
  (visitor_cb : page_table_context -> ghost_simplified_model_result)
  (stage : stage_t)
  (roots : list owner_t)
  (res : ghost_simplified_model_result) :
  ghost_simplified_model_result :=
  match roots, res.(gsmsr_data) with
  | [], _ => res
  (* If the state is failed, there is no point in going on *)
  | _, Error _ _ _ => res
  | r :: q, _ =>
    let res := Mupdate_state (traverse_pgt_from r (root_val r) pa0 l0 stage visitor_cb) res in
    traverse_si_pgt_aux th visitor_cb stage q res
  end
.

(* Generic function to traverse all S1 or S2 roots *)
Definition traverse_si_pgt
  (th : option thread_identifier)
  (gsm : ghost_simplified_model)
  (visitor_cb : page_table_context -> ghost_simplified_model_result)
  (stage : stage_t) :
  ghost_simplified_model_result :=
  let roots :=
    match stage with
    | S2 => gsm.(gsm_roots).(pr_s2)
    | S1 => gsm.(gsm_roots).(pr_s1)
    end
  in
  traverse_si_pgt_aux th visitor_cb stage roots (Mreturn gsm)
.

Definition traverse_all_pgt
  (th : option thread_identifier)
  (gsm : ghost_simplified_model)
  (visitor_cb : page_table_context -> ghost_simplified_model_result) :=
  match traverse_si_pgt th gsm visitor_cb S1 with
  | {| gsmsr_log := logs; gsmsr_data := Ok _ _ gsm |} => 
    let res := traverse_si_pgt th gsm visitor_cb S2 in
    res <| gsmsr_log := res.(gsmsr_log) ++ logs |>
  | err => err
  end
.

(*******************************************************************)
(* Some generic walker functions to mark and unmark entries as PTE *)

Definition mark_cb
  (cpu_id : thread_identifier)
  (ctx : page_table_context) :
  ghost_simplified_model_result :=
  match ctx.(ptc_loc) with
  | Some location =>
    match location.(sl_pte) with
    | Some _ => Merror (GSME_double_use_of_pte ctx.(ptc_addr))
    | None =>
      let new_desc := deconstruct_pte cpu_id ctx.(ptc_partial_ia) location.(sl_val) ctx.(ptc_level) ctx.(ptc_root) ctx.(ptc_stage) in
      let new_location := location <| sl_pte := (Some new_desc) |> <| sl_thread_owner := None |> in
      let new_state := ctx.(ptc_state) <| gsm_memory := <[ location.(sl_phys_addr) := new_location]> ctx.(ptc_state).(gsm_memory) |> in
      Mreturn new_state
    end
  | None =>  (* In the C model, it is not an issue memory can be read, here we cannot continue because we don't have the value at that memory location *)
    Merror (GSME_uninitialised "mark_cb" ctx.(ptc_addr))
  end
.

Definition unmark_cb
  (cpu_id : thread_identifier)
  (ctx : page_table_context) :
  ghost_simplified_model_result :=
  match ctx.(ptc_loc) with
  | Some location =>
    match location.(sl_pte) with
      | Some _ =>
        let new_loc := location <| sl_pte := None |> in
        let new_st := <[ location.(sl_phys_addr) := new_loc ]> ctx.(ptc_state).(gsm_memory) in
        Mreturn (ctx.(ptc_state) <| gsm_memory := new_st |>)
      | None =>
        Merror (GSME_not_a_pte "unmark_cb"%string ctx.(ptc_addr))
    end
  | None =>  (* In the C model, it is not an issue memory can be read, here we cannot continue because we don't have the value at that memory location *)
      Merror (GSME_uninitialised "unmark_cb" ctx.(ptc_addr))
  end
.

Definition mark_not_writable_cb
  (cpu_id : thread_identifier)
  (ctx : page_table_context) :
  ghost_simplified_model_result :=
  match ctx.(ptc_loc) with
  | Some location =>
    match location.(sl_thread_owner) with
    | None =>
        match location.(sl_pte) with
        | Some desc =>
          let new_desc := desc <| ged_state := SPS_STATE_PTE_NOT_WRITABLE |> in
          let new_location := location <| sl_pte := Some new_desc |> in
          let new_gsm := <[ location.(sl_phys_addr) := new_location ]> ctx.(ptc_state).(gsm_memory) in
          Mreturn (ctx.(ptc_state) <| gsm_memory := new_gsm |>)
        | None =>
          Merror (GSME_not_a_pte "mark_not_writable"%string ctx.(ptc_addr))
      end
    | Some tho => Merror (GSME_parent_invalidated location.(sl_phys_addr))
    end
  | None =>  (* In the C model, it is not an issue memory can be read, here we cannot continue because we don't have the value at that memory location *)
      Merror (GSME_uninitialised "mark_not_writable" ctx.(ptc_addr))
  end
.
