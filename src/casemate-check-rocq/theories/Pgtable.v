From RecordUpdate Require Export RecordSet.
Import RecordSetNotations.
Require Import Lists.List.

Require Export ArchHeader.
Require Export ModelHeader.
Require Export PgtableHeader.
Require Import Machine.
Require Import Blobs.

Definition PTE_BIT_VALID : u64.t := BIT 0.
Definition PTE_BIT_TABLE : u64.t := BIT 1.
Definition PTE_BITS_TABLE_POINTER : u64.t := GENMASK 47 12.
Definition PTE_BIT_OA_MSB : u64.t := 47.

Definition KiB_SHIFT : u64.t := 10.
Definition MiB_SHIFT : u64.t := 20.
Definition GiB_SHIFT : u64.t := 30.

Definition KiB (n : u64.t) : u64.t := n << KiB_SHIFT.
Definition MiB (n : u64.t) : u64.t := n << MiB_SHIFT.
Definition GiB (n : u64.t) : u64.t := n << GiB_SHIFT.

Definition MAP_SIZES : list u64.t := [
  GiB 512;
  GiB 1;
  MiB 2;
  KiB 4
].
Definition map_size (n : nat) : u64.t :=
  nth n MAP_SIZES zeros.

Definition PTE_FIELD_LVL1_OA_MASK := GENMASK 47 30.
Definition PTE_FIELD_LVL2_OA_MASK := GENMASK 47 21.
Definition PTE_FIELD_LVL3_OA_MASK := GENMASK 47 12.

Definition PTE_FIELD_OA_MASK : list u64.t := [
  u64.zeros;
  PTE_FIELD_LVL1_OA_MASK;
	PTE_FIELD_LVL2_OA_MASK;
	PTE_FIELD_LVL3_OA_MASK
].
Definition pte_field_oa_mask (n : nat) : u64.t :=
  nth n PTE_FIELD_OA_MASK u64.zeros.

Definition read_start_level (tcr : u64.t) : u64.t :=
  let t0sz := (and tcr TCR_EL2_T0SZ_MASK) << TCR_EL2_T0SZ_LO in
  let ia_bits := u64.sub 64 t0sz in
  div (48 - ia_bits) 9.

Definition discover_start_level
  (stage : EntryStage.t) : ghost_model_result :=
  tcr <- (match stage with
          | ENTRY_STAGE2 => read_sysreg SYSREG_VTCR_EL2
          | _ => read_sysreg SYSREG_TCR_EL2
          end);
  let start_level := read_start_level tcr in
  Level.of_u64 start_level.

Definition discover_page_size
  (stage : EntryStage.t) : ghost_model_result :=
  tcr <- (match stage with
          | ENTRY_STAGE2 => read_sysreg SYSREG_VTCR_EL2
          | _ => read_sysreg SYSREG_TCR_EL2
          end);
  let tg0 := (and tcr TCR_TG0_MASK) >> TCR_TG0_LO in
  if (tg0 u=? 0) then ok (4 u* 1024)
  else if (tg0 u=? 1) then ok (64 u* 1024)
  else if (tg0 u=? 2) then ok (16 u* 1024)
  else err (assertion_fail unreachable).

Definition discover_nr_concatenated_pgtables
  (stage : EntryStage.t) : ghost_model_result :=
  match stage with
  | ENTRY_STAGE1 => ok 1
  | ENTRY_STAGE2 =>
      size <- discover_page_size ENTRY_STAGE2;
      (size u=? PAGE_SIZE) else_ret err (assertion_fail assumes_4k_granule);
      res <- read_sysreg SYSREG_VTCR_EL2;
      let t0sz := and res (u64.decr (BIT 7)) in
      if 16 u<=? t0sz then ok 1
      else if t0sz u=? 15 then ok 2
      else if t0sz u=? 14 then ok 4
      else if t0sz u=? 13 then ok 8
      else if t0sz u=? 12 then ok 16
      else err (assertion_fail unreachable)
  | _ => err (assertion_fail assumes_stage2_translation_starting_at_level_0)
  end.

Definition is_desc_valid (descriptor : u64.t) : bool :=
  (and descriptor PTE_BIT_VALID) u=? PTE_BIT_VALID.

Definition is_desc_table (descriptor : u64.t) (level : Level.t) (stage : EntryStage.t) : bool :=
  match level with
  | LEVEL3 => false
  | _ => (and descriptor PTE_BIT_TABLE) u=? PTE_BIT_TABLE
  end.

Definition extract_output_address (desc : u64.t) (level : Level.t) : u64.t :=
  and desc (pte_field_oa_mask level).

Definition extract_table_address (desc : u64.t) : u64.t :=
  and desc PTE_BITS_TABLE_POINTER.

Fixpoint perms_from_aal_attrs
  (attrs : list u64.t)
  (level : nat)
  (perms : EntryPermissions.t) : ghost_model_result :=
  match level with
  | 0 => ok perms
  | S n =>
      match attrs with
      | [] => err (bug index_out_of_bounds)
      | attr :: rest =>
          if negb (is_null attr) then ok ENTRY_PERM_UNKNOWN
          else perms_from_aal_attrs rest n perms
      end
  end.

Definition parse_perms
  (stage : EntryStage.t)
  (mair : GhostMair.t)
  (desc : u64.t)
  (lvl : Level.t)
  (next_level_aal : aal) : ghost_model_result :=
    perms <-
      match stage with
      | ENTRY_STAGE1 =>
          let ro := __s1_is_ro desc in
          let xn := __s1_is_xn desc in
          let r_perm := ENTRY_PERM_R in
          let w_perm := if ro then ENTRY_PERM_EMPTY else ENTRY_PERM_W in
          let x_perm := if xn then ENTRY_PERM_EMPTY else ENTRY_PERM_X in
          ok (perm_or (perm_or r_perm w_perm) x_perm)
      | ENTRY_STAGE2 =>
          let r := __s2_is_r desc in
          let w := __s2_is_w desc in
          let xn := __s2_is_xn desc in
          let r_perm := if r then ENTRY_PERM_R else ENTRY_PERM_EMPTY in
          let w_perm := if w then ENTRY_PERM_W else ENTRY_PERM_EMPTY in
          let x_perm := if xn then ENTRY_PERM_EMPTY else ENTRY_PERM_X in
          if __s2_is_x desc then
            ok ENTRY_PERM_UNKNOWN
          else
            ok (perm_or (perm_or r_perm w_perm) x_perm)
      | _ => err (bug parses_attrs_for_a_non_pagetable_pte)
      end;
    perms_from_aal_attrs next_level_aal.(attr_at_level) lvl perms.

Definition parse_memtype
  (stage : EntryStage.t)
  (mair : GhostMair.t)
  (desc : u64.t)
  (lvl : Level.t)
  (next_level_aal : aal) : @ghost_model_result EntryMemTypeAttr.t :=
    match stage with
    | ENTRY_STAGE1 =>
      mair.(present) else_ret err (assertion_fail mair_must_be_present);
      let attr_idx := PTE_EXTRACT PTE_FIELD_S1_ATTRINDX_MASK PTE_FIELD_S1_ATTRINDX_LO desc in
      let attr := mair_attr mair (u64.to_nat attr_idx) in
      if (attr u=? MEMATTR_FIELD_DEVICE_nGnRE) then ok ENTRY_MEMTYPE_DEVICE
      else if (attr u=? MEMATTR_FIELD_NORMAL_OUTER_INNER_WRITE_BACK_CACHEABLE) then
        ok ENTRY_MEMTYPE_NORMAL_CACHEABLE
      else
        ok ENTRY_MEMTYPE_UNKNOWN
    | ENTRY_STAGE2 =>
      let attr := PTE_EXTRACT PTE_FIELD_S2_MEMATTR_MASK PTE_FIELD_S2_MEMATTR_LO desc in
      if (attr u=? MEMATTR_FIELD_DEVICE_nGnRE)
        then ok ENTRY_MEMTYPE_DEVICE
      else if (attr u=? MEMATTR_FIELD_NORMAL_OUTER_INNER_WRITE_BACK_CACHEABLE) then
        ok ENTRY_MEMTYPE_NORMAL_CACHEABLE
      else
        ok ENTRY_MEMTYPE_UNKNOWN
    | _ => err (assertion_fail unreachable)
  end.

Definition parse_attrs
  (stage : EntryStage.t)
  (mair : GhostMair.t)
  (desc : u64.t)
  (lvl : Level.t)
  (next_level_aal : aal) : @ghost_model_result EntryAttr.t :=
  perms <- parse_perms stage mair desc lvl next_level_aal;
  memtype <- parse_memtype stage mair desc lvl next_level_aal;
  let raw_arch_attrs := and desc PTE_FIELD_ATTRS_MASK in
  ok (mk_EA perms memtype raw_arch_attrs).

Definition deconstruct_pte
  (partial_ia desc : u64.t)
  (lvl : Level.t)
  (stage : EntryStage.t) : @ghost_model_result EED.t :=
  let ia_region := {| range_start := partial_ia; range_size := map_size lvl |} in
    if negb (is_desc_valid desc) then
      ok {| ia_region := ia_region;
            level := lvl;
            stage := stage;
            pte := PTE.invalid |}
    else if is_desc_table desc lvl stage then
      ok {| ia_region := ia_region;
            level := lvl;
            stage := stage;
            pte := PTE.table (extract_table_address desc) |}
    else
      sysreg <- read_sysreg SYSREG_MAIR_EL2;
      let mair := match stage with
                  | ENTRY_STAGE1 => read_mair sysreg
                  | _ => no_mair
                  end in
      attr <- parse_attrs stage mair desc lvl DUMMY_AAL;
      let addr_range := {| range_start := extract_output_address desc lvl;
                            range_size := map_size lvl |} in
      ok {| ia_region := ia_region;
            level := lvl;
            stage := stage;
            pte := PTE.map addr_range attr |}.

(** Pagee Traversal *)
Definition PgtTraverseCB : Type :=
  Machine.t -> PgtTraverseCtxt.t ->
  @ghost_model_result (Machine.t * PgtTraverseCtxt.t).

Fixpoint traverse_pgtable_from_inner_slot
  (fuel : nat)  (* Fuel parameter *)
  (cm : Machine.t)
  (root pte_phys pte_ia : u64.t)
  (lvl : Level.t)
  (stage : EntryStage.t)
  (visitor_cb : PgtTraverseCB)
  (flag : PgtTraversalFlag.t)
  (data : CallbackData.t) : @ghost_model_result (Machine.t * CallbackData.t * bool):=
  match fuel with
  | 0 => err (bug out_of_fuels_during_pgtable_traversal)
  | S fuel' =>
    res <- location cm (PAddr.intro pte_phys);
    let (cm', loc) := res in

    let early_return :=
      let flag_check := PgtTraversalFlag.eqb flag NO_READ_UNLOCKED_LOCATIONS in
      match flag_check, (Location.thread_owner loc) with
      | true, Some id => negb (TId.eqb id (cpu_id cm))
      | _, _ => false
      end in

    (negb early_return) else_ret ok (cm', data, true);
    res <- read_phys cm' pte_phys;
    let (cm'', desc) := res in
    exploded_descriptor <- deconstruct_pte pte_ia desc lvl stage;
    let ctxt :=
      {| PgtTraverseCtxt.root := root;
         PgtTraverseCtxt.stage := stage;
         PgtTraverseCtxt.data := data;
         PgtTraverseCtxt.level := lvl;
         PgtTraverseCtxt.loc_phys := (PAddr.intro pte_phys);
         PgtTraverseCtxt.descriptor := desc;
         PgtTraverseCtxt.exploded_descriptor := exploded_descriptor;
         PgtTraverseCtxt.leaf := EED.is_leaf exploded_descriptor; |} in

    res <- visitor_cb cm'' ctxt;
    let (cm''', ctxt') := res in
    match EED.pte (PgtTraverseCtxt.exploded_descriptor ctxt') with
    | PTE.table next_level_table_addr =>
        next_lvl <- next_level lvl;
        res <- traverse_pgtable_from_inner
                fuel'
                cm
                root next_level_table_addr pte_ia
                next_lvl
                stage
                visitor_cb
                flag
                data;
        let (cm'''', data') := res in
        ok (cm'''', data', false)
    | PTE.map _ _
    | PTE.invalid => ok (cm''', data, false)
    end
  end
with traverse_pgtable_from_inner
  (fuel : nat)
  (cm : Machine.t)
  (root table_start partial_ia : u64.t)
  (lvl : Level.t)
  (stage : EntryStage.t)
  (visitor_cb : PgtTraverseCB)
  (flag : PgtTraversalFlag.t)
  (data : CallbackData.t) : @ghost_model_result (Machine.t * CallbackData.t) :=
  match fuel with
  | O => err (bug out_of_fuels_during_pgtable_traversal)
  | S fuel' =>
    (IS_PAGE_ALIGNED table_start) else_ret err (assertion_fail not_page_aligned);
    res <-
      fold_left (fun acc i =>
        match acc with
        | ok (cm, data, false) =>
            let idx := u64.of_nat i in
            let pte_phys := table_start u+ (idx u* sizeof_u64) in
            let pte_ia := partial_ia u+ (idx u* (map_size lvl)) in
            traverse_pgtable_from_inner_slot
              fuel'
              cm
              root pte_phys pte_ia
              lvl
              stage
              visitor_cb
              flag
              data
        | _ => acc
        end) (seq 0 SLOTS_PER_PAGE) (ok (cm, data, false));
    let (cm', data') := (fst res) in
    ok (cm', data')
  end.

Definition traverse_pgtable_from
  (cm : Machine.t)
  (root table_start partial_ia : u64.t)
  (lvl : Level.t)
  (stage : EntryStage.t)
  (visitor_cb : PgtTraverseCB)
  (flag : PgtTraversalFlag.t)
  (data : CallbackData.t) : @ghost_model_result (Machine.t * CallbackData.t) :=
  let fuel := (SLOTS_PER_PAGE * SLOTS_PER_PAGE * SLOTS_PER_PAGE * SLOTS_PER_PAGE) in
  traverse_pgtable_from_inner
    fuel
    cm
    root table_start partial_ia
    lvl
    stage
    visitor_cb
    flag
    data.

Definition traverse_pgtable
  (cm : Machine.t)
  (root : u64.t)
  (stage : EntryStage.t)
  (visitor_cb : PgtTraverseCB)
  (flag : PgtTraversalFlag.t)
  (data : CallbackData.t) : @ghost_model_result (Machine.t * CallbackData.t) :=
  start_level <- discover_start_level stage;
  if negb (Level.eqb start_level LEVEL0) then
    err (assertion_fail pgtable_traverse_from_nonzero_level)
  else
    page_size <- discover_page_size stage;
    if negb (page_size u=? PAGE_SIZE) then
      err (assertion_fail assumes_4k_granule)
  else
    nr_concatenated_pgtables <- discover_nr_concatenated_pgtables stage;
    if negb (nr_concatenated_pgtables u=? 1) then
      err (assertion_fail found_multiple_contenated_pgtables)
  else
    traverse_pgtable_from
      cm root root 0 start_level stage visitor_cb flag data
.

Definition get_unclean_locations_in_machine (m : Machine.t) : LocationSet.t :=
  m.(Machine.state).(ModelState.unclean_locations).

Definition update_unclean_locations_in_memory
(m : Machine.t) (loc_set : LocationSet.t) : Machine.t :=
  m <| Machine.state; ModelState.unclean_locations := loc_set |>.

Definition delete_unclean_location_in_machine
  (m : Machine.t) (k : PAddr.t) : Machine.t :=
  let cur_locations := get_unclean_locations_in_machine m in
  update_unclean_locations_in_memory m (LocationSet.remove k cur_locations).

Definition add_location_to_unclean_PTE
  (cm : Machine.t)
  (loc_phys : PAddr.t) : ghost_model_result :=
  let locations := get_unclean_locations_in_machine cm in
  if LocationSet.lookup loc_phys locations then
    err (assertion_fail location_already_in_unclean_ptes)
  else if (MAX_UNCLEAN_LOCATIONS <? LocationSet.len locations) then
    err (assertion_fail exceeds_max_unclean_locations)
  else
    ok (update_unclean_locations_in_memory cm (LocationSet.append loc_phys locations)).

Definition construct_context_from_pte
  (cm : Machine.t)
  (phys : PAddr.t)
  (data : CallbackData.t) : @ghost_model_result (Machine.t * PgtTraverseCtxt.t) :=
  res <- read_phys cm phys;
  let (cm', desc) := res in

  loc <- get_location_without_ensure cm phys;
  loc_info <- (Location.info loc) ?? err (assertion_fail location_not_initialised);
  pte_info <- (LocationInfo.pte_info loc_info) ?? err (assertion_fail location_not_pte);

  let descriptor := (PTEInfo.descriptor pte_info) in
  let ctxt := {| PgtTraverseCtxt.loc_phys := loc.(Location.phys_addr);
                 PgtTraverseCtxt.descriptor := desc;
                 PgtTraverseCtxt.level := descriptor.(EED.level);
                 PgtTraverseCtxt.leaf := EED.is_leaf descriptor;
                 PgtTraverseCtxt.exploded_descriptor := descriptor;
                 PgtTraverseCtxt.root := loc_info.(LocationInfo.owner);
                 PgtTraverseCtxt.stage := descriptor.(EED.stage);
                 PgtTraverseCtxt.data := data |} in
  ok (cm', ctxt).

Definition traverse_all_unclean_PTE
  (cm : Machine.t)
  (visitor_cb : PgtTraverseCB)
  (data : CallbackData.t)
  (stage : EntryStage.t) : @ghost_model_result Machine.t :=
  let locations := LocationSet.locations (get_unclean_locations_in_machine cm) in
  fold_left (fun acc phys =>
    cm <- acc;
    loc <- get_location_without_ensure cm phys;
    loc_info <- (Location.info loc) ?? err (assertion_fail location_not_initialised);
    pte_info <- (LocationInfo.pte_info loc_info) ?? err (assertion_fail location_not_pte);

    let descriptor := PTEInfo.descriptor pte_info in
    (PTEInfo.is_invalid_unclean pte_info) else_ret err (assertion_fail location_not_invalid_unclean_pte);

    if (negb (EntryStage.eqb stage ENTRY_STAGE_NONE))
      && (negb (EntryStage.eqb stage (EED.stage descriptor))) then
        ok cm
      else
        res <- construct_context_from_pte cm phys data;
        let (cm', ctxt) := res in
        res <- visitor_cb cm' ctxt;

        let (cm'', ctxt') := res in
        loc' <- get_location_without_ensure cm'' ctxt'.(PgtTraverseCtxt.loc_phys);
        loc_info' <- (Location.info loc) ?? err (assertion_fail location_not_initialised);
        pte_info' <- (LocationInfo.pte_info loc_info) ?? err (assertion_fail location_not_pte);

        if PTEInfo.is_invalid_unclean pte_info' then ok cm''
        else ok (delete_unclean_location_in_machine cm'' phys)
  ) locations (ok cm).

Definition finder_cb : PgtTraverseCB :=
  fun cm ctxt =>
    match (PgtTraverseCtxt.data ctxt) with
    | finder_cb_data data =>
        ((PgtTraverseCtxt.loc_phys ctxt) u=? (PgtWalkResult.requested_pte data)) else_ret ok (cm, ctxt);
        let new_data :=
           data <| PgtWalkResult.found := true |>
                <| PgtWalkResult.root := ctxt.(PgtTraverseCtxt.root) |>
                <| PgtWalkResult.descriptor := Some ctxt.(PgtTraverseCtxt.exploded_descriptor) |>
                <| PgtWalkResult.stage := ctxt.(PgtTraverseCtxt.stage) |>
                <| PgtWalkResult.level := ctxt.(PgtTraverseCtxt.level) |> in
        ok (cm, ctxt <| PgtTraverseCtxt.data := finder_cb_data new_data |>)
    | _ => err (bug invalid_callback_data)
    end.

Definition find_pte
  (cm : Machine.t)
  (loc : Location.t) : @ghost_model_result (Machine.t * PgtWalkResult.t) :=
  let result := PgtWalkResult.initialise
                  <| PgtWalkResult.found := false |>
                  <| PgtWalkResult.requested_pte := Location.phys_addr loc |> in
  loc_info <- (Location.info loc) ?? err (assertion_fail location_not_initialised);
  pte_info <- (LocationInfo.pte_info loc_info) ?? err (assertion_fail location_not_pte);
  let descriptor := (PTEInfo.descriptor pte_info) in
  res <- traverse_pgtable
          cm
          (LocationInfo.owner loc_info)
          (EED.stage descriptor)
          finder_cb
          NO_READ_UNLOCKED_LOCATIONS
          (finder_cb_data result);
  let (cm', data) := res in
  match data with
  | finder_cb_data data => ok (cm', data)
  | _ => err (bug invalid_callback_data)
  end.

Definition initial_state
  (cm : Machine.t)
  (partial_ia desc : u64.t)
  (lvl : Level.t)
  (stage : EntryStage.t) : @ghost_model_result PTEState.t :=
  deconstructed <- deconstruct_pte partial_ia desc lvl stage;
  match (EED.pte deconstructed) with
  | PTE.invalid =>
      ok (PTEState.invalid {| ICState.invalidator_tid := cpu_id cm |})
  | PTE.map _ _
  | PTE.table _ => ok (PTEState.valid VState.initialise)
  end.

