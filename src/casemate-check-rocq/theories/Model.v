From stdpp Require Import gmap.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Require Export ModelHeader.

Require Import Transitions.
Require Import Blobs.
Require Import Machine.
Require Import Pgtable.

(** Locks - Lock Ownership *)
Definition get_lock_owner_map (cm : Machine.t) : LockOwnerMap.t :=
  cm.(Machine.state).(ModelState.locks).

Definition update_lock_owner_map (cm : Machine.t) (m : Map.t LockAddr.t) : Machine.t :=
  cm <| Machine.state; ModelState.locks; LockOwnerMap.locks := m |>.

Definition owner_lock
  (cm : Machine.t)
  (owner_id : u64.t) : option LockAddr.t :=
  let lmap := get_lock_owner_map cm in (LockOwnerMap.locks lmap) !! owner_id.

Definition insert_lock
  (cm : Machine.t)
  (root : u64.t)
  (lock : LockAddr.t) : Machine.t :=
  let lmap := get_lock_owner_map cm in
  update_lock_owner_map cm (insert root lock (LockOwnerMap.locks lmap)).

Definition delete_lock
  (cm : Machine.t) (root : u64.t) : Machine.t :=
  let lmap := get_lock_owner_map cm in
  update_lock_owner_map cm (delete root (LockOwnerMap.locks lmap)).

Definition swap_lock
  (cm : Machine.t)
  (root : OwnerAddr.t)
  (lock : LockAddr.t) : @ghost_model_result Machine.t :=
  match (owner_lock cm root) with
  | Some _ => ok (insert_lock cm root lock)
  | None => err (catch_fire change_lock_on_unlocked_location)
  end.

Definition append_lock
  (cm : Machine.t)
  (root : OwnerAddr.t)
  (lock : LockAddr.t) : @ghost_model_result Machine.t :=
  match (owner_lock cm root) with
  | Some _ => err (catch_fire append_lock_on_locked_location)
  | None =>
      let lmap := get_lock_owner_map cm in
      if (Nat.eqb (LockOwnerMap.len lmap) casemate_model_MAX_LOCKS) then
        err (bug exceeds_num_of_max_locks)
      else
        ok (insert_lock cm root lock)
  end.

Definition associate_lock
  (cm : Machine.t)
  (root : OwnerAddr.t)
  (lock : LockAddr.t) : @ghost_model_result Machine.t :=
  match owner_lock cm root with
  | Some _ => swap_lock cm root lock
  | None => append_lock cm root lock
  end.

Definition unregister_lock
  (cm : Machine.t)
  (root : OwnerAddr.t) : @ghost_model_result Machine.t :=
  match owner_lock cm root with
  | Some _ => ok (delete_lock cm root)
  | None => err (catch_fire release_table_without_lock)
  end.

(** Locks - Lock State *)
Definition get_lock_state_map (cm : Machine.t) : LockStateMap.t :=
  cm.(Machine.state).(ModelState.state).

Definition lock_state_by_addr
  (cm : Machine.t)
  (lock : u64.t) : option LockState.t :=
  let lsmap := get_lock_state_map cm in
  (LockStateMap.locker lsmap) !! lock.

Definition update_lock_state_by_addr
  (cm : Machine.t)
  (lock : u64.t)
  (lock_state : LockState.t) : Machine.t :=
  let lsmap := get_lock_state_map cm in
  cm <| Machine.state;
        ModelState.state;
        LockStateMap.locker := insert lock lock_state (LockStateMap.locker lsmap) |>.

Definition update_lock_state_map
  (cm : Machine.t)
  (lsmap : LockStateMap.t) : Machine.t :=
  cm <| Machine.state;
        ModelState.state := lsmap |>.

Definition is_correctly_locked
  (cm : Machine.t)
  (lock : LockAddr.t) : option LockState.t :=
  (get_check_synchronisation cm) else_ret None;
  match (lock_state_by_addr cm lock) with
  | Some state =>
      if TId.eqb (cpu_id cm) (LockState.id state) then Some state
      else None
  | None => None
  end.

Definition is_location_locked
  (cm : Machine.t)
  (loc_phys : PAddr.t) : @ghost_model_result bool :=
  (get_check_synchronisation cm) else_ret (ok true);
  loc <- get_location_without_ensure cm loc_phys;
  loc_info <- (Location.info loc) ?? ok true;
  pte_info <- (LocationInfo.pte_info loc_info) ?? ok true;
  match (Location.thread_owner loc) with
  | Some thread_owner => ok (TId.eqb (cpu_id cm) thread_owner)
  | None =>
      let owner_id := (LocationInfo.owner loc_info) in
      if (is_null owner_id) then
        err (catch_fire missing_location_owner)
      else
        lock <- (owner_lock cm owner_id) ?? (ok false);
        match (is_correctly_locked cm lock) with
        | Some _ => ok true
        | None => ok false
        end
  end.

Definition assert_owner_locked
  (cm : Machine.t)
  (loc_phys : PAddr.t) : @ghost_model_result (option (LockAddr.t * LockState.t)) :=
  loc <- get_location_without_ensure cm loc_phys;
  loc_info <- (Location.info loc) ?? err (assertion_fail location_not_initialised);
  pte_info <- (LocationInfo.pte_info loc_info) ?? err (assertion_fail location_not_pte);

  get_check_synchronisation cm else_ret (ok None);
  let owner_id := (LocationInfo.owner loc_info) in
  if is_null owner_id then
    err (catch_fire missing_location_owner)
  else
    lock <- (owner_lock cm owner_id) ?? err (catch_fire missing_owner_root);
    match (is_correctly_locked cm lock) with
    | Some state => ok (Some (lock, state))
    | None => err (catch_fire write_to_pte_without_owner_lock)
    end.

(** TLB maintenance *)
Definition decode_tlbi_method_kind (k : TLBIKind.t) : tlbi_op_method_kind :=
  match k with
  | TLBI_vmalls12e1
  | TLBI_vmalls12e1is
  | TLBI_vmalle1is
  | TLBI_vmalle1 =>
      TLBI_OP_BY_ADDR_SPACE
  | TLBI_vale2is
  | TLBI_vae2is
  | TLBI_ipas2e1is =>
      TLBI_OP_BY_INPUT_ADDR
  | TLBI_alle1is =>
      TLBI_OP_BY_ALL
  end.

Definition decode_tlbi_shootdown_kind (k : TLBIKind.t) : bool :=
  match k with
  | TLBI_vmalls12e1is
  | TLBI_vmalle1is
  | TLBI_vale2is
  | TLBI_vae2is
  | TLBI_ipas2e1is
  | TLBI_alle1is =>
      true
  | TLBI_vmalls12e1
  | TLBI_vmalle1 =>
      false
  end.

Definition decode_tlbi_stage_kind (k : TLBIKind.t) : tlbi_op_stage :=
  match k with
  | TLBI_vale2is
  | TLBI_vae2is
  | TLBI_vmalle1is
  | TLBI_vmalle1 =>
      TLBI_OP_STAGE1
  | TLBI_ipas2e1is =>
      TLBI_OP_STAGE2
  | TLBI_vmalls12e1
  | TLBI_vmalls12e1is
  | TLBI_alle1is =>
      TLBI_OP_BOTH_STAGES
  end.

Definition decode_tlbi_regime_kind (k : TLBIKind.t) : tlbi_op_regime_kind :=
  match k with
  | TLBI_vale2is
  | TLBI_vae2is =>
      TLBI_REGIME_EL2
  | TLBI_vmalle1is
  | TLBI_vmalle1
  | TLBI_ipas2e1is
  | TLBI_vmalls12e1
  | TLBI_vmalls12e1is
  | TLBI_alle1is =>
      TLBI_REGIME_EL10
  end.

Definition decode_tlbi_by_addr (data : TransTlbiData.t) : tlbi_op_method_data :=
  let page := (TransTlbiData.page data) in
  let affects_last_level_only := (TLBIKind.eqb (TransTlbiData.tlbi_kind data) TLBI_vale2is) in
  let has_level_hint := u64.ltb (TransTlbiData.level data) (u64.of_nat 4) in
  let level_hint :=
    if has_level_hint then (u64.and (Level.to_u64 (TransTlbiData.level data)) (u64.of_nat 3))
    else u64.zeros in
  tlbi_op_method_by_address_data
    page
    has_level_hint
    level_hint
    affects_last_level_only.

Definition decode_tlbi_by_space_id (data : TransTlbiData.t) : tlbi_op_method_data :=
  tlbi_op_method_by_address_space_id_data u64.zeros.

Definition decode_tlbi (data : TransTlbiData.t) : @ghost_model_result TLBIOp.t :=
  let stage := decode_tlbi_stage_kind (TransTlbiData.tlbi_kind data) in
  let regime := decode_tlbi_regime_kind (TransTlbiData.tlbi_kind data) in
  let shootdown := decode_tlbi_shootdown_kind (TransTlbiData.tlbi_kind data) in
  let method_kind := decode_tlbi_method_kind (TransTlbiData.tlbi_kind data) in
  tlbi_op_method_data <-
    (match method_kind with
      | TLBI_OP_BY_INPUT_ADDR => ok (decode_tlbi_by_addr data)
      | TLBI_OP_BY_ADDR_SPACE => ok (decode_tlbi_by_space_id data)
      | TLBI_OP_BY_ALL => err (assertion_fail unimplemented)
      end);
  let tlbi_op_method := mk_TOM method_kind tlbi_op_method_data in
  ok (mk_TO stage regime tlbi_op_method shootdown).

(** BBM requirements *)
Definition is_only_update_to_sw_bits (before after : u64.t) : bool :=
  u64.eqb (u64.and before (u64.not PTE_FIELD_UPPER_ATTRS_SW_MASK))
          (u64.and after (u64.not PTE_FIELD_UPPER_ATTRS_SW_MASK)).

Definition requires_bbm
  (cm : Machine.t)
  (loc_phys : PAddr.t)
  (before after : u64.t) : @ghost_model_result bool :=
  loc <- get_location_without_ensure cm loc_phys;
  loc_info <- (Location.info loc) ?? err (assertion_fail location_not_initialised);
  pte_info <- (LocationInfo.pte_info loc_info) ??  err (assertion_fail location_not_pte);

  let descriptor := (PTEInfo.descriptor pte_info) in
  before_descriptor <-
    deconstruct_pte (EED.ia_region descriptor).(range_start) before (EED.level descriptor) (EED.stage descriptor);
  after_descriptor <-
    deconstruct_pte (EED.ia_region descriptor).(range_start) after (EED.level descriptor) (EED.stage descriptor);

  if (EED.is_invalid before_descriptor)
      || (EED.is_invalid after_descriptor) then ok false
  else
    if (EED.is_table before_descriptor)
        || (EED.is_table after_descriptor) then ok true
  else
    match (EED.pte before_descriptor), (EED.pte after_descriptor) with
    | PTE.map range1 _, PTE.map range2 _ =>
        if range1.(range_size) u=? range2.(range_size) then
          ok (negb (is_only_update_to_sw_bits before after))
        else ok true
    | _, _ => err (assertion_fail unreachable)
    end.

(** Reachability *)
Definition clean_reachability_checker_cb : PgtTraverseCB :=
  fun cm ctxt =>
    let loc_phys := (PgtTraverseCtxt.loc_phys ctxt) in
    loc <- get_location_without_ensure cm loc_phys;
    loc_info <- (Location.info loc) ?? ok (cm, ctxt);
    pte_info <- (LocationInfo.pte_info loc_info) ?? ok (cm, ctxt);
    if (PTEInfo.is_invalid_unclean pte_info) then
      ok (cm, ctxt <| PgtTraverseCtxt.data := clean_reach_cb_data false |>)
    else ok (cm, ctxt).

Definition pre_all_reachable_clean
  (cm : Machine.t)
  (loc_phys : PAddr.t) : @ghost_model_result (Machine.t * bool) :=
  loc <- get_location_without_ensure cm loc_phys;
  loc_info <- (Location.info loc) ?? ok (cm, true);
  pte_info <- (LocationInfo.pte_info loc_info) ?? ok (cm, true);

  res <- find_pte cm loc;
  let (cm', walk_result) := res in
  (PgtWalkResult.found walk_result) else_ret err (assertion_fail location_pte_not_in_pgtable);

  let descriptor := (PTEInfo.descriptor pte_info) in
  match (EED.pte descriptor) with
  | PTE.table next_level_table_addr =>
      next_lvl <- next_level (EED.level descriptor);
      res <- traverse_pgtable_from
                cm
                (LocationInfo.owner loc_info)
                next_level_table_addr
                (EED.ia_region descriptor).(range_start)
                next_lvl
                (EED.stage descriptor)
                clean_reachability_checker_cb
                READ_UNLOCKED_LOCATIONS
                (clean_reach_cb_data true);
      let (cm'', data) := res in
      match data with
      | clean_reach_cb_data all_clean => ok (cm'', all_clean)
      | _ => err (bug invalid_callback_data)
      end
  | _ => ok (cm, true)
  end.

Definition initialise_location
  (cm : Machine.t)
  (loc_phys : PAddr.t)
  (val : u64.t) : @ghost_model_result Machine.t :=
  loc <- get_location_without_ensure cm loc_phys;
  match (Location.info loc) with
  | Some loc_info => err (catch_fire initialize_already_initialized_location)
  | None =>
      step <- Machine.step cm ?? err (bug transition_not_initialised);
      if ModelStep.is_on_write_transition step loc_phys then
        err (assertion_fail address_on_write_transition)
      else
        let loc_info := mk_LI val None (OwnerAddr.intro u64.zeros) in
        let loc' := loc <| Location.info := Some loc_info |>
                        <| Location.thread_owner := None |> in
        update_location cm loc'
  end.

Definition mark_cb : PgtTraverseCB :=
  fun cm ctxt =>
    let loc_phys := (PgtTraverseCtxt.loc_phys ctxt) in
    cm' <-
      loc <- get_location_without_ensure cm loc_phys;
      match (Location.info loc) with
      | None => initialise_location cm loc_phys (PgtTraverseCtxt.descriptor ctxt)
      | Some {| LocationInfo.pte_info := Some _; |} => err (catch_fire double_use_pte)
      | Some _ => ok cm
      end;

    loc <- get_location_without_ensure cm loc_phys;
    loc_info <- (Location.info loc) ?? err (assertion_fail location_not_initialised);

    new_pte_info <-
      let descriptor := (PgtTraverseCtxt.exploded_descriptor ctxt) in
      let partial_ia := (EED.ia_region descriptor).(range_start) in
      let desc := (PgtTraverseCtxt.descriptor ctxt) in
      let level := (PgtTraverseCtxt.level ctxt) in
      let stage := (PgtTraverseCtxt.stage ctxt) in
      state <- initial_state cm partial_ia desc level stage;
      ok {| PTEInfo.descriptor := descriptor; PTEInfo.state := state |};

    let root := (PgtTraverseCtxt.root ctxt) in
    let loc_info' := loc_info <| LocationInfo.owner := OwnerAddr.intro root |>
                              <| LocationInfo.pte_info := Some new_pte_info |> in
    let loc' := loc <| Location.info := Some loc_info' |> in
    cm'' <- update_location cm' loc';
    ok (cm'', ctxt).

Definition unmark_cb : PgtTraverseCB :=
  fun cm ctxt =>
    let loc_phys := (PgtTraverseCtxt.loc_phys ctxt) in
    cm' <-
      loc <- get_location_without_ensure cm loc_phys;
      match (Location.info loc) with
      | None => initialise_location cm loc_phys (PgtTraverseCtxt.descriptor ctxt)
      | Some {| LocationInfo.pte_info := None; |} => err (catch_fire unmark_non_pte)
      | Some _ => ok cm
      end;

    loc <- get_location_without_ensure cm loc_phys;
    loc_info <- (Location.info loc) ?? err (assertion_fail location_not_initialised);
    let loc_info' := loc_info <| LocationInfo.pte_info := None |> in
    let loc' := loc <| Location.info := Some loc_info' |> in
    cm'' <- update_location cm' loc';
    ok (cm'', ctxt).

Definition mark_not_writable_cb : PgtTraverseCB :=
  fun cm ctxt =>
    let loc_phys := (PgtTraverseCtxt.loc_phys ctxt) in
    loc <- get_location_without_ensure cm loc_phys;
    match (Location.thread_owner loc) with
    | Some _ =>
        err (catch_fire invalidated_owned_entry_parent)
    | None =>
        loc_info <- (Location.info loc) ?? err (assertion_fail location_not_initialised);
        pte_info <- (LocationInfo.pte_info loc_info) ?? err (assertion_fail location_not_pte);
        let pte_info' := pte_info <| PTEInfo.state := PTEState.not_writable |> in
        let loc_info' := loc_info <| LocationInfo.pte_info := Some pte_info' |> in
        let loc' := loc <| Location.info := Some loc_info' |> in
        cm' <- update_location cm loc';
        ok (cm', ctxt)
    end.

(** Pagetable roots *)
Definition root_exists_in (root_table : list PAddr.t) (root : PAddr.t) : bool :=
  existsb (A:=PAddr.t) (u64.eqb root) root_table.

Definition root_exists (cm : Machine.t) (root : PAddr.t) : bool :=
  root_exists_in cm.(Machine.state).(ModelState.s1_roots) root ||
  root_exists_in cm.(Machine.state).(ModelState.s2_roots) root.

Definition try_insert_root_inner
  (root_table : list PAddr.t)
  (root : PAddr.t) : ghost_model_result :=
  if MAX_ROOTS <=? (length root_table) then
    err (catch_fire exceed_max_root_limit)
  else
    ok (root_table ++ [root]).

Definition try_insert_root
  (cm : Machine.t)
  (stage : EntryStage.t)
  (root : PAddr.t) : @ghost_model_result Machine.t :=
    if EntryStage.eqb stage ENTRY_STAGE2 then
      root_table <- try_insert_root_inner cm.(Machine.state).(ModelState.s2_roots) root;
      ok (cm <| Machine.state; ModelState.s2_roots := root_table |>)
    else
      root_table <- try_insert_root_inner cm.(Machine.state).(ModelState.s1_roots) root;
      ok (cm <| Machine.state; ModelState.s1_roots := root_table |>).

Definition try_remove_root_inner
  (root_table : list PAddr.t)
  (root : PAddr.t) : ghost_model_result :=
  if root_exists_in root_table root then
    ok (filter (A:=PAddr.t) (fun r => negb (r u=? root)) root_table)
  else
    err (catch_fire root_does_not_exist).

Definition try_remove_root
  (cm : Machine.t)
  (stage : EntryStage.t)
  (root : PAddr.t) : ghost_model_result :=
    if EntryStage.eqb stage ENTRY_STAGE2 then
      root_table <- try_remove_root_inner cm.(Machine.state).(ModelState.s2_roots) root;
      ok (cm <| Machine.state; ModelState.s2_roots := root_table |>)
    else
      root_table <- try_remove_root_inner cm.(Machine.state).(ModelState.s1_roots) root;
      ok (cm <| Machine.state; ModelState.s1_roots := root_table |>).

Definition try_register_root
  (cm : Machine.t)
  (stage : EntryStage.t)
  (root : PAddr.t) : @ghost_model_result Machine.t :=
  if root_exists cm root then
    err (catch_fire root_already_exists)
  else
    cm' <- try_insert_root cm stage root;
    res <- traverse_pgtable
              cm'
              root
              stage
              mark_cb
              READ_UNLOCKED_LOCATIONS
              empty_cb_data;
    ok (fst res).

Definition try_unregister_root
  (cm : Machine.t)
  (stage : EntryStage.t)
  (root : PAddr.t) : ghost_model_result :=
  res <- traverse_pgtable
            cm
            root
            stage
            unmark_cb
            READ_UNLOCKED_LOCATIONS
            empty_cb_data;
  let cm' := fst res in
  try_remove_root cm' stage root.

(** Step write sysreg *)
Definition step_msr
  (cm : Machine.t)
  (msr_data : TransMsrData.t) : ghost_model_result :=
  match (TransMsrData.sysreg msr_data) with
  | SYSREG_TTBR_EL2 =>
      let root := extract_s1_root (TransMsrData.val msr_data) in
      if negb (root_exists_in cm.(Machine.state).(ModelState.s1_roots) root) then
        try_register_root cm ENTRY_STAGE1 root
      else
        ok cm
  | SYSREG_VTTBR =>
      let root := extract_s2_root (TransMsrData.val msr_data) in
      if negb (root_exists_in cm.(Machine.state).(ModelState.s2_roots) root) then
        try_register_root cm ENTRY_STAGE2 root
      else
        ok cm
  | _ => err (assertion_fail unreachable)
  end.

(** Step on memory write *)
Definition __update_descriptor_on_write
  (cm : Machine.t)
  (loc_phys : PAddr.t)
  (val : u64.t) : @ghost_model_result Machine.t :=
  loc <- get_location_without_ensure cm loc_phys;
  loc_info <- (Location.info loc) ?? err (assertion_fail location_not_initialised);
  pte_info <- (LocationInfo.pte_info loc_info) ??  err (assertion_fail location_not_pte);

  let descriptor := (PTEInfo.descriptor pte_info) in
  descriptor' <- deconstruct_pte
                    (EED.ia_region descriptor).(range_start)
                    val (EED.level descriptor)
                    (EED.stage descriptor);
  let pte_info' := pte_info <| PTEInfo.descriptor := descriptor' |> in
  let loc_info' := loc_info <| LocationInfo.pte_info := Some pte_info' |> in
  let loc' := loc <| Location.info := Some loc_info' |> in
  update_location cm loc'.

Definition step_write_table_mark_children
  (cm : Machine.t)
  (visitor_cb : PgtTraverseCB)
  (loc_phys : PAddr.t) : @ghost_model_result Machine.t :=
  loc <- get_location_without_ensure cm loc_phys;
  loc_info <- (Location.info loc) ?? err (assertion_fail location_not_initialised);
  pte_info <- (LocationInfo.pte_info loc_info) ??  err (assertion_fail location_not_pte);

  let descriptor := (PTEInfo.descriptor pte_info) in
  match (EED.pte descriptor) with
  | PTE.table next_level_table_addr =>
      res <- pre_all_reachable_clean cm loc_phys;
      let (cm', all_clean) := res in
      if negb all_clean then
        err (catch_fire bbm_write_table_descriptor_with_unclean_children)
      else
        next_level <- Level.next_level (EED.level descriptor);
        res <- traverse_pgtable_from
                cm
                (LocationInfo.owner loc_info)
                next_level_table_addr
                (EED.ia_region descriptor).(range_start)
                next_level
                (EED.stage descriptor)
                visitor_cb
                READ_UNLOCKED_LOCATIONS
                empty_cb_data;
        let (cm'', _) := res in
        ok cm''
    | _ => ok cm
    end.

Definition step_write_on_invalid
  (cm : Machine.t)
  (mo : memory_order_t)
  (loc_phys : PAddr.t)
  (val : u64.t) : @ghost_model_result Machine.t :=
  (is_desc_valid val) else_ret (ok cm);
  cm' <- __update_descriptor_on_write cm loc_phys val;
  cm'' <- step_write_table_mark_children cm' mark_cb loc_phys;

  loc <- get_location_without_ensure cm loc_phys;
  loc_info <- (Location.info loc) ?? err (assertion_fail location_not_initialised);
  pte_info <- (LocationInfo.pte_info loc_info) ??  err (assertion_fail location_not_pte);
  let pte_info' := pte_info <| PTEInfo.state := PTEState.valid VState.initialise |> in
  let loc_info' := loc_info <| LocationInfo.pte_info := Some pte_info' |> in
  let loc' := loc <| Location.info := Some loc_info' |> in
  ok cm''.

Definition step_write_on_invalid_unclean
  (cm : Machine.t)
  (mo : memory_order_t)
  (loc_phys : PAddr.t)
  (val : u64.t) : @ghost_model_result Machine.t :=
  (is_desc_valid val) else_ret (ok cm);
  err (catch_fire bbm_invalid_unclean_to_valid).

Definition step_write_on_valid
  (cm : Machine.t)
  (mo : memory_order_t)
  (loc_phys : PAddr.t)
  (val : u64.t) : @ghost_model_result Machine.t :=
  res <- read_phys_pre cm loc_phys;
  let (cm, old) := res in
  if is_desc_valid val then
    bbm_check <- requires_bbm cm loc_phys old val;
    if negb bbm_check then ok cm
    else err (catch_fire bbm_valid_to_valid)
  else
    loc <- get_location_without_ensure cm loc_phys;
    loc_info <- (Location.info loc) ?? err (assertion_fail location_not_initialised);
    pte_info <- (LocationInfo.pte_info loc_info) ??  err (assertion_fail location_not_pte);
    let pte_info := pte_info <| PTEInfo.state := PTEState.invalid_unclean (mk_IUS (cpu_id cm) old LIS.unguarded) |> in
    let loc_info := loc_info <| LocationInfo.pte_info := Some pte_info |> in
    let loc := loc <| Location.info := Some loc_info |> in
    cm' <- update_location cm loc;
    cm'' <- add_location_to_unclean_PTE cm' loc_phys;
    step_write_table_mark_children cm'' mark_not_writable_cb loc_phys.

Definition step_write_on_unwritable
  (cm : Machine.t)
  (mo : memory_order_t)
  (loc_phys : PAddr.t)
  (val : u64.t) : @ghost_model_result Machine.t :=
  loc <- get_location_without_ensure cm loc_phys;
  loc_info <- (Location.info loc) ?? err (assertion_fail location_not_initialised);

  let other_val := (LocationInfo.val loc_info) in
  negb (other_val u=? val) else_ret (ok cm);
  if negb (is_desc_valid val) && negb (is_desc_valid other_val)  then
    ok cm
  else
    err (catch_fire write_page_with_unclean_parent).

Definition check_write_is_authorized
  (cm : Machine.t)
  (loc_phys : PAddr.t)
  (mo : memory_order_t)
  (val : u64.t) : @ghost_model_result Machine.t :=
  get_check_synchronisation cm else_ret (ok cm);

  res <- assert_owner_locked cm loc_phys;
  res <- res ?? ok cm;
  let (lock, state) := res in
  match (LockState.write_authorization state) with
  | WriteAuth.AUTHORIZED =>
      let lock_state := state <| LockState.write_authorization := WriteAuth.UNAUTHORIZED_PLAIN |> in
      ok (update_lock_state_by_addr cm loc_phys lock_state)
  | WriteAuth.UNAUTHORIZED_PLAIN =>
      match mo with
      | WMO_plain =>
        loc <- get_location_without_ensure cm loc_phys;
        loc_info <- (Location.info loc) ?? err (assertion_fail location_not_initialised);
        pte_info <- (LocationInfo.pte_info loc_info) ?? err (assertion_fail location_not_pte);
        if (PTEInfo.is_valid pte_info) || is_desc_valid val then
          err (catch_fire write_plain_without_authorization)
        else
          ok cm
      | WMO_release => ok cm
      end
  end.

Definition step_write
  (cm : Machine.t)
  (write_data : TransWriteData.t) : @ghost_model_result Machine.t :=

  let mo := write_data.(TransWriteData.mo) in
  let loc_phys := write_data.(TransWriteData.phys_addr) in
  let val := write_data.(TransWriteData.val) in

  res <- location cm loc_phys;
  let (cm', loc) := res in
  loc_info <- (Location.info loc) ?? ok cm';
  pte_info <- (LocationInfo.pte_info loc_info) ?? ok cm';

  cm <- check_write_is_authorized cm loc_phys mo val;
  match (PTEInfo.state pte_info) with
  | PTEState.invalid_unclean _ => step_write_on_invalid_unclean cm mo loc_phys val
  | PTEState.valid _ => step_write_on_valid cm mo loc_phys val
  | PTEState.not_writable => step_write_on_unwritable cm mo loc_phys val
  | PTEState.invalid _ => step_write_on_invalid cm mo loc_phys val
  end.

(** Step on memory read *)
Definition step_read
  (cm : Machine.t)
  (read_data : TransReadData.t) : @ghost_model_result Machine.t :=
  let loc_phys := read_data.(TransReadData.phys_addr) in
  let val := read_data.(TransReadData.val) in
  res <- location cm read_data.(TransReadData.phys_addr);

  val_read <- read_phys cm loc_phys;
  let (cm, val) := val_read in
  if val u=? val then ok cm
  else err (assertion_fail read_inconsistent).

(** ISB *)
Definition step_isb (cm : Machine.t) : @ghost_model_result Machine.t := ok cm.

(** Step on a DSB *)
Definition step_dsb_invalid_unclean_unmark_children
  (cm : Machine.t)
  (loc_phys : PAddr.t) : @ghost_model_result Machine.t :=
  loc <- get_location_without_ensure cm loc_phys;
  loc_info <- (Location.info loc) ?? ok cm;
  pte_info <- (LocationInfo.pte_info loc_info) ?? ok cm;

  match (PTEInfo.state pte_info) with
  | PTEState.invalid_unclean iu_state =>
      let old := (IUState.old_valid_desc iu_state) in
      old_desc <- deconstruct_pte
                    (EED.ia_region (PTEInfo.descriptor pte_info)).(range_start)
                    old
                    (EED.level (PTEInfo.descriptor pte_info))
                    (EED.stage (PTEInfo.descriptor pte_info));

      match (EED.pte old_desc) with
      | PTE.table next_table_addr =>
          res <- pre_all_reachable_clean cm loc_phys;
          let (cm', all_clean) := res in
          all_clean else_ret
            err (catch_fire bbm_write_table_descriptor_with_unclean_children);

          next_level <- Level.next_level (EED.level (PTEInfo.descriptor pte_info));
          res <- traverse_pgtable_from
                  cm
                  (LocationInfo.owner loc_info)
                  next_table_addr
                  (EED.ia_region (PTEInfo.descriptor pte_info)).(range_start)
                  next_level
                  (EED.stage (PTEInfo.descriptor pte_info))
                  unmark_cb
                  READ_UNLOCKED_LOCATIONS
                  empty_cb_data;
          let (cm'', _) := res in
          ok cm''
      | _ => ok cm
      end
  | _ => ok cm
  end.

Definition dsb_visitor : PgtTraverseCB :=
  fun cm ctxt =>
    let this_cpu := cpu_id cm in
    dsb_kind <- (
      match (PgtTraverseCtxt.data ctxt) with
      | dsb_visitor_cb_data data => ok data
      | _ => err (bug invalid_callback_data)
      end);

    dsb_kind <- (
      if DxbKind.eqb dsb_kind DxB_nsh then
        if get_promote_dsb_nsh cm then ok DxB_ish
        else err (catch_fire unsupported_dsb_nsh)
      else
        ok dsb_kind
    );


    let loc_phys := (PgtTraverseCtxt.loc_phys ctxt) in
    loc <- get_location_without_ensure cm loc_phys;
    loc_info <- (Location.info loc) ?? ok (cm, ctxt);
    pte_info <- (LocationInfo.pte_info loc_info) ?? ok (cm, ctxt);

    match (PTEInfo.state pte_info) with
    | PTEState.invalid_unclean iu_state =>
      (TId.eqb (IUState.invalidator_tid iu_state) this_cpu) else_ret (ok (cm, ctxt));

      match (IUState.lis iu_state) with
      | LIS.unguarded =>
          let iu_state' := iu_state <| IUState.lis := LIS.dsbed |> in
          let pte_info' := pte_info <| PTEInfo.state := PTEState.invalid_unclean iu_state' |> in
          let loc_info' := loc_info <| LocationInfo.pte_info := Some pte_info' |> in
          let loc' := loc <| Location.info := Some loc_info' |> in
          cm' <- update_location cm loc';
          ok (cm', ctxt)

      | LIS.dsb_tlbied =>
          if DxbKind.eqb dsb_kind DxB_ish then
            let ic_state := {| ICState.invalidator_tid := this_cpu |} in
            let pte_info' := pte_info <| PTEInfo.state := PTEState.invalid ic_state |> in
            let loc_info' := loc_info <| LocationInfo.pte_info := Some pte_info' |> in
            let loc' := loc <| Location.info := Some loc_info' |> in
            cm' <- update_location cm loc';
            cm'' <- __update_descriptor_on_write cm' loc_phys (LocationInfo.val loc_info);
            ok (cm'', ctxt)
          else
            ok (cm, ctxt)

      | LIS.dsb_tlbi_ipa =>
          if DxbKind.eqb dsb_kind DxB_ish then
            let iu_state' := iu_state <| IUState.lis := LIS.dsb_tlbi_ipa_dsb |> in
            let pte_info' := pte_info <| PTEInfo.state := PTEState.invalid_unclean iu_state' |> in
            let loc_info' := loc_info <| LocationInfo.pte_info := Some pte_info' |> in
            let loc' := loc <| Location.info := Some loc_info' |> in
            cm' <- update_location cm loc';
            ok (cm', ctxt)
          else
            ok (cm, ctxt)

      | _ => ok (cm, ctxt)
      end
    | _ => ok (cm, ctxt)
    end.

Definition reset_write_authorizations (cm : Machine.t) : Machine.t :=
  let locker := cm.(Machine.state).(ModelState.state).(LockStateMap.locker) in
  let locker' := map_fold (
    fun k state acc =>
      let state' :=
        if TId.eqb (LockState.id state) (cpu_id cm) then
          state <| LockState.write_authorization := WriteAuth.AUTHORIZED |>
        else state in
      insert k state acc
  ) (Map.empty LockState.t) locker in
  let lsmap := @mk_LSM locker' in
  update_lock_state_map cm lsmap.

Definition step_dsb (cm : Machine.t) (barrier_data : TransBarrierData.t) : @ghost_model_result Machine.t :=
  let data := dsb_visitor_cb_data (TransBarrierData.dxb_kind barrier_data) in
  cm <- traverse_all_unclean_PTE cm dsb_visitor data ENTRY_STAGE_NONE;
  let cm' := reset_write_authorizations cm in
  ok cm'.

(** Barriers *)
Definition step_barrier
  (cm : Machine.t)
  (barrier_data : TransBarrierData.t) : @ghost_model_result Machine.t :=
  match barrier_data.(TransBarrierData.barrier_kind) with
  | BARRIER_ISB => step_isb cm
  | BARRIER_DSB => step_dsb cm barrier_data
  end.

(** Step on a TLBI *)
Definition step_pte_on_tlbi_after_dsb
  (cm : Machine.t)
  (loc_phys : PAddr.t)
  (tlbi : TLBIOp.t) : @ghost_model_result Machine.t :=
  loc <- get_location_without_ensure cm loc_phys;
  loc_info <- (Location.info loc) ?? ok cm;
  pte_info <- (LocationInfo.pte_info loc_info) ?? ok cm;

  match (PTEInfo.state pte_info) with
  | PTEState.invalid_unclean iu_state =>
    iu_state' <- (match TLBIOp.regime tlbi with
                  | TLBI_REGIME_EL2 =>
                      Some (iu_state <| IUState.lis := LIS.dsb_tlbied |>)
                  | TLBI_REGIME_EL10 =>
                      match (TLBIOp.stage tlbi) with
                      | TLBI_OP_STAGE1 => None
                      | TLBI_OP_STAGE2 =>
                          Some (iu_state <| IUState.lis := LIS.dsb_tlbi_ipa |>)
                      | TLBI_OP_BOTH_STAGES =>
                        Some (iu_state <| IUState.lis := LIS.dsb_tlbied |>)
                      end
                  end) ?? ok cm;
    let pte_info' := pte_info <| PTEInfo.state := PTEState.invalid_unclean iu_state |> in
    let loc_info' := loc_info <| LocationInfo.pte_info := Some pte_info' |> in
    let loc' := loc <| Location.info := Some loc_info' |> in
    update_location cm loc'
  | _ => ok cm
  end.

Definition step_pte_on_tlbi_after_tlbi_ipa
  (cm : Machine.t)
  (loc_phys : PAddr.t)
  (tlbi : TLBIOp.t) : @ghost_model_result Machine.t :=
  match TLBIOp.regime tlbi with
  | TLBI_REGIME_EL2 => err (assertion_fail invalid_tlbi_regime)
  | TLBI_REGIME_EL10 =>
    loc <- get_location_without_ensure cm loc_phys;
    loc_info <- (Location.info loc) ?? ok cm;
    pte_info <- (LocationInfo.pte_info loc_info) ?? ok cm;

    match (PTEInfo.state pte_info), (TLBIOp.stage tlbi) with
    | PTEState.invalid_unclean iu_state, TLBI_OP_STAGE1
    | PTEState.invalid_unclean iu_state, TLBI_OP_BOTH_STAGES =>
      let iu_state' := iu_state <| IUState.lis := LIS.dsb_tlbied |> in
      let pte_info' := pte_info <| PTEInfo.state := PTEState.invalid_unclean iu_state |> in
      let loc_info' := loc_info <| LocationInfo.pte_info := Some pte_info' |> in
      let loc' := loc <| Location.info := Some loc_info' |> in
      update_location cm loc'
    | _, _ => ok cm
    end
  end.

Definition step_pte_on_tlbi : PgtTraverseCB :=
  fun cm ctxt =>
    let this_cpu := cpu_id cm in
    match (PgtTraverseCtxt.data ctxt) with
    | tlbi_cb_data tlbi =>
        let loc_phys := (PgtTraverseCtxt.loc_phys ctxt) in
        loc <- get_location_without_ensure cm loc_phys;
        loc_info <- (Location.info loc) ?? err (assertion_fail location_not_initialised);
        pte_info <- (LocationInfo.pte_info loc_info) ?? ok (cm, ctxt);

        match (PTEInfo.state pte_info) with
        | PTEState.invalid_unclean iu_state =>
          (TId.eqb iu_state.(IUState.invalidator_tid) this_cpu) else_ret ok (cm, ctxt);

          match iu_state.(IUState.lis) with
          | LIS.unguarded => ok (cm, ctxt)
          | LIS.dsbed =>
              cm' <- step_pte_on_tlbi_after_dsb cm loc_phys tlbi;
              ok (cm', ctxt)
          | LIS.dsb_tlbi_ipa_dsb =>
              cm' <- step_pte_on_tlbi_after_tlbi_ipa cm loc_phys tlbi;
              ok (cm', ctxt)
          | _ => err (assertion_fail unimplemented)
          end
        | _ => ok (cm, ctxt)
        end
    | _ => err (bug invalid_callback_data)
    end.

Definition all_children_invalid
  (cm : Machine.t)
  (loc_phys : PAddr.t) : @ghost_model_result (Machine.t * bool) :=
  loc <- get_location_without_ensure cm loc_phys;
  loc_info <- (Location.info loc) ?? err (assertion_fail location_not_initialised);
  pte_info <- (LocationInfo.pte_info loc_info) ?? err (assertion_fail location_not_pte);

  let descriptor := pte_info.(PTEInfo.descriptor) in
  match descriptor.(EED.pte) with
  | PTE.map _ _
  | PTE.invalid => ok (cm, true)
  | PTE.table next_level_table_addr =>
  fold_left (fun (acc : @ghost_model_result (Machine.t * bool)) i =>
        res <- acc;
        let (cm, all_invalid) := res in
        all_invalid else_ret ok (cm, false);

        let idx := u64.of_nat i in
        let phys := PAddr.intro (next_level_table_addr u+ (8 u* idx)) in
        res <- location cm phys;
        let (cm', child) := res in

        loc_info <- (Location.info child) ?? err (assertion_fail location_not_initialised);
        pte_info <- (LocationInfo.pte_info loc_info) ?? err (assertion_fail location_not_pte);

        match (PTEInfo.state pte_info) with
        | PTEState.invalid _ => ok (cm', true)
        | _ => ok (cm', false)
        end
      ) (seq 0 SLOTS_PER_PAGE) (ok (cm, true))
  end.


Definition should_perform_tlbi
  (cm : Machine.t)
  (ctxt : PgtTraverseCtxt.t) : @ghost_model_result (Machine.t * bool * PgtTraverseCtxt.t) :=
  is_locked <- is_location_locked cm (PgtTraverseCtxt.loc_phys ctxt);
  if negb is_locked then ok (cm, false, ctxt)
  else
    tlbi <- (match (PgtTraverseCtxt.data ctxt) with
            | tlbi_cb_data tlbi => ok tlbi
            | _ => err (bug invalid_callback_data)
            end);
    tlbi <- (
      if negb tlbi.(TLBIOp.shootdown) then
        if get_promote_TLBI_nsh cm then
          ok (tlbi <| TLBIOp.shootdown := true |>)
        else
          err (catch_fire unsupported_tlbi_broadcast_expected)
      else ok tlbi);

    tlbi <- (
      match tlbi.(TLBIOp.method).(TLBIOpMethod.kind) with
      | TLBI_OP_BY_ADDR_SPACE =>
          if get_promote_TLBI_by_id cm then
            ok (tlbi <| TLBIOp.method; TLBIOpMethod.kind := TLBI_OP_BY_ALL |>)
          else
            err (catch_fire unsupported_tlbi_by_addr_id)
      | _ => ok tlbi
      end);

    let ctxt := ctxt <| PgtTraverseCtxt.data := tlbi_cb_data tlbi |> in
    match tlbi.(TLBIOp.method).(TLBIOpMethod.kind) with
    | TLBI_OP_BY_INPUT_ADDR =>
        let descriptor := PgtTraverseCtxt.exploded_descriptor ctxt in
        let ia_region := descriptor.(EED.ia_region) in
        let ia_start := (AddrRange.range_start ia_region) in
        let ia_end := ia_start u+ (AddrRange.range_size ia_region) in
        match tlbi.(TLBIOp.method).(TLBIOpMethod.data) with
        | tlbi_op_method_by_address_data
            page has_level_hint level_hint affects_last_level_only =>
            let tlbi_addr := page << PAGE_SHIFT in
            res <- (
              if negb ctxt.(PgtTraverseCtxt.leaf) then
                res <- all_children_invalid cm (PgtTraverseCtxt.loc_phys ctxt);
                let (cm', all_invalid) := res in
                if negb all_invalid then ok (cm', false)
                else ok (cm', true)
              else ok (cm, true)
            );
            let (cm, check) := res in
            check else_ret ok (cm, check, ctxt);

            if (u64.leb ia_start tlbi_addr) && (u64.ltb tlbi_addr ia_end) then
              if (negb (Level.eqb LEVEL3 ctxt.(PgtTraverseCtxt.level))) &&
                  affects_last_level_only then
                ok (cm, false, ctxt)
              else
                ok (cm, true, ctxt)
            else
              ok (cm, false, ctxt)
        | _ => err (catch_fire unsupported_tlbi_by_addr_id)
        end
    | TLBI_OP_BY_ALL => ok (cm, true, ctxt)
    | TLBI_OP_BY_ADDR_SPACE => err (catch_fire unsupported_tlbi_by_addr_id)
    end.


Definition tlbi_visitor : PgtTraverseCB :=
  fun cm ctxt =>
    res <- should_perform_tlbi cm ctxt;
    let (cm, perform) := fst res in
    let ctxt := snd res in
    if perform then
      res <- step_pte_on_tlbi cm ctxt;
      let (cm, ctxt) := res in
      ok (cm, ctxt)
    else ok (cm, ctxt).

Definition step_tlbi
  (cm : Machine.t)
  (tlbi_data : TransTlbiData.t) : @ghost_model_result Machine.t :=
  decoded <- decode_tlbi tlbi_data;
  match decoded.(TLBIOp.regime) with
  | TLBI_REGIME_EL10 =>
      traverse_all_unclean_PTE cm tlbi_visitor (tlbi_cb_data decoded) ENTRY_STAGE1
  | TLBI_REGIME_EL2 =>
      traverse_all_unclean_PTE cm tlbi_visitor (tlbi_cb_data decoded) ENTRY_STAGE2
  end.

(** Hardware Steps *)
Definition step_hw
  (cm : Machine.t)
  (hw_step : ghost_hw_step) : @ghost_model_result Machine.t :=
  match hw_step with
  | hw_mem_write write_data => step_write cm write_data
  | hw_mem_read read_data => step_read cm read_data
  | hw_barrier barrier_data => step_barrier cm barrier_data
  | hw_tlbi tlbi_data => step_tlbi cm tlbi_data
  | hw_msr msr_data => step_msr cm msr_data
  end.

(** Hint *)
Definition step_hint_set_root_lock
  (cm : Machine.t)
  (root : u64.t)
  (lock : u64.t) : @ghost_model_result Machine.t :=
  associate_lock cm (OwnerAddr.intro root) (LockAddr.intro lock).

Fixpoint step_hint_set_owner_root_inner
  (cm : Machine.t)
  (n : nat)
  (phys root : u64.t) : @ghost_model_result Machine.t :=
  match n with
  | O => ok cm
  | S n' =>
    res <- location cm (PAddr.intro phys);
    let (cm', loc) := res in
    loc_info <- (Location.info loc) ?? err (assertion_fail location_not_initialised);
    let loc_info' := loc_info <| LocationInfo.owner := OwnerAddr.intro root |> in
    let loc' := loc <| Location.info := Some loc_info' |> in
    cm'' <- update_location cm' loc';
    step_hint_set_owner_root_inner cm'' n' (phys u+ 8) root
  end.

Definition step_hint_set_owner_root
  (cm : Machine.t)
  (phys root : u64.t) : @ghost_model_result Machine.t :=
  let start_page := PAGE_ALIGN_DOWN phys in
  let end_page := PAGE_ALIGN phys in
  let nr_pages := u64.to_nat ((end_page - start_page) >> 8) in
  step_hint_set_owner_root_inner cm nr_pages phys root.

Definition check_release_cb : PgtTraverseCB :=
  fun cm ctxt =>
    let loc_phys := ctxt.(PgtTraverseCtxt.loc_phys) in
    loc <- get_location_without_ensure cm loc_phys;
    loc_info <- (Location.info loc) ?? err (assertion_fail location_not_initialised);
    pte_info <- (LocationInfo.pte_info loc_info) ?? err (assertion_fail location_not_pte);

    match pte_info.(PTEInfo.state) with
    | PTEState.invalid_unclean _ =>
      err (catch_fire release_table_with_unclean_children)
    | _ => ok (cm, ctxt)
    end.

Definition step_hint_release_table
  (cm : Machine.t)
  (root : u64.t) : @ghost_model_result Machine.t :=
  loc <- get_location_without_ensure cm (PAddr.intro root);
  loc_info <- (Location.info loc) ?? err (assertion_fail location_not_initialised);
  pte_info <- (LocationInfo.pte_info loc_info) ?? err (assertion_fail location_not_pte);
  let descriptor := PTEInfo.descriptor pte_info in
  let table_start := LocationInfo.owner loc_info in
  let partial_ia := descriptor.(EED.ia_region).(AddrRange.range_size) in
  let level := descriptor.(EED.level) in
  let stage := descriptor.(EED.stage) in

  res <- (traverse_pgtable_from
            cm
            root table_start partial_ia
            level
            stage
            check_release_cb
            READ_UNLOCKED_LOCATIONS
            empty_cb_data);
  let (cm', _) := res in
  try_unregister_root cm' stage (PAddr.intro root).

Definition step_hint_set_PTE_thread_owner
  (cm : Machine.t)
  (phys val : u64.t) : @ghost_model_result Machine.t :=
  loc <- get_location_without_ensure cm (PAddr.intro phys);
  loc_info <- (Location.info loc) ?? err (assertion_fail location_not_initialised);
  pte_info <- (LocationInfo.pte_info loc_info) ?? err (assertion_fail location_not_pte);

  let descriptor := PTEInfo.descriptor pte_info in
  let level := descriptor.(EED.level) in
  match descriptor.(EED.level) with
  | LEVEL3 =>
      let loc' := loc <| Location.thread_owner := Some (u64.to_nat val) |> in
      update_location cm loc'
  | _ => err (assertion_fail location_not_in_LEVEL3)
  end.

Definition step_hint
  (cm : Machine.t) (hint_step : ghost_hint_step) : @ghost_model_result Machine.t :=
  match hint_step with
  | ghost_hint_set_root_lock location value =>
      step_hint_set_root_lock cm location value
  | ghost_hint_set_owner_root location value =>
      step_hint_set_owner_root cm location value
  | ghost_hint_release_table location =>
      step_hint_release_table cm location
  | ghost_hint_set_pte_thread_owner location value =>
      step_hint_set_PTE_thread_owner cm location value
  end.

(** ABS *)

Definition __step_lock
  (cm : Machine.t)
  (lock_addr : LockAddr.t) : @ghost_model_result Machine.t :=
  match lock_state_by_addr cm lock_addr with
  | Some _ => err (catch_fire lock_component_already_held)
  | _ =>
      let lsmap := get_lock_state_map cm in
      if LockStateMap.len lsmap <? casemate_model_MAX_LOCKS then
        let lock_state :=
          {| id := cpu_id cm;
             write_authorization := WriteAuth.AUTHORIZED |} in
        ok (update_lock_state_by_addr cm lock_addr lock_state)
      else
        err (bug exceeds_num_of_max_locks)
  end.

Definition __step_unlock
  (cm : Machine.t)
  (lock_addr : LockAddr.t) : @ghost_model_result Machine.t :=
  match lock_state_by_addr cm lock_addr with
  | Some state =>
      if state.(LockState.id) =? (cpu_id cm) then
        let lsmap := get_lock_state_map cm in
        let lsmap' := lsmap <| LockStateMap.locker ::= delete lock_addr |> in
        ok (update_lock_state_map cm lsmap')
      else err (catch_fire unlock_component_held_by_another_thread)
  | _ =>
      err (catch_fire unlock_component_not_held)
  end.

Definition __do_plain_write
  (cm : Machine.t)
  (phys_addr : u64.t)
  (val : u64.t) : @ghost_model_result Machine.t :=
  let write_data :=
    {| TransWriteData.mo := WMO_plain;
       TransWriteData.phys_addr := PAddr.intro phys_addr;
       TransWriteData.val := val; |} in
  step_write cm write_data.

Definition __step_memset
  (cm : Machine.t)
  (phys_addr size val : u64.t) : @ghost_model_result Machine.t :=
  (IS_PAGE_ALIGNED phys_addr) else_ret err (assertion_fail not_page_aligned);
  (IS_PAGE_ALIGNED size) else_ret err (assertion_fail not_page_aligned);
  let nr_pages := u64.to_nat (size >> 8) in

  fold_left (fun acc i =>
    cm <- acc;
    let idx := u64.of_nat i in
    let phys := phys_addr u+ idx u* sizeof_u64 in
    __do_plain_write cm phys val
  ) (seq 0 nr_pages) (ok cm).

Definition __step_init
  (cm : Machine.t)
  (phys_addr size : u64.t) : @ghost_model_result Machine.t :=
  let start_page := phys_addr in
  let end_page := phys_addr u+ size in
  let nr_pages := u64.to_nat ((u64.sub end_page start_page) >> 8) in

  fold_left (fun acc i =>
    cm <- acc;
    let idx := u64.of_nat i in
    let phys := PAddr.intro (phys_addr u+ idx u* sizeof_u64) in
    res <- location cm phys;
    let (cm', loc) := res in

    match Location.info loc with
    | None =>
        initialise_location cm phys zeros
    | Some _ =>
        __do_plain_write cm phys zeros
    end
  ) (seq 0 nr_pages) (ok cm).

Definition step_abs
  (cm : Machine.t)
  (abs_step : ghost_abs_step) : @ghost_model_result Machine.t :=
  match abs_step with
  | ghost_abs_init init_data =>
      __step_init cm (TransInitData.location init_data) (TransInitData.size init_data)
  | ghost_abs_lock lock_data =>
      __step_lock cm (LockAddr.intro (TransLockData.address lock_data))
  | ghost_abs_unlock lock_data =>
      __step_unlock cm (LockAddr.intro (TransLockData.address lock_data))
  | ghost_abs_memset memset_data =>
      __step_memset cm
        (TransMemsetData.address memset_data)
        (TransMemsetData.size memset_data)
        (TransMemsetData.value memset_data)
  end.

Definition step
  (cm : Machine.t)
  (trans : ModelStep.t) : @ghost_model_result Machine.t :=
  let cm := cm <| Machine.step := Some trans |> in
  match trans.(ModelStep.kind) with
  | Step.trans_hw_step hw_step => step_hw cm hw_step
  | Step.trans_abs_step abs_step => step_abs cm abs_step
  | Step.trans_hint_step hint_step => step_hint cm hint_step
 end.
