Require Import ZArith.
Require Import PeanoNat.
From stdpp Require Import gmap.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Require Export ModelHeader.
Require Import Transitions.
Require Import Machine.

(** Memory *)
Definition get_memory_from_machine (m : Machine.t) : Memory.t :=
  m.(Machine.state).(ModelState.memory).

Definition update_memory_in_machine
  (m : Machine.t) (mem : Memory.t) : Machine.t :=
  m <| Machine.state; ModelState.memory := mem |>.

Definition initialize_ghost_ptes_memory
  (the_ghost_state : ModelState.t)
  (phys : PAddr.t)
  (size : u64.t) : ModelState.t :=
  the_ghost_state <| ModelState.base_addr := phys |>
                  <| ModelState.size := size |>
                  <| ModelState.memory := Memory.empty |>.

Definition check_sanity_of_blobs (mem : Memory.t) : bool :=
  forallb (fun x => MemoryBlob.valid (snd x)) (map_to_list mem.(Memory.blobs_backing)).

Definition check_sanity_of_no_blob
  (mem : Memory.t)
  (phys : PAddr.t) : bool :=
  let page := ALIGN_DOWN_TO_BLOB phys in
  match Map.lookup page mem.(Memory.blobs_backing) with
  | Some blob => blob.(MemoryBlob.valid)
  | None => true
  end.

Definition blob_of
  (mem : Memory.t)
  (phys : PAddr.t) : option MemoryBlob.t :=
  Map.lookup phys mem.(Memory.blobs_backing).

Definition find_blob
  (mem : Memory.t)
  (phys : PAddr.t) : option MemoryBlob.t :=
  blob_of mem (PAddr.intro (ALIGN_DOWN_TO_BLOB phys)).

Definition insert_blob_at_end
  (cm : Machine.t)
  (blob : MemoryBlob.t) : Machine.t :=
  let mem := get_memory_from_machine cm in
  let phys := blob.(MemoryBlob.phys) in
  let mem' := mem <| Memory.blobs_backing ::= insert phys blob |> in
  update_memory_in_machine cm mem'.

Definition ensure_blob
  (cm : Machine.t)
  (phys : PAddr.t) : @ghost_model_result Machine.t :=
  let mem := get_memory_from_machine cm in
  let blob_phys := ALIGN_DOWN_TO_BLOB phys in
  match find_blob mem (PAddr.intro blob_phys) with
  | Some blob => ok cm
  | None =>
    if negb (check_sanity_of_no_blob mem phys) then
      err (bug failed_blobs_sanity_check)
    else if ((Memory.nr_allocated_blobs mem) =? MAX_BLOBS) then
      err (assertion_fail run_out_of_free_blobs)
    else
      let initialized_blob := MemoryBlob.initialise blob_phys in
      ok (insert_blob_at_end cm initialized_blob)
  end.

Definition blob_unclean (blob : MemoryBlob.t) : bool :=
  existsb (fun slot =>
    loc_info <- (Location.info slot) ?? false;
    pte_info <- (LocationInfo.pte_info loc_info) ?? false;
    match pte_info.(PTEInfo.state) with
    | PTEState.invalid_unclean _ => true
    | _ => false
    end) blob.(MemoryBlob.slots).

Definition location
  (cm : Machine.t)
  (phys : PAddr.t) : ghost_model_result (A := Machine.t * Location.t) :=
  cm' <- ensure_blob cm phys;
  let mem := get_memory_from_machine cm' in
  blob <- find_blob mem phys ?? err (bug ensured_blobs_not_found);
  match nth_opt blob.(MemoryBlob.slots) (SLOT_OFFSET_IN_BLOB phys) with
  | Some loc => ok (cm', loc)
  | None => err (bug index_out_of_bounds)
  end.

Definition __read_phys
  (cm : Machine.t)
  (addr : u64.t)
  (pre : bool) : ghost_model_result (A := Machine.t * u64.t) :=
  let mem := get_memory_from_machine cm in
  res <- location cm (PAddr.intro addr);

  let (cm', loc) := res in
  loc_info <- (Location.info loc) ?? err (catch_fire uninitialized_location);

  step <- Machine.step cm ?? err (bug transition_not_initialised);
  match (ModelStep.is_on_write_transition step addr), pre with
  | true, false => ok (cm', addr)
  | _, _ => ok (cm', (LocationInfo.val loc_info))
  end.

Definition read_phys_pre
  (cm : Machine.t)
  (addr : u64.t) : ghost_model_result (A := Machine.t * u64.t) :=
  __read_phys cm addr true.

Definition read_phys
  (cm : Machine.t)
  (addr : u64.t) : ghost_model_result (A := Machine.t * u64.t) :=
  __read_phys cm addr false.

(* Helper function to update the nth element in a list *)
Fixpoint update_nth {A} (l : list A) (idx : u64.t) (v : A) : list A :=
  match l with
  | [] => []
  | hd :: tl => if idx u=? zeros then v :: tl else hd :: update_nth tl (u64.decr idx) v
  end.

Definition update_location
  (cm : Machine.t) (loc : Location.t) : @ghost_model_result Machine.t :=
  let phys := Location.phys_addr loc in
  let mem := get_memory_from_machine cm in
  blob <- find_blob mem phys ?? err (bug ensured_blobs_not_found);
  let slots' := update_nth blob.(MemoryBlob.slots) (SLOT_OFFSET_IN_BLOB phys) loc in
  let blob' := blob <| MemoryBlob.slots := slots' |> in
  let mem' := mem <| Memory.blobs_backing ::= update blob.(MemoryBlob.phys) blob |> in
  ok (update_memory_in_machine cm mem').
