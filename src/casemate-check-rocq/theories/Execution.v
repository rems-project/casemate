Require Extraction.
Require Import String.
Require stdpp.bitvector.bitvector.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.
Require Import stdpp.gmap.

Require Import Blobs.
Require Import Transitions.
Require Import Model.
Require Import Machine.

Definition initialise_machine
  (cfg : Options.t)
  (phys : PAddr.t)
  (size : u64.t) : Machine.t :=
  let init_state := initialize_ghost_ptes_memory ModelState.empty phys size in
  let init_step := None in
  {| Machine.state := init_state;
     Machine.step := init_step;
     Machine.options := cfg |}.

Definition steps
  (traces : list ModelStep.t)
  (cfg : Options.t)
  (phys : PAddr.t)
  (size : u64.t) : @ghost_model_result Machine.t :=
  let cm := initialise_machine cfg phys size in
  fold_left (fun acc trans =>
    cm <- acc;
    Model.step cm trans
  ) traces (ok cm).

