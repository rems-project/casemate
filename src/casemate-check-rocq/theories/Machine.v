Require Import ZArith.
Require Import PeanoNat.
From stdpp Require Import gmap.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Require Export ModelHeader.
Require Import Transitions.
Require Import Types.

(** Options *)
Module CheckerOptions. (* casemate_checker_options *)
  Record t := mk_CO {
    promote_dsb_nsh : bool;              (* Silently promote all DSB NSH to DSB ISH *)
    promote_tlbi_nsh : bool;             (* Silently promote all TLBI to broadcast ones *)
    promote_tlbi_by_id : bool;           (* Silently promote all TLBI-by-ASID and by-VMID to ALL *)
    check_synchronisation : bool;        (* Check that locks are respected; unsafe to disable for online checking *)
  }.
End CheckerOptions.

#[export] Instance eta_CO : Settable _ :=
  settable! CheckerOptions.mk_CO <
    CheckerOptions.promote_dsb_nsh;
    CheckerOptions.promote_tlbi_nsh;
    CheckerOptions.promote_tlbi_by_id;
    CheckerOptions.check_synchronisation>.

Module Options. (* casemate_options *)
  Record t := mk_OPT {
    enable_checking : bool;                (* Enable or disable runtime model checking *)
    check_opts : CheckerOptions.t;         (* Nested checker options record *)
    enable_safety_checks : bool;           (* Enable non-functional model-internal consistency checks *)
  }.
End Options.
#[export] Instance eta_OPT : Settable _ :=
  settable! Options.mk_OPT <
    Options.enable_checking;
    Options.check_opts;
    Options.enable_safety_checks>.

(** State Machine *)
Module Export Machine.
  Record t := mk_M {
    state : ModelState.t;
    step : option ModelStep.t;
    options : Options.t;
  }.

  #[export] Instance eta_M : Settable _ :=
    settable! mk_M <
      state;
      step;
      options>.
End Machine.
(* Shortcuts *)
Definition get_check_synchronisation (m : Machine.t) : bool :=
  m.(Machine.options).(Options.check_opts).(CheckerOptions.check_synchronisation).

Definition get_promote_dsb_nsh (m : Machine.t) : bool :=
  m.(Machine.options).(Options.check_opts).(CheckerOptions.promote_dsb_nsh).

Definition get_promote_TLBI_nsh (m : Machine.t) : bool :=
  m.(Machine.options).(Options.check_opts).(CheckerOptions.promote_tlbi_nsh).

Definition get_promote_TLBI_by_id (m : Machine.t) : bool :=
  m.(Machine.options).(Options.check_opts).(CheckerOptions.promote_tlbi_by_id).

Definition cpu_id (m : Machine.t) : TId.t :=
  match m.(Machine.step) with
  | None => O
  | Some step => (ModelStep.thread_identifier step)
  end.
