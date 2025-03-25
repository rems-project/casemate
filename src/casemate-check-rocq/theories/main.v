(** Casemate *)
Require Import String.
Require stdpp.bitvector.bitvector.
Require Import Cmap.cmap.
Require Import Zmap.zmap.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.
Require Import stdpp.gmap.
Require Import Recdef.

Require Export step.

Definition take_step
  (trans : casemate_model_step)
  (cm : casemate_model_state) :
  casemate_model_result :=
  match trans.(cms_data) with
  | CMSD_TRANS_HW_MEM_WRITE wd =>
    step_write trans.(cms_thread_identifier) wd cm
  | CMSD_TRANS_HW_MEM_READ rd =>
    step_read trans.(cms_thread_identifier) rd cm
  | CMSD_TRANS_HW_BARRIER (Barrier_DSB dsb_data) =>
    step_dsb trans.(cms_thread_identifier) dsb_data cm
  | CMSD_TRANS_HW_BARRIER (_) =>
    {| cmr_log := []; cmr_data := Ok _ _ cm |}
  | CMSD_TRANS_HW_TLBI tlbi_data =>
    step_tlbi trans.(cms_thread_identifier) tlbi_data cm
  | CMSD_TRANS_HW_MSR msr_data =>
    step_msr trans.(cms_thread_identifier) msr_data cm
  | CMSD_TRANS_ABS_LOCK lock_data =>
    step_lock trans.(cms_thread_identifier) lock_data cm
  | CMSD_TRANS_ABS_UNLOCK lock_data =>
    step_unlock trans.(cms_thread_identifier) lock_data cm
  | CMSD_TRANS_ABS_MEM_INIT init_data =>
    step_init init_data cm
  | CMSD_TRANS_ABS_MEMSET memset_data =>
    step_memset trans.(cms_thread_identifier) memset_data cm
  | CMSD_TRANS_HINT hint_data =>
    step_hint trans.(cms_thread_identifier) hint_data cm
  end.

Definition memory_init := {|
  cm_roots := {| pr_s1 := []; pr_s2 := []; |};
  cm_memory := ∅;
  cm_initialised := ∅;
  cm_thrd_ctxt := [];
  cm_lock_addr := ∅;
  cm_lock_state := ∅;
  cm_lock_authorization := ∅;
|}.

Fixpoint steps_aux
  (transitions : list casemate_model_step)
  (logs : list log_element)
  (cm : casemate_model_state) :
  casemate_model_result :=
  match transitions with
  | [] => {| cmr_log := logs; cmr_data := Ok _ _ cm; |}
  | h :: t =>
    match take_step h cm with
    | {| cmr_log := logs_next; cmr_data := Ok _ _ st_next |} =>
        steps_aux t (logs_next ++ logs) st_next
    | {| cmr_log := logs_next; cmr_data := Error _ _ f |} =>
        {| cmr_log := logs_next ++ logs; cmr_data := Error _ _ f |}
    end
  end
.

Definition steps
  (transitions : list casemate_model_step) :
  casemate_model_result :=
  let res := steps_aux transitions [] memory_init in
  res <| cmr_log := rev res.(cmr_log) |>
.

