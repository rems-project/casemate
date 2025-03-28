(** Casemate - Entrypoint *)
Require Export utils.
Require Export transitions.
Require Export model.
Require Export pgtable.
Require Export step.

Definition step
  (trans : ghost_simplified_model_transition) 
  (gsm : ghost_simplified_model) : 
  ghost_simplified_model_result :=
  match trans.(gsmt_data) with
  | GSMDT_TRANS_MEM_WRITE wd =>
      step_write trans.(gsmt_thread_identifier) wd gsm
  | GSMDT_TRANS_MEM_ZALLOC zd =>
      step_zalloc zd gsm
  | GSMDT_TRANS_MEM_READ rd =>
      step_read trans.(gsmt_thread_identifier) rd gsm
  | GSMDT_TRANS_BARRIER ( Barrier_DSB dsb_data) =>
      step_dsb trans.(gsmt_thread_identifier) dsb_data gsm
  | GSMDT_TRANS_BARRIER (_) =>
      {| gsmsr_log := []; gsmsr_data := Ok _ _ gsm |}
  | GSMDT_TRANS_TLBI tlbi_data =>
      step_tlbi trans.(gsmt_thread_identifier) tlbi_data gsm
  | GSMDT_TRANS_MSR msr_data =>
      step_msr trans.(gsmt_thread_identifier) msr_data gsm
  | GSMDT_TRANS_HINT hint_data =>
      step_hint trans.(gsmt_thread_identifier) hint_data gsm
  | GSMDT_TRANS_LOCK lock_data =>
      step_lock trans.(gsmt_thread_identifier) lock_data gsm
  end.

Definition memory_init := {|
  gsm_roots := {| pr_s1 := []; pr_s2 := []; |};
  gsm_memory := ∅;
  gsm_zalloc := ∅;
  gsm_lock_addr := ∅;
  gsm_lock_state := ∅;
  gsm_lock_authorization := ∅;
|}.

Fixpoint steps
  (transitions : list ghost_simplified_model_transition)
  (logs : list log_element)
  (gsm : ghost_simplified_model) :
  ghost_simplified_model_result :=
  match transitions with
    | [] => {| gsmsr_log := logs; gsmsr_data := Ok _ _ gsm; |}
    | h :: t =>
      match step h gsm with
        | {| gsmsr_log := logs_next; gsmsr_data := Ok _ _ st_next |} =>
            steps t (logs_next ++ logs) st_next
        | {| gsmsr_log := logs_next; gsmsr_data := Error _ _ f |} =>
            {| gsmsr_log := logs_next ++ logs; gsmsr_data := Error _ _ f |}
      end
  end
.

Definition run_model 
  (transitions : list ghost_simplified_model_transition) :
  ghost_simplified_model_result :=
  let res := steps transitions [] memory_init in
  res <| gsmsr_log := rev res.(gsmsr_log) |>
.
