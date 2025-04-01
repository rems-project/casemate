(** Casemate - Entrypoint *)
Require Export utils.
Require Export transitions.
Require Export model.
Require Export pgtable.
Require Export step.

Fixpoint steps
  (transitions : list casemate_model_step)
  (logs : list log_element)
  (cms : casemate_model_state) :
  casemate_model_result :=
  match transitions with
    | [] => {| cmr_log := logs; cmr_data := Ok _ _ cms; |}
    | h :: t =>
      match step h cms with
        | {| cmr_log := logs_next; cmr_data := Ok _ _ st_next |} =>
            steps t (logs_next ++ logs) st_next
        | {| cmr_log := logs_next; cmr_data := Error _ _ f |} =>
            {| cmr_log := logs_next ++ logs; cmr_data := Error _ _ f |}
      end
  end
.

Definition run_model 
  (transitions : list casemate_model_step) :
  casemate_model_result :=
  let res := steps transitions [] cms_init in
  res <| cmr_log := rev res.(cmr_log) |>
.
