(** Simplified model *)
(* https://github.com/rems-project/linux/blob/pkvm-verif-6.4/arch/arm64/kvm/hyp/include/nvhe/ghost_simplified_model.h *)
Require Import String.
Require stdpp.bitvector.bitvector.
Require Import Cmap.cmap.
Require Import Zmap.zmap.
(* uses https://github.com/tchajed/coq-record-update *)
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.
Require Import stdpp.gmap.
Require Import Recdef.

Require Export automata.


(******************************************************************************************)
(*                             Toplevel function                                          *)
(******************************************************************************************)

Definition step (trans : ghost_simplified_model_transition) (st : ghost_simplified_memory) : ghost_simplified_model_result :=
  match trans.(gsmt_data) with
  | GSMDT_TRANS_MEM_WRITE wd =>
    step_write trans.(gsmt_thread_identifier) wd st
  | GSMDT_TRANS_MEM_ZALLOC zd => step_zalloc zd st
  | GSMDT_TRANS_MEM_READ rd =>
    step_read trans.(gsmt_thread_identifier) rd st
  | GSMDT_TRANS_BARRIER ( Barrier_DSB dsb_data) =>
    step_dsb trans.(gsmt_thread_identifier) dsb_data st
  | GSMDT_TRANS_BARRIER (_) => {| gsmsr_log := nil; gsmsr_data := Ok _ _ st|} (* Ignored *)
  | GSMDT_TRANS_TLBI tlbi_data => step_tlbi trans.(gsmt_thread_identifier) tlbi_data st
  | GSMDT_TRANS_MSR msr_data => step_msr trans.(gsmt_thread_identifier) msr_data st
  | GSMDT_TRANS_HINT hint_data => step_hint trans.(gsmt_thread_identifier) hint_data st
  | GSMDT_TRANS_LOCK lock_data => step_lock trans.(gsmt_thread_identifier) lock_data st
  end.


Fixpoint all_steps_aux (transitions : list ghost_simplified_model_transition) (logs : list log_element) (st : ghost_simplified_memory) : ghost_simplified_model_result :=
  match transitions with
    | [] => {| gsmsr_log := logs; gsmsr_data := Ok _ _ st; |}
    | h :: t =>
      match step h st with
        | {| gsmsr_log := logs1; gsmsr_data := Ok _ _ st |} => all_steps_aux t (logs1 ++ logs) st
        | {| gsmsr_log := logs1; gsmsr_data := Error _ _ f |} =>
            {| gsmsr_log := logs1 ++ logs; gsmsr_data := Error _ _ f; |}
      end
  end
.


Definition memory_0 := {|
  gsm_roots := {| pr_s1 := []; pr_s2 := []; |};
  gsm_memory := empty;
  gsm_zalloc := zmap_empty;
  gsm_lock_addr := zmap_empty;
  gsm_lock_state := zmap_empty;
|}.


Definition all_steps (transitions : list ghost_simplified_model_transition) : ghost_simplified_model_result :=
  let
    initial_state := memory_0
  in
  let res := all_steps_aux transitions [] initial_state in
  res <| gsmsr_log := rev res.(gsmsr_log) |>
.

(* https://github.com/rems-project/linux/blob/pkvm-verif-6.4/arch/arm64/kvm/hyp/nvhe/ghost_simplified_model.c *)
