Require Coq.extraction.Extraction.
Extraction Language OCaml.

Require Export Casemate.Execution.
Require Import stdpp.bitvector.bitvector.
Require Import stdpp.bitvector.definitions.
Require Import stdpp.gmap.

(**
  Extract Inlined Constant u64.t => "".
  Extract Inlined Constant Z_to_bv_checked => "(fun _ _ -> ())".

  Extract Inlined Constant u64.of_nat => "Za.of_nat".
  Extract Inlined Constant u64.to_nat => "Za.to_nat".
  Extract Inlined Constant u64.add => "Za.add64".
  Extract Inlined Constant u64.sub => "Za.sub64".
  Extract Inlined Constant u64.mul => "Za.mul64".
  Extract Inlined Constant u64.and => "Za.and64".
  Extract Inlined Constant u64.shiftr => "Za.shr64".
  Extract Inlined Constant u64.shiftl => "Za.shl64".

  Extract Inductive ghost_model_result => "Stdlib.result" [ "Ok" "Error" ]. *)

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNativeString.
Require Import ExtrOcamlZBigInt.
Require Import ExtrOcamlNatInt.

Set Extraction Optimize.
(* Enable all optimizations *)
Set Extraction Flag 2031.
Set Extraction Output Directory ".".

Set Warnings "-extraction-opaque-accessed -extraction-axiom-to-realize".
Extraction "coq_executable_cm.ml" initialise_machine steps.
