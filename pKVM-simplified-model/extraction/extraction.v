
Require Import simplified.simplified.

Require Coq.extraction.Extraction.
Extraction Language OCaml.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNativeString.
Require Import ExtrOcamlZBigInt.
Require Import ExtrOcamlNatInt.

Set Extraction Optimize.
(* Enable all optimizations *)
Set Extraction Flag 2031.
Set Extraction Output Directory ".".

Extraction "coq_executable_sm.ml" all_steps.
