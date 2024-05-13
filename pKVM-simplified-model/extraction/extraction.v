
Require Import simplified.simplified.

Require Coq.extraction.Extraction.
Extraction Language OCaml.

Extract Inlined Constant n512 => "512".

Extract Inlined Constant b0 => "(Big_int_Z.big_int_of_int 0)".
Extract Inlined Constant b1 => "(Big_int_Z.big_int_of_int 1)".
Extract Inlined Constant b2 => "(Big_int_Z.big_int_of_int 2)".
Extract Inlined Constant b8 => "(Big_int_Z.big_int_of_int 8)".
Extract Inlined Constant b12 => "(Big_int_Z.big_int_of_int 12)".
Extract Inlined Constant b16 => "(Big_int_Z.big_int_of_int 16)".
Extract Inlined Constant b47 => "(Big_int_Z.big_int_of_int 47)".
Extract Inlined Constant b63 => "(Big_int_Z.big_int_of_int 63)".
Extract Inlined Constant b512 => "(Big_int_Z.big_int_of_int 512)".
Extract Inlined Constant b1023 => "(Big_int_Z.big_int_of_int 1023)".

Extract Inductive result => "Stdlib.result" [ "Ok" "Error" ].

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNativeString.
Require Import ExtrOcamlZBigInt.
Require Import ExtrOcamlNatInt.

Set Extraction Optimize.
(* Enable all optimizations *)
Set Extraction Flag 2031.
Set Extraction Output Directory ".".

Extraction "coq_executable_sm.ml" all_steps state_0 step_.
