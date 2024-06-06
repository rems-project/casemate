
Require Import simplified.simplified.
Require Import stdpp.bitvector.bitvector.
Require Import stdpp.bitvector.definitions.
Require Import stdpp.gmap.
Require Import Cmap.cmap.

Require Coq.extraction.Extraction.
Extraction Language OCaml.

Extract Inlined Constant n512 => "512".

Extract Inlined Constant bv64.BV64 => "".
Extract Inlined Constant Z_to_bv_checked => "(fun _ _ -> ())".
Extract Inlined Constant b0 => "(Za.of_int 0)".
Extract Inlined Constant b1 => "(Za.of_int 1)".
Extract Inlined Constant b2 => "(Za.of_int 2)".
Extract Inlined Constant b8 => "(Za.of_int 8)".
Extract Inlined Constant b12 => "(Za.of_int 12)".
Extract Inlined Constant b16 => "(Za.of_int 16)".
Extract Inlined Constant b47 => "(Za.of_int 47)".
Extract Inlined Constant b63 => "(Za.of_int 63)".
Extract Inlined Constant b512 => "(Za.of_int 512)".
Extract Inlined Constant b1023 => "(Za.of_int 1023)".

Extract Inlined Constant bv64.bv_add_64 => "Za.add64".
Extract Inlined Constant bv64.bv_mul_64 => "Za.mul64".
Extract Inlined Constant bv64.bv_mul_Z_64 => "Za.mul64".
Extract Inlined Constant bv64.bv_and_64 => "Za.and64".
Extract Inlined Constant bv64.bv_shiftr_64 => "Za.shr64".
Extract Inlined Constant bv64.bv_shiftl_64 => "Za.shl64".

Extract Inlined Constant ghost_simplified_model_state => "(sm_location Cmap.t)".
Extract Inlined Constant cmap_empty => "(Cmap.empty ())".
Extract Inlined Constant cmap_lookup => "Cmap.lookup".
Extract Inlined Constant cmap_insert => "Cmap.insert".


Extract Inductive result => "Stdlib.result" [ "Ok" "Error" ].

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNativeString.
Require Import ExtrOcamlZBigInt.
Require Import ExtrOcamlNatInt.

Set Extraction Optimize.
(* Enable all optimizations *)
Set Extraction Flag 2031.
Set Extraction Output Directory ".".

Set Warnings "-extraction-opaque-accessed -extraction-axiom-to-realize".
Extraction "coq_executable_sm.ml" all_steps memory_0 step.
