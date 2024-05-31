
Require Import simplified.simplified.
Require Import stdpp.bitvector.bitvector.
Require Import stdpp.bitvector.definitions.
Require Import stdpp.gmap.
Require Import Cmap.cmap.

Require Coq.extraction.Extraction.
Extraction Language OCaml.

Extract Inlined Constant n512 => "512".

Extract Inlined Constant BV64 => "".
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

Extract Inlined Constant bv_add => "(fun _ a b -> Za.add a b)".
Extract Inlined Constant bv_sub => "(fun _ a b -> Za.sub a b)".
Extract Inlined Constant bv_mul => "(fun _ a b -> Za.mul a b)".
Extract Inlined Constant bv_and => "(fun _ a b -> Za.logand a b)".
Extract Inlined Constant bv_mul_Z => "(fun _ a b -> Za.mul a b)".

Extract Inlined Constant ghost_simplified_model_state => "sm_location Cmap.t".
Extract Inlined Constant cmap_empty => "(Cmap.empty ())".
Extract Inlined Constant cmap_lookup => "(fun g m -> Cmap.lookup g m)".
Extract Inlined Constant cmap_insert => "(fun k a m -> Cmap.insert k a m)".


Extract Inductive result => "Stdlib.result" [ "Ok" "Error" ].

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNativeString.
Require Import ExtrOcamlZBigInt.
Require Import ExtrOcamlNatInt.

Set Extraction Optimize.
(* Enable all optimizations *)
Set Extraction Flag 2031.
Set Extraction Output Directory ".".

Set Warnings "-extraction-opaque-accessed".
Extraction "coq_executable_sm.ml" all_steps memory_0 step.
