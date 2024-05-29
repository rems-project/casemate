
Require Import simplified.simplified.
Require Import stdpp.bitvector.bitvector.
Require Import stdpp.bitvector.definitions.
Require Import stdpp.gmap.

Require Coq.extraction.Extraction.
Extraction Language OCaml.

Extract Inlined Constant n512 => "512".

Extract Inlined Constant BV64 => "".
Extract Inlined Constant Z_to_bv_checked => "(fun _ _ -> ())".
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

Extract Inlined Constant bv_add => "(fun _ a b -> Z.add a b)".
Extract Inlined Constant bv_sub => "(fun _ a b -> Z.sub a b)".
Extract Inlined Constant bv_mul => "(fun _ a b -> Z.mul a b)".
Extract Inlined Constant bv_and => "(fun _ a b -> Big_int_Z.and_big_int a b)".
Extract Inlined Constant bv_mul_Z => "(fun _ a b -> Z.mul a b)".



Extract Inlined Constant ghost_simplified_model_state => "sm_location Cmap.t".
Extract Inlined Constant ghost_simplified_model_zallocd => "unit Cmap.t".
Extract Inlined Constant gmap_empty => "(fun _ _ -> Cmap.empty ())".
Extract Inlined Constant lookup => "(fun _ g m -> Cmap.lookup g m)".
Extract Inlined Constant insert => "(fun _ k a m -> Cmap.insert k a m)".


Extract Inductive result => "Stdlib.result" [ "Ok" "Error" ].

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNativeString.
Require Import ExtrOcamlZBigInt.
Require Import ExtrOcamlNatInt.

Set Extraction Optimize.
(* Enable all optimizations *)
Set Extraction Flag 2031.
Set Extraction Output Directory ".".

Extraction "coq_executable_sm.ml"
  all_steps memory_0 step
  state_fold zallocd_fold.
