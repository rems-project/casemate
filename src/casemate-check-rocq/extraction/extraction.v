Require Export casemate.main.
Require Import stdpp.bitvector.bitvector.
Require Import stdpp.bitvector.definitions.
Require Import stdpp.gmap.
Require Import Cmap.cmap.
Require Import Zmap.zmap.

Require Coq.extraction.Extraction.
Extraction Language OCaml.

Extract Inlined Constant bv64.BV64 => "".
Extract Inlined Constant Z_to_bv_checked => "(fun _ _ -> ())".

Extract Inlined Constant bv64.bv_add_64 => "Za.add64".
Extract Inlined Constant bv64.bv_mul_64 => "Za.mul64".
Extract Inlined Constant bv64.bv_mul_Z_64 => "Za.mul64".
Extract Inlined Constant bv64.bv_and_64 => "Za.and64".
Extract Inlined Constant bv64.bv_shiftr_64 => "Za.shr64".
Extract Inlined Constant bv64.bv_shiftl_64 => "Za.shl64".

Extract Constant cmap "'x" => "'x Cmap.t".
Extract Inlined Constant cmap_empty => "(Cmap.empty ())".
Extract Inlined Constant cmap_lookup => "Cmap.lookup".
Extract Inlined Constant cmap_insert => "Cmap.insert".


Extract Constant zmap "'x" => "'x Zmap.t". 
Extract Inlined Constant zmap_empty => "Zmap.empty".
Extract Inlined Constant zmap_lookup => "Zmap.find_opt".
Extract Inlined Constant zmap_insert => "Zmap.add".
Extract Inlined Constant zmap_delete => "Zmap.remove".


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
Extraction "rocq_casemate.ml" run_model cms_init step.
