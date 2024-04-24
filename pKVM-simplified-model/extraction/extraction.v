
Require Import simplified.simplified.

Require Coq.extraction.Extraction.
Extraction Language OCaml.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNativeString.
Require Import ExtrOcamlZBigInt.
Require Import ExtrOcamlNatInt.


Extraction "extraction.ml" step.
