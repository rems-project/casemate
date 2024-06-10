
Require Import stdpp.gmap.
Require Import stdpp.bitvector.bitvector.

Axiom zmap : Type -> Type.

Axiom zmap_empty : forall {A}, Empty (zmap A).
Existing Instance zmap_empty.

Axiom zmap_lookup : forall {A}, Lookup (bv 64) A (zmap A).
Existing Instance zmap_lookup.

Axiom zmap_insert : forall {A}, Insert (bv 64) A (zmap A).
Existing Instance zmap_insert.

Axiom zmap_delete : forall {A}, Delete (bv 64) (zmap A).
Existing Instance zmap_delete.

Axiom zmap_lookup_empty : forall {A} (a : bv 64), (∅ : zmap A) !! a = None.
