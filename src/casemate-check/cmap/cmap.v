
Require Import stdpp.gmap.
Require Import stdpp.bitvector.bitvector.

Axiom cmap : Type -> Type.

Axiom cmap_empty : forall {A}, Empty (cmap A).
Existing Instance cmap_empty.

Axiom cmap_lookup : forall {A}, Lookup (bv 64) A (cmap A).
Existing Instance cmap_lookup.

Axiom cmap_insert : forall {A}, Insert (bv 64) A (cmap A).
Existing Instance cmap_insert.

Axiom cmap_delete : forall {A}, Delete (bv 64) (cmap A).
Existing Instance cmap_delete.

Axiom cmap_lookup_empty : forall {A} (a : bv 64), (∅ : cmap A) !! a = None.
