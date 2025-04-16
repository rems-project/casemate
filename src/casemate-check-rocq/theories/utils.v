Require Export String Cmap.cmap Zmap.zmap stdpp.gmap.
Require Export stdpp.bitvector.bitvector.
From RecordUpdate Require Export RecordSet.
Export RecordSetNotations.
Require Export Recdef.

(* This is to prevent non-bools from being used as bools *)
Notation "'if' C 'then' A 'else' B" :=
  (match C with
    | true => A
    | false => B
  end)
(at level 200, right associativity).

(** Handling bitvectors *)
Module bv64.
  Import stdpp.bitvector.bitvector.
  Export stdpp.bitvector.definitions (bv).

  #[local] Definition _64 := 64%N.

  Definition BV64 (n : Z) {p : BvWf 64 n} : bv 64 := BV 64 n.

  #[global] Instance bv_64_eq_dec : EqDecision (bv 64) := @bv_eq_dec _64.
  #[global] Instance bv_64_countable : Countable (bv 64) := @bv_countable _64.

  Definition bv_add_64 := @bv_add _64.
  Definition bv_mul_64 := @bv_mul _64.
  Definition bv_mul_Z_64 := @bv_mul_Z _64.
  Definition bv_shiftr_64 := @bv_shiftr _64.
  Definition bv_shiftl_64 := @bv_shiftl _64.
  Definition bv_and_64 := @bv_and _64.
  Definition bv_not_64 := @bv_not _64.
  Definition bv_sub_64 := @bv_sub _64.

  Definition to_nat (n : bv 64) := Z.to_nat (bv_unsigned n).
  Definition to_Z (n : bv 64) := bv_unsigned n.

  Definition u64_eqb (x y : bv 64) : bool :=
    (bv_unsigned x =? bv_unsigned y)%Z .

  Definition u64_ltb (x y : bv 64) : bool :=
    ((bv_unsigned x) <? (bv_unsigned y))%Z .

  Definition u64_lte (x y : bv 64) : bool :=
    ((bv_unsigned x) <=? (bv_unsigned y))%Z .

  Declare Scope bv64_scope.
  Delimit Scope bv64_scope with bv64.

  Infix "b=?" := u64_eqb (at level 70) : bv64_scope.
  Infix "b<?" := u64_ltb (at level 70) : bv64_scope.
  Infix "b<=?" := u64_lte (at level 70) : bv64_scope.
  Infix "b+" := bv_add_64 (at level 50) : bv64_scope.
  Infix "b*" := bv_mul_64 (at level 40) : bv64_scope.
  Infix "`b*Z`" := bv_mul_Z_64 (at level 40) : bv64_scope.
  Infix "≫" := bv_shiftr_64 (at level 35) : bv64_scope.
  Infix "≪" := bv_shiftl_64 (at level 35) : bv64_scope.
End bv64.

Import bv64.
Export bv64.
Open Scope bv64_scope.

Infix "+s" := append (right associativity, at level 60).

Definition n512 := 512.
Definition z512 := 512%Z.

Definition u64 := bv 64.

Definition b0 := BV64 0.
Definition b1 := BV64 1.
Definition b2 := BV64 2.
Definition b3 := BV64 3.
Definition b4 := BV64 4.
Definition b7 := BV64 7.
Definition b8 := BV64 8.
Definition b12 := BV64 12.
Definition b16 := BV64 16.
Definition b47 := BV64 47.
Definition b63 := BV64 63.
Definition b512 := BV64 512.
Definition b1023 := BV64 1023.

(** Addresses **)

Inductive thread_identifier :=
| TID : u64 -> thread_identifier
.
Global Instance thread_identifier_eq_decision : EqDecision thread_identifier.
  Proof. solve_decision. Qed.

Definition thread_identifier_to_val (tid : thread_identifier) : u64 :=
  match tid with
  | TID val => val
  end.

Inductive phys_addr_t :=
| PA : u64 -> phys_addr_t
.

Global Instance phys_addr_t_eq_decision : EqDecision phys_addr_t.
  Proof. solve_decision. Qed.

Definition phys_addr_val (phys_addr : phys_addr_t) : u64 :=
  match phys_addr with
  | PA val => val
  end.

Definition pa_plus (a b : phys_addr_t) : phys_addr_t :=
  PA ((phys_addr_val a) b+ (phys_addr_val b))
.
Infix "pa+" := pa_plus (at level 50).
Definition pa_mul (a b : phys_addr_t) : phys_addr_t :=
  PA ((phys_addr_val a) b* (phys_addr_val b))
.
Infix "pa*" := pa_mul (at level 40).
Notation "<[ K := V ]> D" := (<[ bv_shiftr_64 (phys_addr_val K) b3 := V ]> D) (at level 100).
Definition pa0 := PA b0.

Inductive sm_owner_t :=
| Root : phys_addr_t -> sm_owner_t
.
Global Instance owner_t_eq_decision : EqDecision sm_owner_t.
  Proof. solve_decision. Qed.

Definition owner_val (root : sm_owner_t) : phys_addr_t :=
  match root with
  | Root r => r
  end
.

Inductive entry_stage_t :=
  | S1
  | S2
.

Inductive vmid_t :=
   | U64 : u64 -> vmid_t
 .

Inductive addr_id_t :=
  | AID : u64 -> addr_id_t
.

Global Instance addr_id_t_eq_decision : EqDecision addr_id_t.
  Proof. solve_decision. Qed.

Inductive result (A B: Type): Type :=
  | Ok (a: A)
  | Error (b: B)
.

Inductive log_element :=
  | Inconsistent_read : u64 -> u64 -> phys_addr_t -> log_element
  | Warning_read_write_non_allocd : phys_addr_t -> log_element
  | Warning_unsupported_TLBI
  | Log : string -> u64 -> log_element
.

Inductive internal_error_type :=
  | IET_infinite_loop
  | IET_unexpected_none
  | IET_no_write_authorization
.

Fixpoint idx_of {A : Type} (f : A -> bool) (acc : nat) (l : list A) {struct l} : nat :=
  match l with
  | nil => acc
  | x :: l' => if (f x) then acc else idx_of f (acc + 1) l'
  end.

Definition index_of {A : Type} (f : A -> bool) (l : list A) : nat :=
  idx_of f 0 l.