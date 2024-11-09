From stdpp Require Export bitvector.bitvector.
From stdpp Require Export gmap.

Require Export Asserts.

Module Export u64.
  #[local] Definition n64 := 64%N.

  Definition t := bv 64.

  Lemma bv_wrap_wf (z : Z) : BvWf 64 (bv_wrap 64 z).
  Proof.
    apply bv_wrap_wf.
  Qed.

  Definition wrap_Z (z : Z) : {w | BvWf 64 w} :=
    exist _ (bv_wrap 64 z) (bv_wrap_wf z).

  Definition of_Z (z : Z) : t :=
    let (w, _) := wrap_Z z in BV 64 w.
  Coercion of_Z : Z >-> t.

  Definition of_nat (n : nat) : t := of_Z (Z.of_nat n).
  Coercion of_nat : nat >-> t.

  Definition to_nat (x : t) : nat :=
    Z.to_nat x.(bv_unsigned).

  Instance eq_dec : EqDecision t := @bv_eq_dec n64.
  Instance countable : Countable t := @bv_countable n64.

  Definition add := @bv_add n64.
  Definition sub := @bv_sub n64.
  Definition mul := @bv_mul n64.
  Definition div := @bv_divu n64.
  Definition mulz := @bv_mul_Z n64.
  Definition shiftr := @bv_shiftr n64.
  Definition shiftl := @bv_shiftl n64.
  Definition and := @bv_and n64.
  Definition or := @bv_or n64.
  Definition not := @bv_not n64.
  Definition incr := @bv_add n64 1.
  Definition decr := @bv_sub n64 1.

  Definition eqb (x y : t) : bool :=
    (bv_unsigned x =? bv_unsigned y)%Z.

  Definition ltb (x y : t) : bool :=
    ((bv_unsigned x) <? (bv_unsigned y))%Z.

  Definition leb (x y : t) : bool :=
    ((bv_unsigned x) <=? (bv_unsigned y))%Z.

  Definition eq (x y : t) : Prop :=
    eqb x y = true.

  Definition lt (x y : t) : Prop :=
    ltb x y = true.

  Definition le (x y : t) : Prop :=
    leb x y.

  Definition zeros := of_Z 0.
  Definition ones := not zeros.
  Definition NULL := zeros.

  Declare Scope u64_scope.

  Infix "u+" := add (at level 50) : u64_scope.
  Infix "u*" := mul (at level 40) : u64_scope.
  Infix "`u*Z`" := mulz (at level 40) : u64_scope.
  Infix ">>" := shiftr (at level 35) : u64_scope.
  Infix "<<" := shiftl (at level 35) : u64_scope.
  Infix "u=?" := eqb (at level 70) : u64_scope.
  Infix "u<?" := ltb (at level 70) : u64_scope.
  Infix "u<=?" := leb (at level 70) : u64_scope.
End u64.

#[global] Open Scope u64_scope.

Definition sizeof_u64 : u64.t := 64.

Module Export u8.
  Definition t := bv 8.

  Definition of_u64 (v : u64.t) : t := bv_extract 0 8 v.
  Definition to_u64 (v : u8.t) : u64.t := bv_extract 0 64 v.
  Coercion u8.to_u64 : u8.t >-> u64.t.

  Definition zeros := of_u64 u64.zeros.
End u8.

Module Export Map.
  Definition t (A : Type) := gmap u64.t A.
  Definition empty (A : Type) : t A := gmap_empty (A:=A).

  Definition lookup {A} k (m : t A) : option A := m !! k.
  Definition insert {A} k v (m : t A) : t A := <[k := v]> m.
  Definition update {A} k v (m : t A) : t A := <[k := v]> m.
  Definition delete {A} k (m : t A) : t A := delete k m.

  Definition fold {A} {B} (f : A -> B -> B) (acc : B) := gmap_fold (K:=u64.t) (A:=A) B (fun _ => f) acc.

  Definition size {A} (m : t A) : nat := size m.
End Map.

Module Export TId. (* thread_identifier *)
  Definition t := nat.

  Definition eqb (t1 t2 :t) : bool :=
    Nat.eqb t1 t2.

  Definition to_nat (tid : t) : nat := tid.
  Coercion to_nat : t >-> nat.
End TId.

Module Export Level.
  Inductive t :=
    | LEVEL0
    | LEVEL1
    | LEVEL2
    | LEVEL3
  .

  Definition eqb (l1 l2 : t) : bool :=
    match l1, l2 with
    | LEVEL0, LEVEL0 => true
    | LEVEL1, LEVEL1 => true
    | LEVEL2, LEVEL2 => true
    | LEVEL3, LEVEL3 => true
    | _, _ => false
    end.

  Definition to_nat (l : t) : nat :=
    match l with
    | LEVEL0 => 0
    | LEVEL1 => 1
    | LEVEL2 => 2
    | LEVEL3 => 3
    end.
  Coercion to_nat : t >-> nat.

  Definition next_level (l : t) : @ghost_model_result t :=
    match l with
    | LEVEL0 => ok LEVEL1
    | LEVEL1 => ok LEVEL2
    | LEVEL2 => ok LEVEL3
    | LEVEL3 => err (bug exceeds_max_level)
    end.

  Definition of_u64 (bits : u64.t) : @ghost_model_result t :=
    if bits u=? 0 then ok LEVEL0
    else if bits u=? 1 then ok LEVEL1
    else if bits u=? 2 then ok LEVEL2
    else if bits u=? 3 then ok LEVEL3
    else err (bug exceeds_max_level).

  Definition to_u64 (l : t) : u64.t :=
    u64.of_nat (to_nat l).
End Level.

Module Export PAddr. (* phsy_addr_t *)
  Inductive t :=
    | intro : u64.t -> t.

  Definition eqb (phys1 phys2 : t) : bool :=
    match phys1, phys2 with
    | intro bits1, intro bits2 => u64.eqb bits1 bits2
    end.

  Definition to_u64 (phys : t) : u64.t :=
    match phys with
    | intro bits => bits
    end.
  Coercion to_u64 : t >-> u64.t.
End PAddr.

Module Export LockAddr. (* gsm_lock_addr_t *)
  Inductive t :=
    | intro : u64.t -> t.

  Definition eqb (laddr1 laddr2 : t) : bool :=
    match laddr1, laddr2 with
    | intro bits1, intro bits2 => u64.eqb bits1 bits2
    end.

  Definition to_u64 (laddr : t) : u64.t :=
    match laddr with
    | intro bits => bits
    end.
  Coercion to_u64 : t >-> u64.t.
End LockAddr.

Module Export OwnerAddr. (* sm_owner_t *)
  Inductive t :=
    | intro : u64.t -> t.

  Definition eqb (owner1 owner2 : t) : bool :=
    match owner1, owner2 with
    | intro bits1, intro bits2 => u64.eqb bits1 bits2
    end.

  Definition to_u64 (owner : t) : u64.t :=
    match owner with
    | intro bits => bits
    end.
  Coercion to_u64 : t >-> u64.t.
End OwnerAddr.

Module Export AddrRange. (* addr_range *)
  Record t := mk_AR {
    range_start : u64.t;
    range_size : u64.t;
  }.

  Definition eqb (ar1 ar2 : t) : bool :=
    u64.eqb ar1.(range_start) ar2.(range_start) &&
    u64.eqb ar1.(range_size) ar2.(range_size).
End AddrRange.


(** 0........0  1....1  0.....0
  * 63-h zeros  h....l  l zeros *)
Definition GENMASK (h l : u64.t) : u64.t :=
  (* h < l triggers UB *)
  u64.and
    (u64.ones << l)
    ((u64.ones >> (u64.sub 63 h))).

Definition BIT (n : nat) : u64.t := 2 ^ n.

Definition is_null (addr : u64.t) : bool :=
    u64.eqb addr zeros.
