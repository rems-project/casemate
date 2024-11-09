Require Import ZArith.
Require Import PeanoNat.
From stdpp Require Import gmap.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Require Export ModelHeader.
Require Import Transitions.
Require Import Blobs.
Require Import Machine.

Definition PTE_FIELD_INVALID_00 : u64.t := 0.
Definition PTE_FIELD_INVALID_10 : u64.t := 2.

Definition PTE_FIELD_LVL012_BLOCK : u64.t := 1.
Definition PTE_FIELD_LVL012_TABLE : u64.t := 3.

Definition PTE_FIELD_LVL3_PAGE : u64.t := 3.
Definition PTE_FIELD_LVL3_RESERVED : u64.t := 1.

Definition PTE_FIELD_OWNER_ID_LO : u64.t := 2.
Definition PTE_FIELD_PKVM_OWNER_ID_HOST : u64.t :=
  0 << PTE_FIELD_OWNER_ID_LO.
Definition PTE_FIELD_PKVM_OWNER_ID_HYP : u64.t :=
  1 << PTE_FIELD_OWNER_ID_LO.
Definition PTE_FIELD_PKVM_OWNER_ID_GUEST : u64.t :=
  2 << PTE_FIELD_OWNER_ID_LO.

Definition PTE_FIELD_UPPER_ATTRS_LO : u64.t := 59.
Definition PTE_FIELD_UPPER_ATTRS_MASK : u64.t := GENMASK 63 50.

Definition PTE_FIELD_LOWER_ATTRS_LO : u64.t := 2.
Definition PTE_FIELD_LOWER_ATTRS_MASK : u64.t := GENMASK 11 2.

Definition PTE_FIELD_ATTRS_MASK : u64.t := u64.or PTE_FIELD_UPPER_ATTRS_MASK PTE_FIELD_LOWER_ATTRS_MASK.

Definition PTE_FIELD_UPPER_ATTRS_SW_LO : u64.t := 55.
Definition PTE_FIELD_UPPER_ATTRS_SW_MASK : u64.t := GENMASK 58 55.

Definition PTE_FIELD_TABLE_UPPER_IGNORED_MASK : u64.t := GENMASK 58 51.
Definition PTE_FIELD_TABLE_IGNORED_MASK : u64.t :=
  u64.or PTE_FIELD_LOWER_ATTRS_MASK PTE_FIELD_TABLE_UPPER_IGNORED_MASK.

Definition PTE_FIELD_TABLE_NEXT_LEVEL_ADDR_MASK : u64.t := GENMASK 47 12.

Definition PTE_FIELD_S1_AP2_LO : u64.t := 7.
Definition PTE_FIELD_S1_AP2_MASK : u64.t := BIT 7.
Definition PTE_FIELD_S1_AP2_READ_ONLY : u64.t := 1.
Definition PTE_FIELD_S1_AP2_READ_WRITE : u64.t := 0.

Definition PTE_FIELD_S1_AP1_LO : u64.t := 6.
Definition PTE_FIELD_S1_AP1_MASK : u64.t := BIT 6.

Definition PTE_FIELD_S1_XN_LO : u64.t := 54.
Definition PTE_FIELD_S1_XN_MASK : u64.t := BIT 54.
Definition PTE_FIELD_S1_XN_NOT_EXEC_NEVER : u64.t := 0.
Definition PTE_FIELD_S1_XN_EXEC_NEVER : u64.t := 1.

Definition PTE_FIELD_S1_ATTRINDX_LO : u64.t := 2.
Definition PTE_FIELD_S1_ATTRINDX_MASK : u64.t := GENMASK 4 2.

Definition PTE_FIELD_S2_S2AP10_LO : u64.t := 6.
Definition PTE_FIELD_S2_S2AP10_MASK : u64.t := GENMASK 7 6.

Definition PTE_FIELD_S2_S2AP0_LO : u64.t := 6.
Definition PTE_FIELD_S2_S2AP0_MASK : u64.t := BIT 6.
Definition PTE_FIELD_S2_S2AP0_READABLE : u64.t := 1.
Definition PTE_FIELD_S2_S2AP0_NOT_READABLE : u64.t := 0.

Definition PTE_FIELD_S2_S2AP1_LO : u64.t := 7.
Definition PTE_FIELD_S2_S2AP1_MASK : u64.t := BIT 7.
Definition PTE_FIELD_S2_S2AP1_WRITEABLE : u64.t := 1.
Definition PTE_FIELD_S2_S2AP1_NOT_WRITEABLE : u64.t := 0.

Definition PTE_FIELD_S2_XN_LO : u64.t := 53.
Definition PTE_FIELD_S2_XN_MASK : u64.t := GENMASK 54 53.

Definition PTE_FIELD_S2_XN_NOT_EXEC_NEVER : u64.t := 0.
Definition PTE_FIELD_S2_XN_EXEC_NEVER : u64.t := 2.

Definition PTE_FIELD_S2_MEMATTR_LO : u64.t := 2.
Definition PTE_FIELD_S2_MEMATTR_MASK : u64.t := GENMASK 5 2.
Definition PTE_FIELD_S2_MEMATTR_DEVICE_nGnRE : u64.t := 2.
Definition PTE_FIELD_S2_MEMATTR_NORMAL_OUTER_INNER_WRITE_BACK_CACHEABLE : u64.t := 15. (* 0b1111 *)

Definition PTE_EXTRACT (mask lo val : u64.t) : u64.t :=
  (and val mask) >> lo.

(* Example functions using the extractor *)
Definition __s1_is_ro (pte : u64.t) : bool :=
  (PTE_EXTRACT PTE_FIELD_S1_AP2_MASK PTE_FIELD_S1_AP2_LO pte) u=? PTE_FIELD_S1_AP2_READ_ONLY.

Definition __s1_is_xn (pte : u64.t) : bool :=
  (PTE_EXTRACT PTE_FIELD_S1_XN_MASK PTE_FIELD_S1_XN_LO pte) u=?PTE_FIELD_S1_XN_EXEC_NEVER.

Definition __s2_is_r (pte : u64.t) : bool :=
  (PTE_EXTRACT PTE_FIELD_S2_S2AP0_MASK PTE_FIELD_S2_S2AP0_LO pte) u=? PTE_FIELD_S2_S2AP0_READABLE.

Definition __s2_is_w (pte : u64.t) : bool :=
  (PTE_EXTRACT PTE_FIELD_S2_S2AP1_MASK PTE_FIELD_S2_S2AP1_LO pte) u=? PTE_FIELD_S2_S2AP1_WRITEABLE.

Definition __s2_is_xn (pte : u64.t) : bool :=
  (PTE_EXTRACT PTE_FIELD_S2_XN_MASK PTE_FIELD_S2_XN_LO pte) u=? PTE_FIELD_S2_XN_EXEC_NEVER.

Definition __s2_is_x (pte : u64.t) : bool :=
  negb ((PTE_EXTRACT PTE_FIELD_S2_XN_MASK PTE_FIELD_S2_XN_LO pte) u=? PTE_FIELD_S2_XN_NOT_EXEC_NEVER).

Module Export GhostMair.
  Record t := {
    present : bool;
    attrs : list u8.t;
  }.
End GhostMair.

Definition mair_attr (mair : GhostMair.t) (attr_idx : nat) : u8.t := nth attr_idx mair.(attrs) u8.zeros.

Definition TCR_TG0_LO : u64.t := 14.
Definition TCR_TG0_WIDTH : u64.t := 2.
Definition TCR_TG0_MASK : u64.t := (GENMASK (u64.decr TCR_TG0_WIDTH) 0) << TCR_TG0_LO.

Definition TCR_EL2_T0SZ_LO : u64.t := 0.
Definition TCR_EL2_T0SZ_WIDTH : u64.t := 6.
Definition TCR_EL2_T0SZ_MASK := (GENMASK (u64.decr TCR_EL2_T0SZ_WIDTH) 0) << TCR_EL2_T0SZ_LO.

Definition MEMATTR_LEN := 8.
Definition MEMATTR_MASK := GENMASK 7 0.
Definition EXTRACT_MEMATTR (mair : u64.t) (idx : nat) : u8.t :=
  u8.of_u64 (and (mair >> ((u64.of_nat idx) u* 8)) (GENMASK 7 0)).
Definition MEMATTR_FIELD_DEVICE_nGnRE : u64.t := 4.
Definition MEMATTR_FIELD_NORMAL_OUTER_INNER_WRITE_BACK_CACHEABLE : u64.t := u64.decr (BIT 9).

Definition read_mair (mair : u64.t) : GhostMair.t :=
  {| present := true;
     attrs := map (EXTRACT_MEMATTR mair) (seq 0 8) |}.

Definition no_mair : GhostMair.t :=
  {| present := false; attrs := [] |}.

Definition GHOST_ATTR_MAX_LEVEL : u64.t := 3.

Record aal := {
  attr_at_level : list u64.t;
}.

Definition DUMMY_AAL : aal := {| attr_at_level := map u64.of_nat (repeat 0 4) |}.

Definition VTTBR_EL2_BADDR_MASK : u64.t := GENMASK 47 1.
Definition extract_s2_root (vttb : u64.t) : PAddr.t :=
  PAddr.intro (and vttb VTTBR_EL2_BADDR_MASK).

Definition TTBR0_EL2_BADDR_MASK : u64.t := GENMASK 47 1.
Definition extract_s1_root (ttb : u64.t) : PAddr.t :=
  PAddr.intro (and ttb TTBR0_EL2_BADDR_MASK).

(** Handle read_sysreg *)
Definition TCR_EL2 : u64.t :=
  or (u64.zeros << TCR_TG0_LO) ((64 - 48) << TCR_EL2_T0SZ_LO).

Definition VTCR_EL2 : u64.t :=
  or (u64.zeros << TCR_TG0_LO) ((64 - 48) << TCR_EL2_T0SZ_LO).

Definition MAIR_EL2 : u64.t := u64.zeros.

Definition read_sysreg (sysreg : GhostSysReg.t) : @ghost_model_result u64.t :=
  match sysreg with
  | SYSREG_VTCR_EL2 => ok VTCR_EL2
  | SYSREG_TCR_EL2 => ok TCR_EL2
  | SYSREG_MAIR_EL2 => ok MAIR_EL2
  | SYSREG_VTTBR => err (assertion_fail unsupported_sysreg_VTTBR)
  | SYSREG_TTBR_EL2 => err (assertion_fail unsupported_sysreg_TTBR_EL2)
  end.

Module Export PgtWalkResult. (* pgtable_walk_result *)
  Record t := mk_PWR {
    requested_pte : u64.t;
    found : bool;
    descriptor : option EED.t;
    root : u64.t;
    stage : EntryStage.t;
    level : Level.t;
  }.

  #[export]Instance eta_PWR : Settable _ :=
  settable! mk_PWR <
    requested_pte;
    found;
    descriptor;
    root;
    stage;
    level
  >.

  Program Definition initialise :=
  @mk_PWR
    zeros false None zeros ENTRY_STAGE_NONE LEVEL0.
End PgtWalkResult.

Module Export CallbackData.
  Inductive t :=
    | finder_cb_data (data : PgtWalkResult.t)
    | clean_reach_cb_data (data : bool)
    | dsb_visitor_cb_data (data : DxbKind.t)
    | tlbi_cb_data (data : TLBIOp.t)
    (* NOTE: below are considered null *)
    | empty_cb_data
  .
End CallbackData.

Module Export PgtTraverseCtxt. (* pgtable_traverse_context *)
  Record t := mk_PTC {
    (* unlike C, ptc_loc_phys is a physical address of the sm_location *)
    loc_phys : PAddr.t;
    descriptor : u64.t;
    level : Level.t;
    leaf : bool;
    exploded_descriptor : EED.t;
    root : u64.t;
    stage : EntryStage.t;
    data : CallbackData.t;
  }.

  #[export]Instance eta_PTC : Settable _ :=
    settable! mk_PTC <
      loc_phys;
      descriptor;
      level;
      leaf;
      exploded_descriptor;
      root;
      stage;
      data
    >.
End PgtTraverseCtxt.

Module Export PgtTraversalFlag. (* pgtable_traversal_flag *)
  Inductive t :=
    | READ_UNLOCKED_LOCATIONS
    | NO_READ_UNLOCKED_LOCATIONS.

  Definition eqb (flag1 flag2 : t) : bool :=
    match flag1, flag2 with
    | READ_UNLOCKED_LOCATIONS, READ_UNLOCKED_LOCATIONS => true
    | NO_READ_UNLOCKED_LOCATIONS, NO_READ_UNLOCKED_LOCATIONS => true
    | _, _ => false
    end.
End PgtTraversalFlag.

Definition get_location_without_ensure
  (cm : Machine.t)
  (loc_phys : PAddr.t) : @ghost_model_result Location.t :=
  let mem := get_memory_from_machine cm in
  blob <- find_blob mem loc_phys ?? err (bug ensured_blobs_not_found);
  match nth_opt blob.(MemoryBlob.slots) (SLOT_OFFSET_IN_BLOB loc_phys) with
  | Some loc => ok loc
  | None => err (bug index_out_of_bounds)
  end.
