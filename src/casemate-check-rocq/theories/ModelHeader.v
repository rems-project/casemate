Require Import ZArith.
Require Import PeanoNat.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Require Export Asserts.
Require Export Types.

(* When u64 is used as an index *)
Fixpoint nth_opt {A} (l : list A) (idx : u64.t) : option A :=
  match l with
  | [] => None
  | hd :: tl =>
    if (idx u=? zeros) then Some hd
    else nth_opt tl (u64.decr idx)
  end.

Parameters MAX_CPU : nat.

(** PTE related states *)
Module LVS.
  Inductive t : Type :=
    | unguarded
    | dsbed
    | dsb_csed
  .

  Definition eqb (lvs1 lvs2 : t) : bool :=
    match lvs1, lvs2 with
    | unguarded, unguarded => true
    | dsbed, dsbed => true
    | dsb_csed, dsb_csed => true
    | _, _ => false
    end.
End LVS.

Module VState. (* aut_valid *)
  Record t := mk_VS {
    lvs : list LVS.t;
  }.

  Scheme Equality for list.

  Definition eqb (vs1 vs2 : t) : bool :=
    list_beq LVS.t LVS.eqb vs1.(lvs) vs2.(lvs).

  Program Definition initialise : t :=
    let init_lvs := map (fun _ => LVS.unguarded) (seq 0 MAX_CPU) in
    @mk_VS init_lvs.
End VState.

Module LIS.
  Inductive t : Type :=
    | unguarded
    | dsbed
    | dsb_tlbi_all
    | dsb_tlbi_ipa
    | dsb_tlbied
    | dsb_tlbi_ipa_dsb
  .

  Definition eqb (lis1 lis2 : t) : bool :=
    match lis1, lis2 with
    | unguarded, unguarded => true
    | dsbed, dsbed => true
    | dsb_tlbi_all, dsb_tlbi_all => true
    | dsb_tlbi_ipa, dsb_tlbi_ipa => true
    | dsb_tlbied, dsb_tlbied => true
    | dsb_tlbi_ipa_dsb, dsb_tlbi_ipa_dsb => true
    | _, _ => false
    end.
End LIS.

Module Export IUState. (* aut_invalid_unclean *)
  Record t := mk_IUS {
    invalidator_tid : TId.t;
    old_valid_desc : u64.t;
    lis : LIS.t;
  }.

  Definition eqb (ius1 ius2 : t) : bool :=
    TId.eqb ius1.(invalidator_tid) ius2.(invalidator_tid) &&
    u64.eqb ius1.(old_valid_desc) ius2.(old_valid_desc) &&
    LIS.eqb ius1.(lis) ius2.(lis).

  #[export] Instance eta_IUS : Settable _ :=
    settable! IUState.mk_IUS <IUState.invalidator_tid; IUState.old_valid_desc; IUState.lis>.
End IUState.

Module Export ICState. (* aut_invalid_clean *)
  Record t := mk_ICS {
    invalidator_tid : TId.t;
  }.

  Definition eqb (ics1 ics2 : t) : bool :=
    TId.eqb ics1.(invalidator_tid) ics2.(invalidator_tid).

  #[export] Instance eta_ICS : Settable _ :=
    settable! ICState.mk_ICS <ICState.invalidator_tid>.
End ICState.

Module PTEState. (* sm_pte_state *)
  Inductive t : Type :=
    | valid (valid_state : VState.t)
    | invalid_unclean (invalid_unclean_state : IUState.t)
    | invalid (invalid_clean_state : ICState.t)
    | not_writable.

  Definition eqb (s1 s2 : t) : bool :=
    match s1, s2 with
    | valid v1, valid v2 => VState.eqb v1 v2
    | invalid_unclean u1, invalid_unclean u2 => IUState.eqb u1 u2
    | invalid c1, invalid c2 => ICState.eqb c1 c2
    | not_writable, not_writable => true
    | _, _ => false
    end.
End PTEState.

Module Export EntryStage. (* EntryStage.t *)
  Inductive t : Type :=
    | ENTRY_STAGE2
    | ENTRY_STAGE1
    | ENTRY_STAGE_NONE
  .

  Definition eqb (e1 e2 : t) : bool :=
    match e1, e2 with
    | ENTRY_STAGE2, ENTRY_STAGE2 => true
    | ENTRY_STAGE1, ENTRY_STAGE1 => true
    | ENTRY_STAGE_NONE, ENTRY_STAGE_NONE => true
    | _, _ => false
    end.
End EntryStage.

Module Export EntryPermissions. (* entry_permissions_t *)
  Inductive t : Type :=
    | ENTRY_PERM_EMPTY
    | ENTRY_PERM_R
    | ENTRY_PERM_W
    | ENTRY_PERM_X
    | ENTRY_PERM_RW
    | ENTRY_PERM_RX
    | ENTRY_PERM_WX
    | ENTRY_PERM_RWX
    | ENTRY_PERM_UNKNOWN
  .

  Definition eqb (p1 p2 : t) : bool :=
    match p1, p2 with
    | ENTRY_PERM_EMPTY, ENTRY_PERM_EMPTY => true
    | ENTRY_PERM_R, ENTRY_PERM_R => true
    | ENTRY_PERM_W, ENTRY_PERM_W => true
    | ENTRY_PERM_X, ENTRY_PERM_X => true
    | ENTRY_PERM_RW, ENTRY_PERM_RW => true
    | ENTRY_PERM_RX, ENTRY_PERM_RX => true
    | ENTRY_PERM_WX, ENTRY_PERM_WX => true
    | ENTRY_PERM_RWX, ENTRY_PERM_RWX => true
    | ENTRY_PERM_UNKNOWN, ENTRY_PERM_UNKNOWN => true
    | _, _ => false
    end.

  Definition has_read (perms : t) : bool :=
    match perms with
    | ENTRY_PERM_R | ENTRY_PERM_RW | ENTRY_PERM_RX | ENTRY_PERM_RWX => true
    | _ => false
    end.

  Definition has_write (perms : t) : bool :=
    match perms with
    | ENTRY_PERM_W | ENTRY_PERM_RW | ENTRY_PERM_WX | ENTRY_PERM_RWX => true
    | _ => false
    end.

  Definition has_execute (perms : t) : bool :=
    match perms with
    | ENTRY_PERM_X | ENTRY_PERM_RX | ENTRY_PERM_WX | ENTRY_PERM_RWX => true
    | _ => false
    end.

  Definition perm_or (perms1 perms2 : t) : t :=
    match has_read perms1 || has_read perms2,
          has_write perms1 || has_write perms2,
          has_execute perms1 || has_execute perms2 with
    | true, false, false => ENTRY_PERM_R
    | false, true, false => ENTRY_PERM_W
    | false, false, true => ENTRY_PERM_X
    | true, true, false => ENTRY_PERM_RW
    | true, false, true => ENTRY_PERM_RX
    | false, true, true => ENTRY_PERM_WX
    | true, true, true => ENTRY_PERM_RWX
    | false, false, false => ENTRY_PERM_EMPTY
    end.
End EntryPermissions.

Module Export EntryMemTypeAttr. (* entry_memtype_attr *)
  Inductive t : Type :=
    | ENTRY_MEMTYPE_DEVICE
    | ENTRY_MEMTYPE_NORMAL_CACHEABLE
    | ENTRY_MEMTYPE_UNKNOWN
  .

  Definition eqb (a1 a2 : t) : bool :=
    match a1, a2 with
    | ENTRY_MEMTYPE_DEVICE, ENTRY_MEMTYPE_DEVICE => true
    | ENTRY_MEMTYPE_NORMAL_CACHEABLE, ENTRY_MEMTYPE_NORMAL_CACHEABLE => true
    | ENTRY_MEMTYPE_UNKNOWN, ENTRY_MEMTYPE_UNKNOWN => true
    | _, _ => false
    end.
End EntryMemTypeAttr.

Module Export EntryAttr. (* entry_attributes *)
  Record t := mk_EA {
    prot : EntryPermissions.t;
    memtype : EntryMemTypeAttr.t;
    raw_arch_attrs : u64.t;
  }.

  Definition eqb (attrs1 attrs2 : t) : bool :=
    EntryPermissions.eqb attrs1.(prot) attrs2.(prot) &&
    EntryMemTypeAttr.eqb attrs1.(memtype) attrs2.(memtype) &&
    u64.eqb attrs1.(raw_arch_attrs) attrs2.(raw_arch_attrs).
End EntryAttr.

Module PTE.
  Inductive t : Type :=
    | table (next_level_table_addr : u64.t)
      (* BLOCK, PAGE *)
    | map (oa_range : AddrRange.t) (attrs : EntryAttr.t)
    | invalid
  .

  Definition eqb (pte1 pte2 : t) : bool :=
    match pte1, pte2 with
    | table addr1, table addr2 => u64.eqb addr1 addr2
    | map range1 attrs1, map range2 attrs2 =>
        AddrRange.eqb range1 range2 && EntryAttr.eqb attrs1 attrs2
    | invalid, invalid => true
    | _, _ => false
    end.
End PTE.

(** exploded descriptor states *)
Module Export EED. (* entry_exploded_descriptor *)
  Record t := mk_EED {
    pte : PTE.t;
    ia_region : AddrRange.t;
    level : Level.t;
    stage : EntryStage.t;
  }.

  Definition eqb (eed1 eed2 : t) : bool :=
    PTE.eqb eed1.(pte) eed2.(pte) &&
    AddrRange.eqb eed1.(ia_region) eed2.(ia_region) &&
    Level.eqb eed1.(level) eed2.(level) &&
    EntryStage.eqb eed1.(stage) eed2.(stage).

  Definition is_invalid (eed : t) : bool :=
    match eed.(pte) with
    | PTE.invalid => true
    | _ => false
    end.

  Definition is_table (eed : t) : bool :=
    match eed.(pte) with
    | PTE.table _ => true
    | _ => false
    end.

  Definition is_leaf (eed : t) : bool :=
    negb (is_table eed).
End EED.

#[export] Instance eta_EED : Settable _ :=
  settable! EED.mk_EED <EED.pte; EED.ia_region; EED.level; EED.stage>.

(** sm_location related states *)
Module PTEInfo.
  Record t := mk_PTEI {
    descriptor : EED.t;
    state : PTEState.t;
  }.

  Definition eqb (pte_info1 pte_info2 : t) : bool :=
    EED.eqb pte_info1.(descriptor) pte_info2.(descriptor) &&
    PTEState.eqb pte_info1.(state) pte_info2.(state).

  Definition is_invalid_unclean (pte_info : t) : bool :=
    match pte_info.(state) with
    | PTEState.invalid_unclean _ => true
    | _ => false
    end.

  Definition is_valid (pte_info : t) : bool :=
    match pte_info.(state) with
    | PTEState.valid _ => true
    | _ => false
    end.
End PTEInfo.

#[export] Instance eta_PTEI : Settable _ :=
  settable! PTEInfo.mk_PTEI <PTEInfo.descriptor; PTEInfo.state>.


Module Export LocationInfo.
  Record t := mk_LI {
    val : u64.t;
    pte_info : option PTEInfo.t;
    owner : OwnerAddr.t;
  }.

  Definition eqb (info1 info2 : t) : bool :=
    u64.eqb info1.(val) info2.(val) &&
    match info1.(pte_info), info2.(pte_info) with
    | Some pte_info1, Some pte_info2 => PTEInfo.eqb pte_info1 pte_info2
    | None, None => true
    | _, _ => false
    end &&
    u64.eqb info1.(owner) info2.(owner).

  #[export] Instance eta_LI : Settable _ :=
    settable! LocationInfo.mk_LI <LocationInfo.val; LocationInfo.pte_info; LocationInfo.owner>.
End LocationInfo.


(** Note: In the C implementation, `struct sm_location` flattens
   all necessary information by incorporating conditional variables to verify the availability of inner data.
   Here, however, `Location.t` utilizes the option type to store `Some info` when the location is initialized
   and `Some pte_info` when the location represents an actual PTE.
   Also, "sm" is erased in the naming convention. *)

Module Location.
  Record t := mk_L {
    phys_addr : PAddr.t;
    thread_owner : option TId.t;
    info : option LocationInfo.t;
  }.

  Program Definition empty (phys : PAddr.t) : t :=
    mk_L phys None None.

  Definition eqb (loc1 loc2 : t) : bool :=
    PAddr.eqb loc1.(phys_addr) loc2.(phys_addr) &&
    match loc1.(info), loc2.(info) with
    | Some info1, Some info2 => LocationInfo.eqb info1 info2
    | None, None => true
    | _, _ => false
    end &&
    match loc1.(thread_owner), loc2.(thread_owner) with
    | Some owner1, Some owner2 => TId.eqb owner1 owner2
    | None, None => true
    | _, _ => false
    end.

  Definition get_ia_region (loc : t) : option AddrRange.t :=
    info <- loc.(info) ?? None;
    pte_info <- info.(LocationInfo.pte_info) ?? None;
    Some pte_info.(PTEInfo.descriptor).(EED.ia_region).
End Location.

#[export] Instance eta_L : Settable _ :=
  settable! Location.mk_L <Location.phys_addr; Location.thread_owner; Location.info>.


(** Ghost system registers *)
Module Export GhostSysReg. (* ghost_sysreg_kind *)
  Inductive t : Type :=
    | SYSREG_VTTBR
    | SYSREG_TTBR_EL2
    | SYSREG_VTCR_EL2
    | SYSREG_TCR_EL2
    | SYSREG_MAIR_EL2.

  Definition to_u64 (kind : t) : u64.t :=
    match kind with
    | SYSREG_VTTBR => 0
    | SYSREG_TTBR_EL2 => 1
    | SYSREG_VTCR_EL2 => 2
    | SYSREG_TCR_EL2 => 3
    | SYSREG_MAIR_EL2 => 4
    end.
  Coercion to_u64 : t >-> u64.t.
End GhostSysReg.

Definition SLOTS_PER_PAGE := 512.
Definition SLOT_SHIFT : u64.t := 3.
Definition BLOB_SHIFT : u64.t := 12.
Definition MAX_BLOBS := Z.to_nat 0x2000.
Definition MAX_ROOTS := 10.
Definition MAX_UNCLEAN_LOCATIONS := 10.

Definition BLOB_SIZE : u64.t := u64.shiftl 1 BLOB_SHIFT.
Definition BLOB_OFFSET_MASK : u64.t := GENMASK (u64.decr BLOB_SHIFT) 0.
Definition ALIGN_DOWN_TO_BLOB (x : u64.t) : u64.t := u64.and x (u64.not BLOB_OFFSET_MASK).
Definition OFFSET_IN_BLOB (x : u64.t) : u64.t := u64.and x BLOB_OFFSET_MASK.
Definition SLOT_OFFSET_IN_BLOB (x : u64.t) : u64.t := u64.shiftr (OFFSET_IN_BLOB x) SLOT_SHIFT.

(** Memory *)
Module MemoryBlob. (* casemate_memory_blob *)
  Record t := mk_MB {
    valid : bool;
    phys : u64.t;
    slots : list Location.t; (* this is where actual sm_location data is stored *)
  }.
  Scheme Equality for list.

  Definition eqb (blob1 blob2 : t) : bool :=
    Bool.eqb blob1.(valid) blob2.(valid) &&
    u64.eqb blob1.(phys) blob2.(phys) &&
    list_beq Location.t Location.eqb blob1.(slots) blob2.(slots).

  (* Coercion not working? *)
  Definition initialise (blob_phys : u64.t) :=
    let blob_slots := repeat (Location.empty (PAddr.intro blob_phys)) SLOTS_PER_PAGE in
    {| valid := true;
       phys := blob_phys;
       slots := blob_slots |}.
End MemoryBlob.

#[export] Instance eta_MB : Settable _ :=
  settable! MemoryBlob.mk_MB <MemoryBlob.valid; MemoryBlob.phys; MemoryBlob.slots>.


(* NOTE: while casemate_model_memory has a sorted list of
   a starting physical address of each blob and a list of pointers to blob,
   here, we have a map from a starting physical address to the actual blob record.
 *)
Module Memory. (* casemate_model_memory *)
  Record t := mk_MEM {
    blobs_backing : Map.t MemoryBlob.t;
  }.

  Definition empty : t :=
    {| blobs_backing := Map.empty MemoryBlob.t |}.

  Definition nr_allocated_blobs (mem : t) : nat :=
    size mem.(blobs_backing).
End Memory.

#[export] Instance eta_MEM : Settable _ :=
  settable! Memory.mk_MEM <Memory.blobs_backing>.


Module Export LocationSet. (* location_set *)
  (* NOTE: this will be a cache for Location.t *)
  Record t := mk_LS {
    locations : list PAddr.t; (* physical address of sm_location *)
  }.
  #[export] Instance eta_LS : Settable _ :=
    settable! mk_LS <locations>.

  Program Definition empty := mk_LS [].

  Definition len (ls : t) := length ls.(locations).

  Definition lookup (phys : PAddr.t) (ls : t) : bool :=
    existsb (PAddr.eqb phys) ls.(locations).

  Definition append (phys : PAddr.t) (ls : t) : t :=
    mk_LS (ls.(locations) ++ [phys]).

  Definition remove (phys : PAddr.t) (ls : t) : t :=
    mk_LS (filter (fun x => negb (PAddr.eqb x phys)) ls.(locations)).

End LocationSet.

Definition casemate_model_MAX_LOCKS := 8.

(** Locks *)
Module Export LockOwnerMap. (* lower_owner_map *)
  Record t := mk_LOM {
    locks : Map.t LockAddr.t;
  }.
  #[export] Instance eta_LOM : Settable _ :=
    settable! LockOwnerMap.mk_LOM <LockOwnerMap.locks>.

  Definition len (lo : t) : nat := size lo.(locks).

  Program Definition empty : t :=
    mk_LOM (Map.empty LockAddr.t).
End LockOwnerMap.


Module WriteAuth.
  Inductive t : Type :=
    | AUTHORIZED
    | UNAUTHORIZED_PLAIN
  .

  Definition eqb (wa1 wa2 : t) : bool :=
    match wa1, wa2 with
    | AUTHORIZED, AUTHORIZED => true
    | UNAUTHORIZED_PLAIN, UNAUTHORIZED_PLAIN => true
    | _, _ => false
    end.
End WriteAuth.

Module Export LockState. (* lock_state *)
  Record t := mk_LS {
    id : TId.t;
    write_authorization : WriteAuth.t;
  }.
  #[export] Instance eta_LS : Settable _ :=
    settable! mk_LS <id; write_authorization>.

  Definition eqb (ls1 ls2 : t) : bool :=
    TId.eqb ls1.(id) ls2.(id) &&
    WriteAuth.eqb ls1.(write_authorization) ls2.(write_authorization).
End LockState.

Module Export LockStateMap. (* lock_state_map *)
  Record t := mk_LSM {
    locker : Map.t LockState.t;
  }.
  #[export] Instance eta_LSM : Settable _ :=
    settable! mk_LSM <locker>.

  Definition len (lsm : t) : nat := size lsm.(locker).

  Program Definition empty : t :=
    mk_LSM (Map.empty LockState.t).
End LockStateMap.

(** Model State : consists of memory, lock information,
    and cache for unclean locations *)
Module Export ModelState. (* casemate_model_state *)
  Record t := mk_MS {
    base_addr : PAddr.t;
    size : u64.t;
    memory : Memory.t;
    unclean_locations : LocationSet.t;
    s1_roots : list PAddr.t;
    s2_roots : list PAddr.t;
    locks : LockOwnerMap.t;
    state : LockStateMap.t;
  }.
  Definition nr_s1_roots (state : t) :=
    length state.(s1_roots).
  Definition nr_s2_roots (state : t) :=
    length state.(s2_roots).

  #[export]Instance eta_MS : Settable _ :=
    settable! mk_MS <
      base_addr;
      size;
      memory;
      unclean_locations;
      s1_roots;
      s2_roots;
      locks;
      state>.

  Definition empty : t :=
    {| base_addr := PAddr.intro zeros;
       size := zeros;
       memory := Memory.empty;
       unclean_locations := LocationSet.empty;
       s1_roots := [];
       s2_roots := [];
       locks := LockOwnerMap.empty;
       state := LockStateMap.empty; |}.
End ModelState.


