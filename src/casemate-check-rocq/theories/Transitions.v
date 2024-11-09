Require Import String.
Require Import Coq.Classes.EquivDec.
From RecordUpdate Require Export RecordSet.
Import RecordSetNotations.

Require Export ModelHeader.

Inductive memory_order_t : Type := (* memory_order *)
  | WMO_plain
  | WMO_release
.

(** TLBI oeprations *)
(* NOTE: "sm" prefix has been removed *)
Inductive tlbi_op_method_kind : Type :=
  | TLBI_OP_BY_ALL        (* TLBI ALL* only *)
  | TLBI_OP_BY_INPUT_ADDR (* by Input-Address *)
  | TLBI_OP_BY_ADDR_SPACE (* by ASID/VMID *).

(* Define aliases for specific operations *)
Definition TLBI_OP_BY_VA := TLBI_OP_BY_INPUT_ADDR.
Definition TLBI_OP_BY_IPA := TLBI_OP_BY_INPUT_ADDR.
Definition TLBI_OP_BY_VMID := TLBI_OP_BY_ADDR_SPACE.
Definition TLBI_OP_BY_ASID := TLBI_OP_BY_ADDR_SPACE.

Inductive tlbi_op_stage :=
  | TLBI_OP_STAGE1
  | TLBI_OP_STAGE2
  | TLBI_OP_BOTH_STAGES (* = TLBI_OP_STAGE1 | TLBI_OP_STAGE2 *)
.
Inductive tlbi_op_method_data :=
  | tlbi_op_method_by_address_data
      (page : u64.t) (has_level_hint : bool)
      (level_hint : u64.t) (affects_last_level_only : bool)
  | tlbi_op_method_by_address_space_id_data (asid_or_vmid : u64.t)
.

Inductive tlbi_op_regime_kind :=
  | TLBI_REGIME_EL10 (* = 1, EL1&0 regime *)
  | TLBI_REGIME_EL2  (* = 2, EL2 regime *)
.

Module Export TLBIOpMethod. (* sm_tlbi_op_method *)
  Record t := mk_TOM {
    kind : tlbi_op_method_kind;
    data : tlbi_op_method_data;
  }.

  #[export]Instance eta_TOM : Settable _ := settable! mk_TOM <kind; data>.
End TLBIOpMethod.

Module Export TLBIOp. (* sm_tlbi_op_regime *)
  Record t := mk_TO {
    stage : tlbi_op_stage;
    regime : tlbi_op_regime_kind;
    method : TLBIOpMethod.t;
    shootdown : bool
  }.

  #[export]Instance eta_TO : Settable _ :=
    settable! mk_TO <stage; regime; method; shootdown>.
End TLBIOp.

Module Export TLBIKind. (* tlbi_kind *)
  Inductive t :=
    | TLBI_vmalls12e1
    | TLBI_vmalls12e1is
    | TLBI_vmalle1is
    | TLBI_alle1is
    | TLBI_vmalle1
    | TLBI_vale2is
    | TLBI_vae2is
    | TLBI_ipas2e1is
  .

  Definition eqb (t1 t2 : t) : bool :=
    match t1, t2 with
    | TLBI_vmalls12e1, TLBI_vmalls12e1 => true
    | TLBI_vmalls12e1is, TLBI_vmalls12e1is => true
    | TLBI_vmalle1is, TLBI_vmalle1is => true
    | TLBI_alle1is, TLBI_alle1is => true
    | TLBI_vmalle1, TLBI_vmalle1 => true
    | TLBI_vale2is, TLBI_vale2is => true
    | TLBI_vae2is, TLBI_vae2is => true
    | TLBI_ipas2e1is, TLBI_ipas2e1is => true
    | _, _ => false
    end.

End TLBIKind.

Module Export DxbKind. (* dxb_kind *)
  Inductive t :=
    | DxB_ish
    | DxB_ishst
    | DxB_nsh
  .

  Definition eqb (t1 t2 : t) : bool :=
    match t1, t2 with
    | DxB_ish, DxB_ish => true
    | DxB_ishst, DxB_ishst => true
    | DxB_nsh, DxB_nsh => true
    | _, _ => false
    end.
End DxbKind.

Module Export BarrierKind. (* barrier_kind *)
  Inductive t :=
    | BARRIER_DSB
    | BARRIER_ISB
  .
End BarrierKind.

(** Transition Step *)

Module TransWriteData. (* trans_write_data *)
  Record t := {
    mo : memory_order_t;
    phys_addr : PAddr.t;
    val : u64.t;
  }.
End TransWriteData.

Module TransReadData. (* trans_read_data *)
  Record t := {
    phys_addr : PAddr.t;
    val : u64.t;
  }.
End TransReadData.

Module TransBarrierData. (* trans_barrier_data *)
  Record t := {
    barrier_kind : BarrierKind.t;
    dxb_kind : DxbKind.t;
  }.
End TransBarrierData.

Module TransTlbiData. (* trans_tlbi_data *)
  Record t := {
    tlbi_kind : TLBIKind.t;
    page : u64.t;
    level : Level.t;
  }.
End TransTlbiData.

Module TransMsrData. (* trans_msr_data *)
  Record t := {
    sysreg : GhostSysReg.t;
    val : u64.t;
  }.
End TransMsrData.

Module TransInitData. (* trans_init_data *)
  Record t := {
    location : u64.t;
    size : u64.t;
  }.
End TransInitData.

Module TransLockData. (* trans_lock_data *)
  Record t := {
    address : u64.t;
  }.
End TransLockData.

Module TransMemsetData. (* trans_memset_data *)
  Record t := {
    address : u64.t;
    size : u64.t;
    value : u64.t;
  }.
End TransMemsetData.

Inductive ghost_hw_step :=
  | hw_mem_write (write_data : TransWriteData.t)
  | hw_mem_read (read_data : TransReadData.t)
  | hw_barrier (barrier_data : TransBarrierData.t)
  | hw_tlbi (tlbi_data : TransTlbiData.t)
  | hw_msr (msr_data : TransMsrData.t)
.

Inductive ghost_abs_step :=
  | ghost_abs_init (init_data : TransInitData.t)
  | ghost_abs_lock (lock_data : TransLockData.t)
  | ghost_abs_unlock (lock_data : TransLockData.t)
  | ghost_abs_memset (memset_data : TransMemsetData.t)
.

Inductive ghost_hint_step :=
  | ghost_hint_set_root_lock (location : u64.t) (value : u64.t)
  | ghost_hint_set_owner_root (location : u64.t) (value : u64.t)
  | ghost_hint_release_table (location : u64.t)
  | ghost_hint_set_pte_thread_owner (location : u64.t) (value : u64.t)
.

Module Export Step. (* casemate_model_step *)
  Inductive t : Type :=
    | trans_hw_step (hw_step : ghost_hw_step)
    | trans_abs_step (abs_step : ghost_abs_step)
    | trans_hint_step (hint_step: ghost_hint_step)
  .
End Step.

Module CodeLoc. (* src_loc *)
  Record t := mk_SL {
    file : string;
    func : string;
    lineno : nat;
  }.
End CodeLoc.

Module Export ModelStep. (* casemate_model_step *)
  Record t := mk_MS {
    src_loc : option CodeLoc.t;
    thread_identifier : TId.t;
    kind : Step.t;
    seq_id : nat;
  }.

  Definition is_on_write_transition (mstep : t) (p : u64.t) : bool :=
    match mstep.(kind) with
    | Step.trans_hw_step (hw_step) =>
        match hw_step with
        | hw_mem_write write_data => u64.eqb (TransWriteData.phys_addr write_data) p
        | _ => false
        end
    | _ => false
    end.

  #[export]Instance eta_MS : Settable _ := settable! mk_MS <src_loc; thread_identifier; kind; seq_id>.
End ModelStep.
