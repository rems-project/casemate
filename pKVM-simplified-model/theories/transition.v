Require Import String.
Require stdpp.bitvector.bitvector.
Require Import Cmap.cmap.
(* uses https://github.com/tchajed/coq-record-update *)
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.
Require Import stdpp.gmap.
Require Import Recdef.

Require Import state.

Import bv64.

(* Inductive SecurityState := SS_NonSecure | SS_Root | SS_Realm | SS_Secure. *)
Inductive Regime := Regime_EL3 | Regime_EL30 | Regime_EL2 | Regime_EL20 | Regime_EL10.
Inductive Shareability := Shareability_NSH | Shareability_ISH | Shareability_OSH.

(***************************************)
(* TLBI *)
Inductive TLBIOp :=
  | TLBIOp_DALL
  | TLBIOp_DASID
  | TLBIOp_DVA
  | TLBIOp_IALL
  | TLBIOp_IASID
  | TLBIOp_IVA
  | TLBIOp_ALL
  | TLBIOp_ASID
  | TLBIOp_IPAS2
  | TLBIOp_VAA
  | TLBIOp_VA
  | TLBIOp_VMALL
  | TLBIOp_VMALLS12
  | TLBIOp_RIPAS2
  | TLBIOp_RVAA
  | TLBIOp_RVA
  | TLBIOp_RPA
  | TLBIOp_PAALL
.

Inductive TLBILevel := TLBILevel_Any | TLBILevel_Last.

Record TLBIRecord  := {
    TLBIRecord_op : TLBIOp;
    (* TLBIRecord_from_aarch64 : bool; *)
    (* TLBIRecord_security : SecurityState; *)
    TLBIRecord_regime : Regime;
    (* TLBIRecord_vmid : bits 16; *)
    (* TLBIRecord_asid : bits 16; *)
    TLBIRecord_level : TLBILevel;
    (* TLBIRecord_attr : TLBIMemAttr; *)
    (* TLBIRecord_ipaspace : PASpace; *)
    TLBIRecord_address : phys_addr_t;
    (* TLBIRecord_end_address_name : u64; *)
    (* TLBIRecord_tg : bits 2; *)
}.


Record TLBI := {
  TLBI_rec : TLBIRecord;
  TLBI_shareability : Shareability;
}.

Inductive TLBI_stage_kind :=
  | TLBI_OP_stage1
  | TLBI_OP_stage2
  | TLBI_OP_both_stages
.

Record TLBI_op_by_addr_data := {
  TOBAD_page : phys_addr_t;
  TOBAD_last_level_only : TLBILevel;
}.

Inductive TLBI_method :=
  | TLBI_by_addr_space : phys_addr_t -> TLBI_method
  | TLBI_by_input_addr : TLBI_op_by_addr_data -> TLBI_method
  | TLBI_by_addr_all
.

Record TLBI_intermediate := {
  TI_stage : TLBI_stage_kind;
  TI_regime : Regime;
  TI_shootdown : bool;
  TI_method : TLBI_method;
}.

Definition decode_tlbi (td : TLBI) : option TLBI_intermediate :=
  let stage :=
    match td.(TLBI_rec).(TLBIRecord_op) with
      | TLBIOp_VA | TLBIOp_VMALL =>
          Some TLBI_OP_stage1
      | TLBIOp_IPAS2  => Some TLBI_OP_stage2
      | TLBIOp_VMALLS12 | TLBIOp_ALL => Some TLBI_OP_both_stages
      | _ => None
    end
  in
  let shootdown :=
    match td.(TLBI_shareability) with
      | Shareability_ISH => Some true
      | _ => Some true (* TODO: false *)
    end
  in
  let method :=
    match td.(TLBI_rec).(TLBIRecord_op) with
      | TLBIOp_VMALLS12 | TLBIOp_VMALL =>
        (* TODO: Some (TLBI_by_addr_space (Phys_addr Sth)) *)
        Some TLBI_by_addr_all
      | TLBIOp_VA | TLBIOp_IPAS2 =>
        Some (
          TLBI_by_input_addr
            {|
                TOBAD_page := (td.(TLBI_rec).(TLBIRecord_address));
                TOBAD_last_level_only := td.(TLBI_rec).(TLBIRecord_level);
            |}
        )
      | TLBIOp_ALL => Some TLBI_by_addr_all
      | _ => None
    end
  in
  match stage, shootdown, method with
    | Some stage, Some shootdown, Some method =>
      Some
      {|
        TI_stage := stage;
        TI_regime := td.(TLBI_rec).(TLBIRecord_regime);
        TI_shootdown := shootdown;
        TI_method := method;
      |}
    | _,_,_ => None
  end
.


(***************************************)
(* Barrier *)
Inductive MBReqDomain :=
  | MBReqDomain_Nonshareable
  | MBReqDomain_InnerShareable
  | MBReqDomain_OuterShareable
  | MBReqDomain_FullSystem
.

(* Inductive MBReqTypes :=
  | MBReqTypes_Reads
  | MBReqTypes_Writes
  | MBReqTypes_All
. *)

Record DxB  := {
  DxB_domain : MBReqDomain;
  (* DxB_types : MBReqTypes; *)
  (* DxB_nXS : bool; *)
}.

Inductive Barrier  :=
  | Barrier_DSB : DxB -> Barrier
  | Barrier_DMB : DxB -> Barrier
  | Barrier_ISB : unit -> Barrier
  | Barrier_SSBB : unit -> Barrier
  | Barrier_PSSBB : unit -> Barrier
  | Barrier_SB : unit -> Barrier
.

(* All those transitions will go in favor of ARM ISA description (except for hints) *)
Inductive write_memory_order :=
  | WMO_plain
  | WMO_page
  | WMO_release
.

Record trans_zalloc_data := {
    tzd_addr : phys_addr_t;
    tzd_size : u64;
}.

Record tlbi_op_method_by_address_space_id_data := {
  tombas_asid_or_vmid : u64;
}.

Inductive ghost_sysreg_kind :=
  | SYSREG_VTTBR
  | SYSREG_TTBR_EL2
.

Inductive ghost_hint_kind :=
  | GHOST_HINT_SET_ROOT_LOCK
  | GHOST_HINT_SET_OWNER_ROOT
  | GHOST_HINT_RELEASE
.

Record src_loc := {
  sl_file : string;
  sl_func : string;
  sl_lineno : nat;
}.

Record trans_write_data := {
  twd_mo : write_memory_order;
  twd_phys_addr : phys_addr_t;
  twd_val : u64;
}.

Record trans_read_data := {
  trd_phys_addr : phys_addr_t;
  trd_val : u64;
}.

Record trans_msr_data := {
  tmd_sysreg : ghost_sysreg_kind;
  tmd_val : u64;
}.

Record trans_hint_data := {
  thd_hint_kind : ghost_hint_kind;
  thd_location : phys_addr_t;
  thd_value : owner_t;
}.

Inductive lock_kind :=
  | LOCK
  | UNLOCK
.

Record trans_lock_data := {
  tld_kind : lock_kind;
  tld_addr : phys_addr_t;
}.

Inductive ghost_simplified_model_transition_data :=
  | GSMDT_TRANS_MEM_WRITE (write_data : trans_write_data)
  | GSMDT_TRANS_MEM_ZALLOC (zalloc_data : trans_zalloc_data)
  | GSMDT_TRANS_MEM_READ (read_data : trans_read_data)
  | GSMDT_TRANS_BARRIER (dsb_data : Barrier)
  | GSMDT_TRANS_TLBI (tlbi_data : TLBI)
  | GSMDT_TRANS_MSR (msr_data : trans_msr_data)
  | GSMDT_TRANS_HINT (hint_data : trans_hint_data)
  | GSMDT_TRANS_LOCK (lock_data : trans_lock_data)
.

Record ghost_simplified_model_transition := {
  gsmt_src_loc : option src_loc;
  gsmt_thread_identifier : thread_identifier;
  gsmt_data : ghost_simplified_model_transition_data;
  gsmt_id : nat;
}.

