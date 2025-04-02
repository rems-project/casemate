Require Import String.
Require stdpp.bitvector.bitvector.
Require Import Cmap.cmap.
Require Import Zmap.zmap.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.
Require Import stdpp.gmap.
Require Import Recdef.

Require Import model.
Require Import pgtable.

(* Inductive SecurityState := SS_NonSecure | SS_Root | SS_Realm | SS_Secure. *)
Inductive Regime := 
  | Regime_EL3
  | Regime_EL30
  | Regime_EL2
  | Regime_EL20
  | Regime_EL10
.

Inductive Shareability := 
  | Shareability_NSH
  | Shareability_ISH 
  | Shareability_OSH
.

(** TLBI *)
(* Inductive TLBIOp :=
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
. *)

Inductive TLBILevel := TLBILevel_Any | TLBILevel_Last.

(* Record TLBIRecord  := {
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
}. *)

Inductive TLBI_stage_kind :=
  | TLBI_OP_stage1
  | TLBI_OP_stage2
  | TLBI_OP_both_stages
.

Record TLBI_op_by_addr_data := {
  TOBAD_page : phys_addr_t;
  TOBAD_level_hint : option u64;
  TOBAD_last_level_only : bool;
  TOBAD_asid : option addr_id_t;
}.

Inductive TLBI_method :=
  | TLBI_by_addr_space : phys_addr_t -> TLBI_method
  | TLBI_by_input_addr : TLBI_op_by_addr_data -> TLBI_method
  | TLBI_by_all
.

Record TLBI_intermediate := {
  TI_stage : TLBI_stage_kind;
  TI_regime : Regime;
  TI_shootdown : bool;
  TI_method : TLBI_method;
}.

Inductive tlbi_kind :=
  | TLBI_vmalls12e1
	| TLBI_vmalls12e1is
	| TLBI_vmalle1is
	| TLBI_alle1is
  | TLBI_vae2
	| TLBI_vmalle1
	| TLBI_vale2is
	| TLBI_vae2is
	| TLBI_ipas2e1is
.

Record trans_tlbi_data := {
  ttd_tlbi_kind : tlbi_kind;
  ttd_value : u64
}.

Definition decode_tlbi_stage (td : trans_tlbi_data) : TLBI_stage_kind :=
  match td.(ttd_tlbi_kind) with
  | TLBI_vmalls12e1 => TLBI_OP_both_stages
	| TLBI_vmalls12e1is => TLBI_OP_both_stages
	| TLBI_vmalle1is => TLBI_OP_stage1
	| TLBI_alle1is => TLBI_OP_stage1
  | TLBI_vae2 => TLBI_OP_stage1
	| TLBI_vmalle1 => TLBI_OP_stage1
	| TLBI_vale2is => TLBI_OP_stage1
	| TLBI_vae2is => TLBI_OP_stage1
	| TLBI_ipas2e1is => TLBI_OP_stage2
  end.

Definition decode_tlbi_regime (td : trans_tlbi_data) : Regime :=
  match td.(ttd_tlbi_kind) with
  | TLBI_vmalls12e1 => Regime_EL10
	| TLBI_vmalls12e1is => Regime_EL10
	| TLBI_vmalle1is => Regime_EL10
	| TLBI_alle1is => Regime_EL10
	| TLBI_vmalle1 => Regime_EL10
  | TLBI_vae2 => Regime_EL2
	| TLBI_vale2is => Regime_EL2
	| TLBI_vae2is => Regime_EL2
	| TLBI_ipas2e1is => Regime_EL10
  end.

Definition decode_tlbi_shootdown (td : trans_tlbi_data) : bool :=
  match td.(ttd_tlbi_kind) with
  | TLBI_vmalls12e1 => false
	| TLBI_vmalls12e1is => true
	| TLBI_vmalle1is => true
	| TLBI_alle1is => true
	| TLBI_vmalle1 => false
  | TLBI_vae2 => false (* TODO: missing kind in C *)
	| TLBI_vale2is => true
	| TLBI_vae2is => true
	| TLBI_ipas2e1is => true
  end.

Definition decoded_tlbi_has_asid (td : trans_tlbi_data) : option addr_id_t :=
  match td.(ttd_tlbi_kind) with
  | TLBI_vale2is
	| TLBI_vae2is => Some (AID (bv_and_64 td.(ttd_value) TLBI_ASID_MASK))
  | TLBI_vmalls12e1 => None
	| TLBI_vmalls12e1is => None
	| TLBI_vmalle1is => None
	| TLBI_alle1is => None
	| TLBI_vmalle1 => None
  | TLBI_vae2 => None
	| TLBI_ipas2e1is => None
  end.

Definition decode_tlbi_by_addr (td : trans_tlbi_data) : TLBI_op_by_addr_data :=
  let page := bv_and_64 td.(ttd_value) TLBI_PAGE_MASK in
  let last_level_only := 
    match td.(ttd_tlbi_kind) with
    | TLBI_vale2is => true
    | _ => false
    end in
  let level := bv_and_64 td.(ttd_value) TLBI_TTL_MASK in
  let level_hint := 
    if (level b<? b4) then None 
    else Some (bv_and_64 level b4) in

  {|
    TOBAD_page := PA page;
    TOBAD_last_level_only := last_level_only;
    TOBAD_level_hint := level_hint;
    TOBAD_asid := decoded_tlbi_has_asid td;
  |}.

Definition decode_tlbi_by_space_id (td : trans_tlbi_data) : phys_addr_t := PA b0.

Definition decode_tlbi_method (td : trans_tlbi_data) : TLBI_method :=
  match td.(ttd_tlbi_kind) with
  | TLBI_vmalls12e1
	| TLBI_vmalls12e1is
	| TLBI_vmalle1is
  | TLBI_vmalle1 => TLBI_by_input_addr (decode_tlbi_by_addr td)
  | TLBI_vale2is
  | TLBI_vae2
  | TLBI_vae2is
  | TLBI_ipas2e1is => TLBI_by_addr_space (decode_tlbi_by_space_id td)
	| TLBI_alle1is => TLBI_by_all
  end.

Definition decode_tlbi (td : trans_tlbi_data) : TLBI_intermediate :=
  let stage := decode_tlbi_stage td in
  let regime := decode_tlbi_regime td in
  let shootdown := decode_tlbi_shootdown td in
  let method := decode_tlbi_method td in
  
  {|
    TI_stage := stage;
    TI_regime := regime;
    TI_shootdown := shootdown;
    TI_method := method;
  |}.


(** Barrier *)
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

Record DxB := {
  DxB_domain : MBReqDomain;
  (* DxB_types : MBReqTypes; *)
  (* DxB_nXS : bool; *)
}.

Inductive Barrier :=
  | Barrier_DSB : DxB -> Barrier
  | Barrier_DMB : DxB -> Barrier
  | Barrier_ISB : unit -> Barrier
  (* Speculative barriers *)
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
  | GHOST_HINT_RELEASE_TABLE
  | GHOST_HINT_SET_PTE_THREAD_OWNER
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

Record trans_init_data := {
  tid_addr : phys_addr_t;
  tid_size : u64;
}.

Record trans_memset_data := {
  tmd_addr : phys_addr_t;
  tmd_size : u64;
  tmd_value : u64;
}.

Record trans_msr_data := {
  tmd_sysreg : ghost_sysreg_kind;
  tmd_val : u64;
}.

Record trans_hint_data := {
  thd_hint_kind : ghost_hint_kind;
  thd_location : phys_addr_t;
  thd_value : sm_owner_t;
}.

Record trans_lock_data := {
  tld_addr : phys_addr_t;
}.

Inductive casemate_model_step_data :=
  (* HW_step *)
  | CMSD_TRANS_HW_MEM_WRITE (write_data : trans_write_data)
  | CMSD_TRANS_HW_MEM_READ (read_data : trans_read_data)
  | CMSD_TRANS_HW_BARRIER (dsb_data : Barrier)
  | CMSD_TRANS_HW_TLBI (tlbi_data : trans_tlbi_data)
  | CMSD_TRANS_HW_MSR (msr_data : trans_msr_data)
  (* ABS_step *)
  | CMSD_TRANS_ABS_MEM_INIT (init_data : trans_init_data)
  | CMSD_TRANS_ABS_MEMSET (memset_data : trans_memset_data)
  | CMSD_TRANS_ABS_LOCK (lock_data : trans_lock_data)
  | CMSD_TRANS_ABS_UNLOCK (unlock_data : trans_lock_data)
  (* HINT_step *)
  | CMSD_TRANS_HINT (hint_data : trans_hint_data)
.

Record casemate_model_step := {
  cms_src_loc : option src_loc;
  cms_thread_identifier : thread_identifier;
  cms_data : casemate_model_step_data;
  cms_id : nat;
}.

(** Write *)

(* Visiting a page table fails with this visitor iff the visited part has an uninitialised or invalid unclean entry *)
Definition clean_reachable_cb (ctx : pgtable_traverse_context) : casemate_model_result :=
  match ctx.(ptc_loc) with
  | None => Merror (CME_uninitialised "clean_reachable" ctx.(ptc_addr))
  | Some location =>
    match location.(sl_pte) with
    | None => Mreturn ctx.(ptc_state)
    | Some descriptor =>
      match descriptor.(ged_state) with
      | SPS_STATE_PTE_INVALID_UNCLEAN _ =>
        Merror (CME_unclean_child ctx.(ptc_addr))
      | _ => Mreturn ctx.(ptc_state)
      end 
    end
  end.

Definition clean_reachable
  (map : table_data_t)
  (descriptor : ghost_exploded_descriptor)
  (cm : casemate_model_state):
  casemate_model_result :=
  traverse_pgt_from
    descriptor.(ged_owner)
    map.(next_level_table_addr)
    descriptor.(ged_ia_region).(range_start)
    (next_level descriptor.(ged_level))
    descriptor.(ged_stage)
    clean_reachable_cb
    cm
.

Definition step_write_table_mark_children
  (tid : thread_identifier)
  (wmo : write_memory_order)
  (loc : sm_location)
  (val : u64)
  (descriptor : ghost_exploded_descriptor)
  (visitor_cb : pgtable_traverse_context -> casemate_model_result)
  (cm : casemate_model_state) :
  casemate_model_result :=
  if is_desc_valid val then
    (* Tests if the page table is well formed *)
    match descriptor.(ged_pte_kind) with
    | PTER_PTE_KIND_TABLE map =>
      let st := clean_reachable map descriptor cm in
      let st := Mlog
        (Log "BBM: invalid clean->valid"%string (phys_addr_val loc.(sl_phys_addr))) st in
      Mupdate_state (traverse_pgt_from
                        descriptor.(ged_owner)
                        map.(next_level_table_addr)
                        descriptor.(ged_ia_region).(range_start)
                        (next_level descriptor.(ged_level))
                        descriptor.(ged_stage)
                        visitor_cb) st
    | _ => Mlog
          (Log "BBM: invalid clean->valid"%string (phys_addr_val loc.(sl_phys_addr))) (Mreturn cm)
    end
  else
    (* if the descriptor is invalid, do nothing *)
    Mreturn cm.

Definition step_write_on_invalid
  (tid : thread_identifier)
  (wmo : write_memory_order)
  (loc : sm_location)
  (val : u64)
  (cm : casemate_model_state) :
  casemate_model_result :=
  (* If the location is a PTE table, tests if its children are clean *)
  match loc.(sl_pte) with
    | None => (* This should not happen because if we write on invalid, we write on PTE *)
      Merror (CME_internal_error IET_unexpected_none)
    | Some descriptor =>
      let descriptor := deconstruct_pte
          tid
          descriptor.(ged_ia_region).(range_start)
          val descriptor.(ged_level)
          descriptor.(ged_owner)
          descriptor.(ged_stage) in
      let new_loc := loc <| sl_val := val |> <| sl_pte := Some descriptor |> in
      let new_cm := cm <| cms_memory := <[ loc.(sl_phys_addr) := new_loc ]> cm.(cms_memory) |> in
      step_write_table_mark_children tid wmo loc val descriptor (mark_cb tid) new_cm
    end.

Definition step_write_on_invalid_unclean
  (tid : thread_identifier)
  (wmo : write_memory_order)
  (loc : sm_location)
  (val : u64)
  (cm : casemate_model_state) :
  casemate_model_result :=
  (* Only invalid descriptor are allowed *)
  if is_desc_valid val then
    (Merror (CME_bbm_violation VT_valid_on_invalid_unclean loc.(sl_phys_addr)))
  else
    Mreturn (cm <|cms_memory := <[loc.(sl_phys_addr) := loc <|sl_val := val|> ]> cm.(cms_memory) |>)
.

Definition is_only_update_to_sw_bit (old new : u64) : bool :=
  (bv_and_64 old NOT_PTE_FIELD_UPPER_ATTRS_SW_MASK) b=? (bv_and_64 new NOT_PTE_FIELD_UPPER_ATTRS_SW_MASK)
.

Definition require_bbm
  (tid : thread_identifier)
  (loc : sm_location)
  (val : u64) :
  option bool :=
  match loc.(sl_pte) with
  | None => None (* PTE cannot be valid if it is not a PTE *)
  | Some old_descriptor =>
    let new_descriptor := deconstruct_pte tid old_descriptor.(ged_ia_region).(range_start) val old_descriptor.(ged_level) old_descriptor.(ged_owner) old_descriptor.(ged_stage) in
    match old_descriptor.(ged_pte_kind), new_descriptor.(ged_pte_kind) with
    | PTER_PTE_KIND_INVALID, _ | _, PTER_PTE_KIND_INVALID => Some false
    | PTER_PTE_KIND_TABLE _, _ | _, PTER_PTE_KIND_TABLE _ => Some true
    | PTER_PTE_KIND_MAP r1, PTER_PTE_KIND_MAP r2 =>
      if negb (phys_addr_val r1.(oa_region).(range_size) b=? phys_addr_val r2.(oa_region).(range_size)) then
        Some true
      else
        Some (negb (is_only_update_to_sw_bit loc.(sl_val) val))
    end
  end
.

Definition step_write_valid_on_valid
  (tid : thread_identifier)
  (wmo : write_memory_order)
  (loc : sm_location)
  (val : u64)
  (cm : casemate_model_state) :
  casemate_model_result :=
  match require_bbm tid loc val with (* If no change in memory: no problem*)
  | None => Merror (CME_internal_error IET_unexpected_none)
  | Some false =>
      (* if the location des not require BBM, then we can update the value and the descriptor *)
      match loc.(sl_pte) with
      | None => (* This does not make sense because function is called on a pgt *)
        Merror (CME_internal_error IET_unexpected_none)
      | Some pte =>
        let new_pte := deconstruct_pte tid pte.(ged_ia_region).(range_start) val pte.(ged_level) pte.(ged_owner) pte.(ged_stage) in
        let loc := loc <| sl_val := val |> <| sl_pte := Some new_pte |> in
        Mreturn (insert_location loc cm)
      end
  | Some true =>
    (* Changing the descriptor is illegal *)
    Merror (CME_bbm_violation VT_valid_on_valid loc.(sl_phys_addr))
  end
.

Definition step_write_invalid_on_valid
  (tid : thread_identifier)
  (wmo : write_memory_order)
  (loc : sm_location)
  (val : u64)
  (cm : casemate_model_state) :
  casemate_model_result :=
  (* Invalidation of pgt: changing the state to invalid unclean unguarded *)
  let old := loc.(sl_val) in
  match loc.(sl_pte) with
  | None => (* This does not make sense because function is called on a pgt *)
      Merror (CME_internal_error IET_unexpected_none)
  | Some descriptor =>
    let new_desc := descriptor <| ged_state := (SPS_STATE_PTE_INVALID_UNCLEAN {| ai_invalidator_tid := tid; ai_old_valid_desc :=  old; ai_lis := LIS_unguarded; |}) |> in
    let cm := (cm <| cms_memory := (<[ loc.(sl_phys_addr) := loc <|sl_pte := Some (new_desc)|> <| sl_val := val |> ]> cm.(cms_memory))|> ) in
    Mlog (Log "BBM: valid->invalid_unclean"%string (phys_addr_val loc.(sl_phys_addr)))
    match descriptor.(ged_pte_kind) with
    | PTER_PTE_KIND_TABLE map =>
      let res := clean_reachable map descriptor cm in
      let res := Mlog (Log "invalidating a table descriptor"%string (phys_addr_val loc.(sl_phys_addr))) res in
      (* If it is well formed, mark its children as page tables, otherwise, return the same error *)
      Mupdate_state (step_write_table_mark_children tid wmo loc val descriptor (mark_not_writable_cb tid)) res
    | _ => Mreturn cm
    end
  end
.

Definition step_write_on_valid
  (tid : thread_identifier)
  (wmo : write_memory_order)
  (loc : sm_location)
  (val : u64)
  (cm : casemate_model_state) :
  casemate_model_result :=
  if is_desc_valid val
    then step_write_valid_on_valid tid wmo loc val cm
  else
    step_write_invalid_on_valid tid wmo loc val cm
.

Definition is_valid_state (st: sm_pte_state) : bool :=
  match st with
  | SPS_STATE_PTE_VALID _ => true
  | _ => false
  end
.

Definition drop_write_authorization_of_lock
  (cpu : thread_identifier)
  (addr : phys_addr_t)
  (wmo : write_memory_order)
  (descriptor : u64)
  (pte : ghost_exploded_descriptor)
  (cm : casemate_model_state) : casemate_model_result :=
  match get_lock_of_owner pte.(ged_owner) cm with
  | None => Mreturn cm
  | Some addr_lock =>
    match lookup addr_lock cm.(cms_lock_state) with
    | Some {| ls_tid := lock_owner; ls_write_authorization := auth |} =>
      if bool_decide (lock_owner = cpu) then
        match wmo with
        | WMO_page | WMO_plain => (* check that the write is authorized, and then drop the authorization *)
          match auth with
          | WA_AUTHORIZED => 
            let new_lock_state := {| ls_tid := lock_owner; ls_write_authorization := WA_UNAUTHORIZED |} in
            Mreturn (cm <| cms_lock_state := insert addr_lock new_lock_state cm.(cms_lock_state)|>)
          | WA_UNAUTHORIZED =>
            if (is_desc_valid descriptor) || is_valid_state pte.(ged_state) then
              Merror (CME_write_without_authorization addr)
            else
              let new_lock_state := {| ls_tid := lock_owner; ls_write_authorization := WA_UNAUTHORIZED |} in
              Mreturn (cm <| cms_lock_state := insert addr_lock new_lock_state cm.(cms_lock_state)|>)
          end
        | WMO_release => (* drop the authorization *)
          let new_lock_state := {| ls_tid := lock_owner; ls_write_authorization := WA_UNAUTHORIZED |} in
          Mreturn (cm <| cms_lock_state := insert addr_lock new_lock_state cm.(cms_lock_state)|>)
        end
      else
        Merror (CME_transition_without_lock addr)
    | None => Merror (CME_transition_without_lock addr)
    end
  end.

Definition drop_write_authorization
  (tid : thread_identifier)
  (wd : trans_write_data)
  (cm : casemate_model_state) :
  casemate_model_result :=
  let wmo := wd.(twd_mo) in
  let val := wd.(twd_val) in
  let addr := wd.(twd_phys_addr) in
  if negb ((bv_and_64 (phys_addr_val addr) b7) b=? b0)
    then Merror CME_unaligned_write
  else
    match cm !! addr with
    | None => Mreturn cm
    | Some location =>
        match location.(sl_pte) with
        | None => Mreturn cm
        | Some pte =>
          if is_loc_thread_owned tid location cm then
            Mreturn cm
          else
            drop_write_authorization_of_lock tid addr wmo val pte cm
        end
    end
.

Definition step_write_aux
  (tid : thread_identifier)
  (wd : trans_write_data)
  (cm : casemate_model_state) : casemate_model_result :=
  let wmo := wd.(twd_mo) in
  let val := wd.(twd_val) in
  let addr := wd.(twd_phys_addr) in
  if negb ((bv_and_64 (phys_addr_val addr) b7) b=? b0)
    then Merror CME_unaligned_write else
  let new_st := drop_write_authorization tid wd cm in
  let write_update s :=
    match s !! addr with
    | Some (loc) =>
      match loc.(sl_pte) with
      | Some desc =>
        (* If we write to a page table, depending on its state, we update them  *)
        match desc.(ged_state) with
        | SPS_STATE_PTE_VALID av =>
            (step_write_on_valid tid wmo loc val s)
        | SPS_STATE_PTE_INVALID_CLEAN av =>
            (step_write_on_invalid tid wmo loc val s)
        | SPS_STATE_PTE_INVALID_UNCLEAN av =>
            (step_write_on_invalid_unclean tid wmo loc val s)
        | SPS_STATE_PTE_NOT_WRITABLE =>
            (Merror (CME_write_on_not_writable addr))
        end
      | None => (* If it is not a pte, we just update the value *)
        let new_loc := loc <| sl_val := val |> in
        {|
          cmr_log := nil;
          cmr_data :=
            Ok _ _ (
              s <| cms_memory := <[ addr := new_loc ]> s.(cms_memory) |>
            );
        |}
      end
    | None =>
      (* If the location has not been written to, it is not a pgt, just save its value *)
        let new_st := s <| cms_memory :=
            <[ addr := {|
                sl_phys_addr := addr;
                sl_val := val;
                sl_pte := None;
                sl_thread_owner := None;
              |}
            ]> s.(cms_memory) |> in
                Mreturn new_st
          end
  in
  Mupdate_state write_update new_st
.

Function step_write_page
  (tid : thread_identifier)
  (wd : trans_write_data)
  (res : casemate_model_result)
  (offs : Z) {measure Z.abs_nat offs} :
  casemate_model_result :=
  if Zle_bool offs 0 then
    res
  else
    let addr := wd.(twd_phys_addr) pa+ (PA (bv_mul_Z_64 b8 (offs - 1))) in
    let sub_wd :=
      {|
        twd_mo := WMO_plain;
        twd_phys_addr := addr;
        twd_val := wd.(twd_val);
      |}
    in
    let res := Mupdate_state (step_write_aux tid sub_wd) res in
    step_write_page tid wd res (offs - 1).
Proof. lia. Qed.

Definition step_write
  (tid : thread_identifier)
  (wd : trans_write_data)
  (cm : casemate_model_state) : casemate_model_result :=
  match wd.(twd_mo) with
  | WMO_plain | WMO_release => step_write_aux tid wd cm
  | WMO_page => step_write_page tid wd (Mreturn cm) z512
  end.

(** Mem init *)

Definition step_init_aux
  (addr : phys_addr_t)
  (st : casemate_model_result) :
  casemate_model_result :=
  let update s := {| cmr_log := nil; cmr_data := Ok _ _ (s <| cms_initialised := <[ addr := () ]> s.(cms_initialised) |>) |} in
  Mupdate_state update st.

Definition _step_init_step_size := PA (bv_shiftl_64 b1 b3).

Fixpoint step_init_all
  (addr : phys_addr_t)
  (st : casemate_model_result)
  (offs : phys_addr_t)
  (max : nat) :
  casemate_model_result :=
  match max with
  | O => st
  | S max =>
    let st := step_init_aux (addr pa+ offs) st in
    step_init_all addr st (offs pa+ (_step_init_step_size)) max
  end.

Definition step_init
  (init_data : trans_init_data)
  (cm : casemate_model_state) :
  casemate_model_result :=
  step_init_all (PA (bv_shiftr_64 (phys_addr_val init_data.(tid_addr)) (bv64.BV64 9))) {|cmr_log := nil; cmr_data := Ok _ _ cm|} pa0 (to_nat init_data.(tid_size)).

Definition step_memset
  (tid : thread_identifier)
  (memset_data : trans_memset_data)
  (cm : casemate_model_state) : casemate_model_result :=
  let write_data := {|
    twd_mo := WMO_plain;
    twd_phys_addr := memset_data.(tmd_addr);
    twd_val := memset_data.(tmd_value);
  |} in
  (* memset is a plain write *)
  step_write_page tid write_data (Mreturn cm) (bv64.to_Z (bv_shiftr_64 memset_data.(tmd_size) b3)).

(** Read *)

Definition step_read
  (tid : thread_identifier)
  (rd : trans_read_data)
  (cm : casemate_model_state) :
  casemate_model_result :=
  (* Test if the memory has been initialised (it might refuse acceptable executions, not sure if it is a good idea) and its content is consistent. *)
  match cm !! rd.(trd_phys_addr) with
  | Some loc =>
      if loc.(sl_val) b=? rd.(trd_val) then
        Mreturn cm
      else
        let new_loc := loc <| sl_val := rd.(trd_val) |> in
        {| cmr_log :=
            [Inconsistent_read loc.(sl_val) rd.(trd_val) rd.(trd_phys_addr)];
           cmr_data := (Ok _ _ (cm <| cms_memory := <[rd.(trd_phys_addr) := new_loc ]> cm.(cms_memory) |>)) |}
  | None =>
      let loc := {| sl_phys_addr := rd.(trd_phys_addr); sl_val := rd.(trd_val); sl_pte := None; sl_thread_owner := Some tid |} in
      let st := cm <| cms_memory := <[ rd.(trd_phys_addr) := loc ]> cm.(cms_memory) |> in
      {| cmr_log :=
          [Warning_read_write_non_allocd loc.(sl_phys_addr)];
         cmr_data := Ok _ _ st
      |}
  end.

(** DSB *)

Definition dsb_invalid_unclean_unmark_children
  (cpu_id : thread_identifier)
  (loc : sm_location)
  (lis : aut_invalid_unclean)
  (ptc : pgtable_traverse_context) :
  casemate_model_result :=
  let st := ptc.(ptc_state) in
  let desc := (* This uses the old descriptor to rebuild a fresh old descriptor *)
    deconstruct_pte cpu_id ptc.(ptc_partial_ia) lis.(ai_old_valid_desc) ptc.(ptc_level) ptc.(ptc_root) ptc.(ptc_stage)
  in
  match desc.(ged_pte_kind) with
  | PTER_PTE_KIND_TABLE map =>
    (* The children are clean, and not writable, otherwise, it would catch fire *)
    traverse_pgt_from desc.(ged_owner) map.(next_level_table_addr) desc.(ged_ia_region).(range_start) (next_level desc.(ged_level)) desc.(ged_stage) (unmark_cb cpu_id) st
  | _ => {| cmr_log  := nil; cmr_data := Ok _ _ st |}
  end.


Definition new_pte_after_dsb
  (cpu_id : thread_identifier)
  (pte : ghost_exploded_descriptor)
  (kind : DxB) : ghost_exploded_descriptor :=
  match pte.(ged_state) with
  | SPS_STATE_PTE_INVALID_UNCLEAN sst =>
    (* DSB has an effect on invalid unclean state only *)
    if negb (bool_decide (sst.(ai_invalidator_tid) = cpu_id)) then
      pte (* If it is another CPU that did the invalidation, do noting*)
    else
      (* Otherwise, update the state invalid unclean sub-automaton *)
      match sst.(ai_lis) with
      | LIS_unguarded =>
        pte <|ged_state := SPS_STATE_PTE_INVALID_UNCLEAN (sst <| ai_lis := LIS_dsbed |>) |>
      | LIS_dsbed => pte
      | LIS_dsb_tlbied =>
        match kind.(DxB_domain) with
        | MBReqDomain_InnerShareable | MBReqDomain_FullSystem =>
          pte <| ged_state := SPS_STATE_PTE_INVALID_CLEAN {| aic_invalidator_tid := sst.(ai_invalidator_tid) |} |>
              <| ged_pte_kind := PTER_PTE_KIND_INVALID |>
        | _ => pte
        end
      | LIS_dsb_tlbi_ipa =>
          match kind.(DxB_domain) with
          | MBReqDomain_InnerShareable | MBReqDomain_FullSystem =>
            pte <|ged_state := SPS_STATE_PTE_INVALID_UNCLEAN (sst <|ai_lis := LIS_dsb_tlbi_ipa_dsb |>) |>
          | _ => pte
          end
      | _ => pte
      end
  | _ => pte (* If not invalid unclean, then do nothing *)
  end.

Definition dsb_visitor
  (kind : DxB)
  (cpu_id : thread_identifier)
  (ctx : pgtable_traverse_context) :
  casemate_model_result :=
  match ctx.(ptc_loc) with
  | None => (* This case is not explicitly excluded by the C code, but we cannot do anything in this case. *)
    Merror (CME_uninitialised "dsb_visitor"%string ctx.(ptc_addr))
  | Some location =>
    match location.(sl_pte) with
    | None => Merror (CME_not_a_pte "dsb_visitor" ctx.(ptc_addr))
    | Some pte =>
      let new_pte := new_pte_after_dsb cpu_id pte kind in
      (* then update state and return *)
      let new_loc := (location <| sl_pte := Some new_pte |>) in
      let new_state := ctx.(ptc_state) <| cms_memory := <[ location.(sl_phys_addr) := new_loc ]> ctx.(ptc_state).(cms_memory) |> in
      let log :=
        match pte.(ged_state), new_pte.(ged_state) with
        | SPS_STATE_PTE_INVALID_UNCLEAN _ , SPS_STATE_PTE_INVALID_CLEAN _ =>
          Some (Log "BBM: invalid_unclean->invalid_clean"%string (phys_addr_val location.(sl_phys_addr)))
        | SPS_STATE_PTE_INVALID_UNCLEAN {| ai_lis := LIS_unguarded|} , SPS_STATE_PTE_INVALID_UNCLEAN {| ai_lis := _|} =>
          Some (Log "BBM: unguareded->dsbed"%string (phys_addr_val location.(sl_phys_addr)))
        | SPS_STATE_PTE_INVALID_UNCLEAN {| ai_lis := LIS_dsb_tlbi_ipa|} , SPS_STATE_PTE_INVALID_UNCLEAN {| ai_lis := _|} =>
          Some (Log "BBM: tlbied_ipa->tlbied_ipa_dsbed"%string (phys_addr_val location.(sl_phys_addr)))
        | _, _ => None
        end
      in
      let new_state :=
        match pte.(ged_state), new_pte.(ged_state) with
        | SPS_STATE_PTE_INVALID_UNCLEAN lis , SPS_STATE_PTE_INVALID_CLEAN _ =>
          dsb_invalid_unclean_unmark_children cpu_id new_loc lis
              (ctx <| ptc_state := new_state |> <|ptc_loc := Some new_loc|>)
        | _, _ => Mreturn new_state
        end
      in
      match log with
      | Some txt => Mlog txt new_state
      | None => new_state
      end
    end
  end.

Fixpoint reset_write_authorizations_aux
  (tid : thread_identifier)
  (roots: list cm_root)
  (cm : casemate_model_state) :
  casemate_model_state :=
  match roots with
  | [] => cm
  | {| r_baddr := baddr; r_id := _; r_refcount := _ |} :: q =>
    match lookup (phys_addr_val (root_val baddr)) cm.(cms_lock_addr) with
    | Some lock_addr =>
      let new_st :=
        match lookup lock_addr cm.(cms_lock_state) with
        | None => cm
        | Some {| ls_tid := thread; ls_write_authorization := _ |} =>
          if bool_decide (thread = tid) then
            let new_lock_state := {| ls_tid := tid; ls_write_authorization := WA_AUTHORIZED |} in
            (cm <| cms_lock_state :=
                insert lock_addr new_lock_state cm.(cms_lock_state) |>)
          else
            cm
        end
      in
      reset_write_authorizations_aux tid q new_st
    | None => reset_write_authorizations_aux tid q cm
    end
  end.


Definition reset_write_authorizations 
  (tid : thread_identifier)
  (cm : casemate_model_state) : casemate_model_state :=
  (* Reset the authorizations for both states *)
  reset_write_authorizations_aux tid cm.(cms_roots).(cmr_s2)
    (reset_write_authorizations_aux tid cm.(cms_roots).(cmr_s1) cm).

Definition step_dsb (tid : thread_identifier) (dk : DxB) (cm : casemate_model_state) : casemate_model_result :=
  (* There is enough barrier now to write plain again *)
  let st := reset_write_authorizations tid cm in
  (* walk the pgt with dsb_visitor*)
  traverse_all_pgt (Some tid) st (dsb_visitor dk tid).

(** TLBI *)

Definition is_leaf (kind : pte_rec) : bool :=
  match kind with
  | PTER_PTE_KIND_TABLE _ => false
  | _ => true
  end.

Definition __get_tlbi_asid (td : TLBI_intermediate) : option addr_id_t :=
  match td.(TI_method) with
  | TLBI_by_input_addr d => d.(TOBAD_asid)
  | TLBI_by_addr_space (PA addr_id) => Some (AID addr_id)
  | _ => None
  end.

Fixpoint all_children_invalid_iter
  (idx : u64)
  (n_children : nat)
  (table_start : phys_addr_t)
  (cm : casemate_model_state) :=
  match n_children with
  | O => true
  | S n_children =>
    let child_addr := table_start pa+ (PA (b8 b* idx)) in
    match cm !! child_addr with
    | Some child_loc =>
      match child_loc.(sl_pte) with
      | None => false
      | Some child_pte_desc =>
        match child_pte_desc.(ged_pte_kind) with
        | PTER_PTE_KIND_INVALID =>
          all_children_invalid_iter (idx b+ b1) n_children table_start cm
        | _ => false
        end
      end
    | None => false
    end
  end.

Definition all_children_invalid (pte_desc : ghost_exploded_descriptor) (cm : casemate_model_state): bool :=
  match pte_desc.(ged_pte_kind) with
  | PTER_PTE_KIND_TABLE table_data =>
    let table_start := table_data.(next_level_table_addr) in
    all_children_invalid_iter b0 512 table_start cm
  | _ => true
  end.

Definition should_perform_tlbi 
  (cpu_id : thread_identifier)
  (td : TLBI_intermediate)
  (ptc : pgtable_traverse_context) : option bool :=
  match ptc.(ptc_loc) with
  | None => None (* does not happen because we call it in tlbi_visitor in which we test that the location is init *)
  | Some loc =>
    match loc.(sl_pte) with
    | None => None (* if the PTE is not initialised, it has not been used; TLBI has no effect *)
    | Some pte_desc =>
      match td.(TI_method) with
      | TLBI_by_input_addr d =>
        let tlbi_addr := bv_shiftl_64 (phys_addr_val d.(TOBAD_page)) b12 in
        let ia_start := pte_desc.(ged_ia_region).(range_start) in
        let ia_end := ia_start pa+ pte_desc.(ged_ia_region).(range_size) in

        (* If the PTE has valid children, the TLBI by VA is not enough *)
        if (negb (is_leaf pte_desc.(ged_pte_kind)) && negb (all_children_invalid pte_desc ptc.(ptc_state))) then
          Some false

        (* __should_perform_tlbi_matches_addr *)
        else if negb ((phys_addr_val ia_start b<=? tlbi_addr)
                  && (tlbi_addr b<? phys_addr_val ia_end)) then Some false
        
        (* __should_perform_tlbi_matches_level *)
        else if ((negb (is_l3 pte_desc.(ged_level))) && d.(TOBAD_last_level_only)) then
          Some false

        else
          (* __should_perform_tlbi_matches_id *)
          match td.(TI_regime), pte_desc.(ged_stage) with
          | Regime_EL10, S2 =>
            let roots := retrieve_roots_for_stage S2 ptc.(ptc_state).(cms_roots) in
            match retrieve_root_for_baddr roots ptc.(ptc_root) with
            | Some pte_root =>
              match get_current_vttbr cpu_id ptc.(ptc_state) with
              | Some vttbr => Some (negb (bool_decide (pte_root.(r_id) = vttbr.(r_id))))
              | None => Some true
              end
            | None => Some true
            end
          | Regime_EL2, S1 =>
            let roots := retrieve_roots_for_stage S1 ptc.(ptc_state).(cms_roots) in
            match retrieve_root_for_baddr roots ptc.(ptc_root) with
            | Some pte_root =>
              match __get_tlbi_asid td with
              | Some asid => Some (negb (bool_decide (pte_root.(r_id) = asid)))
              | None => Some true
              end
            | None => Some true
            end
          | _, _ => Some true
          end
      | TLBI_by_addr_space addr_id =>
        match td.(TI_regime), pte_desc.(ged_stage) with
        | Regime_EL10, S2 =>
          let roots := retrieve_roots_for_stage S2 ptc.(ptc_state).(cms_roots) in
          match retrieve_root_for_baddr roots ptc.(ptc_root) with
          | Some pte_root =>
            match get_current_vttbr cpu_id ptc.(ptc_state) with
            | Some vttbr => Some (negb (bool_decide (pte_root.(r_id) = vttbr.(r_id))))
            | None => Some true
            end
          | None => Some true
          end
        | Regime_EL2, S1 =>
          let roots := retrieve_roots_for_stage S1 ptc.(ptc_state).(cms_roots) in
          match retrieve_root_for_baddr roots ptc.(ptc_root) with
          | Some pte_root =>
            match __get_tlbi_asid td with
            | Some asid => Some (negb (bool_decide (pte_root.(r_id) = asid)))
            | None => Some true
            end
          | None => Some true
          end
        | _, _ => Some true
        end
      | TLBI_by_all => Some true
      end
    end
  end.


Definition step_pte_on_tlbi_after_dsb (td: TLBI_intermediate) : option LIS :=
  match td.(TI_regime) with
  | Regime_EL2 => Some LIS_dsb_tlbied
  | Regime_EL10 =>
    match td.(TI_stage) with
    | TLBI_OP_stage1 => Some LIS_dsbed (* no effect*)
    | TLBI_OP_stage2 => Some LIS_dsb_tlbi_ipa
    | TLBI_OP_both_stages => Some LIS_dsb_tlbied
    end
  | _ => None
  end.

Definition step_pte_on_tlbi_after_tlbi_ipa (td: TLBI_intermediate) : option LIS :=
  match td.(TI_regime) with
  | Regime_EL10 =>
      match td.(TI_stage) with
      | TLBI_OP_stage1 | TLBI_OP_both_stages => Some LIS_dsb_tlbied
      | TLBI_OP_stage2 => Some LIS_dsb_tlbi_ipa_dsb
      end
  | _ => None
  end.

Definition tlbi_visitor
  (cpu_id : thread_identifier)
  (td : TLBI_intermediate)
  (ptc : pgtable_traverse_context) :
  casemate_model_result :=
  match ptc.(ptc_loc) with
  | None => (* Cannot do anything if the page is not initialised *)
    Merror (CME_uninitialised "tlbi_visitor" ptc.(ptc_addr))
  | Some location =>
    (* Test if there is something to do *)
    match should_perform_tlbi cpu_id td ptc with
    | None => Merror CME_unimplemented
    | Some b =>
      if b then
        (* step_pte_on_tlbi: inlined *)
        match location.(sl_pte) with
        | None => Merror (CME_internal_error IET_unexpected_none)
          (* This cannot happen (otherwise, should_perform_tlbi would be false) *)
        | Some exploded_desc =>
          match exploded_desc.(ged_state) with
          | SPS_STATE_PTE_INVALID_UNCLEAN ai =>
            (* If the CPU that does the transformation is not the one that initiated the invalidation, do nothing *)
            if bool_decide (cpu_id = ai.(ai_invalidator_tid)) then
              let new_substate :=
                (* Depending on the current state and the TLBI kind, we update the sub-state *)
                match ai.(ai_lis) with
                | LIS_dsbed => step_pte_on_tlbi_after_dsb td
                | LIS_dsb_tlbi_ipa_dsb => step_pte_on_tlbi_after_tlbi_ipa td
                | a => Some a (* Otherwise, it does not make the sub-automaton change *)
                end
              in
              match new_substate with
              | None => Merror CME_unimplemented
              | Some new_substate =>
                let log :=
                  match new_substate, ai.(ai_lis) with
                  | LIS_dsb_tlbied, LIS_dsbed => Mlog (Log "BBM: dsb'd->tlbied" (phys_addr_val ptc.(ptc_addr)))
                  | LIS_dsb_tlbi_ipa, LIS_dsbed => Mlog (Log "BBM: dsb'd->tlbied_ipa" (phys_addr_val ptc.(ptc_addr)))
                  | LIS_dsb_tlbied, LIS_dsb_tlbi_ipa_dsb => Mlog (Log "BBM: dsb_tlbi_ipa_dsbed->tlbied" (phys_addr_val ptc.(ptc_addr)))
                  | _, _ => id
                  end
                in
                (* Write the new sub-state in the global automaton *)
                let new_loc := location <| sl_pte := Some (exploded_desc <|ged_state := SPS_STATE_PTE_INVALID_UNCLEAN (ai <| ai_lis := new_substate|>) |>)|> in
                let new_mem := ptc.(ptc_state) <| cms_memory := <[location.(sl_phys_addr) := new_loc]> ptc.(ptc_state).(cms_memory)|> in
                log (Mreturn new_mem)
              end
            else
              Mreturn ptc.(ptc_state)
          | _ => Mreturn ptc.(ptc_state)
          end
        end
      else (* In the case where the PTE is not affected by the TLBI, we do nothing *)
        {|cmr_log := nil; cmr_data := Ok _ _ ptc.(ptc_state) |}
    end
  end.

Definition step_tlbi (tid : thread_identifier) (td : trans_tlbi_data) (cm : casemate_model_state) : casemate_model_result :=
  let tlbi := decode_tlbi td in
  match tlbi.(TI_regime) with
  | Regime_EL2 =>
    (* traverse all s1 pages*)
    traverse_si_pgt (Some tid) cm (tlbi_visitor tid tlbi) S1
  | Regime_EL10 =>
    (* traverse s2 pages *)
    traverse_si_pgt (Some tid) cm (tlbi_visitor tid tlbi) S2
  | _ =>
    (* traverse all page tables and add a warning *)
    let res := traverse_all_pgt (Some tid) cm (tlbi_visitor tid tlbi) in
    res <| cmr_log := Warning_unsupported_TLBI :: res.(cmr_log) |>
  end.

(** MSR *)

Fixpoint root_exists (root : sm_owner_t) (roots : list cm_root) : bool :=
  match roots with
  | [] => false
  | t :: q => (bool_decide (t.(r_baddr) = root)) || (root_exists root q)
  end.

Definition register_root
  (tid : thread_identifier)
  (addr_id : addr_id_t)
  (cm : casemate_model_state)
  (root : sm_owner_t)
  (stage : entry_stage_t) :
  casemate_model_result :=
  let other_root_list :=
    match stage with
    | S1 => cmr_s2
    | S2 => cmr_s1
    end cm.(cms_roots) in
  (* Check that the root does not already exist in the other root list*)
  if root_exists root other_root_list then Merror CME_root_already_exists
  else
    (* Add the root to the list of roots *)
    let new_roots :=
      let new_root := {| r_baddr := root; r_id := addr_id; r_refcount := 0 |} in
      match stage with
      | S2 => cm.(cms_roots) <| cmr_s2 := new_root :: cm.(cms_roots).(cmr_s2) |>
      | S1 => cm.(cms_roots) <| cmr_s1 := new_root :: cm.(cms_roots).(cmr_s1) |>
      end
    in
    let new_st := cm <| cms_roots := new_roots |> in
    (* then mark all its children as PTE *)
    match root with
    | Root r => traverse_pgt_from root r pa0 l0 stage (mark_cb tid) new_st
    end.

Definition check_ttbr0_el2_asid
  (md : trans_msr_data)
  (addr_id : addr_id_t) : bool :=
  (* TTBR0_EL2 in non-VHE mode has a Res0 ASID *)
  match md.(tmd_sysreg), addr_id with
  | SYSREG_TTBR_EL2, AID aid => aid b=? b0
  | SYSREG_VTTBR, _ => true
  end.

Definition context_switch
  (tid : thread_identifier)
  (addr_id : addr_id_t)
  (stage : entry_stage_t)
  (md : trans_msr_data)
  (cm : casemate_model_state) : 
  casemate_model_result :=
  (* decrement refcount on current root (if applicable) *)
  let assoc_root := current_thread_context_root tid stage cm in
  let decr_cm := 
    match assoc_root with
    | Some root =>
      let new_assoc_root := {| 
        r_baddr := root.(r_baddr);
        r_id := root.(r_id);
        r_refcount := root.(r_refcount) - 1 |} in
      let new_cms_roots := update_cms_root_for_baddr stage (root.(r_baddr)) new_assoc_root cm.(cms_roots) in
      cm <| cms_roots := new_cms_roots |>
    | None => cm
    end in

  (* and increment refcount on cone we just switched to *)
  let roots := retrieve_roots_for_stage stage decr_cm.(cms_roots) in
  let assoc_root := retrieve_root_for_id roots addr_id in
  match assoc_root with
  | Some root =>
    let new_assoc_root := {| 
      r_baddr := root.(r_baddr);
      r_id := root.(r_id);
      r_refcount := root.(r_refcount) + 1 |} in
    let new_cms_roots := update_cms_root_for_id stage (root.(r_id)) new_assoc_root cm.(cms_roots) in
    let incr_cm := decr_cm <| cms_roots := new_cms_roots |> in
    (* update the current context *)
    let final_cm := update_current_thread_context tid stage root.(r_baddr) incr_cm in
    Mreturn final_cm
  | None => Merror (CME_internal_error IET_unexpected_none)
  end.
  
Definition step_msr 
  (tid : thread_identifier)
  (md : trans_msr_data)
  (cm : casemate_model_state) : 
  casemate_model_result :=
  let stage :=
    match md.(tmd_sysreg) with
    | SYSREG_TTBR_EL2 => S1
    | SYSREG_VTTBR => S2
    end
  in
  let root := ttbr_extract_baddr md.(tmd_val) in
  let addr_id := ttbr_extract_id md.(tmd_val) in
  (* TTBR0_EL2 in non-VHE mode has a Res0 ASID *)
  if negb (check_ttbr0_el2_asid md addr_id) then
    Merror (CME_addr_id_error "TTBR0_EL2 ASID is reserved 0")
  else
    let roots := retrieve_roots_for_stage stage cm.(cms_roots) in
    match retrieve_root_for_baddr roots root with
    | Some assoc_root =>
      (* if that root with that id exists already, were just context switching *)
      if (bool_decide (assoc_root.(r_id) = addr_id)) then
        context_switch tid addr_id stage md cm
      else
      (* see if that root is already associated with a different (VM/AS)ID *)
        Merror (CME_addr_id_error "root already associated with an (VM/AS)ID")
    | None =>
      let res :=
        match retrieve_root_for_id roots addr_id with
        | Some assoc_root =>
          if negb (bool_decide (assoc_root.(r_baddr) = root)) then
            Merror (CME_addr_id_error "duplicate (VM/AS)ID")
          else if negb (bool_decide (assoc_root.(r_id) = addr_id)) then
            Merror (CME_addr_id_error "root already associated with an (VM/AS)ID")
          else register_root tid addr_id cm root stage
        | None => register_root tid addr_id cm root stage
        end in
      match res.(cmr_data) with
      | Ok _ _ cm => context_switch tid addr_id stage md cm
      | _ => res
      end
    end.

(** Hint *)

Definition step_hint_set_root_lock
  (root : sm_owner_t)
  (addr : phys_addr_t)
  (cm : casemate_model_state) :
  casemate_model_result :=
    Mreturn (cm <| cms_lock_addr := insert (phys_addr_val (root_val root)) (phys_addr_val addr) cm.(cms_lock_addr)|>).

Function set_owner_root
  (phys : phys_addr_t)
  (root : sm_owner_t)
  (cm : casemate_model_state)
  (logs : list log_element)
  (offs : Z)
  {measure Z.abs_nat offs} :
  casemate_model_result :=
  if Zle_bool offs 0 then
    {| cmr_log := logs; cmr_data := Ok _ _ cm |}
  else
    let addr := phys pa+ (PA (bv_mul_Z_64 b8 (offs - 1))) in
    match cm !! addr with
    | None =>
      {|
        cmr_log :=
          logs;
          cmr_data := Error _ _ (CME_uninitialised "set_owner_root" addr)
      |}
    | Some location =>
      let new_pte :=
        match location.(sl_pte) with
        | None => None
        | Some pte => Some (pte <| ged_owner := root|>) (* actually change the root *)
        end
      in
      (* Write the change to the global state *)
      let new_loc := location <| sl_pte := new_pte |> in
      let new_state := cm <|cms_memory := <[ location.(sl_phys_addr) := new_loc ]> cm.(cms_memory) |> in
      set_owner_root phys root new_state logs (offs - 1)
    end
.
Set Warnings "-funind-cannot-build-inversion -funind-cannot-define-graph".
Proof. lia. Qed.
Set Warnings "funind-cannot-build-inversion funind-cannot-define-graph".

Definition step_release_cb (ctx : pgtable_traverse_context) : casemate_model_result :=
  match ctx.(ptc_loc) with
  | None => Merror (CME_uninitialised "step_release_cb"%string ctx.(ptc_addr))
  | Some location =>
    match location.(sl_pte) with
    | None => Merror (CME_not_a_pte "release_cb" ctx.(ptc_addr))
    | Some desc =>
      match desc.(ged_state) with
      | SPS_STATE_PTE_INVALID_UNCLEAN _ =>
          Merror (CME_bbm_violation VT_release_unclean ctx.(ptc_addr))
      | _ => Mreturn ctx.(ptc_state)
      end
    end
  end.


Fixpoint remove (x : sm_owner_t) (l : list sm_owner_t) : list sm_owner_t :=
  match l with
  | nil => nil
  | y :: tl => if bool_decide (x = y) then remove x tl else y::(remove x tl)
  end.

Fixpoint unregister_root
  (addr : sm_owner_t)
  (remaining : list cm_root)
  (roots : list cm_root) : list cm_root :=
  match roots with
  | [] => []
  | root :: tl =>
    if bool_decide (root.(r_baddr) = addr) then remaining ++ tl
    else unregister_root addr (remaining ++ [root]) tl
  end.

Definition try_unregister_root
  (addr : sm_owner_t)
  (cpu : thread_identifier)
  (cm : casemate_model_state) :
  casemate_model_result :=
  match cm !! root_val addr with
  | None => Merror (CME_internal_error IET_unexpected_none)
  | Some loc =>
    match loc.(sl_pte) with
    | None => Merror (CME_internal_error IET_unexpected_none)
    | Some pte =>
      let new_roots :=
        match pte.(ged_stage) with
        | S2 => cm.(cms_roots) <| cmr_s2 := unregister_root addr [] cm.(cms_roots).(cmr_s2) |>
        | S1 => cm.(cms_roots) <| cmr_s1 := unregister_root addr [] cm.(cms_roots).(cmr_s1) |>
        end
      in
      let cm := cm <| cms_roots := new_roots |> in
      traverse_pgt_from_root addr pte.(ged_stage) (unmark_cb cpu) cm
    end
  end.

Definition step_release_table
  (cpu : thread_identifier)
  (addr : sm_owner_t)
  (cm : casemate_model_state) :
  casemate_model_result :=
  match cm !! root_val addr with
  | None => Merror (CME_uninitialised "release"%string (root_val addr))
  | Some location =>
    match location.(sl_pte) with
    | None => Merror (CME_not_a_pte "release"%string (root_val addr))
    | Some desc =>
      let new_st := traverse_pgt_from
        addr
        (root_val desc.(ged_owner))
        desc.(ged_ia_region).(range_start)
        desc.(ged_level)
        desc.(ged_stage)
        step_release_cb
        cm in
      Mupdate_state (try_unregister_root (addr) cpu) new_st
    end
  end
.

Definition step_hint_set_pte_thread_owner
  (phys : phys_addr_t)
  (val : sm_owner_t)
  (cm : casemate_model_state) :
  casemate_model_result :=
  match cm !! phys with
  | None => Merror (CME_uninitialised "set_pte_thread_owner"%string phys)
  | Some location =>
    match location.(sl_pte) with
    | None => Merror (CME_not_a_pte "set_pte_thread_owner"%string phys)
    | Some _ =>
      let thread_owner := TID (to_nat (phys_addr_val (root_val val))) in
      Mreturn (cm <| cms_memory :=
        (<[ location.(sl_phys_addr) := location <| sl_thread_owner := Some thread_owner |> ]> cm.(cms_memory))
      |> )
    end
  end
.

Definition step_hint
  (cpu : thread_identifier)
  (hd : trans_hint_data)
  (cm : casemate_model_state) :
  casemate_model_result :=
  match hd.(thd_hint_kind) with
  | GHOST_HINT_SET_ROOT_LOCK =>
    (* The types are weird here because of the order is reversed from SET_OWNER_ROOT (the root is first and the address second) *)
    step_hint_set_root_lock (Root hd.(thd_location)) (root_val hd.(thd_value)) cm
    (* AFAIK, this only affects the internal locking discipline of the C casemate model and does nothing on the Coq version *)
  | GHOST_HINT_SET_OWNER_ROOT =>
    (* When ownership is transferred *)
    (* Not sure about the size of the iteration *)
    set_owner_root (align_4k hd.(thd_location)) hd.(thd_value) cm [] z512
  | GHOST_HINT_RELEASE_TABLE =>
    step_release_table cpu (Root hd.(thd_location)) cm
  | GHOST_HINT_SET_PTE_THREAD_OWNER =>
    (* Set an owner thread of the PTE to track private ownership *)
    step_hint_set_pte_thread_owner hd.(thd_location) hd.(thd_value) cm
  end
.


Definition step_lock
  (cpu : thread_identifier)
  (hd : trans_lock_data)
  (cm : casemate_model_state) :
  casemate_model_result :=
  match lookup (phys_addr_val hd.(tld_addr)) cm.(cms_lock_state) with
  | None => (* give the lock write_authorization to write the page-table *)
    let lock_state := {| ls_tid := cpu; ls_write_authorization := WA_AUTHORIZED |} in
    Mreturn (cm <| cms_lock_state := insert (phys_addr_val hd.(tld_addr)) lock_state cm.(cms_lock_state) |>)
  | Some {| ls_tid := thread; ls_write_authorization := _ |} => Merror (CME_double_lock_acquire cpu thread)
  end
.

Definition step_unlock
  (cpu : thread_identifier)
  (hd : trans_lock_data)
  (cm : casemate_model_state) : 
  casemate_model_result :=
  match lookup (phys_addr_val hd.(tld_addr)) cm.(cms_lock_state) with
  | Some {| ls_tid := thread; ls_write_authorization := _ |} =>
    if bool_decide (thread = cpu) then
      Mreturn (cm <| cms_lock_state := delete (phys_addr_val hd.(tld_addr)) cm.(cms_lock_state) |>)
    else
      Merror (CME_double_lock_acquire cpu thread)
  | None => Merror (CME_double_lock_acquire cpu cpu)
  end.
