Require Import utils.
Require Import model.
Require Import pgtable.

(* Inductive SecurityState := SS_NonSecure | SS_Root | SS_Realm | SS_Secure. *)
Inductive Regime := Regime_EL3 | Regime_EL30 | Regime_EL2 | Regime_EL20 | Regime_EL10.
Inductive Shareability := Shareability_NSH | Shareability_ISH | Shareability_OSH.

(** TLBI *)

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

Definition decode_Regime (td : trans_tlbi_data) : Regime :=
  match td.(ttd_tlbi_kind) with
  | TLBI_vmalle1is
  | TLBI_vmalle1
  | TLBI_ipas2e1is
  | TLBI_vmalls12e1
  | TLBI_vmalls12e1is
  | TLBI_alle1is => Regime_EL10
  | TLBI_vale2is
  | TLBI_vae2is
  | TLBI_vae2 => Regime_EL2
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
    else Some (bv_and_64 level b3) in

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
  | TLBI_vmalle1 => TLBI_by_addr_space (decode_tlbi_by_space_id td)
  | TLBI_vale2is
  | TLBI_vae2
  | TLBI_vae2is
  | TLBI_ipas2e1is => TLBI_by_input_addr (decode_tlbi_by_addr td)
  | TLBI_alle1is => TLBI_by_all
  end.

Definition decode_tlbi (td : trans_tlbi_data) : TLBI_intermediate :=
  let stage := decode_tlbi_stage td in
  let regime := decode_Regime td in
  let shootdown := decode_tlbi_shootdown td in
  let method := decode_tlbi_method td in
  {|
    TI_stage := stage;
    TI_regime := regime;
    TI_shootdown := shootdown;
    TI_method := method;
  |}.

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

(******************************************************************************************)
(*                             Code for write                                             *)
(******************************************************************************************)
(* Visiting a page table fails with this visitor iff the visited part has an uninitialized or invalid unclean entry *)
Definition clean_reachable_cb (ctx : pgtable_traverse_context) : casemate_model_result :=
  match ctx.(ptc_loc) with
    | None => Merror (CME_uninitialised "clean_reachable" ctx.(ptc_addr))
    | Some location =>
      match location.(sl_pte) with
        | None => Mreturn ctx.(ptc_state)
        | Some descriptor =>
          match descriptor.(eed_state) with
            | SPS_STATE_PTE_INVALID_UNCLEAN _ =>
              Merror (CME_unclean_child ctx.(ptc_addr))
            | _ => Mreturn ctx.(ptc_state)
          end
      end
  end
.

Definition clean_reachable
  (map : table_data_t)
  (descriptor : entry_exploded_descriptor)
  (cms : casemate_model_state):
  casemate_model_result :=
  traverse_pgt_from
    descriptor.(eed_owner)
    map.(next_level_table_addr)
    descriptor.(eed_ia_region).(range_start)
    (next_level descriptor.(eed_level))
    descriptor.(eed_stage)
    clean_reachable_cb
    cms
.

Definition step_write_table_mark_children
  (tid : thread_identifier)
  (wmo : write_memory_order)
  (loc : sm_location)
  (val : u64)
  (descriptor : entry_exploded_descriptor)
  (visitor_cb : pgtable_traverse_context -> casemate_model_result)
  (cms : casemate_model_state) :
  casemate_model_result :=
  if is_desc_valid val then
    (* Tests if the page table is well formed *)
    match descriptor.(eed_pte_kind) with
      | PTER_PTE_KIND_TABLE map =>
        let st := clean_reachable map descriptor cms in
        let st := Mlog
          (Log "BBM: invalid clean->valid"%string (phys_addr_val loc.(sl_phys_addr))) st in
        Mupdate_state (traverse_pgt_from
                          descriptor.(eed_owner)
                          map.(next_level_table_addr)
                          descriptor.(eed_ia_region).(range_start)
                          (next_level descriptor.(eed_level))
                          descriptor.(eed_stage)
                          visitor_cb) st
      | _ => Mlog
            (Log "BBM: invalid clean->valid"%string (phys_addr_val loc.(sl_phys_addr))) (Mreturn cms)
    end
  else
    (* if the descriptor is invalid, do nothing *)
    Mreturn cms
.

Definition step_write_on_invalid
  (tid : thread_identifier)
  (wmo : write_memory_order)
  (loc : sm_location)
  (val : u64)
  (cms : casemate_model_state) :
  casemate_model_result :=
  (* If the location is a PTE table, tests if its children are clean *)
  match loc.(sl_pte) with
    | None => (* This should not happen because if we write on invalid, we write on PTE *)
      Merror (CME_internal_error IET_unexpected_none)
    | Some descriptor =>
      let descriptor := deconstruct_pte
          tid
          descriptor.(eed_ia_region).(range_start)
          val descriptor.(eed_level)
          descriptor.(eed_owner)
          descriptor.(eed_stage) in
      let new_loc := loc <| sl_val := val |> <| sl_pte := Some descriptor |> in
      let new_cms := cms <| cms_memory := <[ loc.(sl_phys_addr) := new_loc ]> cms.(cms_memory) |> in
      step_write_table_mark_children tid wmo loc val descriptor (mark_cb tid) new_cms
    end
.

Definition step_write_on_invalid_unclean
  (tid : thread_identifier)
  (wmo : write_memory_order)
  (loc : sm_location)
  (val : u64)
  (cms : casemate_model_state) :
  casemate_model_result :=
  (* Only invalid descriptor are allowed *)
  if is_desc_valid val then
    (Merror (CME_bbm_violation BBM_valid_on_invalid_unclean loc.(sl_phys_addr)))
  else
    Mreturn (cms <|cms_memory := <[loc.(sl_phys_addr) := loc <|sl_val := val|> ]> cms.(cms_memory) |>)
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
      let new_descriptor := deconstruct_pte tid old_descriptor.(eed_ia_region).(range_start) val old_descriptor.(eed_level) old_descriptor.(eed_owner) old_descriptor.(eed_stage) in
      match old_descriptor.(eed_pte_kind), new_descriptor.(eed_pte_kind) with
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
  (cms : casemate_model_state) :
  casemate_model_result :=
  match require_bbm tid loc val with (* If no change in memory: no problem*)
    | None => Merror (CME_internal_error IET_unexpected_none)
    | Some false =>
        (* if the location des not require BBM, then we can update the value and the descriptor *)
        match loc.(sl_pte) with
          | None => (* This does not make sense because function is called on a pgt *)
            Merror (CME_internal_error IET_unexpected_none)
          | Some pte =>
            let new_pte := deconstruct_pte tid pte.(eed_ia_region).(range_start) val pte.(eed_level) pte.(eed_owner) pte.(eed_stage) in
            let loc := loc <| sl_val := val |> <| sl_pte := Some new_pte |> in
            Mreturn (insert_location loc cms)
        end
    | Some true =>
      (* Changing the descriptor is illegal *)
      Merror (CME_bbm_violation BBM_valid_on_valid loc.(sl_phys_addr))
  end
.

Definition step_write_invalid_on_valid
  (tid : thread_identifier)
  (wmo : write_memory_order)
  (loc : sm_location)
  (val : u64)
  (cms : casemate_model_state) :
  casemate_model_result :=
  (* Invalidation of pgt: changing the state to invalid unclean unguarded *)
  let old := loc.(sl_val) in
  match loc.(sl_pte) with
  | None => (* This does not make sense because function is called on a pgt *)
      Merror (CME_internal_error IET_unexpected_none)
  | Some descriptor =>
    let new_desc := descriptor <| eed_state := (SPS_STATE_PTE_INVALID_UNCLEAN {| ai_invalidator_tid := tid; ai_old_valid_desc :=  old; ai_lis := LIS_unguarded; |}) |> in
    let cms := (cms <| cms_memory := (<[ loc.(sl_phys_addr) := loc <|sl_pte := Some (new_desc)|> <| sl_val := val |> ]> cms.(cms_memory))|> ) in
    Mlog (Log "BBM: valid->invalid_unclean"%string (phys_addr_val loc.(sl_phys_addr)))
    match descriptor.(eed_pte_kind) with
    | PTER_PTE_KIND_TABLE map =>
      let res := clean_reachable map descriptor cms in
      let res := Mlog (Log "invalidating a table descriptor"%string (phys_addr_val loc.(sl_phys_addr))) res in
      (* If it is well formed, mark its children as page tables, otherwise, return the same error *)
      Mupdate_state (step_write_table_mark_children tid wmo loc val descriptor (mark_not_writable_cb tid)) res
    | _ => Mreturn cms
    end
  end
.

Definition step_write_on_valid
  (tid : thread_identifier)
  (wmo : write_memory_order)
  (loc : sm_location)
  (val : u64)
  (cms : casemate_model_state) :
  casemate_model_result :=
  if is_desc_valid val
    then step_write_valid_on_valid tid wmo loc val cms
  else
    step_write_invalid_on_valid tid wmo loc val cms
.

Definition is_valid_state (st: sm_pte_state) : bool :=
  match st with
    | SPS_STATE_PTE_VALID _ => true
    | _ => false
  end
.

Definition drop_write_authorisation
  (cpu : thread_identifier)
  (addr : phys_addr_t)
  (wmo : write_memory_order)
  (descriptor : u64)
  (pte : entry_exploded_descriptor)
  (cms : casemate_model_state) :
  casemate_model_result :=
  match get_lock_of_owner pte.(eed_owner) cms with
  | None => Merror CME_owner_not_associated_with_a_root
  | Some lock_addr =>
    match lookup lock_addr cms.(cms_lock_state) with
    | Some {| ls_tid := lock_owner; ls_write_authorization := auth |} =>
      if bool_decide (lock_owner = cpu) then
        match wmo with
        | WMO_page | WMO_plain => (* check that the write is authorized, and then drop the authorization *)
          match auth with
          | write_authorized =>
            let new_lock_state := {| ls_tid := lock_owner; ls_write_authorization := write_unauthorized |} in
            Mreturn (cms <| cms_lock_state := insert lock_addr new_lock_state cms.(cms_lock_state)|>)
          | write_unauthorized =>
            if (is_desc_valid descriptor) || is_valid_state pte.(eed_state) then
              Merror (CME_write_without_authorization addr)
            else
              let new_lock_state := {| ls_tid := lock_owner; ls_write_authorization := write_unauthorized |} in
              Mreturn (cms <| cms_lock_state := insert lock_addr new_lock_state cms.(cms_lock_state)|>)
          end
          | WMO_release => (* drop the authorization *)
            let new_lock_state := {| ls_tid := lock_owner; ls_write_authorization := write_unauthorized |} in
            Mreturn (cms <| cms_lock_state := insert lock_addr new_lock_state cms.(cms_lock_state)|>)
        end
      else
        Merror (CME_transition_without_lock addr)
    | None => Merror (CME_transition_without_lock addr)
    end
  end
.

Definition check_write_authorized
  (tid : thread_identifier)
  (wd : trans_write_data)
  (cms : casemate_model_state) :
  casemate_model_result :=
  let wmo := wd.(twd_mo) in
  let val := wd.(twd_val) in
  let addr := wd.(twd_phys_addr) in
  if negb ((bv_and_64 (phys_addr_val addr) b7) b=? b0)
    then Merror CME_unaligned_write
  else
    match cms !! addr with
    | None => Mreturn cms
    | Some location =>
        match location.(sl_pte) with
        | None => Mreturn cms
        | Some pte =>
          match location.(sl_thread_owner) with
          | Some thread_owner =>
            if bool_decide (thread_owner = tid) then
              Mreturn cms
            else
              Merror (CME_owned_pte_accessed_by_other_thread addr)
          | None => drop_write_authorisation tid addr wmo val pte cms
          end
        end
    end
.

Definition step_write_aux
  (tid : thread_identifier)
  (wd : trans_write_data)
  (cms : casemate_model_state) :
  casemate_model_result :=
  let mo := wd.(twd_mo) in
  let val := wd.(twd_val) in
  let addr := wd.(twd_phys_addr) in
  if negb ((bv_and_64 (phys_addr_val addr) b7) b=? b0)
    then Merror CME_unaligned_write else
  let new_st := check_write_authorized tid wd cms in
  let write_update s :=
    match s !! addr with
    | Some (loc) =>
      match loc.(sl_pte) with
      | Some desc =>
        (* If we write to a page table, depending on its state, we update them  *)
        match desc.(eed_state) with
        | SPS_STATE_PTE_VALID av =>
            (step_write_on_valid tid mo loc val s)
        | SPS_STATE_PTE_INVALID_CLEAN av =>
            (step_write_on_invalid tid mo loc val s)
        | SPS_STATE_PTE_INVALID_UNCLEAN av =>
            (step_write_on_invalid_unclean tid mo loc val s)
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
    step_write_page tid wd res (offs - 1)
.
Proof. lia. Qed.

Definition step_write
  (tid : thread_identifier)
  (wd : trans_write_data)
  (cms : casemate_model_state) :
  casemate_model_result :=
  match wd.(twd_mo) with
    | WMO_plain | WMO_release => step_write_aux tid wd cms
    | WMO_page => step_write_page tid wd (Mreturn cms) z512
  end.

(******************************************************************************************)
(*                             Code for init                                            *)
(******************************************************************************************)

Definition step_init_aux
  (addr : phys_addr_t)
  (st : casemate_model_result) :
  casemate_model_result :=
  let update s := {| cmr_log := nil; cmr_data := Ok _ _ (s <| cms_initialised := <[ addr := () ]> s.(cms_initialised) |>) |} in
  Mupdate_state update st
.

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
  end
.

Definition step_init
  (init_data : trans_init_data)
  (cms : casemate_model_state) :
  casemate_model_result :=
  step_init_all (PA (bv_shiftr_64 (phys_addr_val init_data.(tid_addr)) (bv64.BV64 9))) {|cmr_log := nil; cmr_data := Ok _ _ cms|} pa0 (to_nat init_data.(tid_size))
.


(******************************************************************************************)
(*                             Code for read                                              *)
(******************************************************************************************)
Definition step_memset
  (tid : thread_identifier)
  (memset_data : trans_memset_data)
  (cms : casemate_model_state) : casemate_model_result :=
  let write_data := {|
    twd_mo := WMO_plain;
    twd_phys_addr := memset_data.(tmd_addr);
    twd_val := memset_data.(tmd_value);
  |} in
  (* memset is a plain write *)
  step_write_page tid write_data (Mreturn cms) (bv64.to_Z (bv_shiftr_64 memset_data.(tmd_size) b3)).

Definition step_read
  (tid : thread_identifier)
  (rd : trans_read_data)
  (cms : casemate_model_state) :
  casemate_model_result :=
  (* Test if the memory has been initialized (it might refuse acceptable executions, not sure if it is a good idea) and its content is consistent. *)
  match cms !! rd.(trd_phys_addr) with
    | Some loc =>
        if loc.(sl_val) b=? rd.(trd_val) then
          Mreturn cms
        else
          let new_loc := loc <| sl_val := rd.(trd_val) |> in
          {| cmr_log :=
              [Inconsistent_read loc.(sl_val) rd.(trd_val) rd.(trd_phys_addr)];
             cmr_data := (Ok _ _ (cms <| cms_memory := <[rd.(trd_phys_addr) := new_loc ]> cms.(cms_memory) |>)) |}
    | None =>
        let loc := {| sl_phys_addr := rd.(trd_phys_addr); sl_val := rd.(trd_val); sl_pte := None; sl_thread_owner := Some tid |} in
        let st := cms <| cms_memory := <[ rd.(trd_phys_addr) := loc ]> cms.(cms_memory) |> in
        {| cmr_log :=
            [Warning_read_write_non_allocd loc.(sl_phys_addr)];
           cmr_data := Ok _ _ st
        |}
  end
.

(******************************************************************************************)
(*                                      DSB                                               *)
(******************************************************************************************)
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
  match desc.(eed_pte_kind) with
    | PTER_PTE_KIND_TABLE map =>
      (* The children are clean, and not writable, otherwise, it would catch fire *)
      traverse_pgt_from desc.(eed_owner) map.(next_level_table_addr) desc.(eed_ia_region).(range_start) (next_level desc.(eed_level)) desc.(eed_stage) (unmark_cb cpu_id) st
    | _ => {| cmr_log  := nil; cmr_data := Ok _ _ st |}
  end
.


Definition new_pte_after_dsb
  (cpu_id : thread_identifier)
  (pte : entry_exploded_descriptor)
  (kind : DxB) : entry_exploded_descriptor :=
  match pte.(eed_state) with
    | SPS_STATE_PTE_INVALID_UNCLEAN sst =>
      (* DSB has an effect on invalid unclean state only *)
      if negb (bool_decide (sst.(ai_invalidator_tid) = cpu_id)) then
        pte (* If it is another CPU that did the invalidation, do noting*)
      else
        (* Otherwise, update the state invalid unclean sub-automaton *)
        match sst.(ai_lis) with
          | LIS_unguarded =>
            pte <|eed_state := SPS_STATE_PTE_INVALID_UNCLEAN (sst <| ai_lis := LIS_dsbed |>) |>
          | LIS_dsbed => pte
          | LIS_dsb_tlbied =>
            match kind.(DxB_domain) with
              | MBReqDomain_InnerShareable | MBReqDomain_FullSystem =>
                pte <| eed_state := SPS_STATE_PTE_INVALID_CLEAN {| aic_invalidator_tid := sst.(ai_invalidator_tid) |} |>
                    <| eed_pte_kind := PTER_PTE_KIND_INVALID |>
              | _ => pte
            end
          | LIS_dsb_tlbi_ipa =>
              match kind.(DxB_domain) with
                | MBReqDomain_InnerShareable | MBReqDomain_FullSystem =>
                  pte <|eed_state := SPS_STATE_PTE_INVALID_UNCLEAN (sst <|ai_lis := LIS_dsb_tlbi_ipa_dsb |>) |>
                | _ => pte
              end
          | _ => pte
        end
    | _ => pte (* If not invalid unclean, then do nothing *)
  end
.

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
            match pte.(eed_state), new_pte.(eed_state) with
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
            match pte.(eed_state), new_pte.(eed_state) with
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
  end
.

Fixpoint reset_write_authorizations_aux
  (tid : thread_identifier)
  (roots: list cm_root)
  (cm : casemate_model_state) :
  casemate_model_state :=
  match roots with
  | [] => cm
  | {| r_baddr := baddr; r_id := _; r_refcount := _ |} :: q =>
    match lookup (phys_addr_val (owner_val baddr)) cm.(cms_lock_addr) with
    | Some lock_addr =>
      let new_st :=
        match lookup lock_addr cm.(cms_lock_state) with
        | None => cm
        | Some {| ls_tid := thread; ls_write_authorization := _ |} =>
          if bool_decide (thread = tid) then
            let new_lock_state := {| ls_tid := tid; ls_write_authorization := write_authorized |} in
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

Definition reset_write_authorizations (tid : thread_identifier) (cms : casemate_model_state) : casemate_model_state :=
  (* Reset the authorizations for both states *)
  reset_write_authorizations_aux tid cms.(cms_roots).(cmr_s2)
    (reset_write_authorizations_aux tid cms.(cms_roots).(cmr_s1) cms)
.

Definition step_dsb (tid : thread_identifier) (dk : DxB) (cms : casemate_model_state) : casemate_model_result :=
  (* There is enough barrier now to write plain again *)
  let st := reset_write_authorizations tid cms in
  (* walk the pgt with dsb_visitor*)
  traverse_all_pgt (Some tid) st (dsb_visitor dk tid)
.

(******************************************************************************************)
(*                                     TLBI                                               *)
(******************************************************************************************)

Definition is_leaf (kind : pte_rec) : bool :=
  match kind with
    | PTER_PTE_KIND_TABLE _ => false
    | _ => true
  end
.

Definition get_tlbi_asid (td : TLBI_intermediate) : option addr_id_t :=
  match td.(TI_method) with
  | TLBI_by_input_addr d => d.(TOBAD_asid)
  | TLBI_by_addr_space (PA addr_id) => Some (AID addr_id)
  | _ => None
  end.

Fixpoint all_children_invalid_iter
  (idx : u64)
  (n_children : nat)
  (table_start : phys_addr_t)
  (cms : casemate_model_state) : bool :=
  match n_children with
  | O => true
  | S n_children =>
    let child_addr := table_start pa+ (PA (b8 b* idx)) in
    match cms !! child_addr with
    | Some child_loc =>
      match child_loc.(sl_pte) with
      | None => false
      | Some child_pte_desc =>
        match child_pte_desc.(eed_pte_kind) with
        | PTER_PTE_KIND_INVALID =>
          all_children_invalid_iter (idx b+ b1) n_children table_start cms
        | _ => false
        end
      end
    | None => false
    end
  end.

Definition all_children_invalid (pte_desc : entry_exploded_descriptor) (cms : casemate_model_state): bool :=
  match pte_desc.(eed_pte_kind) with
  | PTER_PTE_KIND_TABLE table_data =>
    let table_start := table_data.(next_level_table_addr) in
    all_children_invalid_iter b0 512 table_start cms
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
        let ia_start := pte_desc.(eed_ia_region).(range_start) in
        let ia_end := ia_start pa+ pte_desc.(eed_ia_region).(range_size) in

        (* If the PTE has valid children, the TLBI by VA is not enough *)
        if (negb (is_leaf pte_desc.(eed_pte_kind)) && negb (all_children_invalid pte_desc ptc.(ptc_state))) then
          Some false

        (* __should_perform_tlbi_matches_addr *)
        else if negb ((phys_addr_val ia_start b<=? tlbi_addr)
                  && (tlbi_addr b<? phys_addr_val ia_end)) then Some false

        (* __should_perform_tlbi_matches_level *)
        else if ((negb (is_l3 pte_desc.(eed_level))) && d.(TOBAD_last_level_only)) then
          Some false

        else
          (* __should_perform_tlbi_matches_id *)
          match td.(TI_regime), pte_desc.(eed_stage) with
          | Regime_EL10, S2 =>
            match retrieve_root_for_baddr S2 ptc.(ptc_state).(cms_roots) ptc.(ptc_root) with
            | Some pte_root =>
              match get_current_vttbr cpu_id ptc.(ptc_state) with
              | Some vttbr => Some (bool_decide (pte_root.(r_id) = vttbr.(r_id)))
              | None => Some true
              end
            | None => Some true
            end
          | Regime_EL2, S1 =>
            match retrieve_root_for_baddr S1 ptc.(ptc_state).(cms_roots) ptc.(ptc_root) with
            | Some pte_root =>
              match get_tlbi_asid td with
              | Some asid => Some (bool_decide (pte_root.(r_id) = asid))
              | None => Some true
              end
            | None => Some true
            end
          | _, _ => Some true
          end
      | TLBI_by_addr_space addr_id =>
        match td.(TI_regime), pte_desc.(eed_stage) with
        | Regime_EL10, S2 =>
          match retrieve_root_for_baddr S2 ptc.(ptc_state).(cms_roots) ptc.(ptc_root) with
          | Some pte_root =>
            match get_current_vttbr cpu_id ptc.(ptc_state) with
            | Some vttbr => Some (bool_decide (pte_root.(r_id) = vttbr.(r_id)))
            | None => Some true
            end
          | None => Some true
          end
        | Regime_EL2, S1 =>
          match retrieve_root_for_baddr S1 ptc.(ptc_state).(cms_roots) ptc.(ptc_root) with
          | Some pte_root =>
            match get_tlbi_asid td with
            | Some asid => Some (bool_decide (pte_root.(r_id) = asid))
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
  end
.

Definition step_pte_on_tlbi_after_tlbi_ipa (td: TLBI_intermediate) : option LIS :=
  match td.(TI_regime) with
    | Regime_EL10 =>
        match td.(TI_stage) with
          | TLBI_OP_stage1 | TLBI_OP_both_stages => Some LIS_dsb_tlbied
          | TLBI_OP_stage2 => Some LIS_dsb_tlbi_ipa_dsb
        end
    | _ => None
  end
.

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
                match exploded_desc.(eed_state) with
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
                          let new_loc := location <| sl_pte := Some (exploded_desc <|eed_state := SPS_STATE_PTE_INVALID_UNCLEAN (ai <| ai_lis := new_substate|>) |>)|> in
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

Definition step_tlbi
  (tid : thread_identifier)
  (td : trans_tlbi_data)
  (cm : casemate_model_state) :
  casemate_model_result :=
  let tlbi := decode_tlbi td in
  match tlbi.(TI_regime) with
    | Regime_EL10 =>
      (* TLBIs that hit host/guest tables *)
      traverse_pgt (Some tid) cm (tlbi_visitor tid tlbi) S2
    | Regime_EL2 =>
      (* TLBIs that hit pKVM's own pagetable *)
      traverse_pgt (Some tid) cm (tlbi_visitor tid tlbi) S1
    | _ =>
      Merror CME_unimplemented
      (* let res := traverse_all_pgt (Some tid) cm (tlbi_visitor tid tlbi) in
      res <| cmr_log := Warning_unsupported_TLBI :: res.(cmr_log) |> *)
  end.


(** MSR *)

Fixpoint root_exists (root : sm_owner_t) (roots : list cm_root) : bool :=
  match roots with
    | [] => false
    | t :: q => (bool_decide (t.(r_baddr) = root)) || (root_exists root q)
  end.

Definition try_register_root
  (tid : thread_identifier)
  (addr_id : addr_id_t)
  (cm : casemate_model_state)
  (baddr : sm_owner_t)
  (stage : entry_stage_t) :
  casemate_model_result :=
  (* Add the root to the list of roots *)
  let new_root := {| r_baddr := baddr; r_id := addr_id; r_refcount := 0 |} in
  let new_roots := insert_cms_root stage new_root cm.(cms_roots) in
  let new_st := cm <| cms_roots := new_roots |> in
  (* then mark all its children as PTE *)
  match baddr with
  | Root r => traverse_pgt_from baddr r pa0 l0 stage (mark_cb tid) new_st
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
  let assoc_root := retrieve_root_for_id stage decr_cm.(cms_roots) addr_id in
  match assoc_root with
  | Some root =>
    let new_assoc_root := {|
      r_baddr := root.(r_baddr);
      r_id := root.(r_id);
      r_refcount := root.(r_refcount) + 1 |} in
    let new_cms_roots := update_cms_root_for_id stage (root.(r_id)) new_assoc_root cm.(cms_roots) in
    let incr_cm := decr_cm <| cms_roots := new_cms_roots |> in
    (* make it the curent context *)
    let final_cm := update_current_thread_context tid stage root.(r_baddr) incr_cm in
    Mreturn final_cm
  | None => Merror (CME_internal_error IET_unexpected_none)
  end.

Definition stage_from_ttbr
  (sysreg : ghost_sysreg_kind) : entry_stage_t :=
  match sysreg with
  | SYSREG_TTBR_EL2 => S1
  | SYSREG_VTTBR => S2
  end.

Definition step_msr
  (tid : thread_identifier)
  (md : trans_msr_data)
  (cm : casemate_model_state) :
  casemate_model_result :=
  let stage := stage_from_ttbr md.(tmd_sysreg) in
  let baddr := ttbr_extract_baddr md.(tmd_val) in
  let addr_id := ttbr_extract_id md.(tmd_val) in

  (* TTBR0_EL2 in non-VHE mode has a Res0 ASID *)
  if negb (check_ttbr0_el2_asid md addr_id) then
    Merror (CME_addr_id_error AID_TTBR0_EL2_reserved_zero)
  else
    match retrieve_root_for_baddr stage cm.(cms_roots) baddr with
    | Some assoc_root =>
      (* if that root with that id exists already, were just context switching *)
      if (bool_decide (assoc_root.(r_id) = addr_id)) then
        context_switch tid addr_id stage md cm
      else
        (* see if that root is already associated with a different (VM/AS)ID *)
        Merror (CME_addr_id_error AID_root_already_associated)
    | None =>
      let res :=
        match retrieve_root_for_id stage cm.(cms_roots) addr_id with
        | Some assoc_root =>
          if negb (bool_decide (assoc_root.(r_baddr) = baddr)) then
            Merror (CME_addr_id_error AID_duplicate_addr_id)
          else if negb (bool_decide (assoc_root.(r_id) = addr_id)) then
            Merror (CME_addr_id_error AID_root_already_associated)
          else try_register_root tid addr_id cm baddr stage
        | None => try_register_root tid addr_id cm baddr stage
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
    Mreturn (cm <| cms_lock_addr := insert (phys_addr_val (owner_val root)) (phys_addr_val addr) cm.(cms_lock_addr)|>).

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
        | Some pte => Some (pte <| eed_owner := root|>) (* actually change the root *)
        end
      in
      (* Write the change to the global state *)
      let new_loc := location <| sl_pte := new_pte |> in
      let new_state := cm <|cms_memory := <[ location.(sl_phys_addr) := new_loc ]> cm.(cms_memory) |> in
      set_owner_root phys root new_state logs (offs - 1)
    end.

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
      match desc.(eed_state) with
      | SPS_STATE_PTE_INVALID_UNCLEAN _ =>
          Merror (CME_bbm_violation BBM_release_unclean ctx.(ptc_addr))
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
  match cm !! owner_val addr with
  | None => Merror (CME_internal_error IET_unexpected_none)
  | Some loc =>
    match loc.(sl_pte) with
    | None => Merror (CME_internal_error IET_unexpected_none)
    | Some pte =>
      let new_roots :=
        match pte.(eed_stage) with
        | S2 => cm.(cms_roots) <| cmr_s2 := unregister_root addr [] cm.(cms_roots).(cmr_s2) |>
        | S1 => cm.(cms_roots) <| cmr_s1 := unregister_root addr [] cm.(cms_roots).(cmr_s1) |>
        end
      in
      let cm := cm <| cms_roots := new_roots |> in
      traverse_pgt_from_root addr pte.(eed_stage) (unmark_cb cpu) cm
    end
  end.

Definition step_release_table
  (cpu : thread_identifier)
  (addr : sm_owner_t)
  (cm : casemate_model_state) :
  casemate_model_result :=
  match cm !! owner_val addr with
  | None => Merror (CME_uninitialised "release"%string (owner_val addr))
  | Some location =>
    match location.(sl_pte) with
    | None => Merror (CME_not_a_pte "release"%string (owner_val addr))
    | Some desc =>
      let new_st := traverse_pgt_from
        addr
        (owner_val desc.(eed_owner))
        desc.(eed_ia_region).(range_start)
        desc.(eed_level)
        desc.(eed_stage)
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
      let thread_owner := TID (phys_addr_val (owner_val val)) in
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
    step_hint_set_root_lock (Root hd.(thd_location)) (owner_val hd.(thd_value)) cm
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

(*** Lock *)

Definition step_lock
  (cpu : thread_identifier)
  (lock_data : trans_lock_data)
  (cms : casemate_model_state)
: casemate_model_result :=
  match lookup (phys_addr_val lock_data.(tld_addr)) cms.(cms_lock_state) with
  | None =>(* lock and give the lock write_authorization to write the page-table *)
    let lock_state := {| ls_tid := cpu; ls_write_authorization := write_authorized |} in
    Mreturn (cms <| cms_lock_state := insert (phys_addr_val lock_data.(tld_addr)) lock_state cms.(cms_lock_state) |>)
  | Some {| ls_tid := thread; ls_write_authorization := _ |} => Merror (CME_double_lock_acquire cpu thread)
  end
.

Definition step_unlock
  (cpu : thread_identifier)
  (lock_data : trans_lock_data)
  (cms : casemate_model_state)
: casemate_model_result :=
  match lookup (phys_addr_val lock_data.(tld_addr)) cms.(cms_lock_state) with
  | Some {| ls_tid := thread; ls_write_authorization := _ |} =>
    if bool_decide (thread = cpu) then
      Mreturn (cms <| cms_lock_state := delete (phys_addr_val lock_data.(tld_addr)) cms.(cms_lock_state) |>)
    else
      Merror (CME_double_lock_acquire cpu thread)
  | None => Merror (CME_double_lock_acquire cpu cpu)
  end
.

Definition step
  (trans : casemate_model_step)
  (cms : casemate_model_state) :
  casemate_model_result :=
  match trans.(cms_data) with
  | CMSD_TRANS_HW_MEM_WRITE wd =>
    step_write trans.(cms_thread_identifier) wd cms
  | CMSD_TRANS_HW_MEM_READ rd =>
    step_read trans.(cms_thread_identifier) rd cms
  | CMSD_TRANS_HW_BARRIER (Barrier_DSB dsb_data) =>
    step_dsb trans.(cms_thread_identifier) dsb_data cms
  | CMSD_TRANS_HW_BARRIER (_) =>
    {| cmr_log := []; cmr_data := Ok _ _ cms |}
  | CMSD_TRANS_HW_TLBI tlbi_data =>
    step_tlbi trans.(cms_thread_identifier) tlbi_data cms
  | CMSD_TRANS_HW_MSR msr_data =>
    step_msr trans.(cms_thread_identifier) msr_data cms
  | CMSD_TRANS_ABS_LOCK lock_data =>
    step_lock trans.(cms_thread_identifier) lock_data cms
  | CMSD_TRANS_ABS_UNLOCK lock_data =>
    step_unlock trans.(cms_thread_identifier) lock_data cms
  | CMSD_TRANS_ABS_MEM_INIT init_data =>
    step_init init_data cms
  | CMSD_TRANS_ABS_MEMSET memset_data =>
    step_memset trans.(cms_thread_identifier) memset_data cms
  | CMSD_TRANS_HINT hint_data =>
    step_hint trans.(cms_thread_identifier) hint_data cms
  end.
