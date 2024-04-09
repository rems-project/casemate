(** Simplified model *)
(* https://github.com/rems-project/linux/blob/pkvm-verif-6.4/arch/arm64/kvm/hyp/include/nvhe/ghost_simplified_model.h *)



Require Import String.
Require Import stdpp.unstable.bitvector.

(* uses https://github.com/tchajed/coq-record-update *)
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Require Import stdpp.gmap.


Definition u64 := bv 64.
Search (bv _ -> bv _ -> bool).
Definition u64_eqb (x y : u64) : bool :=
  true (* TODO: fight typeclasses *).

Infix "=?" := u64_eqb.

Definition phys_addr_t := u64.

Definition sm_owner_t := u64.

Definition thread_identifier := nat.

Inductive LVS :=
| LVS_unguarded
| LVS_dsbed
| LVS_dsb_csed
.

Record aut_valid := {
  lvs : list LVS;
}.



(*****************************************************************************)
(********                Automaton definition                        *********)
(*****************************************************************************)

Inductive LIS :=
| LIS_unguarded
| LIS_dsbed
| LIS_dsb_tlbi_all
.

Record aut_invalid := {
  ai_invalidator_tid : thread_identifier;
  ai_old_valid_desc : u64;
  ai_lis : LIS;
}.

Record aut_invalid_clean := {
  aic_invalidator_tid : thread_identifier;
}.

Inductive sm_pte_state :=
| SPS_STATE_PTE_VALID (valid_state:aut_valid)
| SPS_STATE_PTE_INVALID_UNCLEAN (invalid_unclean_state:aut_invalid)
| SPS_STATE_PTE_INVALID (invalid_clean_state:aut_invalid_clean)
.

Record ghost_addr_range := {
  range_start : u64;
  range_size : u64;
}.

Record table_data_t := {
  next_level_table_addr : u64;
}.

Record map_data_t := {
  oa_region : ghost_addr_range;
}.

Inductive pte_rec :=
| PTER_PTE_KIND_TABLE (table_data:table_data_t)
| PTER_PTE_KIND_MAP (map_data:map_data_t)
| PTER_PTE_KIND_INVALID
.

Record ghost_exploded_descriptor := {
  ged_ia_region : ghost_addr_range;
  ged_level : u64;
  ged_s2 : bool;
  ged_pte_kind : pte_rec;
}.

Record sm_location := mk_sm_location {
  (* sl_initialised : bool; *)
  sl_phys_addr : u64;
  sl_val : u64;
  sl_is_pte : bool;
  sl_descriptor : ghost_exploded_descriptor;
  sl_state : sm_pte_state;
  sl_owner : sm_owner_t;
}.
#[export] Instance eta_sm_location : Settable _ := settable! mk_sm_location < sl_phys_addr; sl_val; sl_is_pte; sl_descriptor; sl_state; sl_owner>.

(* Do we need locks? *)
Record owner_locks := {
  ol_len : u64;
  ol_owner_ids : list sm_owner_t;
  ol_locks : unit (* TODO??? *);
}.

(* The memory state is a map from address to simplified model location *)
Definition ghost_simplified_model_state := gmap u64 sm_location.

(* Storing roots for PTE walkthrough (we might need to distinguish S1 and S2 roots) *)
Record pte_roots := {
  pr_list : list u64 
}.

Record ghost_simplified_memory := mk_ghost_simplified_model {
  gsm_roots : pte_roots;
  gsm_memory : ghost_simplified_model_state
}.
#[export] Instance eta_ghost_simplified_memory : Settable _ := settable! mk_ghost_simplified_model <gsm_roots; gsm_memory>.

Definition initial_state := {|
  gsm_roots := {| pr_list := []; |};
  gsm_memory := gmap_empty;
|}.


(*****************************************************************************)
(********               Transition definition                        *********)
(*****************************************************************************)
(* All those transitions will go in favor of ARM ISA description (except for hints) *)
Inductive write_memory_order :=
| WMO_plain
| WMO_release
.

(* TODO: careful!!! the C code has clever bit pattern stuff *)
Inductive sm_tlbi_op_stage :=
| TLBI_OP_STAGE1
| TLBI_OP_STAGE2
| TLBI_OP_BOTH_STAGES
.

Inductive sm_tlbi_op_method_kind :=
| TLBI_OP_BY_ALL
| TLBI_OP_BY_INPUT_ADDR
| TLBI_OP_BY_ADDR_SPACE
.

Definition TLBI_OP_BY_VA := TLBI_OP_BY_INPUT_ADDR.
Definition TLBI_OP_BY_IPA := TLBI_OP_BY_INPUT_ADDR.

Definition TLBI_OP_BY_VMID := TLBI_OP_BY_ADDR_SPACE.
Definition TLBI_OP_BY_ASID := TLBI_OP_BY_ADDR_SPACE.

Inductive sm_tlbi_op_regime_kind :=
| TLBI_REGIME_EL10
| TLBI_REGIME_EL2
.

Record tlbi_op_method_by_address_data := {
  tombad_page : u64;
  tombad_level_hint : option u64;
  tombad_last_level_only : bool;
}.

Record tlbi_op_method_by_address_space_id_data := {
  tombas_asid_or_vmid : u64;
}.

Inductive sm_tlbi_op_method :=
| TOM_by_ALL
| TOM_by_input_addr (by_address_data : tlbi_op_method_by_address_data)
| TOM_by_addr_space (by_id_data : tlbi_op_method_by_address_space_id_data)
.

Record sm_tlbi_op := {
  sto_stage : sm_tlbi_op_stage;
  sto_regime : sm_tlbi_op_regime_kind;
  sto_method : sm_tlbi_op_method;
  sto_shootdown : bool;
}.

Inductive tlbi_kind :=
|	TLBI_vmalls12e1
|	TLBI_vmalls12e1is
|	TLBI_vmalle1is
|	TLBI_alle1is
|	TLBI_vmalle1
|	TLBI_vale2is
|	TLBI_vae2is
|	TLBI_ipas2e1is
.

Inductive dsb_kind :=
|	DSB_ish
|	DSB_ishst
|	DSB_nsh
.


Inductive ghost_sysreg_kind :=
|	SYSREG_VTTBR
|	SYSREG_TTBR_EL2
.

Inductive ghost_hint_kind :=
| GHOST_HINT_SET_ROOT_LOCK
| GHOST_HINT_SET_OWNER_ROOT
.

Record src_loc := {
  sl_file : string;
  sl_func : string;
  sl_lineno : nat;
}.

Record trans_write_data := {
  twd_mo : write_memory_order;
  twd_phys_addr : u64;
  twd_val : u64;
}.

Record trans_read_data := {
  trd_phys_addr : u64;
  trd_val : u64;
}.

Record trans_tlbi_data := {
  ttd_tlbi_kind : tlbi_kind;
  ttd_page : u64;
  ttd_level : u64;
}.

Record trans_msr_data := {
  tmd_sysreg : ghost_sysreg_kind;
  tmd_val : u64;
}.

Record trans_hint_data := {
  thd_hint_kind : ghost_hint_kind;
  thd_location : u64;
  thd_value : u64;
}.

Inductive ghost_simplified_model_transition_data :=
|	GSMDT_TRANS_MEM_WRITE (write_data : trans_write_data)
|	GSMDT_TRANS_MEM_READ (read_data : trans_read_data)
|	GSMDT_TRANS_DSB (dsb_data : dsb_kind)
|	GSMDT_TRANS_ISB
|	GSMDT_TRANS_TLBI (tlbi_data : trans_tlbi_data)
|	GSMDT_TRANS_MSR (msr_data : trans_msr_data)
| GSMDT_TRANS_HINT (hint_data : trans_hint_data)
.

Record ghost_simplified_model_transition := {
  gsmt_src_loc : option src_loc;
  gsmt_thread_identifier : thread_identifier;
  gsmt_data : ghost_simplified_model_transition_data;
}.


(*****************************************************************************)
(********               Error reporting datastructures               *********)
(*****************************************************************************)

Inductive ghost_simplified_model_error :=
| GSME_bbm_valid_valid
| GSME_unimplemented
(* TODO: others, more info... *)
.

(* TODO: this type needs to be made nicer *)
Inductive ghost_simplified_model_step_result_data :=
| GSMSR_success (next : ghost_simplified_memory)
| GSMSR_failure (s : ghost_simplified_model_error).

(* TODO: this type needs to be made nicer *)
Record ghost_simplified_model_step_result := {
  gsmsr_log : list string;
  gsmsr_data : ghost_simplified_model_step_result_data
}.



(*****************************************************************************)
(********                   Code of the transitions                  *********)
(*****************************************************************************)


Definition Mreturn (st : ghost_simplified_memory) : ghost_simplified_model_step_result :=
  {| gsmsr_log := nil;
    gsmsr_data := GSMSR_success st |}.

Definition Mbind (r : ghost_simplified_model_step_result) (f : ghost_simplified_memory -> ghost_simplified_model_step_result) : ghost_simplified_model_step_result :=
  match r.(gsmsr_data) with
  | GSMSR_failure s => r
  | GSMSR_success st =>
    let st' := f st in
    {| gsmsr_log := app st'.(gsmsr_log) r.(gsmsr_log);
      gsmsr_data := st'.(gsmsr_data);
    |}
  end.

Definition Merror (s : ghost_simplified_model_error) : ghost_simplified_model_step_result :=
  {| gsmsr_log := nil;
    gsmsr_data := GSMSR_failure s |}.

Definition Mlog (s : string) (r : ghost_simplified_model_step_result) : ghost_simplified_model_step_result :=
  match r.(gsmsr_data) with
  | GSMSR_failure s =>
    (* TODO: or add to log? *)
    r
  | GSMSR_success st =>
    {| gsmsr_log := cons s r.(gsmsr_log);
      gsmsr_data := GSMSR_success st |}
  end.

Definition update_loc_val (loc : sm_location) (val : u64) (st : ghost_simplified_memory) : ghost_simplified_memory :=
  (* TODO: implement *)
  st.

Definition __read_phys (addr : u64) (pre : bool) (st : ghost_simplified_model_state) : u64 :=
  (* TODO: implement *)
  addr.

Definition read_phys_pre (addr : u64) (st : ghost_simplified_model_state) : u64 :=
  __read_phys addr true st.

(* TODO: move this *)
Definition PTE_BIT_VALID : u64 :=
  (* TODO: actually, should be 0000...0001 *)
  bv_0 64.

Definition is_desc_valid (descriptor : u64) : bool :=
  bool_decide ((bv_and descriptor PTE_BIT_VALID) = PTE_BIT_VALID).




Definition requires_bbm (loc : sm_location) (before after : u64) : bool :=
  (* TODO *)
  true.



Definition step_write_on_valid (tid : thread_identifier) (wmo : write_memory_order) (loc : sm_location) (val : u64) (st : ghost_simplified_memory) : ghost_simplified_model_step_result :=
  let old := loc.(sl_val) in
  if old =? val then
   {| gsmsr_log := []; gsmsr_data := GSMSR_success st |}
  else
    if is_desc_valid val then
      {| gsmsr_log := []; gsmsr_data := GSMSR_failure GSME_bbm_valid_valid |}
    else
    (
      let new_loc := loc <| sl_state := (SPS_STATE_PTE_INVALID_UNCLEAN {| ai_invalidator_tid := tid; ai_old_valid_desc :=  old; ai_lis := LIS_unguarded; |}) |> in
      {| gsmsr_log := []; 
      gsmsr_data := GSMSR_success (st <| gsm_memory := (<[ loc.(sl_phys_addr) := new_loc ]> st.(gsm_memory)) |> ) |}
    ).


Require Extraction.
Recursive Extraction step_write_on_valid.



Definition step_write (tid : thread_identifier) (wd : trans_write_data) (st : ghost_simplified_memory) : ghost_simplified_model_step_result :=
  (* TODO *)
  let wmo := wd.(twd_mo) in
  let val := wd.(twd_val) in
  match st.(gsm_memory) !! wd.(twd_phys_addr) with
    | Some (loc) =>
      if negb loc.(sl_is_pte) then
        let st' := update_loc_val loc val st (* TODO *) in
        {| gsmsr_log := nil;
          gsmsr_data := GSMSR_success st' |}
      else
        match loc.(sl_state) with
        | SPS_STATE_PTE_VALID av =>
            (step_write_on_valid tid wmo loc val st)
        |_ =>
          (* TODO: other cases *)
        {| gsmsr_log := nil;
          gsmsr_data := GSMSR_failure GSME_unimplemented |}
        end
    | None => 
      {| gsmsr_log := nil;
        gsmsr_data := GSMSR_failure GSME_unimplemented |}
  end.


(* TODO: actually do this *)
Definition step (trans : ghost_simplified_model_transition) (st : ghost_simplified_memory) : ghost_simplified_model_step_result :=
  match trans.(gsmt_data) with
  | GSMDT_TRANS_MEM_WRITE wd =>
    step_write trans.(gsmt_thread_identifier) wd st
  | _ => (* TODO: and so on... *)
    {| gsmsr_log := nil;
      gsmsr_data := GSMSR_failure GSME_unimplemented |}
  end.


Definition ghost_simplified_model_step (trans : ghost_simplified_model_transition) (st : ghost_simplified_memory) : ghost_simplified_model_step_result :=
  step trans st.

Definition __ghost_simplified_model_step_write (src_loc : src_loc) (tid : thread_identifier) (wmo : write_memory_order) (phys : phys_addr_t) (val : u64) :=
  ghost_simplified_model_step {|
    gsmt_src_loc := Some src_loc;
    gsmt_thread_identifier := tid;
    gsmt_data := GSMDT_TRANS_MEM_WRITE ({|
      twd_mo := wmo;
      twd_phys_addr := phys;
      twd_val := val;
    |})
  |}.
(* TODO: and all of its friends *)

(* TODO: continue *)


(* https://github.com/rems-project/linux/blob/pkvm-verif-6.4/arch/arm64/kvm/hyp/nvhe/ghost_simplified_model.c *)