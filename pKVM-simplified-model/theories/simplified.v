(** Simplified model *)
(* https://github.com/rems-project/linux/blob/pkvm-verif-6.4/arch/arm64/kvm/hyp/include/nvhe/ghost_simplified_model.h *)



Require Import String.
Require Import stdpp.bitvector.bitvector.
Require Import Cmap.cmap.

(* uses https://github.com/tchajed/coq-record-update *)
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Require Import stdpp.gmap.

Require Import Recdef.

(* This is to prevent non-bools from being used as bools *)
Notation "'if' C 'then' A 'else' B" :=
  (match C with
    | true => A
    | false => B
  end)
(at level 200, right associativity).

Definition u64 := bv 64.
Search (bv _ -> bv _ -> bool).

Definition _64 := 64%N.

Instance bv_64_eq_dec : EqDecision (bv 64) := @bv_eq_dec _64.
Instance bv_64_countable : Countable (bv 64) := @bv_countable _64.

Definition bv_add_64 := @bv_add _64.
Definition bv_mul_64 := @bv_mul _64.
Definition bv_mul_Z_64 := @bv_mul_Z _64.
Definition bv_shiftr_64 := @bv_shiftr _64.
Definition bv_shiftl_64 := @bv_shiftl _64.
Definition bv_and_64 := @bv_and _64.

Definition BV64 (n : Z) {p : BvWf 64 n} : u64 := BV 64 n.

Definition u64_eqb (x y : u64) : bool :=
  (bv_unsigned x =? bv_unsigned y)%Z.

Definition u64_ltb (x y : u64) : bool :=
  ((bv_unsigned x) <? (bv_unsigned y))%Z
.

Definition u64_lte (x y : u64) : bool :=
  ((bv_unsigned x) <=? (bv_unsigned y))%Z
.

Infix "b=?" := u64_eqb (at level 70).
Infix "b<?" := u64_ltb (at level 70).
Infix "b<=?" := u64_lte (at level 70).
Infix "b+" := bv_add_64 (at level 50).
Infix "b*" := bv_mul_64 (at level 40).

Infix "+s" := append (right associativity, at level 60).

Definition n512 := 512.

Definition b0 := BV64 0.
Definition b1 := BV64 1.
Definition b2 := BV64 2.
Definition b8 := BV64 8.
Definition b12 := BV64 12.
Definition b16 := BV64 16.
Definition b47 := BV64 47.
Definition b63 := BV64 63.
Definition b512 := BV64 512.
Definition b1023 := BV64 1023.

(*******************)
(* Numerical types *)
Inductive thread_identifier :=
| Thread_identifier : nat -> thread_identifier
.
Global Instance thread_identifier_eq_decision : EqDecision thread_identifier.
  Proof. solve_decision. Qed.


Inductive phys_addr_t :=
| Phys_addr : u64 -> phys_addr_t
.
Global Instance phys_addr_t_eq_decision : EqDecision phys_addr_t.
  Proof. solve_decision. Qed.

Definition phys_addr_val (root : phys_addr_t) : u64 :=
  match root with
    | Phys_addr r => r
  end
.
Definition pa_plus (a b : phys_addr_t) : phys_addr_t :=
  Phys_addr ((phys_addr_val a) b+ (phys_addr_val b))
.
Infix "pa+" := pa_plus (at level 50).
Definition pa_mul (a b : phys_addr_t) : phys_addr_t :=
  Phys_addr ((phys_addr_val a) b* (phys_addr_val b))
.
Infix "pa*" := pa_mul (at level 40).
Notation "<[ K := V ]> D" := (<[ bv_shiftr_64 (phys_addr_val K) (BV64 3%Z) := V ]> D) (at level 100).
Definition pa0 := Phys_addr b0.

Inductive owner_t :=
| Root : phys_addr_t -> owner_t
.
Global Instance owner_t_eq_decision : EqDecision owner_t.
  Proof. solve_decision. Qed.

Definition root_val (root : owner_t) : phys_addr_t :=
  match root with
    | Root r => r
  end
.

Inductive level_t :=
| l0
| l1
| l2
| l3
| lerror
.
Definition next_level (l : level_t) : level_t :=
  match l with
    | l0 => l1
    | l1 => l2
    | l2 => l3
    | l3 => lerror
    | lerror => lerror
  end
.
Definition is_l3 (l : level_t) : bool :=
  match l with
    | l3 => true
    | _ => false
  end
.
Global Instance level_t_eq_decision : EqDecision level_t.
  Proof. solve_decision. Qed.


(*****************************************************************************)
(********                Automaton definition                        *********)
(*****************************************************************************)

Inductive stage_t :=
  | S1
  | S2
.

Inductive LVS :=
  | LVS_unguarded
  | LVS_dsbed
  | LVS_dsb_csed
.

Record aut_valid := {
  lvs : list LVS;
}.

Inductive LIS :=
  | LIS_unguarded
  | LIS_dsbed
  | LIS_dsb_tlbi_all
  | LIS_dsb_tlbi_ipa
  | LIS_dsb_tlbied
  | LIS_dsb_tlbi_ipa_dsb
.

Record aut_invalid_unclean := mk_aut_invalid_unclean {
  ai_invalidator_tid : thread_identifier;
  ai_old_valid_desc : u64;
  ai_lis : LIS;
}.
#[export] Instance eta_aut_invalid_unclean : Settable _ := settable! mk_aut_invalid_unclean <ai_invalidator_tid; ai_old_valid_desc; ai_lis>.


Record aut_invalid_clean := {
  aic_invalidator_tid : thread_identifier;
}.

Inductive sm_pte_state :=
  | SPS_STATE_PTE_VALID (valid_state:aut_valid)
  | SPS_STATE_PTE_INVALID_UNCLEAN (invalid_unclean_state:aut_invalid_unclean)
  | SPS_STATE_PTE_INVALID_CLEAN (invalid_clean_state:aut_invalid_clean)
.

Record ghost_addr_range := {
  range_start : phys_addr_t;
  range_size : phys_addr_t;
}.

Record table_data_t := {
  next_level_table_addr : phys_addr_t;
}.

Record map_data_t := {
  oa_region : ghost_addr_range;
}.

Inductive pte_rec :=
  | PTER_PTE_KIND_TABLE (table_data:table_data_t)
  | PTER_PTE_KIND_MAP (map_data:map_data_t)
  | PTER_PTE_KIND_INVALID
.

Record ghost_exploded_descriptor := mk_ghost_exploded_descriptor {
  ged_ia_region : ghost_addr_range;
  ged_level : level_t;
  ged_stage : stage_t;
  ged_pte_kind : pte_rec;
  ged_state : sm_pte_state;
  (* address of the root of the PTE *)
  ged_owner : owner_t;
}.
#[export] Instance eta_ghost_exploded_descriptor : Settable _ := settable! mk_ghost_exploded_descriptor <ged_ia_region; ged_level; ged_stage; ged_pte_kind; ged_state; ged_owner>.



Record sm_location := mk_sm_location {
  (* sl_initialised : bool; *)
  sl_phys_addr : phys_addr_t;
  sl_val : u64;
  sl_pte : option ghost_exploded_descriptor;
}.
#[export] Instance eta_sm_location : Settable _ := settable! mk_sm_location < sl_phys_addr; sl_val; sl_pte>.

(* Do we need locks? *)
Record owner_locks := {
  ol_len : u64;
  ol_owner_ids : list owner_t;
  ol_locks : unit (* TODO??? *);
}.

(* The memory state is a map from address to simplified model location *)
Definition ghost_simplified_model_state := cmap sm_location.

(* The zalloc'd memory is stored here *)
Definition ghost_simplified_model_zallocd := gset u64.

(* the map from root to lock address *)
Definition ghost_simplified_model_lock_addr := gmap u64 u64.

(* the map from lock address to thread that acquired it if any *)
Definition ghost_simplified_model_lock_state := gmap u64 thread_identifier.

(* Storing roots for PTE walkthrough (we might need to distinguish S1 and S2 roots) *)
Record pte_roots := mk_pte_roots {
  pr_s1 : list owner_t;
  pr_s2 : list owner_t;
}.
#[export] Instance eta_pte_roots : Settable _ := settable! mk_pte_roots <pr_s1; pr_s2>.


Record ghost_simplified_memory := mk_ghost_simplified_model {
  gsm_roots : pte_roots;
  gsm_memory : ghost_simplified_model_state;
  gsm_zalloc : ghost_simplified_model_zallocd;
  gsm_lock_addr : ghost_simplified_model_lock_addr;
  gsm_lock_state : ghost_simplified_model_lock_state;
}.
#[export] Instance eta_ghost_simplified_memory : Settable _ := settable! mk_ghost_simplified_model <gsm_roots; gsm_memory; gsm_zalloc; gsm_lock_addr; gsm_lock_state>.



(*****************************************************************************)
(********               Transition definition                        *********)
(*****************************************************************************)


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
  |	GSMDT_TRANS_MEM_WRITE (write_data : trans_write_data)
  | GSMDT_TRANS_MEM_ZALLOC (zalloc_data : trans_zalloc_data)
  |	GSMDT_TRANS_MEM_READ (read_data : trans_read_data)
  |	GSMDT_TRANS_BARRIER (dsb_data : Barrier)
  |	GSMDT_TRANS_TLBI (tlbi_data : TLBI)
  |	GSMDT_TRANS_MSR (msr_data : trans_msr_data)
  | GSMDT_TRANS_HINT (hint_data : trans_hint_data)
  | GSMDT_TRANS_LOCK (lock_data : trans_lock_data)
.

Record ghost_simplified_model_transition := {
  gsmt_src_loc : option src_loc;
  gsmt_thread_identifier : thread_identifier;
  gsmt_data : ghost_simplified_model_transition_data;
  gsmt_id : nat;
}.


(*****************************************************************************)
(********               Error reporting datastructures               *********)
(*****************************************************************************)
Inductive violation_type :=
  | VT_valid_on_invalid_unclean
  | VT_valid_on_valid
  | VT_release_unclean
.

Inductive internal_error_type :=
  | IET_infinite_loop
  | IET_unexpected_none
.

Inductive ghost_simplified_model_error :=
  | GSME_bbm_violation : violation_type -> phys_addr_t -> ghost_simplified_model_error
  | GSME_not_a_pte : string -> phys_addr_t -> ghost_simplified_model_error
  | GSME_inconsistent_read
  | GSME_uninitialised : string -> phys_addr_t -> ghost_simplified_model_error
  | GSME_unclean_child : phys_addr_t -> ghost_simplified_model_error
  | GSME_double_use_of_pte
  | GSME_root_already_exists
  | GSME_unaligned_write
  | GSME_double_lock_aquire : thread_identifier -> thread_identifier -> ghost_simplified_model_error
  | GSME_transition_without_lock : phys_addr_t -> ghost_simplified_model_error
  | GSME_unimplemented
  | GSME_internal_error : internal_error_type -> ghost_simplified_model_error
.

Inductive result (A B: Type): Type
  := Ok (a: A) | Error (b: B).

Inductive log_element :=
  | Inconsistent_read : u64 -> u64 -> phys_addr_t -> log_element
  | Warning_read_write_non_allocd : phys_addr_t -> log_element
  | Warning_unsupported_TLBI
  | Log : string -> u64 -> log_element
.

Record ghost_simplified_model_result := mk_ghost_simplified_model_result {
  gsmsr_log : list log_element;
  gsmsr_data : result ghost_simplified_memory ghost_simplified_model_error
}.
#[export] Instance eta_ghost_simplified_model_result : Settable _ := settable! mk_ghost_simplified_model_result <gsmsr_log; gsmsr_data>.

(* Type used as input of the page table visitor function  *)
Record page_table_context := mk_page_table_context {
  ptc_state: ghost_simplified_memory;
  ptc_loc: option sm_location;
  ptc_partial_ia: phys_addr_t;
  ptc_addr: phys_addr_t;
  ptc_root: owner_t;
  ptc_level: level_t;
  ptc_stage: stage_t;
}.
#[export] Instance eta_page_table_context : Settable _ := settable! mk_page_table_context <ptc_state; ptc_loc; ptc_partial_ia; ptc_addr; ptc_root; ptc_level; ptc_stage>.


(*****************************************************************************)
(********                   Code of the transitions                  *********)
(*****************************************************************************)

Definition Mreturn (st : ghost_simplified_memory) : ghost_simplified_model_result :=
  {| gsmsr_log := nil;
    gsmsr_data := Ok _ _ st |}.

Definition Mbind (r : ghost_simplified_model_result) (f : ghost_simplified_memory -> ghost_simplified_model_result) : ghost_simplified_model_result :=
  match r.(gsmsr_data) with
  | Error _ _ s => r
  | Ok _ _ st =>
    let st' := f st in
    {| gsmsr_log := app st'.(gsmsr_log) r.(gsmsr_log);
      gsmsr_data := st'.(gsmsr_data);
    |}
  end.

Definition Merror (s : ghost_simplified_model_error) : ghost_simplified_model_result :=
  {| gsmsr_log := nil;
    gsmsr_data := Error _ _ s |}.

Definition Mlog (s : log_element) (r : ghost_simplified_model_result) : ghost_simplified_model_result :=
  r <|gsmsr_log := s :: r.(gsmsr_log) |>.


Definition Mupdate_state (updater : ghost_simplified_memory -> ghost_simplified_model_result) (st : ghost_simplified_model_result) : ghost_simplified_model_result :=
  match st with
    | {| gsmsr_log := logs; gsmsr_data := Ok _ _ st |} =>
      let new_st := updater st in
      new_st <| gsmsr_log := new_st.(gsmsr_log) ++ logs |>
    | e => e
  end
.

Definition insert_location (loc : sm_location) (st : ghost_simplified_memory) : ghost_simplified_memory :=
  (st <| gsm_memory := <[ loc.(sl_phys_addr) := loc ]> st.(gsm_memory) |>)
.

Definition Minsert_location (loc : sm_location) (mon : ghost_simplified_model_result) : ghost_simplified_model_result :=
  match mon with
    | {| gsmsr_log := logs; gsmsr_data := Ok _ _ st |} =>
      {|
        gsmsr_log := logs;
        gsmsr_data := Ok _ _ (insert_location loc st)
      |}
    | e => e
  end
.


(*****************************************************************************)
(********                   Code for bit-pattern                     *********)
(*****************************************************************************)

Definition PTE_BIT_VALID : u64 := b1. (* binary: 0001 *)

Definition PTE_BIT_TABLE : u64 := b2. (* binary: 0010 *)

Definition GENMASK (l r : u64) : u64 :=
(bv_and_64
  ((bv_not b0) ≪ r)
  ((bv_not b0) ≫ (bv_sub 63 l))
)%bv.
(**  0......0  1....1  0....0
  *  i zeros          j zeros
  *)

(* Definition PTE_BITS_ADDRESS : u64 := GENMASK b47 b12. *)
Definition PTE_BITS_ADDRESS : u64 := BV64 0xfffffffff000%Z.

(* Definition PTE_FIELD_UPPER_ATTRS_SW_MASK : u64 := GENMASK (BV 64 58) (BV 64 55). *)
Definition NOT_PTE_FIELD_UPPER_ATTRS_SW_MASK : u64 := BV64 0x7fffffffffffff%Z.

Definition is_desc_valid (descriptor : u64) : bool :=
  negb ((bv_and_64 descriptor PTE_BIT_VALID) b=? b0)
.

Definition OA_shift (level : level_t) : u64 :=
match level with
  | l1 => BV64 (12 + 9 + 9)
  | l2 => BV64 (12 + 9 )
  | l3 => b12
  | _ => b0  (* Should not happen*)
end
.

Definition mask_OA_shift (level : level_t) : u64 :=
  match level with
    | l1 => BV64 0xffffc0000000%Z
    | l2 => BV64 0xffffffe00000%Z
    | l3 => BV64 0xfffffffff000%Z
    | _ => BV64 0%Z (* Should not happen*)
  end
.


Definition map_size (level : level_t) : phys_addr_t :=
match level with
  | l0 => Phys_addr (BV64 0x8000000000%Z) (* bv_shiftl b512     (BV64 30) *) (* 512 Go *)
  | l1 => Phys_addr (BV64 0x0040000000%Z) (* bv_shiftl (b1)     (BV64 30) *) (* 1 Go *)
  | l2 => Phys_addr (BV64 0x0000200000%Z) (* bv_shiftl (b2)     (BV64 20) *) (* 2 Mo *)
  | l3 => Phys_addr (BV64 0x0000001000%Z) (* bv_shiftl (BV64 4) (BV64 10) *) (* 4 Ko *)
  | _ => pa0  (* Should not happen*)
end
.

Definition is_desc_table (descriptor : u64) (level : level_t) :=
  match level with
    | l3 => false
    | _ => (bv_and_64 descriptor PTE_BIT_TABLE) b=? PTE_BIT_TABLE
  end
.

Definition extract_table_address (pte_val : u64) : phys_addr_t :=
Phys_addr (bv_and_64 pte_val PTE_BITS_ADDRESS).

Definition extract_output_address (pte_val : u64) (level : level_t) :=
bv_and_64 pte_val (GENMASK b47 (OA_shift level))
.

Definition align_4k (addr : phys_addr_t) : phys_addr_t :=
  Phys_addr (bv_and_64 (phys_addr_val addr) (BV64 0xfffffffffffffc00%Z) (* bv_not b1023 *))
.

Definition is_zallocd (st : ghost_simplified_memory) (addr : phys_addr_t) : bool :=
  bool_decide ((bv_shiftr_64 (phys_addr_val addr) b12) ∈ st.(gsm_zalloc))
.

Definition get_location (st : ghost_simplified_memory) (addr : phys_addr_t) : option sm_location :=
  match st.(gsm_memory) !! bv_shiftr_64 (phys_addr_val addr) 3 with
    | Some loc => Some loc
    | None =>
      match is_zallocd st addr with
        | true => Some {| sl_phys_addr := addr; sl_val := b0; sl_pte := None; |}
        | false => None
      end
  end
.

Infix "!!" := get_location (at level 20) .


Definition is_well_locked (cpu : thread_identifier) (location : phys_addr_t) (st : ghost_simplified_memory) : bool :=
  match st !! location with
    | None => true
    | Some location =>
      match location.(sl_pte) with
        | None => true
        | Some pte =>
          match lookup (phys_addr_val (root_val pte.(ged_owner))) st.(gsm_lock_addr) with
            | None => false
            | Some addr =>
              match lookup addr st.(gsm_lock_state) with
                | Some lock_owner => bool_decide (lock_owner = cpu)
                | None => false
              end
          end
      end
  end
.

(******************************************************************************************)
(*                             Page table traversal                                       *)
(******************************************************************************************)

Definition initial_state (partial_ia : phys_addr_t) (desc : u64) (level : level_t) (cpu_id : thread_identifier) (pte_kind : pte_rec) (stage : stage_t) : sm_pte_state :=
  match pte_kind with
    | PTER_PTE_KIND_INVALID =>
      SPS_STATE_PTE_INVALID_CLEAN ({|aic_invalidator_tid := cpu_id |})
    | PTER_PTE_KIND_MAP _ | PTER_PTE_KIND_TABLE _ =>
      SPS_STATE_PTE_VALID {|lvs := [] |}
  end
.

Definition deconstruct_pte (cpu_id : thread_identifier) (partial_ia : phys_addr_t) (desc : u64) (level : level_t) (root : owner_t) (stage : stage_t) : ghost_exploded_descriptor :=
  let pte_kind :=
    if is_desc_valid desc then
      if is_desc_table desc level then
        PTER_PTE_KIND_TABLE (
          {|
            next_level_table_addr := extract_table_address desc;
          |}
        )
      else
        PTER_PTE_KIND_MAP (
          {|
            oa_region := {| range_start := extract_table_address desc; range_size := map_size level |}
          |}
        )
    else
      PTER_PTE_KIND_INVALID
  in
  {|
    ged_ia_region :=
      {|
        range_start := partial_ia; (* It is already conveniently aligned *)
        range_size := map_size level (* The mapped (or partially mapped) region only depends on the level *)
      |};
    ged_level := level;
    ged_stage := stage;
    ged_pte_kind := pte_kind;
    ged_state := initial_state partial_ia desc level cpu_id pte_kind stage;
    ged_owner := root;
  |}
.

Fixpoint traverse_pgt_from_aux (root : owner_t) (table_start partial_ia : phys_addr_t) (level : level_t) (stage : stage_t) (visitor_cb : page_table_context -> ghost_simplified_model_result)  (max_call_number : nat) (mon : ghost_simplified_model_result) : ghost_simplified_model_result :=
  match max_call_number with
   | S max_call_number => traverse_pgt_from_offs root table_start partial_ia level stage visitor_cb b0 max_call_number mon
   | O => (* Coq typechecking needs a guarantee that the function terminates, that is why the max_call_number nat exists,
            the number of recursive calls is bounded. *)
   {| gsmsr_log := [] ; gsmsr_data := Error _ _ (GSME_internal_error IET_infinite_loop) |}
  end
  (* This is the for loop that iterates over all the entries of a page table *)
with traverse_pgt_from_offs (root : owner_t) (table_start partial_ia : phys_addr_t) (level : level_t) (stage : stage_t) (visitor_cb : page_table_context -> ghost_simplified_model_result) (i : u64) (max_call_number : nat) (mon : ghost_simplified_model_result) : ghost_simplified_model_result :=
  match max_call_number with
    | S max_call_number =>
      if i b=? b512 then
        (* We are done with this page table *)
        mon
      else
        match mon with
          | {| gsmsr_log := _; gsmsr_data := Error _ _ _ |}  => mon (* If it fails, it fails *)
          | {| gsmsr_log := _; gsmsr_data := Ok _ _ st |} as mon =>
            let addr := table_start pa+ (Phys_addr (b8 b* i)) in
            let location := st !! addr in
            let visitor_state_updater s := (* We construct the context, we don't know if the location exists but the visitor might create it *)
              visitor_cb
              {|
                ptc_state := s;
                ptc_loc := location;
                ptc_addr := addr;
                ptc_partial_ia := partial_ia;
                ptc_root := root;
                ptc_level:= level;
                ptc_stage := stage;
              |}
            in
            let mon := Mupdate_state visitor_state_updater mon in
            match mon.(gsmsr_data) with (* The visitor can edit the state and write logs *)
              | Error _ _ r  => mon (* If it fails, it fails *)
              | Ok _ _ updated_state =>
                let location := updated_state !! addr in
                match location with
                  | None => mon (* If the page table was not initialised, we cannot continue (or we could ignore this and continue.) *)
                  | Some location =>
                    let exploded_desc :=
                      match location.(sl_pte) with
                        | Some pte => pte
                        | None => (* 0 is a placeholder, we do not use it afterwards *)
                          deconstruct_pte (Thread_identifier 0) partial_ia location.(sl_val) level root stage
                      end
                    in
                    let mon :=
                      (* if it is a valid descriptor, recursively call pgt_traversal_from, otherwise, continue *)
                      match exploded_desc.(ged_pte_kind) with
                        | PTER_PTE_KIND_TABLE table_data =>
                          (* If it is a page table descriptor, we we traverse the sub-page table *)
                          let rec_table_start := table_data.(next_level_table_addr) in
                          let next_partial_ia := exploded_desc.(ged_ia_region).(range_start) pa+ (((Phys_addr i) pa* exploded_desc.(ged_ia_region).(range_size))) in
                          (* recursive call: explore sub-pgt *)
                          traverse_pgt_from_aux root rec_table_start next_partial_ia (next_level level) stage visitor_cb max_call_number mon
                        | _ => mon
                      end
                    in
                    traverse_pgt_from_offs root table_start partial_ia level stage visitor_cb (bv_add_64 i b1)  max_call_number mon
                end
            end
        end
    | O => {| gsmsr_log := []; gsmsr_data := Error _ _ (GSME_internal_error IET_infinite_loop) |}
  end
.

Definition traverse_pgt_from (root : owner_t) (table_start partial_ia : phys_addr_t) (level : level_t) (stage : stage_t) (visitor_cb : page_table_context -> ghost_simplified_model_result) (st : ghost_simplified_memory) : ghost_simplified_model_result :=
  traverse_pgt_from_aux root table_start partial_ia level stage visitor_cb (4*n512) (Mreturn st)
.

Definition traverse_pgt_from_root (root : owner_t) (stage : stage_t) (visitor_cb : page_table_context -> ghost_simplified_model_result) (st : ghost_simplified_memory) : ghost_simplified_model_result :=
  traverse_pgt_from root (root_val root) pa0 l0 stage visitor_cb st
.

(* Generic function (for s1 and s2) to traverse all page tables starting with root in roots *)
Fixpoint traverse_si_pgt_aux (visitor_cb : page_table_context -> ghost_simplified_model_result) (stage : stage_t) (roots : list owner_t) (st : ghost_simplified_model_result) : ghost_simplified_model_result :=
  match roots with
    | r :: q =>
      (* If the state is failed, there is no point in going on *)
      match st.(gsmsr_data) with
        | Error _ _ _ => st
        | _ =>
          let st := Mupdate_state (traverse_pgt_from r (root_val r) pa0 l0 stage visitor_cb) st in
          traverse_si_pgt_aux visitor_cb stage q st
      end
    | [] => st
  end
.

(* Generic function to traverse all S1 or S2 roots *)
Definition traverse_si_pgt (st : ghost_simplified_memory) (visitor_cb : page_table_context -> ghost_simplified_model_result) (stage : stage_t) : ghost_simplified_model_result :=
  let roots :=
    match stage with
      | S2 => st.(gsm_roots).(pr_s2)
      | S1 => st.(gsm_roots).(pr_s1)
    end
  in
  traverse_si_pgt_aux visitor_cb stage roots {| gsmsr_log := nil; gsmsr_data := Ok _ _ st |}
.

Definition traverse_all_pgt (st: ghost_simplified_memory) (visitor_cb : page_table_context -> ghost_simplified_model_result) :=
  match traverse_si_pgt st visitor_cb S1 with
    | {|gsmsr_log := logs; gsmsr_data := Ok _ _ st|} =>
      let res := traverse_si_pgt st visitor_cb S2 in
      res <| gsmsr_log := res.(gsmsr_log) ++ logs |>
    | err => err
  end
.

(*******************************************************************)
(* Some generic walker functions to mark and unmark entries as PTE *)

Definition mark_cb (cpu_id : thread_identifier) (ctx : page_table_context) : ghost_simplified_model_result :=
  match ctx.(ptc_loc) with
    | Some location =>
      match location.(sl_pte) with
        | Some _ =>
          {| gsmsr_log := []; gsmsr_data := Error _ _ GSME_double_use_of_pte |}
        | None =>
          let new_descriptor := deconstruct_pte cpu_id ctx.(ptc_partial_ia) location.(sl_val) ctx.(ptc_level) ctx.(ptc_root) ctx.(ptc_stage) in
          let new_location :=  (location <| sl_pte := (Some new_descriptor) |>) in
          let new_state := ctx.(ptc_state) <| gsm_memory := <[ location.(sl_phys_addr) := new_location]> ctx.(ptc_state).(gsm_memory) |> in
          Mreturn new_state
      end
    | None =>  (* In the C model, it is not an issue memory can be read, here we cannot continue because we don't have the value at that memory location *)
        {|
          gsmsr_log := [];
          gsmsr_data := Error _ _ (GSME_uninitialised "mark_cb" ctx.(ptc_addr))
        |}
  end
.

Definition unmark_cb (cpu_id : thread_identifier) (ctx : page_table_context) : ghost_simplified_model_result :=
  match ctx.(ptc_loc) with
    | Some location =>
      match location.(sl_pte) with
        | Some desc =>
          let new_loc := location <|sl_pte := None |> in
          let new_st := <[ location.(sl_phys_addr) := new_loc ]> ctx.(ptc_state).(gsm_memory) in
          {| gsmsr_log := nil; gsmsr_data := Ok _ _ (ctx.(ptc_state) <| gsm_memory := new_st |>) |}
        | None =>
          {| gsmsr_log := []; gsmsr_data := Error _ _ (GSME_not_a_pte "unmark_cb"%string ctx.(ptc_addr)) |}
      end
    | None =>  (* In the C model, it is not an issue memory can be read, here we cannot continue because we don't have the value at that memory location *)
        {|
          gsmsr_log := [];
          gsmsr_data := Error _ _ (GSME_uninitialised "unmark_cb" ctx.(ptc_addr))
        |}
  end
.

(******************************************************************************************)
(*                             Code for write                                             *)
(******************************************************************************************)
(* Visiting a page table fails with this visitor iff the visited part has an uninitialized or invalid unclean entry *)
Definition clean_reachable (ctx : page_table_context) : ghost_simplified_model_result :=
  match ctx.(ptc_loc) with
    | None => Merror (GSME_uninitialised "clean_reachable" ctx.(ptc_addr))
    | Some location =>
      match location.(sl_pte) with
        | None => Mreturn ctx.(ptc_state)
        | Some descriptor =>
          match descriptor.(ged_state) with
            | SPS_STATE_PTE_INVALID_UNCLEAN _ =>
              Merror (GSME_unclean_child ctx.(ptc_addr))
            | _ => Mreturn ctx.(ptc_state)
          end
      end
  end
.

Definition step_write_on_invalid (tid : thread_identifier) (wmo : write_memory_order) (loc : sm_location) (val : u64) (st : ghost_simplified_memory) : ghost_simplified_model_result :=
  (* If the location is a PTE table, tests if its children are clean *)
  match loc.(sl_pte) with
    | None => (* This should not happen because if we write on invalid, we write on PTE *)
      Merror (GSME_internal_error IET_unexpected_none)
    | Some descriptor =>
      (* TODO: save old descriptor *)
      let descriptor := deconstruct_pte tid descriptor.(ged_ia_region).(range_start) val descriptor.(ged_level) descriptor.(ged_owner) descriptor.(ged_stage) in
      let new_loc := loc <| sl_val := val |> <| sl_pte := Some descriptor |> in
      let st := st <| gsm_memory := <[ loc.(sl_phys_addr) := new_loc ]> st.(gsm_memory) |> in
      if is_desc_valid val then
        (* Tests if the page table is well formed *)
        match descriptor.(ged_pte_kind) with
          | PTER_PTE_KIND_TABLE map =>
            let
              st := traverse_pgt_from descriptor.(ged_owner) map.(next_level_table_addr) descriptor.(ged_ia_region).(range_start) (next_level descriptor.(ged_level)) descriptor.(ged_stage) clean_reachable st
            in
            let st := Mlog (Log "BBM: invalid clean->valid"%string (phys_addr_val loc.(sl_phys_addr))) st in
            (* If it is well formed, mark its children as page tables, otherwise, return the same error *)
            Mupdate_state (traverse_pgt_from descriptor.(ged_owner) map.(next_level_table_addr) descriptor.(ged_ia_region).(range_start) (next_level descriptor.(ged_level)) descriptor.(ged_stage) (mark_cb tid)) st
          | _ => Mreturn st
        end
      else
        (* if the descriptor is invalid, do nothing *)
        Mreturn st
  end
  (* Question: In the C model, the LVS status is updated for each CPU but never used, what should the Coq model do? *)
.

Definition step_write_on_invalid_unclean (tid : thread_identifier) (wmo : write_memory_order) (loc : sm_location) (val : u64) (st : ghost_simplified_memory) : ghost_simplified_model_result :=
  (* Only invalid descriptor are allowed *)
  if is_desc_valid val then
    (Merror (GSME_bbm_violation VT_valid_on_invalid_unclean loc.(sl_phys_addr)))
  else
    Mreturn (st <|gsm_memory := <[loc.(sl_phys_addr) := loc <|sl_val := val|> ]> st.(gsm_memory) |>)
.

Definition is_only_update_to_sw_bit (old new : u64) : bool :=
  (bv_and_64 old NOT_PTE_FIELD_UPPER_ATTRS_SW_MASK)
b=?
  (bv_and_64 new NOT_PTE_FIELD_UPPER_ATTRS_SW_MASK)
.

Definition require_bbm (tid : thread_identifier) (loc : sm_location) (val : u64) : option bool :=
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

Definition step_write_on_valid (tid : thread_identifier) (wmo : write_memory_order) (loc : sm_location) (val : u64) (st : ghost_simplified_memory) : ghost_simplified_model_result :=
  let old := loc.(sl_val) in
  if is_desc_valid val then
    match require_bbm tid loc val with (* If no change in memory: no problem*)
      | None => Merror (GSME_internal_error IET_unexpected_none)
      | Some false =>
          (* if the location des not require BBM, then we can update the value and the descriptor *)
          match loc.(sl_pte) with
            | None => (* This does not make sense because function is called on a pgt *)
              {| gsmsr_log := []; gsmsr_data := Error _ _ (GSME_internal_error IET_unexpected_none) |}
            | Some pte =>
              let loc := loc <| sl_val := val |>
                <| sl_pte :=
                  Some (deconstruct_pte tid pte.(ged_ia_region).(range_start) val pte.(ged_level) pte.(ged_owner) pte.(ged_stage)) |>
              in
              Mreturn (insert_location loc st)
          end
      | Some true =>
        (* Changing the descriptor is illegal *)
        {| gsmsr_log := []; gsmsr_data := Error _ _ (GSME_bbm_violation VT_valid_on_valid loc.(sl_phys_addr)) |}
    end
  else
    (* Invalidation of pgt: changing the state to invalid unclean unguarded *)
    match loc.(sl_pte) with
      | None => (* This does not make sense because function is called on a pgt *)
        {| gsmsr_log := []; gsmsr_data := Error _ _ (GSME_internal_error IET_unexpected_none) |}
      | Some desc =>
        let new_desc := desc <| ged_state := (SPS_STATE_PTE_INVALID_UNCLEAN {| ai_invalidator_tid := tid; ai_old_valid_desc :=  old; ai_lis := LIS_unguarded; |}) |> in
        {|
          gsmsr_log := [Log "valid->invalid_unclean"%string (phys_addr_val loc.(sl_phys_addr))];
          gsmsr_data := Ok _ _ (st
            <| gsm_memory :=
              (<[ loc.(sl_phys_addr) := loc <|sl_pte := Some (new_desc)|> ]> st.(gsm_memory))
            |> );
        |}
    end
.

Definition step_write_aux (tid : thread_identifier) (wd : trans_write_data) (st : ghost_simplified_memory) : ghost_simplified_model_result :=
  let wmo := wd.(twd_mo) in
  let val := wd.(twd_val) in
  let addr := wd.(twd_phys_addr) in
  if negb ((bv_and_64 (phys_addr_val addr) 7) b=? b0)
    then Merror GSME_unaligned_write else
  if negb (is_well_locked tid addr st)
    then Merror (GSME_transition_without_lock addr) else
  match st !! addr with
    | Some (loc) =>
      match loc.(sl_pte) with
        | Some desc =>
          (* If we write to a page table, depending on its state, we update them  *)
          match desc.(ged_state) with
            | SPS_STATE_PTE_VALID av =>
                (step_write_on_valid tid wmo loc val st)
            | SPS_STATE_PTE_INVALID_CLEAN av =>
                (step_write_on_invalid tid wmo loc val st)
            | SPS_STATE_PTE_INVALID_UNCLEAN av =>
                (step_write_on_invalid_unclean tid wmo loc val st)
          end
        | None => (* If it is not a pte, we just update the value *)
          let new_loc := loc <| sl_val := val |> in
          {|
            gsmsr_log := nil;
            gsmsr_data :=
              Ok _ _ (
                st <| gsm_memory := <[ addr := new_loc ]> st.(gsm_memory) |>
              );
          |}
      end
    | None =>
      (* If the location has not been written to, it is not a pgt, just save its value *)
      {| gsmsr_log := [];
        gsmsr_data := Ok _ _ (
          st <| gsm_memory :=
            <[ addr :=
              {|
                sl_phys_addr := addr;
                sl_val := val;
                sl_pte := None;
              |}
            ]> st.(gsm_memory) |>
        ) |}
  end
.

Function step_write_page (tid : thread_identifier) (wd : trans_write_data) (mon : ghost_simplified_model_result) (offs : Z) {measure Z.abs_nat offs} : ghost_simplified_model_result :=
  if Zle_bool offs 0 then
    mon
  else
    let addr := wd.(twd_phys_addr) pa+ (Phys_addr (bv_mul_Z_64 (BV64 8) (offs - 1))) in
    let sub_wd :=
      {|
        twd_mo := WMO_plain;
        twd_phys_addr := addr;
        twd_val := wd.(twd_val);
      |}
    in
    let mon := Mupdate_state (step_write_aux tid sub_wd) mon in
    step_write_page tid wd mon (offs - 1)
.
Proof. lia. Qed.

Definition step_write (tid : thread_identifier) (wd : trans_write_data) (st : ghost_simplified_memory) : ghost_simplified_model_result :=
  match st !! wd.(twd_phys_addr) with
    | Some _ => id
    | None  => Mlog (Warning_read_write_non_allocd wd.(twd_phys_addr))
  end
  match wd.(twd_mo) with
    | WMO_plain | WMO_release => step_write_aux tid wd st
    | WMO_page => step_write_page tid wd (Mreturn st) 512
  end
.


(******************************************************************************************)
(*                             Code for zalloc                                            *)
(******************************************************************************************)

Definition step_zalloc_aux (addr : phys_addr_t) (st : ghost_simplified_model_result) : ghost_simplified_model_result :=
  let update s := {| gsmsr_log := nil; gsmsr_data := Ok _ _ (s <| gsm_zalloc := union {[ phys_addr_val addr ]} s.(gsm_zalloc) |>) |} in
  Mupdate_state update st
.

Fixpoint step_zalloc_all (addr : phys_addr_t) (st : ghost_simplified_model_result) (offs : phys_addr_t) (max : nat) : ghost_simplified_model_result :=
  match max with
    | O => st
    | S max =>
      let st := step_zalloc_aux (addr pa+ offs) st in
      step_zalloc_all addr st (offs pa+ (Phys_addr b1)) max
  end
.

Definition step_zalloc (zd : trans_zalloc_data) (st : ghost_simplified_memory) : ghost_simplified_model_result :=
  step_zalloc_all (Phys_addr (bv_shiftr_64 (phys_addr_val zd.(tzd_addr)) (b12))) {|gsmsr_log := nil; gsmsr_data := Ok _ _ st|} pa0 (Z.to_nat (bv_unsigned zd.(tzd_size)))
.


(******************************************************************************************)
(*                             Code for read                                              *)
(******************************************************************************************)

Definition step_read (tid : thread_identifier) (rd : trans_read_data) (st : ghost_simplified_memory) : ghost_simplified_model_result :=
  (* Test if the memory has been initialized (it might refuse acceptable executions, not sure if it is a good idea) and its content is consistent. *)
  match st !! rd.(trd_phys_addr) with
    | Some loc => if loc.(sl_val) b=? rd.(trd_val) then
      {| gsmsr_log := nil;
        gsmsr_data := (Ok _ _ st) |}  else
        let new_loc := loc <| sl_val := rd.(trd_val) |> in
      {| gsmsr_log :=
        [
          Inconsistent_read loc.(sl_val) rd.(trd_val) rd.(trd_phys_addr)
        ];
        gsmsr_data := (Ok _ _ (st <| gsm_memory := <[rd.(trd_phys_addr) := new_loc ]> st.(gsm_memory) |>)) |}
    | None =>
        let loc := {| sl_phys_addr := rd.(trd_phys_addr); sl_val := rd.(trd_val); sl_pte := None |} in
        let st := st <| gsm_memory := <[ rd.(trd_phys_addr) := loc ]> st.(gsm_memory) |> in
        {| gsmsr_log :=
            [Warning_read_write_non_allocd loc.(sl_phys_addr)];
            gsmsr_data := Ok _ _ st
        |}
  end
.

(******************************************************************************************)
(*                                      DSB                                               *)
(******************************************************************************************)
Definition dsb_visitor (kind : DxB) (cpu_id : thread_identifier) (ctx : page_table_context) : ghost_simplified_model_result :=
  match ctx.(ptc_loc) with
    | None => (* This case is not explicitly excluded by the C code, but we cannot do anything in this case. *)
      (* Question: should we ignore it and return the state? *)
      {| gsmsr_log := nil; gsmsr_data := Error _ _ (GSME_uninitialised "dsb_visitor"%string ctx.(ptc_addr)) |}
    | Some location =>
      let pte :=
        match location.(sl_pte) with
          | None => deconstruct_pte cpu_id ctx.(ptc_partial_ia) location.(sl_val) ctx.(ptc_level) ctx.(ptc_root) ctx.(ptc_stage)
          | Some pte => pte
        end
      in
      let new_pte :=
        match pte.(ged_state) with
          | SPS_STATE_PTE_INVALID_UNCLEAN sst =>
            (* DSB has an effect on invalid unclean state only *)
            if negb (bool_decide (sst.(ai_invalidator_tid) = cpu_id)) then
              pte (* If it is another CPU that did the invalidation, do noting*)
            else
              (* Otherwise, update the state invalid unclean sub-automaton *)
              match sst.(ai_lis) with
                | LIS_unguarded =>
                  pte <|ged_state := SPS_STATE_PTE_INVALID_UNCLEAN (sst <|ai_lis := LIS_dsbed |>) |>
                | LIS_dsbed => pte
                | LIS_dsb_tlbied =>
                  match kind.(DxB_domain) with
                    | MBReqDomain_InnerShareable | MBReqDomain_FullSystem =>
                      pte <|ged_state := SPS_STATE_PTE_INVALID_CLEAN {| aic_invalidator_tid := sst.(ai_invalidator_tid) |} |>
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
        end
      in
      (* then update state and return *)
      let new_loc := (location <| sl_pte := Some new_pte |>) in
      let new_state := ctx.(ptc_state) <| gsm_memory := <[ location.(sl_phys_addr) := new_loc ]> ctx.(ptc_state).(gsm_memory) |> in
      let log := (* Log "DSB on"%string (phys_addr_val new_loc.(sl_phys_addr)) :: *)
        match pte.(ged_state), new_pte.(ged_state) with
          | SPS_STATE_PTE_INVALID_UNCLEAN _ , SPS_STATE_PTE_INVALID_CLEAN _ =>
              [Log "invalid_unclean->invalid_clean"%string (phys_addr_val location.(sl_phys_addr))]
           | SPS_STATE_PTE_INVALID_UNCLEAN {| ai_lis := LIS_unguarded|} , SPS_STATE_PTE_INVALID_UNCLEAN {| ai_lis := _|} =>
                [Log "unguareded->dsbed"%string (phys_addr_val location.(sl_phys_addr))]
           | SPS_STATE_PTE_INVALID_UNCLEAN {| ai_lis := LIS_dsb_tlbi_ipa|} , SPS_STATE_PTE_INVALID_UNCLEAN {| ai_lis := _|} =>
                [Log "tlbied_ipa->tlbied_ipa_dsbed"%string (phys_addr_val location.(sl_phys_addr))]
          | _, _ => (* [Log "DSBed: " (phys_addr_val location.(sl_phys_addr))] *) nil
        end
        in
      {| gsmsr_log := log; gsmsr_data := Ok _ _ new_state |}
  end
.

Definition step_dsb (tid : thread_identifier) (dk : DxB) (st : ghost_simplified_memory) : ghost_simplified_model_result :=
  (* walk the pgt with dsb_visitor*)
  traverse_all_pgt st (dsb_visitor dk tid)
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

Definition is_last_level_only (d : TLBI_op_by_addr_data) : bool :=
  match d.(TOBAD_last_level_only) with
    | TLBILevel_Any => false
    | TLBILevel_Last => true
  end
.

Definition should_perform_tlbi (td : TLBI_intermediate) (ptc : page_table_context) : option bool :=
  match ptc.(ptc_loc) with
    | None => None (* does not happen because we call it in tlbi_visitor in which we test that the location is init *)
    | Some loc =>
      match loc.(sl_pte) with
        | None => None (* if the PTE is not initialised, it has not been used; TLBI has no effect *)
        | Some pte_desc =>
          match td.(TI_method) with
            | TLBI_by_input_addr d =>
              let tlbi_addr := bv_shiftl_64 (phys_addr_val d.(TOBAD_page)) 12 in
              let ia_start := pte_desc.(ged_ia_region).(range_start) in
              let ia_end := ia_start pa+ pte_desc.(ged_ia_region).(range_size) in
              (* TODO: check that this is correct *)
              if (is_leaf pte_desc.(ged_pte_kind)
                       && (phys_addr_val ia_start b<=? tlbi_addr)
                       && (tlbi_addr b<? phys_addr_val ia_end)) then
                Some false
              else if ((negb (is_l3 pte_desc.(ged_level))) && is_last_level_only d) then
                Some false
              else
                Some true
            | TLBI_by_addr_space _ => None
            | TLBI_by_addr_all => Some true
          end
      end
  end
.

Definition tlbi_invalid_unclean_unmark_children (cpu_id : thread_identifier) (loc : sm_location) (ptc : page_table_context) : ghost_simplified_model_result :=
  let pte := (* build the PTE if it is not done already *)
    match loc.(sl_pte) with
      | None => deconstruct_pte cpu_id ptc.(ptc_partial_ia) loc.(sl_val) ptc.(ptc_level) ptc.(ptc_root) ptc.(ptc_stage)
      | Some pte => pte
    end
  in
  let st := ptc.(ptc_state) in
  match pte.(ged_state) with
    | SPS_STATE_PTE_INVALID_UNCLEAN lis =>
      let old_desc := (* This uses the old descriptor to rebuild a fresh old descriptor *)
        deconstruct_pte cpu_id ptc.(ptc_partial_ia) lis.(ai_old_valid_desc) ptc.(ptc_level) ptc.(ptc_root) ptc.(ptc_stage)
      in
      match old_desc.(ged_pte_kind) with
        | PTER_PTE_KIND_TABLE table_data =>
          (* check if all children are reachable *)
          match traverse_pgt_from pte.(ged_owner) pte.(ged_ia_region).(range_start) pa0 pte.(ged_level) pte.(ged_stage) clean_reachable st with
            | {| gsmsr_log := logs; gsmsr_data:= Ok _ _ st|} =>
              (* If all children are clean, we can unmark them as PTE *)
              match traverse_pgt_from old_desc.(ged_owner) old_desc.(ged_ia_region).(range_start) pa0 old_desc.(ged_level) old_desc.(ged_stage) (unmark_cb cpu_id) st with
                | {| gsmsr_log := logs1; gsmsr_data := st|} => {|gsmsr_log :=  logs1 ++ logs; gsmsr_data := st |}
              end
            | e => e
          end
        | _ => {| gsmsr_log  := nil; gsmsr_data := Ok _ _ st |}
      end
    | _ => (* if it is not invalid unclean, the TLBI has no effect *)
      {| gsmsr_log := nil; gsmsr_data := Ok _ _ st |}
  end
.

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

Definition tlbi_visitor (cpu_id : thread_identifier) (td : TLBI_intermediate) (ptc : page_table_context) : ghost_simplified_model_result :=
  match ptc.(ptc_loc) with
    | None => (* Cannot do anything if the page is not initialized *)
      Merror (GSME_uninitialised "tlbi_visitor" ptc.(ptc_addr))
    | Some location =>
      (* Test if there is something to do *)
      match should_perform_tlbi td ptc with
        | None => Merror GSME_unimplemented
        | Some b =>
          if b then
            (* step_pte_on_tlbi: inlined *)
            match location.(sl_pte) with
              | None => Merror (GSME_internal_error IET_unexpected_none)
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
                        | None => Merror GSME_unimplemented
                        | Some new_substate =>
                          let log := 
                            match new_substate, ai.(ai_lis) with
                              | LIS_dsb_tlbied, LIS_dsbed => Mlog (Log "dsb'd->tlbied" (phys_addr_val ptc.(ptc_addr)))
                              | LIS_dsb_tlbi_ipa, LIS_dsbed => Mlog (Log "dsb'd->tlbied_ipa" (phys_addr_val ptc.(ptc_addr)))
                              | LIS_dsb_tlbied, LIS_dsb_tlbi_ipa_dsb => Mlog (Log "dsb_tlbi_ipa_dsbed->tlbied" (phys_addr_val ptc.(ptc_addr)))
                              | _, _ => id
                            end
                          in
                          (* Write the new sub-state in the global automaton *)
                          let new_loc := location <| sl_pte := Some (exploded_desc <|ged_state := SPS_STATE_PTE_INVALID_UNCLEAN (ai <| ai_lis := new_substate|>) |>)|> in
                          let new_mem := ptc.(ptc_state) <| gsm_memory := <[location.(sl_phys_addr) := new_loc]> ptc.(ptc_state).(gsm_memory)|> in
                          log
                          match new_substate with
                            | LIS_dsb_tlbied => tlbi_invalid_unclean_unmark_children cpu_id new_loc (ptc <| ptc_state := new_mem |> <|ptc_loc := Some new_loc|>)
                            | _ => Mreturn new_mem
                          end
                      end
                    else
                      Mreturn ptc.(ptc_state)
                  | _ => Mreturn ptc.(ptc_state)
                end
            end
          else (* In the case where the PTE is not affected by the TLBI, we do nothing *)
            {|gsmsr_log := nil; gsmsr_data := Ok _ _ ptc.(ptc_state) |}
      end
  end
.

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


Definition step_tlbi (tid : thread_identifier) (td : TLBI) (st : ghost_simplified_memory) : ghost_simplified_model_result :=
  match decode_tlbi td with
    | None => Merror GSME_unimplemented
    | Some decoded_TLBI =>
      match td.(TLBI_rec).(TLBIRecord_regime) with
        | Regime_EL2 =>
          (* traverse all s1 pages*)
          traverse_si_pgt st (tlbi_visitor tid decoded_TLBI) S1
        | Regime_EL10 =>
          (* traverse s2 pages *)
          traverse_si_pgt st (tlbi_visitor tid decoded_TLBI) S2
        | _ =>
          (* traverse all page tables and add a warning *)
          let res := traverse_all_pgt st (tlbi_visitor tid decoded_TLBI) in
          res <| gsmsr_log := Warning_unsupported_TLBI :: res.(gsmsr_log) |>
      end
  end
.


(******************************************************************************************)
(*                                  Step MSR                                              *)
(******************************************************************************************)

Fixpoint si_root_exists (root : owner_t) (roots : list owner_t) : bool :=
  match roots with
    | [] => false
    | t :: q => (bool_decide (t = root)) || (si_root_exists root q)
  end
.

Definition extract_si_root (val : u64) (stage : stage_t) : owner_t :=
  (* Does not depends on the S1/S2 level but two separate functions in C, might depend on CPU config *)
  Root (Phys_addr (bv_and_64 val (BV64 0xfffffffffffe%Z) (* GENMASK (b47) (b1) *)))
.

Definition register_si_root (tid : thread_identifier) (st : ghost_simplified_memory) (root : owner_t) (stage : stage_t) : ghost_simplified_model_result :=
  let other_root_list :=
    match stage with
      | S1 => pr_s2
      | S2 => pr_s1
    end st.(gsm_roots) in
  (* Check that the root does not already exist in the other root list*)
  if si_root_exists root other_root_list then
    {| gsmsr_log := nil; gsmsr_data := Error _ _ GSME_root_already_exists |}
  else
    (* Add the root to the list of roots*)
    let new_roots :=
      match stage with
        | S2 => st.(gsm_roots) <| pr_s2 := root :: st.(gsm_roots).(pr_s2) |>
        | S1 => st.(gsm_roots) <| pr_s1 := root :: st.(gsm_roots).(pr_s1) |>
      end
    in
    let new_st := st <| gsm_roots := new_roots |> in
    (* then mark all its children as PTE *)
    match root with
      | Root r => traverse_pgt_from root r pa0 l0 stage (mark_cb tid) new_st
    end
.

Definition step_msr (tid : thread_identifier) (md : trans_msr_data) (st : ghost_simplified_memory) : ghost_simplified_model_result :=
  let stage :=
    match md.(tmd_sysreg) with
      | SYSREG_TTBR_EL2 => S1
      | SYSREG_VTTBR => S2
    end
  in
  let root := extract_si_root md.(tmd_val) stage in
  (* The value written to TTRB is a root, it might be new. *)
  let roots :=
    match stage with
      | S2 =>  pr_s2
      | S1 => pr_s1
    end st.(gsm_roots)
  in
  if si_root_exists root (match stage with | S2 =>  pr_s2 | S1 => pr_s1 end st.(gsm_roots)) then
    Mreturn st (* If it is already known to be a root, do nothing, it has already been registered *)
  else
    (* Otherwise, register it *)
    register_si_root tid st root stage
.

(******************************************************************************************)
(*                                  Step hint                                             *)
(******************************************************************************************)

Definition step_hint_set_root_lock (root : owner_t) (addr : phys_addr_t) (st : ghost_simplified_memory) : ghost_simplified_model_result :=
    Mreturn (st <| gsm_lock_addr := insert (phys_addr_val (root_val root)) (phys_addr_val addr) st.(gsm_lock_addr)|>)
.

Function set_owner_root (phys : phys_addr_t) (root : owner_t) (st : ghost_simplified_memory) (logs : list log_element) (offs : Z) {measure Z.abs_nat offs} : ghost_simplified_model_result :=
  if Zle_bool offs 0 then
    {| gsmsr_log := logs; gsmsr_data := Ok _ _ st |}
  else
    let addr := phys pa+ (Phys_addr (bv_mul_Z_64 (BV64 8) (offs - 1))) in
    match st !! addr with
      | None =>
        {|
          gsmsr_log :=
            logs;
            gsmsr_data := Error _ _ (GSME_uninitialised "set_owner_root" addr)
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
        let new_state := st <|gsm_memory := <[ location.(sl_phys_addr) := new_loc ]> st.(gsm_memory) |> in
        set_owner_root phys root new_state logs (offs - 1)
    end
.
Set Warnings "-funind-cannot-build-inversion -funind-cannot-define-graph".
Proof. lia. Qed.
Set Warnings "funind-cannot-build-inversion funind-cannot-define-graph".

Definition step_release_cb (ctx : page_table_context) : ghost_simplified_model_result :=
    match ctx.(ptc_loc) with
    | None =>
      {|
        gsmsr_log := [];
        gsmsr_data := Error _ _ (GSME_uninitialised "step_release_cb"%string ctx.(ptc_addr))
      |}
    | Some location =>
      match location.(sl_pte) with
        | None =>
          {|
            gsmsr_log := [];
            gsmsr_data := Error _ _ (GSME_not_a_pte "release_cb" ctx.(ptc_addr))
          |}
        | Some desc =>
          match desc.(ged_state) with
            | SPS_STATE_PTE_INVALID_UNCLEAN _ =>
              {|
                gsmsr_log := [];
                gsmsr_data := Error _ _ (GSME_bbm_violation VT_release_unclean ctx.(ptc_addr))
              |}
            | _ => Mreturn ctx.(ptc_state)
          end
      end
  end
.


Fixpoint remove (x : owner_t) (l : list owner_t) : list owner_t :=
  match l with
    | nil => nil
    | y::tl => if bool_decide (x = y) then remove x tl else y::(remove x tl)
  end
.

Definition try_unregister_root (addr : owner_t) (cpu : thread_identifier) (st : ghost_simplified_memory) : ghost_simplified_model_result :=
  match st !! root_val addr with
    | None => Merror (GSME_internal_error IET_unexpected_none)
    | Some loc =>
      match loc.(sl_pte) with
        | None => Merror (GSME_internal_error IET_unexpected_none)
        | Some pte =>
          let new_roots :=
            match pte.(ged_stage) with
              | S2 => st.(gsm_roots) <| pr_s2 := remove addr st.(gsm_roots).(pr_s2) |>
              | S1 => st.(gsm_roots) <| pr_s1 := remove addr st.(gsm_roots).(pr_s1) |>
            end
          in
          let st := st <| gsm_roots := new_roots |> in
          traverse_pgt_from_root addr pte.(ged_stage) (unmark_cb cpu) st
      end
  end
.

Definition step_release_table (cpu : thread_identifier) (addr : owner_t) (st : ghost_simplified_memory) : ghost_simplified_model_result :=
  match st !! root_val addr with
    | None =>
      {|
        gsmsr_log := [];
        gsmsr_data := Error _ _ (GSME_uninitialised "release"%string (root_val addr))
      |}
    | Some location =>
      match location.(sl_pte) with
        | None =>
          {|
            gsmsr_log := [];
            gsmsr_data := Error _ _ (GSME_not_a_pte "release"%string (root_val addr))
          |}
        | Some desc =>
          let st := traverse_pgt_from addr (root_val desc.(ged_owner)) desc.(ged_ia_region).(range_start) desc.(ged_level) desc.(ged_stage) step_release_cb st in
          Mupdate_state (try_unregister_root (addr) cpu) st
      end
  end
.

Definition step_hint (cpu : thread_identifier) (hd : trans_hint_data) (st : ghost_simplified_memory) : ghost_simplified_model_result :=
  match hd.(thd_hint_kind) with
    | GHOST_HINT_SET_ROOT_LOCK =>
      (* The types are weird here because of the order is reversed from SET_OWNER_ROOT (the root is first and the address second) *)
      step_hint_set_root_lock (Root hd.(thd_location)) (root_val hd.(thd_value)) st
      (* AFAIK, this only affects the internal locking discipline of the C simplified model and does nothing on the Coq version *)
    | GHOST_HINT_SET_OWNER_ROOT =>
      (* When ownership is transferred *)
      (* Not sure about the size of the iteration *)
      set_owner_root (align_4k hd.(thd_location)) hd.(thd_value) st [] 512
    | GHOST_HINT_RELEASE =>
      (* Can we use the free to detect when page tables are released? *)
      step_release_table cpu (Root hd.(thd_location)) st
  end
.


(******************************************************************************************)
(*                                  Step lock                                             *)
(******************************************************************************************)

Definition step_lock (cpu : thread_identifier) (hd : trans_lock_data) (st : ghost_simplified_memory) : ghost_simplified_model_result :=
  match hd.(tld_kind), lookup (phys_addr_val hd.(tld_addr)) st.(gsm_lock_state) with
    | LOCK, None => Mreturn (st <| gsm_lock_state := insert (phys_addr_val hd.(tld_addr)) cpu st.(gsm_lock_state) |>)
    | UNLOCK, Some thread =>
        if bool_decide (thread = cpu) then 
          Mreturn (st <| gsm_lock_state := delete (phys_addr_val hd.(tld_addr)) st.(gsm_lock_state) |>)
        else
          Merror (GSME_double_lock_aquire cpu thread)
    | LOCK, Some thread => Merror (GSME_double_lock_aquire cpu thread)
    | UNLOCK, None => Merror (GSME_double_lock_aquire cpu cpu)
  end
.


(******************************************************************************************)
(*                             Toplevel function                                          *)
(******************************************************************************************)

Definition step (trans : ghost_simplified_model_transition) (st : ghost_simplified_memory) : ghost_simplified_model_result :=
  match trans.(gsmt_data) with
  | GSMDT_TRANS_MEM_WRITE wd =>
    step_write trans.(gsmt_thread_identifier) wd st
  | GSMDT_TRANS_MEM_ZALLOC zd => step_zalloc zd st
  | GSMDT_TRANS_MEM_READ rd =>
    step_read trans.(gsmt_thread_identifier) rd st
  | GSMDT_TRANS_BARRIER ( Barrier_DSB dsb_data) =>
    step_dsb trans.(gsmt_thread_identifier) dsb_data st
  | GSMDT_TRANS_BARRIER (_) => {| gsmsr_log := nil; gsmsr_data := Ok _ _ st|} (* Ignored *)
  | GSMDT_TRANS_TLBI tlbi_data => step_tlbi trans.(gsmt_thread_identifier) tlbi_data st
  | GSMDT_TRANS_MSR msr_data => step_msr trans.(gsmt_thread_identifier) msr_data st
  | GSMDT_TRANS_HINT hint_data => step_hint trans.(gsmt_thread_identifier) hint_data st
  | GSMDT_TRANS_LOCK lock_data => step_lock trans.(gsmt_thread_identifier) lock_data st
  end.


Fixpoint all_steps_aux (transitions : list ghost_simplified_model_transition) (logs : list log_element) (st : ghost_simplified_memory) : ghost_simplified_model_result :=
  match transitions with
    | [] => {| gsmsr_log := logs; gsmsr_data := Ok _ _ st; |}
    | h :: t =>
      match step h st with
        | {| gsmsr_log := logs1; gsmsr_data := Ok _ _ st |} => all_steps_aux t (logs1 ++ logs) st
        | {| gsmsr_log := logs1; gsmsr_data := Error _ _ f |} =>
            {| gsmsr_log := logs1 ++ logs; gsmsr_data := Error _ _ f; |}
      end
  end
.


Definition memory_0 := {|
  gsm_roots := {| pr_s1 := []; pr_s2 := []; |};
  gsm_memory := empty;
  gsm_zalloc := gset_empty;
  gsm_lock_addr := gmap_empty;
  gsm_lock_state := gmap_empty;
|}.

Definition all_steps (transitions : list ghost_simplified_model_transition) : ghost_simplified_model_result :=
  let
    initial_state := memory_0
  in
  let res := all_steps_aux transitions [] initial_state in
  res <| gsmsr_log := rev res.(gsmsr_log) |>
.




(* https://github.com/rems-project/linux/blob/pkvm-verif-6.4/arch/arm64/kvm/hyp/nvhe/ghost_simplified_model.c *)
