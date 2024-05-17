(** Simplified model *)
(* https://github.com/rems-project/linux/blob/pkvm-verif-6.4/arch/arm64/kvm/hyp/include/nvhe/ghost_simplified_model.h *)



Require Import String.
Require Import stdpp.bitvector.bitvector.

(* uses https://github.com/tchajed/coq-record-update *)
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Require Import stdpp.gmap.

Require Import Recdef.


Definition u64 := bv 64.
Search (bv _ -> bv _ -> bool).
Definition u64_eqb (x y : u64) : bool :=
  bool_decide (x = y).

Definition u64_ltb (x y : u64) : bool :=
  ((bv_unsigned x) <? (bv_unsigned y))%Z
.

Definition u64_lte (x y : u64) : bool :=
  ((bv_unsigned x) <=? (bv_unsigned y))%Z
.

Infix "b=?" := u64_eqb (at level 70).
Infix "b<?" := u64_ltb (at level 70).
Infix "b<=?" := u64_lte (at level 70).
Infix "b+" := bv_add (at level 50).
Infix "b*" := bv_mul (at level 40).

Infix "+s" := append (right associativity, at level 60).

Definition n512 := 512.

Definition b0 := BV 64 0.
Definition b1 := BV 64 1.
Definition b2 := BV 64 2.
Definition b8 := BV 64 8.
Definition b12 := BV 64 12.
Definition b16 := BV 64 16.
Definition b47 := BV 64 47.
Definition b63 := BV 64 63.
Definition b512 := BV 64 512.
Definition b1023 := BV 64 1023.

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
Notation "<[ K := V ]> D" := (<[ phys_addr_val K := V ]> D) (at level 100).
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
  ged_s2 : bool;
  ged_pte_kind : pte_rec;
  ged_state : sm_pte_state;
  (* address of the root of the PTE *)
  ged_owner : owner_t;
}.
#[export] Instance eta_ghost_exploded_descriptor : Settable _ := settable! mk_ghost_exploded_descriptor <ged_ia_region; ged_level; ged_s2; ged_pte_kind; ged_state; ged_owner>.



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
Definition ghost_simplified_model_state := gmap u64 sm_location.

(* The zalloc'd memory is stored here *)
Definition ghost_simplified_model_zallocd := gmap u64 unit.

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
}.
#[export] Instance eta_ghost_simplified_memory : Settable _ := settable! mk_ghost_simplified_model <gsm_roots; gsm_memory; gsm_zalloc>.



(*****************************************************************************)
(********               Transition definition                        *********)
(*****************************************************************************)


(* Inductive SecurityState := SS_NonSecure | SS_Root | SS_Realm | SS_Secure. *)
Inductive Regime := Regime_EL3 | Regime_EL30 | Regime_EL2 | Regime_EL20 | Regime_EL10.
Inductive Shareability := Shareability_NSH | Shareability_ISH | Shareability_OSH.

(***************************************)
(* TLBI *)
Inductive TLBIOp :=
  TLBIOp_DALL
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
  | TLBIOp_PAALL.

(* Inductive TLBILevel := TLBILevel_Any | TLBILevel_Last. *)

Record TLBIRecord  := {
    TLBIRecord_op : TLBIOp;
    (* TLBIRecord_from_aarch64 : bool; *)
    (* TLBIRecord_security : SecurityState; *)
    TLBIRecord_regime : Regime;
    (* TLBIRecord_vmid : bits 16; *)
    (* TLBIRecord_asid : bits 16; *)
    (* TLBIRecord_level : TLBILevel; *)
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
  TOBAD_last_level_only : bool;
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
  | MBReqDomain_FullSystem.


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
  | Barrier_SB : unit -> Barrier.

(* All those transitions will go in favor of ARM ISA description (except for hints) *)
Inductive write_memory_order :=
| WMO_plain
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
|	SYSREG_VTTBR
|	SYSREG_TTBR_EL2
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

Inductive ghost_simplified_model_transition_data :=
|	GSMDT_TRANS_MEM_WRITE (write_data : trans_write_data)
| GSMDT_TRANS_MEM_ZALLOC (zalloc_data : trans_zalloc_data)
|	GSMDT_TRANS_MEM_READ (read_data : trans_read_data)
|	GSMDT_TRANS_BARRIER (dsb_data : Barrier)
|	GSMDT_TRANS_TLBI (tlbi_data : TLBI)
|	GSMDT_TRANS_MSR (msr_data : trans_msr_data)
| GSMDT_TRANS_HINT (hint_data : trans_hint_data)
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
| VT_realease_unclean
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
| GSME_unclean_child
| GSME_double_use_of_pte
| GSME_root_already_exists
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
Record page_table_context := {
  ptc_state: ghost_simplified_memory;
  ptc_loc: option sm_location;
  ptc_partial_ia: phys_addr_t;
  ptc_addr: phys_addr_t;
  ptc_root: owner_t;
  ptc_level: level_t;
  ptc_s2: bool;
}.

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


(*****************************************************************************)
(********                   Code for bit-pattern                     *********)
(*****************************************************************************)

Definition PTE_BIT_VALID : u64 := b1. (* binary: 0001 *)

Definition PTE_BIT_TABLE : u64 := b2. (* binary: 0010 *)

Definition GENMASK (h l : u64) : u64 :=
bv_and (bv_sub (bv_not b0) ((bv_shiftl b1 l) b+ b1))
(bv_shiftr (((bv_not b0))) (bv_sub b63 h)).
(**  0......0  1....1  0....0
  *  i zeros          j zeros
  *)

Definition PTE_BITS_ADDRESS : u64  := GENMASK b47 b12.

Definition is_desc_valid (descriptor : u64) : bool :=
  negb ((bv_and descriptor PTE_BIT_VALID) b=? b0)
.

Definition OA_shift (level : level_t) : u64 :=
match level with
  | l1 => BV 64 (12 + 9 + 9)
  | l2 => BV 64 (12 + 9 )
  | l3 => b12
  | _ => b0  (* Should not happen*)
end
.

Definition map_size (level : level_t) : phys_addr_t :=
match level with
  | l0 => Phys_addr (bv_shiftl b512 (BV 64 30)) (* 512 Go *)
  | l1 => Phys_addr (bv_shiftl (b1)   (BV 64 30)) (* 1 Go *)
  | l2 => Phys_addr (bv_shiftl (b12)   (BV 64 20)) (* 2 Mo *)
  | l3 => Phys_addr (bv_shiftl (BV 64 4)   (BV 64 10)) (* 4 Ko *)
  | _ => pa0  (* Should not happen*)
end
.

Definition is_desc_table (descriptor : u64) (level : level_t) :=
  match level with
    | l3 => false
    | _ => (bv_and descriptor PTE_BIT_TABLE) b=? PTE_BIT_TABLE
  end
.

Definition extract_table_address (pte_val : u64) : phys_addr_t :=
Phys_addr (bv_and pte_val PTE_BITS_ADDRESS).

Definition extract_output_address (pte_val : u64) (level : level_t) :=
bv_and pte_val (GENMASK b47 (OA_shift level))
.

Definition align_4k (addr : phys_addr_t) : phys_addr_t :=
  Phys_addr (bv_and (phys_addr_val addr) (bv_not b1023))
.

Definition is_zallocd (st : ghost_simplified_memory) (addr : phys_addr_t) : bool :=
  match st.(gsm_zalloc) !! (bv_shiftr (phys_addr_val addr) b12) with
    | Some () => true
    | None => false
  end
.

Definition get_location (st : ghost_simplified_memory) (addr : phys_addr_t) : option sm_location :=
  match st.(gsm_memory) !! phys_addr_val addr with
    | Some loc => Some loc
    | None =>
      match is_zallocd st addr with
        | true => Some {| sl_phys_addr := addr; sl_val := b0; sl_pte := None; |}
        | false => None
      end
  end
.

Infix "!!" := get_location (at level 20) .


(******************************************************************************************)
(*                             Page table traversal                                       *)
(******************************************************************************************)

Definition initial_state (partial_ia : phys_addr_t) (desc : u64) (level : level_t) (cpu_id : thread_identifier) (pte_kind : pte_rec) (s2 : bool) : sm_pte_state :=
  match pte_kind with
    | PTER_PTE_KIND_INVALID =>
      SPS_STATE_PTE_INVALID_CLEAN ({|aic_invalidator_tid := cpu_id |})
    | PTER_PTE_KIND_MAP _ | PTER_PTE_KIND_TABLE _ =>
      SPS_STATE_PTE_VALID {|lvs := [] |}
  end
.

Definition deconstruct_pte (cpu_id : thread_identifier) (partial_ia : phys_addr_t) (desc : u64) (level : level_t) (root : owner_t) (s2 : bool) : ghost_exploded_descriptor :=
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
    ged_s2 := s2;
    ged_pte_kind := pte_kind;
    ged_state := initial_state partial_ia desc level cpu_id pte_kind s2;
    ged_owner := root;
  |}
.

Fixpoint traverse_pgt_from_aux (root : owner_t) (table_start partial_ia : phys_addr_t) (level : level_t) (s2 : bool) (visitor_cb : page_table_context -> ghost_simplified_model_result)  (max_call_number : nat) (mon : ghost_simplified_model_result) : ghost_simplified_model_result :=
  match max_call_number with
   | S max_call_number => traverse_pgt_from_offs root table_start partial_ia level s2 visitor_cb b0 max_call_number mon
   | O => (* Coq typechecking needs a guarantee that the function terminates, that is why the max_call_number nat exists,
            the number of recursive calls is bounded. *)
   {| gsmsr_log := [] ; gsmsr_data := Error _ _ (GSME_internal_error IET_infinite_loop) |}
  end
  (* This is the for loop that iterates over all the entries of a page table *)
with traverse_pgt_from_offs (root : owner_t) (table_start partial_ia : phys_addr_t) (level : level_t) (s2 : bool) (visitor_cb : page_table_context -> ghost_simplified_model_result) (i : u64) (max_call_number : nat) (mon : ghost_simplified_model_result) : ghost_simplified_model_result :=
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
                ptc_s2 := s2;
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
                          deconstruct_pte (Thread_identifier 0) partial_ia location.(sl_val) level root s2
                      end
                    in
                    let mon :=
                      (* if it is a valid descriptor, recurisvely call pgt_traversal_from, otherwise, continue *)
                      match exploded_desc.(ged_pte_kind) with
                        | PTER_PTE_KIND_TABLE table_data =>
                          (* If it is a page table descriptor, we we traverse the sub-page table *)
                          let rec_table_start := table_data.(next_level_table_addr) in
                          let next_partial_ia := exploded_desc.(ged_ia_region).(range_start) pa+ (((Phys_addr i) pa* exploded_desc.(ged_ia_region).(range_size))) in
                          (* recursive call: explore sub-pgt *)
                          traverse_pgt_from_aux root rec_table_start next_partial_ia (next_level level) s2 visitor_cb max_call_number mon
                        | _ => mon
                      end
                    in
                    traverse_pgt_from_offs root table_start partial_ia level s2 visitor_cb (bv_add i b1)  max_call_number mon
                end
            end
        end
    | O => {| gsmsr_log := []; gsmsr_data := Error _ _ (GSME_internal_error IET_infinite_loop) |}
  end
.

Definition traverse_pgt_from (root : owner_t) (table_start partial_ia : phys_addr_t) (level : level_t) (s2 : bool) (visitor_cb : page_table_context -> ghost_simplified_model_result) (st : ghost_simplified_memory) : ghost_simplified_model_result :=
  traverse_pgt_from_aux root table_start partial_ia level s2 visitor_cb (4*n512) (Mreturn st)
.

Definition traverse_pgt_from_root (root : owner_t) (s2 : bool) (visitor_cb : page_table_context -> ghost_simplified_model_result) (st : ghost_simplified_memory) : ghost_simplified_model_result :=
  traverse_pgt_from root (root_val root) pa0 l0 s2 visitor_cb st
.

(* Generic function (for s1 and s2) to traverse all page tables starting with root in roots *)
Fixpoint traverse_si_pgt_aux (visitor_cb : page_table_context -> ghost_simplified_model_result) (s2 : bool) (roots : list owner_t) (st : ghost_simplified_model_result) : ghost_simplified_model_result :=
  match roots with
    | r :: q =>
      (* If the state is failed, there is no point in going on *)
      match st.(gsmsr_data) with
        | Error _ _ _ => st
        | _ =>
          let st := Mupdate_state (traverse_pgt_from r (root_val r) pa0 l0 s2 visitor_cb) st in
          traverse_si_pgt_aux visitor_cb s2 q st
      end
    | [] => st
  end
.

(* Generic function to traverse all S1 or S2 roots *)
Definition traverse_si_pgt (st : ghost_simplified_memory) (visitor_cb : page_table_context -> ghost_simplified_model_result) (s2 : bool) : ghost_simplified_model_result :=
  let roots :=
    if s2 then st.(gsm_roots).(pr_s2) else st.(gsm_roots).(pr_s1)
  in
  traverse_si_pgt_aux visitor_cb s2 roots {| gsmsr_log := nil; gsmsr_data := Ok _ _ st |}
.

Definition traverse_all_pgt (st: ghost_simplified_memory) (visitor_cb : page_table_context -> ghost_simplified_model_result) :=
  match traverse_si_pgt st visitor_cb true with
    | {|gsmsr_log := logs; gsmsr_data := Ok _ _ st|} =>
      let res := traverse_si_pgt st visitor_cb false in
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
          let new_descriptor := deconstruct_pte cpu_id ctx.(ptc_partial_ia) location.(sl_val) ctx.(ptc_level) ctx.(ptc_root) ctx.(ptc_s2) in
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
    | None => {| gsmsr_log := nil; gsmsr_data := Error _ _ GSME_unclean_child |}
    | Some location =>
      match location.(sl_pte) with
        | None => Mreturn ctx.(ptc_state)
        | Some descriptor =>
          match descriptor.(ged_state) with
            | SPS_STATE_PTE_INVALID_UNCLEAN _ =>
              Merror GSME_unclean_child
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
      let descriptor := deconstruct_pte tid descriptor.(ged_ia_region).(range_start) val descriptor.(ged_level) descriptor.(ged_owner) descriptor.(ged_s2) in
      let new_loc := loc <| sl_val := val |> <| sl_pte := Some descriptor |> in
      let st := st <| gsm_memory := <[ loc.(sl_phys_addr) := new_loc ]> st.(gsm_memory) |> in
      if is_desc_valid val then
        (* Tests if the page table is well formed *)
        match descriptor.(ged_pte_kind) with
          | PTER_PTE_KIND_TABLE map =>
            let
              st := traverse_pgt_from descriptor.(ged_owner) map.(next_level_table_addr) descriptor.(ged_ia_region).(range_start) descriptor.(ged_level) descriptor.(ged_s2) clean_reachable st
            in
            let st := Mlog (Log "BBM: invalid clean->valid"%string (phys_addr_val loc.(sl_phys_addr))) st in
            (* If it is well formed, mark its children as pagetables, otherwise, return the same error *)
            Mupdate_state (traverse_pgt_from descriptor.(ged_owner) map.(next_level_table_addr) descriptor.(ged_ia_region).(range_start) descriptor.(ged_level) descriptor.(ged_s2) (mark_cb tid)) st
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

Definition step_write_on_valid (tid : thread_identifier) (wmo : write_memory_order) (loc : sm_location) (val : u64) (st : ghost_simplified_memory) : ghost_simplified_model_result :=
  let old := loc.(sl_val) in
  if old b=? val then (* If no change in memory: no problem*)
   {| gsmsr_log := []; gsmsr_data := Ok _ _ st |}
  else
    if is_desc_valid val then
      (* Changing the descriptor is illegal *)
      {| gsmsr_log := []; gsmsr_data := Error _ _ (GSME_bbm_violation VT_valid_on_valid loc.(sl_phys_addr)) |}
    else
    (
      (* Invalidation of pgt: changing the state to  *)
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
    ).

Definition step_write (tid : thread_identifier) (wd : trans_write_data) (st : ghost_simplified_memory) : ghost_simplified_model_result :=
  let wmo := wd.(twd_mo) in
  let val := wd.(twd_val) in
  let addr := wd.(twd_phys_addr) in
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
      {| gsmsr_log := [Warning_read_write_non_allocd addr];
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
  end.

(******************************************************************************************)
(*                             Code for zalloc                                            *)
(******************************************************************************************)

Definition step_zalloc_aux (addr : phys_addr_t) (st : ghost_simplified_model_result) : ghost_simplified_model_result :=
  let update s := {| gsmsr_log := nil; gsmsr_data := Ok _ _ (s <| gsm_zalloc := <[ addr := () ]> s.(gsm_zalloc) |>) |} in
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
  step_zalloc_all (Phys_addr (bv_shiftr (phys_addr_val zd.(tzd_addr)) (b12))) {|gsmsr_log := nil; gsmsr_data := Ok _ _ st|} pa0 (Z.to_nat (bv_unsigned zd.(tzd_size)))
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
          | None => deconstruct_pte cpu_id ctx.(ptc_partial_ia) location.(sl_val) ctx.(ptc_level) ctx.(ptc_root) ctx.(ptc_s2)
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

Definition should_perform_tlbi (td : TLBI_intermediate) (ptc : page_table_context) : option bool :=
  match ptc.(ptc_loc) with
    | None => None (* does not happen because we call it in tlbi_visitor in which we test that the location is init *)
    | Some loc =>
      match loc.(sl_pte) with
        | None => Some false (* if the PTE is not initialised, it has not been used; TLBI has no effect *)
        | Some pte_desc =>
          match td.(TI_method) with
            | TLBI_by_input_addr d =>
              let tlbi_addr := bv_shiftr (phys_addr_val d.(TOBAD_page)) 12 in
              let ia_start := pte_desc.(ged_ia_region).(range_start) in
              let ia_end := ia_start pa+ (pte_desc.(ged_ia_region).(range_start)) in
              if negb (is_leaf pte_desc.(ged_pte_kind) && (phys_addr_val ia_start b<=? tlbi_addr) 
                       && (tlbi_addr b<=? phys_addr_val ia_end)) then
                Some false
              else if (is_l3 pte_desc.(ged_level) && d.(TOBAD_last_level_only)) then
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
      | None => deconstruct_pte cpu_id ptc.(ptc_partial_ia) loc.(sl_val) ptc.(ptc_level) ptc.(ptc_root) ptc.(ptc_s2)
      | Some pte => pte
    end
  in
  let st := ptc.(ptc_state) in
  match pte.(ged_state) with
    | SPS_STATE_PTE_INVALID_UNCLEAN lis =>
      let old_desc := (* This uses the old descriptor to rebuild a fresh old descriptor *)
        deconstruct_pte cpu_id ptc.(ptc_partial_ia) lis.(ai_old_valid_desc) ptc.(ptc_level) ptc.(ptc_root) ptc.(ptc_s2)
      in
      match old_desc.(ged_pte_kind) with
        | PTER_PTE_KIND_TABLE table_data =>
          (* check if all children are reachable *)
          match traverse_pgt_from pte.(ged_owner) pte.(ged_ia_region).(range_start) pa0 pte.(ged_level) pte.(ged_s2) clean_reachable st with
            | {| gsmsr_log := logs; gsmsr_data:= Ok _ _ st|} =>
              (* If all children are clean, we can unmark them as PTE *)
              match traverse_pgt_from old_desc.(ged_owner) old_desc.(ged_ia_region).(range_start) pa0 old_desc.(ged_level) old_desc.(ged_s2) (unmark_cb cpu_id) st with
                | {| gsmsr_log := logs1; gsmsr_data := st|} => {|gsmsr_log :=  logs1 ++ logs; gsmsr_data := st |}
              end
            | e => e
          end
        | _ => {| gsmsr_log := nil; gsmsr_data := Ok _ _ st |}
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
    | Regime_EL10 => None
    | Regime_EL2 =>
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
      if should_perform_tlbi td ptc then
        (* step_pte_on_tlbi: inlined *)
        match tlbi_invalid_unclean_unmark_children cpu_id location ptc with
          | {| gsmsr_log := log; gsmsr_data := Ok _ _ st|} as ret =>
            (* If it worked, then we update the invalid unclean sub-automaton *)
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
                          | a => Some a (* Otherwise, it does not make the subotomaton change *)
                        end
                      in
                      match new_substate with
                        | None => Merror GSME_unimplemented
                        | Some new_substate =>
                          (* Write the new sub-state in the global automaton *)
                          let new_loc := location <| sl_pte := Some (exploded_desc <|ged_state := SPS_STATE_PTE_INVALID_UNCLEAN (ai <| ai_lis := new_substate|>) |>)|> in
                          let new_mem := st <| gsm_memory := <[location.(sl_phys_addr) := new_loc]> st.(gsm_memory)|> in
                          ret <|gsmsr_data := Ok _ _ new_mem|>
                      end
                    else
                      ret
                  | _ => ret
                end
            end
          | e => e
        end
      else (* In the case where the PTE is not affected by the TLBI, we do nothing *)
        {|gsmsr_log := nil; gsmsr_data := Ok _ _ ptc.(ptc_state) |}
  end
.

Definition decode_tlbi (td : TLBI) : option TLBI_intermediate :=
  let stage := 
    match td.(TLBI_rec).(TLBIRecord_op) with
      | TLBIOp_VA | TLBIOp_VMALL =>
          Some TLBI_OP_stage1
      | TLBIOp_IPAS2  => Some TLBI_OP_stage1
      | TLBIOp_VMALLS12 | TLBIOp_ALL => Some TLBI_OP_both_stages
      | _ => None
    end
  in
  let shootdown :=
    match td.(TLBI_shareability) with
      | Shareability_ISH => Some true
      | _ => Some false
    end
  in
  let method :=
    match td.(TLBI_rec).(TLBIRecord_op) with
      | TLBIOp_VMALLS12 | TLBIOp_VMALL =>
        Some (TLBI_by_addr_space (Phys_addr b0)) (* TODO *)
      | TLBIOp_VA (* Also VAL? *) | TLBIOp_IPAS2 =>
        Some (
          TLBI_by_input_addr
            {| 
                TOBAD_page := (td.(TLBI_rec).(TLBIRecord_address));
                TOBAD_last_level_only :=
                  match td.(TLBI_rec).(TLBIRecord_regime), td.(TLBI_shareability) with
                    | Regime_EL2, Shareability_ISH => true
                    | _,_ => false
                  end;
            |}
        )
      | TLBIOp_ALL => Some TLBI_by_addr_all
      | _ => None (* TODO: fail *)
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
          traverse_si_pgt st (tlbi_visitor tid decoded_TLBI) true
        | Regime_EL10 =>
          (* traverse s2 pages *)
          traverse_si_pgt st (tlbi_visitor tid decoded_TLBI) false
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

Definition extract_si_root (val : u64) (s2 : bool) : owner_t :=
  (* Does not depends on the S1/S2 level but two separate functions in C, might depend on CPU config *)
  Root (Phys_addr (bv_and val (GENMASK (b47) (b1))))
.

Definition register_si_root (tid : thread_identifier) (st : ghost_simplified_memory) (root : owner_t) (s2 : bool) : ghost_simplified_model_result :=
  let other_root_levels := (if s2 then pr_s1 else pr_s2) st.(gsm_roots) in
  (* Check that the root does not already exist in the other root list*)
  if si_root_exists root other_root_levels then
    {| gsmsr_log := nil; gsmsr_data := Error _ _ GSME_root_already_exists |}
  else
    (* Add the root to the list of roots*)
    let new_roots :=
      if s2 then
        st.(gsm_roots) <| pr_s2 := root :: st.(gsm_roots).(pr_s2) |>
      else
        st.(gsm_roots) <| pr_s1 := root :: st.(gsm_roots).(pr_s1) |>
    in
    let new_st := st <| gsm_roots := new_roots |> in
    (* then mark all its children as PTE *)
    match root with
      | Root r => traverse_pgt_from root r pa0 l0 s2 (mark_cb tid) new_st
    end
.

Definition step_msr (tid : thread_identifier) (md : trans_msr_data) (st : ghost_simplified_memory) : ghost_simplified_model_result :=
  let s2 :=
    match md.(tmd_sysreg) with
      | SYSREG_TTBR_EL2 => true
      | SYSREG_VTTBR => false
    end
  in
  let root := extract_si_root md.(tmd_val) s2 in
  (* The value written to TTRB is a root, it might be new. *)
  if si_root_exists root ((if s2 then pr_s2 else pr_s1) st.(gsm_roots)) then
    Mreturn st (* If it is already known to be a root, do nothing, it has already been registered *)
  else
    (* Otherwise, register it *)
    register_si_root tid st root s2
.

(******************************************************************************************)
(*                                  Step hint                                             *)
(******************************************************************************************)

Function set_owner_root (phys : phys_addr_t) (root : owner_t) (st : ghost_simplified_memory) (logs : list log_element) (offs : Z) {measure Z.abs_nat offs} : ghost_simplified_model_result :=
  if Zle_bool offs 0 then
    {| gsmsr_log := logs; gsmsr_data := Ok _ _ st |}
  else
    let addr := phys pa+ (Phys_addr (bv_mul_Z (BV 64 8) (offs - 1))) in
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
Proof.
intros phys st offs location new_offs offs_pos. intro location0. intro x.
lia.
Qed.

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
                gsmsr_data := Error _ _ (GSME_bbm_violation VT_realease_unclean ctx.(ptc_addr))
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
            if pte.(ged_s2) then
              st.(gsm_roots) <| pr_s2 := remove addr st.(gsm_roots).(pr_s2) |>
            else
              st.(gsm_roots) <| pr_s1 := remove addr st.(gsm_roots).(pr_s1) |>
          in
          let st := st <| gsm_roots := new_roots |> in
          traverse_pgt_from_root addr pte.(ged_s2) (unmark_cb cpu) st
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
          let st := traverse_pgt_from addr (root_val desc.(ged_owner)) desc.(ged_ia_region).(range_start) desc.(ged_level) desc.(ged_s2) step_release_cb st in
          Mupdate_state (try_unregister_root (addr) cpu) st
      end
  end
.

Definition step_hint (cpu : thread_identifier) (hd : trans_hint_data) (st : ghost_simplified_memory) : ghost_simplified_model_result :=
  match hd.(thd_hint_kind) with
    | GHOST_HINT_SET_ROOT_LOCK => Mreturn st
      (* AFAIK, this only affects the internal locking discipline of the C simplified model and does nothing on the Coq version *)
    | GHOST_HINT_SET_OWNER_ROOT =>
      (* When ownership is transferred *)
      (* Not sure about the size of the iteration *)
      set_owner_root (align_4k hd.(thd_location)) hd.(thd_value) st [] 512
    | GHOST_HINT_RELEASE =>
      (* Can we use the free to detect when pagetables are released? *)
      step_release_table cpu (Root hd.(thd_location)) st
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

Definition all_steps (transitions : list ghost_simplified_model_transition) : ghost_simplified_model_result :=
  let
    initial_state :=  (* Initially, the memory is empty *)
      {|
        gsm_roots :=
          {|
            pr_s1 := [];
            pr_s2 := [];
          |};
        gsm_memory := gmap_empty;
        gsm_zalloc := gmap_empty;
      |}
  in
  let res := all_steps_aux transitions [] initial_state in
  res <| gsmsr_log := rev res.(gsmsr_log) |>
.


Definition memory_0 := {|
  gsm_roots := {| pr_s1 := []; pr_s2 := []; |};
  gsm_memory := gmap_empty;
  gsm_zalloc := gmap_empty;
|}.

(* We need to inspect the contents of the maps to print them. *)

Definition state_fold (A: Type) f z (m: ghost_simplified_model_state) :=
  gmap_fold A f z m.

Definition zallocd_fold (A: Type) f z (m: ghost_simplified_model_zallocd) :=
  gmap_fold A (fun k 'tt a => f k a) z m.

(* https://github.com/rems-project/linux/blob/pkvm-verif-6.4/arch/arm64/kvm/hyp/nvhe/ghost_simplified_model.c *)
