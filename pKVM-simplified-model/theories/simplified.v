(** Simplified model *)
(* https://github.com/rems-project/linux/blob/pkvm-verif-6.4/arch/arm64/kvm/hyp/include/nvhe/ghost_simplified_model.h *)



Require Import String.
Require Import stdpp.bitvector.bitvector.

(* uses https://github.com/tchajed/coq-record-update *)
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Require Import stdpp.gmap.


Definition u64 := bv 64.
Search (bv _ -> bv _ -> bool).
Definition u64_eqb (x y : u64) : bool :=
  bool_decide (x = y).

Definition u64_ltb (x y : u64) : bool := 
  Z.to_nat (bv_unsigned x) <? Z.to_nat (bv_unsigned y)
.

Infix "b=?" := u64_eqb (at level 70).
Infix "b<?" := u64_ltb (at level 70).
Infix "b+" := bv_add (at level 50).
Infix "b*" := bv_add (at level 40).

Definition phys_addr_t := u64.

Definition sm_owner_t := u64.

Definition thread_identifier := nat.



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

Record ghost_exploded_descriptor := mk_ghost_exploded_descriptor {
  ged_ia_region : ghost_addr_range;
  ged_level : u64;
  ged_s2 : bool;
  ged_pte_kind : pte_rec;
  ged_state : sm_pte_state;
  (* address of the root of the PTE *)
  ged_owner : sm_owner_t;
}.
#[export] Instance eta_ghost_exploded_descriptor : Settable _ := settable! mk_ghost_exploded_descriptor <ged_ia_region; ged_level; ged_s2; ged_pte_kind; ged_state; ged_owner>.



Record sm_location := mk_sm_location {
  (* sl_initialised : bool; *)
  sl_phys_addr : u64;
  sl_val : u64;
  sl_pte : option ghost_exploded_descriptor;
}.
#[export] Instance eta_sm_location : Settable _ := settable! mk_sm_location < sl_phys_addr; sl_val; sl_pte>.

(* Do we need locks? *)
Record owner_locks := {
  ol_len : u64;
  ol_owner_ids : list sm_owner_t;
  ol_locks : unit (* TODO??? *);
}.

(* The memory state is a map from address to simplified model location *)
Definition ghost_simplified_model_state := gmap u64 sm_location.

(* Storing roots for PTE walkthrough (we might need to distinguish S1 and S2 roots) *)
Record pte_roots := mk_pte_roots {
  pr_s1 : list u64;
  pr_s2 : list u64;
}.
#[export] Instance eta_pte_roots : Settable _ := settable! mk_pte_roots <pr_s1; pr_s2>.


Record ghost_simplified_memory := mk_ghost_simplified_model {
  gsm_roots : pte_roots;
  gsm_memory : ghost_simplified_model_state
}.
#[export] Instance eta_ghost_simplified_memory : Settable _ := settable! mk_ghost_simplified_model <gsm_roots; gsm_memory>.



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
| GSME_bbm_valid_valid (code_loc : option src_loc)
| GSME_bbm_invalid_valid (code_loc : option src_loc)
| GSME_use_of_uninitialized_pte (code_loc : option src_loc)
| GSME_inconsistent_read (code_loc : option src_loc)
| GSME_read_uninitialized (code_loc : option src_loc)
| GSME_writing_with_unclean_children (code_loc : option src_loc)
| GSME_double_use_of_pte (code_loc : option src_loc)
| GSME_unmark_non_pte (code_loc : option src_loc)
| GSME_root_already_exists (code_loc : option src_loc)
| GSME_not_enough_information (code_loc : option src_loc)
| GSME_unimplemented (code_loc : option src_loc)
| GSME_internal_error
.

Inductive ghost_simplified_model_step_result_data :=
| GSMSR_success (next : ghost_simplified_memory)
| GSMSR_failure (s : ghost_simplified_model_error).

Record ghost_simplified_model_step_result := mk_ghost_simplified_model_step_result {
  gsmsr_log : list string;
  gsmsr_data : ghost_simplified_model_step_result_data
}.
#[export] Instance eta_ghost_simplified_model_step_result : Settable _ := settable! mk_ghost_simplified_model_step_result <gsmsr_log; gsmsr_data>.

(* Type used as input of the page table visitor function  *)
Record page_table_context := {
  ptc_state: ghost_simplified_memory;
  ptc_loc: option sm_location;
  ptc_partial_ia: u64;
  ptc_addr: u64;
  ptc_root: u64;
  ptc_level: u64;
  ptc_s2: bool;
  ptc_src_loc: option src_loc;
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


(*****************************************************************************)
(********                   Code for bit-pattern                      *********)
(*****************************************************************************)

Definition PTE_BIT_VALID : u64 := BV 64 1. (* binary: 0001 *)

Definition PTE_BIT_TABLE : u64 := BV 64 2. (* binary: 0010 *)

Definition GENMASK (i j : u64) : u64 := bv_shiftl (bv_shiftr (bv_opp (BV 64 1)) (i+j)) j.
(**  0......0  1....1  0....0
  *  i zeros          j zeros
  *)

Definition PTE_BITS_ADDRESS : u64  := GENMASK (BV 64 47) (BV 64 12).

Definition is_desc_valid (descriptor : u64) : bool :=
  ((bv_and descriptor PTE_BIT_VALID) b=? PTE_BIT_VALID)
.

Definition OA_shift (level : u64) : u64 :=
match level with
  | BV _ 1 => BV 64 (12 + 9 + 9)
  | BV _ 2 => BV 64 (12 + 9 )
  | BV _ 3 => BV 64 (12)
  | _ => BV 64 0  (* Should not happen*)
end
.

Definition map_size (level : u64) : u64 :=
match level with 
  | BV _ 0 => bv_shiftl (BV 64 512) (BV 64 30) (* 512 Go *)
  | BV _ 1 => bv_shiftl (BV 64 1)   (BV 64 30) (* 1 Go *)
  | BV _ 2 => bv_shiftl (BV 64 2)   (BV 64 20) (* 2 Mo *)
  | BV _ 3 => bv_shiftl (BV 64 4)   (BV 64 10) (* 4 Ko *)
  | _ => BV 64 0  (* Should not happen*)
end
. 

Definition is_desc_table (descriptor level : u64) :=
(* There is an inequality to make termination easier *)
  if BV 64 2 b<? level then
    false
  else
    ((bv_and descriptor PTE_BIT_TABLE) b=? PTE_BIT_TABLE)
.

Definition extract_table_address (pte_val : u64) : u64 :=
bv_and pte_val PTE_BITS_ADDRESS.

Definition extract_output_address (pte_val level : u64) :=
bv_and pte_val (GENMASK (BV 64 47) (OA_shift level))
.




(******************************************************************************************)
(*                             Page table traversal                                       *)
(******************************************************************************************)

Definition initial_state (partial_ai desc level : u64) (cpu_id : nat) (pte_kind : pte_rec) (s2 : bool) : sm_pte_state :=
  match pte_kind with
    | PTER_PTE_KIND_INVALID =>
      SPS_STATE_PTE_INVALID_CLEAN ({|aic_invalidator_tid := cpu_id |})
    | PTER_PTE_KIND_MAP _ | PTER_PTE_KIND_TABLE _ =>
      SPS_STATE_PTE_VALID {|lvs := [] |}
  end 
.

Definition deconstruct_pte (cpu_id : nat) (partial_ia desc level root : u64) (s2 : bool) : ghost_exploded_descriptor :=
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

Fixpoint traverse_pgt_from_aux (root table_start partial_ia level : u64) (s2 : bool) (visitor_cb : page_table_context -> ghost_simplified_model_step_result) (src_loc : option src_loc) (st : ghost_simplified_memory) (logs : list string) (max_call_number : nat) : ghost_simplified_model_step_result :=
  match max_call_number with
   | S max_call_number => traverse_pgt_from_offs root table_start partial_ia level s2 visitor_cb src_loc st (BV 64 0) logs max_call_number
   | O => (* Coq typechecking needs a guarantee that the function terminates, that is why the max_call_number nat exists,
            the number of recursive calls is bounded. *)
   {| gsmsr_log := ["The maximum number of recursive calls of traverse_pgt_from_aux has been reached, stopping"%string]; gsmsr_data := GSMSR_failure (GSME_internal_error) |}
  end
  (* This is the for loop that iterates over all the entries of a page table *)
with traverse_pgt_from_offs (root table_start partial_ia level : u64) (s2 : bool) (visitor_cb : page_table_context -> ghost_simplified_model_step_result) (src_loc : option src_loc)(st : ghost_simplified_memory) (i : u64) (logs : list string) (max_call_number : nat) : ghost_simplified_model_step_result :=
  match max_call_number with
    | S max_call_number => 
        if i b=? (BV 64 512) then
          (* We are done with this page table *)
          {| gsmsr_log := logs; gsmsr_data := GSMSR_success st |}
        else
          let location := st.(gsm_memory) !! (bv_add (table_start) ((BV 64 8) b* i)) in
          let ctx := (* We construct the context, we don't know if the location exists but the visitor might create it *)
            {|
              ptc_state := st;
              ptc_loc := location;
              ptc_addr := bv_add (table_start) ((BV 64 8) b* i);
              ptc_partial_ia := partial_ia;
              ptc_root := root;
              ptc_level:= level;
              ptc_s2 := s2;
              ptc_src_loc := src_loc
            |}
          in
          match visitor_cb ctx with (* The visitor can edit the state and write logs *)
            | {| gsmsr_log := log1; gsmsr_data := GSMSR_failure r |}  => (* If it fails, it fails *)
              {|gsmsr_log := concat [logs; log1]; gsmsr_data := GSMSR_failure r |}
            | {| gsmsr_log := log1; gsmsr_data := GSMSR_success updated_state |} =>
              let location := updated_state.(gsm_memory) !! (bv_add (table_start) (i b* (BV 64 8))) in
              match location with
                | None => (* If the page table was not initialised, we cannot continue (or we could ignore this and continue.) *)
                  {|gsmsr_log := concat [logs; log1]; gsmsr_data := (GSMSR_failure (GSME_not_enough_information src_loc)) |}
                | Some location =>
                  let exploded_desc :=
                    match location.(sl_pte) with
                      | Some pte => pte
                      | None => (* 0 is a placeholder, we do not use it afterwards *)
                        deconstruct_pte 0 partial_ia location.(sl_val) level root s2
                    end
                  in
                  match exploded_desc.(ged_pte_kind) with
                    | PTER_PTE_KIND_TABLE table_data => 
                      (* If it is a page table descriptor, we we traverse the sub-page table *)
                      let rec_table_start := table_data.(next_level_table_addr) in
                      let next_partial_ia := exploded_desc.(ged_ia_region).(range_start) b+ i b* exploded_desc.(ged_ia_region).(range_size)  in
                      (* recursive call: explore sub-pgt *)
                      let rec_updated_state := traverse_pgt_from_aux root rec_table_start next_partial_ia (level) s2 visitor_cb src_loc updated_state logs max_call_number in
                      match rec_updated_state with
                        | {| gsmsr_log := log2 ; gsmsr_data := GSMSR_success rec_updated_state |} => 
                          (* If recursive call succeeds, continue *)
                          traverse_pgt_from_offs root table_start partial_ia level s2 visitor_cb src_loc rec_updated_state (bv_add i (BV 64 1)) (concat [logs; log1; log2]) max_call_number
                        | e => e (* if it failed, return immediately *)
                      end
                    | _ => (* if the current location is a block descriptor, we can stop and return success *)
                      {| gsmsr_log := logs; gsmsr_data := GSMSR_success (updated_state) |}
                  end
              end
          end
    | O => {| gsmsr_log := ["The maximum number of recursive calls of traverse_pgt_from_offs has been reached, stopping"%string]; gsmsr_data := GSMSR_failure (GSME_internal_error) |}
  end
.

Definition traverse_pgt_from (root table_start partial_ia level : u64) (s2 : bool) (visitor_cb : page_table_context -> ghost_simplified_model_step_result) (src_loc : option src_loc) (st : ghost_simplified_memory) : ghost_simplified_model_step_result :=
  traverse_pgt_from_aux root table_start partial_ia level s2 visitor_cb src_loc st [] (4*512)
.

(* Generic function (for s1 and s2) to traverse all page tables starting with root in roots *)
Fixpoint traverse_si_pgt_aux (st : ghost_simplified_memory) (visitor_cb : page_table_context -> ghost_simplified_model_step_result) (s2 : bool) (logs: list string) (roots : list u64) : ghost_simplified_model_step_result :=
  match roots with
    | r :: q =>
      match traverse_pgt_from r r (BV 64 0) (BV 64 0) s2 visitor_cb None st with
        | {| gsmsr_log := l_logs; gsmsr_data := GSMSR_success next |} =>
          traverse_si_pgt_aux next visitor_cb s2 (concat [logs; l_logs]) q
        | err => err <|gsmsr_log := concat [err.(gsmsr_log) ; logs] |>
      end
    | [] => {| gsmsr_log := logs; gsmsr_data := GSMSR_success st |}
  end
.

(* Generic function to traverse all S1 or S2 roots *)
Definition traverse_si_pgt (st : ghost_simplified_memory) (visitor_cb : page_table_context -> ghost_simplified_model_step_result) (s2 : bool) : ghost_simplified_model_step_result := 
  let roots := 
    if s2 then st.(gsm_roots).(pr_s2) else st.(gsm_roots).(pr_s1)
  in 
  traverse_si_pgt_aux st visitor_cb s2 [] roots
.

Definition traverse_all_pgt (st: ghost_simplified_memory) (visitor_cb : page_table_context -> ghost_simplified_model_step_result)  :=
  match traverse_si_pgt st visitor_cb true with
    | {|gsmsr_log := logs; gsmsr_data := GSMSR_success st|} =>
      let res := traverse_si_pgt st visitor_cb false in
      res <| gsmsr_log := concat [logs; res.(gsmsr_log)] |>
    | err => err
  end
.

(*******************************************************************)
(* Some generic walker functions to mark and unmark entries as PTE *)

Definition mark_cb (cpu_id : nat) (ctx : page_table_context) : ghost_simplified_model_step_result :=
  match ctx.(ptc_loc) with
    | Some location => 
      if location.(sl_pte) then 
        {| gsmsr_log := nil; gsmsr_data := GSMSR_failure (GSME_double_use_of_pte ctx.(ptc_src_loc)) |}
      else 
        let new_descriptor := deconstruct_pte cpu_id ctx.(ptc_partial_ia) ctx.(ptc_partial_ia) location.(sl_val) ctx.(ptc_level) ctx.(ptc_s2) in
        let new_location :=  (location <| sl_pte := (Some new_descriptor) |>) in
        let new_state := ctx.(ptc_state) <| gsm_memory := <[ location.(sl_phys_addr) := new_location]> ctx.(ptc_state).(gsm_memory) |> in
        {| gsmsr_log := nil; gsmsr_data := GSMSR_success new_state |}
    | None =>  (* In the C model, it is not an issue memory can be read, here we cannot continue because we don't have the value at that memory location *)
        {| gsmsr_log := nil; gsmsr_data := GSMSR_failure (GSME_not_enough_information None) |}
  end
.

Definition unmark_cb (cpu_id : nat) (ctx : page_table_context) : ghost_simplified_model_step_result :=
  match ctx.(ptc_loc) with
    | Some location =>
      match location.(sl_pte) with
        | Some desc => 
          let new_loc := location <|sl_pte := None |> in
          let new_st := <[ location.(sl_phys_addr) := new_loc ]> ctx.(ptc_state).(gsm_memory) in
          {| gsmsr_log := nil; gsmsr_data := GSMSR_success (ctx.(ptc_state) <| gsm_memory := new_st |>) |}
        | None =>
          {| gsmsr_log := nil; gsmsr_data := GSMSR_failure (GSME_unmark_non_pte ctx.(ptc_src_loc)) |}
      end
    | None =>  (* In the C model, it is not an issue memory can be read, here we cannot continue because we don't have the value at that memory location *)
        {| gsmsr_log := nil; gsmsr_data := GSMSR_failure (GSME_not_enough_information None) |}
  end
.

(******************************************************************************************)
(*                             Code for write                                             *)
(******************************************************************************************)
(* Visiting a page table fails with this visitor iff the visited part has an uninitialized or invalid unclean entry *)
Definition clean_reachable (ctx : page_table_context) : ghost_simplified_model_step_result := 
  match ctx.(ptc_loc) with 
    | Some location => 
      match location.(sl_pte) with
        | None => {| gsmsr_log := nil; gsmsr_data := GSMSR_failure (GSME_use_of_uninitialized_pte (ctx.(ptc_src_loc))) |}
        | Some descriptor => 
          match descriptor.(ged_state) with
            | SPS_STATE_PTE_INVALID_UNCLEAN _ => 
              let st := ctx.(ptc_state) in
              {|gsmsr_log := nil; gsmsr_data := GSMSR_failure (GSME_writing_with_unclean_children (ctx.(ptc_src_loc)))|}
            | _ => {|
                    gsmsr_log := nil;
                    gsmsr_data := GSMSR_success ctx.(ptc_state)
                  |}
          end
      end
    | None => {| gsmsr_log := nil; gsmsr_data := GSMSR_failure  (GSME_use_of_uninitialized_pte (ctx.(ptc_src_loc))) |}
  end
.

Definition step_write_on_invalid (tid : thread_identifier) (wmo : write_memory_order) (code_loc: option src_loc) (loc : sm_location) (val : u64) (st : ghost_simplified_memory) : ghost_simplified_model_step_result := 
(* If the location is a PTE table, tests if its children are clean *)
  match loc.(sl_pte) with
    | None => (* This should not happen because if we write on invalid, we write on PTE *)
      {| gsmsr_log := []; gsmsr_data := GSMSR_failure GSME_internal_error |}
    | Some descriptor =>
      (* Tests if the page table is well formed *)
      match traverse_pgt_from descriptor.(ged_owner) descriptor.(ged_ia_region).(range_start) (BV 64 0) descriptor.(ged_level) descriptor.(ged_s2) clean_reachable code_loc st with
        | {| gsmsr_log := logs; gsmsr_data :=  GSMSR_success st |} =>
            (* Mark all children as part of page-table entries *)
            let children_marked := 
              traverse_pgt_from descriptor.(ged_owner) descriptor.(ged_ia_region).(range_start) (BV 64 0) descriptor.(ged_level) descriptor.(ged_s2) (mark_cb tid) code_loc st
            in
            children_marked <|gsmsr_log := concat [logs; children_marked.(gsmsr_log)]|>
        | e => e
      end
  end
  (* Question: In the C model, the LVS status is updated for each CPU but never used, what should the Coq model do? *)
.

Definition step_write_on_invalid_unclean (tid : thread_identifier) (wmo : write_memory_order) (code_loc: option src_loc) (loc : sm_location) (val : u64) (st : ghost_simplified_memory) : ghost_simplified_model_step_result :=
  (* Only invalid descriptor are allowed *)
  if is_desc_valid val then
    {| gsmsr_log := []; gsmsr_data := GSMSR_failure (GSME_bbm_invalid_valid (code_loc)) |}
  else 
   {| gsmsr_log := []; gsmsr_data := GSMSR_success (st <|gsm_memory := <[loc.(sl_phys_addr) := loc <|sl_val := val|> ]> st.(gsm_memory) |>) |}
.

Definition step_write_on_valid (tid : thread_identifier) (wmo : write_memory_order) (code_loc: option src_loc) (loc : sm_location) (val : u64) (st : ghost_simplified_memory) : ghost_simplified_model_step_result :=
  let old := loc.(sl_val) in
  if old b=? val then (* If no change in memory: no problem*)
   {| gsmsr_log := []; gsmsr_data := GSMSR_success st |}
  else
    if is_desc_valid val then 
      (* Changing the descriptor is illegal *)
      {| gsmsr_log := []; gsmsr_data := GSMSR_failure (GSME_bbm_valid_valid (code_loc)) |}
    else
    (
      (* Invalidation of pgt: changing the state to  *)
      match loc.(sl_pte) with
        | None => (* This does not make sense because function is called on a pgt *)
          {| gsmsr_log := []; gsmsr_data := GSMSR_failure GSME_internal_error |}
        | Some desc =>
          let new_desc := desc <| ged_state := (SPS_STATE_PTE_INVALID_UNCLEAN {| ai_invalidator_tid := tid; ai_old_valid_desc :=  old; ai_lis := LIS_unguarded; |}) |> in
          {|
            gsmsr_log := [];
            gsmsr_data := GSMSR_success (st
              <| gsm_memory :=
                (<[ loc.(sl_phys_addr) := loc <|sl_pte := Some (new_desc)|> ]> st.(gsm_memory))
              |> );
          |}
      end
    ).

Definition step_write (tid : thread_identifier) (wd : trans_write_data) (code_loc: option src_loc) (st : ghost_simplified_memory) : ghost_simplified_model_step_result :=
  let wmo := wd.(twd_mo) in
  let val := wd.(twd_val) in
  let addr := wd.(twd_phys_addr) in
  match st.(gsm_memory) !! addr with
    | Some (loc) =>
        match loc.(sl_pte) with
          | Some desc =>
            (* If we write to a page table, depending on its state, we update them  *)
            match desc.(ged_state) with
            | SPS_STATE_PTE_VALID av =>
                (step_write_on_valid tid wmo code_loc loc val st)
            | SPS_STATE_PTE_INVALID_CLEAN av =>
                (step_write_on_invalid tid wmo code_loc loc val st)
            | SPS_STATE_PTE_INVALID_UNCLEAN av =>
                (step_write_on_invalid_unclean tid wmo code_loc loc val st)
            end
          | None => (* If it is not a pte, we just update the value *)
            let new_loc := loc <| sl_val := val |> in
            {| gsmsr_log := nil;
                gsmsr_data := GSMSR_success (
                  st <| gsm_memory := <[ addr := new_loc ]> st.(gsm_memory) |>
              )
            |}
        end
    | None => 
      (* If the location has not been written to, it is not a pgt, just save its value *)
      {| gsmsr_log := nil;
        gsmsr_data := GSMSR_success (
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
(*                             Code for read                                              *)
(******************************************************************************************)

Definition step_read (tid : thread_identifier) (rd : trans_read_data) (code_loc: option src_loc) (st : ghost_simplified_memory) : ghost_simplified_model_step_result :=
  (* Test if the memory has been initialized (it might refuse acceptable executions, not sure if it is a good idea) and its content is consistent. *)
  match st.(gsm_memory) !! rd.(trd_phys_addr) with
    | Some mem_loc => if mem_loc.(sl_val) b=? rd.(trd_val) then 
      {| gsmsr_log := nil;
        gsmsr_data := (GSMSR_success st) |}  else
      {| gsmsr_log := nil;
        gsmsr_data := GSMSR_failure (GSME_inconsistent_read code_loc) |}
    | None => 
      (* Question: Should this really fail? *)
      {| gsmsr_log := nil;
        gsmsr_data := GSMSR_failure (GSME_read_uninitialized code_loc) |}
  end
.

(******************************************************************************************)
(*                                      DSB                                               *)
(******************************************************************************************)
Definition dsb_visitor (kind : dsb_kind) (cpu_id : nat) (ctx : page_table_context) : ghost_simplified_model_step_result :=
  match ctx.(ptc_loc) with
    | None => (* This case is not explicitly excluded by the C code, but we cannot do anything in this case. *)
      (* Question: should we ignore it and return the state? *)
      {| gsmsr_log := nil; gsmsr_data := GSMSR_failure (GSME_use_of_uninitialized_pte ctx.(ptc_src_loc)) |}
    | Some location =>
      let pte :=
        match location.(sl_pte) with
          | None => deconstruct_pte cpu_id ctx.(ptc_partial_ia) ctx.(ptc_partial_ia) location.(sl_val) ctx.(ptc_level) ctx.(ptc_s2)
          | Some pte => pte
        end
      in
      let new_pte := 
        match pte.(ged_state) with
          | SPS_STATE_PTE_INVALID_UNCLEAN sst =>
            (* DSB has an effect on invalid unclean state only *)
            if negb (sst.(ai_invalidator_tid) =? cpu_id) then
              pte (* If it is another CPU that did the invalidation, do noting*)
            else
              (* Otherwise, update the state invalid unclean sub-automaton *)
              match sst.(ai_lis) with
                | LIS_unguarded =>
                  pte <|ged_state := SPS_STATE_PTE_INVALID_UNCLEAN (sst <|ai_lis := LIS_dsbed |>) |>
                | LIS_dsbed => pte
                | LIS_dsb_tlbied => 
                  match kind with
                    | DSB_ish => 
                      pte <|ged_state := SPS_STATE_PTE_INVALID_CLEAN {| aic_invalidator_tid := sst.(ai_invalidator_tid) |} |>
                    | _ => pte 
                  end
                | LIS_dsb_tlbi_ipa =>  
                    match kind with
                      | DSB_ish =>
                  pte <|ged_state := SPS_STATE_PTE_INVALID_UNCLEAN (sst <|ai_lis := LIS_dsb_tlbi_ipa_dsb |>) |>
                      | _ => pte
                    end
                | _ => pte
              end
          | _ => pte (* If not invalid unclean, then do nothing *)
        end
      in
      (* then update state and return *)
      let new_loc := (location <| sl_pte := Some pte |>) in
      let new_state := ctx.(ptc_state) <| gsm_memory := <[ location.(sl_phys_addr) := new_loc ]> ctx.(ptc_state).(gsm_memory) |> in
      {| gsmsr_log := nil; gsmsr_data := GSMSR_success new_state |}
  end
.

Definition step_dsb (tid : thread_identifier) (dk : dsb_kind) (code_loc: option src_loc) (st : ghost_simplified_memory) : ghost_simplified_model_step_result := 
  (* walk the pgt with dsb_visitor*)
  traverse_all_pgt st (dsb_visitor dk tid)
.

(******************************************************************************************)
(*                                     TLBI                                               *)
(******************************************************************************************)

Definition should_perform_tlbi (td : trans_tlbi_data) (ptc : page_table_context) : bool :=
  match ptc.(ptc_loc) with
    | None => false (* does not happen because we call it in tlbi_visitor in which we test that the location is init *)
    | Some loc =>
      match loc.(sl_pte) with
        | None => false (* if the PTE is not initialised, it has not been used; TLBI has no effect *)
        | Some pte_desc =>
          match td.(ttd_tlbi_kind) with
            | TLBI_vae2is | TLBI_ipas2e1is => 
              let tlbi_addr := bv_shiftr td.(ttd_page) 12 in
                (negb (is_desc_table loc.(sl_val) (pte_desc.(ged_level)))) (* Not a leaf *)
                && (pte_desc.(ged_ia_region).(range_start) b<? tlbi_addr) (* and in the range of the TLBI *)
                && (tlbi_addr b<? (bv_add pte_desc.(ged_ia_region).(range_start) pte_desc.(ged_ia_region).(range_size)))
            | _ => true (* This should change depending on the TLBI kind *)
          end
      end
  end
.

Definition tlbi_invalid_unclean_unmark_children (cpu_id : nat) (loc : sm_location) (ptc : page_table_context) : ghost_simplified_model_step_result :=
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
          match traverse_pgt_from pte.(ged_owner) pte.(ged_ia_region).(range_start) (BV 64 0) pte.(ged_level) pte.(ged_s2) clean_reachable ptc.(ptc_src_loc) st with
            | {| gsmsr_log := logs; gsmsr_data:= GSMSR_success st|} =>
              (* If all children are clean, we can unmark them as PTE *)
              match traverse_pgt_from old_desc.(ged_owner) old_desc.(ged_ia_region).(range_start) (BV 64 0) old_desc.(ged_level) old_desc.(ged_s2) (unmark_cb cpu_id) ptc.(ptc_src_loc) st with
                | {| gsmsr_log := logs1; gsmsr_data := st|} => {|gsmsr_log := concat [logs; logs1]; gsmsr_data := st |}
              end
            | e => e
          end
        | _ => {| gsmsr_log := nil; gsmsr_data := GSMSR_success st |}
      end
    | _ => (* if it is not invalid unclean, the TLBI has no effect *)
      {| gsmsr_log := nil; gsmsr_data := GSMSR_success st |}
  end
.

Definition tlbi_visitor (cpu_id : nat) (td : trans_tlbi_data) (ptc : page_table_context) : ghost_simplified_model_step_result :=
  match ptc.(ptc_loc) with
    | None => (* Cannot do anything if the page is not initialized *)
      {| gsmsr_log := nil; gsmsr_data := GSMSR_failure (GSME_use_of_uninitialized_pte ptc.(ptc_src_loc)) |}
    | Some location =>
      (* Test if there is something to do *)
      if should_perform_tlbi td ptc then
        (* step_pte_on_tlbi: inlined *)
        match tlbi_invalid_unclean_unmark_children cpu_id location ptc with
          | {| gsmsr_log := log; gsmsr_data := GSMSR_success st|} as ret =>
            (* If it worked, then we update the invalid unclean sub-automaton *)
            match location.(sl_pte) with
              | None => ret (* This cannot happen (otherwise, should_perform_tlbi would be false) *)
              | Some exploded_desc =>
                match exploded_desc.(ged_state) with
                  | SPS_STATE_PTE_INVALID_UNCLEAN ai =>
                    (* If the CPU that does the transformation is not the one that initiated the invalidation, do nothing *)
                    if bool_decide (cpu_id = ai.(ai_invalidator_tid)) then
                      let new_substate :=
                        (* Depending on the current state and the TLBI kind, we update the sub-state *)
                        match ai.(ai_lis) with
                          | LIS_dsbed => (* step_pte_on_tlbi_after_dsb: inlined *)
                              match td.(ttd_tlbi_kind) with
                                | TLBI_vmalle1is => LIS_dsb_tlbied
                                | TLBI_ipas2e1is => LIS_dsb_tlbi_ipa
                                | _ => LIS_dsbed
                              end
                          | LIS_dsb_tlbi_ipa_dsb => (* step_pte_on_tlbi_after_tlbi_ipa: inlined *)
                              match td.(ttd_tlbi_kind) with
                                | TLBI_vmalle1is => LIS_dsb_tlbied
                                | _ => LIS_dsb_tlbi_ipa_dsb
                              end
                          | r => r
                        end
                      in
                      (* Write the new sub-state in the global automaton *)
                      let new_loc := location <| sl_pte := Some (exploded_desc <|ged_state := SPS_STATE_PTE_INVALID_UNCLEAN (ai <| ai_lis := new_substate|>) |>)|> in
                      let new_mem := st <| gsm_memory := <[location.(sl_phys_addr) := new_loc]> st.(gsm_memory)|> in
                      ret <|gsmsr_data := GSMSR_success new_mem|>
                    else
                      ret
                  | _ => ret
                end
            end
          | e => e
        end
      else (* In the case where the PTE is not affected by the TLBI, we do nothing *)
        {|gsmsr_log := nil; gsmsr_data := GSMSR_success ptc.(ptc_state) |}
  end
.


Definition step_tlbi (tid : thread_identifier) (td : trans_tlbi_data) (code_loc: option src_loc) (st : ghost_simplified_memory) : ghost_simplified_model_step_result :=
  match td.(ttd_tlbi_kind) with
    | TLBI_vae2is =>
      (* traverse all s1 pages*)
      traverse_si_pgt st (tlbi_visitor tid td) false
    | TLBI_vmalls12e1is | TLBI_ipas2e1is | TLBI_vmalle1is =>
      (* traverse s2 pages *)
      traverse_si_pgt st (tlbi_visitor tid td) true
    | _ =>
      (* traverse all page tables and add a warning *)
      let res := traverse_all_pgt st (tlbi_visitor tid td) in
      res <| gsmsr_log := concat [res.(gsmsr_log); ["Warning: unsupported TLBI, defaulting to TLBI VMALLS12E1IS;TLBI ALLE2."%string]] |>
  end
.


(******************************************************************************************)
(*                                  Step MSR                                              *)
(******************************************************************************************)

Fixpoint si_root_exists (root : u64) (roots : list u64) :=
  match roots with
    | [] => false
    | t :: q => (t b=? root) || (si_root_exists root q)
  end
.

Definition extract_si_root (val : u64) (s2 : bool) : u64 :=
  bv_and val (GENMASK (BV 64 47) (BV 64 1))
.

Definition register_si_root (tid : thread_identifier) (st : ghost_simplified_memory) (root : u64) (s2 : bool) (code_loc: option src_loc) : ghost_simplified_model_step_result :=
  let other_root_levels := (if s2 then pr_s1 else pr_s2) st.(gsm_roots) in
  if si_root_exists root other_root_levels then
    {| gsmsr_log := nil; gsmsr_data := GSMSR_failure (GSME_root_already_exists code_loc) |}
  else
    let new_roots :=
      if s2 then
        st.(gsm_roots) <| pr_s2 := st.(gsm_roots).(pr_s2) |>
      else
        st.(gsm_roots) <| pr_s1 := st.(gsm_roots).(pr_s1) |>
    in
    let new_st := st <| gsm_roots := new_roots |> in
    traverse_si_pgt new_st (mark_cb tid) s2 
.

Definition step_msr (tid : thread_identifier) (md : trans_msr_data) (code_loc: option src_loc) (st : ghost_simplified_memory) : ghost_simplified_model_step_result :=
  let s2 := 
    match md.(tmd_sysreg) with
      | SYSREG_TTBR_EL2 => true
      | SYSREG_VTTBR => false
    end
  in
  let root := extract_si_root md.(tmd_val) s2 in
  if si_root_exists root ((if s2 then pr_s2 else pr_s1) st.(gsm_roots)) then
    Mreturn st
  else
    register_si_root tid st root true code_loc
.

(******************************************************************************************)
(*                                  Step hint                                             *)
(******************************************************************************************)

Fixpoint set_owner_root (phys root : u64) (st : ghost_simplified_memory) (logs : list string) (offs : nat) : ghost_simplified_model_step_result :=
  match offs with
    | O => {|gsmsr_log := logs; gsmsr_data := GSMSR_success st |}
    | S offs => 
      let addr := bv_add_Z phys ((Z.of_nat (offs * 8))) in
      match st.(gsm_memory) !! addr with
        | None => set_owner_root phys root st logs offs (* We might want to do something here, but no data… *)
        | Some location => 
          let new_pte := 
            match location.(sl_pte) with 
              | None => None
              | Some pte => Some (pte <| ged_owner := root|>)
            end
          in
          let new_loc := location <| sl_pte := new_pte |> in
          let new_state := st <|gsm_memory := <[ location.(sl_phys_addr) := new_loc ]> st.(gsm_memory) |> in
          set_owner_root phys root new_state logs offs
      end
  end
.

Definition align_4k (addr : u64) : u64 :=
  bv_and addr (GENMASK (BV 64 64) (BV 64 12))
.

Definition step_hint (hd : trans_hint_data) (code_loc: option src_loc) (st : ghost_simplified_memory) : ghost_simplified_model_step_result :=
  match hd.(thd_hint_kind) with 
    | GHOST_HINT_SET_ROOT_LOCK => Mreturn st
    | GHOST_HINT_SET_OWNER_ROOT => 
      set_owner_root (align_4k hd.(thd_location)) hd.(thd_value) st [] 512
  end
.

(******************************************************************************************)
(*                             Toplevel function                                          *)
(******************************************************************************************)

Definition step (trans : ghost_simplified_model_transition) (st : ghost_simplified_memory) : ghost_simplified_model_step_result :=
  match trans.(gsmt_data) with
  | GSMDT_TRANS_MEM_WRITE wd =>
    step_write trans.(gsmt_thread_identifier) wd trans.(gsmt_src_loc) st
  | GSMDT_TRANS_MEM_READ rd => 
    step_read trans.(gsmt_thread_identifier) rd trans.(gsmt_src_loc) st
  | GSMDT_TRANS_DSB dsb_data => 
    step_dsb trans.(gsmt_thread_identifier) dsb_data trans.(gsmt_src_loc) st
  | GSMDT_TRANS_ISB => {| gsmsr_log := nil; gsmsr_data := GSMSR_success st|} (* Ignored *) 
  | GSMDT_TRANS_TLBI tlbi_data => step_tlbi trans.(gsmt_thread_identifier) tlbi_data trans.(gsmt_src_loc) st
  | GSMDT_TRANS_MSR msr_data => step_msr trans.(gsmt_thread_identifier) msr_data trans.(gsmt_src_loc) st
  | GSMDT_TRANS_HINT hint_data => step_hint hint_data trans.(gsmt_src_loc) st
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