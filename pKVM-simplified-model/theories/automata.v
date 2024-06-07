(** Simplified model *)
(* https://github.com/rems-project/linux/blob/pkvm-verif-6.4/arch/arm64/kvm/hyp/include/nvhe/ghost_simplified_model.h *)
Require Import String.
Require stdpp.bitvector.bitvector.
Require Import Cmap.cmap.
(* uses https://github.com/tchajed/coq-record-update *)
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.
Require Import stdpp.gmap.
Require Import Recdef.

Require Export state.
Require Export transition.

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
  if negb ((bv_and_64 (phys_addr_val addr) b7) b=? b0)
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
    let addr := wd.(twd_phys_addr) pa+ (Phys_addr (bv_mul_Z_64 b8 (offs - 1))) in
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
    | WMO_page => step_write_page tid wd (Mreturn st) z512
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
  step_zalloc_all (Phys_addr (bv_shiftr_64 (phys_addr_val zd.(tzd_addr)) (b12))) {|gsmsr_log := nil; gsmsr_data := Ok _ _ st|} pa0 (to_nat zd.(tzd_size))
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
              let tlbi_addr := bv_shiftl_64 (phys_addr_val d.(TOBAD_page)) b12 in
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

Definition _extract_si_root_big_bv := BV64 0xfffffffffffe%Z. (* GENMASK (b47) (b1) *)
Definition extract_si_root (val : u64) (stage : stage_t) : owner_t :=
  (* Does not depends on the S1/S2 level but two separate functions in C, might depend on CPU config *)
  Root (Phys_addr (bv_and_64 val _extract_si_root_big_bv))
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
    let addr := phys pa+ (Phys_addr (bv_mul_Z_64 b8 (offs - 1))) in
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
      set_owner_root (align_4k hd.(thd_location)) hd.(thd_value) st [] z512
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



