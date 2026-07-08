Require Import utils.
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
  | TLBI_alle1
  | TLBI_alle1is
  | TLBI_vmalle1
  | TLBI_alle2
  | TLBI_alle2is
  | TLBI_vale2is
  | TLBI_vae2is
  | TLBI_ipas2e1is
.

Record trans_tlbi_data := {
  ttd_tlbi_kind : tlbi_kind;
  ttd_value : u64
}.

Inductive TLBI_method_shape :=
  | TLBI_method_by_addr_space
  | TLBI_method_by_input_addr
  | TLBI_method_by_all
.

Record tlbi_kind_info := {
  tki_stage : TLBI_stage_kind;
  tki_regime : Regime;
  tki_shootdown : bool;
  tki_has_asid : bool;
  tki_last_level_only : bool;
  tki_method_shape : TLBI_method_shape;
}.

Definition tlbi_kind_info_of (kind : tlbi_kind) : tlbi_kind_info :=
  match kind with
  | TLBI_vmalls12e1 =>
      {| tki_stage := TLBI_OP_both_stages;
         tki_regime := Regime_EL10;
         tki_shootdown := false;
         tki_has_asid := false;
         tki_last_level_only := false;
         tki_method_shape := TLBI_method_by_addr_space |}
  | TLBI_vmalls12e1is =>
      {| tki_stage := TLBI_OP_both_stages;
         tki_regime := Regime_EL10;
         tki_shootdown := true;
         tki_has_asid := false;
         tki_last_level_only := false;
         tki_method_shape := TLBI_method_by_addr_space |}
  | TLBI_vmalle1is =>
      {| tki_stage := TLBI_OP_stage1;
         tki_regime := Regime_EL10;
         tki_shootdown := true;
         tki_has_asid := false;
         tki_last_level_only := false;
         tki_method_shape := TLBI_method_by_addr_space |}
  | TLBI_alle1 =>
      {| tki_stage := TLBI_OP_both_stages;
         tki_regime := Regime_EL10;
         tki_shootdown := false;
         tki_has_asid := false;
         tki_last_level_only := false;
         tki_method_shape := TLBI_method_by_all |}
  | TLBI_alle1is =>
      {| tki_stage := TLBI_OP_both_stages;
         tki_regime := Regime_EL10;
         tki_shootdown := true;
         tki_has_asid := false;
         tki_last_level_only := false;
         tki_method_shape := TLBI_method_by_all |}
  | TLBI_vmalle1 =>
      {| tki_stage := TLBI_OP_stage1;
         tki_regime := Regime_EL10;
         tki_shootdown := false;
         tki_has_asid := false;
         tki_last_level_only := false;
         tki_method_shape := TLBI_method_by_addr_space |}
  | TLBI_alle2 =>
      {| tki_stage := TLBI_OP_stage1;
         tki_regime := Regime_EL2;
         tki_shootdown := false;
         tki_has_asid := false;
         tki_last_level_only := false;
         tki_method_shape := TLBI_method_by_all |}
  | TLBI_alle2is =>
      {| tki_stage := TLBI_OP_stage1;
         tki_regime := Regime_EL2;
         tki_shootdown := true;
         tki_has_asid := false;
         tki_last_level_only := false;
         tki_method_shape := TLBI_method_by_all |}
  | TLBI_vale2is =>
      {| tki_stage := TLBI_OP_stage1;
         tki_regime := Regime_EL2;
         tki_shootdown := true;
         tki_has_asid := true;
         tki_last_level_only := true;
         tki_method_shape := TLBI_method_by_input_addr |}
  | TLBI_vae2is =>
      {| tki_stage := TLBI_OP_stage1;
         tki_regime := Regime_EL2;
         tki_shootdown := true;
         tki_has_asid := true;
         tki_last_level_only := false;
         tki_method_shape := TLBI_method_by_input_addr |}
  | TLBI_ipas2e1is =>
      {| tki_stage := TLBI_OP_stage2;
         tki_regime := Regime_EL10;
         tki_shootdown := true;
         tki_has_asid := false;
         tki_last_level_only := false;
         tki_method_shape := TLBI_method_by_input_addr |}
  end.

Definition decode_tlbi_stage (td : trans_tlbi_data) : TLBI_stage_kind :=
  (tlbi_kind_info_of td.(ttd_tlbi_kind)).(tki_stage).

Definition decode_Regime (td : trans_tlbi_data) : Regime :=
  (tlbi_kind_info_of td.(ttd_tlbi_kind)).(tki_regime).

Definition decode_tlbi_shootdown (td : trans_tlbi_data) : bool :=
  (tlbi_kind_info_of td.(ttd_tlbi_kind)).(tki_shootdown).

Definition decoded_tlbi_has_asid (td : trans_tlbi_data) : option addr_id_t :=
  if (tlbi_kind_info_of td.(ttd_tlbi_kind)).(tki_has_asid) then
    Some (AID (bv_and_64 td.(ttd_value) TLBI_ASID_MASK))
  else None.

Definition decode_tlbi_by_addr (td : trans_tlbi_data) : TLBI_op_by_addr_data :=
  let page := bv_and_64 td.(ttd_value) TLBI_PAGE_MASK in
  let last_level_only :=
    (tlbi_kind_info_of td.(ttd_tlbi_kind)).(tki_last_level_only) in
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
  match (tlbi_kind_info_of td.(ttd_tlbi_kind)).(tki_method_shape) with
  | TLBI_method_by_addr_space => TLBI_by_addr_space (decode_tlbi_by_space_id td)
  | TLBI_method_by_input_addr => TLBI_by_input_addr (decode_tlbi_by_addr td)
  | TLBI_method_by_all => TLBI_by_all
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
