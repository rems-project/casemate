Require Import String.

Inductive ghost_model_catch_fire :=
  | change_lock_on_unlocked_location
  | append_lock_on_locked_location
  | release_table_without_lock
  | missing_location_owner
  | missing_owner_root
  | write_to_pte_without_owner_lock
  | initialize_already_initialized_location
  | double_use_pte
  | unmark_non_pte
  | invalidated_owned_entry_parent
  | exceed_max_root_limit
  | root_already_exists
  | root_does_not_exist
  | bbm_write_table_descriptor_with_unclean_children
  | bbm_invalid_unclean_to_valid
  | bbm_valid_to_valid
  | write_page_with_unclean_parent
  | location_accessed_by_another_thread
  | write_plain_without_authorization
  | unsupported_dsb_nsh
  | unsupported_tlbi_broadcast_expected
  | unsupported_tlbi_by_addr_id
  | release_table_with_unclean_children
  | lock_component_already_held
  | unlock_component_held_by_another_thread
  | unlock_component_not_held
  | uninitialized_location
.

Inductive ghost_model_bug :=
  | index_out_of_bounds
  | exceeds_num_of_max_locks
  | parses_attrs_for_a_non_pagetable_pte
  | failed_blobs_sanity_check
  | ensured_blobs_not_found
  | exceeds_max_level
  | out_of_fuels_during_pgtable_traversal
  | invalid_callback_data
  | transition_not_initialised
.

Inductive ghost_model_assertion_fail :=
  | assumes_4k_granule
  | assumes_stage2_translation_starting_at_level_0
  | mair_must_be_present
  | not_page_aligned
  | run_out_of_free_blobs
  | pgtable_traverse_from_nonzero_level
  | found_multiple_contenated_pgtables
  | location_already_in_unclean_ptes
  | exceeds_max_unclean_locations
  | location_not_initialised
  | location_not_pte
  | location_not_invalid_unclean_pte
  | location_pte_not_in_pgtable
  | address_on_write_transition
  | unsupported_sysreg_VTTBR
  | unsupported_sysreg_TTBR_EL2
  | invalid_tlbi_regime
  | read_inconsistent
  | location_not_in_LEVEL3
  | unreachable
  | unimplemented
.

Inductive termination :=
  | bug : ghost_model_bug -> termination
  | assertion_fail : ghost_model_assertion_fail -> termination
  | catch_fire : ghost_model_catch_fire -> termination.

Inductive ghost_model_result {A : Type} :=
  | ok : A -> ghost_model_result
  | err : termination -> ghost_model_result.

Definition opt_bind {A B : Type} (opt : option A) (f : A -> option B) : option B :=
  match opt with
  | Some x => f x
  | None => None
  end.

Definition is_some {A : Type} (opt : option A) : bool :=
  match opt with
  | Some _ => true
  | None => false
  end.

Definition bind {A B: Type}
  (res : ghost_model_result (A:=A))
  (f : A -> ghost_model_result (A:=B)) : ghost_model_result :=
  match res with
  | ok a => f a
  | err e => err e
  end.

Definition bind_opt_ret {A B : Type}
  (opt : option A)
  (ret : B)
  (f : A -> B) : B :=
  match opt with
  | Some x => f x
  | None => ret
  end.

Definition bind_cond {A : Type} (condition : bool) (ret : A)  (f : A) :=
  match condition with
  | true => f
  | false => ret
  end.

Declare Scope result_scope.
Notation "x <- m ';' f" := (bind m (fun x => f))
  (at level 60, right associativity) : result_scope.
Notation "x <- m '??' t ';' f" := (bind_opt_ret m t (fun x => f))
  (at level 60, right associativity) : result_scope.
Notation "m 'else_ret' t ';' f" := (bind_cond m t f)
  (at level 60, right associativity) : result_scope.

#[global] Open Scope result_scope.

