#include <casemate-impl.h>

/// Equality checks
bool sm_aut_invalid_eq(struct aut_invalid *i1, struct aut_invalid *i2)
{
	if (i1->invalidator_tid != i2->invalidator_tid)
		return false;

	if (i1->old_valid_desc != i2->old_valid_desc)
		return false;

	if (i1->lis != i2->lis) {
		return false;
	}

	return true;
}

bool sm_pte_state_eq(struct sm_pte_state *s1, struct sm_pte_state *s2)
{
	if (s1->kind != s2->kind)
		return false;

	switch (s1->kind) {
	case STATE_PTE_INVALID:
		return (s1->invalid_clean_state.invalidator_tid ==
			s2->invalid_clean_state.invalidator_tid);
	case STATE_PTE_INVALID_UNCLEAN:
		return sm_aut_invalid_eq(&s1->invalid_unclean_state, &s2->invalid_unclean_state);
	case STATE_PTE_VALID:
	case STATE_PTE_NOT_WRITABLE:
		// TODO: per-CPU LVS
		return true;

	default:
		unreachable();
	}
}

bool sm_loc_eq(struct sm_location *loc1, struct sm_location *loc2)
{
	if (loc1->phys_addr != loc2->phys_addr)
		return false;

	if (loc1->initialised != loc2->initialised)
		return false;

	if (loc1->initialised && (loc1->val != loc2->val))
		return false;

	if (loc1->is_pte != loc2->is_pte)
		return false;

	if (! sm_pte_state_eq(&loc1->state, &loc2->state))
		return false;

	return true;
}

// Copying
void copy_cm_state_into(struct casemate_model_state *out)
{
	memcpy(out, MODEL(), sizeof(struct casemate_model_state));
}
