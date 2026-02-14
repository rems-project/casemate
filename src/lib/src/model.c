#include <casemate-impl.h>

////////////////////////
// Watching

static bool is_watched(u64 location)
{
	for (int i = 0; i < STATE()->watchpoints.num_watchpoints; i++) {
		if (STATE()->watchpoints.watchpoints[i] == location)
			return true;
	}

	return false;
}

void touch(u64 location)
{
	if (is_watched(location))
		STATE()->touched_watchpoint = true;
}

////////////////////
// Locks

gsm_lock_addr_t *owner_lock(sm_owner_t owner_id)
{
	for (int i = 0; i < MODEL()->locks.len; i++) {
		if (MODEL()->locks.owner_ids[i] == owner_id) {
			return MODEL()->locks.locks[i];
		}
	}

	return NULL;
}

static void swap_lock(sm_owner_t root, gsm_lock_addr_t *lock)
{
	struct lock_owner_map *locks = &MODEL()->locks;

	if (! owner_lock(root)) {
		ghost_assert(false);
	}

	for (int i = 0; i < MODEL()->locks.len; i++) {
		if (locks->owner_ids[i] == root) {
			locks->locks[i] = lock;
			return;
		}
	}

	GHOST_MODEL_CATCH_FIRE("can't change lock on unlocked location");
}

static void append_lock(sm_owner_t root, gsm_lock_addr_t *lock)
{
	u64 i;

	if (owner_lock(root)) {
		GHOST_MODEL_CATCH_FIRE("can't append lock on already locked location");
		unreachable();
	}

	i = MODEL()->locks.len++;
	ghost_assert(i < CASEMATE_MAX_LOCKS);
	MODEL()->locks.owner_ids[i] = root;
	MODEL()->locks.locks[i] = lock;
}

static void associate_lock(sm_owner_t root, gsm_lock_addr_t *lock)
{
	if (owner_lock(root)) {
		swap_lock(root, lock);
	} else {
		append_lock(root, lock);
	}
}

static void unregister_lock(u64 root)
{
	int len = MODEL()->locks.len;

	for (int i = 0; i < len; i++) {
		if (MODEL()->locks.owner_ids[i] == root) {
			len--;
			MODEL()->locks.owner_ids[i] = MODEL()->locks.owner_ids[len];
			MODEL()->locks.locks[i] = MODEL()->locks.locks[len];
			MODEL()->locks.len--;
			return;
		}
	}
	GHOST_MODEL_CATCH_FIRE("Tried to release a table which did not have a lock");
}

bool is_correctly_locked(gsm_lock_addr_t *lock, struct lock_state **state)
{
	if (! opts()->check_opts.check_synchronisation) {
		*state = NULL;
		return false;
	}

	for (int i = 0; i < MODEL()->lock_state.len; i++) {
		if (MODEL()->lock_state.address[i] == lock) {
			if (state != NULL) {
				*state = &MODEL()->lock_state.locker[i];
			}
			return MODEL()->lock_state.locker[i].id == cpu_id();
		}
	}

	return false;
}

bool is_location_locked(struct sm_location *loc)
{
	struct lock_state *state;
	sm_owner_t owner_id;
	gsm_lock_addr_t *lock;

	if (! loc->initialised || ! loc->is_pte)
		return true;

	if (! opts()->check_opts.check_synchronisation)
		return true;

	// If the location is owned by a thread, check that it is this thread.
	if (loc->thread_owner >= 0)
		return loc->thread_owner == cpu_id();

	// Otherwise, get the owner of the location
	owner_id = loc->owner;
	// assume 0 cannot be a valid owner id
	if (! owner_id)
		GHOST_MODEL_CATCH_FIRE("must have associated location with an owner");
	// get the address of the lock
	lock = owner_lock(owner_id);
	// check the state of the lock
	return is_correctly_locked(lock, &state);
}

/**
 * assert_owner_locked() - Validates that the owner of a pte is locked by its lock.
 */
static void assert_owner_locked(struct sm_location *loc, struct lock_state **state)
{
	sm_owner_t owner_id;
	gsm_lock_addr_t *lock;

	ghost_assert(loc->initialised && loc->is_pte);

	if (! opts()->check_opts.check_synchronisation)
		return;

	owner_id = loc->owner;

	// assume 0 cannot be a valid owner id
	if (! owner_id)
		GHOST_MODEL_CATCH_FIRE("must have associated location with an owner");

	lock = owner_lock(owner_id);
	if (! lock)
		GHOST_MODEL_CATCH_FIRE("must have associated owner with a root");

	if (! is_correctly_locked(lock, state)) {
		// ghost_printf_ext("%g(sm_loc)", loc);
		// ghost_printf_ext("%g(sm_locks)", MODEL()->locks);
		GHOST_MODEL_CATCH_FIRE("must write to pte while holding owner lock");
	}
}

///////////////////
// TLB maintenance

enum sm_tlbi_op_method_kind decode_tlbi_method_kind(enum tlbi_kind k)
{
	switch (k) {
	case TLBI_vmalls12e1:
	case TLBI_vmalls12e1is:
	case TLBI_vmalle1is:
	case TLBI_vmalle1:
		return TLBI_OP_BY_ADDR_SPACE;

	case TLBI_vale2is:
	case TLBI_vae2is:
	case TLBI_ipas2e1is:
		return TLBI_OP_BY_INPUT_ADDR;

	case TLBI_alle1is:
		return TLBI_OP_BY_ALL;

	default:
		BUG(); // TODO: missing kind
	}
}

bool decode_tlbi_shootdown_kind(enum tlbi_kind k)
{
	switch (k) {
	case TLBI_vmalls12e1is:
	case TLBI_vmalle1is:
	case TLBI_vale2is:
	case TLBI_vae2is:
	case TLBI_ipas2e1is:
	case TLBI_alle1is:
		return true;

	case TLBI_vmalls12e1:
	case TLBI_vmalle1:
		return false;

	default:
		BUG(); // TODO: missing kind
	}
}

enum sm_tlbi_op_stage decode_tlbi_stage_kind(enum tlbi_kind k)
{
	switch (k) {
	case TLBI_vale2is:
	case TLBI_vae2is:
	case TLBI_vmalle1is:
	case TLBI_vmalle1:
		return TLBI_OP_STAGE1;

	case TLBI_ipas2e1is:
		return TLBI_OP_STAGE2;

	case TLBI_vmalls12e1:
	case TLBI_vmalls12e1is:
	case TLBI_alle1is:
		return TLBI_OP_BOTH_STAGES;

	default:
		BUG(); // TODO: missing kind
	}
}

enum sm_tlbi_op_regime_kind decode_tlbi_regime_kind(enum tlbi_kind k)
{
	switch (k) {
	case TLBI_vale2is:
	case TLBI_vae2is:
		return TLBI_REGIME_EL2;

	case TLBI_vmalle1is:
	case TLBI_vmalle1:
	case TLBI_ipas2e1is:
	case TLBI_vmalls12e1:
	case TLBI_vmalls12e1is:
	case TLBI_alle1is:
		return TLBI_REGIME_EL10;

	default:
		BUG(); // TODO: missing kind
	}
}

static bool __decoded_tlbi_has_asid(struct trans_tlbi_data data, u8 *out_asid)
{
	switch (data.tlbi_kind) {
	case TLBI_vale2is:
	case TLBI_vae2is:
		*out_asid = data.value & TLBI_ASID_MASK;
		return true;

	case TLBI_vmalle1is:
	case TLBI_vmalle1:
	case TLBI_ipas2e1is:
	case TLBI_vmalls12e1:
	case TLBI_vmalls12e1is:
	case TLBI_alle1is:
		return false;

	default:
		BUG(); // TODO: missing kind
	}
}

struct tlbi_op_method_by_address_data decode_tlbi_by_addr(struct trans_tlbi_data data)
{
	struct tlbi_op_method_by_address_data decoded_data = { 0 };

	decoded_data.page = data.value & TLBI_PAGE_MASK;

	switch (data.tlbi_kind) {
	case TLBI_vale2is:
		decoded_data.affects_last_level_only = true;
		break;
	default:
		decoded_data.affects_last_level_only = false;
		break;
	}

	u64 level = data.value & TLBI_TTL_MASK;

	if (level < 0b0100) {
		decoded_data.has_level_hint = false;
	} else {
		decoded_data.has_level_hint = true;
		decoded_data.level_hint = level & 0b11;
	}

	decoded_data.has_asid = __decoded_tlbi_has_asid(data, &decoded_data.asid);

	return decoded_data;
}

struct tlbi_op_method_by_address_space_id_data
	decode_tlbi_by_space_id(struct trans_tlbi_data data)
{
	struct tlbi_op_method_by_address_space_id_data decoded_data = { 0 };
	decoded_data.asid_or_vmid = 0;
	return decoded_data;
}

struct sm_tlbi_op decode_tlbi(struct trans_tlbi_data data)
{
	struct sm_tlbi_op tlbi;

	tlbi.stage = decode_tlbi_stage_kind(data.tlbi_kind);
	tlbi.regime = decode_tlbi_regime_kind(data.tlbi_kind);
	tlbi.shootdown = decode_tlbi_shootdown_kind(data.tlbi_kind);
	tlbi.method.kind = decode_tlbi_method_kind(data.tlbi_kind);
	switch (tlbi.method.kind) {
	case TLBI_OP_BY_INPUT_ADDR:
		tlbi.method.by_address_data = decode_tlbi_by_addr(data);
		break;

	case TLBI_OP_BY_ADDR_SPACE:
		tlbi.method.by_id_data = decode_tlbi_by_space_id(data);
		break;

	default:
		BUG(); // TODO: missing kind (TLBI ALL?)
	}

	return tlbi;
}

/////////////////////
// BBM requirements

static bool is_only_update_to_sw_bits(u64 before, u64 after)
{
	return (before & ~PTE_FIELD_UPPER_ATTRS_SW_MASK) ==
	       (after & ~PTE_FIELD_UPPER_ATTRS_SW_MASK);
}

/**
 * requires_bbm() - Whether a break-before-make sequence is architecturally required between two writes.
 * @loc: the memory location.
 * @before: the value of the first write.
 * @after: the value of the second write.
 *
 * See ARM DDI 0487 J.a D8.14.1 ("Using break-before-make when updating translation table entries")
 */
static bool requires_bbm(struct sm_location *loc, u64 before, u64 after)
{
	struct entry_exploded_descriptor before_descriptor =
		deconstruct_pte(loc->descriptor.ia_region.range_start, before,
				loc->descriptor.level, loc->descriptor.stage);
	struct entry_exploded_descriptor after_descriptor =
		deconstruct_pte(loc->descriptor.ia_region.range_start, after,
				loc->descriptor.level, loc->descriptor.stage);

	/* BBM is only a requirement between writes of valid PTEs */
	if (before_descriptor.kind == PTE_KIND_INVALID ||
	    after_descriptor.kind == PTE_KIND_INVALID)
		return false;

	/* if one is a table entry, really need to BBM between */
	if (before_descriptor.kind == PTE_KIND_TABLE || after_descriptor.kind == PTE_KIND_TABLE)
		return true;

	ghost_assert(before_descriptor.kind == PTE_KIND_MAP);
	ghost_assert(after_descriptor.kind == PTE_KIND_MAP);

	/* if a change in OA */
	if (before_descriptor.map_data.oa_region.range_size !=
	    after_descriptor.map_data.oa_region.range_size) {
		// TODO: BS: this is overapproximate,
		//           should be: "and if at least one is writeable, or memory contents different"
		return true;
	}

	// TODO: BS: a change in memory type, shareability, or cacheability
	// TODO: BS: FEAT_BBM (?)
	// TODO: BS: global entries (?)
	// over approximate all of the above, by checking everything same except maybe SW bits.
	if (! is_only_update_to_sw_bits(before, after))
		return true;

	return false;
}

////////////////////
// Reachability

static void clean_reachability_checker_cb(struct pgtable_traverse_context *ctxt)
{
	struct sm_location *loc = ctxt->loc;

	if (! loc->initialised)
		return;

	if (loc->state.kind == STATE_PTE_INVALID_UNCLEAN) {
		bool *data = (bool *)ctxt->data;
		*data = false;
	}
}

/*
 * if loc (was) a table entry, traverse the old children
 * and check they were all clean (VALID or INVALID, but not INVALID_UNCLEAN).
 */
static bool pre_all_reachable_clean(struct sm_location *loc)
{
	bool all_clean;

	if (! loc->is_pte)
		return true;

	// sanity check: it's actually in a tree somewhere...
	// If the location is not owned by a thread, check that we can reach it by walking
	// from the registered root.
	if (loc->thread_owner == -1) {
		struct pgtable_walk_result pte = find_pte(loc);
		if (! pte.found) {
			GHOST_WARN("loc.is_pte should imply existence in pgtable");
			ghost_assert(false);
		}
	}

	if (loc->descriptor.kind != PTE_KIND_TABLE) {
		return true;
	}

	// if the old value was a table, then traverse it from here.
	all_clean = true;
	traverse_pgtable_from(loc->owner, loc->descriptor.table_data.next_level_table_addr,
			      loc->descriptor.ia_region.range_start, loc->descriptor.level + 1,
			      loc->descriptor.stage, clean_reachability_checker_cb,
			      READ_UNLOCKED_LOCATIONS, &all_clean);

	// NOTE: the traversal may have unset all_clean.
	return all_clean;
}

static void initialise_location(struct sm_location *loc, u64 val)
{
	if (loc->initialised)
		GHOST_MODEL_CATCH_FIRE("cannot initialise an already-initialised location");

	loc->initialised = true;

	// by default, the location is not owned by any thread
	loc->thread_owner = -1;

	// sanity check: we really aren't writing to it ...
	if (is_on_write_transition(loc->phys_addr))
		ghost_assert(false);

	loc->val = val;
	loc->is_pte = false;
}

/**
 * Callback to mark a location in the page table as a page table entry
 * in the ghost model.
*/
void mark_cb(struct pgtable_traverse_context *ctxt)
{
	struct sm_location *loc = ctxt->loc;

	if (! loc->initialised) {
		initialise_location(loc, ctxt->descriptor);
	} else if (loc->is_pte) {
		GHOST_MODEL_CATCH_FIRE("double-use pte");
	}

	// mark that this location is now an active pte
	// and start following the automata
	loc->is_pte = true;
	loc->owner = (sm_owner_t)ctxt->root;
	loc->descriptor = ctxt->exploded_descriptor;
	loc->state = initial_state(ctxt->exploded_descriptor.ia_region.range_start,
				   ctxt->descriptor, ctxt->level, ctxt->stage);
}

void unmark_cb(struct pgtable_traverse_context *ctxt)
{
	struct sm_location *loc = ctxt->loc;

	if (! loc->initialised) {
		initialise_location(loc, ctxt->descriptor);
	} else if (! loc->is_pte) {
		// TODO: BS: is this catch-fire or simply unreachable?
		GHOST_MODEL_CATCH_FIRE("unmark non-PTE");
	}

	// mark that this location is no longer an active pte
	// and stop following the automata
	loc->is_pte = false;

	// can now forget about the location entirely
	forget_location(loc);
}

/**
 * walker function to mark the PTE as not writable. This function is not exercised in
 * pKVM.
 */
void mark_not_writable_cb(struct pgtable_traverse_context *ctxt)
{
	struct sm_location *loc = ctxt->loc;

	if (loc->thread_owner >= 0)
		GHOST_MODEL_CATCH_FIRE(
			"The parent of an entry that is owned by a thread has been invalidated");

	if (! loc->initialised) {
		// unreachable
		BUG();
	} else if (! loc->is_pte) {
		// unreachable
		BUG();
	} else {
		// mark the child as not writable
		loc->state.kind = STATE_PTE_NOT_WRITABLE;
	}
}

///////////////////
// Pagetable roots

static inline struct cm_thrd_ctxt *current_thread_context(void)
{
	return &MODEL()->thread_context[cpu_id()];
}

struct root *get_current_ttbr(void)
{
	return current_thread_context()->current_s1;
}

struct root *get_current_vttbr(void)
{
	return current_thread_context()->current_s2;
}

struct root *retrieve_root_for_id(struct roots *roots, addr_id_t id)
{
	for (int i = 0; i < roots->len; i++) {
		if (roots->roots[i].id == id) {
			return &roots->roots[i];
		}
	}
	return NULL;
}

struct root *retrieve_root_for_baddr(struct roots *roots, sm_owner_t root)
{
	for (int i = 0; i < roots->len; i++) {
		if (roots->roots[i].baddr == root) {
			return &roots->roots[i];
		}
	}
	return NULL;
}

void free_root(struct roots *roots, struct root *root)
{
	ghost_assert(root != NULL);

	for (int i = 0; i < roots->len; i++) {
		/* remove exactly this root object */
		if (&roots->roots[i] == root) {
			/* swap old last slot in */
			if (i < roots->len - 1)
				roots->roots[i] = roots->roots[roots->len - 1];

			roots->len--;
			return;
		}
	}

	/* should never be trying to free a root that does not exist */
	ghost_assert(false);
}

bool stage_from_ttbr(enum ghost_sysreg_kind sysreg, entry_stage_t *out_stage)
{
	switch (sysreg) {
	case SYSREG_TTBR_EL2:
		*out_stage = ENTRY_STAGE1;
		return true;

	case SYSREG_VTTBR:
		*out_stage = ENTRY_STAGE2;
		return true;

	default:
		return false;
	}
}

void try_register_root(struct roots *roots, phys_addr_t baddr, addr_id_t id)
{
	struct root new_root;
	GHOST_LOG_CONTEXT_ENTER();

	if (roots->len >= MAX_ROOTS) {
		GHOST_MODEL_CATCH_FIRE("too many roots");
	}

	new_root = (struct root){
		.baddr = baddr,
		.id = id,
		.refcount = 0,
	};
	roots->roots[roots->len++] = new_root;

	traverse_pgtable(baddr, roots->stage, mark_cb, READ_UNLOCKED_LOCATIONS, NULL);
	GHOST_LOG_CONTEXT_EXIT();
}

static void try_unregister_root(entry_stage_t stage, phys_addr_t root)
{
	struct roots *roots;
	struct root *assoc_root;
	GHOST_LOG_CONTEXT_ENTER();

	roots = (stage == ENTRY_STAGE1) ? &MODEL()->roots_s1 : &MODEL()->roots_s2;
	assoc_root = retrieve_root_for_baddr(roots, root);

	if (! assoc_root)
		GHOST_MODEL_CATCH_FIRE("root does not exist");

	if (assoc_root->refcount > 0)
		GHOST_MODEL_CATCH_FIRE("cannot release table still in use");

	traverse_pgtable(root, stage, unmark_cb, READ_UNLOCKED_LOCATIONS, NULL);
	free_root(roots, assoc_root);

	GHOST_LOG_CONTEXT_EXIT();
}

////////////////////
// Step write sysreg

static void step_msr(struct ghost_hw_step *step)
{
	bool ret;
	phys_addr_t root;
	vmid_t id;
	entry_stage_t stage;
	struct roots *roots;
	struct root *assoc_root;

	struct cm_thrd_ctxt *ctxt = current_thread_context();

	// TODO: BS: also remember which is current?
	switch (step->msr_data.sysreg) {
	case SYSREG_TTBR_EL2:
	case SYSREG_VTTBR:
		ret = stage_from_ttbr(step->msr_data.sysreg, &stage);
		ghost_assert(ret);
		root = ttbr_extract_baddr(step->msr_data.val);
		id = ttbr_extract_id(step->msr_data.val);

		/* TTBR0_EL2 in non-VHE mode has a Res0 ASID */
		if (step->msr_data.sysreg == SYSREG_TTBR_EL2) {
			if (id != 0) {
				GHOST_MODEL_CATCH_FIRE("TTBR0_EL2 ASID is reserved 0");
			}
		}

		roots = (stage == ENTRY_STAGE1) ? &MODEL()->roots_s1 : &MODEL()->roots_s2;

		/* if that root with that id exists already, were just context switching */
		assoc_root = retrieve_root_for_baddr(roots, root);
		if (assoc_root && assoc_root->id == id) {
			goto context_switch;
		}
		/* see if that root is already associated with a different (VM/AS)ID */
		else if (assoc_root && assoc_root->id != id) {
			GHOST_MODEL_CATCH_FIRE("root already associated with an (VM/AS)ID");
		}

		/* see if VMID is already associated */
		assoc_root = retrieve_root_for_id(roots, id);
		if (assoc_root && assoc_root->baddr != root) {
			GHOST_MODEL_CATCH_FIRE("duplicate (VM/AS)ID");
		}
		/* if that VMID is free, check we have not already associated a different VMID */
		else if (assoc_root && assoc_root->id != id) {
			GHOST_MODEL_CATCH_FIRE("root already associated with an (VM/AS)ID");
		}
		/* otherwise, that VMID is free and this root has no associated VMID
		 * so attach this one */
		else {
			try_register_root(roots, root, id);
		}

context_switch:
		/* decrement refcount on current (if applicable)*/
		assoc_root = (stage == ENTRY_STAGE1) ? ctxt->current_s1 : ctxt->current_s2;
		if (assoc_root)
			assoc_root->refcount--;

		/* and increment refcount on one we just switched to */
		assoc_root = retrieve_root_for_id(roots, id);
		ghost_assert(assoc_root);
		assoc_root->refcount++;

		/* and make it the curent context */
		if (stage == ENTRY_STAGE1) {
			ctxt->current_s1 = assoc_root;
		} else {
			ctxt->current_s2 = assoc_root;
		}

		break;

	default:
		GHOST_MODEL_CATCH_FIRE(
			"wrote to unsupported sysreg - only support writes to (V)TTBR");
	}
}

////////////////////////
// Step on memory write

static void __update_descriptor_on_write(struct sm_location *loc, u64 val)
{
	loc->descriptor = deconstruct_pte(loc->descriptor.ia_region.range_start, val,
					  loc->descriptor.level, loc->descriptor.stage);
}

/*
 * when writing a new table entry
 * must ensure that the child table(s) are all clean
 * and not owned by another pgtable
 * then mark them as owned
 */
static void step_write_table_mark_children(pgtable_traverse_cb visitor_cb,
					   struct sm_location *loc)
{
	if (loc->descriptor.kind == PTE_KIND_TABLE) {
		if (! pre_all_reachable_clean(loc)) {
			GHOST_MODEL_CATCH_FIRE(
				"BBM write table descriptor with unclean children");
		}

		traverse_pgtable_from(
			loc->owner, loc->descriptor.table_data.next_level_table_addr,
			loc->descriptor.ia_region.range_start, loc->descriptor.level + 1,
			loc->descriptor.stage, visitor_cb, READ_UNLOCKED_LOCATIONS, NULL);
	}
}

static void step_write_on_invalid(enum memory_order_t mo, struct sm_location *loc, u64 val)
{
	if (! is_desc_valid(val)) {
		// overwrite invalid with another invalid is identity
		return;
	}

	// update the descriptor
	__update_descriptor_on_write(loc, val);

	// check that if we're writing a TABLE entry
	// that the new tables are all 'good'
	step_write_table_mark_children(mark_cb, loc);

	// invalid -> valid
	loc->state.kind = STATE_PTE_VALID;

	// globally all cores see a valid value now
	// (because of the lack of unsychronised races on ptes)
	for (int i = 0; i < MAX_CPU; i++) {
		loc->state.valid_state.lvs[i] = LVS_unguarded;
	}
}

static void step_write_on_invalid_unclean(enum memory_order_t mo, struct sm_location *loc,
					  u64 val)
{
	if (is_desc_valid(val)) {
		GHOST_MODEL_CATCH_FIRE("BBM invalid unclean->valid");
		return;
	} else {
		// can overwrite invalid with another invalid (even if not DSB+TLBI'd yet).
		// this doesn't affect the local state, so just the identity.
		return;
	}
}

static void step_write_on_valid(enum memory_order_t mo, struct sm_location *loc, u64 val)
{
	u64 old = read_phys_pre(loc->phys_addr);

	if (is_desc_valid(val)) {
		if (! requires_bbm(loc, old, val)) {
			return;
		}

		GHOST_MODEL_CATCH_FIRE("BBM valid->valid");
	}

	loc->state.kind = STATE_PTE_INVALID_UNCLEAN;
	loc->state.invalid_unclean_state = (struct aut_invalid){ .invalidator_tid = cpu_id(),
								 .old_valid_desc = old,
								 .lis = LIS_unguarded };

	// Add location to the list of unclean locations
	add_location_to_unclean_PTE(loc);

	step_write_table_mark_children(mark_not_writable_cb, loc);
}

static void step_write_on_unwritable(struct sm_location *loc, u64 val)
{
	// If the write does not change anything, continue
	if (loc->val == val)
		return;

	// Writing invalid on invalid is also benign
	if ((! is_desc_valid(loc->val)) && (! is_desc_valid(val)))
		return;

	// You can't change an unwritable descriptor.
	GHOST_MODEL_CATCH_FIRE("Wrote on a page with an unclean parent");
}

static void check_write_is_authorized(struct sm_location *loc, struct ghost_hw_step *step,
				      u64 val)
{
	struct lock_state *state_of_lock;

	/* if synchronisation is disabled, then cannot check write authorization
	 * as it comes from the synchronisation itself */
	if (! opts()->check_opts.check_synchronisation)
		return;

	// if the location is owned by a given thread, just test if it is this one
	if (loc->thread_owner >= 0) {
		if (loc->thread_owner == cpu_id())
			// Write unauthorized to change?
			return;
		else
			GHOST_MODEL_CATCH_FIRE(
				"Location owned by a thread but accessed by another");
	}

	assert_owner_locked(loc, &state_of_lock);
	ghost_assert(state_of_lock);
	switch (state_of_lock->write_authorization) {
	case AUTHORIZED:
		// We are not authorized to write plain on it anymore
		state_of_lock->write_authorization = UNAUTHORIZED_PLAIN;
		break;
	case UNAUTHORIZED_PLAIN:
		// We cannot write plain (exept invalid on invalid)
		if (step->write_data.mo == WMO_plain) {
			if (loc->state.kind == STATE_PTE_VALID || is_desc_valid(val))
				GHOST_MODEL_CATCH_FIRE("Wrote plain without authorization");
		}
		break;
	default:
		BUG();
	}
}

static void step_write(struct ghost_hw_step *step)
{
	enum memory_order_t mo;
	u64 val;
	struct sm_location *loc;

	ghost_assert(step->kind == HW_MEM_WRITE);

	mo = step->write_data.mo;
	val = step->write_data.val;

	// look inside memory at `addr`
	loc = location(step->write_data.phys_addr);

	if (! loc->is_pte) {
		goto done;
	}

	// must own the lock on the pgtable this pte is in.
	check_write_is_authorized(loc, step, val);

	// actually is a pte, so have to do some checks...
	switch (loc->state.kind) {
	case STATE_PTE_VALID:
		step_write_on_valid(mo, loc, val);
		break;
	case STATE_PTE_INVALID_UNCLEAN:
		step_write_on_invalid_unclean(mo, loc, val);
		break;
	case STATE_PTE_INVALID:
		step_write_on_invalid(mo, loc, val);
		break;
	case STATE_PTE_NOT_WRITABLE:
		step_write_on_unwritable(loc, val);
		break;
	default:
		unreachable();
	}

done:
	loc->val = val;
	return;
}

////////////////////////
// Step on memory read

static void step_read(struct ghost_hw_step *step)
{
	struct sm_location *loc;
	ghost_assert(step->kind == HW_MEM_READ);

	loc = location(step->read_data.phys_addr);

	// read doesn't have any real behaviour, except to return the value stored in memory.
	// so we just assert that the value in the real concrete memory is what we are tracking.
	// (the read_phys already does this check, but it's never bad to double check).
	if (read_phys(loc->phys_addr) != loc->val) {
		GHOST_MODEL_CATCH_FIRE("the ghost model detected a PTE that changed under it");
	}
}

/////////////////////
// ISB

static void step_isb(struct ghost_hw_step *step)
{
	// TODO: thread-local steps
}

/////////////////
// Step on a DSB

/*
 * when invalidating a zeroed table entry
 * unmark them as now no longer owned by the parent
 *
 * TODO: BS: is this correct?
 * TODO: TF: This is not tested as pKVM does not invalidate table descriptors.
 */
static void step_dsb_invalid_unclean_unmark_children(struct sm_location *loc)
{
	u64 old;
	struct aut_invalid aut;
	struct entry_exploded_descriptor old_desc;

	if (loc->state.kind != STATE_PTE_INVALID_UNCLEAN) {
		return;
	}

	GHOST_LOG_CONTEXT_ENTER();

	aut = loc->state.invalid_unclean_state;
	old = aut.old_valid_desc;
	old_desc = deconstruct_pte(loc->descriptor.ia_region.range_start, old,
				   loc->descriptor.level, loc->descriptor.stage);

	// look at the old entry, and see if it was a table.
	if (old_desc.kind == PTE_KIND_TABLE) {
		// if we zero child entry, then zero the table entry
		// require that the child entries were TLBI'd first.
		// this means we don't have to recursively check the olds all the way down...
		// TODO: BS: is this too strong?
		if (! pre_all_reachable_clean(loc)) {
			GHOST_MODEL_CATCH_FIRE(
				"BBM write table descriptor with unclean children");
		}

		traverse_pgtable_from(loc->owner, old_desc.table_data.next_level_table_addr,
				      loc->descriptor.ia_region.range_start,
				      loc->descriptor.level, loc->descriptor.stage, unmark_cb,
				      READ_UNLOCKED_LOCATIONS, NULL);
	}

	GHOST_LOG_CONTEXT_EXIT();
}

void dsb_visitor(struct pgtable_traverse_context *ctxt)
{
	thread_identifier this_cpu = cpu_id();
	struct sm_location *loc = ctxt->loc;
	enum dxb_kind dsb_kind = *(enum dxb_kind *)ctxt->data;

	// If the location is not locked then do not do anything
	if (! is_location_locked(ctxt->loc))
		return;

	if (dsb_kind == DxB_nsh) {
		if (opts()->check_opts.promote_DSB_nsh) {
			// silence noisy warning...
			// GHOST_WARN("DSB NSH not supported -- Assuming DSB ISH");
			dsb_kind = DxB_ish;
		} else {
			GHOST_MODEL_CATCH_FIRE("Unsupported DSB NSH");
		}
	}

	// we just did a DSB:
	switch (loc->state.kind) {
	case STATE_PTE_INVALID_UNCLEAN:
		// if the invalid pte wasn't written by this cpu, skip.
		if (! (loc->state.invalid_unclean_state.invalidator_tid == this_cpu)) {
			break;
		}

		switch (loc->state.invalid_unclean_state.lis) {
		case LIS_unguarded:
			// if not yet DSBd, then tick it forward
			loc->state.invalid_unclean_state.lis = LIS_dsbed;
			break;
		case LIS_dsb_tlbied:
			// if DSB+TLBI'd already, this DSB then propagates that TLBI everywhere,
			// but only if it's the right kind of DSB
			// also release the children
			if (dsb_kind == DxB_ish) {
				// All the children can be released
				step_dsb_invalid_unclean_unmark_children(loc);
				// The PTE is now clean
				loc->state.kind = STATE_PTE_INVALID;
				loc->state.invalid_clean_state.invalidator_tid = this_cpu;
				// So the new descriptor is the only one visible
				__update_descriptor_on_write(loc, loc->val);
			}
			break;
		case LIS_dsb_tlbi_ipa:
			// if DSB+TLBI IPA, then advance the state locally so the next TLBI can happen.
			// but only if it's the right kind of DSB
			if (dsb_kind == DxB_ish) {
				loc->state.invalid_unclean_state.lis = LIS_dsb_tlbi_ipa_dsb;
			}
			break;
		default:
			break;
		}
		break;
	default:
		break;
	}
}

static void reset_write_authorizations(void)
{
	int len = MODEL()->lock_state.len;
	struct lock_state *states = MODEL()->lock_state.locker;
	for (int i = 0; i < len; i++) {
		if (states[i].id == cpu_id())
			states[i].write_authorization = AUTHORIZED;
	}
}

static void step_dsb(struct ghost_hw_step *step)
{
	// annoyingly, DSBs aren't annotated with their addresses.
	// so we do the really dumb thing: we go through every pagetable that we know about
	// and step any we find in the right state.
	traverse_all_unclean_PTE(dsb_visitor, &step->barrier_data.dxb_data, ENTRY_STAGE_NONE);

	// The DSBs also enforce a sufficient barrier to allow plain writes again
	reset_write_authorizations();
}

/////////////////////
// Barriers

static void step_barrier(struct ghost_hw_step *step)
{
	switch (step->barrier_data.kind) {
	case BARRIER_DSB:
		step_dsb(step);
		break;

	case BARRIER_ISB:
		step_isb(step);
		break;
	}
}

///////////////////
// Step on a TLBI

static void step_pte_on_tlbi_after_dsb(struct sm_location *loc, struct sm_tlbi_op *tlbi)
{
	switch (tlbi->regime) {
	case TLBI_REGIME_EL2:
		loc->state.invalid_unclean_state.lis = LIS_dsb_tlbied;
		break;

	case TLBI_REGIME_EL10:
		switch (tlbi->stage) {
		case TLBI_OP_STAGE1:
			/* stage1 invalidation before stage2 invalidation is ineffective */
			break;

		case TLBI_OP_STAGE2:
			/* stage2 invalidation alone only invalidates those ipas */
			loc->state.invalid_unclean_state.lis = LIS_dsb_tlbi_ipa;
			break;

		case TLBI_OP_BOTH_STAGES:
			loc->state.invalid_unclean_state.lis = LIS_dsb_tlbied;
			break;

		default:
			unreachable();
		}
		break;

	default:
		unreachable();
	}
}

static void step_pte_on_tlbi_after_tlbi_ipa(struct sm_location *loc, struct sm_tlbi_op *tlbi)
{
	ghost_assert(tlbi->regime == TLBI_REGIME_EL10);

	switch (tlbi->stage) {
	case TLBI_OP_STAGE1:
	case TLBI_OP_BOTH_STAGES:
		loc->state.invalid_unclean_state.lis = LIS_dsb_tlbied;
		break;

	case TLBI_OP_STAGE2:
		/* additional second-stage invalidation has no added effect */
		break;

	default:
		unreachable();
	}
}

static void step_pte_on_tlbi(struct pgtable_traverse_context *ctxt)
{
	struct sm_location *loc = ctxt->loc;
	struct sm_tlbi_op *tlbi = (struct sm_tlbi_op *)ctxt->data;

	thread_identifier this_cpu = cpu_id();

	// sanity check: if doing a TLBI on a tree with a root we know about
	// then all the children in that tree must have been marked by the (V)TTBR registration
	// or the writes of table entries...
	ghost_assert(loc->initialised);

	switch (loc->state.kind) {
	case STATE_PTE_INVALID_UNCLEAN:
		// if the core that did the unclean write to this pte is not the core doing the tlbi
		// then that tlbi has no effect in the ghost model
		if (loc->state.invalid_unclean_state.invalidator_tid != this_cpu)
			return;

		// TODO: BS: finish dispatch on (loc LIS * TLBI kind)
		switch (loc->state.invalid_unclean_state.lis) {
		// trying to do a TLBI without having done a DSB has no effect
		case LIS_unguarded:
			return;
		case LIS_dsbed:
			step_pte_on_tlbi_after_dsb(loc, tlbi);
			break;
		case LIS_dsb_tlbi_ipa_dsb:
			step_pte_on_tlbi_after_tlbi_ipa(loc, tlbi);
			break;
		default:
			BUG(); // TODO: BS: other TLBIs
		}

		break;
	default:
		/* if clean, no effect */
		break;
	}
}

static bool all_children_invalid(struct sm_location *loc)
{
	phys_addr_t table_addr;
	struct sm_location *child;

	// Assert that we are on a table descriptor
	ghost_assert(loc->initialised && loc->is_pte);

	if (loc->descriptor.kind != PTE_KIND_TABLE)
		return true;

	table_addr = loc->descriptor.table_data.next_level_table_addr;

	for (int i = 0; i < 512; i++) {
		// For each child, check that it is an invalid child
		child = location(table_addr + 8 * i);
		ghost_assert(child->initialised && child->is_pte);
		ghost_assert(child->state.kind == STATE_PTE_NOT_WRITABLE);
		if (child->descriptor.kind != PTE_KIND_INVALID) {
			return false;
		}
	}

	return true;
}

static bool __get_tlbi_asid(struct sm_tlbi_op *tlbi, u64 *out_id)
{
	switch (tlbi->method.kind) {
	case TLBI_OP_BY_INPUT_ADDR:
		if (tlbi->method.by_address_data.has_asid) {
			*out_id = tlbi->method.by_address_data.asid;
			return true;
		}
		break;

	case TLBI_OP_BY_ADDR_SPACE:
		if (tlbi->stage == TLBI_OP_STAGE1) {
			*out_id = tlbi->method.by_id_data.asid_or_vmid;
			return true;
		}
		break;

	default:
		break;
	}

	return false;
}

/**
 * __should_perform_tlbi_matches_id() - Check that the identifier associated with the TLBI matches the pte
 */
static bool __should_perform_tlbi_matches_id(struct pgtable_traverse_context *ctxt,
					     struct sm_tlbi_op *tlbi)
{
	/* for VMID checks, we read the VTTBR
	 * and check the VTTBR VMID annotation matches the one associated with this root
	 */
	if (tlbi->regime == TLBI_REGIME_EL10 && ctxt->exploded_descriptor.stage == ENTRY_STAGE2) {
		struct root *pte_root = retrieve_root_for_baddr(&MODEL()->roots_s2, ctxt->root);
		if (get_current_vttbr()->id != pte_root->id)
			return false;
		else
			return true;
	}

	/* for TLBI that affects an ASID, it is supplied as an argument to the TLBI */
	if (tlbi->regime == TLBI_REGIME_EL2 && ctxt->exploded_descriptor.stage == ENTRY_STAGE1) {
		struct root *pte_root = retrieve_root_for_baddr(&MODEL()->roots_s1, ctxt->root);
		u64 asid;

		if (__get_tlbi_asid(tlbi, &asid))
			if (asid != pte_root->id)
				return false;
	}

	return true;
}

/**
 * __should_perform_tlbi_matches_level() - Check that the level of the pte matches the TLBI level hint
 */
static bool __should_perform_tlbi_matches_level(struct pgtable_traverse_context *ctxt,
						struct sm_tlbi_op *tlbi)
{
	if (ctxt->level != 3 && tlbi->method.by_address_data.affects_last_level_only)
		return false;
	else
		return true;
}

/**
 * __should_perform_tlbi_matches_level() - Check that the level of the pte matches the TLBI level hint
 */
static bool __should_perform_tlbi_matches_addr(struct pgtable_traverse_context *ctxt,
					       struct sm_tlbi_op *tlbi)
{
	u64 tlbi_addr;
	u64 ia_start;
	u64 ia_end;

	// input-address range of the PTE we're visiting
	ia_start = ctxt->exploded_descriptor.ia_region.range_start;
	ia_end = ia_start + ctxt->exploded_descriptor.ia_region.range_size;
	tlbi_addr = tlbi->method.by_address_data.page << PAGE_SHIFT;

	return (ia_start <= tlbi_addr) && (tlbi_addr < ia_end);
}

static bool should_perform_tlbi(struct pgtable_traverse_context *ctxt)
{
	struct sm_tlbi_op *tlbi;

	// If the location is not locked then do not apply the TLBI
	if (! is_location_locked(ctxt->loc))
		return false;

	tlbi = (struct sm_tlbi_op *)ctxt->data;

	// TODO: BS: need to match up regime with which pgtable loc is in.
	//           and broadcast and so on.

	if (! tlbi->shootdown) {
		if (opts()->check_opts.promote_TLBI_nsh) {
			tlbi->shootdown = true;
		} else {
			GHOST_MODEL_CATCH_FIRE("Unsupported TLBI (expected broadcast)");
		}
	}

	if (tlbi->method.kind == TLBI_OP_BY_ADDR_SPACE) {
		if (opts()->check_opts.promote_TLBI_by_id) {
			tlbi->method.kind = TLBI_OP_BY_ALL;
		}
	}

	switch (tlbi->method.kind) {
	case TLBI_OP_BY_INPUT_ADDR:

		// If the PTE has valid children, the TLBI by VA is not enough
		if (! ctxt->leaf) {
			if (! all_children_invalid(ctxt->loc)) {
				return false;
			}
		}

		// Test if the VA address of the PTE is the same as the VA of the TLBI
		if (! __should_perform_tlbi_matches_addr(ctxt, tlbi))
			return false;

		/*
		 * if it is a leaf, but not at the last level, and we asked for last-level-only invalidation,
		 * then nothing happens
		 */
		if (! __should_perform_tlbi_matches_level(ctxt, tlbi))
			return false;

		/*
		 * check whether the address space identifier (if any) associated with this TLBI
		 * matches the id of the pte
		 */
		if (! __should_perform_tlbi_matches_id(ctxt, tlbi))
			return false;

		break;

	case TLBI_OP_BY_ADDR_SPACE:
		/*
		 * check whether the address space identifier (if any) associated with this TLBI
		 * matches the id of the pte
		 */
		if (! __should_perform_tlbi_matches_id(ctxt, tlbi))
			return false;

	case TLBI_OP_BY_ALL:
		return true;

	default:
		unreachable();
	}

	return true;
}

static void tlbi_visitor(struct pgtable_traverse_context *ctxt)
{
	GHOST_LOG_CONTEXT_ENTER();

	if (should_perform_tlbi(ctxt)) {
		step_pte_on_tlbi(ctxt);
	}

	GHOST_LOG_CONTEXT_EXIT();
}

static void step_tlbi(struct ghost_hw_step *step)
{
	struct sm_tlbi_op decoded;
	ghost_assert(step->kind == HW_TLBI);

	decoded = decode_tlbi(step->tlbi_data);
	switch (decoded.regime) {
	/* TLBIs that hit host/guest tables */
	case TLBI_REGIME_EL10:
		traverse_all_unclean_PTE(tlbi_visitor, &decoded, ENTRY_STAGE2);
		break;

	/* TLBIs that hit pKVM's own pagetable */
	case TLBI_REGIME_EL2:
		traverse_all_unclean_PTE(tlbi_visitor, &decoded, ENTRY_STAGE1);
		break;

	default:
		unreachable();
	}
}

///////////////////////
// Hardware Steps

static void step_hw(struct ghost_hw_step *step)
{
	switch (step->kind) {
	case HW_MEM_WRITE:
		step_write(step);
		break;
	case HW_MEM_READ:
		step_read(step);
		break;
	case HW_BARRIER:
		step_barrier(step);
		break;
	case HW_TLBI:
		step_tlbi(step);
		break;
	case HW_MSR:
		step_msr(step);
		break;
	default:
		BUG();
	}
}

//////////////////////
// HINT

void check_release_cb(struct pgtable_traverse_context *ctxt)
{
	struct sm_location *loc = ctxt->loc;

	ghost_assert(loc->initialised);
	ghost_assert(loc->is_pte);

	if (loc->state.kind == STATE_PTE_INVALID_UNCLEAN)
		GHOST_MODEL_CATCH_FIRE("cannot release table where children are still unclean");
}

static void step_hint_set_root_lock(u64 root, gsm_lock_addr_t *lock)
{
	// TODO: BS: on teardown a VM's lock might get disassociated,
	// then re-associated later with a different lock.
	//
	// currently this just swaps the lock over without any safety checks.
	associate_lock(root, lock);
}

static void step_hint_set_owner_root(u64 phys, u64 root)
{
	// the whole page should be owned by the same owner
	// but in the ghost model, the metadata is split by 64-bit location,
	// so we iterate to set all in the same page.
	for (u64 p = PAGE_ALIGN_DOWN(phys); p < PAGE_ALIGN(phys); p += 8) {
		struct sm_location *loc = location(p);

		if (loc->is_pte)
			GHOST_MODEL_CATCH_FIRE("cannot change owned root if already in a tree");

		// before letting us disassociate a pte with a given VM/tree,
		// first we need to check that it's clean enough to forget about
		// the association with the old VM
		traverse_pgtable_from(root, loc->owner, loc->descriptor.ia_region.range_size,
				      loc->descriptor.level, loc->descriptor.stage,
				      check_release_cb, READ_UNLOCKED_LOCATIONS, NULL);

		loc->owner = root;
	}
}

static void step_hint_release_table(u64 root)
{
	struct sm_location *loc = location(root);

	// TODO: BS: also check that it's not currently in-use by someone

	// need to check the table is clean.
	traverse_pgtable_from(root, loc->owner, loc->descriptor.ia_region.range_size,
			      loc->descriptor.level, loc->descriptor.stage, check_release_cb,
			      READ_UNLOCKED_LOCATIONS, NULL);
	try_unregister_root(loc->descriptor.stage, root);

	// remove the mapping from the root to the lock of the page-table
	unregister_lock(root);
}

static void step_hint_set_PTE_thread_owner(u64 phys, u64 val)
{
	// TODO: mark all the parents as immutable
	struct sm_location *loc = location(phys);

	ghost_assert(loc->initialised);
	ghost_assert(loc->is_pte);
	ghost_assert(loc->descriptor.level == 3);

	loc->thread_owner = val;
}

static void step_hint(struct ghost_hint_step *step)
{
	switch (step->kind) {
	case GHOST_HINT_SET_ROOT_LOCK:
		step_hint_set_root_lock(step->location, (gsm_lock_addr_t *)step->value);
		break;
	case GHOST_HINT_SET_OWNER_ROOT:
		step_hint_set_owner_root(step->location, step->value);
		break;
	case GHOST_HINT_RELEASE_TABLE:
		step_hint_release_table(step->location);
		break;
	case GHOST_HINT_SET_PTE_THREAD_OWNER:
		step_hint_set_PTE_thread_owner(step->location, step->value);
		break;
	default:
		unreachable();
	}
}

//////////////////////
// ABS

static void __step_lock(gsm_lock_addr_t *lock_addr)
{
	int len = MODEL()->lock_state.len;
	// look for the address in the map
	for (int i = 0; i < len; i++) {
		if (MODEL()->lock_state.address[i] == lock_addr) {
			GHOST_MODEL_CATCH_FIRE("Tried to lock a component that was alerady held");
		}
	}
	// If the lock is not yet in the map, we append it
	ghost_assert(len < CASEMATE_MAX_LOCKS);

	MODEL()->lock_state.address[len] = lock_addr;
	MODEL()->lock_state.locker[len].id = cpu_id();
	MODEL()->lock_state.locker[len].write_authorization = AUTHORIZED;

	MODEL()->lock_state.len++;
}

static void __step_unlock(gsm_lock_addr_t *lock_addr)
{
	int len = MODEL()->lock_state.len;
	// look for the address in the map
	for (int i = 0; i < len; i++) {
		if (MODEL()->lock_state.address[i] == lock_addr) {
			if (MODEL()->lock_state.locker[i].id == cpu_id()) {
				// unlock the position
				len--;
				MODEL()->lock_state.locker[i] = MODEL()->lock_state.locker[len];
				MODEL()->lock_state.address[i] = MODEL()->lock_state.address[len];
				MODEL()->lock_state.len--;
				return;
			} else {
				GHOST_MODEL_CATCH_FIRE(
					"Tried to unlock a cpmponent that was held by another thread");
			}
		}
	}
	GHOST_MODEL_CATCH_FIRE("Tried to unlock a component that was not held");
}

static void __do_plain_write(u64 phys_addr, u64 val)
{
	struct ghost_hw_step write_step = {
		.kind = HW_MEM_WRITE,
		.write_data =
			(struct trans_write_data){
				.mo = WMO_plain,
				.phys_addr = phys_addr,
				.val = val,
			},
	};
	step_write(&write_step);
}

static void __step_memset(u64 phys_addr, u64 size, u64 val)
{
	/* for now... only support page-granularity memsets  */
	ghost_assert(IS_PAGE_ALIGNED(phys_addr));
	ghost_assert(IS_PAGE_ALIGNED(size));

	/* Implement MEMSET by repeated WRITE transitions. */
	for (u64 i = 0; i < size; i += 8)
		__do_plain_write(phys_addr + i, val);
}

static void __step_init(u64 phys_addr, u64 size)
{
	u64 p;
	for (p = phys_addr; p < phys_addr + size; p += 8) {
		struct sm_location *loc = location(p);

		/* permit re-initialising locations
		 * but in that case just update the state to be zero */
		if (! loc->initialised)
			initialise_location(loc, 0);
		else
			__do_plain_write(phys_addr, 0);
	}
}

static void step_abs(struct ghost_abs_step *step)
{
	switch (step->kind) {
	case GHOST_ABS_LOCK:
		__step_lock((gsm_lock_addr_t *)step->lock_data.address);
		break;
	case GHOST_ABS_UNLOCK:
		__step_unlock((gsm_lock_addr_t *)step->lock_data.address);
		break;
	case GHOST_ABS_INIT:
		// Nothing to do
		__step_init(step->init_data.location, step->init_data.size);
		break;
	case GHOST_ABS_MEMSET:
		__step_memset(step->memset_data.address, step->memset_data.size,
			      step->memset_data.value);
		break;
	default:
		unreachable();
	}
}

/////////////////
// Helpers

static inline bool should_print_state_on_step(void)
{
	if (! should_print_state())
		return false;

	if (should_track_only_watchpoints())
		return STATE()->touched_watchpoint;

	return true;
}

static inline bool should_print_diff_on_step(void)
{
	if (! should_print_diffs())
		return false;

	if (should_track_only_watchpoints())
		return STATE()->touched_watchpoint;

	return true;
}

void ensure_traced_current_transition(bool force)
{
	if (STATE()->traced_current_trans)
		return;

	if (force)
		/* skip further checks */
		goto do_trace;

	if (! should_trace())
		return;

	if (should_track_only_watchpoints() && ! STATE()->touched_watchpoint)
		return;

do_trace:
	trace_step(&CURRENT_TRANS());

	STATE()->traced_current_trans = true;
}

///////////////////////////
/// Generic Step

void step(struct casemate_model_step trans)
{
	GHOST_LOG_CONTEXT_ENTER();
	GHOST_LOG(trans, trans);

	/* XXX RO trans? */
	trans.seq_id = STATE()->transition_id++;

	STATE()->current_transition = trans;
	STATE()->touched_watchpoint = false;
	STATE()->traced_current_trans = false;

	if (! STATE()->is_initialised)
		goto out;

	if (! opts()->enable_checking)
		goto out;

	if (should_print_diffs())
		copy_cm_state_into(STATE()->st_pre);

	switch (trans.kind) {
	case TRANS_HW_STEP:
		step_hw(&trans.hw_step);
		break;
	case TRANS_ABS_STEP:
		step_abs(&trans.abs_step);
		break;
	case TRANS_HINT:
		step_hint(&trans.hint_step);
		break;
	default:
		unreachable();
	};

	/* do any tracing, printing or diffing */

	ensure_traced_current_transition(false);

	if (should_print_state_on_step()) {
		ghost_dump_model_state(NULL, MODEL());
		ghost_printf("\n");
	}

	if (should_print_diff_on_step()) {
		ghost_diff_and_print_sm_state(STATE()->st_pre, STATE()->st);
		ghost_printf("\n");
	}

out:
	ensure_traced_current_transition(false);
	GHOST_LOG_CONTEXT_EXIT();
}

void casemate_model_step(struct casemate_model_step trans)
{
	if (! LOAD_RLX(STATE()))
		return;

	if (! LOAD_RLX(STATE()->is_initialised))
		return;

	lock_sm();
	step(trans);
	unlock_sm();
}
