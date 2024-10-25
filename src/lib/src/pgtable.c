#include <casemate-impl.h>

//////////////////////
// pagetable traversal

#define PTE_BIT_VALID BIT(0)
#define PTE_BIT_TABLE BIT(1)
#define PTE_BITS_TABLE_POINTER GENMASK(47, 12)
#define PTE_BIT_OA_MSB 47

#define KiB_SHIFT 10ULL
#define MiB_SHIFT 20ULL
#define GiB_SHIFT 30ULL

#define KiB(n) ((n) << KiB_SHIFT)
#define MiB(n) ((n) << MiB_SHIFT)
#define GiB(n) ((n) << GiB_SHIFT)

// how much memory a map at level [N] maps
static const u64 MAP_SIZES[] = {
	[0] = GiB(512ULL),
	[1] = GiB(1ULL),
	[2] = MiB(2ULL),
	[3] = KiB(4ULL),
};

// G.b p2742 4KB translation granule has a case split on whether "the Effective value of TCR_ELx.DS or VTCR_EL2.DS is 1".
// DS is for 52-bit output addressing with FEAT_LPA2, and is zero in the register values we see; I'll hard-code that for now.  Thus, G.b says:
// - For a level 1 Block descriptor, bits[47:30] are bits[47:30] of the output address. This output address specifies a 1GB block of memory.
// - For a level 2 Block descriptor, bits[47:21] are bits[47:21] of the output address.This output address specifies a 2MB block of memory.
#define PTE_FIELD_LVL1_OA_MASK GENMASK(47, 30)
#define PTE_FIELD_LVL2_OA_MASK GENMASK(47, 21)
#define PTE_FIELD_LVL3_OA_MASK GENMASK(47, 12)

static u64 PTE_FIELD_OA_MASK[4] = {
	[1] = PTE_FIELD_LVL1_OA_MASK,
	[2] = PTE_FIELD_LVL2_OA_MASK,
	[3] = PTE_FIELD_LVL3_OA_MASK,
};

static u64 read_start_level(u64 tcr)
{
	u64 t0sz = (tcr & TCR_EL2_T0SZ_MASK) >> TCR_EL2_T0SZ_LO;
	// input address = (64 - t0sz) bits
	// max = 48
	// min = 21 (only level 3 table)
	// each 9 bits in-between increases start by 1 level
	u64 ia_bits = 64 - t0sz;
	return (48 - ia_bits) / 9;
}


static u64 discover_start_level(entry_stage_t stage)
{
	if (stage == ENTRY_STAGE2) {
		u64 vtcr = side_effect()->read_sysreg(SYSREG_VTCR_EL2);
		return read_start_level(vtcr);
	} else {
		u64 tcr = side_effect()->read_sysreg(SYSREG_TCR_EL2);
		return read_start_level(tcr);
	}
}

static u64 discover_page_size(entry_stage_t stage)
{
	u64 tcr;
	u64 tg0;

	if (stage == ENTRY_STAGE2) {
		tcr = side_effect()->read_sysreg(SYSREG_VTCR_EL2);
	} else {
		tcr = side_effect()->read_sysreg(SYSREG_TCR_EL2);
	}

	tg0 = (tcr & TCR_TG0_MASK) >> TCR_TG0_LO;

	if (tg0 == 0) {
		return 4*1024;
	} else if (tg0 == 1) {
		return 64*1024;
	} else if (tg0 == 2) {
		return 16*1024;
	} else {
		unreachable();
	}
}

static u64 discover_nr_concatenated_pgtables(entry_stage_t stage)
{
	u64 t0sz;

	/* stage1 is never concatenated */
	if (stage == ENTRY_STAGE1)
		return 1;

	/* as per J.a D8-5832 */

	// assume pkvm has 4k graule
	ghost_assert(discover_page_size(ENTRY_STAGE2) == PAGE_SIZE);

	// assume stage2 translations starting at level 0
	ghost_assert(discover_start_level(ENTRY_STAGE2) == 0);

	t0sz = (side_effect()->read_sysreg(SYSREG_VTCR_EL2) & 0b111111);

	// now we know t0sz must be between 24 and 12.
	if (t0sz >= 16) {
		return 1;
	} else if (t0sz == 15) {
		return 2;
	} else if (t0sz == 14) {
		return 4;
	} else if (t0sz == 13) {
		return 8;
	} else if (t0sz == 12) {
		return 16;
	} else {
		unreachable();
	}
}

bool is_desc_valid(u64 descriptor)
{
	return (descriptor & PTE_BIT_VALID) == PTE_BIT_VALID;
}

bool is_desc_table(u64 descriptor, u64 level, entry_stage_t stage)
{
	if (level == 3)
		return false;

	return (descriptor & PTE_BIT_TABLE) == PTE_BIT_TABLE;
}

u64 extract_output_address(u64 desc, u64 level)
{
	u64 OA_mask = PTE_FIELD_OA_MASK[level];
	return (desc & OA_mask);
}

u64 extract_table_address(u64 desc)
{
	return desc & PTE_BITS_TABLE_POINTER;
}

/**
 * parse_attrs() - Construct abstracted maplet attributes from the concrete pte encoding.
 * @stage: the stage (either ENTRY_STAGE1 or ENTRY_STAGE2) to parse the pte as from.
 * @mair: the concrete MAIR_ELx value to use for Stage 1 memory attributes.
 * @desc: the concrete 64-bit descriptor.
 * @level: the level this PTE is at in the table.
 * @next_level_aal: the attrs-at-level so far, for re-constructing hierarchical permissions.
 */
static struct entry_attributes parse_attrs(entry_stage_t stage, ghost_mair_t mair, u64 desc, u8 level, struct aal next_level_aal)
{
	// first fill in the permissions
	enum entry_permissions perms;
	enum entry_memtype_attr memtype_attr;
	switch (stage) {
	case ENTRY_STAGE1: {
		bool ro = __s1_is_ro(desc);
		bool xn = __s1_is_xn(desc);

		/* Stage1 always has R permission. */
		perms = ENTRY_PERM_R;

		/* If not read-only, also has W */
		if (!ro)
			perms |= ENTRY_PERM_W;

		/* If not e(x)-(n)ever, also has X */
		if (!xn)
			perms |= ENTRY_PERM_X;

		break;
	}
	case ENTRY_STAGE2: {
		bool r = __s2_is_r(desc);
		bool w = __s2_is_w(desc);
		bool xn = __s2_is_xn(desc);

		perms = 0;

		if (r)
			perms |= ENTRY_PERM_R;

		if (w)
			perms |= ENTRY_PERM_W;

		if (!xn)
			perms |= ENTRY_PERM_X;

		/* check for bad encoding, and overrule anything we did if we find one */
		if (__s2_is_x(desc))
		 	perms = ENTRY_PERM_UNKNOWN;

		break;
	}
	case ENTRY_STAGE_NONE:
		// can't parse attrs for a not-a-pagetable pte
		BUG();
	default:
		BUG();
	}

	// TODO: fill in hierarchical permissions from `next_level_aal`
	// rather than just giving up with UNKNOWN
	for (int i = 0; i < level; i++) {
		if (next_level_aal.attr_at_level[i]) {
			perms = ENTRY_PERM_UNKNOWN;
		}
	}

	// finally, read out the mem_attr
	switch (stage) {
	case ENTRY_STAGE1: {
		// hard case: pte contains AttrIndx, which indirects through MAIR_ELx
		u64 attr_idx = PTE_EXTRACT(PTE_FIELD_S1_ATTRINDX, desc);
		// mair must be read_mair(...) not no_mair() if asking for Stage 2
		ghost_assert(mair.present);
		switch(mair.attrs[attr_idx]) {
		case MEMATTR_FIELD_DEVICE_nGnRE:
			memtype_attr = ENTRY_MEMTYPE_DEVICE;
			break;
		case MEMATTR_FIELD_NORMAL_OUTER_INNER_WRITE_BACK_CACHEABLE:
			memtype_attr = ENTRY_MEMTYPE_NORMAL_CACHEABLE;
			break;
		default:
			memtype_attr = ENTRY_MEMTYPE_UNKNOWN;
			break;
		}
		break;
	}
	case ENTRY_STAGE2:
		// easy case, MemAttr encoded directly into the pte.
		switch (PTE_EXTRACT(PTE_FIELD_S2_MEMATTR, desc)) {
		case PTE_FIELD_S2_MEMATTR_DEVICE_nGnRE:
			memtype_attr = ENTRY_MEMTYPE_DEVICE;
			break;
		case PTE_FIELD_S2_MEMATTR_NORMAL_OUTER_INNER_WRITE_BACK_CACHEABLE:
			memtype_attr = ENTRY_MEMTYPE_NORMAL_CACHEABLE;
			break;
		default:
			memtype_attr = ENTRY_MEMTYPE_UNKNOWN;
			break;
		}
		break;
	default:
		// already checked
		unreachable();
	}

	return (struct entry_attributes){
		.prot = perms,
		.memtype = memtype_attr,
		.raw_arch_attrs = desc & PTE_FIELD_ATTRS_MASK,
	};
}

struct entry_exploded_descriptor deconstruct_pte(u64 partial_ia, u64 desc, u64 level, entry_stage_t stage)
{
	struct entry_exploded_descriptor deconstructed;

	deconstructed.ia_region = (struct addr_range){
		.range_start = partial_ia,
		.range_size = MAP_SIZES[level],
	};
	deconstructed.level = level;
	deconstructed.stage = stage;


	if (! is_desc_valid(desc)) {
		deconstructed.kind = PTE_KIND_INVALID;
		return deconstructed;
	} else if (is_desc_table(desc, level, stage)) {
		deconstructed.kind = PTE_KIND_TABLE;
		deconstructed.table_data.next_level_table_addr = extract_table_address(desc);
		return deconstructed;
	} else {
		ghost_mair_t mair;
		deconstructed.kind = PTE_KIND_MAP;
		deconstructed.map_data.oa_region = (struct addr_range){
			.range_start = extract_output_address(desc, level),
			.range_size = MAP_SIZES[level],
		};

		// for pKVM's own Stage 1 tables, the memory attributes are actually stored
		// in the indirection register (MAIR)
		if (stage == ENTRY_STAGE1)
			// TODO: BS: read sysregs from ghost model not h/w
			//           they should be part of s1_roots or something?
			mair = read_mair(side_effect()->read_sysreg(SYSREG_MAIR_EL2));
		else
			mair = no_mair();
		deconstructed.map_data.attrs = parse_attrs(stage, mair, desc, (u8)level, DUMMY_AAL);
		return deconstructed;
	}
}

void traverse_pgtable_from(u64 root, u64 table_start, u64 partial_ia, u64 level, entry_stage_t stage, pgtable_traverse_cb visitor_cb, enum pgtable_traversal_flag flag, void *data)
{
	struct pgtable_traverse_context ctxt;

	GHOST_LOG_CONTEXT_ENTER();
	ctxt.root = root;
	ctxt.stage = stage;
	ctxt.data = data;
	ctxt.level = level;

	ghost_assert(IS_PAGE_ALIGNED(table_start));

	for (int i = 0; i < 512; i++) {
		u64 pte_phys;
		u64 desc;
		u64 pte_ia;

		struct sm_location *loc;

		GHOST_LOG_CONTEXT_ENTER_INNER("loop");
		GHOST_LOG_INNER("loop", i, u32);

		pte_phys = table_start + i*sizeof(u64);
		GHOST_LOG_INNER("loop", pte_phys, u64);

		loc = location(pte_phys);

		// If the location is owned by another thread, then don't keep going
		if (flag == NO_READ_UNLOCKED_LOCATIONS && loc->thread_owner >= 0 && loc->thread_owner != cpu_id()) {
			GHOST_LOG_CONTEXT_EXIT_INNER("loop");
			break;
		}

		desc = read_phys(pte_phys);
		GHOST_LOG_INNER("loop", desc, u64);


		/* this pte maps a region of MAP_SIZES[level] starting from here */
		pte_ia = partial_ia + i*MAP_SIZES[level];

		ctxt.loc = loc;
		ctxt.descriptor = desc;
		ctxt.exploded_descriptor = deconstruct_pte(pte_ia, desc, level, stage);
		ctxt.leaf = ctxt.exploded_descriptor.kind != PTE_KIND_TABLE;
		visitor_cb(&ctxt);

		/* visitor can't have changed the actual descriptor ... */
		ghost_safety_check(read_phys(pte_phys) == desc);

		switch (ctxt.exploded_descriptor.kind) {
		case PTE_KIND_TABLE:
			traverse_pgtable_from(
				root,
				ctxt.exploded_descriptor.table_data.next_level_table_addr,
				pte_ia,
				level+1,
				stage,
				visitor_cb,
				flag,
				data
			);
			break;
		case PTE_KIND_MAP:
		case PTE_KIND_INVALID:
		default:
			break;
		}
		GHOST_LOG_CONTEXT_EXIT_INNER("loop");
	}
	GHOST_LOG_CONTEXT_EXIT();
}

void traverse_pgtable(u64 root, entry_stage_t stage, pgtable_traverse_cb visitor_cb, enum pgtable_traversal_flag flag, void *data)
{
	u64 start_level;
	GHOST_LOG_CONTEXT_ENTER();

	start_level = discover_start_level(stage);
	GHOST_LOG(root, u64);
	GHOST_LOG(start_level, u64);

	// assume uses 4k granule, starting from level 0, without multiple concatenated pagetables
	ghost_assert(start_level == 0);
	ghost_assert(discover_page_size(stage) == PAGE_SIZE);
	ghost_assert(discover_nr_concatenated_pgtables(stage) == 1);

	traverse_pgtable_from(root, root, 0, start_level, stage, visitor_cb, flag, data);
	GHOST_LOG_CONTEXT_EXIT();
}

void add_location_to_unclean_PTE(struct sm_location* loc)
{
	// Check that the location is not already in the set
	for (int i = 0; i < the_ghost_state->unclean_locations.len; i++) {
		if (loc == the_ghost_state->unclean_locations.locations[i]) {
			GHOST_WARN("A location was added twice to the unclean PTEs");
			ghost_assert(false);
		}
	}

	// Add it to the set
	ghost_assert(the_ghost_state->unclean_locations.len < MAX_UNCLEAN_LOCATIONS);
	the_ghost_state->unclean_locations.locations[the_ghost_state->unclean_locations.len] =
		loc;
	the_ghost_state->unclean_locations.len ++;


}

static struct pgtable_traverse_context construct_context_from_pte(struct sm_location *loc, void *data) {

	// Check that the location is consistent and well-locked
	u64 desc = read_phys(loc->phys_addr);

	struct pgtable_traverse_context ctx;
	ctx.loc = loc;
	ctx.descriptor = desc;
	ctx.exploded_descriptor = loc->descriptor;
	ctx.level = ctx.exploded_descriptor.level;
	ctx.leaf = ctx.exploded_descriptor.kind != PTE_KIND_TABLE;
	ctx.root = loc->owner;
	ctx.stage = ctx.exploded_descriptor.stage;
	ctx.data = data;

	return ctx;
}

void traverse_all_unclean_PTE(pgtable_traverse_cb visitor_cb, void* data, entry_stage_t stage)
{
	struct sm_location *loc;
	u64 *len = &the_ghost_state->unclean_locations.len;
	struct pgtable_traverse_context ctx;

	for (int i = 0; i < *len; i++) {
		loc = the_ghost_state->unclean_locations.locations[i];

		ghost_assert(loc->initialised);
		ghost_assert(loc->is_pte);
		ghost_assert(loc->state.kind == STATE_PTE_INVALID_UNCLEAN);

		if (stage != ENTRY_STAGE_NONE)
			if (stage != loc->descriptor.stage)
				break;



		// We rebuild the context from the descriptor of the location
		ctx = construct_context_from_pte(loc, data);
		visitor_cb(&ctx);
		// If the update resulted in cleaning the location, remove it from the list of
		// unclean locations
		if (loc->state.kind != STATE_PTE_INVALID_UNCLEAN) {
			// Take the last location of the list and put it in the current cell
			(*len)--;
			the_ghost_state->unclean_locations.locations[i] =
					the_ghost_state->unclean_locations.locations[*len];
			// decrement i to run on the current cell
			i--;
		}
	}
}

static void finder_cb(struct pgtable_traverse_context *ctxt)
{
	struct pgtable_walk_result *result = (struct pgtable_walk_result*)ctxt->data;
	if (ctxt->loc->phys_addr == result->requested_pte) {
		result->found = true;
		result->root = ctxt->root;
		result->descriptor = ctxt->exploded_descriptor;
		result->stage = ctxt->stage;
		result->level = ctxt->level;
	}
}

struct pgtable_walk_result find_pte(struct sm_location *loc)
{
	struct pgtable_walk_result result;
	result.found = false;
	result.requested_pte = loc->phys_addr;

	ghost_assert(loc->initialised && loc->is_pte);

	traverse_pgtable(loc->owner, loc->descriptor.stage, finder_cb, NO_READ_UNLOCKED_LOCATIONS, &result);

	return result;
}

/**
 * initial_state() - Construct an initial sm_pte_state for a clean descriptor.
 */
struct sm_pte_state initial_state(u64 partial_ia, u64 desc, u64 level, entry_stage_t stage)
{
	struct sm_pte_state state;
	struct entry_exploded_descriptor deconstructed = deconstruct_pte(partial_ia, desc, level, stage);
	switch (deconstructed.kind) {
	case PTE_KIND_INVALID:
		state.kind = STATE_PTE_INVALID;
		state.invalid_clean_state.invalidator_tid = cpu_id();
		break;
	case PTE_KIND_MAP:
	case PTE_KIND_TABLE:
		state.kind = STATE_PTE_VALID;
		for (int i = 0; i < MAX_CPU; i++) {
			state.valid_state.lvs[i] = LVS_unguarded;
		}
		break;
	default:
		unreachable();
	}

	return state;
}
