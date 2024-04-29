#ifndef GHOST_SIMPLIFIED_MODEL_H
#define GHOST_SIMPLIFIED_MODEL_H

#include <linux/types.h>
#include <asm/kvm_pgtable.h>

#include <nvhe/spinlock.h>

#include <nvhe/ghost/ghost_maplets.h>
#include <nvhe/ghost/ghost_asserts.h>
#include <nvhe/ghost/ghost_control.h>
#include <hyp/ghost/ghost_extra_debug-pl011.h>


#define MAX_CPU 4 // TODO: JP

#define OFFSET_IN_PAGE(x) (((x) & GENMASK(PAGE_SHIFT - 1, 0)))
#define IS_PAGE_ALIGNED(x) (OFFSET_IN_PAGE(x) == 0)

#define ID_STRING(x) [x]=#x

typedef int thread_identifier;

/**
 * typedef sm_owner_t - ID for ownership
 *
 * This is the physical address of the pagetable root.
 */
typedef u64 sm_owner_t;

thread_identifier cpu_id(void);

/**
 * enum LVS - Local (this CPU) Valid State of a single non-invalid PTE.
 * @LVS_unguarded: a valid value has been written by this core, but not DSB'd.
 * @LVS_dsbed: a valid value has been written by this core, and now DSB'd.
 * @LVS_dsb_csed: a valid value has been written by this core,
 *                a subsequent DSB has been performed,
 *                and also a context-synchronisation event on this core.
 */
enum LVS {
	LVS_unguarded,
	LVS_dsbed,
	LVS_dsb_csed
};

/**
 * struct aut_valid - Automata state for a valid PTE.
 * @lvs: per-CPU local-valid-state.
 */
struct aut_valid {
	// TODO:JP: this feel fishy, especially given the comments for LVS
	// I think we should we remember the writer, and treat it specially
	enum LVS lvs[MAX_CPU];
};

/**
 * enum LIS - Local (this CPU) Invalid State of a single invalid PTE.
 * @LIS_unguarded: an invalid value has been written by this core, but not DSB'd.
 * @LIS_dsbed: an invalid value has been written by this core, and now DSB'd, but not TLBI'd.
 * @LIS_dsb_tlbi_ipa: the invalid write has been written by this core, DSB'd, and only a TLBI that hit the IPA mappings for this loc.
 * @LIS_dsb_tlbi_ipa_dsb: the invalid write has been written by this core, DSB'd, and only a TLBI that hit the IPA mappings for this loc, and now a DSB has been performed.
 * @LIS_dsb_tlbied: the invalid write has been written by this core, DSB'd, and now fully TLBI'd.
 */
enum LIS {
	LIS_unguarded,
	LIS_dsbed,
	LIS_dsb_tlbi_ipa,
	LIS_dsb_tlbi_ipa_dsb,
	LIS_dsb_tlbied,
};

/**
 * struct aut_invalid - Automata state for an invalid PTE
 * @invalidator_tid: thread id of the thread which wrote invalid.
 * @old_valid_desc: the descriptor which got overwritten.
 * @lis: sub-invalid-state, for thread with tid invalidator_tid.
 */
struct aut_invalid {
	thread_identifier invalidator_tid;
	u64 old_valid_desc;
	enum LIS lis;
};

/**
 * struct aut_invalid_clean - Automata state for an invalid+sufficiently globally TLBI'd PTE.
 * @invalidator_tid: thread id of the thread which wrote invalid.
 */
struct aut_invalid_clean {
	thread_identifier invalidator_tid;
};

enum automaton_state_kind {
	STATE_PTE_VALID,
	STATE_PTE_INVALID_UNCLEAN,
	STATE_PTE_INVALID,
};
static const char *automaton_state_names[] = {
	ID_STRING(STATE_PTE_VALID),
	ID_STRING(STATE_PTE_INVALID_UNCLEAN),
	ID_STRING(STATE_PTE_INVALID)
};

/**
 * struct pte_state - Automata state of a single PTE location.
 */
struct sm_pte_state {
	enum automaton_state_kind kind;
	union {
		struct aut_valid valid_state;
		struct aut_invalid invalid_unclean_state;
		struct aut_invalid_clean invalid_clean_state;
	};
};

/**
 * struct ghost_addr_range - A range start+size
 */
struct ghost_addr_range {
	u64 range_start;
	u64 range_size;
};

enum pte_kind {
	PTE_KIND_TABLE,
	PTE_KIND_MAP,  /* BLOCK,PAGE */
	PTE_KIND_INVALID,
};
static const char *pte_kind_names[] = {
	ID_STRING(PTE_KIND_TABLE),
	ID_STRING(PTE_KIND_MAP),
	ID_STRING(PTE_KIND_INVALID),
};

/**
 * struct  ghost_exploded_descriptor - Information about a PTE.
 * @kind: Whether the descriptor is invalid/a table/a block or page mapping.
 * @region: the input-address region this PTE covers.
 * @level: the level within the pgtable this entry is at.
 * @s2: whether this descriptor is for a Stage2 table.
 * @table_data: if kind is PTE_KIND_TABLE, the table descriptor data (next level table address).
 * @map_data: if kind is PTE_KIND_MAP, the mapping data (output address range, and other attributes).
 *
 * TODO: replace with maplet_target...
 */
struct ghost_exploded_descriptor {
	enum pte_kind kind;
	struct ghost_addr_range ia_region;
	u64 level;
	ghost_stage_t stage;
	union {
		struct {
			u64 next_level_table_addr;
		} table_data;

		struct {
			struct ghost_addr_range oa_region;
			struct maplet_attributes attrs;
		} map_data;
	};
};

/**
 * struct sm_location - A (64-bit) Location in the simplified model memory.
 * @initialised: whether this mem block has been initialised.
 * @phys_addr: the physical address of this location.
 * @val: if initialised, value stored by model for this location.
 * @is_pte: if initialised, whether this location is tracked as a PTE.
 * @descriptor: if initialised and is_pte, the value as an exploded descriptor.
 * @state: if initialised and is_pte, the automata state for this location.
 * @owner: if initialised, the root of the tree that owns this location.
 *
 * The owner and descriptor are here as helpful cached values,
 * and could be computed by doing translation table walks.
 */
struct sm_location {
	bool initialised;
	u64 phys_addr;
	u64 val;
	bool is_pte;
	struct ghost_exploded_descriptor descriptor;
	struct sm_pte_state state;
	sm_owner_t owner;
};

/*
 * Memory
 *
 * To not duplicate the entire machines memory,
 * we instead only track "blobs" (arbitrary aligned chunks)
 * of memory that the simplified model checking machinery is actually aware of.
 */

#define SLOTS_PER_PAGE (512)

#define SLOT_SHIFT 3

#define BLOB_SHIFT 12
#define MAX_BLOBS (0x2000)
#define MAX_ROOTS 10

#define BLOB_SIZE ((1UL) << BLOB_SHIFT)
#define BLOB_OFFSET_MASK GENMASK(BLOB_SHIFT - 1, 0)
#define ALIGN_DOWN_TO_BLOB(x) ((x) & ~BLOB_OFFSET_MASK)
#define OFFSET_IN_BLOB(x) ((x) & BLOB_OFFSET_MASK)
#define SLOT_OFFSET_IN_BLOB(x) (OFFSET_IN_BLOB(x) >> SLOT_SHIFT)

/**
 * struct ghost_memory_blob - A page of memory.
 * @valid: whether this blob is being used.
 * @phys: if valid, the physical address of the start of this region.
 * @slots: if valid, the array of memory locations within this region.
 *
 * Each blob is a aligned and contiguous page of memory.
 */
struct ghost_memory_blob {
	bool valid;
	u64 phys;
	struct sm_location slots[SLOTS_PER_PAGE];
};

/**
 * struct ghost_simplified_memory - simplified model memory.
 * @blobs_backing: the set of memory blobs.
 * @nr_allocated_blobs: the number of blobs created so far.
 * @ordered_blob_list: a list of indices of allocated blobs, in order of their physical addresses.
 */
struct ghost_simplified_memory {
	struct ghost_memory_blob blobs_backing[MAX_BLOBS];

	u64 nr_allocated_blobs;
	u64 ordered_blob_list[MAX_BLOBS];
};

/**
 * find_blob() - Given a phys, find the blob containing it.
 *
 * Returns NULL if no blob is found.
 */
struct ghost_memory_blob *find_blob(struct ghost_simplified_memory *mem, u64 phys);

/**
 * blob_of() - Given an index in the ordered_blob_list, return the corresponding blob
 */
struct ghost_memory_blob *blob_of(struct ghost_simplified_memory *mem, u64 i);

/**
 * blob_unclean() - Is any slot in the blob in an unclean state.
 */
bool blob_unclean(struct ghost_memory_blob *blob);

/**
 * location() - Retrieve the simplified-model memory for a given physical address
 */
struct sm_location *location(u64 phys);

#define GHOST_SIMPLIFIED_MODEL_MAX_LOCKS 16

/**
 * struct owner_locks - Map of owner root to lock.
 */
struct owner_locks {
	u64 len;
	sm_owner_t owner_ids[GHOST_SIMPLIFIED_MODEL_MAX_LOCKS];
	hyp_spinlock_t *locks[GHOST_SIMPLIFIED_MODEL_MAX_LOCKS];
};

/**
 * owner_lock() - Get hyp spinlock for an owner.
 *
 * Returns NULL if no lock for that owner_id.
 */
hyp_spinlock_t *owner_lock(sm_owner_t owner_id);

/**
 * struct ghost_simplified_model_state - Top-level simplified model state.
 * @base_addr: the physical address of the start of the (simplified) memory.
 * @size: the number of bytes in the simplified memory to track.
 * @memory: the actual simplified model memory.
 * @nr_s1_roots: number of EL2 stage1 pagetable roots being tracked.
 * @s1_roots: set of known EL2 stage1 pagetable roots.
 * @nr_s2_roots: number of EL2 stage2 pagetable roots being tracked.
 * @s2_roots: set of known EL2 stage2 pagetable roots.
 */
struct ghost_simplified_model_state {
	u64 base_addr;
	u64 size;
	struct ghost_simplified_memory memory;

	u64 nr_s2_roots;
	u64 s2_roots[MAX_ROOTS];

	u64 nr_s1_roots;
	u64 s1_roots[MAX_ROOTS];

	struct owner_locks locks;
};


/// Equality and printing
bool sm_aut_invalid_eq(struct aut_invalid *i1, struct aut_invalid *i2);
bool sm_pte_state_eq(struct sm_pte_state *s1, struct sm_pte_state *s2);
bool sm_loc_eq(struct sm_location *loc1, struct sm_location *loc2);
void dump_sm_state(struct ghost_simplified_model_state *st);

/**
 * struct ghost_simplified_model_options - Global configuration of simplified model behaviour
 *
 * Provides selective enabling/disabling of supported behaviours.
 */
struct ghost_simplified_model_options {
	/**
	 * @promote_DSB_nsh - Silently promote all DSB NSH to DSB ISH
	 */
	bool promote_DSB_nsh;

	/**
	 * @promote_TLBI_nsh - Silently promote all TLBI to broadcast ones
	 */
	bool promote_TLBI_nsh;

	/**
	 * @promote_TLBI_by_id - Silently promote all TLBI-by-ASID and by-VMID to ALL
	 */
	bool promote_TLBI_by_id;
};


enum memory_order_t {
	WMO_plain,
	WMO_release,

	/** @GHOST_MEMSET_PAGE - A helpful wrapper around a full page-sized memset() */
	GHOST_MEMSET_PAGE
};

/// Decoded TLBIs

enum sm_tlbi_op_stage {
	TLBI_OP_STAGE1 = 1,
	TLBI_OP_STAGE2 = 2,
	TLBI_OP_BOTH_STAGES = TLBI_OP_STAGE1 | TLBI_OP_STAGE2,
};
static const char *sm_tlbi_op_stage_names[] = {
	ID_STRING(TLBI_OP_STAGE1),
	ID_STRING(TLBI_OP_STAGE2),
	ID_STRING(TLBI_OP_BOTH_STAGES),
};

enum sm_tlbi_op_method_kind {
	TLBI_OP_BY_ALL        = 0, /* TLBI ALL* only */
	TLBI_OP_BY_INPUT_ADDR = 1, /* by Input-Address */
	TLBI_OP_BY_ADDR_SPACE = 2, /* by ASID/VMID */

	TLBI_OP_BY_VA = TLBI_OP_BY_INPUT_ADDR,
	TLBI_OP_BY_IPA = TLBI_OP_BY_INPUT_ADDR,

	TLBI_OP_BY_VMID = TLBI_OP_BY_ADDR_SPACE,
	TLBI_OP_BY_ASID = TLBI_OP_BY_ADDR_SPACE,
};
static const char *sm_tlbi_op_method_kind_names[] = {
	ID_STRING(TLBI_OP_BY_ALL),
	ID_STRING(TLBI_OP_BY_INPUT_ADDR),
	ID_STRING(TLBI_OP_BY_ADDR_SPACE),
};

enum sm_tlbi_op_regime_kind {
	TLBI_REGIME_EL10 = 1, /* EL1&0 regime */
	TLBI_REGIME_EL2  = 2, /* EL2 regime */
};
static const char *sm_tlbi_op_regime_kind_names[] = {
	ID_STRING(TLBI_REGIME_EL10),
	ID_STRING(TLBI_REGIME_EL2),
};

/**
 * struct sm_tlbi_op_method - Decoded TLBI by-method
 * @kind: whether this is "all", by address, or by address-space-identifier.
 */
struct sm_tlbi_op_method {
	enum sm_tlbi_op_method_kind kind;
	union {
		struct tlbi_op_method_by_address_data {
			u64 page;

			bool has_level_hint;
			u8 level_hint;

			bool affects_last_level_only;
		} by_address_data;

		struct tlbi_op_method_by_address_space_id_data {
			u64 asid_or_vmid;
		} by_id_data;
	};
};

/**
 * struct sm_tlbi_op - A decoded TLB maintenance operation.
 * @stage: whether this affects cached stage1 translations, cached stage2 translations, or both.
 * @regime: the translation regime that this TLB maintenance operation would affect the cached entries of.
 * @method: whether this TLBI is by IPA, by VA, or by VMID, etc., and the relevant address/vmid, etc.
 * @shootdown: whether this TLB maintenance operation is broadcast to other cores.
 */
struct sm_tlbi_op {
	enum sm_tlbi_op_stage stage;
	enum sm_tlbi_op_regime_kind regime;
	struct sm_tlbi_op_method method;
	bool shootdown;
};

/// Encoded TLBIs

enum tlbi_kind {
	TLBI_vmalls12e1,
	TLBI_vmalls12e1is,
	TLBI_vmalle1is,
	TLBI_alle1is,
	TLBI_vmalle1,
	TLBI_vale2is,
	TLBI_vae2is,
	TLBI_ipas2e1is
};
static const char *tlbi_kind_names[] = {
	ID_STRING(TLBI_vmalls12e1),
	ID_STRING(TLBI_vmalls12e1is),
	ID_STRING(TLBI_vmalle1is),
	ID_STRING(TLBI_alle1is),
	ID_STRING(TLBI_vmalle1),
	ID_STRING(TLBI_vale2is),
	ID_STRING(TLBI_vae2is),
	ID_STRING(TLBI_ipas2e1is)
};

enum dsb_kind {
	DSB_ish,
	DSB_ishst,
	DSB_nsh
};
static const char *dsb_kind_names[] = {
	ID_STRING(DSB_ish),
	ID_STRING(DSB_ishst),
	ID_STRING(DSB_nsh)
};


enum ghost_simplified_model_transition_kind {
	TRANS_MEM_WRITE,
	TRANS_MEM_READ,
	TRANS_DSB,
	TRANS_ISB,
	TRANS_TLBI,
	TRANS_MSR,

	/**
	 * @TRANS_HINT - A non-hardware-model transition
	 * These generally provide additional information to the simplified model,
	 * such as ownership,
	 * to resolve otherwise unbounded non-determinism
	 */
	TRANS_HINT,
};

enum ghost_sysreg_kind {
	SYSREG_VTTBR,
	SYSREG_TTBR_EL2,
};
static const char *sysreg_names[] = {
	ID_STRING(SYSREG_VTTBR),
	ID_STRING(SYSREG_TTBR_EL2),
};

enum ghost_hint_kind {
	/**
	 * @GHOST_HINT_SET_ROOT_LOCK - Set the hyp_spinlock_t* owning a pgtable root.
	 */
	GHOST_HINT_SET_ROOT_LOCK,

	/**
	 * @GHOST_HINT_SET_OWNER_ROOT - Set the pgtable root which owns a pte
	 */
	GHOST_HINT_SET_OWNER_ROOT,

	/**
	 * @GHOST_HINT_RELEASE_TABLE - Stop tracking a whole table (and subtables recursively)
	 */
	GHOST_HINT_RELEASE_TABLE,
};
static const char *hint_names[] = {
	ID_STRING(GHOST_HINT_SET_ROOT_LOCK),
	ID_STRING(GHOST_HINT_SET_OWNER_ROOT),
	ID_STRING(GHOST_HINT_RELEASE_TABLE),
};

/**
 * Source location info
 */
struct src_loc {
	const char *file;
	const char *func;
	int lineno;
};

struct ghost_simplified_model_transition {
	/**
	 * @src_loc: string location (path, function name, lineno etc)
	 *           of where the transition happens in the source code.
	 *           For debugging/pretty printing.
	 */
	struct src_loc src_loc;

	enum ghost_simplified_model_transition_kind kind;
	union {
		struct trans_write_data {
			enum memory_order_t mo;
			u64 phys_addr;
			u64 val;
		} write_data;

		struct trans_read_data {
			u64 phys_addr;
			u64 val;
		} read_data;

		enum dsb_kind dsb_data;

		struct trans_tlbi_data {
			enum tlbi_kind tlbi_kind;
			u64 page;
			u64 level;
		} tlbi_data;

		struct trans_msr_data {
			enum ghost_sysreg_kind sysreg;
			u64 val;
		} msr_data;

		struct trans_hint_data {
			enum ghost_hint_kind hint_kind;
			u64 location;
			u64 value;
		} hint_data;
	};
};
void GHOST_transprinter(void *p);

static inline bool sm_print_condensed(void)
{
	return ghost_control_print_enabled("sm_condensed");
}

/**
 * initialise_ghost_simplified_model() - One-shot initialisation of simplified model state.
 * @phys: the start physical address of the memory given to pKVM.
 * @size: the size of the region of physical address space given to pKVM.
 * @sm_virt: the start of the virtual address of the memory the ghost simplified model state can live in
 * @sm_size: the space given for the ghost simplified model memory.
 *
 * `phys` and `size` should be those passed to __pkvm_init
 */
void initialise_ghost_simplified_model(phys_addr_t phys, u64 size, unsigned long sm_virt, u64 sm_size);

/**
 * ghost_simplified_model_step() - Take a step in the simplified model.
 */
void ghost_simplified_model_step(struct ghost_simplified_model_transition trans);

//////////////
// Step helpers

#define SRC_LOC (struct src_loc){.file=__FILE__, .lineno=__LINE__, .func=__func__}

#define ghost_simplified_model_step_write(...) __ghost_simplified_model_step_write(SRC_LOC, __VA_ARGS__)
static inline void __ghost_simplified_model_step_write(struct src_loc src_loc, enum memory_order_t mo, phys_addr_t phys, u64 val)
{
	ghost_simplified_model_step((struct ghost_simplified_model_transition){
		.src_loc = src_loc,
		.kind = TRANS_MEM_WRITE,
		.write_data = (struct trans_write_data){
			.mo = mo,
			.phys_addr = phys,
			.val = val,
		},
	});
}

#define ghost_simplified_model_step_read(...) __ghost_simplified_model_step_read(SRC_LOC, __VA_ARGS__)
static inline void __ghost_simplified_model_step_read(struct src_loc src_loc, phys_addr_t phys, u64 val)
{
	ghost_simplified_model_step((struct ghost_simplified_model_transition){
		.src_loc = src_loc,
		.kind = TRANS_MEM_READ,
		.read_data = (struct trans_read_data){
			.phys_addr = phys,
			.val = val,
		},
	});
}

#define ghost_simplified_model_step_dsb(...) __ghost_simplified_model_step_dsb(SRC_LOC, __VA_ARGS__)
static inline void __ghost_simplified_model_step_dsb(struct src_loc src_loc, enum dsb_kind kind)
{
	ghost_simplified_model_step((struct ghost_simplified_model_transition){
		.src_loc = src_loc,
		.kind = TRANS_DSB,
		.dsb_data = kind,
	});
}

#define ghost_simplified_model_step_isb() __ghost_simplified_model_step_isb(SRC_LOC)
static inline void __ghost_simplified_model_step_isb(struct src_loc src_loc)
{
	ghost_simplified_model_step((struct ghost_simplified_model_transition){
		.src_loc = src_loc,
		.kind = TRANS_ISB,
	});
}

#define ghost_simplified_model_step_tlbi3(...) __ghost_simplified_model_step_tlbi3(SRC_LOC, __VA_ARGS__)
static inline void __ghost_simplified_model_step_tlbi3(struct src_loc src_loc, enum tlbi_kind kind, u64 page, int level)
{
	ghost_simplified_model_step((struct ghost_simplified_model_transition){
		.src_loc = src_loc,
		.kind = TRANS_TLBI,
		.tlbi_data = (struct trans_tlbi_data){
			.tlbi_kind = kind,
			.page = page,
			.level = level,
		},
	});
}

#define ghost_simplified_model_step_tlbi1(...) __ghost_simplified_model_step_tlbi1(SRC_LOC, __VA_ARGS__)
static inline void __ghost_simplified_model_step_tlbi1(struct src_loc src_loc, enum tlbi_kind kind)
{
	ghost_simplified_model_step((struct ghost_simplified_model_transition){
		.src_loc = src_loc,
		.kind = TRANS_TLBI,
		.tlbi_data = (struct trans_tlbi_data){
			.tlbi_kind = kind,
		},
	});
}

#define ghost_simplified_model_step_msr(...) __ghost_simplified_model_step_msr(SRC_LOC, __VA_ARGS__)
static inline void __ghost_simplified_model_step_msr(struct src_loc src_loc, enum ghost_sysreg_kind sysreg, u64 val)
{
	ghost_simplified_model_step((struct ghost_simplified_model_transition){
		.src_loc = src_loc,
		.kind = TRANS_MSR,
		.msr_data = (struct trans_msr_data){
			.sysreg = sysreg,
			.val = val,
		},
	});
}

#define ghost_simplified_model_step_hint(...) __ghost_simplified_model_step_hint(SRC_LOC, __VA_ARGS__)
static inline void __ghost_simplified_model_step_hint(struct src_loc src_loc, enum ghost_hint_kind kind, u64 location, u64 value)
{
	ghost_simplified_model_step((struct ghost_simplified_model_transition){
		.src_loc = src_loc,
		.kind = TRANS_HINT,
		.hint_data = (struct trans_hint_data){
			.hint_kind = kind,
			.location = location,
			.value = value,
		},
	});
}

#define ghost_simplified_model_step_zalloc(...) __ghost_simplified_model_step_zalloc(SRC_LOC, __VA_ARGS__)
static inline void __ghost_simplified_model_step_zalloc(struct src_loc src_loc, u64 location)
{
	ghost_printf(GHOST_WHITE_ON_CYAN "CPU: %d; ZALLOC %lx size: 1 at %s:%d in %s" GHOST_NORMAL "\n", cpu_id(), location, src_loc.file, src_loc.lineno, src_loc. func);
}

#define ghost_simplified_model_step_zalloc_exact(...) __ghost_simplified_model_step_zalloc_exact(SRC_LOC, __VA_ARGS__)
static inline void __ghost_simplified_model_step_zalloc_exact(struct src_loc src_loc, u64 location, u64 size)
{
	ghost_printf(GHOST_WHITE_ON_CYAN "CPU: %d; ZALLOC %lx size: %d at %s:%d in %s" GHOST_NORMAL "\n", cpu_id(), location, size, src_loc.file, src_loc.lineno, src_loc. func);
}

#endif /* GHOST_SIMPLIFIED_MODEL_H */