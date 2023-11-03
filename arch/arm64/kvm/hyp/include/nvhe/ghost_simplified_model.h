#ifndef GHOST_SIMPLIFIED_MODEL_H
#define GHOST_SIMPLIFIED_MODEL_H

#include <linux/types.h>
#include <asm/kvm_pgtable.h>

#include <nvhe/ghost_asserts.h>


#define MAX_CPU 4 // TODO: JP

#define OFFSET_IN_PAGE(x) (((x) & GENMASK(PAGE_SHIFT - 1, 0)))
#define IS_PAGE_ALIGNED(x) (OFFSET_IN_PAGE(x) == 0)

#define ID_STRING(x) [x]=#x

typedef int thread_identifier;

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
	enum LVS lvs[MAX_CPU];
};

/**
 * enum LIS - Local (this CPU) Invalid State of a single invalid PTE.
 * @LIS_unguarded: an invalid value has been written by this core, but not DSB'd.
 * @LIS_dsbed: an invalid value has been written by this core, and now DSB'd, but not TLBI'd.
 * @LIS_dsb_csed: an invalid value has been written by this core,
 *                a subsequent DSB has been performed,
 *                and also a TLBI on that location has been performed.
 */
enum LIS {
	LIS_unguarded,
	LIS_dsbed,
	LIS_dsb_tlbi_all
};

/**
 * struct aut_invalid - Automata state for an invalid PTE
 * @invalidator_tid: thread id of the thread which wrote invalid.
 * @old_valid_desc: the descriptor which got overwritten.
 * @lis: per-CPU local-invalid-state.
 */
struct aut_invalid {
	thread_identifier invalidator_tid;
	int old_valid_desc;
	enum LIS lis[MAX_CPU];
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
 * struct sm_location - State for a doubleword of memory.
 * @initialised: whether this mem block has been initialised.
 * @val: if initialised, current value.
 * @is_pte: if initialised, whether this location is currently being tracked and treated as a PTE.
 * @state: if initialised and is_pte, the current automata state for this location.
 * @owner_root: if initialised, the root of the logical tree that owns this location.
 */
struct sm_location {
	bool initialised;
	u64 addr;
	u64 val;
	bool is_pte;
	struct sm_pte_state state;
	u64 owner_root;
};

/*
 * Memory
 *
 * To not duplicate the entire machines memory,
 * we instead only track "blobs" (arbitrary aligned chunks)
 * of memory that the simplified model checking machinery is actually aware of.
 *
 * Each blob is a single 2MiB region.
 */

#define SLOTS_PER_PAGE (512)
#define PAGES_PER_BLOB (512)
#define BLOB_SHIFT (12+9)
#define SLOT_SHIFT 3
#define MAX_BLOBS (0x20)
#define MAX_ROOTS 10

#define ALIGN_DOWN_TO_BLOB(x) (((x) >> BLOB_SHIFT) << BLOB_SHIFT)
#define OFFSET_IN_BLOB(x) (((x) & GENMASK(BLOB_SHIFT, 0)))

/**
 * struct ghost_memory_blob - An arbitrary (aligned) blob of memory.
 */
struct ghost_memory_blob {
	bool valid;
	u64 phys;
	struct sm_location slots[PAGES_PER_BLOB*SLOTS_PER_PAGE];
};

/**
 * struct ghost_simplified_model_state - Top-level simplified model state.
 * @base_addr: the physical address of the start of the (simplified) memory.
 * @size: the number of bytes in the simplified memory to track.
 * @memory: ghost memory.
 * @nr_s1_roots: number of EL2 stage1 pagetable roots being tracked.
 * @s1_roots: set of known EL2 stage1 pagetable roots.
 * @nr_s2_roots: number of EL2 stage2 pagetable roots being tracked.
 * @s2_roots: set of known EL2 stage2 pagetable roots.
 */
struct ghost_simplified_model_state {
	u64 base_addr;
	u64 size;
	struct ghost_memory_blob memory[MAX_BLOBS];

	u64 nr_s2_roots;
	u64 s2_roots[MAX_ROOTS];

	u64 nr_s1_roots;
	u64 s1_roots[MAX_ROOTS];
};


/**
 * phys_location() - Retrieve the simplified-model memory for a given physical address
 */
struct sm_location *phys_location(u64 phys);

enum memory_order_t {
	WMO_plain,
	WMO_release
};

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
};

enum ghost_sysreg_kind {
	SYSREG_VTTBR,
	SYSREG_TTBR_EL2,
};
static const char *sysreg_names[] = {
	ID_STRING(SYSREG_VTTBR),
	ID_STRING(SYSREG_TTBR_EL2),
};

struct ghost_simplified_model_transition {
	enum ghost_simplified_model_transition_kind kind;
	union {
		struct trans_write_data {
			enum memory_order_t mo;
			u64 *hyp_va;
			u64 val;
		} write_data;

		struct trans_read_data {
			u64 *hyp_va;
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
	};
};
void GHOST_transprinter(void *p);


/**
 * initialise_ghost_ptes_memory() - One-shot initialisation of simplified model state.
 */
void initialise_ghost_ptes_memory(phys_addr_t phys, u64 size);

/**
 * ghost_simplified_model_step() - Take a step in the simplified model.
 */
void ghost_simplified_model_step(struct ghost_simplified_model_transition trans);

//////////////
// Step helpers

static inline void ghost_simplified_model_step_write(enum memory_order_t mo, kvm_pte_t *pte, u64 val)
{
	ghost_simplified_model_step((struct ghost_simplified_model_transition){
		.kind = TRANS_MEM_WRITE,
		.write_data = (struct trans_write_data){
			.mo = mo,
			.hyp_va = (u64 *)pte,
			.val = val,
		},
	});
}

static inline void ghost_simplified_model_step_read(u64 *addr, u64 val)
{
	ghost_simplified_model_step((struct ghost_simplified_model_transition){
		.kind = TRANS_MEM_READ,
		.read_data = (struct trans_read_data){
			.hyp_va = addr,
			.val = val,
		},
	});
}

static inline void ghost_simplified_model_step_dsb(enum dsb_kind kind)
{
	ghost_simplified_model_step((struct ghost_simplified_model_transition){
		.kind = TRANS_DSB,
		.dsb_data = kind,
	});
}

static inline void ghost_simplified_model_step_isb(void)
{
	ghost_simplified_model_step((struct ghost_simplified_model_transition){
		.kind = TRANS_ISB,
	});
}

static inline void ghost_simplified_model_step_tlbi3(enum tlbi_kind kind, u64 page, int level)
{
	ghost_simplified_model_step((struct ghost_simplified_model_transition){
		.kind = TRANS_TLBI,
		.tlbi_data = (struct trans_tlbi_data){
			.tlbi_kind = kind,
			.page = page,
			.level = level,
		},
	});
}

static inline void ghost_simplified_model_step_tlbi1(enum tlbi_kind kind)
{
	ghost_simplified_model_step((struct ghost_simplified_model_transition){
		.kind = TRANS_TLBI,
		.tlbi_data = (struct trans_tlbi_data){
			.tlbi_kind = kind,
		},
	});
}

static inline void ghost_simplified_model_step_msr(enum ghost_sysreg_kind sysreg, u64 val)
{
	ghost_simplified_model_step((struct ghost_simplified_model_transition){
		.kind = TRANS_MSR,
		.msr_data = (struct trans_msr_data){
			.sysreg = sysreg,
			.val = val,
		},
	});
}

#endif /* GHOST_SIMPLIFIED_MODEL_H */