#ifndef CASEMATE_STATE_H
#define CASEMATE_STATE_H

#include <casemate-impl/types.h>
#include <casemate-impl/sync.h>

/*
 * Model types
 *
 * We try to create opaque typedefs where possible, when we do not care
 * about the implementation details (e.g. various integer types and sync primitives)
 */

#ifndef MAX_CPU
#define MAX_CPU 4
#endif

/**
 * typedef gsm_lock_addr_t - ghost model lock
 */
typedef u64 gsm_lock_addr_t;

/**
 * typedef thread_identifier - ID for hardware thread/CPU.
 */
typedef int thread_identifier;

/**
 * typedef sm_owner_t - ID for ownership
 *
 * This is the physical address of the pagetable root.
 */
typedef u64 sm_owner_t;

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
 *
 * TODO: JP: should we remember writer thread?
 */
struct aut_valid {
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

/**
 * enum automaton_state_kind - Global top-level per-PTE tracker state.
 * @STATE_PTE_VALID: a valid and cleaned location, i.e. all threads agree the pgtable has been updated.
 * @STATE_PTE_INVALID_UNCLEAN: a thread has written an invalid descriptor to this location,
 *                             but any required break-before-make has not been completed yet.
 * @STATE_PTE_INVALID: all break-before-make requirements are complete and all cores agree the location is clean.
 * @STATE_PTE_NOT_WRITABLE: the location is frozen, and no thread is permitted to write to it.
 */
enum automaton_state_kind {
	STATE_PTE_VALID,
	STATE_PTE_INVALID_UNCLEAN,
	STATE_PTE_INVALID,
	STATE_PTE_NOT_WRITABLE,
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
 * enum pte_kind - Pagetable descriptor kind.
 * @PTE_KIND_TABLE: A table entry with a pointer to another pagetable.
 * @PTE_KIND_MAP: Either a block or page entry, with a pointer to an output page.
 * @PTE_KIND_INVALID: An invalid descriptor.
 */
enum pte_kind {
	PTE_KIND_TABLE,
	PTE_KIND_MAP, /* BLOCK,PAGE */
	PTE_KIND_INVALID,
};

/**
 * struct addr_range - A range start+size
 */
struct addr_range {
	u64 range_start;
	u64 range_size;
};

/**
 * enum entry_stage - (optional) stage of translation
 */
typedef enum {
	ENTRY_STAGE2 = 2,
	ENTRY_STAGE1 = 1,

	/**
	 * @ENTRY_STAGE_NONE: for memblocks and other non-pgtable mappings.
	 */
	ENTRY_STAGE_NONE = 0,
} entry_stage_t;

/**
 * enum entry_permissions - Abstract permissions for a range of OA, as bitflags
 */
enum entry_permissions {
	ENTRY_PERM_R = 1,
	ENTRY_PERM_W = 2,
	ENTRY_PERM_X = 4,

	/*
	 * ENTRY_PERM_UNKNOWN for encodings that do not correspond to any of the above.
	 */
	ENTRY_PERM_UNKNOWN = 8,
};
#define ENTRY_PERM_RW (ENTRY_PERM_R | ENTRY_PERM_W)
#define ENTRY_PERM_RWX (ENTRY_PERM_R | ENTRY_PERM_W | ENTRY_PERM_X)

/**
 * enum entry_memtype_attr - Abstract memory type.
 */
enum entry_memtype_attr {
	ENTRY_MEMTYPE_DEVICE,
	ENTRY_MEMTYPE_NORMAL_CACHEABLE,

	/* ENTRY_MEMTYPE_UNKNOWN for encodings that do not correspond to any of the above */
	ENTRY_MEMTYPE_UNKNOWN,
};

struct entry_attributes {
	enum entry_permissions prot;
	enum entry_memtype_attr memtype;

	/**
	 * @af - access flag bit set
	 */
	bool af;

	/**
	 * @raw_arch_attrs: the raw descriptor, masked to the attribute bits
	 * Not semantically meaningful, but used in printing and diffs.
	 */
	u64 raw_arch_attrs;
};

/**
 * struct  entry_exploded_descriptor - Cached information about a PTE.
 * @kind: Whether the descriptor is invalid/a table/a block or page mapping.
 * @region: the input-address region this PTE covers.
 * @level: the level within the pgtable this entry is at.
 * @s2: whether this descriptor is for a Stage2 table.
 * @table_data: if kind is PTE_KIND_TABLE, the table descriptor data (next level table address).
 * @map_data: if kind is PTE_KIND_MAP, the mapping data (output address range, and other attributes).
 *
 * TODO: replace with entry_target...
 */
struct entry_exploded_descriptor {
	enum pte_kind kind;
	struct addr_range ia_region;
	u64 level;
	entry_stage_t stage;
	union {
		struct {
			u64 next_level_table_addr;
		} table_data;

		struct {
			struct addr_range oa_region;
			struct entry_attributes attrs;
		} map_data;
	};
};

/**
 * struct sm_location - A (64-bit) Location in the ghost model memory.
 * @initialised: whether this mem block has been initialised.
 * @phys_addr: the physical address of this location.
 * @val: if initialised, value stored by model for this location.
 * @is_pte: if initialised, whether this location is tracked as a PTE.
 * @descriptor: if initialised and is_pte, the value as a pre-computed descriptor kind.
 *              If the state is invalid unclean, then it is the last valid descriptor.
 * @state: if initialised and is_pte, the automata state for this location.
 * @owner: if initialised, the root of the tree that owns this location.
 * @thread_owner: if positive, the ID of the thread that can freely access this location
 *
 * The owner and descriptor are here as helpful cached values,
 * and could be computed by doing translation table walks.
 */
struct sm_location {
	bool initialised;
	u64 phys_addr;
	u64 val;
	bool is_pte;
	struct entry_exploded_descriptor descriptor;
	struct sm_pte_state state;
	sm_owner_t owner;
	int thread_owner;
};

/*
 * Memory
 *
 * To not duplicate the entire machines memory,
 * we instead only track "blobs" (arbitrary aligned chunks)
 * of memory that the ghost model checking machinery is actually aware of.
 *
 * These blobs are not really part of the public interface, but in C one cannot split
 * the private and public parts of the state so easily.
 */

#define SLOTS_PER_PAGE (512)

#define SLOT_SHIFT 3

#define BLOB_SHIFT 12

#ifndef MAX_BLOBS
#define MAX_BLOBS 0x2000
#endif

#ifndef MAX_ROOTS
#define MAX_ROOTS 64
#endif

#ifndef MAX_UNCLEAN_LOCATIONS
#define MAX_UNCLEAN_LOCATIONS 10
#endif

/**
 * struct casemate_memory_blob - A page of memory.
 * @valid: whether this blob is being used.
 * @phys: if valid, the physical address of the start of this region.
 * @slots: if valid, the array of memory locations within this region.
 *
 * Each blob is a aligned and contiguous page of memory.
 */
struct casemate_memory_blob {
	bool valid;
	u64 phys;
	struct sm_location slots[SLOTS_PER_PAGE];
};

/**
 * struct casemate_model_memory - ghost model memory.
 * @blobs_backing: the set of memory blobs.
 * @nr_allocated_blobs: the number of blobs created so far.
 * @ordered_blob_list: a list of indices of allocated blobs, in order of their physical addresses.
 */
struct casemate_model_memory {
	struct casemate_memory_blob blobs_backing[MAX_BLOBS];

	u64 nr_allocated_blobs;
	u64 ordered_blob_list[MAX_BLOBS];
};

/**
 * struct location_set - set of locations
 */
struct location_set {
	u64 locations[MAX_UNCLEAN_LOCATIONS];
	u64 len;
};

#ifndef MAX_LOCKS
#define MAX_LOCKS 64
#endif

/**
 * struct lock_owner_map - Map of pgtable root to lock that owns it.
 */
struct lock_owner_map {
	u64 len;
	sm_owner_t owner_ids[MAX_LOCKS];
	gsm_lock_addr_t locks[MAX_LOCKS];
};

/**
 * enum write_authorization - Permission to write to the pagetable
 * @AUTHORIZED: Can perform any write to the locked object without constraints.
 * @UNAUTHORIZED_PLAIN: Cannot perform a plain (non-atomic) write to valid entries.
 *
 * Captures which kinds of writes to a locked object are permitted.
 */
enum write_authorization {
	AUTHORIZED,
	UNAUTHORIZED_PLAIN,
};

/**
 * struct lock_state - The current ghost state of a lock.
 * @id: The thread ID of the thread that currently owns the lock, or -1 if not held.
 * @write_authorization: what permission the owner of the lock has to the protected object.
 * @count: number of times this lock has been locked.
 */
struct lock_state {
	thread_identifier id;
	enum write_authorization write_authorization;
	u64 count;
};

/**
 * struct lock_state_map - Map of the locks to their current state.
 */
struct lock_state_map {
	u64 len;
	gsm_lock_addr_t address[MAX_LOCKS];
	struct lock_state locker[MAX_LOCKS];
};

/**
 * owner_lock() - Get hyp spinlock for an owner.
 *
 * Returns NULL if no lock for that owner_id.
 */
gsm_lock_addr_t owner_lock(sm_owner_t owner_id);

/**
 * MAX_VMIDS - Maximum number of VMIDs Casemate can support concurrently.
 */
#ifndef MAX_VMIDS
#define MAX_VMIDS 64
#endif

/**
 * typedef vmid_t - A virtual machine identifier (VMID)
 */
typedef u64 vmid_t;

/**
 * typedef addr_id_t - Generic address space identifier (ASID/VMID).
 */
typedef u64 addr_id_t;

/**
 * struct vmid_map - Map from VMID to Root.
 */
struct vmid_map {
	u64 len;
	vmid_t vmids[MAX_VMIDS];
	sm_owner_t roots[MAX_VMIDS];
};

/**
 * struct root - A single root (base addr + ASID/VMID)
 * @present: whether this root is active
 * @stage: whether this points to a stage1 or a stage2 table
 * @baddr: the root base (physical) address.
 * @id: the associated ASID/VMID.
 * @refcount: the number of CPUs that have this root currently active.
 * @index: index of this root in the roots table
 */
struct root {
	bool present;
	entry_stage_t stage;
	sm_owner_t baddr;
	addr_id_t id;
	u64 refcount;
	u64 index;
};

/**
 * struct roots - Pool of currently known roots
 */
struct roots {
	u64 len;
	struct root roots[MAX_ROOTS];
};

/**
 * struct sysreg - A single possibly-present system register value
 */
struct sysreg {
	bool present;
	u64 value;
};

/**
 * try_read_sysreg() - Read system register from Ghost state
 *
 * Returns false if ghost state has no known value for that register
 */
bool try_read_sysreg(enum ghost_sysreg_kind reg, u64 *ret);

/**
 * read_sysreg() - Read system register
 *
 * Performs register read side-effect if register is not known.
 */
u64 read_sysreg(enum ghost_sysreg_kind reg);

/**
 * struct root_index - An (optionally) loaded root with index to it
 */
struct root_index {
	bool present;
	u64 index;
};

typedef struct root_index root_index_t;

/**
 * struct cm_thrd_ctxt - Per thread context ghost copy
 * @current_s1: index into the roots map of the currently-loaded stage1 root
 * @current_s2: index into the roots map of the currently-loaded stage1 root
 */
struct cm_thrd_ctxt {
	root_index_t current_s1;
	root_index_t current_s2;
	struct sysreg regs[MAX_SYSREG];
};

/**
 * struct casemate_model_state - Top-level ghost model state.
 * @base_addr: the physical address of the start of the (ghost) memory.
 * @size: the number of bytes in the ghost memory to track.
 * @memory: the actual ghost model memory.
 * @unclean_locations: set of all the unclean locations
 * @roots: set of known pagetable roots.
 * @thread_context: per-CPU thread-local context.
 * @locks: map from root physical address to lock physical address.
 * @lock_state: map from lock physical address to thread which owns the lock.
 */
struct casemate_model_state {
	u64 base_addr;
	u64 size;
	struct casemate_model_memory memory;

	struct location_set unclean_locations;

	struct roots roots;

	struct cm_thrd_ctxt thread_context[MAX_CPU];

	struct lock_owner_map locks;
	struct lock_state_map lock_state;
};

int ghost_dump_model_state(void *arg, struct casemate_model_state *st);

/**
 * struct casemate_state - Top-level casemate state
 */
struct casemate_state {
	sm_mtx_t sm_lock;

	bool is_initialised;
	struct casemate_options opts;

	/**
	 * current_transition - The step currently being executed.
	 */
	struct casemate_model_step current_transition;

	/**
	 * traced_current_trans - Whether the current step has been traced so far 
	 */
	bool traced_current_trans;

	/**
	 * transition_id - The sequence ID to give to the next transition.
	 */
	u64 transition_id;

	bool touched_watchpoint;
	struct casemate_watchpoints watchpoints;

	/**
	 * st - The model state
	 *
	 * st[0] is the real global state
	 * st[1] is, optionally, a snapshot of the state
	 */
	struct casemate_model_state st[];
};

extern struct ghost_driver driver;
extern struct casemate_state *the_ghost_state;
#define STATE() the_ghost_state
#define MODEL() (&STATE()->st[0])
#define MODEL_PRE() (&STATE()->st[1])
#define CURRENT_TRANS() STATE()->current_transition

#endif /* CASEMATE_STATE_H */
