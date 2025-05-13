/**
 * enum memory_order_t - A custom subset of standard `memory_order`.
 */
enum memory_order_t {
	WMO_plain,
	WMO_release,
};

/// Decoded TLBIs

enum sm_tlbi_op_stage {
	TLBI_OP_STAGE1 = 1,
	TLBI_OP_STAGE2 = 2,
	TLBI_OP_BOTH_STAGES = TLBI_OP_STAGE1 | TLBI_OP_STAGE2,
};

enum sm_tlbi_op_method_kind {
	TLBI_OP_BY_ALL = 0, /* TLBI ALL* only */
	TLBI_OP_BY_INPUT_ADDR = 1, /* by Input-Address */
	TLBI_OP_BY_ADDR_SPACE = 2, /* by ASID/VMID */

	TLBI_OP_BY_VA = TLBI_OP_BY_INPUT_ADDR,
	TLBI_OP_BY_IPA = TLBI_OP_BY_INPUT_ADDR,

	TLBI_OP_BY_VMID = TLBI_OP_BY_ADDR_SPACE,
	TLBI_OP_BY_ASID = TLBI_OP_BY_ADDR_SPACE,
};

enum sm_tlbi_op_regime_kind {
	TLBI_REGIME_EL10 = 1, /* EL1&0 regime */
	TLBI_REGIME_EL2 = 2, /* EL2 regime */
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

enum dxb_kind {
	DxB_ish,
	DxB_ishst,
	DxB_nsh,
};

enum barrier_kind {
	BARRIER_DSB,
	BARRIER_ISB
};

enum ghost_hint_kind {
	/**
	 * @GHOST_HINT_SET_ROOT_LOCK - Set the lock owning a pgtable root.
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

	/**
	 * @GHOST_HINT_SET_PTE_THREAD_OWNER - Set the a thread to be the owner of a PTE (only for leaves)
	 */
	GHOST_HINT_SET_PTE_THREAD_OWNER,
};

/**
 * Source location info
 */
struct src_loc {
	const char *file;
	const char *func;
	int lineno;
};

/**
 * initialise_casemate_model() - One-shot initialisation of model state.
 * @opts: a reference to an initial configuration to use during setup.
 * @phys: the start physical address of the memory given to pKVM.
 * @size: the size of the region of physical address space given to pKVM.
 * @sm_virt: the start of the virtual address of the memory the ghost model state can live in
 * @sm_size: the space given for the ghost model memory.
 *
 * `phys` and `size` define the region of memory that the model reserves for its own state.
 *
 * Returns -12 (ENOMEM) if `sm_size` is not enough memory, otherwise 0.
 *
 * NOTE: After this the target must manually initialise the already-existing pagetable memory with steps.
 */
int initialise_casemate_model(struct casemate_options *opts, uint64_t phys, uint64_t size,
			      void *sm_virt, uint64_t sm_size);

/**
 * casemate_cpu_id() - Return current CPU identifier.
 *
 * Users should implement this if they want to use the helper macros.
 */
extern uint64_t casemate_cpu_id(void);

/// Transition API Steps ///

// Step helpers

#define SRC_LOC \
	(struct src_loc) \
	{ \
		.file = __FILE__, .lineno = __LINE__, .func = __func__ \
	}

#define THREAD_ID casemate_cpu_id()

#define casemate_model_step_write(...) \
	__casemate_model_step_write(THREAD_ID, SRC_LOC, __VA_ARGS__)
void __casemate_model_step_write(uint64_t tid, struct src_loc src_loc, enum memory_order_t mo,
				 uint64_t phys, uint64_t val);

#define casemate_model_step_read(...) __casemate_model_step_read(THREAD_ID, SRC_LOC, __VA_ARGS__)
void __casemate_model_step_read(uint64_t tid, struct src_loc src_loc, uint64_t phys,
				uint64_t val);

#define casemate_model_step_dsb(...) __casemate_model_step_dsb(THREAD_ID, SRC_LOC, __VA_ARGS__)
void __casemate_model_step_dsb(uint64_t tid, struct src_loc src_loc, enum dxb_kind kind);

#define casemate_model_step_isb() __casemate_model_step_isb(THREAD_ID, SRC_LOC)
void __casemate_model_step_isb(uint64_t tid, struct src_loc src_loc);

#define casemate_model_step_tlbi_reg(...) \
	__casemate_model_step_tlbi_reg(THREAD_ID, SRC_LOC, __VA_ARGS__)

void __casemate_model_step_tlbi_reg(uint64_t tid, struct src_loc src_loc, enum tlbi_kind kind,
				    uint64_t value);

#define casemate_model_step_tlbi(...) __casemate_model_step_tlbi(THREAD_ID, SRC_LOC, __VA_ARGS__)
#define casemate_model_step_tlbi_va(TLBI_KIND, ADDR, TTL, ASID) \
	casemate_model_step_tlbi_reg((TLBI_KIND), (ADDR) | ((TTL) << 44ULL) | ((ASID) << 48ULL))

#define casemate_model_step_tlbi_ipa(TLBI_KIND, ADDR, TTL) \
	casemate_model_step_tlbi_reg((TLBI_KIND), (ADDR) | ((TTL) << 44ULL))

void __casemate_model_step_tlbi(uint64_t tid, struct src_loc src_loc, enum tlbi_kind kind);

#define casemate_model_step_msr(...) __casemate_model_step_msr(THREAD_ID, SRC_LOC, __VA_ARGS__)
void __casemate_model_step_msr(uint64_t tid, struct src_loc src_loc,
			       enum ghost_sysreg_kind sysreg, uint64_t val);

#define casemate_model_step_hint(...) __casemate_model_step_hint(THREAD_ID, SRC_LOC, __VA_ARGS__)
void __casemate_model_step_hint(uint64_t tid, struct src_loc src_loc, enum ghost_hint_kind kind,
				uint64_t location, uint64_t value);

#define casemate_model_step_init(...) __casemate_model_step_init(THREAD_ID, SRC_LOC, __VA_ARGS__)
void __casemate_model_step_init(uint64_t tid, struct src_loc src_loc, uint64_t location,
				uint64_t size);

#define casemate_model_step_memset(...) \
	__casemate_model_step_memset(THREAD_ID, SRC_LOC, __VA_ARGS__)
void __casemate_model_step_memset(uint64_t tid, struct src_loc src_loc, uint64_t location,
				  uint64_t value, uint64_t size);

#define casemate_model_step_lock(...) __casemate_model_step_lock(THREAD_ID, SRC_LOC, __VA_ARGS__)
void __casemate_model_step_lock(uint64_t tid, struct src_loc src_loc, uint64_t address);

#define casemate_model_step_unlock(...) \
	__casemate_model_step_unlock(THREAD_ID, SRC_LOC, __VA_ARGS__)
void __casemate_model_step_unlock(uint64_t tid, struct src_loc src_loc, uint64_t address);
