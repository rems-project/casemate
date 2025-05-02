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

/**
 * struct sm_tlbi_op_method - Decoded TLBI by-method
 * @kind: whether this is "all", by address, or by address-space-identifier.
 */
struct sm_tlbi_op_method {
	enum sm_tlbi_op_method_kind kind;
	union {
		struct tlbi_op_method_by_address_data {
			uint64_t page;

			bool has_level_hint;
			uint8_t level_hint;

			bool has_asid;
			uint8_t asid;

			bool affects_last_level_only;
		} by_address_data;

		struct tlbi_op_method_by_address_space_id_data {
			uint64_t asid_or_vmid;
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

enum dxb_kind {
	DxB_ish,
	DxB_ishst,
	DxB_nsh,
};

enum barrier_kind {
	BARRIER_DSB,
	BARRIER_ISB
};

enum casemate_model_step_kind {
	/**
	 * @TRANS_HW_STEP - Hardware instruction
	 */
	TRANS_HW_STEP,

	/**
	 * @TRANS_ABS_STEP - An abstract software state transition
	 * These generally transition some abstract reified ghost state in the model
	 * e.g. for locks and C initialisations that are not exposed to the model
	 */
	TRANS_ABS_STEP,

	/**
	 * @TRANS_HINT - A non-hardware-model transition
	 * These generally provide additional information to the casemate model,
	 * such as ownership, to resolve otherwise unbounded non-determinism
	 *
	 * Removing HINTs should not change soundness
	 */
	TRANS_HINT,
};

enum ghost_hw_step_kind {
	HW_MEM_WRITE,
	HW_MEM_READ,
	HW_BARRIER,
	HW_TLBI,
	HW_MSR,
};

struct ghost_hw_step {
	enum ghost_hw_step_kind kind;
	union {
		struct trans_write_data {
			enum memory_order_t mo;
			uint64_t phys_addr;
			uint64_t val;
		} write_data;

		struct trans_read_data {
			uint64_t phys_addr;
			uint64_t val;
		} read_data;

		struct trans_barrier_data {
			enum barrier_kind kind;
			enum dxb_kind dxb_data;
		} barrier_data;

		struct trans_tlbi_data {
			enum tlbi_kind tlbi_kind;
			uint64_t value;
		} tlbi_data;

		struct trans_msr_data {
			enum ghost_sysreg_kind sysreg;
			uint64_t val;
		} msr_data;
	};
};

enum ghost_abs_kind {
	/**
	 * @GHOST_ABS_LOCK - Acquire a mutex
	 */
	GHOST_ABS_LOCK,

	/**
	 * @GHOST_ABS_UNLOCK - Release a mutex
	 */
	GHOST_ABS_UNLOCK,

	/**
	 * @GHOST_ABS_INIT - Zeroed initialisation of some fresh memory
	 */
	GHOST_ABS_INIT,

	/**
	 * @GHOST_ABS_MEMSET - A C memset() call.
	 */
	GHOST_ABS_MEMSET,
};

struct ghost_abs_step {
	enum ghost_abs_kind kind;
	union {
		struct trans_init_data {
			uint64_t location;
			uint64_t size;
		} init_data;

		struct trans_lock_data {
			uint64_t address;
		} lock_data;

		struct trans_memset_data {
			uint64_t address;
			uint64_t size;
			uint64_t value;
		} memset_data;
	};
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

struct ghost_hint_step {
	enum ghost_hint_kind kind;
	uint64_t location;
	uint64_t value;
};

/**
 * Source location info
 */
struct src_loc {
	const char *file;
	const char *func;
	int lineno;
};

struct casemate_model_step {
	/**
	 * @tid: thread identifier.
	 */
	uint8_t tid;

	/**
	 * @seq_id: sequence id number of the transition.
	 */
	uint64_t seq_id;

	/**
	 * @src_loc: string location (path, function name, lineno etc)
	 *           of where the transition happens in the source code.
	 *           For debugging/pretty printing.
	 */
	struct src_loc src_loc;

	enum casemate_model_step_kind kind;
	union {
		struct ghost_hw_step hw_step;
		struct ghost_abs_step abs_step;
		struct ghost_hint_step hint_step;
	};
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
 * casemate_model_step() - Take a step in the ghost model.
 */
void casemate_model_step(struct casemate_model_step trans);
