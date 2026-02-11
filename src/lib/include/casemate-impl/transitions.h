#ifndef CASEMATE_TRANSITIONS_H
#define CASEMATE_TRANSITIONS_H

#include <casemate.h>

#include <casemate-impl/types.h>

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

			bool has_asid;
			u8 asid;

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
			u64 phys_addr;
			u64 val;
		} write_data;

		struct trans_read_data {
			u64 phys_addr;
			u64 val;
		} read_data;

		struct trans_barrier_data {
			enum barrier_kind kind;
			enum dxb_kind dxb_data;
		} barrier_data;

		struct trans_tlbi_data {
			enum tlbi_kind tlbi_kind;
			u64 value;
		} tlbi_data;

		struct trans_msr_data {
			enum ghost_sysreg_kind sysreg;
			u64 val;
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
			u64 location;
			u64 size;
		} init_data;

		struct trans_lock_data {
			u64 address;
		} lock_data;

		struct trans_memset_data {
			u64 address;
			u64 size;
			u64 value;
		} memset_data;
	};
};

struct ghost_hint_step {
	enum ghost_hint_kind kind;
	u64 location;
	u64 value;
};

struct casemate_model_step {
	/**
	 * @tid: thread identifier.
	 */
	u8 tid;

	/**
	 * @seq_id: sequence id number of the transition.
	 */
	u64 seq_id;

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
 * casemate_model_step() - Take a step in the ghost model.
 */
void casemate_model_step(struct casemate_model_step trans);

#endif /* CASEMATE_TRANSITIONS_H */
