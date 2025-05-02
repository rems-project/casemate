//////////////
// Step helpers

#define SRC_LOC \
	(struct src_loc) \
	{ \
		.file = __FILE__, .lineno = __LINE__, .func = __func__ \
	}

/**
 * casemate_cpu_id() - Return current CPU identifier.
 *
 * Users should implement this if they want to use the helper macros.
 */
extern uint64_t casemate_cpu_id(void);
#define THREAD_ID casemate_cpu_id()

#define casemate_model_step_write(...) \
	__casemate_model_step_write(THREAD_ID, SRC_LOC, __VA_ARGS__)
static inline void __casemate_model_step_write(uint64_t tid, struct src_loc src_loc,
					       enum memory_order_t mo, uint64_t phys,
					       uint64_t val)
{
	casemate_model_step((struct casemate_model_step){
		.tid = tid,
		.src_loc = src_loc,
		.kind = TRANS_HW_STEP,
		.hw_step =
			(struct ghost_hw_step){
				.kind = HW_MEM_WRITE,
				.write_data =
					(struct trans_write_data){
						.mo = mo,
						.phys_addr = phys,
						.val = val,
					},
			},
	});
}

#define casemate_model_step_read(...) __casemate_model_step_read(THREAD_ID, SRC_LOC, __VA_ARGS__)
static inline void __casemate_model_step_read(uint64_t tid, struct src_loc src_loc, uint64_t phys,
					      uint64_t val)
{
	casemate_model_step((struct casemate_model_step){
		.tid = tid,
		.src_loc = src_loc,
		.kind = TRANS_HW_STEP,
		.hw_step =
			(struct ghost_hw_step){
				.kind = HW_MEM_READ,
				.read_data =
					(struct trans_read_data){
						.phys_addr = phys,
						.val = val,
					},
			},
	});
}

#define casemate_model_step_dsb(...) __casemate_model_step_dsb(THREAD_ID, SRC_LOC, __VA_ARGS__)
static inline void __casemate_model_step_dsb(uint64_t tid, struct src_loc src_loc,
					     enum dxb_kind kind)
{
	casemate_model_step((struct casemate_model_step){
		.tid = tid,
		.src_loc = src_loc,
		.kind = TRANS_HW_STEP,
		.hw_step =
			(struct ghost_hw_step){
				.kind = HW_BARRIER,
				.barrier_data =
					(struct trans_barrier_data){
						.kind = BARRIER_DSB,
						.dxb_data = kind,
					},
			},
	});
}

#define casemate_model_step_isb() __casemate_model_step_isb(THREAD_ID, SRC_LOC)
static inline void __casemate_model_step_isb(uint64_t tid, struct src_loc src_loc)
{
	casemate_model_step((struct casemate_model_step){
		.tid = tid,
		.src_loc = src_loc,
		.kind = TRANS_HW_STEP,
		.hw_step =
			(struct ghost_hw_step){
				.kind = HW_BARRIER,
				.barrier_data =
					(struct trans_barrier_data){
						.kind = BARRIER_ISB,
					},
			},
	});
}

#define casemate_model_step_tlbi_reg(...) \
	__casemate_model_step_tlbi_reg(THREAD_ID, SRC_LOC, __VA_ARGS__)
static inline void __casemate_model_step_tlbi_reg(uint64_t tid, struct src_loc src_loc,
						  enum tlbi_kind kind, uint64_t value)
{
	casemate_model_step((struct casemate_model_step){
		.tid = tid,
		.src_loc = src_loc,
		.kind = TRANS_HW_STEP,
		.hw_step =
			(struct ghost_hw_step){
				.kind = HW_TLBI,
				.tlbi_data =
					(struct trans_tlbi_data){
						.tlbi_kind = kind,
						.value = value,
					},
			},
	});
}

#define casemate_model_step_tlbi(...) __casemate_model_step_tlbi(THREAD_ID, SRC_LOC, __VA_ARGS__)
static inline void __casemate_model_step_tlbi(uint64_t tid, struct src_loc src_loc,
					      enum tlbi_kind kind)
{
	casemate_model_step((struct casemate_model_step){
		.tid = tid,
		.src_loc = src_loc,
		.kind = TRANS_HW_STEP,
		.hw_step =
			(struct ghost_hw_step){
				.kind = HW_TLBI,
				.tlbi_data =
					(struct trans_tlbi_data){
						.tlbi_kind = kind,
					},
			},
	});
}

#define casemate_model_step_tlbi_va(TLBI_KIND, ADDR, TTL, ASID) \
	casemate_model_step_tlbi_reg((TLBI_KIND), (ADDR) | ((TTL) << 44ULL) | ((ASID) << 48ULL))

#define casemate_model_step_tlbi_ipa(TLBI_KIND, ADDR, TTL) \
	casemate_model_step_tlbi_reg((TLBI_KIND), (ADDR) | ((TTL) << 44ULL))

#define casemate_model_step_msr(...) __casemate_model_step_msr(THREAD_ID, SRC_LOC, __VA_ARGS__)
static inline void __casemate_model_step_msr(uint64_t tid, struct src_loc src_loc,
					     enum ghost_sysreg_kind sysreg, uint64_t val)
{
	casemate_model_step((struct casemate_model_step){
		.tid = tid,
		.src_loc = src_loc,
		.kind = TRANS_HW_STEP,
		.hw_step =
			(struct ghost_hw_step){
				.kind = HW_MSR,
				.msr_data =
					(struct trans_msr_data){
						.sysreg = sysreg,
						.val = val,
					},
			},
	});
}

#define casemate_model_step_hint(...) __casemate_model_step_hint(THREAD_ID, SRC_LOC, __VA_ARGS__)
static inline void __casemate_model_step_hint(uint64_t tid, struct src_loc src_loc,
					      enum ghost_hint_kind kind, uint64_t location,
					      uint64_t value)
{
	casemate_model_step((struct casemate_model_step){
		.tid = tid,
		.src_loc = src_loc,
		.kind = TRANS_HINT,
		.hint_step =
			(struct ghost_hint_step){
				.kind = kind,
				.location = location,
				.value = value,
			},
	});
}

#define casemate_model_step_init(...) __casemate_model_step_init(THREAD_ID, SRC_LOC, __VA_ARGS__)
static inline void __casemate_model_step_init(uint64_t tid, struct src_loc src_loc,
					      uint64_t location, uint64_t size)
{
	casemate_model_step((struct casemate_model_step){
		.tid = tid,
		.src_loc = src_loc,
		.kind = TRANS_ABS_STEP,
		.abs_step =
			(struct ghost_abs_step){
				.kind = GHOST_ABS_INIT,
				.init_data =
					(struct trans_init_data){
						.location = location,
						.size = size,
					},
			},
	});
}

#define casemate_model_step_memset(...) \
	__casemate_model_step_memset(THREAD_ID, SRC_LOC, __VA_ARGS__)
static inline void __casemate_model_step_memset(uint64_t tid, struct src_loc src_loc,
						uint64_t location, uint64_t value, uint64_t size)
{
	casemate_model_step((struct casemate_model_step){
		.tid = tid,
		.src_loc = src_loc,
		.kind = TRANS_ABS_STEP,
		.abs_step =
			(struct ghost_abs_step){
				.kind = GHOST_ABS_MEMSET,
				.memset_data =
					(struct trans_memset_data){
						.address = location,
						.size = size,
						.value = value,
					},
			},
	});
}

#define casemate_model_step_lock(...) __casemate_model_step_lock(THREAD_ID, SRC_LOC, __VA_ARGS__)
static inline void __casemate_model_step_lock(uint64_t tid, struct src_loc src_loc,
					      uint64_t address)
{
	casemate_model_step((struct casemate_model_step){
		.tid = tid,
		.src_loc = src_loc,
		.kind = TRANS_ABS_STEP,
		.abs_step =
			(struct ghost_abs_step){
				.kind = GHOST_ABS_LOCK,
				.lock_data =
					(struct trans_lock_data){
						.address = address,
					},
			},
	});
}

#define casemate_model_step_unlock(...) \
	__casemate_model_step_unlock(THREAD_ID, SRC_LOC, __VA_ARGS__)
static inline void __casemate_model_step_unlock(uint64_t tid, struct src_loc src_loc,
						uint64_t address)
{
	casemate_model_step((struct casemate_model_step){
		.tid = tid,
		.src_loc = src_loc,
		.kind = TRANS_ABS_STEP,
		.abs_step =
			(struct ghost_abs_step){
				.kind = GHOST_ABS_UNLOCK,
				.lock_data =
					(struct trans_lock_data){
						.address = address,
					},
			},
	});
}
