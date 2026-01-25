#include <casemate.h>

#include <casemate-impl.h>

void __casemate_model_step_write(uint64_t tid, struct src_loc src_loc, enum memory_order_t mo,
				 uint64_t phys, uint64_t val)
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

void __casemate_model_step_read(uint64_t tid, struct src_loc src_loc, uint64_t phys, uint64_t val)
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

void __casemate_model_step_dsb(uint64_t tid, struct src_loc src_loc, enum dxb_kind kind)
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

void __casemate_model_step_isb(uint64_t tid, struct src_loc src_loc)
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

void __casemate_model_step_tlbi_reg(uint64_t tid, struct src_loc src_loc, enum tlbi_kind kind,
				    uint64_t value)
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

void __casemate_model_step_tlbi(uint64_t tid, struct src_loc src_loc, enum tlbi_kind kind)
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

void __casemate_model_step_msr(uint64_t tid, struct src_loc src_loc,
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

void __casemate_model_step_hint(uint64_t tid, struct src_loc src_loc, enum ghost_hint_kind kind,
				uint64_t location, uint64_t value)
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

void __casemate_model_step_init(uint64_t tid, struct src_loc src_loc, uint64_t location,
				uint64_t size)
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

void __casemate_model_step_free(uint64_t tid, struct src_loc src_loc, uint64_t location,
				uint64_t size)
{
	casemate_model_step((struct casemate_model_step){
		.tid = tid,
		.src_loc = src_loc,
		.kind = TRANS_ABS_STEP,
		.abs_step =
			(struct ghost_abs_step){
				.kind = GHOST_ABS_FREE,
				.init_data =
					(struct trans_init_data){
						.location = location,
						.size = size,
					},
			},
	});
}

void __casemate_model_step_memset(uint64_t tid, struct src_loc src_loc, uint64_t location,
				  uint64_t value, uint64_t size)
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

void __casemate_model_step_lock(uint64_t tid, struct src_loc src_loc, uint64_t address)
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

void __casemate_model_step_trylock(uint64_t tid, struct src_loc src_loc, uint64_t address)
{
	casemate_model_step((struct casemate_model_step){
		.tid = tid,
		.src_loc = src_loc,
		.kind = TRANS_ABS_STEP,
		.abs_step =
			(struct ghost_abs_step){
				.kind = GHOST_ABS_TRYLOCK,
				.lock_data =
					(struct trans_lock_data){
						.address = address,
					},
			},
	});
}

void __casemate_model_step_unlock(uint64_t tid, struct src_loc src_loc, uint64_t address)
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
