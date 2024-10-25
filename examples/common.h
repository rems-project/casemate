#ifndef COMMON_H
#define COMMON_H

#include <casemate.h>

void common_init(int argc, char **argv);

/* dummy variables pretending to be hypervisor system registers */
extern u64 TCR_EL2;
extern u64 VTCR_EL2;
extern u64 MAIR_EL2;

#define WRITE_ONCE(VAR, VAL) \
	({	\
		casemate_model_step_write(WMO_plain, (u64)&VAR, (VAL)); \
		VAR = (VAL); \
	})

#define WRITE_RELEASE(VAR, VAL) \
	({	\
		VAR = (VAL); \
		casemate_model_step_write(WMO_release, (u64)&VAR, (VAL)); \
	})

#define READ_ONCE(VAR, VAL) \
	({	\
		typeof(VAR) tmp = (VAR); \
		casemate_model_step_read((u64)&VAR, tmp); \
		tmp; \
	})

#define DSB(KIND) \
	casemate_model_step_dsb(DxB_##KIND)

#define ISB() \
	casemate_model_step_isb()

#define TLBI_ALL(OP) \
	casemate_model_step_tlbi1(TLBI_##OP)

#define TLBI_ADDR(OP, ADDR, LEVEL) \
	casemate_model_step_tlbi3(TLBI_##OP, ADDR, LEVEL)

#define LOCK(L) \
	casemate_model_step_lock((u64)&(L))

#define UNLOCK(L) \
	casemate_model_step_unlock((u64)&(L))

#define HINT(HINT, VAR, VAL) \
	casemate_model_step_hint(HINT, VAR, VAL)

#define TRANS_MEM_INIT(VAR, SIZE) \
	casemate_model_step_init(VAR, SIZE)

#define TRANS_MEM_SET(VAR, SIZE, VAL) \
	casemate_model_step_memset(VAR, SIZE, VAL)

#define MSR(REG, VAL) \
	casemate_model_step_msr(REG, VAL)

#endif /* COMMON_H */