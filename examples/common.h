#ifndef COMMON_H
#define COMMON_H

#include <casemate.h>

void common_init(int argc, char **argv);

/* dummy variables pretending to be hypervisor system registers */
extern u64 TCR_EL2;
extern u64 VTCR_EL2;
extern u64 MAIR_EL2;

typedef u64 tid_t;
void spawn_thread(int fn(void*));
void join(void);
void send(tid_t to, int v);
int recv(void);

/*
 * Macros that require input of a maximum size
 *
 * TODO: make compiler check
 */
#define REQ_U8_AS_U64(X) ((u64)(X))
#define REQ_U64(X) ((u64)(X))

#define MAKE_TTBR(BADDR,ID) \
	((BADDR) | ((ID) << 48ULL))

#define ID0 0ULL
#define ID1 1ULL
#define ID2 2ULL

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
	casemate_model_step_tlbi(TLBI_##OP)

#define TLBI_ADDR(OP, ADDR, LEVEL) \
	casemate_model_step_tlbi_reg(TLBI_##OP, REQ_U64(ADDR) | (REQ_U8_AS_U64(LEVEL) << 44ULL))

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