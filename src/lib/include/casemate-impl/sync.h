#ifndef CASEMATE_SYNC_H
#define CASEMATE_SYNC_H

#if defined(__AARCH64__)
typedef struct mutex {
	u64 locked;
} sm_mtx_t;
#elif defined(__X86__)
#include <threads.h>
typedef mtx_t sm_mtx_t;
#else
#error REQUIRES_CONFIGURE_WITH_AN_ARCHITECTURE
#endif

void init_sm_lock(void);
void lock_sm(void);
void unlock_sm(void);

#define LOAD_RLX(L) *((volatile __typeof__(L) *)&L)

#define STORE_RLX(L, V) *((volatile __typeof__(L) *)(&L)) = V

#endif /* CASEMATE_SYNC_H */
