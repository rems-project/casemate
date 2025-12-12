#include <casemate-impl.h>

///////////
// atomics

#define SM_LOCK() (&STATE()->sm_lock)

#if defined(__AARCH64__)

void __atomic_cas(volatile u64 *va, u64 old, u64 new)
{
	/* atomic test and update
	 * equivalent to an atomic:
	 * <while (*va != old); *va = new>;
	 */
	asm volatile(
		/* dont wait on first read */
		"sevl\n"

		/* skip to first read */
		"b 1f\n"
		"0:\n"
		/* if the load-exclusive failed to read old,
		 * then clear the exclusives manually, so as not to
		 * block any other read/write
		 */
		"clrex\n"
		"1:\n"
		"wfe\n"
		"ldaxr x0, [%[va]]\n"
		"cmp x0, %[old]\n"
		"b.ne 0b\n"
		"stlxr w1, %[val], [%[va]]\n"
		"cbnz w1, 1b\n"

		"1:\n"
		"sev\n"
		:
		: [va] "r"(va), [val] "r"(new), [old] "r"(old)
		: "memory", "x0", "x1");
}

///////////
// locking

void init_sm_lock(void)
{
	SM_LOCK()->locked = 0;
}

void lock_sm(void)
{
	__atomic_cas(&SM_LOCK()->locked, 0, 1);
}

void unlock_sm(void)
{
	__atomic_cas(&SM_LOCK()->locked, 1, 0);
}

#elif defined(__X86__)

/* it's okay to include stdatomic on X86 builds
 * as they won't be linked into an actual core.
 */
#include <threads.h>

void init_sm_lock(void)
{
	mtx_init(SM_LOCK(), mtx_plain);
}

void lock_sm(void)
{
	mtx_lock(SM_LOCK());
}

void unlock_sm(void)
{
	mtx_unlock(SM_LOCK());
}

#else

#error REQUIRES_CONFIGURE_WITH_AN_ARCHITECTURE

#endif
