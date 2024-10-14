#include <casemate-impl.h>

///////////
// atomics

void __atomic_cas(volatile u64 *va, u64 old, u64 new) {
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
    "ldxr x0, [%[va]]\n"
    "cmp x0, %[old]\n"
    "b.ne 0b\n"
    "dsb sy\n"
    "stxr w1, %[val], [%[va]]\n"
    "cbnz w1, 1b\n"

    "1:\n"
    "sev\n"
    :
    : [va] "r"(va), [val] "r"(new), [old] "r"(old)
    : "memory", "x0", "x1"
  );
}

///////////
// locking

struct mutex {
	u64 locked;
};

struct mutex sm_lock = {.locked = 0};

void lock_sm(void)
{
	__atomic_cas(&sm_lock.locked, 0, 1);
}

void unlock_sm(void)
{
	__atomic_cas(&sm_lock.locked, 1, 0);
}
