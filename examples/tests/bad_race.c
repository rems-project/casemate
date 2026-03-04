#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>

#include <threads.h>

#include "common.h"

#define YIELD() \
	thrd_yield()

/* locations we can pretend are pagetables
 */
__attribute__((aligned(4096)))
u64 l0[512], l1[512];
u64 lock;

int write_pte1(void *arg)
{
	common_init_thread();
	WRITE_RELEASE(l1[0], 0);
	thr_send((tid_t)2, 1);
	return 0;
}

int write_pte2(void *arg)
{
	common_init_thread();
	thr_recv();
	WRITE_RELEASE(l1[0], 0);
	return 0;
}

int main(int argc, char **argv)
{
	common_init(argc, argv);

	TRANS_MEM_INIT((u64)l0, 4096);
	TRANS_MEM_INIT((u64)l1, 4096);

	HINT(GHOST_HINT_SET_ROOT_LOCK, (u64)l0, (u64)&lock);

	/* tree */
	WRITE_ONCE(l0[0], (u64)l1 | 0b11);
	WRITE_ONCE(l1[0], (u64)0xDEAD000 | 0b01);

	/* track table as the root of a tree */
	MSR(SYSREG_VTTBR, (u64)l0);
	MSR(SYSREG_HCR_EL2, HCR_MMU_ON);

	thr_spawn(write_pte1);
	thr_spawn(write_pte2);
	thr_join();

	return 0;
}
