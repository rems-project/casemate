/**
 * A very simple test of the tracer and driver,
 * generates a sequence of all the transitions over dummy variables and traces them.
 */
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
u64 table[512];
u64 l;

int write_pte1(void *arg)
{
	WRITE_RELEASE(table[1], 1);
	send((tid_t)2, 1);
	return 0;
}

int write_pte2(void *arg)
{
	recv();
	WRITE_RELEASE(table[1], 1);
	return 0;
}

int main(int argc, char **argv)
{
	common_init(argc, argv);

	/* tell the modle pud and pgd tables exist,
	 * and logically associate them with the lock. */
	TRANS_MEM_INIT((u64)table, 4096);
	HINT(GHOST_HINT_SET_ROOT_LOCK, (u64)table, (u64)&l);

	/* track table as the root of a tree */
	MSR(SYSREG_VTTBR, (u64)table);
	spawn_thread(write_pte1);
	spawn_thread(write_pte2);
	join();

	return 0;
}
