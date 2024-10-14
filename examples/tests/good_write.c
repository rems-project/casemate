/**
 * A very simple test of the tracer and driver,
 * generates a sequence of all the transitions over dummy variables and traces them.
 */
#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>

#include "common.h"

/* locations we can pretend are pagetables
 */
__attribute__((aligned(4096)))
u64 table[512];
u64 l;

int main(int argc, char **argv)
{
	common_init(argc, argv);
	MARK_VAR(table);
	MARK_VAR(l);

	/* tell the modle pud and pgd tables exist,
	 * and logically associate them with the lock. */
	TRANS_MEM_INIT((u64)table, 4096);
	HINT(GHOST_HINT_SET_ROOT_LOCK, (u64)table, (u64)&l);

	/* track table as the root of a tree */
	MSR(SYSREG_VTTBR, (u64)table);

	LOCK(l);
	WRITE_ONCE(table[0], 0);
	UNLOCK(l);
}