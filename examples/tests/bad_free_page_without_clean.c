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
u64 root[512];
u64 child[512];
u64 new_root[512];
u64 l1,l2;

int main(int argc, char **argv)
{
	common_init(argc, argv);

	TRANS_MEM_INIT((u64)root, 4096);
	TRANS_MEM_INIT((u64)child, 4096);
	TRANS_MEM_INIT((u64)new_root, 4096);
	HINT(GHOST_HINT_SET_ROOT_LOCK, (u64)root, (u64)&l1);
	HINT(GHOST_HINT_SET_ROOT_LOCK, (u64)new_root, (u64)&l2);
	HINT(GHOST_HINT_SET_OWNER_ROOT, (u64)child, (u64)root);
	WRITE_ONCE(root[0], (u64)child | 0b11);

	MSR(SYSREG_VTTBR, (u64)root);

	LOCK(l1);
	WRITE_ONCE(root[0], 0);

	/* cannot release child without TLB maintenance */
	HINT(GHOST_HINT_RELEASE_TABLE, (u64)child, 0);
}