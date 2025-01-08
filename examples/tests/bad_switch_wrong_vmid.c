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
u64 new_child[512];
u64 l;

int main(int argc, char **argv)
{
	common_init(argc, argv);

	TRANS_MEM_INIT((u64)root, 4096);
	HINT(GHOST_HINT_SET_ROOT_LOCK, (u64)root, (u64)&l);

	/* associate with VMID 0 */
	MSR(SYSREG_VTTBR, MAKE_TTBR((u64)root, 0ULL));
	DSB(ish);
	ISB();

	/* try context-switch to same baddr with different VMID */
	MSR(SYSREG_VTTBR, MAKE_TTBR((u64)root, 1ULL));
}