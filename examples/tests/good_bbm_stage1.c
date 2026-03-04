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
u64 l0[512],l1[512];
u64 l;

int main(int argc, char **argv)
{
	common_init(argc, argv);

	TRANS_MEM_INIT((u64)l0, 4096);
	TRANS_MEM_INIT((u64)l1, 4096);
	HINT(GHOST_HINT_SET_ROOT_LOCK, (u64)l0, (u64)&l);
	HINT(GHOST_HINT_SET_OWNER_ROOT, (u64)l1, (u64)l0);

	/* setup tree */
	WRITE_ONCE(l0[0], (u64)l1 | 0b11);
	WRITE_ONCE(l1[0], (u64)0xDEAD000 | 0b01);

	MSR(SYSREG_TTBR_EL2, (u64)l0);
	MSR(SYSREG_SCTLR_EL2, SCTLR_MMU_ON);

	LOCK(l);
	WRITE_ONCE(l1[0], 0);
	DSB(ish);
	TLBI_ADDR(vae2is,0,3);
	DSB(ish);
	WRITE_ONCE(l1[0], (u64)0xBEEF000 | 0b01);
	UNLOCK(l);
}
