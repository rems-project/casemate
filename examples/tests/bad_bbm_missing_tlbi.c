#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>

#include "common.h"

/* locations we can pretend are pagetables
 */
__attribute__((aligned(4096)))
u64 l0[512], l1[512], l2[512], l3[512];
u64 l;

int main(int argc, char **argv)
{
	common_init(argc, argv);

	TRANS_MEM_INIT((u64)l0, 4096);
	TRANS_MEM_INIT((u64)l1, 4096);
	TRANS_MEM_INIT((u64)l2, 4096);
	TRANS_MEM_INIT((u64)l3, 4096);

	HINT(GHOST_HINT_SET_ROOT_LOCK, (u64)l0, (u64)&l);

	HINT(GHOST_HINT_SET_OWNER_ROOT, (u64)l1, (u64)l0);
	HINT(GHOST_HINT_SET_OWNER_ROOT, (u64)l2, (u64)l0);
	HINT(GHOST_HINT_SET_OWNER_ROOT, (u64)l3, (u64)l0);

	/* make tree */
	WRITE_ONCE(l0[0], (u64)l1 | 0b11);
	WRITE_ONCE(l1[0], (u64)l2 | 0b11);
	WRITE_ONCE(l2[0], (u64)l3 | 0b11);
	WRITE_ONCE(l3[0], (u64)0xDEAD000 | 0b11);

	/* track tree */
	MSR(SYSREG_VTTBR, (u64)l0);
	MSR(SYSREG_HCR_EL2, HCR_MMU_ON);

	LOCK(l);
	WRITE_ONCE(l3[0], 0);
	DSB(ish);
	/* no TLBI */
	DSB(ish);
	WRITE_ONCE(l3[0], 0xBEEF000 | 0b11);
	UNLOCK(l);
}
