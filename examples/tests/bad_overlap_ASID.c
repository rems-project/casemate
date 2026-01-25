#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>

#include "common.h"

/* locations we can pretend are pagetables
 */
__attribute__((aligned(4096)))
u64 root1[512], root2[512];
u64 l1, l2;

int main(int argc, char **argv)
{
	common_init(argc, argv);

	/* tell the modle pud and pgd tables exist,
	 * and logically associate them with the lock. */
	TRANS_MEM_INIT((u64)root1, 4096);
	TRANS_MEM_INIT((u64)root2, 4096);

	HINT(GHOST_HINT_SET_ROOT_LOCK, (u64)root1, (u64)&l1);
	HINT(GHOST_HINT_SET_ROOT_LOCK, (u64)root2, (u64)&l2);

	MSR(SYSREG_TTBR_EL2, MAKE_TTBR((u64)root1, ID0));
	DSB(ish);
	ISB();

	/* two roots cannot be "live" at the same time with the same ASID */
	MSR(SYSREG_TTBR_EL2, MAKE_TTBR((u64)root2, ID0));
}
