#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>

#include "common.h"

/* locations we can pretend are pagetables
 */
__attribute__((aligned(4096)))
u64 root[512];
u64 child[512];
u64 l;

int main(int argc, char **argv)
{
	common_init(argc, argv);

	TRANS_MEM_INIT((u64)root, 4096);
	TRANS_MEM_INIT((u64)child, 4096);
	HINT(GHOST_HINT_SET_ROOT_LOCK, (u64)root, (u64)&l);
	HINT(GHOST_HINT_SET_OWNER_ROOT, (u64)child, (u64)root);

	MSR(SYSREG_VTTBR, (u64)root);
	MSR(SYSREG_HCR_EL2, HCR_MMU_ON);
	LOCK(l);
	WRITE_ONCE(root[0], (u64)child | 0b11);
	/* write in the middle */
	WRITE_RELEASE(child[256], 0 | 0b01);
	UNLOCK(l);
}