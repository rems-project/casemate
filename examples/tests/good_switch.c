#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>

#include "common.h"

/* locations we can pretend are pagetables
 */
__attribute__((aligned(4096)))
u64 root[512];
u64 new_root[512];
u64 l1,l2;

int main(int argc, char **argv)
{
	common_init(argc, argv);

	TRANS_MEM_INIT((u64)root, 4096);
	TRANS_MEM_INIT((u64)new_root, 4096);
	HINT(GHOST_HINT_SET_ROOT_LOCK, (u64)root, (u64)&l1);
	HINT(GHOST_HINT_SET_ROOT_LOCK, (u64)new_root, (u64)&l2);

	MSR(SYSREG_VTTBR, MAKE_TTBR((u64)root, ID0));
	ISB();

	MSR(SYSREG_VTTBR, MAKE_TTBR((u64)new_root, ID1));
	ISB();

	MSR(SYSREG_VTTBR, MAKE_TTBR((u64)root, ID0));
	ISB();
}
