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

	/* start casemate transitions */
	TRANS_MEM_INIT((u64)table, 4096);
	HINT(GHOST_HINT_SET_ROOT_LOCK, (u64)table, (u64)&l);
	MSR(SYSREG_VTTBR, (u64)table);
	WRITE_ONCE(table[0], 0);
}