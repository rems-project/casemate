#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>

#include "common.h"

/* locations we can pretend are pagetables
 */
__attribute__((aligned(4096)))
u64 table[512];

int main(int argc, char **argv)
{
	common_init(argc, argv);

	/* start casemate transitions */
	TRANS_MEM_INIT((u64)table, 4096);
	MSR(SYSREG_VTTBR, (u64)table);
	WRITE_ONCE(table[0], 0);
}
