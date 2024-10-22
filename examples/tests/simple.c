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
u64 x, y;

int main(int argc, char **argv)
{
	common_init(argc, argv);

	WRITE_ONCE(y, 0);
	DSB(ish);
	WRITE_ONCE(x, 0);
	DSB(ish);
	TLBI_ALL(vmalle1is);
	DSB(nsh);
	ISB();
}