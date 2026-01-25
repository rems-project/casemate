#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>

#include "common.h"

u64 l;

int main(int argc, char **argv)
{
	common_init(argc, argv);

	LOCK(l);
	UNLOCK(l);
	LOCK(l);
	TRYLOCK(l);
	TRYLOCK(l);
	UNLOCK(l);
	UNLOCK(l);
}
