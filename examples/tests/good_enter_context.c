/**
 * Check exception context exit/enter lets an out-of-context loaded root be
 * released, but requires reinitialisation before it can be used again.
 */
#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>

#include "common.h"

__attribute__((aligned(4096)))
u64 root[512],new_root[512];
u64 l1,l2;

int main(int argc, char **argv)
{
	common_init(argc, argv);

	TRANS_MEM_INIT((u64)root, 4096);
	TRANS_MEM_INIT((u64)new_root, 4096);
	HINT(GHOST_HINT_SET_ROOT_LOCK, (u64)root, (u64)&l1);
	HINT(GHOST_HINT_SET_ROOT_LOCK, (u64)new_root, (u64)&l2);

	MSR(SYSREG_VTTBR, (u64)root);
	MSR(SYSREG_HCR_EL2, HCR_MMU_ON);
	MSR(SYSREG_VTTBR, MAKE_TTBR((u64)new_root, ID1));

	casemate_model_step_exit_context();
	HINT(GHOST_HINT_RELEASE_TABLE, (u64)new_root, 0);
	TRANS_MEM_INIT((u64)new_root, 4096);
	HINT(GHOST_HINT_SET_ROOT_LOCK, (u64)new_root, (u64)&l2);
	casemate_model_step_enter_context(1);
}
