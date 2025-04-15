#ifndef CASEMATE_LINUX_H
#define CASEMATE_LINUX_H

#ifdef __KVM_NVHE_HYPERVISOR__
#endif

#include <linux/bits.h>

#include <nvhe/ghost/ghost_context.h>
#include <nvhe/ghost/ghost_asserts.h>

#define GHOST_MODEL_CATCH_FIRE(msg) \
	{ \
		ensure_traced_current_transition(true); \
		GHOST_WARN(msg); \
		ghost_assert(false); \
	}

#define BITMASK(HI, LO) GENMASK(HI, LO)

#define CONFIG_LINUX

#define CONFIG_HAS_BITWISE
#define CONFIG_HAS_ASSERT
#define CONFIG_HAS_PRINTF
#define CONFIG_HAS_STRLEN

#endif /* CASEMATE_LINUX_H */