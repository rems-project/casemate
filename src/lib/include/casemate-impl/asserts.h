#ifndef CASEMATE_ASSERTS_H
#define CASEMATE_ASSERTS_H

#ifndef __KVM_NVHE_HYPERVISOR__
#include <casemate-impl/options.h>
#include <casemate-impl/printer.h>
#include <casemate-impl/model.h>

#define ghost_assert(expr) \
	if (!(expr)) { \
		GHOST_WARN(#expr); \
		side_effect()->abort("assertion failed: " #expr " in " __FILE__); \
		__builtin_unreachable(); \
	}

#define ghost_safety_check(expr) \
	if (opts()->enable_safety_checks) { \
		ghost_assert(expr); \
	}

#define BUG() do { \
	ghost_assert(false); \
 	__builtin_unreachable(); \
} while (0);

#define GHOST_MODEL_CATCH_FIRE(msg) { \
	ensure_traced_current_transition(true); \
	side_effect()->abort(msg); \
}

#define unreachable() do { \
	ghost_assert(false); \
	__builtin_unreachable(); \
} while (0);

#else

#include <nvhe/ghost/ghost_context.h>
#include <nvhe/ghost/ghost_asserts.h>

#define GHOST_MODEL_CATCH_FIRE(msg) { \
	ensure_traced_current_transition(true); \
	GHOST_WARN(msg); \
	ghost_assert(false); \
}

#endif

#endif /* CASEMATE_ASSERTS_H */