#ifndef CASEMATE_ASSERTS_H
#define CASEMATE_ASSERTS_H

#include <casemate-impl/options.h>
#include <casemate-impl/printer.h>
#include <casemate-impl/model.h>

#ifndef CONFIG_HAS_ASSERT
#define ghost_assert(expr) \
	if (! (expr)) { \
		GHOST_WARN(#expr); \
		ensure_traced_current_transition(true); \
		side_effect()->abort("assertion failed: " #expr " in " __FILE__); \
		__builtin_unreachable(); \
	}

#define ghost_safety_check(expr) \
	if (opts()->enable_safety_checks) { \
		ghost_assert(expr); \
	}

#define BUG() \
	do { \
		ghost_assert(false); \
		__builtin_unreachable(); \
	} while (0)

#define GHOST_MODEL_CATCH_FIRE(msg) \
	{ \
		ensure_traced_current_transition(true); \
		side_effect()->abort(msg); \
	}

#define unreachable() \
	do { \
		ghost_assert(false); \
		__builtin_unreachable(); \
	} while (0)
#endif /* CONFIG_HAS_ASSERT */

#endif /* CASEMATE_ASSERTS_H */