#ifndef CASEMATE_ASSERTS_H
#define CASEMATE_ASSERTS_H

#include <casemate-impl/options.h>
#include <casemate-impl/printer.h>

#define GHOST_WARN(FMT, ...) { \
		ghost_printf(NULL, GHOST_WHITE_ON_YELLOW FMT GHOST_NORMAL "\n", ##__VA_ARGS__); \
	}

#define ghost_assert(expr) \
	if (!(expr)) { \
		GHOST_WARN(#expr); \
		side_effect()->abort("assertion failed: " #expr " in " __FILE__); \
	}

#define ghost_safety_check(expr) \
	if (opts()->enable_safety_checks) { \
		ghost_assert(expr); \
	}

#define GHOST_MODEL_CATCH_FIRE(msg) { \
	side_effect()->abort(msg); \
}

#define BUG() __builtin_unreachable()

#endif /* CASEMATE_ASSERTS_H */