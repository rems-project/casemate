#ifndef CASEMATE_TYPES_H
#define CASEMATE_TYPES_H

#ifndef CONFIG_HAS_STDARG
#include <stdarg.h>
#endif /* CONFIG_HAS_STDARG */

#ifndef CONFIG_HAS_STDINT
#include <stdint.h>
#include <stdbool.h>

typedef uint64_t u64;
typedef int64_t s64;
typedef uint32_t u32;
typedef int32_t s32;
typedef uint8_t u8;
typedef uint64_t phys_addr_t;
#endif /* CONFIG_HAS_STDINT */

#ifndef NULL
#define NULL ((void *)0)
#endif

#endif /* CASEMATE_TYPES_H */
