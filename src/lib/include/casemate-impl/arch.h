#ifndef CASEMATE_ARCH_H
#define CASEMATE_ARCH_H

#include <casemate-impl/bitwise.h>

#define PAGE_SHIFT 12
#define PAGE_SIZE (1 << PAGE_SHIFT)

#define OFFSET_IN_PAGE(x) (((x)&BITMASK(PAGE_SHIFT - 1, 0)))
#define PAGE_ALIGN_DOWN(x) ((x) & ~BITMASK(PAGE_SHIFT - 1, 0))
#define PAGE_ALIGN(x) PAGE_ALIGN_DOWN(((x) + PAGE_SIZE - 1))
#define IS_PAGE_ALIGNED(x) (OFFSET_IN_PAGE(x) == 0)

#endif /* CASEMATE_ARCH_H */