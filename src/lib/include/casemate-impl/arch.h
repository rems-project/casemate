#ifndef CASEMATE_ARCH_H
#define CASEMATE_ARCH_H

#include <casemate-impl/bitwise.h>

#define PAGE_SHIFT 12
#define PAGE_SIZE (1 << PAGE_SHIFT)

#define OFFSET_IN_PAGE(x) (((x)&BITMASK(PAGE_SHIFT - 1, 0)))
#define PAGE_ALIGN_DOWN(x) ((x) & ~BITMASK(PAGE_SHIFT - 1, 0))
#define PAGE_ALIGN(x) PAGE_ALIGN_DOWN(((x) + PAGE_SIZE - 1))
#define IS_PAGE_ALIGNED(x) (OFFSET_IN_PAGE(x) == 0)

#ifdef __AARCH64__

#define ARCH_READ_SYSREG(r) \
	({ \
		u64 reg; \
		asm volatile("mrs %[reg], " #r : [reg] "=r"(reg)); \
		reg; \
	})

#define ARCH_WRITE_SYSREG(r, v) \
	do { \
		asm volatile("msr " #r ", %[reg]" : : [reg] "r"(v)); \
	} while (0)

#ifdef CONFIG_MASK_INTERRUPTS
static inline u64 mask_interrupts(void)
{
	u64 flags = ARCH_READ_SYSREG(DAIF);
	asm volatile("msr daifset, #0b1111\n" // {D,A,I,F}=1
	);
	return flags;
}

static inline void restore_interrupts(u64 flags)
{
	ARCH_WRITE_SYSREG(DAIF, flags);
}
#endif

#endif /* __AARCH64__ */

#endif /* CASEMATE_ARCH_H */
