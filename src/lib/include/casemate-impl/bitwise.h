#ifndef BITWISE_H
#define BITWISE_H

#ifndef __KVM_NVHE_HYPERVISOR__
#define BIT(I) (1UL << (I))
#define BITMASK(HI, LO) (((1UL << ((HI) - (LO) + 1)) - 1UL) << (LO))
#else
#include <linux/bits.h>
#define BITMASK(HI, LO) GENMASK(HI, LO)
#endif

#endif /* BITWISE_H */