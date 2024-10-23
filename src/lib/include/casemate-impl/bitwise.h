#ifndef BITWISE_H
#define BITWISE_H

#ifndef __KVM_NVHE_HYPERVISOR__
#define BIT(I) (1UL << (I))
#define GENMASK(L, S) (((1UL << (L)) - 1UL) << (S))
#else
#include <linux/bits.h>
#endif

#endif /* BITWISE_H */