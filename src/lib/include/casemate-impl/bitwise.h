#ifndef BITWISE_H
#define BITWISE_H

#include <casemate-impl/types.h>

#ifndef CONFIG_HAS_BITWISE
#define BIT(I) (U64_C(1) << (I))
#define BITMASK(HI, LO) (((U64_C(1) << ((HI) - (LO) + 1)) - U64_C(1)) << (LO))
#endif /* CONFIG_HAS_BITWISE */

/* align to a power of 2 boundary */
#define ALIGN_UP_TO(V, A) (V) + (((A)-1) & (1 + ((V) ^ -1)))

#define BITS_SET(V, MASK) (((V) & (MASK)) == (MASK))

#endif /* BITWISE_H */
