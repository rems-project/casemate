#ifndef BITWISE_H
#define BITWISE_H

#ifndef CONFIG_HAS_BITWISE
#define BIT(I) (1UL << (I))
#define BITMASK(HI, LO) (((1UL << ((HI) - (LO) + 1)) - 1UL) << (LO))
#endif /* CONFIG_HAS_BITWISE */

#endif /* BITWISE_H */