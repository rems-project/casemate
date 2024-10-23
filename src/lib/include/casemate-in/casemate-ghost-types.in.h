/* Types also defined by UoC's pKVM ghost code headers
 * so do not try to include them in the top-level casemate.h if they are already defined
 */

#ifndef __KVM_NVHE_HYPERVISOR__

#include <stdarg.h>
#include <stdint.h>
#include <stdbool.h>

typedef unsigned long u64;
typedef signed long s64;
typedef unsigned int u32;
typedef signed int s32;
typedef int u8;
typedef u64 phys_addr_t;

#else

#include <linux/stdarg.h>
#include <linux/types.h>

#endif /* __KVM_NVHE_HYPERVISOR */
