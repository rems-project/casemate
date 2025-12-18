#ifndef CASEMATE_H
#define CASEMATE_H

#ifdef __KVM_NVHE_HYPERVISOR__
#include <linux/stdarg.h>
#include <linux/types.h>
#elif defined(__CASEMATE_FREEBSD__)
#include <sys/stdarg.h>
#include <sys/stdint.h>
#include <sys/stdatomic.h>
#else
#include <stdarg.h>
#include <stdint.h>
#include <stdbool.h>
#endif

/*
 * Casemate public interface
 */

#define CASEMATE_VERSION "CASEMATE_VERSION_H"

/* auto-included by Makefile */
CASEMATE_CONFIG_H

/* auto-included by Makefile */
CASEMATE_TRANSITIONS_H

#endif /* CASEMATE_H */