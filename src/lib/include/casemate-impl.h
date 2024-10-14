#ifndef CASEMATE_IMPL_H
#define CASEMATE_IMPL_H

/* the implementation should not need this! */
#define GHOST_CPU_ID 0

/* grab public API */
#include <casemate.h>

/* grab internal APIs */
#include <casemate-impl/types.h>
#include <casemate-impl/string.h>

#include <casemate-impl/bitwise.h>
#include <casemate-impl/asserts.h>
#include <casemate-impl/dummy_macros.h>

#include <casemate-impl/printer.h>
#include <casemate-impl/options.h>

#include <casemate-impl/sync.h>
#include <casemate-impl/memcpy.h>
#include <casemate-impl/arch.h>
#include <casemate-impl/pgtable.h>

#include <casemate-impl/model.h>

#endif /* CASEMATE_IMPL_H */