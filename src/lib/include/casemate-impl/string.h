#ifndef CASEMATE_STRING_H
#define CASEMATE_STRING_H

#include <casemate-impl/types.h>

unsigned long strlen(const char *s);

bool streq(const char *s1, const char *s2);

void *memset(void *ptr, int value, unsigned long num);

#endif /* CASEMATE_STRING_H */
