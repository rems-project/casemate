#include <casemate-impl.h>

#ifndef __KVM_NVHE_HYPERVISOR__
u64 strlen(const char *s) {
	u64 i = 0;

	while (*s != '\0') {
		s++;
		i++;
	}

	return i;
}
#endif /* __KVM_NVHE_HYPERVISOR__ */

bool streq(const char *s1, const char *s2) {
	if (*s1 == '\0')
		return *s2 == '\0';

	if (*s1 != *s2)
		return 0;

	return streq(s1 + 1, s2 + 1);
}
