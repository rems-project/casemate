#include <casemate-impl.h>

#ifndef CONFIG_HAS_STRLEN
u64 strlen(const char *s)
{
	u64 i = 0;

	while (*s != '\0') {
		s++;
		i++;
	}

	return i;
}
#endif /* CONFIG_HAS_STRLEN */

bool streq(const char *s1, const char *s2)
{
	if (*s1 == '\0')
		return *s2 == '\0';

	if (*s1 != *s2)
		return 0;

	return streq(s1 + 1, s2 + 1);
}

#ifndef CONFIG_HAS_MEMCPY
void *memcpy(void *dest, const void *src, u64 num)
{
	u64 i;
	unsigned char *bs = (unsigned char *)src;
	unsigned char *bd = (unsigned char *)dest;
	for (i = 0; i < num; i++) {
		bd[i] = bs[i];
	}
	return dest;
}
#endif /* CONFIG_HAS_MEMCPY */

#ifndef CONFIG_HAS_MEMSET
void *memset(void *ptr, int value, u64 num)
{
	u64 i;
	unsigned char *dest = (unsigned char *)ptr;
	for (i = 0; i < num; i++) {
		dest[i] = value;
	}
	return ptr;
}
#endif /* CONFIG_HAS_MEMCPY */
