#ifndef CASEMATE_PRINT_H
#define CASEMATE_PRINT_H

#include <casemate-impl/types.h>

#ifndef CONFIG_LINUX
#define GHOST_WHITE_ON_BLACK "\033[40;37;1m"
#define GHOST_WHITE_ON_RED "\033[41;37;1m"
#define GHOST_WHITE_ON_GREEN "\033[42;37;1m"
#define GHOST_WHITE_ON_YELLOW "\033[43;37;1m"
#define GHOST_WHITE_ON_BLUE "\033[44;37;1m"
#define GHOST_WHITE_ON_MAGENTA "\033[45;37;1m"
#define GHOST_WHITE_ON_CYAN "\033[46;37;1m"
#define GHOST_NORMAL "\033[0m"
#endif /* CONFIG_LINUX */

#ifndef CONFIG_HAS_PRINTF
int ghost_printf(const char *fmt, ...);
#endif

/**
 * ghost_fprintf() - fprintf-like function that uses the ghost driver.
 */
int ghost_fprintf(void *arg, const char *fmt, ...);

/**
 * ghost_print_indent() - Insert an indent.
 */
int ghost_print_indent(void *arg, u64 n);

////////////////////////////
// String builder

struct string_builder {
	char *out;
	char *cur;
	u64 rem;
};

#define DEFINE_STRING_BUFFER(VAR, LEN) \
	char __##VAR##__buf[LEN] = { 0 }; \
	struct string_builder VAR = { .out = __##VAR##__buf, .cur = __##VAR##__buf, .rem = LEN }

int sb_putc(struct string_builder *buf, const char c);
int sb_puts(struct string_builder *buf, const char *s);
int sb_putbool(struct string_builder *buf, const bool b);
int sb_putn(struct string_builder *buf, u64 n);
int sb_putd(struct string_builder *buf, s64 n);
int sb_putx(struct string_builder *buf, u32 x);
int sb_putxn(struct string_builder *buf, u64 x, u32 n);

#define TRY(X) \
	do { \
		int __ret = (X); \
		if (__ret) \
			return __ret; \
	} while (0)

#define TRY_PUT(c) TRY(sb_putc(buf, (c)))

#define TRY_PUTS(s) TRY(sb_puts(buf, (s)))

#define TRY_PUTn(n) TRY(sb_putn(buf, (n)))

#define TRY_PUTd(d) TRY(sb_putd(buf, (d)))

#define TRY_PUTxn(x, n) TRY(sb_putxn(buf, (x), (n)))

#define TRY_PUT_KV(k, v) \
	do { \
		if (! should_trace_condensed()) { \
			TRY_PUT('('); \
			TRY(sb_puts(buf, (k))); \
			TRY_PUT(' '); \
		} \
		TRY((v)); \
		if (! should_trace_condensed()) { \
			TRY_PUT(')'); \
		} \
	} while (0)

void put_trans(void *arg);
#define GHOST_transprinter put_trans

#endif /* CASEMATE_PRINT_H */