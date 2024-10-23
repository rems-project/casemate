#include <errno.h>
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <casemate.h>
#include <casemate-impl.h>
#include <casemate-check-impl.h>

////////////////
// Parser buffer

struct parser {
	FILE *stream;
	bool at_EOF;

	bool has_lookahead;
	char lookahead_c;

	unsigned int line;
	unsigned int column;

	struct casemate_model_step *out;
};

#define parse_error(P, FMT, ...) \
	do { \
		fprintf(stderr, "! parse error at line%u col%u: " FMT "\n", (P)->line, (P)->column,##__VA_ARGS__); \
		assert(false); \
	} while (0)

int maybe_next(struct parser *p)
{
	int ret;

	if (p->at_EOF)
		return -1;

	if (p->has_lookahead) {
		char lk = p->lookahead_c;
		p->has_lookahead = false;
		return lk;
	}

	ret = fgetc(p->stream);

	if (feof(p->stream)) {
		p->at_EOF = true;
	} else if (ret < 0) {
		parse_error(p, "unexpected error, %d (%s)", errno, strerror(errno));
	}

	if ((char)ret == '\n') {
		p->column = 0;
		p->line++;
	} else {
		p->column++;
	}

	return ret;
}

char next(struct parser *p)
{
	int r = maybe_next(p);
	if (p->at_EOF)
		parse_error(p, "reached end of file unexpectedly");
	return (char)r;
}

int maybe_lookahead(struct parser *p)
{
	int ret;

	if (p->at_EOF)
		return -1;

	if (p->has_lookahead)
		return p->lookahead_c;

	ret = maybe_next(p);
	if (ret > 0) {
		p->lookahead_c = ret;
		p->has_lookahead = true;
	}

	return ret;
}

char lookahead(struct parser *p)
{
	int r = maybe_lookahead(p);
	if (p->at_EOF)
		parse_error(p, "reached end of file unexpectedly");
	return (char)r;
}

void acceptc(struct parser *p, char c)
{
	char n = next(p);
	if (n != c)
		parse_error(p, "expected '%c' but got '%c'", c, n);
}

void accept_EOF(struct parser *p)
{
	int r = maybe_next(p);
	if (! p->at_EOF)
		parse_error(p, "expected EOF, got '%c'", (char)r);
}


/////////
// Helpers

bool is_whitespace(char c)
{
	return (c == '\n' || c == ' ' || c == '\t');
}

bool is_bracket(char c)
{
	return (c == '(' || c == ')');
}

bool is_hex(char c)
{
	return (
		   ('0' <= c && c <= '9')
		|| ('a' <= c && c <= 'f')
		|| ('A' <= c && c <= 'F')
	);
}

int hexchar_to_i(char c)
{
	if ('0' <= c && c <= '9')
		return c - '0';
	else if ('a' <= c && c <= 'f')
		return (c - 'a') + 10;
	else if ('A' <= c && c <= 'F')
		return (c - 'A') + 10;
	assert(false);
}

int hextoi(const char *s, u64 *out)
{
	*out = 0;
	char c;

	while ((c = *s++)) {
		if (!is_hex(c))
			return -1;
		*out *= 16;
		*out += hexchar_to_i(c);
	}

	return 0;
}

void consume_whitespace(struct parser *p)
{
	int r;
	while ((r = maybe_lookahead(p)) > 0 && is_whitespace((char)r)) {
		next(p);
	}
}

void accept_open_bracket(struct parser *p)
{
	consume_whitespace(p);
	acceptc(p, '(');
	consume_whitespace(p);
}

void accept_close_bracket(struct parser *p)
{
	consume_whitespace(p);
	acceptc(p, ')');
	consume_whitespace(p);
}

void accept_close_bracket_if(struct parser *p, bool needs)
{
	consume_whitespace(p);
	if (needs)
		accept_close_bracket(p);
}

const char *next_word(struct parser *p)
{
	int i = 0;
	int buf_size = 512;
	char *buf;
	int r;
	char c;

	consume_whitespace(p);
	buf = malloc(buf_size);
	buf[i++] = next(p);
	do {
		r = maybe_lookahead(p);
		if (r < 0)
			break;

		c = (char)r;
		if (is_whitespace(c) || is_bracket(c))
			break;

		buf[i++] = next(p);

		if (i >= buf_size)
			parse_error(p, "word of unexpectedly long length");
	} while (1);
	buf[i] = '\0';
	TRACE("consumed word '%s'", buf);
	consume_whitespace(p);
	return buf;
}

void accept_word(struct parser *p, const char *key)
{
	consume_whitespace(p);
	const char *word = next_word(p);
	if (! streq(word, key))
		parse_error(p, "unexpected word, expected '%s' but got %s'\n", key, word);
	consume_whitespace(p);
}

u64 next_hex(struct parser *p)
{
	int r;
	u64 h;
	const char *word;
	acceptc(p, '0');
	acceptc(p, 'x');
	word = next_word(p);
	r = hextoi(word, &h);
	if (r < 0)
		parse_error(p, "expected hex integer, but got '%s'", word);
	free((void*)word);
	return h;
}

u64 next_decimal(struct parser *p)
{
	u64 r;
	const char *word;
	word = next_word(p);
	r = atoi(word);
	free((void*)word);
	return r;
}

struct enum_map_entry {
	const char *key;
	const int val;
};

struct enum_map {
	int count;
	const char *name;
	struct enum_map_entry entries[];
};

int next_enum(struct parser *p, struct enum_map *map)
{
	const char *word = next_word(p);

	for (int i = 0; i < map->count; i++) {
		if (streq(word, map->entries[i].key))
			return map->entries[i].val;
	}

	parse_error(p, "unexpected word '%s', expected a %s", word, map->name);
}

//////////
// Parsers

bool parse_kv_or_v_head(struct parser *p, const char *k)
{
	if (lookahead(p) == '(') {
		accept_open_bracket(p);
		accept_word(p, k);
		return true;
	} else {
		return false;
	}
}

#define PARSE_KV_WITH(P, KEY, TY, FN, ...) \
	({ \
		TY r; \
		bool needs_close; \
		needs_close = parse_kv_or_v_head(P, KEY); \
		r = FN(P, ##__VA_ARGS__); \
		accept_close_bracket_if(P, needs_close); \
		r; \
	})

#define PARSE_KV_DECIMAL(P, KEY) \
	PARSE_KV_WITH(P, KEY, u64, next_decimal)

#define PARSE_KV_HEX(P, KEY) \
	PARSE_KV_WITH(P, KEY, u64, next_hex)

#define PARSE_KV_WORD(P, KEY) \
	PARSE_KV_WITH(P, KEY, const char*, next_word)

#define PARSE_KV_ENUM(P, KEY, MAP) \
	PARSE_KV_WITH(P, KEY, int, next_enum, &(MAP))


void parse_common_fields(struct parser *p)
{
	p->out->seq_id = PARSE_KV_DECIMAL(p, "id");
	p->out->tid = PARSE_KV_DECIMAL(p, "tid");
}

struct enum_map memory_orders_map = {
	.count = 2,
	.name = "memory_order",
	.entries = {
		{"plain", WMO_plain},
		{"release", WMO_release},
	},
};

void parse_mem_write_tail(struct parser *p)
{
	p->out->hw_step.write_data.mo = PARSE_KV_ENUM(p, "mem-order", memory_orders_map);
	p->out->hw_step.write_data.phys_addr = PARSE_KV_HEX(p, "address");
	p->out->hw_step.write_data.val = PARSE_KV_HEX(p, "value");
}

void parse_mem_read_tail(struct parser *p)
{
	p->out->hw_step.read_data.phys_addr = PARSE_KV_HEX(p, "address");
	p->out->hw_step.read_data.val = PARSE_KV_HEX(p, "value");
}

void parse_mem_init_tail(struct parser *p)
{
	p->out->abs_step.init_data.location = PARSE_KV_HEX(p, "address");
	p->out->abs_step.init_data.size = PARSE_KV_HEX(p, "size");
}

void parse_mem_set_tail(struct parser *p)
{
	p->out->abs_step.memset_data.address = PARSE_KV_HEX(p, "address");
	p->out->abs_step.memset_data.size = PARSE_KV_HEX(p, "size");
	p->out->abs_step.memset_data.value = PARSE_KV_HEX(p, "value");
}

struct enum_map barrier_map = {
	.count = 2,
	.name = "barrier_kind",
	.entries = {
		{"dsb", BARRIER_DSB},
		{"isb", BARRIER_ISB},
	},
};

#define DXB_KIND(K) {#K, DxB_##K}
struct enum_map barrier_dxb_map = {
	.count = 3,
	.name = "barrier_dxb_kind",
	.entries = {
		DXB_KIND(nsh),
		DXB_KIND(ish),
		DXB_KIND(ishst),
	},
};

void parse_barrier_tail(struct parser *p)
{
	p->out->hw_step.barrier_data.kind = next_enum(p, &barrier_map);

	if (p->out->hw_step.barrier_data.kind == BARRIER_DSB) {
		p->out->hw_step.barrier_data.dxb_data = PARSE_KV_ENUM(p, "kind", barrier_dxb_map);
	}
}

#define TLBI_ENTRY(k) {#k, TLBI_##k}
struct enum_map tlbi_map = {
	.count = 6,
	.name = "tlbi_kind",
	.entries = {
		TLBI_ENTRY(vmalls12e1),
		TLBI_ENTRY(vmalls12e1is),
		TLBI_ENTRY(vmalle1is),
		TLBI_ENTRY(alle1is),
		// TLBI_ENTRY(vae2),
		TLBI_ENTRY(vae2is),
		TLBI_ENTRY(ipas2e1is),
	},
};

void parse_tlbi_tail(struct parser *p)
{
	p->out->hw_step.tlbi_data.tlbi_kind = next_enum(p, &tlbi_map);
	switch (p->out->hw_step.tlbi_data.tlbi_kind) {
	case TLBI_vmalls12e1:
	case TLBI_vmalls12e1is:
	case TLBI_vmalle1is:
	case TLBI_alle1is:
		break;

	case TLBI_ipas2e1is:
	case TLBI_vale2is:
	case TLBI_vae2is:
		p->out->hw_step.tlbi_data.page = PARSE_KV_HEX(p, "addr");
		p->out->hw_step.tlbi_data.level = PARSE_KV_DECIMAL(p, "level");
		break;

	default:
		assert(false);
	}
}

struct enum_map sysreg_map = {
	.count = 2,
	.name = "sysreg",
	.entries = {
		{"vttbr_el2", SYSREG_VTTBR},
		{"ttbr0_el2", SYSREG_TTBR_EL2},
	},
};

void parse_sysreg_write_tail(struct parser *p)
{
	p->out->hw_step.msr_data.sysreg = PARSE_KV_ENUM(p, "sysreg", sysreg_map);
	p->out->hw_step.msr_data.val = PARSE_KV_HEX(p, "value");
}

struct enum_map hint_map = {
	.count = 4,
	.name = "hint",
	.entries = {
		{"set_root_lock", GHOST_HINT_SET_ROOT_LOCK},
		{"set_owner_root", GHOST_HINT_SET_OWNER_ROOT},
		{"release", GHOST_HINT_RELEASE_TABLE},
		{"set_pte_thread_owner", GHOST_HINT_SET_PTE_THREAD_OWNER},
	},
};

void parse_hint_tail(struct parser *p)
{
	p->out->hint_step.kind = PARSE_KV_ENUM(p, "kind", hint_map);
	p->out->hint_step.location = PARSE_KV_HEX(p, "location");
	p->out->hint_step.value = PARSE_KV_HEX(p, "value");
}

void parse_lock_tail(struct parser *p)
{
	p->out->abs_step.lock_data.address = PARSE_KV_HEX(p, "address");
}

void parse_common_fields_tail(struct parser *p)
{
	// TODO: BS: parse srclocs
	p->out->src_loc.file = PARSE_KV_WORD(p, "src");
	p->out->src_loc.func = "";
	p->out->src_loc.lineno = 0;
}

void parse_trans(struct parser *p)
{
	const char *prefix;
	accept_open_bracket(p);

	prefix = next_word(p);
	parse_common_fields(p);

	if (streq(prefix, "mem-write")) {
		p->out->kind = TRANS_HW_STEP;
		p->out->hw_step.kind = HW_MEM_WRITE;
		parse_mem_write_tail(p);
	} else if (streq(prefix, "mem-read")) {
		p->out->kind = TRANS_HW_STEP;
		p->out->hw_step.kind = HW_MEM_READ;
		parse_mem_read_tail(p);
	} else if (streq(prefix, "mem-init")) {
		p->out->kind = TRANS_ABS_STEP;
		p->out->abs_step.kind = GHOST_ABS_INIT;
		parse_mem_init_tail(p);
	} else if (streq(prefix, "mem-set")) {
		p->out->kind = TRANS_ABS_STEP;
		p->out->abs_step.kind = GHOST_ABS_MEMSET;
		parse_mem_set_tail(p);
	} else if (streq(prefix, "sysreg-write")) {
		p->out->kind = TRANS_HW_STEP;
		p->out->hw_step.kind = HW_MSR;
		parse_sysreg_write_tail(p);
	} else if (streq(prefix, "barrier")) {
		p->out->kind = TRANS_HW_STEP;
		p->out->hw_step.kind = HW_BARRIER;
		parse_barrier_tail(p);
	} else if (streq(prefix, "tlbi")) {
		p->out->kind = TRANS_HW_STEP;
		p->out->hw_step.kind = HW_TLBI;
		parse_tlbi_tail(p);
	} else if (streq(prefix, "hint")) {
		p->out->kind = TRANS_HINT;
		parse_hint_tail(p);
	} else if (streq(prefix, "lock")) {
		p->out->kind = TRANS_ABS_STEP;
		p->out->abs_step.kind = GHOST_ABS_LOCK;
		parse_lock_tail(p);
	} else if (streq(prefix, "unlock")) {
		p->out->kind = TRANS_ABS_STEP;
		p->out->abs_step.kind = GHOST_ABS_UNLOCK;
		parse_lock_tail(p);
	}
	parse_common_fields_tail(p);
	accept_close_bracket(p);
}

//////////
// Top-level API

void *make_parser(FILE *f, struct casemate_model_step *step)
{
	struct parser *p = malloc(sizeof(struct parser));
	p->stream = f;
	p->at_EOF = false;
	p->has_lookahead = false;
	p->line = 0;
	p->column = 0;
	p->lookahead_c = '\0';
	p->out = step;
	return (void*)p;
}

bool parser_at_EOF(void *arg)
{
	struct parser *p = (struct parser *)arg;
	consume_whitespace(p);
	maybe_lookahead(p);
	return p->at_EOF;
}

bool parser_at_exclamation(void *arg)
{
	int r;
	struct parser *p = (struct parser *)arg;
	consume_whitespace(p);

	r = maybe_lookahead(p);
	if (r < 0)
		return false;

	return (char)r == '!';
}

void parse_record(void *p)
{
	parse_trans((struct parser *)p);
}