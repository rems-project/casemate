#include <stdarg.h>

#include <casemate-impl.h>


/////////
// String builder

int sb_putc(struct string_builder *buf, const char c)
{
	if (buf->rem == 0) {
		return -1;
	}

	buf->rem--;
	*buf->cur++ = c;
	return 0;
}

int sb_puts(struct string_builder *buf, const char *s)
{
	while (*s)
		TRY_PUT(*s++);

	return 0;
}

int sb_putbool(struct string_builder *buf, const bool b)
{
	if (b) {
		TRY_PUTS("true");
	} else {
		TRY_PUTS("false");
	}
	return 0;
}

int sb_putn(struct string_builder *buf, u64 n)
{
	char digits[20] = {0};
	int i = 0;

	do {
		digits[i] = (n % 10) + '0';
		n /= 10;
		i++;
	} while (n > 0);

	i--;

	do {
		TRY_PUT(digits[i]);
	} while (i--);

	return 0;
}

int sb_putd(struct string_builder *buf, s64 n)
{
	bool negative = false;

	if (n < 0) {
		negative = true;
		n = -n;
	}

	char digits[20] = {0};
	int i = 0;

	do {
		digits[i] = (n % 10) + '0';
		n /= 10;
		i++;
	} while (n > 0);

	i--;

	if (negative)
		TRY_PUT('-');

	do {
		TRY_PUT(digits[i]);
	} while (i--);

	return 0;
}

int sb_putx(struct string_builder *buf, u32 x)
{
	x &= 0xf;
	if (x <= 9)
		x += '0';
	else
		x += ('a' - 0xa);

	TRY_PUT(x);
	return 0;
}

int sb_putxn(struct string_builder *buf, u64 x, u32 n)
{
	int i = n >> 2;

	// always prefix hex with 0x
	TRY_PUT('0');
	TRY_PUT('x');

	while (i--) {
		/*
		 * skip leading 0s
		 */
		if (i == 0 || (x >> (4 * i)) != 0)
			TRY(sb_putx(buf, (x >> (4 * i)) & 0xf));
	}
	return 0;
}


//////////
// Printf

int ghost_printf(void *arg, const char *fmt, ...)
{
	int ret;
	va_list ap;
	va_start(ap, fmt);
	ret = side_effect()->print(arg, fmt, ap);
	va_end(ap);

	/* instead of returning error codes, really just fail,
	 * as no recovery on printing to UART. */
	if (ret)
		BUG();

	return ret;
}

int ghost_print_indent(void *arg, u64 n)
{
	for (u64 i = 0; i < n; i++)
		TRY(ghost_printf(arg, " "));
	return 0;
}

////////////////////////////
// Trace points

#pragma GCC diagnostic ignored "-Wunused-variable"

#define ID_STRING(x) [x]=#x
static const char *automaton_state_names[] = {
	ID_STRING(STATE_PTE_VALID),
	ID_STRING(STATE_PTE_INVALID_UNCLEAN),
	ID_STRING(STATE_PTE_INVALID),
	ID_STRING(STATE_PTE_NOT_WRITABLE)
};

static const char *pte_kind_names[] = {
	ID_STRING(PTE_KIND_TABLE),
	ID_STRING(PTE_KIND_MAP),
	ID_STRING(PTE_KIND_INVALID),
};

static const int KIND_PREFIX_LEN = 2;
static const char* KIND_PREFIX_NAMES[] = {
	[STATE_PTE_INVALID] = "I ",
	[STATE_PTE_INVALID_UNCLEAN] = "IU",
	[STATE_PTE_VALID] = "V ",
	[STATE_PTE_NOT_WRITABLE] = "NW",
};

static const int LIS_NAME_LEN = 2;
static const char* LIS_NAMES[] = {
	[LIS_unguarded] = "n ",
	[LIS_dsbed] = "d ",
	[LIS_dsb_tlbi_ipa] = "ti",
	[LIS_dsb_tlbi_ipa_dsb] = "td",
	[LIS_dsb_tlbied] = "ta",
};


// TODO: invalidator_tid will only be 1 char as MAX_CPU is 4, maybe this could be less fragile.
static const int INVALIDATOR_TID_NAME_LEN = 1;

// output needs to be long enough for at least "{prefix} {LIS} {INVALIDATOR_THREAD}"
static const int PTE_STATE_LEN = KIND_PREFIX_LEN + 1 + LIS_NAME_LEN + 1 + INVALIDATOR_TID_NAME_LEN;

#define TRY_INDENT(ARG, INDENT) \
	TRY(ghost_print_indent(ARG, INDENT))

// Printers for sm state
int gp_print_cm_pte_state(void *arg, struct sm_pte_state *st)
{
	const char *prefix = KIND_PREFIX_NAMES[st->kind];

	TRY(ghost_printf(arg, "%s", prefix));

	switch (st->kind) {
	case STATE_PTE_INVALID:
		TRY_INDENT(arg, PTE_STATE_LEN - KIND_PREFIX_LEN - INVALIDATOR_TID_NAME_LEN);
		return ghost_printf(arg, "%d", st->invalid_clean_state.invalidator_tid);
	case STATE_PTE_INVALID_UNCLEAN:
		TRY_INDENT(arg, PTE_STATE_LEN - KIND_PREFIX_LEN - LIS_NAME_LEN - 1 - INVALIDATOR_TID_NAME_LEN);
		return ghost_printf(arg, "%s %d", LIS_NAMES[st->invalid_unclean_state.lis], st->invalid_unclean_state.invalidator_tid);
	case STATE_PTE_VALID:
		TRY_INDENT(arg, PTE_STATE_LEN - KIND_PREFIX_LEN);
		return 0;
	case STATE_PTE_NOT_WRITABLE:
		TRY_INDENT(arg, PTE_STATE_LEN - KIND_PREFIX_LEN - LIS_NAME_LEN - 1 - INVALIDATOR_TID_NAME_LEN);
		return ghost_printf(arg, "%s%I%s %d", LIS_NAMES[st->invalid_unclean_state.lis], st->invalid_unclean_state.invalidator_tid);
	}
}

int gp_print_cm_loc(void *arg, struct sm_location *loc)
{
	char *init = loc->initialised ? "*" : "!";

	if (loc->is_pte) {
		u64 start = loc->descriptor.ia_region.range_start;
		u64 end = loc->descriptor.ia_region.range_size + start;

		TRY(ghost_printf(arg, "%s[%16p]=%16lx (pte_st:", init, loc->phys_addr, loc->val));
		TRY(gp_print_cm_pte_state(arg, &loc->state));
		TRY(ghost_printf(arg, " root:%16p, range:%16lx-%16lx)", loc->owner, start, end));
		return 0;
	} else {
		return ghost_printf(arg, "%s[%16p]=%16lx", init, loc->phys_addr, loc->val);
	}

}

int gp_print_cm_blob_info(void *arg, struct ghost_memory_blob *b)
{
	if (b->valid) {
		int tracked = 0;
		int invalid = 0;
		int invalid_unclean = 0;

		for (u64 i = 0; i < SLOTS_PER_PAGE; i++) {
			struct sm_location *loc = &b->slots[i];
			// only show those that are ptes we're tracking
			if (!loc->is_pte)
				continue;
			++tracked;
			if (loc->state.kind == STATE_PTE_INVALID)
				invalid++;
			else if (loc->state.kind == STATE_PTE_INVALID_UNCLEAN)
				invalid_unclean++;
		}

		return ghost_printf(arg, "<blob %16p->%16p, %d tracked, %d invalid (clean), %d invalid (unclean)>", b->phys, b->phys + BLOB_SIZE, tracked, invalid, invalid_unclean);
	} else {
		return ghost_printf(arg, "<invalid blob>");
	}
}

int gp_print_cm_blob(void *arg, struct ghost_memory_blob *b, u64 indent)
{
	int ret;

	if (should_print_unclean_only() && !blob_unclean(b))
		return 0;

	if (!b->valid)
		return ghost_printf(arg, "<invalid blob>");

	TRY(ghost_printf(arg, "\n"));
	TRY(ghost_print_indent(arg, indent));
	TRY(gp_print_cm_blob_info(arg, b));

	for (u64 i = 0; i < SLOTS_PER_PAGE; i++) {
		struct sm_location *loc = &b->slots[i];
		// only show those that are ptes we're tracking
		if (!loc->is_pte)
			continue;

		// don't waste energy printing 'clean' entries...
		if (!should_print_unclean_only() || loc->state.kind == STATE_PTE_INVALID_UNCLEAN) {
			TRY(ghost_printf(arg, "\n"));
			TRY(ghost_print_indent(arg, indent+2));
			TRY(gp_print_cm_loc(arg, loc));
		}
	}

	return 0;
}

int gp_print_cm_blob_noindent(void *arg, struct ghost_memory_blob *b)
{
	return gp_print_cm_blob(arg, b, 0);
}


int gp_print_cm_mem(void *arg, struct casemate_model_memory *mem)
{
	int ret;
	bool empty = true;

	ret = ghost_printf(arg, "mem:");
	if (ret)
		return ret;

	for (int bi = 0; bi < mem->nr_allocated_blobs; bi++) {
		struct ghost_memory_blob *b = blob_of(mem, bi);

		if (!should_print_unclean_only() || blob_unclean(b))
			empty = false;

		ret = gp_print_cm_blob_noindent(arg, b);
		if (ret)
			return ret;
	}

	if (empty) {
		TRY(ghost_printf(arg, "\n"));
		ret = ghost_printf(arg, "<clean>");
		if (ret)
			return ret;
	}

	return 0;
}

int gp_print_cm_roots(void *arg, char *name, u64 len, u64 *roots)
{
	int ret;

	ret = ghost_printf(arg, "%s roots: [", name);
	if (ret)
		return ret;

	if (len > 0) {
		ret = ghost_printf(arg, "%16p", roots[0]);
		if (ret)
			return ret;

		for (u64 i = 1; i < len; i++) {
			ret = ghost_printf(arg, ", %16p", roots[i]);
			if (ret)
				return ret;
		}
	}

	return ghost_printf(arg, "]");
}

int gp_print_cm_lock(void *arg, struct lock_owner_map *locks, int i)
{
	int ret;
#ifndef CONFIG_NVHE_casemate_model_LOG_ONLY
	struct lock_state *state;
#endif /* CONFIG_NVHE_casemate_model_LOG_ONLY */

#ifndef CONFIG_NVHE_casemate_model_LOG_ONLY
	if (is_correctly_locked(locks->locks[i], &state))
		ret = ghost_printf(arg, "(%16p,%16p, locked by thread %d, %s)", locks->owner_ids[i], locks->locks[i], state->id, state->write_authorization == AUTHORIZED ? "write authorized" : "write not authorized");
	else
#endif /* CONFIG_NVHE_casemate_model_LOG_ONLY */
		ret = ghost_printf(arg, "(%16p,%16p)", locks->owner_ids[i], locks->locks[i]);

	return ret;
}

int gp_print_cm_locks(void *arg, struct lock_owner_map *locks)
{
	int ret;
	ret = ghost_printf(arg, "%s", "locks: [");
	if (ret)
		return ret;

	if (locks->len > 0) {
	ret = gp_print_cm_lock(arg, locks, 0);
		for (u64 i = 1; i < locks->len; i++) {
			ret = ghost_printf(arg,", ");
			ret = gp_print_cm_lock(arg, locks, i);
		}
	}

	return ghost_printf(arg, "]");
}

int ghost_dump_model_state(void *arg, struct casemate_model_state *s)
{
	TRY(ghost_printf(
		arg,
		""
		"base_addr:.......%16p\n"
		"size:............%16lx\n"
		"nr_s1_roots:.....%16lx\n"
		"nr_s2_roots:.....%16lx\n",
		s->base_addr,
		s->size,
		s->nr_s1_roots,
		s->nr_s2_roots
	));
	TRY(gp_print_cm_roots(arg, "s1", s->nr_s1_roots, s->s1_roots));
	TRY(ghost_printf(arg, "\n"));
	TRY(gp_print_cm_roots(arg, "s2", s->nr_s2_roots, s->s2_roots));
	TRY(ghost_printf(arg, "\n"));
	TRY(gp_print_cm_locks(arg, &s->locks));
	TRY(ghost_printf(arg, "\n"));
	TRY(gp_print_cm_mem(arg, &s->memory));
	return 0;
}