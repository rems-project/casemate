#include <casemate-impl.h>
#include <casemate-impl/printer.h>

#pragma GCC diagnostic ignored "-Wunused-function"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"

#define MAX_PRINT_DIFF_PER_SUBFIELDS 16

/*
 * Ghost state diffs:
 * The ghost state is a tree,
 * and a diff is a tree with the same shape, but whose leaves are +- diffs.
 */

enum ghost_diff_kind {
	/**
	 * A pair that matched (no diff)
	 */
	GHOST_DIFF_NONE,

	/**
	 * A pair that didn't match.
	 */
	GHOST_DIFF_PAIR,

	/**
	 * An element that was or wasn't there.
	 */
	GHOST_DIFF_PM,
};

/*
 * I Hate C, so let's just wrap up the common values (u64, bool, char* etc)
 * so can write some half-generic functions.
 */
enum ghost_diff_val_kind {
	/* generic types, suitable as keys */
	Tu64,
	Tstr,

	/* other generic types */
	Tbool,

	/* A pair of a pointer and a callback to print it */
	Tgprint,
};

typedef int (*gp_print_cb)(void *arg, void *obj);
struct diff_val {
	enum ghost_diff_val_kind kind;
	union {
		bool b;
		u64 n;
		char *s;

		// this is okay to be a reference since the diff is only alive if the two diff'd objects are.
		struct gprint_data {
			gp_print_cb fn;
			void *obj;
	 	} gp;
	};
};
#define TBOOL(value) (struct diff_val){.kind=Tbool, .b=(value)}
#define TU64(value) (struct diff_val){.kind=Tu64, .n=(value)}
#define TSTR(value) (struct diff_val){.kind=Tstr, .s=(value)}
#define TGPRINT(f, value) (struct diff_val){.kind=Tgprint, .gp={.fn=(f), .obj=(value)}}
#define EMPTY_KEY TSTR(NULL)

struct ghost_diff {
	enum ghost_diff_kind kind;
	union {
		struct diff_pair_data {
			struct diff_val lhs;
			struct diff_val rhs;
		} pair;

		struct diff_pm_data {
			/**
			 * whether this is an addition or deletion...
			 */
			bool add;
			struct diff_val val;
		} pm;
	};
};

#define DIFF_NONE ((struct ghost_diff){.kind=GHOST_DIFF_NONE})
#define MAX_CONTAINER_PATH 32

struct diff_container {
	int depth;
	int clean_prefix;
	struct diff_val path[MAX_CONTAINER_PATH];
	bool saw_diff;
	u64 nr_subfield_diffs;
};

/*********/
// Differ

static int __put_val_string(struct diff_val val, char *buf)
{
	switch (val.kind) {
	case Tu64:
		return ghost_fprintf(buf, "%lx", val.n);
	case Tstr:
		return ghost_fprintf(buf, "%s", val.s);
	case Tbool:
		if (val.b)
			return ghost_fprintf(buf, "true");
		else
			return ghost_fprintf(buf, "false");
	case Tgprint:
		return val.gp.fn(buf, val.gp.obj);
	default:
		BUG();
	}
}

static bool val_equal(struct diff_val lhs, struct diff_val rhs)
{
	if (lhs.kind != rhs.kind)
		return false;

	switch (lhs.kind) {
	case Tbool:
		return lhs.b == rhs.b;
	case Tu64:
		return lhs.n == rhs.n;
	case Tstr:
		if (!lhs.s || !rhs.s)
			return lhs.s == rhs.s;
		else
			return streq(lhs.s, rhs.s);
	case Tgprint: {
		/* 256 should be long enough for any of our ghost-y prints.
		 * by construction */
		bool ret;
		char buf1[256];
		char buf2[256];
		char *s1 = side_effect()->sprint_create_buffer(buf1, 256);
		char *s2 = side_effect()->sprint_create_buffer(buf2, 256);
		int r1 = __put_val_string(lhs, s1);
		int r2 = __put_val_string(rhs, s2);
		if (r1 || r2) {
			ghost_assert(!r1 && !r2);
			return false;
		}
		ret = streq(buf1, buf2);
		side_effect()->sprint_destroy_buffer(s1);
		side_effect()->sprint_destroy_buffer(s2);
		return ret;
	}
	default:
		BUG();
	}
}

static void __put_val(struct diff_val val, u64 indent)
{
	switch (val.kind) {
	case Tu64:
		ghost_printf("%lx", val.n);
		break;
	case Tstr:
		ghost_printf("%s", val.s);
		break;
	case Tbool:
		if (val.b)
			ghost_printf("true");
		else
			ghost_printf("false");
		break;
	case Tgprint:
		val.gp.fn(NULL, val.gp.obj);
		break;
	default:
		BUG();
	}
}



static void __put_dirty_string(char *s, bool *dirty, bool negate)
{
	while (*s) {
		char c = *s++;
		bool d = *dirty++;

		if (!d)
			ghost_printf("%c", c);
		else if (negate)
			ghost_printf("%s%c%s", GHOST_WHITE_ON_MAGENTA, c, GHOST_NORMAL);
		else
			ghost_printf("%s%c%s", GHOST_WHITE_ON_GREEN, c, GHOST_NORMAL);
	}
}

#define GHOST_STRING_DUMP_LEN 256
static void __hyp_dump_string_diff(struct diff_container *node, struct diff_val lhs, struct diff_val rhs)
{
	char lhs_s[GHOST_STRING_DUMP_LEN] = {0};
	char rhs_s[GHOST_STRING_DUMP_LEN] = {0};
	bool dirty[GHOST_STRING_DUMP_LEN] = {false};

	char *lhs_buf = side_effect()->sprint_create_buffer(lhs_s, GHOST_STRING_DUMP_LEN);
	char *rhs_buf = side_effect()->sprint_create_buffer(rhs_s, GHOST_STRING_DUMP_LEN);

	__put_val_string(lhs, lhs_buf);
	__put_val_string(rhs, rhs_buf);

	side_effect()->sprint_destroy_buffer(lhs_buf);
	side_effect()->sprint_destroy_buffer(rhs_buf);


	// now, we find those that differ
	// TODO: do something more clever, and find inserted/removed text.
	//       so far, everything is constant-width and consistent so it's ok
	for (int i = 0; i < GHOST_STRING_DUMP_LEN; i++) {
		if (lhs_s[i] != rhs_s[i])
			dirty[i] = true;
	}

	ghost_printf("\n");
	ghost_print_indent(NULL, node->depth*4);
	ghost_printf("-");
	__put_dirty_string(lhs_s, dirty, true);

	ghost_printf("\n");
	ghost_print_indent(NULL, node->depth*4);
	ghost_printf("+");
	__put_dirty_string(rhs_s, dirty, false);
}

static void __ghost_print_diff(struct diff_container *node, struct ghost_diff *diff, u64 indent)
{
	switch (diff->kind) {
	case GHOST_DIFF_NONE:
		break;
	case GHOST_DIFF_PM:
		ghost_print_indent(NULL, node->depth*4);

		if (diff->pm.add)
			ghost_printf(GHOST_WHITE_ON_GREEN "+");
		else
			ghost_printf(GHOST_WHITE_ON_MAGENTA "-");

		__put_val(diff->pm.val, 0);

		ghost_printf(GHOST_NORMAL);
		break;
	case GHOST_DIFF_PAIR:
		__hyp_dump_string_diff(node, diff->pair.lhs, diff->pair.rhs);
		break;
	}
}

static int __put_key(struct diff_container *node, struct diff_val key)
{
	if (! val_equal(key, EMPTY_KEY)) {
		ghost_print_indent(NULL, node->depth*4);
		__put_val(key, 0);
		ghost_printf(":");

		/* the key is really just a transient node */
		node->depth++;
		return 1;
	} else {
		return 0;
	}
}

/**
 * Compare two Tval and if not equal, return a diff.
 */
static struct ghost_diff diff_pair(struct diff_val lhs, struct diff_val rhs)
{
	if (val_equal(lhs, rhs))
		return DIFF_NONE;

	return (struct ghost_diff){
		.kind = GHOST_DIFF_PAIR,
		.pair = (struct diff_pair_data){
			.lhs = lhs,
			.rhs = rhs,
		},
	};
}

static struct ghost_diff diff_pm(bool add, struct diff_val val)
{
	return (struct ghost_diff){
		.kind = GHOST_DIFF_PM,
		.pm = (struct diff_pm_data){
			.add = add,
			.val = val,
		},
	};
}

static void __attach(struct diff_container *node, struct diff_val key, struct ghost_diff diff)
{
	switch (diff.kind) {
	case GHOST_DIFF_NONE:
		break;
	default:
		node->nr_subfield_diffs++;

		// print out the part of the path we've not printed before.
		for (int i = node->clean_prefix; i < node->depth; i++) {
			ghost_print_indent(NULL, i*4);
			__put_val(node->path[i], 0);
			ghost_printf(":");
		};
		if (node->clean_prefix != node->depth && node->nr_subfield_diffs >= MAX_PRINT_DIFF_PER_SUBFIELDS)
			ghost_printf(GHOST_WHITE_ON_YELLOW "<skip diff>" GHOST_NORMAL "\n");

		node->clean_prefix = node->depth;
		node->saw_diff = true;

		if (node->nr_subfield_diffs < MAX_PRINT_DIFF_PER_SUBFIELDS) {
			int i = __put_key(node, key);
			__ghost_print_diff(node, &diff, 0);
			node->depth -= i;
		} else if (node->nr_subfield_diffs == MAX_PRINT_DIFF_PER_SUBFIELDS) {
			// only once, not too noisy...
			ghost_printf("\n");
			ghost_printf(GHOST_WHITE_ON_YELLOW "<skipping diffs>" GHOST_NORMAL "\n");
		}
	}
}

static void ghost_diff_enter_subfield_val(struct diff_container *container, struct diff_val name)
{
	container->path[container->depth++] = name;
}

static void ghost_diff_enter_subfield(struct diff_container *container, const char *name)
{
	container->path[container->depth++] = TSTR((char*)name);
}

static void ghost_diff_pop_subfield(struct diff_container *container)
{
	container->depth--;

	if (container->depth < container->clean_prefix)
		container->clean_prefix = container->depth;

	container->nr_subfield_diffs = 0;
}

static void ghost_diff_field(struct diff_container *container, char *key, struct ghost_diff child)
{
	__attach(container, TSTR(key), child);
}

static void ghost_diff_attach(struct diff_container *container, struct ghost_diff child)
{
	__attach(container, EMPTY_KEY, child);
}

/****************/
// Differ!

int gp_print_cm_loc(void *arg, struct sm_location *loc);
int gp_print_cm_blob_noindent(void *arg, struct casemate_memory_blob *b);

int gp_track_cm_loc(void *arg, struct sm_location *loc)
{
	TRY(ghost_fprintf(arg, "track "));
	return gp_track_cm_loc(arg, loc);
}

#define TSMLOC(LOC) TGPRINT((gp_print_cb)gp_print_cm_loc, (LOC))
#define TSMLOC_TRACK(LOC) TGPRINT((gp_print_cb)gp_track_cm_loc, (LOC))
#define TSMBLOB(BLOB) TGPRINT((gp_print_cb)gp_print_cm_blob_noindent, (BLOB))

static void one_way_diff_blob_slots(struct diff_container *container, struct casemate_memory_blob *b1, struct casemate_memory_blob *b2, bool add)
{
	bool saw_unclean = false;

	for (u64 i = 0; i < SLOTS_PER_PAGE; i++) {
		struct sm_location *loc1 = &b1->slots[i];
		struct sm_location *loc2 = &b2->slots[i];

		// only show the diffs if one side is unclean
		if (loc1->state.kind == STATE_PTE_INVALID_UNCLEAN || loc2->state.kind == STATE_PTE_INVALID_UNCLEAN) {
			if (loc1->is_pte && loc2->is_pte)
				ghost_diff_attach(container, diff_pair(TSMLOC(loc1), TSMLOC(loc2)));
			else if (loc1->is_pte)
				ghost_diff_attach(container, diff_pm(add, TSMLOC_TRACK(loc1)));
			else if (loc2->is_pte)
				ghost_diff_attach(container, diff_pm(!add, TSMLOC_TRACK(loc2)));
			saw_unclean = true;
		}
	}
}

static void one_way_diff_blobs(struct diff_container *container, struct casemate_model_memory *m1, struct casemate_model_memory *m2, bool add, bool skip_eq)
{
	bool found;
	for (u64 bi = 0; bi < m1->nr_allocated_blobs; bi++) {
		struct casemate_memory_blob *b1 = blob_of(m1, bi);
		struct casemate_memory_blob *b2 = find_blob(m2, b1->phys);

		if (b2) {
			found = true;

			// only in one direction should we try diff the blobs themselves
			if (!skip_eq) {
				one_way_diff_blob_slots(container, b1, b2, add);
			}
		} else if (!should_print_unclean_only() || blob_unclean(b1)) {
			ghost_diff_attach(container, diff_pm(add, TSMBLOB(b1)));
		}
	}
}

static void ghost_diff_sm_mem(struct diff_container *node, struct casemate_model_memory *m1, struct casemate_model_memory *m2)
{
	ghost_diff_enter_subfield(node, "mem");
	one_way_diff_blobs(node, m1, m2, false, false);
	one_way_diff_blobs(node, m2, m1, true, true);
	ghost_diff_pop_subfield(node);
}

static void one_way_diff_roots(struct diff_container *container, struct roots *lhs, struct roots *rhs, bool add)
{
	bool found;
	for (u64 i = 0; i < lhs->len; i++) {
		struct root *lhs_root = &lhs->roots[i];
		struct root *rhs_root = NULL;
		found = false;
		for (u64 j = 0; j < rhs->len; j++) {
			rhs_root = &lhs->roots[i];
			if (rhs_root->baddr == lhs_root->baddr)
				found = true;
		}

		// something was removed
		if (!found)
			ghost_diff_attach(container, diff_pm(add, TU64(lhs_root->baddr)));

		// ID was changed
		if (found && lhs_root->id != rhs_root->id) {
			ghost_diff_enter_subfield_val(container, TU64(lhs_root->baddr));
			ghost_diff_enter_subfield(container, "id");
			ghost_diff_attach(container, diff_pair(TU64(lhs_root->id), TU64(rhs_root->id)));
			ghost_diff_pop_subfield(container);
			ghost_diff_pop_subfield(container);
		}
	}
}

static void ghost_diff_sm_roots(struct diff_container *node, const char *name, struct roots *roots1, struct roots *roots2)
{
	ghost_diff_enter_subfield(node, name);
	// roots are unordered
	one_way_diff_roots(node, roots1, roots2, false);
	one_way_diff_roots(node, roots2, roots1, true);
	ghost_diff_pop_subfield(node);
}

static void ghost_diff_sm_state(struct diff_container *node, struct casemate_model_state *s1, struct casemate_model_state *s2)
{
	ghost_diff_field(node, "base", diff_pair(TU64(s1->base_addr), TU64(s2->base_addr)));
	ghost_diff_field(node, "size", diff_pair(TU64(s1->size), TU64(s2->size)));

	ghost_diff_sm_roots(node, "s1_roots", &s1->roots_s1, &s2->roots_s1);
	ghost_diff_sm_roots(node, "s2_roots", &s1->roots_s2, &s2->roots_s2);

	ghost_diff_sm_mem(node, &s1->memory, &s2->memory);
}

static struct diff_container container(void)
{
	struct diff_container n;
	n.depth = 0;
	n.clean_prefix = 0;
	n.saw_diff = false;
	n.nr_subfield_diffs = 0;
	return n;
}

void ghost_diff_and_print_sm_state(struct casemate_model_state *s1, struct casemate_model_state *s2)
{
	struct diff_container node = container();
	ghost_diff_sm_state(&node, s1, s2);
	if (!node.saw_diff)
		ghost_printf("<identical>");
}