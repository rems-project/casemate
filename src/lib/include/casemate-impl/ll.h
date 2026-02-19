#ifndef CASEMATE_LL_H
#define CASEMATE_LL_H

#include <casemate-impl/types.h>

/* opaque address converters, see state.h */
u64 virt2id(void *p);
void *id2virt(u64 id);

/**
 * Linked list with no pointers
 */
struct LL {
	u64 next;
	u64 prev;
};

static inline void ll_new(struct LL *ll)
{
	ll->next = 0;
	ll->prev = 0;
}

static inline void *ll_next(struct LL *el)
{
	if (el->next == 0)
		return NULL;

	return id2virt(el->next);
}

static inline struct LL *ll_prev(struct LL *el)
{
	return id2virt(el->prev);
}

/**
 * ll_head() - Return the first element in a list
 *
 * Returns NULL if the list is empty.
 */
static inline struct LL *ll_head(struct LL *hd)
{
	if (hd->next == 0)
		return NULL;

	return id2virt(hd->next);
}

/**
 * FOREACH_IN_LL - Iterate each element in a list
 */
#define FOREACH_IN_LL(VAR, LL) for (VAR = ll_head(LL); VAR; VAR = ll_next(VAR))

/**
 * ll_push() - Prepend a new entry to the linked list
 */
static inline void ll_push(struct LL *ll, struct LL *new_elem)
{
	struct LL *hd = ll_head(ll);

	new_elem->prev = virt2id(ll);

	if (hd) {
		new_elem->next = virt2id(hd);
		hd->prev = virt2id(new_elem);
	} else {
		new_elem->next = 0;
	}

	ll->next = virt2id(new_elem);
}

/**
 * ll_remove() - Removes a single entry from anywhere in a list
 */
static inline void ll_remove(struct LL *ll, struct LL *elem)
{
	struct LL *prev_elem = ll_prev(elem);
	struct LL *next_elem = ll_next(elem);

	prev_elem->next = elem->next;

	if (next_elem)
		next_elem->prev = elem->prev;
}

static inline bool ll_contains(struct LL *ll, struct LL *elem)
{
	struct LL *e;
	FOREACH_IN_LL(e, ll)
	{
		if (e == elem)
			return true;
	}

	return false;
}

#define offset_of(TY, FIELD) (u64)(&((TY *)(0))->FIELD)

#define container_of(TY, FIELD, VAL) (TY *)((u64)(VAL)-offset_of(TY, FIELD))

#endif /* CASEMATE_LL_H */
