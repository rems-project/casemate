#ifndef CASEMATE_PGTABLE_H
#define CASEMATE_PGTABLE_H

#include <casemate.h>

#include <casemate-impl/types.h>
#include <casemate-impl/bitwise.h>
#include <casemate-impl/state.h>

/*
 * Concrete masks, and field bitpatterns for a variety of PTE bits
 *
 * Key:
 *	PTE_FIELD_XYZ_LO is the bit index the field XYZ starts at
 *	PTE_FIELD_XYZ_LEN is the number of bits the field comprises.
 *	PTE_FIELD_XYZ_MASK is a mask where only the bits of field XYZ are set to 1.
 *	PTE_FIELD_XYZ_ABC is a PTE_FIELD_XYZ_LEN-length bitpattern corresponding to state ABC, of field XYZ.
 *
 *  PTE_FIELD_Sn_LVLm_... is one of the above, but only valid for Stage n at Level m
 *
 * Not all fields will define all variants (e.g. the _LEN is often implicit and not directly needed).
 */

#define PTE_FIELD_INVALID_00 0b00
#define PTE_FIELD_INVALID_10 0b10

#define PTE_FIELD_LVL012_BLOCK 0b01
#define PTE_FIELD_LVL012_TABLE 0b11

#define PTE_FIELD_LVL3_PAGE 0b11
#define PTE_FIELD_LVL3_RESERVED 0b01

#define PTE_FIELD_OWNER_ID_LO 2
#define PTE_FIELD_PKVM_OWNER_ID_HOST (PKVM_ID_HOST << PTE_FIELD_OWNER_ID_LO)
#define PTE_FIELD_PKVM_OWNER_ID_HYP (PKVM_ID_HYP << PTE_FIELD_OWNER_ID_LO)
#define PTE_FIELD_PKVM_OWNER_ID_GUEST (PKVM_ID_GUEST << PTE_FIELD_OWNER_ID_LO)

#define PTE_FIELD_UPPER_ATTRS_LO 59
#define PTE_FIELD_UPPER_ATTRS_MASK BITMASK(63, 50)

#define PTE_FIELD_LOWER_ATTRS_LO 2
#define PTE_FIELD_LOWER_ATTRS_MASK BITMASK(11, 2)

#define PTE_FIELD_ATTRS_MASK (PTE_FIELD_UPPER_ATTRS_MASK | PTE_FIELD_LOWER_ATTRS_MASK)

/* outside of realm security state, bit[55] is IGNORED, so can be used by software */
#define PTE_FIELD_UPPER_ATTRS_SW_LO 55
#define PTE_FIELD_UPPER_ATTRS_SW_MASK BITMASK(58, 55)

#define PTE_FIELD_TABLE_UPPER_IGNORED_MASK BITMASK(58, 51)
#define PTE_FIELD_TABLE_IGNORED_MASK \
	(PTE_FIELD_LOWER_ATTRS_MASK | PTE_FIELD_TABLE_UPPER_IGNORED_MASK)

#define PTE_FIELD_TABLE_NEXT_LEVEL_ADDR_MASK BITMASK(47, 12)

#define PTE_FIELD_S1_AP2_LO 7
#define PTE_FIELD_S1_AP2_MASK BIT(7)
#define PTE_FIELD_S1_AP2_READ_ONLY (1UL)
#define PTE_FIELD_S1_AP2_READ_WRITE (0UL)

#define PTE_FIELD_S1_AP1_LO 6
#define PTE_FIELD_S1_AP1_MASK BIT(6)

#define PTE_FIELD_S1_XN_LO 54
#define PTE_FIELD_S1_XN_MASK BIT(54)
#define PTE_FIELD_S1_XN_NOT_EXEC_NEVER (0UL)
#define PTE_FIELD_S1_XN_EXEC_NEVER (1UL)

#define PTE_FIELD_S1_ATTRINDX_LO 2
#define PTE_FIELD_S1_ATTRINDX_MASK BITMASK(4, 2)

#define PTE_FIELD_S2_S2AP10_LO 6
#define PTE_FIELD_S2_S2AP10_MASK BITMASK(7, 6)

#define PTE_FIELD_S2_S2AP0_LO 6
#define PTE_FIELD_S2_S2AP0_MASK BIT(6)
#define PTE_FIELD_S2_S2AP0_READABLE (1UL)
#define PTE_FIELD_S2_S2AP0_NOT_READABLE (0UL)

#define PTE_FIELD_S2_S2AP1_LO 7
#define PTE_FIELD_S2_S2AP1_MASK BIT(7)
#define PTE_FIELD_S2_S2AP1_WRITEABLE (1UL)
#define PTE_FIELD_S2_S2AP1_NOT_WRITEABLE (0UL)

#define PTE_FIELD_S2_XN_LO 53
#define PTE_FIELD_S2_XN_MASK BITMASK(54, 53)
/*
 * S2 XN is actually two bits encoding EL1 and EL0 execution separately.
 * but we assume they're either both allowed (00) or both forbidden (10)
 */
#define PTE_FIELD_S2_XN_NOT_EXEC_NEVER (0b00UL)
#define PTE_FIELD_S2_XN_EXEC_NEVER (0b10UL)

#define PTE_FIELD_S2_MEMATTR_LO 2
#define PTE_FIELD_S2_MEMATTR_MASK BITMASK(5, 2)

#define PTE_FIELD_S2_MEMATTR_DEVICE_nGnRE (0b0010UL)
#define PTE_FIELD_S2_MEMATTR_NORMAL_OUTER_INNER_WRITE_BACK_CACHEABLE (0b1111UL)

/**
 * PTE_EXTRACT() - Extract a PTE_FIELD from a value.
 *
 * e.g. PTE_EXTRACT(PTE_FIELD_S1_XN, 1 << PTE_FIELD_S1_XN_LO) == 1
 */
#define PTE_EXTRACT(FIELD_PREFIX, VAL) (((VAL)&FIELD_PREFIX##_MASK) >> FIELD_PREFIX##_LO)

static inline bool __s1_is_ro(u64 pte)
{
	return PTE_EXTRACT(PTE_FIELD_S1_AP2, pte) == PTE_FIELD_S1_AP2_READ_ONLY;
}
static inline bool __s1_is_xn(u64 pte)
{
	return PTE_EXTRACT(PTE_FIELD_S1_XN, pte) == PTE_FIELD_S1_XN_EXEC_NEVER;
}

static inline bool __s2_is_r(u64 pte)
{
	return PTE_EXTRACT(PTE_FIELD_S2_S2AP0, pte) == PTE_FIELD_S2_S2AP0_READABLE;
}
static inline bool __s2_is_w(u64 pte)
{
	return PTE_EXTRACT(PTE_FIELD_S2_S2AP1, pte) == PTE_FIELD_S2_S2AP1_WRITEABLE;
}
static inline bool __s2_is_xn(u64 pte)
{
	return PTE_EXTRACT(PTE_FIELD_S2_XN, pte) == PTE_FIELD_S2_XN_EXEC_NEVER;
}
static inline bool __s2_is_x(u64 pte)
{
	return PTE_EXTRACT(PTE_FIELD_S2_XN, pte) != PTE_FIELD_S2_XN_NOT_EXEC_NEVER;
}

typedef struct {
	bool present;
	u8 attrs[8];
} ghost_mair_t;

#define TCR_TG0_LO 14
#define TCR_TG0_WIDTH 2
#define TCR_TG0_MASK (BITMASK(TCR_TG0_WIDTH - 1, 0) << TCR_TG0_LO)

#define TCR_EL2_T0SZ_LO 0
#define TCR_EL2_T0SZ_WIDTH 6
#define TCR_EL2_T0SZ_MASK (BITMASK(TCR_EL2_T0SZ_WIDTH - 1, 0) << TCR_EL2_T0SZ_LO)

/* outside of realm security state, bit[55] is IGNORED, so can be used by software */
#define PTE_FIELD_UPPER_ATTRS_SW_LO 55
#define PTE_FIELD_UPPER_ATTRS_SW_MASK BITMASK(58, 55)

/* Technically, MemAttr is not a PTE field, but actually stored in the MAIR_ELx register, but whatever */
#define MEMATTR_LEN 8
#define MEMATTR_MASK BITMASK(7, 0)
#define EXTRACT_MEMATTR(MAIR, IDX) (((MAIR) >> ((IDX)*MEMATTR_LEN)) & MEMATTR_MASK)
#define MEMATTR_FIELD_DEVICE_nGnRE (0b00000100UL)
#define MEMATTR_FIELD_NORMAL_OUTER_INNER_WRITE_BACK_CACHEABLE (0b11111111)

static inline ghost_mair_t read_mair(u64 mair)
{
	ghost_mair_t attrs;
	attrs.present = true;

	for (int i = 0; i < 8; i++) {
		attrs.attrs[i] = EXTRACT_MEMATTR(mair, i);
	}

	return attrs;
}

static inline ghost_mair_t no_mair(void)
{
	return (ghost_mair_t){ .present = false };
}

/* Parsers from concrete to abstract */

#define GHOST_ATTR_MAX_LEVEL 3

/**
 * struct aal - Record of upper+lower attribute bits of a PTE at each level down the walk.
 */
struct aal {
	u64 attr_at_level[4];
};

#define DUMMY_AAL ((struct aal){ .attr_at_level = { 0 } })

#define TTBR_BADDR_MASK BITMASK(47, 1)
#define TTBR_ID_LO 48UL
#define TTBR_ID_MASK BITMASK(63, 48)

static inline phys_addr_t ttbr_extract_baddr(u64 vttb)
{
	return vttb & TTBR_BADDR_MASK;
}

static inline u64 ttbr_extract_id(u64 ttb)
{
	return (ttb & TTBR_ID_MASK) >> TTBR_ID_LO;
}

#define TLBI_PAGE_MASK BITMASK(43, 0)
#define TLBI_ASID_MASK BITMASK(63, 48)
#define TLBI_TTL_MASK BITMASK(47, 44)

bool is_desc_table(u64 descriptor, u64 level, entry_stage_t stage);
bool is_desc_valid(u64 descriptor);
u64 extract_output_address(u64 desc, u64 level);
u64 extract_table_address(u64 desc);
struct entry_exploded_descriptor deconstruct_pte(u64 partial_ia, u64 desc, u64 level,
						 entry_stage_t stage);
struct sm_pte_state initial_state(u64 partial_ia, u64 desc, u64 level, entry_stage_t stage);

struct pgtable_traverse_context {
	struct sm_location *loc;

	u64 descriptor;
	u64 level;
	bool leaf;

	struct entry_exploded_descriptor exploded_descriptor;

	u64 root;
	entry_stage_t stage;

	void *data;
};

enum pgtable_traversal_flag {
	READ_UNLOCKED_LOCATIONS,
	NO_READ_UNLOCKED_LOCATIONS,
};

typedef void (*pgtable_traverse_cb)(struct pgtable_traverse_context *ctxt);

void traverse_pgtable_from(u64 root, u64 table_start, u64 partial_ia, u64 level,
			   entry_stage_t stage, pgtable_traverse_cb visitor_cb,
			   enum pgtable_traversal_flag flag, void *data);
void traverse_pgtable(u64 root, entry_stage_t stage, pgtable_traverse_cb visitor_cb,
		      enum pgtable_traversal_flag flag, void *data);

void traverse_all_unclean_PTE(pgtable_traverse_cb visitor_cb, void *data, entry_stage_t stage);
void add_location_to_unclean_PTE(struct sm_location *loc);

struct pgtable_walk_result {
	u64 requested_pte;
	bool found;

	struct entry_exploded_descriptor descriptor;

	u64 root;
	entry_stage_t stage;

	u64 level;
};

struct pgtable_walk_result find_pte(struct sm_location *loc);

#endif /* CASEMATE_PGTABLE_H */
