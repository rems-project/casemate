/* Shared types with ghost */

/**
 * enum ghost_stage - (optional) stage of translation
 */
typedef enum {
	GHOST_STAGE2 = 2,
	GHOST_STAGE1 = 1,

	/**
	 * @GHOST_STAGE_NONE: for memblocks and other non-pgtable mappings.
	 */
	GHOST_STAGE_NONE = 0,
} ghost_stage_t;

/**
 * enum maplet_permissions - Abstract permissions for a range of OA, as bitflags
 */
enum maplet_permissions {
	MAPLET_PERM_R = 1,
	MAPLET_PERM_W = 2,
	MAPLET_PERM_X = 4,

	/*
	 * MAPLET_PERM_UNKNOWN for encodings that do not correspond to any of the above.
	 */
	MAPLET_PERM_UNKNOWN = 8,
};
#define MAPLET_PERM_RW (MAPLET_PERM_R | MAPLET_PERM_W)
#define MAPLET_PERM_RWX (MAPLET_PERM_R | MAPLET_PERM_W | MAPLET_PERM_X)

/**
 * enum maplet_memtype_attr - Abstract memory type.
 */
enum maplet_memtype_attr {
	MAPLET_MEMTYPE_DEVICE,
	MAPLET_MEMTYPE_NORMAL_CACHEABLE,

	/* MAPLET_MEMTYPE_UNKNOWN for encodings that do not correspond to any of the above */
	MAPLET_MEMTYPE_UNKNOWN,
};
