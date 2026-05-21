#include <casemate-impl.h>

//////////////////////////
// String reprs for types

#pragma GCC diagnostic ignored "-Wunused-variable"

#define NR_ELEMS(A) (sizeof(A) / sizeof((A)[0]))

struct enum_map {
	u64 count;
	const char **names;
};

#define DEFINE_ENUM_MAP(MAP, NAMES) \
	static struct enum_map MAP = { \
		.count = NR_ELEMS(NAMES), \
		.names = NAMES, \
	}

static const char *enum_map_lookup(struct enum_map *map, int value)
{
	if (value < 0 || (u64)value >= map->count || ! map->names[value])
		return "???";

	return map->names[value];
}

static const char *tlbi_kind_names[] = {
	[TLBI_vmalls12e1] = "vmalls12e1", //
	[TLBI_vmalls12e1is] = "vmalls12e1is", //
	[TLBI_vmalle1is] = "vmalle1is", //
	[TLBI_alle1] = "alle1", //
	[TLBI_alle1is] = "alle1is", //
	[TLBI_vmalle1] = "vmalle1", //
	[TLBI_alle2] = "alle2", //
	[TLBI_alle2is] = "alle2is", //
	[TLBI_vale2is] = "vale2is", //
	[TLBI_vae2is] = "vae2is", //
	[TLBI_ipas2e1is] = "ipas2e1is", //
};
DEFINE_ENUM_MAP(tlbi_kind_map, tlbi_kind_names);

static const char *sysreg_names[] = {
	[SYSREG_VTTBR] = "vttbr_el2", //
	[SYSREG_TTBR_EL2] = "ttbr0_el2", //
	[SYSREG_VTCR_EL2] = "vtcr_el2", //
	[SYSREG_HCR_EL2] = "hcr_el2", //
	[SYSREG_TCR_EL2] = "tcr_el2", //
	[SYSREG_SCTLR_EL2] = "sctlr_el2", //
	[SYSREG_MAIR_EL2] = "mair_el2", //
};
DEFINE_ENUM_MAP(sysreg_map, sysreg_names);

static const char *mem_order_names[] = {
	[WMO_plain] = "plain",
	[WMO_release] = "release",
};
DEFINE_ENUM_MAP(mem_order_map, mem_order_names);

static const char *barrier_dxb_kind_names[] = {
	[DxB_ish] = "ish",
	[DxB_ishst] = "ishst",
	[DxB_nsh] = "nsh",
};
DEFINE_ENUM_MAP(barrier_dxb_kind_map, barrier_dxb_kind_names);

static const char *barrier_kind_names[] = {
	[BARRIER_DSB] = "dsb",
	[BARRIER_ISB] = "isb",
};
DEFINE_ENUM_MAP(barrier_kind_map, barrier_kind_names);

static const char *hw_step_names[] = {
	[HW_MEM_WRITE] = "mem-write", //
	[HW_MEM_READ] = "mem-read", //
	[HW_BARRIER] = "barrier", //
	[HW_TLBI] = "tlbi", //
	[HW_MSR] = "sysreg-write", //
};
DEFINE_ENUM_MAP(hw_step_map, hw_step_names);

static const char *abs_step_names[] = {
	[GHOST_ABS_LOCK] = "lock", //
	[GHOST_ABS_TRYLOCK] = "trylock", //
	[GHOST_ABS_UNLOCK] = "unlock", //
	[GHOST_ABS_INIT] = "mem-init", //
	[GHOST_ABS_FREE] = "mem-free", //
	[GHOST_ABS_MEMSET] = "mem-set", //
};
DEFINE_ENUM_MAP(abs_step_map, abs_step_names);

static const char *hint_names[] = {
	[GHOST_HINT_SET_ROOT_LOCK] = "set_root_lock",
	[GHOST_HINT_SET_OWNER_ROOT] = "set_owner_root",
	[GHOST_HINT_RELEASE_TABLE] = "release_table",
	[GHOST_HINT_SET_PTE_THREAD_OWNER] = "set_pte_thread_owner",
};
DEFINE_ENUM_MAP(hint_map, hint_names);

//////////////////////
// Record construction

static int record_cm_sysreg_fields(struct string_builder *buf, struct trans_msr_data *data)
{
	TRY_PUT_KV("sysreg", sb_puts(buf, enum_map_lookup(&sysreg_map, data->sysreg)));
	TRY_PUT(' ');
	TRY_PUT_KV("value", sb_putxn(buf, data->val, 64));
	return 0;
}

static int record_cm_tlbi_fields(struct string_builder *buf, struct trans_tlbi_data *data)
{
	TRY_PUTS(enum_map_lookup(&tlbi_kind_map, data->tlbi_kind));

	switch (data->tlbi_kind) {
	case TLBI_vmalls12e1:
	case TLBI_vmalls12e1is:
	case TLBI_vmalle1is:
	case TLBI_alle1:
	case TLBI_alle1is:
	case TLBI_alle2:
	case TLBI_alle2is:
	case TLBI_vmalle1:
		return 0;

	case TLBI_vale2is:
	case TLBI_vae2is:
	case TLBI_ipas2e1is:
		TRY_PUT(' ');
		TRY_PUT_KV("value", sb_putxn(buf, data->value, 64));
		return 0;

	default:
		return 0;
	}
}

static int record_cm_barrier_fields(struct string_builder *buf, struct trans_barrier_data *data)
{
	TRY_PUTS(enum_map_lookup(&barrier_kind_map, data->kind));

	switch (data->kind) {
	case BARRIER_ISB:
		return 0;

	case BARRIER_DSB:
		TRY_PUT(' ');
		TRY_PUT_KV("kind",
			   sb_puts(buf, enum_map_lookup(&barrier_dxb_kind_map, data->dxb_data)));
		return 0;

	default:
		return 0;
	}
}

static int record_cm_hw_fields(struct string_builder *buf, struct ghost_hw_step *step)
{
	switch (step->kind) {
	case HW_MEM_WRITE:
		TRY_PUT_KV("mem-order",
			   sb_puts(buf, enum_map_lookup(&mem_order_map, step->write_data.mo)));
		TRY_PUT(' ');
		TRY_PUT_KV("address", sb_putxn(buf, step->write_data.phys_addr, 64));
		TRY_PUT(' ');
		TRY_PUT_KV("value", sb_putxn(buf, step->write_data.val, 64));
		return 0;

	case HW_MEM_READ:
		TRY_PUT_KV("address", sb_putxn(buf, step->read_data.phys_addr, 64));
		TRY_PUT(' ');
		TRY_PUT_KV("value", sb_putxn(buf, step->read_data.val, 64));
		return 0;

	case HW_BARRIER:
		return record_cm_barrier_fields(buf, &step->barrier_data);
		break;

	case HW_TLBI:
		return record_cm_tlbi_fields(buf, &step->tlbi_data);
		break;

	case HW_MSR:
		return record_cm_sysreg_fields(buf, &step->msr_data);
		break;

	default:
		return 0;
	}
}

static int record_cm_abs_fields(struct string_builder *buf, struct ghost_abs_step *step)
{
	int ret;
	switch (step->kind) {
	case GHOST_ABS_LOCK:
	case GHOST_ABS_TRYLOCK:
	case GHOST_ABS_UNLOCK:
		TRY_PUT_KV("address", sb_putxn(buf, step->lock_data.address, 64));
		return 0;

	case GHOST_ABS_INIT:
	case GHOST_ABS_FREE:
		TRY_PUT_KV("address", sb_putxn(buf, step->init_data.location, 64));
		TRY_PUT(' ');
		TRY_PUT_KV("size", sb_putxn(buf, step->init_data.size, 64));
		return 0;

	case GHOST_ABS_MEMSET:
		TRY_PUT_KV("address", sb_putxn(buf, step->memset_data.address, 64));
		TRY_PUT(' ');
		TRY_PUT_KV("size", sb_putxn(buf, step->memset_data.size, 64));
		TRY_PUT(' ');
		TRY_PUT_KV("value", sb_putxn(buf, step->memset_data.value, 8));
		return 0;

	default:
		return 0;
	}
}

static int record_cm_hint_fields(struct string_builder *buf, struct ghost_hint_step *hint_step)
{
	const char *hint_name = enum_map_lookup(&hint_map, hint_step->kind);

	TRY_PUT_KV("kind", sb_puts(buf, hint_name));
	TRY_PUT(' ');
	TRY_PUT_KV("location", sb_putxn(buf, hint_step->location, 64));
	TRY_PUT(' ');
	TRY_PUT_KV("value", sb_putxn(buf, hint_step->value, 64));
	return 0;
}

static int record_trans_fields(struct string_builder *buf, struct casemate_model_step *trans)
{
	switch (trans->kind) {
	case TRANS_HW_STEP:
		return record_cm_hw_fields(buf, &trans->hw_step);

	case TRANS_ABS_STEP:
		return record_cm_abs_fields(buf, &trans->abs_step);

	case TRANS_HINT:
		return record_cm_hint_fields(buf, &trans->hint_step);

	default:
		return 0;
	}
}

static int record_common_src_field(struct string_builder *buf, struct src_loc *loc)
{
	TRY_PUT('"');
	TRY_PUTS(loc->file);
	TRY_PUT(':');
	TRY(sb_putn(buf, loc->lineno));
	TRY_PUT('"');
	return 0;
}

static int record_common_required_fields(struct string_builder *buf,
					 struct casemate_model_step *trans)
{
	TRY_PUT_KV("id", sb_putn(buf, trans->seq_id));
	TRY_PUT(' ');
	TRY_PUT_KV("tid", sb_putn(buf, trans->tid));
	return 0;
}

static int record_prefix(struct string_builder *buf, struct casemate_model_step *trans)
{
	const char *prefix = NULL;

	switch (trans->kind) {
	case TRANS_HW_STEP:
		prefix = enum_map_lookup(&hw_step_map, trans->hw_step.kind);
		break;

	case TRANS_ABS_STEP:
		prefix = enum_map_lookup(&abs_step_map, trans->abs_step.kind);
		break;

	case TRANS_HINT:
		prefix = "hint";
		break;

	default:
		prefix = "???";
		break;
	}

	TRY(sb_puts(buf, prefix));
	return 0;
}

static int record_common_optional_fields(struct string_builder *buf,
					 struct casemate_model_step *trans)
{
	TRY_PUT_KV("src", record_common_src_field(buf, &trans->src_loc));
	return 0;
}

static int record_cm_trans(struct string_builder *buf, struct casemate_model_step *trans)
{
	TRY_PUT('(');
	TRY(record_prefix(buf, trans));
	TRY_PUT(' ');
	TRY(record_common_required_fields(buf, trans));
	TRY_PUT(' ');
	TRY(record_trans_fields(buf, trans));
	TRY_PUT(' ');
	TRY(record_common_optional_fields(buf, trans));
	TRY_PUT(')');
	return 0;
}

void put_step(struct casemate_model_step *step)
{
	int ret;
	DEFINE_STRING_BUFFER(sb, 256);
	ret = record_cm_trans(&sb, step);
	if (ret)
		side_effect()->abort("trace record too long");
	ghost_printf("%s", sb.out);
}

void trace_step(struct casemate_model_step *trans)
{
	int ret;
	DEFINE_STRING_BUFFER(sb, 256);
	ret = record_cm_trans(&sb, trans);

	if (ret) {
		GHOST_WARN("failed to generate trace record, message too long.");
		side_effect()->abort("trace record too long");
	}

	side_effect()->trace(sb.out);
}
