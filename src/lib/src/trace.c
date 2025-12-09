#include <casemate-impl.h>

//////////////////////////
// String reprs for types

#pragma GCC diagnostic ignored "-Wunused-variable"

#define ID_STRING(x) [x] = #x

static const char *tlbi_kind_names[] = {
	[TLBI_vmalls12e1] = "vmalls12e1", //
	[TLBI_vmalls12e1is] = "vmalls12e1is", //
	[TLBI_vmalle1is] = "vmalle1is", //
	[TLBI_alle1is] = "alle1is", //
	[TLBI_vmalle1] = "vmalle1", //
	[TLBI_vale2is] = "vale2is", //
	[TLBI_vae2is] = "vae2is", //
	[TLBI_ipas2e1is] = "ipas2e1is", //
};

static const char *sysreg_names[] = {
	[SYSREG_VTTBR] = "vttbr_el2", //
	[SYSREG_TTBR_EL2] = "ttbr0_el2", //
	[SYSREG_VTCR_EL2] = "vtcr_el2", //
	[SYSREG_TCR_EL2] = "tcr_el2", //
	[SYSREG_MAIR_EL2] = "mair_el2", //
};

static const char *mem_order_names[] = {
	[WMO_plain] = "plain",
	[WMO_release] = "release",
};

static const char *barrier_dxb_kind_names[] = {
	[DxB_ish] = "ish",
	[DxB_ishst] = "ishst",
	[DxB_nsh] = "nsh",
};

static const char *barrier_kind_names[] = {
	[BARRIER_DSB] = "dsb",
	[BARRIER_ISB] = "isb",
};

static const char *hw_step_names[] = {
	[HW_MEM_WRITE] = "mem-write", //
	[HW_MEM_READ] = "mem-read", //
	[HW_BARRIER] = "barrier", //
	[HW_TLBI] = "tlbi", //
	[HW_MSR] = "sysreg-write", //
};

static const char *abs_step_names[] = {
	[GHOST_ABS_LOCK] = "lock",
	[GHOST_ABS_UNLOCK] = "unlock",
	[GHOST_ABS_INIT] = "mem-init",
	[GHOST_ABS_MEMSET] = "mem-set",
};

static const char *hint_step_name = "hint";

static const char *hint_names[] = {
	[GHOST_HINT_SET_ROOT_LOCK] = "set_root_lock",
	[GHOST_HINT_SET_OWNER_ROOT] = "set_owner_root",
	[GHOST_HINT_RELEASE_TABLE] = "release_table",
	[GHOST_HINT_SET_PTE_THREAD_OWNER] = "set_pte_thread_owner",
};

//////////////////////
// Record construction

static int record_cm_sysreg_fields(struct string_builder *buf, struct trans_msr_data *data)
{
	TRY_PUT_KV("sysreg", sb_puts(buf, sysreg_names[data->sysreg]));
	TRY_PUT(' ');
	TRY_PUT_KV("value", sb_putxn(buf, data->val, 64));
	return 0;
}

static int record_cm_tlbi_fields(struct string_builder *buf, struct trans_tlbi_data *data)
{
	TRY_PUTS(tlbi_kind_names[data->tlbi_kind]);

	switch (data->tlbi_kind) {
	case TLBI_vmalls12e1:
	case TLBI_vmalls12e1is:
	case TLBI_vmalle1is:
	case TLBI_alle1is:
	case TLBI_vmalle1:
		return 0;

	case TLBI_vale2is:
	case TLBI_vae2is:
	case TLBI_ipas2e1is:
		TRY_PUT(' ');
		TRY_PUT_KV("value", sb_putxn(buf, data->value, 64));
		return 0;

	default:
		unreachable();
	}
}

static int record_cm_barrier_fields(struct string_builder *buf, struct trans_barrier_data *data)
{
	TRY_PUTS(barrier_kind_names[data->kind]);

	switch (data->kind) {
	case BARRIER_ISB:
		return 0;

	case BARRIER_DSB:
		TRY_PUT(' ');
		TRY_PUT_KV("kind", sb_puts(buf, barrier_dxb_kind_names[data->dxb_data]));
		return 0;

	default:
		unreachable();
	}
}

static int record_cm_hw_fields(struct string_builder *buf, struct ghost_hw_step *step)
{
	switch (step->kind) {
	case HW_MEM_WRITE:
		TRY_PUT_KV("mem-order", sb_puts(buf, mem_order_names[step->write_data.mo]));
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
		unreachable();
	}
}

static int record_cm_abs_fields(struct string_builder *buf, struct ghost_abs_step *step)
{
	int ret;
	switch (step->kind) {
	case GHOST_ABS_LOCK:
	case GHOST_ABS_UNLOCK:
		TRY_PUT_KV("address", sb_putxn(buf, step->lock_data.address, 64));
		return 0;

	case GHOST_ABS_INIT:
		TRY_PUT_KV("address", sb_putxn(buf, step->init_data.location, 64));
		TRY_PUT(' ');
		TRY_PUT_KV("size", sb_putxn(buf, step->init_data.size, 64));
		return 0;

	case GHOST_ABS_MEMSET:
		TRY_PUT_KV("address", sb_putxn(buf, step->memset_data.address, 64));
		TRY_PUT(' ');
		TRY_PUT_KV("size", sb_putxn(buf, step->memset_data.size, 64));
		TRY_PUT(' ');
		TRY_PUT_KV("value", sb_putxn(buf, step->memset_data.size, 8));
		return 0;

	default:
		unreachable();
	}
}

static int record_cm_hint_fields(struct string_builder *buf, struct ghost_hint_step *hint_step)
{
	const char *hint_name = hint_names[hint_step->kind];

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
		BUG();
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
		prefix = hw_step_names[trans->hw_step.kind];
		break;

	case TRANS_ABS_STEP:
		prefix = abs_step_names[trans->hw_step.kind];
		break;

	case TRANS_HINT:
		prefix = hint_step_name;
		break;

	default:
		BUG();
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

void put_trans(void *arg)
{
	int ret;
	DEFINE_STRING_BUFFER(sb, 256);
	struct casemate_model_step *step = (struct casemate_model_step *)arg;
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