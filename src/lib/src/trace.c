#include <casemate-impl.h>

//////////////////////////
// String reprs for types

#pragma GCC diagnostic ignored "-Wunused-variable"

#define ID_STRING(x) [x]=#x

static const char *tlbi_kind_names[] = {
	[TLBI_vmalls12e1] = "VMALLS12E1",
	[TLBI_vmalls12e1is] = "VMALLS12E1IS",
	[TLBI_vmalle1is] = "VMALLE1IS",
	[TLBI_alle1is] = "ALLE1IS",
	[TLBI_vmalle1] = "VMALLE1",
	[TLBI_vale2is] = "VALE2IS",
	[TLBI_vae2is] = "VAE2IS",
	[TLBI_ipas2e1is] = "IPAS2E1IS",
};

static const char *sysreg_names[] = {
	[SYSREG_VTTBR] = "VTTBR_EL2",
	[SYSREG_TTBR_EL2] = "TTBR0_EL2",
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
	[BARRIER_DSB] = "DSB",
	[BARRIER_ISB] = "ISB",
};

static const char *hw_step_names[] = {
	[HW_MEM_WRITE] = "MEM-WRITE",
	[HW_MEM_READ] = "MEM-READ",
	[HW_BARRIER] = "BARRIER",
	[HW_TLBI] = "TLBI",
	[HW_MSR] = "MSR",
};

static const char *abs_step_names[] = {
	[GHOST_ABS_LOCK] = "LOCK",
	[GHOST_ABS_UNLOCK] = "UNLOCK",
	[GHOST_ABS_INIT] = "MEM-INIT",
	[GHOST_ABS_MEMSET] = "MEM-SET",
};

static const char *hint_names[] = {
	[GHOST_HINT_SET_ROOT_LOCK] = "SET_ROOT_LOCK",
	[GHOST_HINT_SET_OWNER_ROOT] = "SET_OWNER_ROOT",
	[GHOST_HINT_RELEASE_TABLE] = "RELEASE_TABLE",
	[GHOST_HINT_SET_PTE_THREAD_OWNER] = "SET_PTE_THREAD_OWNER",
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
		TRY_PUT_KV("addr", sb_putxn(buf, data->page, 64));
		TRY_PUT(' ');
		TRY_PUT_KV("level", sb_putxn(buf, data->level, 64));
		return 0;
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
		BUG(); // unreachable.
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
		BUG();  // unreachable;
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

static int record_common_fields(struct string_builder *buf, struct casemate_model_step *trans)
{
	TRY_PUT_KV("id", sb_putn(buf, trans->seq_id));
	TRY_PUT(' ');
	TRY_PUT_KV("tid", sb_putn(buf, trans->tid));
	TRY_PUT(' ');
	TRY_PUT_KV("src", record_common_src_field(buf, &trans->src_loc));
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
		prefix = "HINT";
		break;

	default:
		BUG();
	}

	TRY(sb_puts(buf, prefix));
	return 0;
}

static int record_cm_trans(struct string_builder *buf, struct casemate_model_step *trans)
{
	TRY_PUT('(');
	TRY(record_prefix(buf, trans));
	TRY_PUT(' ');
	TRY(record_common_fields(buf, trans));
	TRY_PUT(' ');
	TRY(record_trans_fields(buf, trans));
	TRY_PUT(')');
	return 0;
}

void trace_step(struct casemate_model_step *trans)
{
	int ret;
	char buf[256] = {0};
	struct string_builder sb = {.out = buf, .cur = buf, .rem = 256};
	ret = record_cm_trans(&sb, trans);

	if (ret) {
		GHOST_WARN("failed to generate trace record for transition with id=%d, message too long.", 0);
		side_effect()->abort("trace record too long");
	}

	side_effect()->trace(buf);
}