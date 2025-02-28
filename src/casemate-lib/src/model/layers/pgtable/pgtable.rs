use crate::shim::*;

use diffable::{Diffable, DisplayDiff};

use crate::bits::Bitfield;
use crate::model::layers::Machine;
use crate::{collections::region_map::DWordSpan, model::layers::machine::MachineError};

use crate::model::Ctx;

use super::pte::PTE;
use super::{PgtableError, Pgtables};

bitfield!(PTE_FIELD_VALID, 0);
bitfield!(PTE_FIELD_TABLE, 1);
bitfield!(PTE_FIELD_TABLE_POINTER, 47, 12);

// stage1 pte fields
bitfield!(PTE_FIELD_S1_ATTRINDX, 4, 2);
bitfield!(PTE_FIELD_S1_AP1, 6);
bitfield!(PTE_FIELD_S1_AP2, 7);
const PTE_FIELD_S1_AP2_READ_ONLY: u64 = 1u64;
const PTE_FIELD_S1_AP2_READ_WRITE: u64 = 0u64;
bitfield!(PTE_FIELD_S1_XN, 54);
const PTE_FIELD_S1_XN_NOT_EXEC_NEVER: u64 = 0u64;
const PTE_FIELD_S1_XN_EXEC_NEVER: u64 = 1u64;

// stage2 pte fields
bitfield!(PTE_FIELD_S2_S2AP10, 7, 6);
bitfield!(PTE_FIELD_S2_S2AP0, 6);
const PTE_FIELD_S2_S2AP0_READABLE: u64 = 1u64;
const PTE_FIELD_S2_S2AP0_NOT_READABLE: u64 = 0u64;
bitfield!(PTE_FIELD_S2_S2AP1, 7);
const PTE_FIELD_S2_S2AP1_WRITEABLE: u64 = 1u64;
const PTE_FIELD_S2_S2AP1_NOT_WRITEABLE: u64 = 0u64;
bitfield!(PTE_FIELD_S2_XN, 53);
// S2 XN is actually two bits encoding EL1 and EL0 execution separately.
// but we assume they're either both allowed (00) or both forbidden (10)
const PTE_FIELD_S2_XN_NOT_EXEC_NEVER: u64 = 0b00u64;
const PTE_FIELD_S2_XN_EXEC_NEVER: u64 = 0b10u64;
bitfield!(PTE_FIELD_S2_MEMATTR, 5, 2);
#[allow(non_upper_case_globals)]
const PTE_FIELD_S2_MEMATTR_DEVICE_nGnRE: u64 = 0b0010u64;
const PTE_FIELD_S2_MEMATTR_NORMAL_OUTER_INNER_WRITE_BACK_CACHEABLE: u64 = 0b1111u64;

macro_rules! mair_field {
    ($i:expr) => {
        Bitfield::new($i * 8 + 7, $i * 8)
    };
}
const MAIR_FIELDS: [Bitfield; 8] = [
    mair_field!(0),
    mair_field!(1),
    mair_field!(2),
    mair_field!(3),
    mair_field!(4),
    mair_field!(5),
    mair_field!(6),
    mair_field!(7),
];
#[allow(non_upper_case_globals)]
const MEMATTR_FIELD_DEVICE_nGnRE: u64 = 0b00000100u64;
const MEMATTR_FIELD_NORMAL_OUTER_INNER_WRITE_BACK_CACHEABLE: u64 = 0b111111u64;

const KIB_SHIFT: u64 = 10;
const MIB_SHIFT: u64 = 20;
const GIB_SHIFT: u64 = 30;

// how much memory a map at level [N] maps
const MAP_SIZES: [u64; 4] = [
    512 << GIB_SHIFT,
    1 << GIB_SHIFT,
    2 << MIB_SHIFT,
    4 << KIB_SHIFT,
];

// G.b p2742 4KB translation granule has a case split on whether "the Effective value of TCR_ELx.DS or VTCR_EL2.DS is 1".
// DS is for 52-bit output addressing with FEAT_LPA2, and is zero in the register values we see; I'll hard-code that for now.  Thus, G.b says:
// - For a level 1 Block descriptor, bits[47:30] are bits[47:30] of the output address. This output address specifies a 1GB block of memory.
// - For a level 2 Block descriptor, bits[47:21] are bits[47:21] of the output address.This output address specifies a 2MB block of memory.
bitfield!(PTE_FIELD_LVL1_OA, 47, 30);
bitfield!(PTE_FIELD_LVL2_OA, 47, 21);
bitfield!(PTE_FIELD_LVL3_OA, 47, 12);

const PTE_FIELD_OA_MASK: [Bitfield; 4] = [
    Bitfield::empty(),
    PTE_FIELD_LVL1_OA,
    PTE_FIELD_LVL2_OA,
    PTE_FIELD_LVL3_OA,
];

const fn parse_oa(raw: u64, level: u8) -> u64 {
    raw & PTE_FIELD_OA_MASK[level as usize].mask()
}

const TCR_EL2_T0SZ_LO: u64 = 0;
const TCR_EL2_T0SZ_WIDTH: u64 = 6;
const TCR_EL2_T0SZ_MASK: u64 = bitmask!(TCR_EL2_T0SZ_WIDTH - 1, 0) << TCR_EL2_T0SZ_LO;

const TTBR_BADDR_MASK: u64 = bitmask!(47, 1);
const TTBR_ID_LO: u64 = 48;
const TTBR_ID_MASK: u64 = bitmask!(63, 48);

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum TranslationRegime {
    EL2,
    EL10,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Stage {
    Stage1,
    Stage2,
}

/// An architectural context
/// i.e. a set of system registers
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct ArchContext {
    /// The translation-configuration register state
    pub tcr: Option<u64>,

    /// The memory-attributes-indirection-register, if applicable
    pub mair: Option<u64>,
}

impl ArchContext {
    pub fn for_regime(
        mach: &Machine,
        regime: TranslationRegime,
        stage: Stage,
    ) -> Result<Self, MachineError> {
        match (regime, stage) {
            (TranslationRegime::EL10, Stage::Stage2) => Ok(ArchContext {
                tcr: mach.try_read_reg("hcr_el2"),
                mair: None,
            }),
            (TranslationRegime::EL2, Stage::Stage1) => Ok(ArchContext {
                tcr: mach.try_read_reg("tcr_el2"),
                mair: mach.try_read_reg("mair_el2"),
            }),
            _ => todo!(),
        }
    }
}

impl diffable::Scalar for TranslationRegime {}
impl diffable::Scalar for Stage {}

/// A possibly-live translation Context
/// Bundles up the entire architectural state for a translation regime
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Context {
    pub base: u64,
    pub id: u8,
    pub regime: TranslationRegime,
    pub stage: Stage,
    pub arch: ArchContext,
}

impl PartialOrd for Context {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        self.base.partial_cmp(&other.base)
    }
}

impl Ord for Context {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        self.base.cmp(&other.base)
    }
}

impl diffable::Scalar for Context {}

impl fmt::Display for Context {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "(root: {:016x})", self.base)
    }
}

/// Decoded access permissions
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Permissions {
    r: bool,
    w: bool,
    x: bool,
}

impl Permissions {
    pub fn none() -> Self {
        Self {
            r: false,
            w: false,
            x: false,
        }
    }

    pub fn parse_stage1(raw: u64) -> Self {
        let ro = PTE_FIELD_S1_AP2.has_value(raw, PTE_FIELD_S1_AP2_READ_ONLY);
        let xn = PTE_FIELD_S1_XN.has_value(raw, PTE_FIELD_S1_XN_EXEC_NEVER);

        Self {
            // stage1 always has read permissions
            r: true,

            // If not read-only, also has W
            w: !ro,

            // If not e(x)-(n)ever, also has X
            x: !xn,
        }
    }

    pub fn parse_stage2(raw: u64) -> Self {
        let r = PTE_FIELD_S2_S2AP0.has_value(raw, PTE_FIELD_S2_S2AP0_READABLE);
        let w = PTE_FIELD_S2_S2AP1.has_value(raw, PTE_FIELD_S2_S2AP1_WRITEABLE);
        let xn = PTE_FIELD_S2_XN.has_value(raw, PTE_FIELD_S2_XN_EXEC_NEVER);

        Self { r, w, x: !xn }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum MemType {
    Device,
    Normal,
}

impl MemType {
    pub fn parse_mair_memtype(raw: u64) -> Self {
        match raw {
            MEMATTR_FIELD_DEVICE_nGnRE => Self::Device,
            MEMATTR_FIELD_NORMAL_OUTER_INNER_WRITE_BACK_CACHEABLE => Self::Normal,
            _ => panic!("unknown memtype"),
        }
    }

    pub fn parse_stage2_memtype(raw: u64) -> Self {
        match raw {
            PTE_FIELD_S2_MEMATTR_DEVICE_nGnRE => Self::Device,
            PTE_FIELD_S2_MEMATTR_NORMAL_OUTER_INNER_WRITE_BACK_CACHEABLE => Self::Normal,
            _ => panic!("unknown s2 memtype"),
        }
    }
}

/// Decoded page-table-entry attributes
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct DecodedAttributes {
    permissions: Permissions,
    mem_type: MemType,
}

impl DecodedAttributes {
    pub fn parse_stage1(raw: u64, mair: u64) -> Self {
        let permissions = Permissions::parse_stage1(raw);
        let attr_idx = PTE_FIELD_S1_ATTRINDX.extract(raw);
        let attr = MAIR_FIELDS[attr_idx as usize].extract(mair);
        let mem_type = MemType::parse_mair_memtype(attr);

        DecodedAttributes {
            permissions,
            mem_type,
        }
    }

    pub fn parse_stage2(raw: u64) -> Self {
        let permissions = Permissions::parse_stage2(raw);
        let attr = PTE_FIELD_S2_MEMATTR.extract(raw);
        let mem_type = MemType::parse_stage2_memtype(attr);

        DecodedAttributes {
            permissions,
            mem_type,
        }
    }
}

/// A decoded PTE
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Descriptor {
    Invalid { annotation: u64 },
    Block { base: u64, attrs: DecodedAttributes },
    Table { next_level_table: u64 },
}

impl Descriptor {
    pub fn is_leaf(&self) -> bool {
        match self {
            Self::Invalid { annotation: _ } => true,
            Self::Block { base: _, attrs: _ } => true,
            Self::Table {
                next_level_table: _,
            } => false,
        }
    }

    /// Decode the raw PTE into a [`Descriptor`]
    ///
    /// This operation needs some additional data about where in the pagetable the PTE is,
    /// and the current context
    pub fn parse(context: &Context, level: u8, raw: u64) -> Result<Self, PgtableError> {
        let valid = PTE_FIELD_VALID.has_value(raw, 1);
        let is_last_level: bool = level == 3;
        let is_first_level: bool = level == 0;

        if !valid {
            return Ok(Self::Invalid { annotation: raw });
        }

        if is_last_level {
            let page = PTE_FIELD_TABLE.has_value(raw, 1);

            if !page {
                return Err(PgtableError::BadPTEEncoding(
                    "last level entries must have page bit set to 1",
                ));
            }

            let base = parse_oa(raw, level);
            let attrs = match context.stage {
                Stage::Stage1 => DecodedAttributes::parse_stage1(raw, context.arch.mair.unwrap()),
                Stage::Stage2 => DecodedAttributes::parse_stage2(raw),
            };

            Ok(Self::Block { base: base, attrs })
        } else {
            let table = PTE_FIELD_TABLE.has_value(raw, 1);

            if table {
                // TODO: hierarchical attributes/permissions?
                let next_level_table = raw & PTE_FIELD_TABLE_POINTER.mask();
                Ok(Self::Table { next_level_table })
            } else if !is_first_level {
                // block
                let base = parse_oa(raw, level);
                let attrs = match context.stage {
                    Stage::Stage1 => {
                        DecodedAttributes::parse_stage1(raw, context.arch.mair.unwrap())
                    }
                    Stage::Stage2 => DecodedAttributes::parse_stage2(raw),
                };
                Ok(Self::Block { base: base, attrs })
            } else {
                Err(PgtableError::BadPTEEncoding(
                    "level0 entries may not be blocks",
                ))
            }
        }
    }
}

impl<'l> Diffable<'l> for Descriptor {
    // TODO
    type Diff = Descriptor;

    fn diff(&'l self, _other: &'l Self) -> diffable::Difference<&'l Self, Self::Diff> {
        diffable::Difference::NoChange
    }
}

impl DisplayDiff for Descriptor {
    // TODO
    fn fmt(&self, f: &mut diffable::display::DisplayWrapper<'_>) -> core::fmt::Result {
        Ok(())
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum TranslationRegimeTarget {
    EL2,
    EL10,
    All,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum StageTarget {
    Stage1,
    Stage2,
    All,
}

/// A decoded translation-table-base from a TTBR
pub struct DecodedTTB {
    pub base: u64,
    pub id: u8,
}

pub fn read_ttbr(ttb: u64) -> DecodedTTB {
    DecodedTTB {
        base: ttb & TTBR_BADDR_MASK,
        id: ((ttb & TTBR_ID_MASK) >> TTBR_ID_LO) as u8,
    }
}

pub fn is_ttbr(regname: &str) -> bool {
    regname.eq_ignore_ascii_case("vttbr_el2")
        || regname.eq_ignore_ascii_case("ttbr0_el2")
        || regname.eq_ignore_ascii_case("ttbr0_el1")
}

pub fn regime_of_ttbr(ttbr: &str) -> (TranslationRegime, Stage) {
    if ttbr.eq_ignore_ascii_case("ttbr0_el1") {
        (TranslationRegime::EL10, Stage::Stage1)
    } else if ttbr.eq_ignore_ascii_case("ttbr0_el2") {
        (TranslationRegime::EL2, Stage::Stage1)
    } else if ttbr.eq_ignore_ascii_case("vttbr_el2") {
        (TranslationRegime::EL10, Stage::Stage2)
    } else {
        panic!("unknown ttbr")
    }
}

fn read_start_level(tcr: u64) -> u8 {
    let t0sz: u64 = (tcr & TCR_EL2_T0SZ_MASK) >> TCR_EL2_T0SZ_LO;
    // input address = (64 - t0sz) bits
    // max = 48
    // min = 21 (only level 3 table)
    // each 9 bits in-between increases start by 1 level
    let ia_bits: u64 = 64 - t0sz;
    let level: u64 = (48 - ia_bits) / 9;
    level as u8
}

fn discover_start_level(ctx: &Ctx<'_>, trans_ctx: &Context) -> Result<u8, MachineError> {
    let m = ctx.below.mach.as_ref().unwrap();

    match (trans_ctx.regime, trans_ctx.stage) {
        (TranslationRegime::EL10, Stage::Stage2) => {
            let vtcr = m.read_reg("VTCR_EL2")?;
            Ok(read_start_level(vtcr))
        }
        (TranslationRegime::EL2, Stage::Stage1) => {
            let tcr = m.read_reg("TCR_EL2")?;
            Ok(read_start_level(tcr))
        }
        _ => {
            panic!("TODO")
        }
    }
}

pub struct WalkData<'t, 'ctx, 'st> {
    pub ctx: &'ctx Ctx<'t>,
    pub st: &'st mut Pgtables,
    pub ptep: u64,
    pub trans_ctx: Context,
    pub level: u8,
    pub desc: Descriptor,
}

pub const WALKER_FLAGS_SKIP_UNLOCKED: u64 = bit!(0);
pub const WALKER_FLAGS_ALLOW_UNINIT: u64 = bit!(1);

pub fn traverse_pgtable_from<F>(
    ctx: &Ctx<'_>,
    trans_ctx: &Context,
    st: &mut Pgtables,
    table_addr: u64,
    partial_ia: u64,
    level: u8,
    visitor: &F,
    flags: u64,
) -> Result<(), PgtableError>
where
    F: Fn(WalkData<'_, '_, '_>) -> Result<(), PgtableError>,
{
    for i in 0..512 {
        let ptep = table_addr + i * 8;
        let loc = st.ptmem.get(&ptep);

        // {
        //     match st.ptmem.get_mut(&ptep) {
        //         Some(loc) => loc,
        //         None => {
        //             // location unknown to the Pgtable layer
        //             // so create and initialise a new PTE
        //             let raw_desc = ctx.below.mach.as_ref().unwrap().read_mem(ptep).map_err(PgtableError::FailedPgtableWalk)?;
        //             let desc = Descriptor::parse(trans_ctx, level, raw_desc)?;
        //             let loc = PTE::init(trans_ctx.clone(), desc, level);
        //             st.ptmem.insert_range(DWordSpan::new(ptep, 64), loc);
        //             &mut st.ptmem[ptep]
        //         }
        //     }
        // };

        if loc.is_none() && (flags & WALKER_FLAGS_ALLOW_UNINIT != WALKER_FLAGS_ALLOW_UNINIT) {
            return Err(PgtableError::UntrackedLocation(ptep));
        }

        let desc = {
            match loc {
                None => {
                    let raw_desc = ctx
                        .below
                        .mach
                        .as_ref()
                        .unwrap()
                        .read_mem(ptep)
                        .map_err(PgtableError::FailedPgtableWalk)?;
                    Descriptor::parse(trans_ctx, level, raw_desc)?
                }
                Some(loc) => {
                    if (flags & WALKER_FLAGS_SKIP_UNLOCKED) == WALKER_FLAGS_SKIP_UNLOCKED
                        && loc.owner != Some(ctx.t.info.tid)
                    {
                        break;
                    }

                    // We do not have to try decode the PTE here,
                    // as it will have been done when the PTE was first seen
                    // so we just read off the previously-saved context + descriptor
                    // and use those to compute the walk context
                    loc.descriptor
                }
            }
        };

        let tctx = trans_ctx.clone();

        let pte_ia = partial_ia + i * MAP_SIZES[level as usize];

        let walk_data = WalkData {
            ptep,
            st,
            ctx,
            trans_ctx: tctx,
            desc,
            level,
        };

        visitor(walk_data)?;

        // TODO: assert no change to *ptep

        match desc {
            Descriptor::Table { next_level_table } => {
                let next_table_addr = next_level_table & PTE_FIELD_TABLE_POINTER.mask();
                traverse_pgtable_from(
                    ctx,
                    trans_ctx,
                    st,
                    next_table_addr,
                    pte_ia,
                    level,
                    visitor,
                    flags,
                )?;
            }
            _ => (),
        }
    }

    Ok(())
}

pub fn traverse_pgtable<F>(
    ctx: &Ctx<'_>,
    trans_ctx: &Context,
    st: &mut Pgtables,
    visitor: F,
    flags: u64,
) -> Result<(), PgtableError>
where
    F: Fn(WalkData<'_, '_, '_>) -> Result<(), PgtableError>,
{
    let start_level: u8 =
        discover_start_level(ctx, trans_ctx).map_err(PgtableError::FailedPgtableWalk)?;

    // TODO: asserts start_level, nr_concatenated_pgtables, etc.

    let root = trans_ctx.base;

    traverse_pgtable_from(ctx, trans_ctx, st, root, 0, start_level, &visitor, flags)?;
    Ok(())
}

pub fn traverse_all_unclean<F>(
    ctx: &Ctx<'_>,
    st: &mut Pgtables,
    regime: TranslationRegime,
    stage: Stage,
    visitor: F,
    flags: u64,
) -> Result<(), PgtableError>
where
    F: Fn(WalkData<'_, '_, '_>) -> Result<(), PgtableError>,
{
    let uncleans = st.unclean_locs.clone();
    for ptep in uncleans {
        let loc = &mut st.ptmem[ptep];

        let trans_ctx = loc.context;
        let desc = loc.descriptor;
        let leaf = desc.is_leaf();
        let level = loc.level;

        if regime != trans_ctx.regime || stage != trans_ctx.stage {
            continue;
        }

        let walk_data = WalkData {
            ctx,
            st,
            ptep,
            trans_ctx,
            desc,
            level,
        };

        visitor(walk_data)?;
    }

    Ok(())
}
