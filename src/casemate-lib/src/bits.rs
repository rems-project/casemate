/// A fixed-width bitfield
///
/// For easy masking and field extraction from bitvectors
pub struct Bitfield {
    lsb: u8,
    width: u8,
}

impl Bitfield {
    pub const fn new(msb: u8, lsb: u8) -> Self {
        let width = msb - lsb + 1;
        Self { lsb, width }
    }

    /// A zero-width bitfield
    pub const fn empty() -> Self {
        Self { lsb: 0, width: 0 }
    }

    /// Returns the mask of 1s which covers this bitfield
    /// ```
    /// let bf = bitfield!(11, 0);
    /// assert_equals(bf.mask(), 0x3f);
    /// ```
    pub const fn mask(&self) -> u64 {
        ((1 << self.width) - 1) << self.lsb
    }

    pub const fn extract(&self, raw: u64) -> u64 {
        (raw & self.mask()) >> self.lsb
    }

    pub const fn has_value(&self, raw: u64, field_value: u64) -> bool {
        self.extract(raw) == field_value
    }
}

/// A helper macro for creating [`Bitfield`]s.
///
/// `bitfield!(foo, 11, 0)` makes a 12-bit [`Bitfield`] called `foo` with an `lsb` of 0.
/// `bitfield!(bar, 12)` makes a 1-bit [`Bitfield`] called `bar` at bit 12.
macro_rules! bitfield {
    ($name:ident, $msb:expr, $lsb:expr) => {
        const $name: crate::bits::Bitfield = crate::bits::Bitfield::new($msb, $lsb);
    };
    ($name:ident, $lsb:expr) => {
        const $name: crate::bits::Bitfield = crate::bits::Bitfield::new($lsb, $lsb);
    };
}

macro_rules! bitmask {
    ($msb:expr, $lsb:expr) => {
        ((1 << ($msb - $lsb + 1)) - 1) << $lsb
    };
}

macro_rules! bit {
    ($bit:expr) => {
        1 << $bit
    };
}
