//! A basic 'Memory'
//!
//! [`RegionMap`] behaves as a generic `(Hash|BTree)Map<u64, u8>`
//! but generic over the value type, which specialising the address-like-nature
//! of the keys.

use crate::shim::ops::{Index, IndexMut};
use crate::shim::*;

use diffable::{self, display::DisplayDiffBuilder, Diffable, DisplayDiff};

use crate::output::{LayerFormat, LayerFormatter};

/// A trait representing a Region over a contiguous set of addresses
///
/// r1 <= r2 if r1 starts at or before r2
pub trait Range
where
    Self: Copy + Clone,
    Self: PartialEq + Eq,
    Self: PartialOrd + Ord,
{
    /// Construct a new range from a [`Span`]
    #[allow(dead_code)]
    fn from_span(span: Span) -> Self;

    /// Merges two adjacent ranges together
    ///
    /// Can panic if the ranges are not adjacent
    ///
    fn merge(&self, other: &Self) -> Self;

    /// Splits into (up to) three parts:
    /// +----------------------------+
    /// |          Original          |
    /// +----------------------------+
    ///               |
    ///               v
    /// +----------------------------+
    /// | Before | Subregion | After |
    /// +----------------------------+
    ///
    /// Before/After might be zero size if Subregion extends to, or beyond, the start/end.
    /// Original may be smaller than Subregion, if this is partially contained within Subregion.
    ///
    ///
    fn split(&self, subrange: Self) -> (Self, Self, Self);

    /// Whether this [`Range`] overlaps with `r`
    ///
    /// Note: overlaps is non-symmetric:
    ///   if this region is entirely contaiend within `r`
    ///   then `r.overlaps(self)` but `!self.overlaps(r)`
    ///
    fn overlaps(&self, r: &Self) -> bool;

    /// Returns true if `key` is inside this [`Range`]
    fn contains(&self, key: &u64) -> bool;

    /// Span (in bytes) of this [`Range`]
    fn span(&self) -> Span;
}

/// A continuous region of address space
#[derive(Copy, Clone, Debug, Diffable, PartialEq, Eq, PartialOrd, Ord)]
pub struct Span {
    start: u64,
    size: u64,
}

impl fmt::Display for Span {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "[0x{:016x}..0x{:016x}]", self.start, self.end())
    }
}

impl Span {
    pub fn new(start: u64, size: u64) -> Self {
        Self { start, size }
    }

    fn contains_subregion(&self, r: &Span) -> bool {
        self.start <= r.start && r.end() < self.end()
    }

    fn end(&self) -> u64 {
        self.start + self.size
    }

    /// `r` overlaps this Region's left boundary
    fn overlaps_left(&self, r: &Span) -> bool {
        r.start <= self.start && self.start < r.end()
    }

    /// `r` overlaps this Region's right boundary
    fn overlaps_right(&self, r: &Span) -> bool {
        r.start < self.end() && self.end() < r.end()
    }

    pub fn is_empty(&self) -> bool {
        self.start == self.end()
    }
}

impl Range for Span {
    fn from_span(span: Span) -> Self {
        span
    }

    fn contains(&self, key: &u64) -> bool {
        self.start <= *key && *key < self.end()
    }

    fn overlaps(&self, r: &Span) -> bool {
        self.overlaps_left(r) || self.overlaps_right(r) || self.contains_subregion(r)
    }

    fn split(&self, subregion: Span) -> (Span, Span, Span) {
        let before = Span {
            start: self.start,
            size: zeroing_difference_to(self.start, subregion.start),
        };
        let end = Span {
            start: cmp::min(subregion.end(), self.end()),
            size: zeroing_difference_to(subregion.end(), self.end()),
        };
        let middle = Span {
            start: before.end(),
            size: zeroing_difference_to(before.end(), end.start),
        };
        (before, middle, end)
    }

    fn merge(&self, other: &Span) -> Span {
        if self.end() != other.start {
            panic!("cannot merge non-adjacent Spans");
        }

        Span {
            start: self.start,
            size: self.size + other.size,
        }
    }

    fn span(&self) -> Span {
        self.clone()
    }
}

impl<Idx> Into<Span> for ops::Range<Idx>
where
    Idx: Into<u64>,
{
    fn into(self) -> Span {
        let start: u64 = self.start.into();
        let end: u64 = self.end.into();

        let size = end - start;

        Span { start, size }
    }
}

impl<Idx> Into<Span> for ops::RangeInclusive<Idx>
where
    Idx: Into<u64> + Copy,
{
    fn into(self) -> Span {
        let start: u64 = (*self.start()).into();
        let end: u64 = (*self.end()).into();

        let size = end - start + 1;

        Span { start, size }
    }
}

/// The amount that would need to be added to `here` to reach `there`
///
/// If there < here, returns 0.
///
fn zeroing_difference_to(here: u64, there: u64) -> u64 {
    if there <= here {
        0
    } else {
        there - here
    }
}

fn is_aligned(addr: u64, n: u8) -> bool {
    let mask = !((1u64 << n) - 1);
    let masked = addr & mask;
    masked == addr
}

macro_rules! span_bits_wrapper {
    ($name:ident, $namediff:ident, $n:literal) => {
        /// An `$n`-byte-indexed Range
        #[derive(Copy, Clone, Debug, Diffable, PartialEq, Eq, PartialOrd, Ord)]
        pub struct $name {
            inner: Span,
        }

        impl $name {
            pub fn new(start: u64, size: u64) -> Self {
                if !is_aligned(start, $n) {
                    panic!(concat!("cannot create misaligned ", stringify!($name)));
                }

                if !is_aligned(size, $n) {
                    panic!(concat!("cannot create misaligned ", stringify!($name)));
                }

                Self {
                    inner: Span::new(start, size),
                }
            }
        }

        impl Range for $name {
            fn from_span(span: Span) -> Self {
                Self::new(span.start, span.size)
            }

            fn merge(&self, other: &Self) -> Self {
                Self {
                    inner: self.inner.merge(&other.inner),
                }
            }

            fn split(&self, subrange: Self) -> (Self, Self, Self) {
                let (l, m, r) = self.inner.split(subrange.inner);
                (Self { inner: l }, Self { inner: m }, Self { inner: r })
            }

            fn contains(&self, key: &u64) -> bool {
                self.inner.contains(key)
            }

            fn overlaps(&self, r: &Self) -> bool {
                self.inner.overlaps(&r.inner)
            }

            fn span(&self) -> Span {
                self.inner
            }
        }

        impl fmt::Display for $name {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                write!(
                    f,
                    "[0x{:016x}..0x{:016x}]",
                    self.span().start,
                    self.span().end()
                )
            }
        }
    };
}

// N-bit Spans
span_bits_wrapper!(ByteSpan, ByteSpanDiff, 1);
span_bits_wrapper!(WordSpan, WordSpanDiff, 4);
span_bits_wrapper!(DWordSpan, DWordSpanDiff, 8);

/// A logical map from addresses to values
///
/// Keeps track of the value for a range of addresses,
/// merging and splitting as appropriate.
///
/// The `S` knows nothing of the underlying range which it associates with.
/// i.e. if you have [r1..2: s] and append [r2..3: s] the result is [r1..3: s]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RegionMap<R, S>
where
    R: Range,
{
    /// A sorted sequence of disjoint regions
    map: Vec<(R, S)>,
}

impl<R, S> Default for RegionMap<R, S>
where
    S: Copy,
    R: Range,
{
    fn default() -> Self {
        Self { map: Vec::new() }
    }
}

#[allow(dead_code)]
impl<R, S> RegionMap<R, S>
where
    S: Copy,
    R: Range,
{
    pub fn new() -> Self {
        Self { map: Vec::new() }
    }

    pub fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = (R, S)>,
    {
        let mut m = Self::new();
        for (k, v) in iter {
            m.insert_range(k, v);
        }
        m
    }

    /// Returns `true` if the map contains no elements.
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    /// Span over the entire region
    ///
    /// Not all of the contiguous sub-regions are necessarily mapped
    pub fn convex_span(&self) -> Span {
        if let Some((r_start, _)) = self.map.first() {
            let r_end = self.map.last().unwrap().0;
            let start = r_start.span().start;
            let end = r_end.span().end();
            let size = end - start;
            Span::new(start, size)
        } else {
            Span::new(0, 0)
        }
    }

    /// Gets the index + associated [`Region`] for a given key.
    fn find(&self, k: &u64) -> Option<usize> {
        for (i, (r, _)) in self.map.iter().enumerate() {
            if r.contains(k) {
                return Some(i);
            }
        }
        None
    }

    /// Returns true if this [`RegionMap`] maps the given address
    pub fn contains(&self, k: &u64) -> bool {
        matches!(self.find(k), Some(_))
    }

    /// Split an entry at index `i`
    /// +---------------------------+
    /// |          Original         |
    /// +---------------------------+
    ///               |
    ///               v
    /// +---------------------------+
    /// | Before |          | After |
    /// +---------------------------+
    ///
    /// Panics if `i` out-of-region
    ///
    /// Removes `subregion` from the map,
    /// may insert 0, 1 or 2 new entries for the regions before/after the subregion
    ///
    /// Returns the number of inserted entries
    ///
    fn split_at(&mut self, i: usize, subregion: R) -> usize {
        let mut inserted = 0;

        let ((before, _, after), v) = {
            let (r, v) = &self.map[i];
            (r.split(subregion), *v)
        };

        self.map.remove(i);

        if after.span().size > 0 {
            self.map.insert(i, (after, v));
            inserted += 1;
        }

        if before.span().size > 0 {
            self.map.insert(i, (before, v));
            inserted += 1;
        }

        inserted
    }

    fn insert_disjoint(&mut self, key: R, value: S) {
        for i in 1..self.map.len() {
            let (xr, _) = &self.map[i - 1];
            let (yr, _) = &self.map[i];
            if *xr < key && key < *yr {
                self.map.insert(i, (key, value));
                return;
            }
        }
        self.map.push((key, value));
        self.map.sort_by(|(k1, _), (k2, _)| k1.cmp(k2));
    }

    pub fn remove_range(&mut self, key: R) {
        let mut i = 0;

        while i < self.map.len() {
            let inc_by: usize;
            let (r, _) = &self.map[i];

            if r.overlaps(&key) {
                inc_by = self.split_at(i, key);
            } else {
                inc_by = 1;
            }

            i += inc_by;
        }
    }

    fn insert_into(&mut self, key: R, value: S) {
        self.remove_range(key);
        self.insert_disjoint(key, value)
    }

    pub fn insert_range(&mut self, key: R, value: S) {
        self.insert_into(key, value)
    }

    pub fn get(&self, key: &u64) -> Option<&S> {
        let i = self.find(key)?;
        Some(&self.map[i].1)
    }

    pub fn get_mut(&mut self, key: &u64) -> Option<&mut S> {
        let i = self.find(key)?;
        Some(&mut self.map[i].1)
    }

    pub fn as_ref<'a>(&'a self) -> RegionMap<R, &'a S> {
        RegionMap {
            map: self.map.iter().map(|(r, s)| (*r, s)).collect(),
        }
    }

    /// Extends this [`RegionMap`] with the contents of `other`
    ///
    /// Overwrites the contents with any overlap
    pub fn extend(&mut self, other: &Self) {
        for (r, s) in other.map.iter() {
            self.insert_range(*r, *s);
        }
    }

    /// Combines two [`RegionMap`]s together using [`RegionMap::extend`]
    pub fn union(&self, other: &Self) -> Self {
        let mut m = self.clone();
        m.extend(other);
        m
    }

    /// Produces a new [`RegionMap`] without the ranges defined by `other`
    pub fn difference<'a>(&'a self, other: &Self) -> RegionMap<R, &'a S> {
        let mut m = self.as_ref();
        for (r, _) in other.map.iter() {
            m.remove_range(*r);
        }
        m
    }

    /// Produces a new [`RegionMap`] with only the keys unqiue to both
    pub fn symmetric_difference<'a>(&'a self, other: &'a Self) -> RegionMap<R, &'a S> {
        let m1 = self.difference(other);
        let m2 = other.difference(self);
        m1.union(&m2)
    }

    pub fn iter(&self) -> IterRanges<'_, R, S> {
        IterRanges::new(self)
    }

    pub fn iter_chunked(&self) -> IterRangeChunks<'_, R, S> {
        IterRangeChunks::new(self)
    }

    /// Produces a new [`RegionMap`] with the range that is common to both
    /// mapping to pairs of values
    pub fn intersection<'a>(&'a self, other: &'a Self) -> RegionMap<R, (&'a S, &'a S)> {
        let mut inter = RegionMap::new();

        let mut other_ranges = other.iter_chunked();
        for (r1, s1) in self.iter() {
            let mut r: R = *r1;

            while !r.span().is_empty() {
                match other_ranges.next_overlapping_chunk(&r) {
                    None => break,
                    Some((rover, s2)) => {
                        inter.insert_range(rover, (s1, s2));

                        // some r1 is leftover,
                        // so go around again with the leftover
                        if rover.span().end() < r.span().end() {
                            (_, _, r) = r.split(rover);
                        }
                    }
                }
            }
        }

        inter
    }

    pub fn map_values<F, T>(&self, f: F) -> RegionMap<R, T>
    where
        F: Fn(S) -> T,
    {
        let mut new_map = Vec::new();
        for (r, s) in self.map.iter() {
            new_map.push((*r, f(*s)));
        }
        RegionMap { map: new_map }
    }

    pub fn retain<F>(&mut self, f: F)
    where
        F: Fn(&(R, S)) -> bool,
    {
        self.map.retain(f);
    }
}

pub struct IterRanges<'a, R, S>
where
    R: Range,
{
    inner: &'a RegionMap<R, S>,
    i: usize,
}

impl<'a, R, S> Iterator for IterRanges<'a, R, S>
where
    R: Range,
{
    type Item = (&'a R, &'a S);

    fn next(&mut self) -> Option<Self::Item> {
        if self.i < self.inner.map.len() {
            let (r, s) = &self.inner.map[self.i];
            self.i += 1;
            Some((r, s))
        } else {
            None
        }
    }
}

impl<'a, R, S> IterRanges<'a, R, S>
where
    R: Range,
{
    fn new(inner: &'a RegionMap<R, S>) -> Self {
        Self { inner, i: 0 }
    }
}

pub struct IterRangeChunks<'a, R, S>
where
    R: Range,
{
    inner: &'a RegionMap<R, S>,
    head: Option<(R, &'a S)>,
    i: usize,
}

impl<'a, R, S> Iterator for IterRangeChunks<'a, R, S>
where
    R: Range,
{
    type Item = (R, &'a S);

    fn next(&mut self) -> Option<Self::Item> {
        // if there is a saved head chunk, eat that.
        if let Some(hd) = self.head {
            self.head = None;
            return Some(hd);
        }

        // otherwise: advance
        if self.i < self.inner.map.len() {
            let (r, s) = &self.inner.map[self.i];
            self.i += 1;
            Some((*r, s))
        } else {
            None
        }
    }
}

impl<'a, R, S> IterRangeChunks<'a, R, S>
where
    R: Range,
{
    pub fn new(inner: &'a RegionMap<R, S>) -> Self {
        Self {
            inner,
            head: None,
            i: 0,
        }
    }

    /// Iterate until reach `r`
    fn consume_until(&mut self, r: &R) -> Option<<Self as Iterator>::Item> {
        for (subr, s) in self {
            if r.overlaps(&subr) || subr >= *r {
                return Some((subr, s));
            }
        }
        None
    }

    fn next_overlapping_chunk(&mut self, r: &R) -> Option<<Self as Iterator>::Item> {
        match self.consume_until(r) {
            None => None,
            Some((r2, s)) if r2.span().start >= r.span().end() => {
                // r2 starts after
                self.head = Some((r2, s));
                None
            }
            Some((r2, s)) => {
                // r2 starts before end of r
                let (_, overlap, post) = r2.split(*r);
                if !post.span().is_empty() {
                    self.head = Some((overlap, s));
                }
                Some((overlap, s))
            }
        }
    }
}

impl<R, S> Index<u64> for RegionMap<R, S>
where
    S: Copy,
    R: Range,
{
    type Output = S;

    fn index(&self, index: u64) -> &Self::Output {
        self.get(&index).unwrap()
    }
}

impl<R, S> IndexMut<u64> for RegionMap<R, S>
where
    S: Copy,
    R: Range,
{
    fn index_mut(&mut self, index: u64) -> &mut Self::Output {
        self.get_mut(&index).unwrap()
    }
}

type RegionMapDiff<'l, R, S> = RegionMap<R, diffable::InnerDiff<'l, S>>;

impl<'l, R, S> Diffable<'l> for RegionMap<R, S>
where
    S: Clone + Copy,
    R: Range,
    S: Diffable<'l, Diff: Copy + Debug> + 'l,
    S: Debug,
    R: Debug,
{
    type Diff = RegionMapDiff<'l, R, S>;

    fn diff(&'l self, other: &'l Self) -> diffable::Difference<&'l Self, Self::Diff> {
        let mut d: RegionMapDiff<'l, R, S> = RegionMap::new();

        let added: RegionMap<R, diffable::Difference<&'l S, <S as Diffable<'l>>::Diff>> = self
            .difference(other)
            .map_values(diffable::Difference::Added);

        let removed: RegionMap<R, diffable::Difference<&'l S, <S as Diffable<'l>>::Diff>> = other
            .difference(self)
            .map_values(diffable::Difference::Deleted);

        let overlaps: RegionMap<R, diffable::Difference<&'l S, <S as Diffable<'l>>::Diff>> =
            self.intersection(other).map_values(|(s1, s2)| s1.diff(s2));

        d.extend(&added);
        d.extend(&removed);
        d.extend(&overlaps);

        d.retain(|(_r, s)| s.has_changed());

        if d.is_empty() {
            diffable::Difference::NoChange
        } else {
            diffable::Difference::Updated(d)
        }
    }
}

impl<R, S> DisplayDiff for RegionMap<R, S>
where
    R: Range,
    R: fmt::Display,
    S: DisplayDiff,
{
    fn fmt(&self, f: &mut diffable::display::DisplayWrapper<'_>) -> fmt::Result {
        let mut m = f.open_map();
        for (r, s) in self.map.iter() {
            m = m.field(r, s);
        }
        m.finish()?;
        Ok(())
    }
}

impl<R, S> LayerFormat for RegionMap<R, S>
where
    S: PartialEq + Eq,
    S: Clone + Copy,
    R: Range,

    S: fmt::Display,
    R: fmt::Display,
{
    fn fmt_layer(&self, f: &mut LayerFormatter<'_, '_>) -> fmt::Result {
        let items: Vec<String> = self
            .map
            .iter()
            .map(|(r, s)| format!("{} -> {}", r, s))
            .collect();
        items.fmt_layer(f)?;
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use super::{RegionMap, Span};

    macro_rules! assert_map_equals_at {
        (map:expr, a:expr, b:expr) => {
            assert_eq!($map.get($a), $b);
        };
    }

    #[test]
    fn test_empty_region() {
        let m: RegionMap<Span, ()> = RegionMap::new();
        assert_eq!(m.convex_span().size, 0);
    }

    #[test]
    fn test_singleton_region() {
        let m: RegionMap<Span, i32> = RegionMap::from_iter([((1u64..=1u64).into(), 42)]);
        assert_eq!(m.get(&0), None);
        assert_eq!(m.get(&1), Some(&42));
        assert_eq!(m.get(&2), None);
    }

    #[test]
    fn test_wide_region() {
        let mut m: RegionMap<Span, i32> = RegionMap::new();
        m.insert_range(Span::new(1, 10), 42);
        assert_eq!(m.get(&0), None);
        assert_eq!(m.get(&1), Some(&42));
        assert_eq!(m.get(&10), Some(&42));
        assert_eq!(m.get(&11), None);
    }

    #[test]
    fn test_union() {
        let mut m1: RegionMap<Span, i32> = RegionMap::new();
        let mut m2: RegionMap<Span, i32> = RegionMap::new();
        m1.insert_range(Span::new(5, 5), 42);
        m2.insert_range(Span::new(10, 5), 17);
        let m = m1.union(&m2);
        assert_eq!(m.get(&0), None);
        assert_eq!(m.get(&9), Some(&42));
        assert_eq!(m.get(&10), Some(&17));
        assert_eq!(m.get(&15), None);
    }

    #[test]
    fn test_intersection() {
        let m1: RegionMap<Span, i32> =
            RegionMap::from_iter([((1u64..=10u64).into(), 42), ((15u64..=20u64).into(), 17)]);
        let m2: RegionMap<Span, i32> = RegionMap::from_iter([
            ((0u64..=3u64).into(), 1),
            ((5u64..=6u64).into(), 2),
            ((9u64..=12u64).into(), 3),
            ((14u64..=21u64).into(), 4),
        ]);
        let m = m1.intersection(&m2);
        let expected: RegionMap<Span, (&i32, &i32)> = RegionMap::from_iter([
            ((1..=3u64).into(), (&42, &1)),
            ((5..=6u64).into(), (&42, &2)),
            ((9..=10u64).into(), (&42, &3)),
            ((15..=20u64).into(), (&17, &4)),
        ]);
        assert_eq!(m, expected);
    }
}
