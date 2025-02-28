//! A basic 'Memory'
//!
//! [`RegionMap`] behaves as a generic `(Hash|BTree)Map<u64, u8>`
//! but generic over the value type, which specialising the address-like-nature
//! of the keys.

use crate::shim::ops::Index;
use crate::shim::*;

use crate::collections::diff;

#[derive(Debug, Clone)]
pub struct RegionMap<S> {
    map: collections::BTreeMap<u64, S>,
}

impl<S> Default for RegionMap<S> {
    fn default() -> Self {
        Self {
            map: collections::BTreeMap::new(),
        }
    }
}

impl<S> RegionMap<S> {
    pub fn insert(&mut self, key: u64, value: S) -> Option<S> {
        self.map.insert(key, value)
    }

    pub fn get(&self, key: &u64) -> Option<&S> {
        self.map.get(key)
    }

    pub fn get_mut(&mut self, key: &u64) -> Option<&mut S> {
        self.map.get_mut(key)
    }

    #[allow(dead_code)]
    pub fn iter(&self) -> collections::btree_map::Iter<'_, u64, S> {
        self.map.iter()
    }
}

impl<S> Index<u64> for RegionMap<S> {
    type Output = S;

    fn index(&self, index: u64) -> &Self::Output {
        self.map.index(&index)
    }
}

impl<'l, S> diff::Diffable<'l> for RegionMap<S>
where
    S: diff::Diffable<'l> + 'l,
{
    type Diff = collections::BTreeMap<&'l u64, diff::InnerDiff<'l, S>>;

    fn diff(&'l self, other: &'l Self) -> diff::Difference<&'l Self, Self::Diff> {
        self.map.diff(&other.map).lift(self)
    }
}
