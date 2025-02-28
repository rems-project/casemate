use crate::shim::*;

use super::{Diffable, Difference, InnerDiff};

// Ints

make_diffable_value!(u64);
make_diffable_value!(u32);
make_diffable_value!(u16);
make_diffable_value!(u8);

make_diffable_value!(i64);
make_diffable_value!(i32);
make_diffable_value!(i16);
make_diffable_value!(i8);

/// Vecs

impl<'l, T: Diffable<'l> + 'l> Diffable<'l> for Vec<T> {
    type Diff = Vec<InnerDiff<'l, T>>;

    fn diff(&'l self, other: &'l Self) -> Difference<&'l Self, Self::Diff> {
        use Difference::*;

        let n = self.len();
        let m = other.len();

        let l = cmp::max(n, m);
        let mut diff: Vec<Difference<&'l T, T::Diff>> = vec![];

        for i in 0..l {
            if i < n && i < m {
                diff.push(self[i].diff(&other[i]));
            } else if i >= m {
                diff.push(Added(&self[i]));
            } else {
                diff.push(Deleted(&other[i]));
            }
        }

        if diff.iter().any(|x| x.has_changed()) {
            Updated(diff)
        } else {
            NoChange(self)
        }
    }
}

// Maps

impl<'l, K, V> Diffable<'l> for collections::BTreeMap<K, V>
where
    K: fmt::Debug,
    K: Ord + 'l,
    V: Diffable<'l> + 'l,
{
    type Diff = collections::BTreeMap<&'l K, InnerDiff<'l, V>>;

    fn diff(&'l self, other: &'l Self) -> Difference<&'l Self, Self::Diff> {
        use Difference::*;

        let all_keys: collections::BTreeSet<&K> = self.keys().chain(other.keys()).collect();

        let mut diff: collections::BTreeMap<&'l K, InnerDiff<'l, V>> = collections::BTreeMap::new();

        for k in all_keys {
            let d = {
                match (self.get(k), other.get(k)) {
                    (None, Some(v)) => Deleted(v),
                    (Some(v), None) => Added(v),
                    (Some(v1), Some(v2)) => v1.diff(v2),
                    (None, None) => unreachable!(),
                }
            };
            diff.insert(k, d);
        }

        if diff.values().any(|x| x.has_changed()) {
            Updated(diff)
        } else {
            NoChange(self)
        }
    }
}

// Options

impl<'l, T> Diffable<'l> for Option<T>
where
    T: fmt::Debug,
    T: Diffable<'l> + 'l,
    T: Default,
{
    type Diff = InnerDiff<'l, T>;

    fn diff(&'l self, other: &'l Self) -> Difference<&'l Self, Self::Diff> {
        use Difference::*;
        match (self, other) {
            (Some(_), None) => Added(self),
            (None, Some(_)) => Deleted(other),
            (None, None) => NoChange(self),
            (Some(x), Some(y)) => {
                let d = x.diff(y);
                if d.has_changed() {
                    Updated(d)
                } else {
                    NoChange(self)
                }
            }
        }
    }
}

// // Cells

// impl<'l, T> Diffable<'l> for cell::RefCell<T>
// where
//     T: fmt::Debug,
//     T: Diffable<'l> + 'l,
//     T: Default,
// {
//     type Diff = InnerDiff<'l, T>;

//     fn diff(&'l self, other: &'l Self) -> Difference<&'l Self, Self::Diff> {
//         let diff = self.borrow().diff(other.borrow());
//         if diff.has_changed() {
//             Difference::Updated(diff)
//         } else {
//             Difference::NoChange(self)
//         }
//     }
// }
