use crate::shim::*;

#[macro_use]
pub mod macros;

mod impls;

#[derive(Debug)]
pub enum Difference<S, D> {
    NoChange(S),
    Added(S),
    Changed(D),
    Deleted(S),
    Updated(D),
}

impl<S, D> Difference<S, D> {
    pub fn has_changed(&self) -> bool {
        !matches!(self, Self::NoChange(_))
    }

    /// Lift a Difference around a wrapping type.
    ///
    /// e.g. if we have `struct B { a: A }`
    /// then we can take an a.diff(...) and `lift` it to be a suitable B diff
    /// by:
    ///   taking NoChanges, Additions and Deletions on A and making them be on B
    ///   and unwrapping Updates
    ///   
    pub fn lift<'l, T>(self, parent: &'l T) -> InnerDiff<'l, T>
    where
        T: Diffable<'l, Diff = D> + 'l,
    {
        use Difference::*;
        match self {
            NoChange(_) => NoChange(parent),
            Added(_) => Added(parent),
            Updated(u) => Updated(u),
            Changed(u) => Changed(u),
            Deleted(_) => Deleted(parent),
        }
    }
}

pub trait Diffable<'l> {
    type Diff;

    fn diff(&'l self, other: &'l Self) -> Difference<&'l Self, Self::Diff>;
}

impl<S: fmt::Display, D: fmt::Display> fmt::Display for Difference<S, D> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Difference::*;
        match self {
            NoChange(_) => f.write_str("..."),
            Added(v) => {
                f.write_str("+++")?;
                v.fmt(f)?;
                f.write_str("+++")
            }
            Deleted(v) => {
                f.write_str("---")?;
                v.fmt(f)?;
                f.write_str("---")
            }
            Updated(u) => u.fmt(f),
            Changed(u) => {
                f.write_str("~~~")?;
                u.fmt(f)?;
                f.write_str("~~~")
            }
        }
    }
}

/// An inner diff is just a `Difference` for a Diffable object
///
/// The constraint `T: Diffable<'l>` is required to access the associated type
/// and is not required for the typechecking of the lifetimes
#[allow(type_alias_bounds)]
pub type InnerDiff<'l, T>
where
    T: Diffable<'l>,
= Difference<&'l T, T::Diff>;
