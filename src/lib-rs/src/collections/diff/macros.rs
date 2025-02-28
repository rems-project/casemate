#[macro_export]
macro_rules! make_diffable_value {
    ($ty: ty) => {
        impl<'l> $crate::collections::diff::Diffable<'l> for $ty {
            type Diff = &'l $ty;

            fn diff(
                &'l self,
                other: &'l Self,
            ) -> $crate::collections::diff::Difference<&'l Self, Self::Diff> {
                use $crate::collections::diff::Difference::*;
                if self == other {
                    NoChange(self)
                } else {
                    Changed(self)
                }
            }
        }
    };
}

// pub struct MachineDiff<'m> {
//     regs: diff::InnerDiff<'m, RegMap<u64>>,
//     mem: diff::InnerDiff<'m, RegionMap<u64>>,
// }

// impl<'l> diff::Diffable<'l> for Machine {
//     type Diff = MachineDiff<'l>;

//     fn diff(&'l self, other: &'l Self) -> diff::Difference<&'l Self, Self::Diff> {
//         let diff: MachineDiff<'l> = MachineDiff {
//             regs: self.regs.diff(&other.regs),
//             mem: self.mem.diff(&other.mem),
//         };

//         if diff.regs.has_changed() || diff.mem.has_changed() {
//             diff::Difference::Updated(diff)
//         } else {
//             diff::Difference::NoChange(self)
//         }
//     }
// }

/// Make a default Diffable instance for a struct-of-diffable-fields
///
/// ```edition2021
/// #[cfg(feature="std")]
///
/// #[derive(Debug)]
/// struct Foo {
///     a: u64,
///     b: u64,
/// }
///
/// make_diffable_struct!(Foo, FooDiff; a:u64, b:u64)
///
/// let x = Foo { a: 1, b : 1 };
/// let y = Foo { a: 2, b : 1 };
/// let d = (&x).diff(&y);
/// ```
#[macro_export]
macro_rules! make_diffable_struct {
    ($ty: ty, $diffname: ident; $($fname:ident: $fty:ty),*) => {
        #[derive(Debug)]
        pub struct $diffname<'a> {
            $($fname: $crate::collections::diff::InnerDiff<'a, $fty>),*
        }

        impl<'l> $crate::collections::diff::Diffable<'l> for $ty {
            type Diff = $diffname<'l>;

            fn diff(&'l self, other: &'l Self) -> $crate::collections::diff::Difference<&'l Self, Self::Diff> {
                let d: $diffname<'l> = $diffname {
                    $($fname: self.$fname.diff(&other.$fname)),*
                };

                let changes = &[$(d.$fname.has_changed()),+];

                if changes.into_iter().any(|b| *b) {
                    $crate::collections::diff::Difference::Updated(d)
                } else {
                    $crate::collections::diff::Difference::NoChange(self)
                }
            }
        }
    };
}
