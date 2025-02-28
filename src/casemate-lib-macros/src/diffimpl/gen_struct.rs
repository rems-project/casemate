//! Generates [`Diffable`] implementations of structs
//!
//! ```edition2021
//! #[derive(Debug, Diffable)]
//! struct Foo {
//!     a: u64,
//!     b: u64,
//! }
//!
//! let x = Foo { a: 1, b : 1 };
//! let y = Foo { a: 2, b : 1 };
//! let d = (&x).diff(&y);
//! println!("{diff:?}");}
//! ```

use syn;

use crate::diffimpl::DiffImpl;
use crate::names;

/// Generators for the [`Diffable::Diff`] wrapper type
mod diff_obj {
    use proc_macro2::TokenStream;
    use quote::quote;
    use syn;

    use crate::names;

    fn gen_diff_type_field(f: &syn::Field) -> TokenStream {
        let name = &f.ident;
        let ty = &f.ty;
        quote!(
            // Note trailing Comma!
            #name: diffable::InnerDiff<'diffl, #ty>,
        )
    }

    fn gen_diff_type_fields(fs: &syn::Fields) -> TokenStream {
        let fields = Vec::from_iter(fs.iter().map(gen_diff_type_field));

        TokenStream::from_iter(fields.into_iter())
    }

    /// Generates the wrapped [`Diffable::Diff`] object
    pub fn gen_wrapped_diff_struct(input: &syn::DeriveInput, s: &syn::DataStruct) -> TokenStream {
        let diffty = names::gen_diff_type(input);
        let diff_fields = gen_diff_type_fields(&s.fields);
        quote!(
            struct #diffty {
                #diff_fields
            }
        )
    }
}

/// Generators for the [`Diffable::diff`] implementation
mod diff_fn {
    use proc_macro2::TokenStream;
    use quote::quote;
    use syn;

    fn gen_diff_inst_field(f: &syn::Field) -> TokenStream {
        let name = &f.ident;
        quote!(
            // Note trailing Comma!
            #name: self.#name.diff(&other.#name),
        )
    }

    fn gen_diff_inst_fields(fields: &syn::Fields) -> TokenStream {
        let fields: Vec<TokenStream> = Vec::from_iter(fields.iter().map(gen_diff_inst_field));

        TokenStream::from_iter(fields.into_iter())
    }

    fn gen_diff_changes(fields: &syn::Fields) -> TokenStream {
        TokenStream::from_iter(fields.iter().map(|f| {
            let name = &f.ident;
            quote!(
                d.#name.has_changed(),
            )
        }))
    }

    pub fn gen_diff_impl(fields: &syn::Fields) -> TokenStream {
        let diff_fields = gen_diff_inst_fields(fields);
        let diff_changes = gen_diff_changes(fields);
        quote!(
            let d = Self::Diff {
                #diff_fields
            };

            let changes = &[#diff_changes];
            if changes.into_iter().any(|b| *b) {
                diffable::Difference::Updated(d)
            } else {
                diffable::Difference::NoChange
            }
        )
    }
}

/// Generates the struct-specific parts of the Diffable-derived implementation
///
/// For the `Foo` example, generates something aproximating:
/// ```edition2021
/// #[derive(Debug)]
/// struct DiffFoo<'diffl> {
///     x: diffable::InnerDiff<'diffl, u64>,
///     y: diffable::InnerDiff<'diffl, u64>,
/// }
///
/// impl<'diffl> diffable::Diffable<'diffl> for Foo {
///     type Diff = DiffFoo<'diffl>;
///     fn diff(&'diffl self, other: &'diffl Self) -> diffable::Difference<&'diffl Self, Self::Diff> {
///         let d = DiffFoo {
///             x: self.x.diff(&other.x),
///             y: self.y.diff(&other.y),
///         };
///         if d.x.has_changed() || d.y.has_changed() {
///             diffable::Difference::Updated(d)
///         } else {
///             diffable::Difference::NoChange
///         }
///     }
/// }
/// ```
pub fn generate_impl_diffable_struct(input: &syn::DeriveInput, s: &syn::DataStruct) -> DiffImpl {
    let diff_assoc_type = names::gen_diff_type(input);
    let diff_type = diff_obj::gen_wrapped_diff_struct(input, s);
    let diff_impl = diff_fn::gen_diff_impl(&s.fields);
    DiffImpl {
        diff_assoc_type,
        diff_type,
        diff_impl,
    }
}
