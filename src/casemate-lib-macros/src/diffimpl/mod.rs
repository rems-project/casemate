use proc_macro2::TokenStream;
use quote::quote;
use syn;

use crate::names;

mod gen_enum;
mod gen_struct;

/// A wrapper around a generic Diffable implementation
///
pub struct DiffImpl {
    // TODO: BS: Replace these TokenStreams with actual `syn` ASTs
    /// The definition of the diff type
    pub diff_type: TokenStream,

    /// the `Diffable::Diff` associated type name
    pub diff_assoc_type: TokenStream,

    /// The implementation of the Diffable::diff
    pub diff_impl: TokenStream,
}

/// Produces a simple [`Diffable`] implementation
///
/// For structs and enums it replicates the fields, wrapping each in an [`InnerDiff`]
/// and auto-derives [`DisplayDiff`] for each
pub fn diffable(input: syn::DeriveInput) -> TokenStream {
    let ty: TokenStream = names::data_type(&input);

    let diff: DiffImpl = {
        match &input.data {
            syn::Data::Enum(e) => gen_enum::generate_impl_diffable_enum(&input, e),
            syn::Data::Struct(s) => gen_struct::generate_impl_diffable_struct(&input, s),
            _ => panic!("cannot derive Diffable on a union"),
        }
    };

    let diffds = diff.diff_type;
    let diffty = diff.diff_assoc_type;
    let diffimpl = diff.diff_impl;

    quote!(
        #[derive(Debug, diffable::DisplayDiff)]
        #[allow(dead_code)]
        #diffds

        impl<'diffl> diffable::Diffable<'diffl> for #ty {
            type Diff = #diffty;

            fn diff(&'diffl self, other: &'diffl Self) -> diffable::Difference<&'diffl Self, Self::Diff> {
                #diffimpl
            }
        }
    )
}
