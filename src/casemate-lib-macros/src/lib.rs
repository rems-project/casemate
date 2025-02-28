// This `extern` is required for older `rustc` versions but newer `rustc`
// versions warn about the unused `extern crate`.
#[allow(unused_extern_crates)]
extern crate proc_macro;

use proc_macro::TokenStream;
use syn::{parse_macro_input, DeriveInput};


mod coded_error;

#[proc_macro_derive(CodedError, attributes(coded_error))]
pub fn derive_diffable(annotated_item: TokenStream) -> TokenStream {
    let ds = parse_macro_input!(annotated_item as DeriveInput);
    match &ds.data {
        syn::Data::Enum(e) => coded_error::generate_impl(&ds, e),
        _ => panic!("cannot derive CodedError on a struct or union"),
    }.into()
}
