//! Generates [`Diffable`] implementations of structs
//!
//! ```edition2021
//! #[derive(Debug, Diffable)]
//! enum Bar {
//!     A,
//!     B(u64),
//! }
//!
//! let x = Bar::A;
//! let y = Bar::B(11);
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

    fn gen_diffed_variant(v: &syn::Variant) -> TokenStream {
        let ident = &v.ident;
        match &v.fields {
            syn::Fields::Unit => quote!(
                // Note trailing Comma!
                #ident,
            ),
            syn::Fields::Unnamed(unnamed) => {
                let wrapped = unnamed.unnamed.iter().map(|ty| {
                    let inner = &ty.ty;
                    quote!(
                        // Note trailing Comma!
                        diffable::InnerDiff<'diffl, #inner>,
                    )
                });
                let tys = TokenStream::from_iter(wrapped);
                quote!(
                    // Note trailing Comma!
                    #ident(#tys),
                )
            }
            syn::Fields::Named(_) => {
                panic!("cannot derive Diffable on enum with named fields");
            }
        }
    }

    fn gen_diffed_variants(edata: &syn::DataEnum) -> TokenStream {
        let vars: Vec<_> = Vec::from_iter(edata.variants.iter().map(gen_diffed_variant));

        TokenStream::from_iter(vars.into_iter())
    }

    /// Generates the wrapped [`Diffable::Diff`] object
    pub fn gen_wrapped_diff_enum(input: &syn::DeriveInput, edata: &syn::DataEnum) -> TokenStream {
        let diff_variants = gen_diffed_variants(edata);
        let diffty = names::gen_diff_type(input);
        quote!(
            enum #diffty {
                #diff_variants
            }
        )
    }
}

/// Generators for the [`Diffable::diff`] implementation
mod diff_fn {
    use proc_macro2::{Ident, Span, TokenStream};
    use quote::quote;
    use syn;

    fn match_arm_impl(var: &syn::Variant) -> TokenStream {
        match &var.fields {
            syn::Fields::Unit => {
                quote!(diffable::Difference::NoChange)
            }
            syn::Fields::Unnamed(unnamed) => {
                let n = unnamed.unnamed.len();
                let mkbinder = |prefix: &str, i: usize| {
                    Ident::new(format!("{prefix}{i}").as_str(), Span::call_site())
                };
                let diff_bindings = {
                    TokenStream::from_iter((0..n).map(|i| {
                        let d = mkbinder("d", i);
                        let x = mkbinder("x", i);
                        let y = mkbinder("y", i);
                        quote!(
                            let #d = #x.diff(#y);
                        )
                    }))
                };

                let ident = &var.ident;
                let diff_binders = TokenStream::from_iter((0..n).map(|i| {
                    let binder = mkbinder("d", i);
                    quote!(
                        // Note trailing comma
                        #binder,
                    )
                }));

                let or_has_changed_expansion = {
                    TokenStream::from_iter((0..n).map(|i| {
                        let d = mkbinder("d", i);
                        quote!(
                            || #d.has_changed()
                        )
                    }))
                };

                quote!(
                    #diff_bindings

                    if false #or_has_changed_expansion {
                        // Note that we _must_ be in the tuple form here
                        let d = Self::Diff::#ident(#diff_binders);
                        diffable::Difference::Updated(d)
                    } else {
                        diffable::Difference::NoChange
                    }
                )
            }
            syn::Fields::Named(_) => {
                panic!("cannot derive Diffable for enum with named fields");
            }
        }
    }

    /// Creates a `Pattern` which matches a given [`EnumVariant`]
    /// with bindings labelled `#prefix[0-9]+`
    fn var_pattern(prefix: &str, var: &syn::Variant) -> TokenStream {
        let name = &var.ident;
        match &var.fields {
            syn::Fields::Unit => quote!(
                Self::#name
            ),
            syn::Fields::Unnamed(unnamed) => {
                let n = unnamed.unnamed.len();
                let binders = (0..n).map(|i| {
                    let ident = format!("{prefix}{i}");
                    Ident::new(ident.as_str(), Span::call_site())
                });
                quote!(
                    Self::#name(#(#binders),*)
                )
            }
            syn::Fields::Named(_) => {
                panic!("cannot derive Diffable for an enum with named fields");
            }
        }
    }

    fn match_arm(var: &syn::Variant) -> TokenStream {
        let lhs = var_pattern("x", var);
        let rhs = var_pattern("y", var);
        let diff_impl = match_arm_impl(var);
        quote!(
            (#lhs, #rhs) => {
                #diff_impl
            },
        )
    }

    fn match_arms(edata: &syn::DataEnum) -> TokenStream {
        let symmetric_arms = {
            TokenStream::from_iter(edata.variants.iter().map(|v| {
                let arm = match_arm(v);
                quote!(
                    #arm
                )
            }))
        };

        quote!(
            #symmetric_arms
            (_, _) => {
                diffable::Difference::Changed(other, self)
            }
        )
    }

    pub fn gen_diff_impl(edata: &syn::DataEnum) -> TokenStream {
        let arms = match_arms(edata);
        quote!(
            match (self, other) {
                #arms
            }
        )
    }
}

/// Generates the struct-specific parts of the Diffable-derived implementation

/// The derive macro will generate a final implementation,
/// e.g. for the `Bar` enum example:
/// ```edition2021
/// #[derive(Debug)]
/// enum BarDiff<'l> {
///     A,
///     B(diffable::InnerDiff<'l, u64>),
/// }
///
/// impl<'l> diffable::Diffable<'l> for Bar {
///     type Diff = BarDiff<'l>;
///
///     fn diff(&'l self, other: &'l Self) -> diffable::Difference<&'l Self, Self::Diff> {
///         match (self, other) {
///             (Self::A, Self::A) => {
///                 diffable::Difference::NoChange
///             },
///             (Self::B(a), Self::B(b)) => {
///                 let d0 = a.diff(b);
///
///                 if d0.has_changed() {
///                     let d = Self::Diff::B(d0);
///                     diffable::Difference::Updated(d)
///                 } else {
///                     diffable::Difference::NoChange
///                 }
///             },
///             (_, _) => {
///                 diffable::Difference::Changed(other, self)
///             },
///         }
///     }
/// }
/// ```
pub fn generate_impl_diffable_enum(input: &syn::DeriveInput, edata: &syn::DataEnum) -> DiffImpl {
    let diff_assoc_type = names::gen_diff_type(input);
    let diff_type = diff_obj::gen_wrapped_diff_enum(input, edata);
    let diff_impl = diff_fn::gen_diff_impl(edata);
    DiffImpl {
        diff_assoc_type,
        diff_type,
        diff_impl,
    }
}
