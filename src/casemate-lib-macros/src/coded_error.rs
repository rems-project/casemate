
use proc_macro2::TokenStream;
use quote::quote;
use syn;

struct CodedErrorEnumVar {
    is_error: bool,
    error_code: u64,
    short_name: &'static str,
}

struct CodedErrorEnumData {
    fields: Vec<CodedErrorEnumVar>,
}

fn coded_var(var: &syn::Variant) -> CodedErrorEnumVar {
    let mut coded = CodedErrorEnumVar {
        is_error: true,
        error_code: 0u64,
        short_name: "",
    };

    for attr in var.attrs {
        match attr.meta {
            syn::Meta::List(ml) if ml.path.is_ident("error_code") => {
                // error_code(0123, warning=True, message="blah")
                let args = syn::parse_macro_input!(ml.tokens as syn::Punctuated<syn::Expr, syn::Token![,]);
                panic!()
            },
            _ => (),
        }
    }

    coded
}

fn coded_edata_from_derive(edata: &syn::DataEnum) -> CodedErrorEnumData {
    let fields =
        edata.variants.iter().map(|var| coded_var(var)).collect();
    CodedErrorEnumData { fields }
}

pub fn generate_impl(input: &syn::DeriveInput, edata: &syn::DataEnum) -> TokenStream {
    quote!(
        impl casemate::errors::CodedError for Foo {
            fn error_code(&self) -> u64 {

            }
        }
    )
}