use crate::shim::*;

use crate::transitions::Transition;

mod sexp;
// mod parser;
mod pretty_printer;

pub fn to_sexpr(t: &Transition) -> String {
    let sexp: sexp::Sexp = t.into();
    sexp.to_string()
}
