use crate::shim::*;

use crate::transitions::Transition;

pub mod sexp;

mod parser;
pub use parser::parse_trace_sexpevent;
pub use parser::TraceParseError;

mod pretty_printer;
use pretty_printer::emit_trace_sexpevent;

pub fn emit_trace_event(t: &Transition) -> String {
    let sexp = emit_trace_sexpevent(t);
    sexp.to_string()
}
