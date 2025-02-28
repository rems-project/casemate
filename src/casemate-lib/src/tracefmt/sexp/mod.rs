//! Simple S-expr representations
//!
//! [`Sexp`] is a bare-bones S-expr type, where expressions are Stringified values or lists.
//!
//! [`Sexp`] instances come with `Display` implementations for pretty-printing
//! and the [`parse_sexpr`] function can be used to deserialize strings into [`Sexp`]

use crate::shim::*;

mod de;
pub use de::{parse_sexpr, SexpParseError};

mod ser;

#[derive(Debug)]
pub enum Sexp {
    Val(String),
    List(Vec<Sexp>),
}

impl From<String> for Sexp {
    fn from(value: String) -> Self {
        Self::Val(value)
    }
}

impl From<Vec<Sexp>> for Sexp {
    fn from(value: Vec<Sexp>) -> Self {
        Self::List(value)
    }
}

impl Sexp {
    pub fn list<T>(val: Vec<T>) -> Self
    where
        T: Into<Sexp>,
    {
        Self::List(val.into_iter().map(|v| v.into()).collect())
    }

    pub fn value(val: String) -> Self {
        Self::Val(val)
    }

    #[allow(dead_code)]
    pub fn expect_list(&self) -> Option<&Vec<Sexp>> {
        match self {
            Sexp::Val(_) => None,
            Sexp::List(xs) => Some(xs),
        }
    }

    pub fn expect_value(&self) -> Option<&String> {
        match self {
            Sexp::Val(s) => Some(s),
            Sexp::List(_) => None,
        }
    }
}
