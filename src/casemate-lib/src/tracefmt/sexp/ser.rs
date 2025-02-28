use crate::shim::*;

use super::Sexp;

impl fmt::Display for Sexp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Val(s) => write!(f, "{}", s),
            Self::List(vs) => {
                write!(f, "(")?;
                let mut first = true;
                for v in vs {
                    if !first {
                        write!(f, " ")?;
                    }
                    write!(f, "{}", v)?;
                    first = false;
                }
                write!(f, ")")
            }
        }
    }
}
