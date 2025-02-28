use crate::shim::*;

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
}

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
