use crate::shim::*;

/// Errors bubble out of each layer and are each given an error code:
/// e.g. E10100
///
/// E0XXXXX  are generic system errors
/// E1XXXXX  arise from the layer step
/// E10XXXX  are generic step errors
/// E11XXXX  are machine-layer errors
/// E12XXXX  are pgtable-layer errors
#[derive(Debug, Clone, Copy)]
#[allow(non_camel_case_types)]
#[allow(dead_code)]
pub enum Error<'t> {
    // E0... are system errors
    E00000_UnknownError,

    // E1... are layer errors

    // E10... are generic step errors
    E10001_MisalignedAccess(&'t str),

    // E11... are machine::Machine layer errors
    E11000_BadRead {
        address: u64,
        expected: u64,
        actual: u64,
    },
    E11001_UninitialisedAccess {
        address: u64,
    },
    E11002_UnknownRegister {
        regname: &'t str,
    },
    E11003_BadMemSetArguments,
}

impl<'t> Error<'t> {
    pub fn error_code(&self) -> &'static str {
        use Error::*;
        match self {
            E00000_UnknownError => "E00000",
            E10001_MisalignedAccess(_) => "E10001",
            E11000_BadRead {
                address: _,
                expected: _,
                actual: _,
            } => "E11000",
            E11001_UninitialisedAccess { address: _ } => "E11001",
            E11002_UnknownRegister { regname: _ } => "E11002",
            E11003_BadMemSetArguments => "E11003",
        }
    }

    pub fn error_short_name(&self) -> &'static str {
        use Error::*;
        match self {
            E00000_UnknownError => "Unknown Error",
            E10001_MisalignedAccess(_) => "Misaligned Access",
            E11000_BadRead {
                address: _,
                expected: _,
                actual: _,
            } => "Bad Name",
            E11001_UninitialisedAccess { address: _ } => "Uninitialised Access",
            E11002_UnknownRegister { regname: _ } => "Unknown Register",
            E11003_BadMemSetArguments => "Malformed memset() call",
        }
    }

    pub fn error_data(&self) -> Vec<String> {
        use Error::*;
        match self {
            E00000_UnknownError => vec![],
            E10001_MisalignedAccess(a) => vec![a.to_string()],
            E11000_BadRead {
                address,
                expected,
                actual,
            } => {
                vec![
                    format!("address={address}"),
                    format!("expected={expected}"),
                    format!("actual={actual}"),
                ]
            }
            E11001_UninitialisedAccess { address } => vec![format!("address={address}")],
            E11002_UnknownRegister { regname } => vec![regname.to_string()],
            E11003_BadMemSetArguments => vec![],
        }
    }
}

impl<'t> fmt::Display for Error<'t> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "{}: error: {}",
            self.error_code(),
            self.error_short_name()
        )?;
        let data = self.error_data();
        if !data.is_empty() {
            let mut datas: Vec<String> = vec![];
            let sep = ", ".to_string();
            let mut first = true;

            for err in data {
                if !first {
                    datas.push(sep.clone());
                }
                datas.push(err);
                first = false;
            }
            let datastr: String = datas.concat();
            write!(f, ": {}", datastr)?;
        }
        Ok(())
    }
}
