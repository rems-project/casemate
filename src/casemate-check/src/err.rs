use casemate;

use std::io;

/// An error from running `casemate-check`
pub enum CheckError {
    /// An internal error from the casemate model
    TraceError(casemate::CasemateError),

    /// Some std::io error from the wrapper casemate-check machinery
    IOError(io::Error),

    /// Model said yes when log said no
    ModelMismatch(String),
}

impl Into<CheckError> for io::Error {
    fn into(self) -> CheckError {
        CheckError::IOError(self)
    }
}

impl Into<CheckError> for casemate::CasemateError {
    fn into(self) -> CheckError {
        CheckError::TraceError(self)
    }
}
