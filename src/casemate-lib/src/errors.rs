use crate::model::layers::machine::MachineError;
use crate::model::layers::pgtable::PgtableError;
use crate::shim::ToString;
use crate::shim::*;

use crate::tracefmt::TraceParseError;

pub enum ErrorKind {
    Error,
    Warning,
}

/// Errors with an E-code
pub trait CodedError: StdError {
    /// Whether this is a hard error or a warning
    fn kind(&self) -> ErrorKind {
        match self.error_code().chars().nth(0) {
            Some('E') => ErrorKind::Error,
            Some('W') => ErrorKind::Warning,
            _ => panic!("cannot compute error kind from {}", self.error_code()),
        }
    }

    /// the code number for this error
    ///
    /// wrapped errors should propagate the inner code:
    /// e.g. InnerErr.error_code() = "E0001"
    ///      Outer(InnerErr).error_code() = InnerErrr.error_code()
    fn error_code(&self) -> &'static str;
}

/// Errors bubble out of each layer and are each given an error code:
/// e.g. E10100
///
/// E0XXXXX  are generic system errors
/// E1XXXXX  arise from the layer step
/// E10XXXX  are generic step errors
/// E11XXXX  are machine-layer errors
/// E12XXXX  are pgtable-layer errors
///
/// at the core of this is the [`CasemateError`]
/// which is a tagged union of the various kinds of errors from the Casemate model
#[derive(Debug, Clone)]
#[allow(non_camel_case_types)]
#[allow(dead_code)]
pub enum CasemateError {
    // E0... are generic system errors
    UnknownError,
    ConfigurationError(String),
    TraceParseError(TraceParseError),

    // E1... are layer errors
    // E11... are machine::Machine layer errors
    StepMachineError(MachineError),

    // E12... are pgtable::Pgtable layer errors
    StepPgtableError(PgtableError),
}

impl CasemateError {
    pub fn from_mach_err(err: MachineError) -> Self {
        Self::StepMachineError(err)
    }

    pub fn from_pgtable_err(err: PgtableError) -> Self {
        Self::StepPgtableError(err)
    }
}

impl fmt::Display for CasemateError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::UnknownError => write!(f, "unknown error"),
            Self::ConfigurationError(e) => write!(f, "error configuring Casemate: {e}"),
            Self::TraceParseError(e) => write!(f, "error parsing trace event: {e}"),
            Self::StepMachineError(e) => write!(f, "error stepping Machine layer: {e}"),
            Self::StepPgtableError(e) => write!(f, "error stepping Pgtable layer: {e}"),
        }
    }
}

impl StdError for CasemateError {}

impl CodedError for CasemateError {
    fn error_code(&self) -> &'static str {
        match self {
            Self::UnknownError => "E0000",
            Self::ConfigurationError(_) => "E0005",
            Self::TraceParseError(_) => "E0006",
            Self::StepMachineError(e) => e.error_code(),
            Self::StepPgtableError(e) => e.error_code(),
        }
    }
}
