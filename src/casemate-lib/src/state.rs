use crate::shim::*;

use crate::config::{de::make_config_builder, Config};
use crate::model::{Ctx, Model, VisitedLayers};

use crate::tracefmt::{self, sexp, TraceParseError};
use crate::transitions::Transition;
use crate::CasemateError;

struct CasemateState {
    model: Option<Model>,
    config: Config,
}

static mut STATE: CasemateState = CasemateState {
    model: None,
    config: Config::new(),
};

/// Initialise the casemate model
///
/// Installs a fresh [`Model`] instance into the global state.
/// Can re-initialise, deleting all previously known state.
#[allow(static_mut_refs)]
pub fn init_model(_phys_start: u64, _phys_size: u64) {
    unsafe {
        STATE = CasemateState {
            model: Some(Model::new()),
            config: STATE.config.clone(),
        };
    }
}

/// Configure the Casemate model
///
/// Takes a JSON-encoded string in a format accepted by the [`config`] module
/// and applies a partial configuration to the state incrementally.
///
#[allow(static_mut_refs)]
pub fn configure(config: &str) -> Result<(), CasemateError> {
    match make_config_builder(config) {
        Ok(builder) => unsafe {
            builder.apply(&mut STATE.config);
            Ok(())
        },
        Err(e) => Err(CasemateError::ConfigurationError(format!(
            "failed to parse JSON-encoded config: {:?}",
            e
        ))),
    }
}

pub fn is_initialised() -> bool {
    #[allow(static_mut_refs)]
    let m = unsafe { &STATE };

    m.model.is_some()
}

#[allow(static_mut_refs)]
unsafe fn __step_model(t: Transition) {
    panic!("foo");
    let st = unsafe { &mut STATE };
    let model = st
        .model
        .as_mut()
        .expect("__step_model assumes initialised model");

    let mut ctx = Ctx {
        snapshot: None,
        below: VisitedLayers::empty(),
        t: t,
        config: &st.config,
    };
    let res = model.step(&mut ctx);

    match res {
        Ok(()) => (),
        Err(e) => {
            // TODO: eventually make this return an error number?
            panic!("! step failed: {}", e);
        }
    }
}

pub fn step_model(t: Transition) {
    if is_initialised() {
        unsafe {
            __step_model(t);
        }
    }
}

/// Take a step in the model
///
/// Takes a transition as a string formatted in the [trace-format]
pub fn step_model_traceevent(s: &str) -> Result<(), CasemateError> {
    let sexp = sexp::parse_sexpr(s)
        .map_err(TraceParseError::BadSexp)
        .map_err(CasemateError::TraceParseError)?;
    let t = tracefmt::parse_trace_sexpevent(&sexp).map_err(CasemateError::TraceParseError)?;
    step_model(t);
    Ok(())
}

#[allow(static_mut_refs)]
pub fn update_model_with_step<'t, T>(t: T)
where
    T: FnOnce() -> Transition<'t>,
{
    if is_initialised() {
        unsafe {
            __step_model(t());
        }
    }
}
