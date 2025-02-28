use crate::shim::*;

use crate::base_model::{Ctx, Model, VisitedLayers};
use crate::config::{de::ConfigBuilder, Config};

use crate::transitions::Transition;

struct CasemateState {
    model: Option<Model>,
    snapshot: Option<Model>,
    config: Config,
}

static mut STATE: CasemateState = CasemateState {
    model: None,
    snapshot: None,
    config: Config::new(),
};

#[allow(static_mut_refs)]
pub fn init_model(_phys_start: u64, _phys_size: u64) {
    unsafe {
        STATE = CasemateState {
            model: Some(Model::new()),
            snapshot: Some(Model::new()),
            config: STATE.config.clone(),
        };
    }
}

#[allow(static_mut_refs)]
pub fn configure(builder: ConfigBuilder) {
    unsafe {
        builder.apply(&mut STATE.config);
    }
}

pub fn is_initialised() -> bool {
    #[allow(static_mut_refs)]
    let m = unsafe { &STATE };

    m.model.is_some()
}

#[allow(static_mut_refs)]
unsafe fn __step_model(t: Transition) {
    let st = unsafe { &mut STATE };
    let model = st
        .model
        .as_mut()
        .expect("__step_model assumes initialised model");
    let snapshot = st
        .snapshot
        .as_mut()
        .expect("__step_model assumes initialised snapshot");

    *snapshot = model.clone();

    let mut ctx = Ctx {
        snapshot: &snapshot,
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
