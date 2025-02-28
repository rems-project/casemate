use log::*;

use casemate;
use casemate::transitions;

mod con;

fn main() {
    con::setup_loggers();

    info!("hello world");

    casemate::init_model(0, 0);
    casemate::configure(
        casemate::config::make_config_builder(
            "{
                \"printing\": {
                    \"dump\": true,
                    \"diff\": true
                }
            }",
        )
        .unwrap(),
    );

    info!("init'd");
    casemate::step_model(casemate::make_transition!(
        0,
        transitions::SrcLoc::new("<file>".into(), "<func>".into(), 0),
        transitions::Operation::InitMem(0.into(), 8)
    ));

    casemate::step_model(casemate::make_transition!(
        0,
        transitions::SrcLoc::new("<file>".into(), "<func>".into(), 1),
        transitions::Operation::MemSet {
            loc: 0.into(),
            size: 7,
            val: 12
        }
    ));

    casemate::step_model(casemate::make_transition!(
        0,
        transitions::SrcLoc::new("<file>".into(), "<func>".into(), 2),
        transitions::Operation::Write(0.into(), transitions::MemOrder::Plain, 42)
    ));
}
