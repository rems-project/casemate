use getopts::Options;
use log::*;

use std::env;
use std::fs;
use std::io::{self, BufRead};
use std::path::PathBuf;

use casemate;

mod con;
mod err;
use err::CheckError;

mod opts;

/// The default initial configuration used by casemate-check
static CONFIG: &'static str = "
    {
        \"printing\": {
            \"on\": true,
            \"dump\": false,
            \"diff\": true
        }
    }";

/// Run the casemate model over a log contained in a file
fn run_on(log_path: &PathBuf) -> Result<(), err::CheckError> {
    casemate::init_model(0, 0);
    casemate::configure(CONFIG).unwrap();

    let f = fs::File::open(log_path).map_err(CheckError::IOError)?;
    let reader = io::BufReader::new(f);

    for line in reader.lines() {
        let traceev: String = line.map_err(CheckError::IOError)?;

        if traceev.starts_with("!") {
            return Err(CheckError::ModelMismatch(traceev));
        }

        casemate::step_model_traceevent(&traceev).map_err(CheckError::TraceError)?;
    }

    Ok(())
}

fn print_usage_and_exit(program: &str, opts: Options) {
    let brief = format!("Usage: {} FILE [options]", program);
    print!("{}", opts.usage(&brief));
    std::process::exit(0);
}

fn print_version_and_exit() {
    println!("{}", casemate::VERSION);
    std::process::exit(0);
}

fn main() {
    con::setup_loggers();

    let args: Vec<String> = env::args().collect();
    let program = args[0].clone();

    let opts = opts::opts();
    let matches = match opts.parse(&args[1..]) {
        Ok(m) => m,
        Err(e) => {
            panic!("{}", e)
        }
    };

    if matches.opt_present("help") {
        print_usage_and_exit(&program, opts);
    } else if matches.opt_present("version") {
        print_version_and_exit();
    }

    info!("Running Model");
    let log_paths = matches.free.iter().map(PathBuf::from);

    for log_path in log_paths {
        match run_on(&log_path) {
            Ok(()) => (),
            Err(e) => {
                match e {
                    CheckError::ModelMismatch(s) => {
                        let s = s.strip_prefix("! ").unwrap_or("N/A");
                        error!(
                            "model mismatch: trace expected '{}', but was accepted without error",
                            s
                        );
                    }
                    CheckError::IOError(e) => {
                        error!("{}", e);
                    }
                    CheckError::TraceError(e) => {
                        error!("{}", e);
                    }
                }

                std::process::exit(-1);
            }
        }
    }

    info!("Done");
}
