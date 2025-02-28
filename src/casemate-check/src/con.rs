use std::fmt;
use std::io::Write;

use casemate;
use casemate::loggers::ConsoleLogger;

static mut LOGGER: ConsoleLogger<StdoutWriter> = ConsoleLogger::new();

pub struct StdoutWriter {
    f: std::io::Stdout,
}

impl StdoutWriter {
    pub fn new() -> Self {
        Self {
            f: std::io::stdout(),
        }
    }
}

impl fmt::Write for StdoutWriter {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.f.write_all(s.as_bytes()).unwrap();
        Ok(())
    }
}

#[allow(static_mut_refs)]
pub fn setup_loggers() {
    let log = unsafe { &mut LOGGER };

    log.fill(StdoutWriter::new());
    log.set_level(log::LevelFilter::Trace);
    log.start_now();
    log.init();
}
