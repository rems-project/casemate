use log::{self, LevelFilter, Log, Metadata, Record};

pub struct NullLogger;

impl NullLogger {
    pub const fn new() -> Self {
        Self {}
    }

    pub fn init(&'static self) {
        log::set_logger(self).expect("failed to init NullLogger");
        log::set_max_level(LevelFilter::Off);
    }
}

impl Log for NullLogger {
    fn enabled(&self, _metadata: &Metadata) -> bool {
        false
    }

    fn flush(&self) {}

    fn log(&self, _record: &Record<'_>) {}
}
