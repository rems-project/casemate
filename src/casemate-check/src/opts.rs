use getopts::Options;

pub fn opts() -> Options {
    let mut opts = Options::new();
    opts.optflag("h", "help", "print this help message");
    opts.optflag("", "version", "print out version and stop.");
    // actual log files are free
    opts
}
