//! Simple logging instance
//!
//! [`ConsoleLogger`] provides a simple [log] instance but reasonably decent looking

use log::{self, Level, LevelFilter, Log, Metadata, Record};

#[cfg(feature = "std")]
use std::time::Instant;

use crate::shim::cell;
use crate::shim::fmt;
use crate::shim::str;
use crate::shim::sync;
use crate::shim::ToString;

/// A simple Logger instance for printing records to stdout/the UART
///
/// Provides a generic interface for different `Write`rs to produce the same records
pub struct ConsoleLogger<W>
where
    W: fmt::Write,
{
    /// The actual fmt::Write instance
    ///
    /// - we cannot use io::Write in no_std
    /// - it must have inner mutability to be usable, so we wrap in an UnsafeCell
    /// - we need to be able to construct a static version,
    ///   and thus need a const initialiser, so we make it optional
    write: cell::UnsafeCell<Option<W>>,
    level: LevelFilter,

    /// The last log Level that was recorded
    /// so we can skip printing redundant info
    last_level_written: sync::atomic::AtomicUsize,

    #[cfg(feature = "std")]
    start: Option<Instant>,
}

unsafe impl<W: fmt::Write + Send + Sync> Send for ConsoleLogger<W> {}
unsafe impl<W: fmt::Write + Send + Sync> Sync for ConsoleLogger<W> {}

pub fn prefix(lvl: Level) -> &'static str {
    use Level::*;
    match lvl {
        Error => "ERROR",
        Warn => "WARN",
        Info => "INFO",
        Debug => "DEBUG",
        Trace => "TRACE",
    }
}

#[allow(dead_code)]
#[derive(Copy, Clone, Debug)]
enum Color {
    // 8-bit colors
    Black,
    Red,
    Green,
    Yellow,
    Blue,
    Magenta,
    Cyan,
    White,

    // Some particular 256-bit colors
    Grey256,
}

macro_rules! ANSI_ESC {
    () => {
        "\x1b"
    };
}

macro_rules! ANSI_CSI {
    () => {
        concat!(ANSI_ESC!(), "[")
    };
}

macro_rules! ANSI_SGR {
    ($n:literal) => {
        concat!(ANSI_CSI!(), $n, "m")
    };
    (extended:$n:literal) => {
        concat!(ANSI_CSI!(), 38, ";", 5, ";", $n, "m")
    };
    (rgb:$r:literal;$g:literal;$b:literal) => {
        concat!(ANSI_CSI!(), 38, ";", 2, ";", $r, ";", $g, ";", $b, "m")
    };
}

macro_rules! ANSI_SGR_RESET {
    () => {
        ANSI_SGR!(0)
    };
}

impl Color {
    fn ansi_start(&self) -> &'static str {
        use Color::*;
        match self {
            Black => ANSI_SGR!(30),
            Red => ANSI_SGR!(31),
            Green => ANSI_SGR!(32),
            Yellow => ANSI_SGR!(33),
            Blue => ANSI_SGR!(34),
            Magenta => ANSI_SGR!(35),
            Cyan => ANSI_SGR!(36),
            White => ANSI_SGR!(37),
            Grey256 => ANSI_SGR!(extended:242),
        }
    }

    fn ansi_end(&self) -> &'static str {
        ANSI_SGR_RESET!()
    }

    fn from_level(lvl: Level) -> Self {
        use Color::*;
        use Level::*;
        match lvl {
            Error => Red,
            Warn => Yellow,
            Info => Green,
            Debug => Black,
            Trace => Grey256,
        }
    }
}

// struct Colorized<'s>(Color, &'s str);

// impl<'s> fmt::Debug for Colorized<'s> {
//     fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
//         f.write_str(self.0.ansi_start())?;
//         f.write_str(self.1);
//         f.write_str(self.0.ansi_end())
//     }
// }

/// Convert back from usized-`Level as usize` into a Level
///
/// This works because log::Level is defined as #[repr(usize)]
/// and this function below is reproduced from an (internal) method on Level
fn level_from_usize(u: usize) -> Option<Level> {
    match u {
        1 => Some(Level::Error),
        2 => Some(Level::Warn),
        3 => Some(Level::Info),
        4 => Some(Level::Debug),
        5 => Some(Level::Trace),
        _ => None,
    }
}

impl<W> ConsoleLogger<W>
where
    W: fmt::Write,
    W: Send + Sync,
{
    pub const fn new() -> Self {
        Self {
            write: cell::UnsafeCell::new(None),
            level: LevelFilter::Info,
            last_level_written: sync::atomic::AtomicUsize::new(0),
            #[cfg(feature = "std")]
            start: None,
        }
    }

    pub fn set_level(&mut self, lvl: LevelFilter) {
        self.level = lvl;
    }

    #[cfg(feature = "std")]
    pub fn start_now(&mut self) {
        self.start = Some(Instant::now());
    }

    /// Install as the current logger
    ///
    /// This requires a static reference to be compatible with the no_std log interface
    pub fn init(&'static self) {
        log::set_logger(self).expect("failed to init ConsoleLogger");
        log::set_max_level(self.level);
    }

    fn writer<'w>(&'w self) -> &'w mut W {
        let writer: *mut Option<W> = self.write.get();
        let writer: &mut Option<W> = unsafe { writer.as_mut().unwrap() };
        let writer: &mut W = writer.as_mut().unwrap();
        writer
    }

    fn write_header(&self, fmt: &mut W, meta: &Metadata<'_>) -> fmt::Result {
        let level = meta.level();

        #[cfg(feature = "std")]
        {
            use std::time::Instant;
            if let Some(start) = self.start {
                let now = Instant::now();
                let dur = now.duration_since(start);
                let s = dur.as_secs();
                let ms = dur.as_millis() % 1000;
                fmt.write_str(Color::Grey256.ansi_start())?;
                write!(fmt, "[{:>6}.{:<03}] ", s, ms)?;
                fmt.write_str(Color::Grey256.ansi_end())?;
            }
        }

        // fmt.write_str(self.indent(false));

        let fg = Color::from_level(level);

        fmt.write_str(fg.ansi_start())?;
        let prefix = {
            let last_read = self
                .last_level_written
                .load(sync::atomic::Ordering::Relaxed);
            if level_from_usize(last_read) == Some(level) {
                "..."
            } else {
                prefix(level)
            }
        };
        write!(fmt, "{:>4}", prefix)?;
        fmt.write_str(fg.ansi_end())?;
        fmt.write_str(" ")?;
        Ok(())
    }

    fn write_line(&self, fmt: &mut W, line: &str, indent: bool) -> fmt::Result {
        if indent {
            fmt.write_str("                   ")?;
        }

        fmt.write_str(line)?;
        fmt.write_char('\n')
    }

    fn write_body(&self, fmt: &mut W, body: &fmt::Arguments) -> fmt::Result {
        body.to_string()
            .lines()
            .enumerate()
            .map(|(i, s)| self.write_line(fmt, s, i > 0))
            .collect::<fmt::Result>()
    }

    fn write_kvs(&self, _fmt: &mut W, kvs: &dyn log::kv::Source) -> fmt::Result {
        let mut visitor = ConsoleKV(self);
        kvs.visit(&mut visitor).map_err(|_| fmt::Error)
    }

    fn write_message(&self, fmt: &mut W, record: &Record<'_>) -> fmt::Result {
        self.write_header(fmt, &record.metadata())?;
        self.write_body(fmt, record.args())?;
        self.write_kvs(fmt, record.key_values())?;
        Ok(())
    }
}

struct ConsoleKV<'l, W>(&'l ConsoleLogger<W>)
where
    W: fmt::Write,
    W: Send + Sync;

impl<'l, 'kvs, W> log::kv::VisitSource<'kvs> for ConsoleKV<'l, W>
where
    W: fmt::Write,
    W: Send + Sync,
{
    fn visit_pair(
        &mut self,
        key: log::kv::Key<'kvs>,
        value: log::kv::Value<'kvs>,
    ) -> Result<(), log::kv::Error> {
        let writer: &mut W = self.0.writer();
        let k = key.as_str();
        self.0
            .write_body(writer, &format_args!("{} = {}", k, value))
            .unwrap();
        Ok(())
    }
}

impl<W> ConsoleLogger<W>
where
    W: fmt::Write + 'static,
{
    pub fn fill(&mut self, fmt: W) {
        let b = self.write.get_mut();
        *b = Some(fmt);
    }
}

impl<W> Log for ConsoleLogger<W>
where
    W: fmt::Write,
    W: Send + Sync,
{
    fn enabled(&self, _metadata: &Metadata) -> bool {
        true
    }

    fn flush(&self) {}

    fn log(&self, record: &Record<'_>) {
        let writer = self.writer();
        self.write_message(writer, record).unwrap();
        self.last_level_written.store(
            record.metadata().level() as usize,
            sync::atomic::Ordering::Relaxed,
        );
    }
}
