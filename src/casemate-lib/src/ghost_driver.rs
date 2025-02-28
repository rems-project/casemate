#![cfg(not(feature = "std"))]

use crate::shim::*;

use crate::c_api;

use crate::loggers::NullLogger;

static mut CASEMATE_LOGGER: NullLogger = NullLogger::new();

static mut GHOST: c_api::ghost_driver = c_api::ghost_driver {
    writeb: None as c_api::write_byte_cb,
    abort: None as c_api::abort_cb,
    trace: None as c_api::trace_cb,
};

#[allow(static_mut_refs)]
pub fn sync_ghost_driver(driver: *const c_api::ghost_driver) {
    unsafe {
        GHOST = *driver;
        CASEMATE_LOGGER.init();
    }
}

#[no_mangle]
pub fn abort(msg: &'static str) -> ! {
    unsafe {
        if let Some(ghost_abort) = GHOST.abort {
            let cmsg = CString::new(msg).unwrap();
            ghost_abort(cmsg.into_raw());
        }
    }

    loop {}
}

pub struct GhostOut {
    driver: &'static mut c_api::ghost_driver,
}

#[allow(dead_code)]
#[allow(static_mut_refs)]
pub fn stdout() -> GhostOut {
    unsafe { GhostOut { driver: &mut GHOST } }
}

impl fmt::Write for GhostOut {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        if let Some(writeb) = self.driver.writeb {
            for b in s.as_bytes().iter() {
                unsafe {
                    writeb(*b);
                }
            }
        }
        Ok(())
    }
}

#[macro_export]
macro_rules! print {
  ($($arg:tt)*) => {
    write!($crate::ghost_driver::stdout(), $($arg)*)
      .unwrap()
  };
}

#[macro_export]
macro_rules! println {
  ($($arg:tt)*) => {
    writeln!($crate::ghost_driver::stdout(), $($arg)*)
      .unwrap()
  };
}
