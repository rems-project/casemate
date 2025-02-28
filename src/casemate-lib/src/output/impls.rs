//! This module defines some helpful [`LayerFormat`] instances for some data structures

use crate::shim::*;

use super::{LayerFormat, LayerFormatter};

// Ideally we'd implement this for every I where &I: IntoIterator<Item: Display>
// and get a generic printer for borrowed iterables
//
// However, Rust does not like these bounds, i.e.:
// ```edition2021
// impl<'a, I> LayerFormat for I
// where
//     &'a I: IntoIterator<Item: fmt::Display>,
// {
//     fn fmt_layer(&self, f: &mut LayerFormatter<'_, '_>) -> fmt::Result {
//         let mut empty = true;
//         let iter = self.into_iter(); // error: lifetime may not live long enough
//         ...
//     }
// }
// ```
//
// so, we implement just for Vec:
//
impl<T> LayerFormat for Vec<T>
where
    T: fmt::Display,
{
    fn fmt_layer(&self, f: &mut LayerFormatter<'_, '_>) -> fmt::Result {
        let mut empty = true;
        let iter = self.into_iter();
        for e in iter {
            write!(f, "{e}\n")?;
            empty = false;
        }
        if empty {
            write!(f, "(nil)\n")?;
        }
        Ok(())
    }
}
