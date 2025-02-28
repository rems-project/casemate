use alloc::vec::Vec;

use crate::overlays::{Layer, machine};

struct Counter<'m> {
  parent: &'m machine::Machine,
}

impl<'s> Layer for Counter<'s> {
  fn parent<'s>(&'s self) -> Option<&'s dyn Layer> {
    Some(self.parent)
  }

  fn step(self, t: transitions::Operation, parents: Vec<Layer>) {
    
  }
}