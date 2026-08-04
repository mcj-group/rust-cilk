#![feature(cilk)]
// Tests that a value captured by shared reference must implement Sync.

//@ check-fail
//@ compile-flags: -C panic=abort
//@ no-prefer-dynamic

use std::cell::RefCell;
use std::rc::Rc;

fn main() {
    let value = Rc::new(RefCell::new(1_usize));
    cilk_spawn {
        let value = Rc::clone(&value); //~ ERROR `Rc<RefCell<usize>>` cannot be shared between threads safely
        value.replace_with(|n| *n + 1);
    };
}
