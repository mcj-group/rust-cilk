#![feature(cilk)]
// Tests that a value captured by mutable reference must implement Send.

//@ check-fail
//@ compile-flags: -C panic=abort
//@ no-prefer-dynamic

use std::rc::Rc;

fn main() {
    let mut value = Rc::new(1_usize);
    cilk_spawn {
        value = Rc::new(2); //~ ERROR variable captured for Cilk parallel runtime is not thread-safe
    };
}
