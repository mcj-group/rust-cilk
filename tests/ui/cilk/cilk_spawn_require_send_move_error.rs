#![feature(cilk)]
// Tests that a value moved into a cilk_spawn must implement Send.

//@ check-fail
//@ compile-flags: -C panic=abort
//@ no-prefer-dynamic

use std::rc::Rc;

fn main() {
    let value = Rc::new(1_usize);
    cilk_spawn {
        drop(value); //~ ERROR `Rc<usize>` cannot be sent between threads safely
    };
}
