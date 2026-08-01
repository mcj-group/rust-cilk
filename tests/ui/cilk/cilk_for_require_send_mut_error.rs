#![feature(cilk)]
// Tests that a value mutably captured by a cilk_for must implement Send.

//@ check-fail
//@ compile-flags: -C panic=abort
//@ no-prefer-dynamic

use std::rc::Rc;

fn main() {
    let mut value = Rc::new(1_usize);
    cilk_for _i in 0..2 {
        value = Rc::new(2); //~ ERROR `Rc<usize>` cannot be sent between threads safely
    }
}
