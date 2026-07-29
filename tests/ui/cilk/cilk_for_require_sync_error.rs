#![feature(cilk)]
// Tests that a value shared within cilk_for must implement Sync.

//@ check-fail
//@ compile-flags: -C panic=abort
//@ no-prefer-dynamic

use std::cell::RefCell;
use std::rc::Rc;

fn main() {
    let value = Rc::new(RefCell::new(1_usize));

    cilk_for _i in 0..1 {
        let value = Rc::clone(&value); //~ ERROR variable captured for Cilk parallel runtime is not thread-safe
        value.replace_with(|n| *n + 1);
    }
}
