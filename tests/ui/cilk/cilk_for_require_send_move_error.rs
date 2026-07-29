#![feature(cilk)]
// Tests that induction variable requires Send trait in cilk_for

//@ check-fail
//@ compile-flags: -C panic=abort
//@ no-prefer-dynamic

use std::rc::Rc;

fn main() {
    let values = vec![Rc::new(1_usize)];
    cilk_for value in values {
             //~^ ERROR variable captured for Cilk parallel runtime is not thread-safe
        drop(value);
    }
}
