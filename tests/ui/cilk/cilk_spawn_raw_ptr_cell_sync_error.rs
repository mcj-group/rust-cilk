#![feature(cilk)]
// Tests that the pointee of a captured raw pointer must implement Sync. Cell only implements Send.

//@ check-fail
//@ compile-flags: -C panic=abort
//@ no-prefer-dynamic

use std::cell::Cell;

fn main() {
    let value = Cell::new(1_usize);
    let pointer: *const Cell<usize> = &value;

    cilk_spawn {
        unsafe {
            let _ = (*pointer).get();
            //~^ ERROR `Cell<usize>` cannot be shared between threads safely
        }
    };
}
