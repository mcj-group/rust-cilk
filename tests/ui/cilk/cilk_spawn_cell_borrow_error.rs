#![feature(cilk)]
// Cell implements Send but not Sync, thus is only usable in a task if ownership is transfered.

//@ check-fail
//@ compile-flags: -C panic=abort
//@ no-prefer-dynamic

use std::cell::Cell;

fn main() {
    let cell = Cell::new(0);
    cilk_spawn {
        // makes reference without transfering ownersihp
        cell.replace(1); //~ ERROR `Cell<i32>` cannot be shared between threads safely
    };
}
