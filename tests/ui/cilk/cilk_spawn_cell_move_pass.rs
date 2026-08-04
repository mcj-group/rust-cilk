#![feature(cilk)]
// Cell implements Send but not Sync, thus is only usable in a task if ownership is transfered.

//@ check-pass
//@ compile-flags: -C panic=abort
//@ no-prefer-dynamic

use std::cell::Cell;

fn main() {
    let cell = Cell::new(0);
    cilk_spawn {
        // forces transfer of ownership
        let cell = cell;
        cell.replace(1);
    };
}
