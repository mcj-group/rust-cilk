#![feature(cilk)]
// Tests that Send/Sync trait will not be checked for raw ptrs nor its pointee.

//@ check-pass
//@ compile-flags: -C panic=abort
//@ no-prefer-dynamic

use std::cell::Cell;

fn main() {
    let value = Cell::new(1_usize);
    let pointer: *const Cell<usize> = &value;

    cilk_spawn {
        unsafe {
            let _ = (*pointer).get();
        }
    };
}
