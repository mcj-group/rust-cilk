#![feature(cilk)]
// A `cilk_for` body that consumes (moves) a captured local.
//
// The loop body takes ownership of `s` via `drop(s)`, but the body runs once
// per iteration, so the move would happen repeatedly on a value that only
// exists once.
//
// EXPECTED: rejected with E0382 because `s` is moved out of the parent in a
// body that executes more than once.

//@ compile-flags: -C panic=abort
//@ no-prefer-dynamic

fn main() {
    let s = String::new();
    cilk_for i in 0..10 {
                    //~^ ERROR use of moved value: `s` [E0382]
        drop(s);
    };
}
