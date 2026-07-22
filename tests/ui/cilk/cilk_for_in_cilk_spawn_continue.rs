#![feature(cilk)]
// Tests that a nested cilk_for handles its own continue inside a cilk_spawn.

//@ run-pass
//@ check-run-results
//@ compile-flags: -C panic=abort
//@ no-prefer-dynamic

fn main() {
    cilk_spawn {
        'inner: cilk_for i in 0..1 {
            if i == 0 {
                continue 'inner;
            }
            println!("Should not reach here.");
        }
    };
    cilk_sync;

    println!("done");
}
