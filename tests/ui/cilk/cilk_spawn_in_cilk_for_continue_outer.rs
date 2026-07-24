#![feature(cilk)]
// Tests that a cilk_spawn cannot continue its enclosing cilk_for.

//@ compile-flags: -C panic=abort
//@ no-prefer-dynamic

fn main() {
    'outer: cilk_for _i in 0..1 {
        cilk_spawn {
            continue 'outer;
            //~^ error: cannot use `continue` within cilk_spawn
        };
    }
}
