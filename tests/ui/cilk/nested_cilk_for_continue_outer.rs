#![feature(cilk)]
// Tests that a nested cilk_for cannot continue its enclosing cilk_for.

//@ compile-flags: -C panic=abort
//@ no-prefer-dynamic

fn main() {
    'outer: cilk_for _i in 0..1 {
        cilk_for _j in 0..1 {
            continue 'outer;
            //~^ error: cannot use `continue` within cilk_for
        }
    }
}
