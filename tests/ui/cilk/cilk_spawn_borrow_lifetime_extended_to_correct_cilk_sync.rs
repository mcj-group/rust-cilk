#![feature(cilk)]
// Tests that a borrow from an outer `cilk_spawn` is not released by the
// implicit sync at the end of an unrelated nested `cilk_scope`.

//@ check-fail
//@ compile-flags: -C panic=abort
//@ no-prefer-dynamic

fn main() {
    let mut x = 0;

    cilk_spawn {
        let first = &mut x;
        *first += 1;
    };

    cilk_scope {
        cilk_spawn {
            let _ = 1;
        };
    };

    let second = &mut x;
    //~^ ERROR cannot borrow `x` as mutable more than once at a time
    *second += 1;
}
