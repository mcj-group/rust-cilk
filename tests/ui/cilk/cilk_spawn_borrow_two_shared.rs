#![feature(cilk)]
// Tests that two shared borrows of the same place — one inside a
// `cilk_spawn` and one in the parent's continuation — coexist without
// conflict, as expected of `&T` borrows.

//@ run-pass
//@ compile-flags: -C panic=abort
//@ no-prefer-dynamic

fn main() {
    let x = vec![10, 11];
    cilk_spawn {
        println!("spawn: {:?}", &x);
    };
    println!("parent: {:?}", &x);
    cilk_sync;
}
