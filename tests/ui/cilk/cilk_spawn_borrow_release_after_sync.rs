#![feature(cilk)]
// Tests that a borrow held by a spawned task is released by the matching
// `cilk_sync`, so the parent can mutate the value after the sync without
// conflict.

//@ run-pass
//@ compile-flags: -C panic=abort
//@ no-prefer-dynamic

fn main() {
    let mut x = vec![10, 11];
    cilk_spawn {
        let y = &mut x;
        println!("{:?}", y);
    };
    cilk_sync;
    x.push(10);
}
