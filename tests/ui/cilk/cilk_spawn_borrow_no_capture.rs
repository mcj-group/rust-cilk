#![feature(cilk)]
// Tests that a `cilk_spawn` that does not borrow any parent local does not
// constrain the parent's continuation. The parent is free to mutate `x`
// concurrently with the spawned task because the spawn never sees `x`.

//@ run-pass
//@ compile-flags: -C panic=abort
//@ no-prefer-dynamic

fn main() {
    let mut x = vec![10, 11];
    cilk_spawn {
        println!("hello from spawn");
    };
    x.push(10);
    cilk_sync;
    println!("{:?}", x);
}
