#![feature(cilk)]
// Tests that a shared borrow inside a spawn coexists with another shared
// borrow held in the parent's continuation across the matching sync.

//@ run-pass
//@ compile-flags: -C panic=abort
//@ no-prefer-dynamic

fn main() {
    let x = String::from("hello");
    cilk_spawn {
        let r = &x;
        println!("{}", r);
    };
    let r2 = &x;
    println!("{}", r2);
    cilk_sync;
}
