#![feature(cilk)]
// Reproduces an internal compiler error when a shared borrow and a
// mutable borrow occurs in a cilk_spawn nested inside a cilk_for.

//@ known-bug: unknown
//@ compile-flags: -C panic=abort
//@ no-prefer-dynamic

fn main() {
    let mut x = vec![1, 2];
    cilk_for i in 0..10 {
        cilk_spawn {
            println!("{:?}", x);
            x.push(i);
        };
    }
}
