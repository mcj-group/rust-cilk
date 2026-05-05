#![feature(cilk)]
// Test that continue in a subloop targetting the cilk_for is successfully lowered to a reattach

//@ run-pass
//@ compile-flags: -C panic=abort
//@ no-prefer-dynamic

use std::sync::atomic::AtomicU64;

fn main() {
    let sum: AtomicU64 = AtomicU64::new(0);
    'outer: cilk_for i in 0..10 {
        for j in 0..10 {
            if j == 5 {
                continue 'outer;
            }
            sum.fetch_add(i, std::sync::atomic::Ordering::Relaxed);
        }
    }
    assert_eq!(sum.into_inner(), 225);
}
