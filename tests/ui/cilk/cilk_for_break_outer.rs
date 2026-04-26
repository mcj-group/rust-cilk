#![feature(cilk)]

// Tests that a break within a subloop still fails if it targets the outer loop

//@ run-pass
//@ compile-flags: -C panic=abort
//@ no-prefer-dynamic

use std::sync::atomic::AtomicU64;

fn main() {
    let sum: AtomicU64 = AtomicU64::new(0);
    'outer: cilk_for i in 1..10 {
        for j in 1..10 {
            sum.fetch_add(i, std::sync::atomic::Ordering::Relaxed);
            if j == 5 {
                break 'outer;
                //~^ error: cannot use `break` within cilk_for
            }
        }
    }
    assert_eq!(sum.into_inner(), 100);
}