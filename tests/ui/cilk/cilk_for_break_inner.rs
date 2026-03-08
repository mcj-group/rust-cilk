#![feature(cilk)]
// Test that compiling succeeds when a break is placed with a sub loop in a cilk_for

// run-pass

use std::sync::atomic::AtomicU64;

fn main() {
    let sum: AtomicU64 = AtomicU64::new(0);
    cilk_for i in 0..10 {
        for j in 0..10 {
            if j == 5 {
                break;
            }
            sum.fetch_add(i, std::sync::atomic::Ordering::Relaxed);
        }
    }
    assert_eq!(sum.into_inner(), 225);
}
