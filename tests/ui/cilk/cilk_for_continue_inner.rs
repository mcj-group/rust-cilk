#![feature(cilk)]

// Test that continue in a subloop targets that loop, and isn't lowered to a reattach

// run-pass

use std::sync::atomic::AtomicU64;

fn main() {
    let sum: AtomicU64 = AtomicU64::new(0);
    cilk_for i in 0..10 {
        for j in 0..10 {
            if j == 5 {
                continue;
            }
            sum.fetch_add(i, std::sync::atomic::Ordering::Relaxed);
        }
    }
    assert_eq!(sum.into_inner(), 405);
}
