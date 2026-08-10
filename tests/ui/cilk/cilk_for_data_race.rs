#![feature(cilk)]
// Tests that a cilk_for, with some shared and some task-private state doesn't produce a data race
// Rust automatically places allocas at the top of a function body, so if handled incorrectly the `factors` variable
// would be hoisted as such, which would result in it being a shared variable
// we address this by placing the body of the cilk_for inside a closure

//@ run-pass
//@ compile-flags: -C panic=abort
//@ no-prefer-dynamic

use std::sync::atomic::{AtomicU64, Ordering};

fn main() {
    let x = AtomicU64::new(0);
    cilk_for i in 0..1000 {
        let mut factors = 0;
        for j in 1..=i {
            if i % j == 0 {
                factors += 1;
            }
        }
        x.fetch_add(factors, Ordering::Relaxed);
    }
    assert_eq!(x.load(Ordering::Relaxed), 7053);
}
