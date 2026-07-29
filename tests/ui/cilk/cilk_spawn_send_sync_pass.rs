#![feature(cilk)]
// Tests that thread-safe shared, moved, and mutably borrowed captures pass analysis.

//@ check-pass
//@ compile-flags: -C panic=abort
//@ no-prefer-dynamic

use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

fn main() {
    let shared = Arc::new(AtomicUsize::new(0));
    let moved = String::from("moved");
    let mut mutable = 0_usize;

    cilk_spawn {
        shared.fetch_add(1, Ordering::Relaxed);
        drop(moved);
        mutable += 1;
    };
}
