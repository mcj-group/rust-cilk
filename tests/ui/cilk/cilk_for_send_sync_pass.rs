#![feature(cilk)]
// Tests that thread-safe shared and moved captures pass analysis in cilk_for.

//@ check-pass
//@ compile-flags: -C panic=abort
//@ no-prefer-dynamic

use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

fn main() {
    let shared = Arc::new(AtomicUsize::new(0));
    let values = vec![String::from("one"), String::from("two")];

    cilk_for value in values {
        shared.fetch_add(value.len(), Ordering::Relaxed);
        drop(value);
    }
}
