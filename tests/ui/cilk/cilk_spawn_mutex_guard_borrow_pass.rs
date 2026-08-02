#![feature(cilk)]
// MutexGuard implements Sync but not Send, thus it can be used in a task unless we transfer
// ownership.

//@ check-pass
//@ compile-flags: -C panic=abort
//@ no-prefer-dynamic

use std::sync::Mutex;

fn main() {
    let m = Mutex::new(0);
    let unlock = m.lock().unwrap();

    cilk_spawn {
        // this does not transfer ownership
        let _x = *unlock;
    };
}
