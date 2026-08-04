#![feature(cilk)]
// MutexGuard implements Sync but not Send, thus it can be used in a task unless we transfer
// ownership.

//@ check-fail
//@ compile-flags: -C panic=abort
//@ no-prefer-dynamic

use std::sync::Mutex;

fn main() {
    let m = Mutex::new(0);
    let unlock = m.lock().unwrap();

    cilk_spawn {
        // this transfers ownership
        let _x = unlock; //~ ERROR `std::sync::MutexGuard<'_, i32>` cannot be sent between threads safely
    };
}
