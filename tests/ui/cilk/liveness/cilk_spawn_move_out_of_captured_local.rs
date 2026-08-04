#![feature(cilk)]
// A `cilk_spawn` body that consumes (moves) a captured local, after which the
// parent continuation still uses that local.
//
// The spawned task takes ownership of `s` via `drop(s)`, so the value is moved
// into the task's closure. The parent's later `println!("{s}")` therefore reads
// a moved-out value.
//
// EXPECTED: rejected with E0382 because `s` is used after being moved into the
// spawned task.

//@ compile-flags: -C panic=abort
//@ no-prefer-dynamic

fn main() {
    let s = String::new();
    cilk_spawn {
        drop(s);
    };
    println!("{s}");
    //~^ ERROR borrow of moved value: `s` [E0382]
}
