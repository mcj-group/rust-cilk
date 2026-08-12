#![feature(cilk)]
// Tests that a place is considered initialized when one branch initializes it in a task synced by
// a `cilk_scope` and the other in a task synced by a later `cilk_sync`.

//@ build-pass
//@ compile-flags: -C panic=abort
//@ no-prefer-dynamic

fn main() {
    let x;
    if true {
        cilk_scope {
            cilk_spawn {
                x = 0;
            };
        };
    } else {
        cilk_spawn {
            x = 1;
        }
    }
    cilk_sync;
    println!("{x}");
}
