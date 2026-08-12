#![feature(cilk)]
// Tests that a move performed by a task spawned inside a `cilk_scope` is visible after the scope's
// implicit sync, so the moved-out place cannot be used by a later task.

//@ compile-flags: -C panic=abort
//@ no-prefer-dynamic

fn main() {
    let x = String::new();
    cilk_scope {
        cilk_spawn {
            drop(x);
        };
    };
    cilk_spawn {
        println!("{x}");
        //~^ ERROR borrow of moved value: `x` [E0382]
    }
}
