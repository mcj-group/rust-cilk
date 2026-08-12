#![feature(cilk)]
// Tests that the implicit sync at the end of a `cilk_scope` only syncs the tasks spawned inside
// that scope, so a place initialized by an outer task is still uninitialized after the scope.

//@ compile-flags: -C panic=abort
//@ no-prefer-dynamic

fn main() {
    let x;
    cilk_spawn {
        x = 0
    };
    cilk_scope {
        cilk_spawn {};
    };
    println!("{x}");
    //~^ ERROR used binding `x` is possibly-uninitialized [E0381]
}
