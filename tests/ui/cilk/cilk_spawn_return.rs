#![feature(cilk)]
// Tests that returning from a cilk_spawn is not allowed.

//@ compile-flags: -C panic=abort
//@ no-prefer-dynamic

fn main() {
    cilk_spawn { 
        return 5; //~error: cannot use `return` within cilk_spawn
    };
}
