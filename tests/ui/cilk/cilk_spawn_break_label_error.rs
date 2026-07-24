#![feature(cilk)]
// Tests that breaking with label from a cilk_spawn is not allowed.

//@ compile-flags: -C panic=abort
//@ no-prefer-dynamic

fn main() {
    'out: for _ in 0..5 {
        cilk_spawn { 
            break 'out; //~ error: cannot use `break` within cilk_spawn
        };
    }
}
