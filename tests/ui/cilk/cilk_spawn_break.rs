#![feature(cilk)]
// Tests that normal breaking without label is allowed within cilk_spawn.

//@ run-pass
//@ check-run-results
//@ compile-flags: -C panic=abort
//@ no-prefer-dynamic

fn main() {
    cilk_spawn { 
        for i in 0..10{
            if i == 5{
                break
            }
            println!("{:?}", i);
        }
    };
}
