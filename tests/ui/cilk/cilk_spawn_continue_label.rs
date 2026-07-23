#![feature(cilk)]
// Tests that noraml continue with a lable is allowed within a cilk_spawn.

//@ run-pass
//@ check-run-results
//@ compile-flags: -C panic=abort
//@ no-prefer-dynamic

fn main() {
    cilk_spawn {
        for i in 0..10{
            if i == 5{
                continue;
            }
            println!("{:?}", i);
        }
    };
}
