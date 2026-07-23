#![feature(cilk)]
// Tests that normal breaking with label is allowed within cilk_spawn.

//@ run-pass
//@ compile-flags: -C panic=abort
//@ no-prefer-dynamic

fn main() {
    cilk_spawn {
        'out: loop{
            for i in 0..10{
                if i == 5{
                    break 'out;
                }
                print!("{:?}", i);
            }
        } 
    };
}
