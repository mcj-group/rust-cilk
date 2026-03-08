#![feature(cilk)]

// Test that continues still fail if they target a loop outside the cilk_for

// compile-flags: -C panic=abort
// no-prefer-dynamic

fn main() {
    'outside: for i in 0..10 {
        cilk_for j in 0..10 {
            continue 'outside;
            //~^ error: cannot use `continue` within cilk_for
        }
    }
}
