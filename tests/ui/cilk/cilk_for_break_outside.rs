#![feature(cilk)]

// Test that break still fail if they target a loop outside the cilk_for

// compile-flags: -C panic=abort
// no-prefer-dynamic

fn main() {
    'outside: for i in 0..10 {
        cilk_for j in 0..10 {
            break 'outside;
            //~^ error: cannot use `break` within cilk_for
        }
    }
}
