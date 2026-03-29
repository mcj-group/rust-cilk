#![feature(cilk)]

// Test that the return within a cilk_for doesn't cause an error if it's inside a closure

// build-pass

fn main() {
    cilk_for i in 0..10 {
        let foo = |x: i32| { return x + 1; };
    }
}