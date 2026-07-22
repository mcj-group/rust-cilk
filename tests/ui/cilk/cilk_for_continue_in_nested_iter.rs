#![feature(cilk)]
#![allow(unreachable_code)]
// Tests that a continue in a nested cilk_for iterator can target the enclosing cilk_for.

//@ run-pass
//@ check-run-results
//@ compile-flags: -C panic=abort
//@ no-prefer-dynamic

fn main() {
    'outer: cilk_for _i in 0..1 {
        cilk_for _j in {
            continue 'outer;
            0..1
        } {
            println!("Should not reach here.");
        }
        println!("Should not reach here.");
    }

    println!("done");
}
