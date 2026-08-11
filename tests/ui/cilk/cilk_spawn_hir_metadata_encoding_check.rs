#![feature(cilk)]
#![crate_type = "lib"]

//@ check-pass
//@ compile-flags: -C panic=abort

pub fn foo(x: usize) -> usize {
    let mut a = 0;
    cilk_spawn { 
        a = x + 1 
    };
    a
}