#![feature(cilk)]
// Tests that disjoint field borrows do not conflict across the cilk
// extension. The spawn mutably borrows `s.a`; the parent mutably borrows
// `s.b`. These borrows are non-overlapping and should compile.

//@ run-pass
//@ compile-flags: -C panic=abort
//@ no-prefer-dynamic

struct Pair {
    a: Vec<i32>,
    b: Vec<i32>,
}

fn main() {
    let mut s = Pair { a: Vec::new(), b: Vec::new() };
    cilk_spawn {
        s.a.push(1);
    };
    s.b.push(2);
    cilk_sync;
    println!("{:?} {:?}", s.a, s.b);
}
