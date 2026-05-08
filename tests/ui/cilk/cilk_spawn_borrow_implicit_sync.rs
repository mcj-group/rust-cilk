#![feature(cilk)]
// Tests that a `&mut` borrow inside a `cilk_spawn` is held until the
// implicit sync at function exit, even when no explicit `cilk_sync` is
// written. The mutable use in the parent before the function returns must
// still be flagged.

//@ compile-flags: -C panic=abort
//@ no-prefer-dynamic

fn main() {
    let mut x = vec![10, 11];
    cilk_spawn {
        let y = &mut x;
        println!("{:?}", y);
    };
    x.push(10); //~ ERROR cannot borrow `x` as mutable more than once at a time [E0499]
}
