#![feature(cilk)]
// Tests that a `&mut` borrow created inside a `cilk_spawn` block conflicts
// with a mutable use of the same place in the parent's continuation, before
// the matching `cilk_sync`. Without lifetime extension, the borrow's region
// would end at the Reattach and the parent's `x.push(10)` would compile;
// with extension the conflict is correctly detected.

//@ compile-flags: -C panic=abort
//@ no-prefer-dynamic

fn main() {
    let mut x = vec![10, 11];
    cilk_spawn {
        let y = &mut x;
        println!("{:?}", y);
    };
    x.push(10); //~ ERROR cannot borrow `x` as mutable more than once at a time [E0499]
    cilk_sync;
}
