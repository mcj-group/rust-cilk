#![feature(cilk)]
// A cilk_for that mutably indexes a parent-owned Vec from every iteration.
//
// The indices happen to be disjoint here, but the borrow checker cannot prove
// that, so handing out `&mut v` to every parallel iteration is unsound and
// SHOULD be rejected. The safe ways to express disjoint writes are
// `split_at_mut` or raw pointers (see cilk_for_raw_ptr_write.rs).
//
// EXPECTED: rejected with E0499, exactly as the nested-loop sibling
// `cilk_for_for.rs` already is.
//
// CURRENT BEHAVIOR: the compiler emits extra [E0716] error together 
// at the cilk_for span. It also emits some diagnostics to stdout. These
// would be removed in the future.

//@ compile-flags: -C panic=abort
//@ no-prefer-dynamic

fn main() {
    let mut v = vec![0; 5];
    cilk_for i in 0..5 {
                    //~^ ERROR cannot borrow `v` as mutable more than once at a time [E0499]
                    //~| ERROR temporary value dropped while borrowed [E0716]
        v[i] = 1;
    }
    println!("{:?}", v);
}
