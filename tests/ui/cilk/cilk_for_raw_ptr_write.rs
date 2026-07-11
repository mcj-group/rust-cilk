#![feature(cilk)]
// Tests the sanctioned unsafe escape hatch for disjoint writes from a
// cilk_for: each iteration writes a distinct element through a raw pointer,
// so the borrow checker's inability to prove disjointness is bypassed.
// This is the safe-to-run counterpart to cilk_for_borrow_mut_index.rs, which
// attempts the same thing through `&mut` indexing.

//@ run-pass
//@ compile-flags: -C panic=abort
//@ no-prefer-dynamic

fn main() {
    let mut v = vec![0i32; 8];
    let p = v.as_mut_ptr();
    cilk_for i in 0..8 {
        unsafe {
            *p.add(i) = i as i32;
        }
    }
    for i in 0..8 {
        assert_eq!(v[i], i as i32);
    }
}
