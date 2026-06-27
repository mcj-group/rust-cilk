#![feature(cilk)]
// Overlapping mutable indexing across cilk_for iterations.
//
// Iterations write `v[i]` and `v[i + 1]`, so adjacent iterations touch the
// same element concurrently. This is a data race and SHOULD be rejected by
// the borrow checker (analogous to E0499 — `v` mutably borrowed by parallel
// iterations).
//
// CURRENT BEHAVIOR: this ICEs instead of producing a diagnostic. The crash is
//   rustc_borrowck/src/region_infer/mod.rs: `Option::unwrap()` on a `None`
//   value, in `find_sub_region_live_at` (query stack: [mir_borrowck] main).
// Tracked as a known-bug until the error path no longer panics. (Kept here
// rather than tests/crashes/ so all cilk tests stay in one place.)

//@ known-bug: unknown
//@ compile-flags: -C panic=abort
//@ no-prefer-dynamic

fn main() {
    let mut v = vec![0; 5];
    cilk_for i in 0..4 {
        v[i] = 1;
        v[i + 1] = 2;
    }
    println!("{:?}", v);
}
