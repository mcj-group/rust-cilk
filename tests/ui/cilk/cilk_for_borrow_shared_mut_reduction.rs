#![feature(cilk)]
// A cilk_for whose body does a read-modify-write of a captured scalar local
// (`if max < i { max = i }`) — the classic reduction pattern.
//
// Every parallel iteration both reads and writes the shared `max`, which is a
// data race and SHOULD be rejected by the borrow checker. Unlike
// cilk_for_borrow_mut_index.rs this involves no `IndexMut` call, just a direct
// assignment to a parent local.
//
// CURRENT BEHAVIOR: this compiles and runs, so it is a soundness hole rather
// than a crash. Tracked as a known-bug until cilk_for bodies are
// borrow-checked against the parent's continuation.

//@ compile-flags: -C panic=abort
//@ no-prefer-dynamic

fn main() {
    let mut max = 4;
    cilk_for i in 0..1000 {
                    //~^ ERROR cannot borrow `max` as mutable more than once at a time [E0499]
                    //~| ERROR temporary value dropped while borrowed [E0716]
        if max < i {
            max = i;
        }
    }
    println!("{}", max);
}
