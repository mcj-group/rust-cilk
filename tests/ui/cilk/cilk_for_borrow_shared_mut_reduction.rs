#![feature(cilk)]
// A cilk_for whose body does a read-modify-write of a captured scalar local
// (`if max < i { max = i }`) — the classic reduction pattern.
//
// Every parallel iteration both reads and writes the shared `max`, which is a
// data race and SHOULD be rejected by the borrow checker. Unlike
// cilk_for_borrow_mut_index.rs this involves no `IndexMut` call, just a direct
// assignment to a parent local.
//
// EXPECTED: rejected with E0499 because `max` is mutably borrowed across
// parallel loop iterations.

//@ compile-flags: -C panic=abort
//@ no-prefer-dynamic

fn main() {
    let mut max = 4;
    cilk_for i in 0..1000 {
                    //~^ ERROR cannot borrow `max` as mutable more than once at a time [E0499]
        if max < i {
            max = i;
        }
    }
    println!("{}", max);
}
