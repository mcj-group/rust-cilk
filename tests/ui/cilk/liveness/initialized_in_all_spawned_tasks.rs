#![feature(cilk)]
// Tests that when all conditional spawns initialize a place, that place is considered initialized.

//@ build-pass
//@ compile-flags: -C panic=abort
//@ no-prefer-dynamic

fn f() -> usize {
    let y;
    if true {
        cilk_spawn { y = 1; };
    } else {
        cilk_spawn { y = 2; };
    }
    cilk_sync;
    y + 1
}

fn main() {
}
