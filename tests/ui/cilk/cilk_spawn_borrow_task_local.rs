#![feature(cilk)]
// Tests that a borrow of a *task-private* local — one declared inside the
// `cilk_spawn` block — is not extended to the parent's continuation.
// Without this scoping, every short-lived borrow in the task body (e.g.
// formatter aggregates inside a `println!` expansion) would propagate past
// its natural `StorageDead` and trigger spurious "borrow does not live long
// enough" diagnostics.

//@ run-pass
//@ compile-flags: -C panic=abort
//@ no-prefer-dynamic

fn main() {
    let mut x = vec![1];
    cilk_spawn {
        let local = vec![10, 11];
        let r = &local;
        println!("{:?}", r);
    };
    x.push(2);
    cilk_sync;
}
