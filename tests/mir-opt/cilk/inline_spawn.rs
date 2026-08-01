#![feature(cilk)]
// This test checks that a function containing a task can be inlined into a
// caller that itself contains a task. The inlined body is wrapped in its own
// taskframe, and the callee's sync region / taskframe locals are remapped into
// the caller's local space.

//@ compile-flags: -C panic=abort
//@ no-prefer-dynamic

#[inline(always)]
fn foo() {
    cilk_spawn {
        println!("child");
    };
}

// EMIT_MIR inline_spawn.main.Inline.diff
fn main() {
    // CHECK-LABEL: fn main(
    // CHECK: (inlined foo)
    cilk_spawn {
        println!("parent before");
    };
    foo();
    println!("parent after");
}
