#![feature(cilk)]
// Checks the diagnostics produced for incorrect cilk_for syntax.

//@ known-bug: unknown
//@ compile-flags: -C panic=abort
//@ no-prefer-dynamic

fn main() {
    cilk_for 1..10 {}
    //~^ ERROR missing `in` in `for` loop
    //~| ERROR missing expression to iterate on in `for` loop
}
