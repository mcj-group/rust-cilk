#![feature(cilk)]
// Expected error logging for incorrect cilk syntax

//@ compile-flags: -C panic=abort
//@ no-prefer-dynamic

fn main(){
    cilk_for 1..10{}
    //~^ ERROR missing `in` in `for` loop
    //~| ERROR missing expression to iterate on in `for` loop
}