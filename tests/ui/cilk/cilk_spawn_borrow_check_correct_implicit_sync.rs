#![feature(cilk)]
// Tests lifetime of mutable borrow is extended to the correct sync region when multiple sync region exists

//@ compile-flags: -C panic=abort
//@ no-prefer-dynamic

fn main() {
    let mut x = vec![0];

    // uses enclosing fn's sr0
    cilk_spawn {
        x.push(1);
    };

    // creates sr1
    cilk_for _i in 0..10 {
        println!("Hello World");
    }

    x.push(2);
    //~^ ERROR cannot borrow `x` as mutable more than once at a time [E0499]
}