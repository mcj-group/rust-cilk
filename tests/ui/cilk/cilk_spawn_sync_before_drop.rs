#![feature(cilk)]
// checks that the end of the outer cilk_spawn is before the v gets dropped

//@ build-pass
//@ compile-flags: -C panic=abort
//@ no-prefer-dynamic

fn main() {
    cilk_spawn {
        let v = Vec::<i32>::new();
        cilk_spawn{
            println!("{v:?}");
        };
    };
}
