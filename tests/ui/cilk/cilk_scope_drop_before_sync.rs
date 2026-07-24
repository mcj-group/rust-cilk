#![feature(cilk)]
// checks that an error is produced if a task borrows a variable (v) past the end of its scope

//@ compile-flags: -C panic=abort
//@ no-prefer-dynamic

fn main() {
    cilk_scope {
        if true {
            let v = Vec::<i32>::new();
            cilk_spawn{
                println!("{v:?}");
                //~^ ERROR `v` does not live long enough [E0597]
            };
        }
    };
}
