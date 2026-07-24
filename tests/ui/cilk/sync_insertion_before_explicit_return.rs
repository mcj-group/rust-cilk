#![feature(cilk)]
// drops are generated differently in functions with a return statement (in in_breakable_scope) than those without which
// use ast_block_stmts
// makes sure both code paths work

//@ build-pass
//@ compile-flags: -C panic=abort
//@ no-prefer-dynamic

fn main(){
    test();
}

fn test() {
    let v = Vec::<i32>::new();
    cilk_spawn {
        println!("{v:?}");
    };
    return;
}