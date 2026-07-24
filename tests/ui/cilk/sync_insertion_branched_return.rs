#![feature(cilk)]
// drops are generated differently in functions with a return statement (in in_breakable_scope) than those without which
// use ast_block_stmts
// this test checks that the sync before a return is within the scope of v for a return in a child block

//@ build-pass
//@ compile-flags: -C panic=abort
//@ no-prefer-dynamic

fn main(){
    test(true);
}

fn test(b: bool) {
    let v = Vec::<i32>::new();
    cilk_spawn {
        println!("{v:?}");
    };
    if b {
        return;
    }
}