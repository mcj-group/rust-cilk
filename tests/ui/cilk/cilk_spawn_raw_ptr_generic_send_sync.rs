#![feature(cilk)]
// Tests that a captured raw pointer is accepted when its generic pointee is
// constrained to implement both Send and Sync.

//@ check-pass
//@ compile-flags: -C panic=abort
//@ no-prefer-dynamic

fn use_pointer<T: Send + Sync>(pointer: *const T) {
    cilk_spawn {
        unsafe {
            let _ = &*pointer;
        }
    };
}

fn main() {
    let value = 1_usize;
    use_pointer(&value);
}
