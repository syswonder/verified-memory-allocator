// use super::bitalloc_verus_impl::*;
// use super::original::*;
use crate::original;
use crate::bitalloc_verus_impl;

pub fn fibonacci1(n1: u32, n2: u32) -> u32 {
    // let mut a = 0;
    // let mut b = 1;
    // for _ in 0..n {
    //     let tmp = a + b;
    //     a = b;
    //     b = tmp;
    // }
    // a
    n1.wrapping_add(n2)
}

pub fn fibonacci2(n1: u32, n2: u32) -> u32 {
    // if n <= 1 {
    //     n as u64
    // } else {
    //     fibonacci2(n - 1) + fibonacci2(n - 2)
    // }
    n2.wrapping_add(n1)
}

#[cfg(kani)]
#[kani::proof]
fn verify_success() {


    let ba1 = bitalloc_verus_impl::BitAlloc16::default();
    let ba2 = original::BitAlloc16::DEFAULT;
    // let x: u32 = kani::any();
    // let y: u32 = kani::any();
    // kani::assume(x <= 93);
    assert!(ba1 == ba2);
}