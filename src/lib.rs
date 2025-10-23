// #![no_std]
pub mod bitfield;
// pub mod fib;
pub mod original;
// pub mod bitalloc_verus;
pub mod bitalloc_verus_impl;
// use super::bitfield::*;
use crate::bitfield::*;
use core::ops::Range;

pub use original::BitAlloc16 as OrigBitAlloc16;
pub use bitalloc_verus_impl::BitAlloc16 as VerusBitAlloc16;

#[cfg(kani)]
mod proofs {
    use super::*;
    use crate::bitalloc_verus_impl::BitAllocView;
    use crate::bitalloc_verus_impl::BitAlloc as VerusBitAlloc;
    use crate::original::BitAlloc;
    #[kani::proof]
    fn verify_success() {
        // let mut ba1 = VerusBitAlloc16::default();
        // let mut ba2 = OrigBitAlloc16::DEFAULT;
        let bits: u16 = kani::any();
        let mut ba1 = OrigBitAlloc16::set_val(bits);            // 若是 tuple struct
        let mut ba2 = VerusBitAlloc16 { bits };        // 若是带命名字段
        // let mut ba1: OrigBitAlloc16  = kani::any();
        // let mut ba2: VerusBitAlloc16 = kani::any();
        kani::assume(ba1.get_val() == ba2.bits);
        let b1 = ba1.alloc();
        let b2 = ba2.alloc();
        assert_eq!(b1,b2);
    }
}
