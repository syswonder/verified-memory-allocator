mod test_trait;
use vstd::{prelude::*, seq_lib::*};

/// Macro to get a specific bit from a u16 value.
/// Returns true if the bit at the given index is 1, false otherwise.
macro_rules! get_bit16_macro {
    ($a:expr, $b:expr) => {{ (($a >> $b) & 0x1u16) == 1u16 }};
}

/// Verus-proof-wrapped version of `get_bit16_macro`.
#[allow(unused_macros)]
macro_rules! get_bit16 {
    ($($a:tt)*) => {
        verus_proof_macro_exprs!(get_bit16_macro!($($a)*))
    }
}

verus!{
/// Converts a u16 value into a sequence of boolean bits.
pub open spec fn u16_view(u: u16) -> Seq<bool> {
    Seq::new(16, |i: int| get_bit16!(u, i as u16))
}

impl test_trait::BitAllocView for test_trait::BitAlloc16 {
    /// Specification function to view the internal u16 as a sequence of booleans.
    open spec fn view(&self) -> Seq<bool> {
        let width = Self::spec_cap() as nat;
        Seq::new(width, |i: int| u16_view(self.bits)[i])
    }

    /// The maximum capacity of the bitmap (16 bits).
    fn cap() -> (res:usize) {
        16
    }

    open spec fn spec_cap() -> (res:usize){
        16
    }

    open spec fn cascade_not_overflow() -> bool {
        true
    }

    open spec fn lemma_cap_is_pow16_pre() -> bool {
        true
    }

    proof fn lemma_cap_is_pow16()
    {
        assert(test_trait::is_pow16(16)) by (compute);
    }

    /// Creates a new `BitmapAllocator16` with all bits set to 0 (all free).
    fn default() -> Self {
        test_trait::BitAlloc16 { bits: 0 }
    }

    /// Checks if there are any free bits (bits set to 1) in the bitmap.
    fn any(&self) -> (res:bool){
        self.bits != 0
    }

    open spec fn spec_any(&self) -> bool{
        self.bits != 0
    }

    proof fn lemma_bits_nonzero_implies_exists_true(&self)
    {
        let bits = self.bits;
        let ba = self@;
        if self.spec_any() {
            let i: u16 = bits.trailing_zeros() as u16;
            // 1) bits != 0  ==>  0 <= i < 16
            assert(0 <= i < 16);
            // 2) bits != 0  ==>  get_bit16!(bits, i) == true
            assert(get_bit16!(bits, i) == true);

            // 用映射得到 ba[i] == true
            assert(ba[i as int] == get_bit16!(bits, i));
            assert(ba[i as int] == true);

            // 给出见证
            assert(exists|k:int| 0 <= k < 16 && ba[k] == true);
        } else {
            let i: u16 = bits.trailing_zeros() as u16;
            vstd::std_specs::bits::axiom_u16_trailing_zeros(bits);

            assert(i == 16);
            assert(forall|j: u16| 0 <= j < i ==> #[trigger] (bits >> j) & 1u16 == 0u16)
        }

        assert(self.spec_any() == exists|k:int| 0 <= k < 16 && ba[k] == true);
    }


    open spec fn wf(&self) -> bool {
        &&& Self::cascade_not_overflow()
        &&& Self::spec_cap() == 16
    }

}


fn main() {}

}