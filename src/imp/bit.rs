#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use core::ops::Range;
use vstd::{prelude::*, seq::*, seq_lib::*};

/// Macro to get a specific bit from a u16 value.
/// Returns true if the bit at the given index is 1, false otherwise.
macro_rules! get_bit16_macro {
    ($a:expr, $b:expr) => {{ (0x1u16 & ($a >> $b)) == 1 }};
}

/// Verus-proof-wrapped version of `get_bit16_macro`.
macro_rules! get_bit16 {
    ($($a:tt)*) => {
        verus_proof_macro_exprs!(get_bit16_macro!($($a)*))
    }
}

/// Macro to extract a range of bits from a u16 value.
/// $val: The u16 value.
/// $start: The starting bit index (inclusive).
/// $end: The ending bit index (exclusive).
macro_rules! get_bits16_macro {
    ($val:expr, $start:expr, $end:expr) => {{
        let bitlen = 16u16;
        let bits = ($val << (bitlen - $end)) >> (bitlen - $end);
        bits >> $start
    }};
}

/// Verus-proof-wrapped version of `get_bits16_macro`.
macro_rules! get_bits16 {
    ($($a:tt)*) => {
        verus_proof_macro_exprs!(get_bits16_macro!($($a)*))
    }
}

/// Macro to set a specific bit in a u16 value.
/// $val: The u16 value to modify.
/// $idx: The index of the bit to set.
/// $bit: The boolean value to set the bit to (true for 1, false for 0).
macro_rules! set_bit16_macro {
    ($val:expr,$idx:expr, $bit:expr) => {{
        if $bit {
            $val | 1u16 << $idx
        } else {
            $val & (!(1u16 << $idx))
        }
    }};
}

/// Verus-proof-wrapped version of `set_bit16_macro`.
macro_rules! set_bit16 {
    ($($a:tt)*) => {
        verus_proof_macro_exprs!(set_bit16_macro!($($a)*))
    }
}

/// Macro to set a range of bits in a u16 value.
/// $val: The u16 value to modify.
/// $start: The starting bit index (inclusive).
/// $end: The ending bit index (exclusive).
/// $new_val: The u16 value containing the bits to set.
macro_rules! set_bits16_macro {
    ($val:expr, $start:expr, $end:expr, $new_val:expr) => {{
        let bitlen = 16;
        let mask = !(!0u16 << (bitlen - $end) >> (bitlen - $end) >> $start << $start);
        ($val & mask) | ($new_val << $start)
    }};
}

/// Verus-proof-wrapped version of `set_bits16_macro`.
macro_rules! set_bits16 {
    ($($a:tt)*) => {
        verus_proof_macro_exprs!(set_bits16_macro!($($a)*))
    }
}

verus! {

// global layout usize is size == 4;

/// Converts a u16 value into a sequence of boolean bits.
pub open spec fn u16_view(u: u16) -> Seq<bool> {
    Seq::new(16, |i: int| get_bit16!(u, i as u16))
}

// spec fn u64_view(u: usize) -> Seq<bool> {
//     Seq::new(usize::BITS as nat, |i: int| get_bit64!(u, i as usize))
// }

// #[verifier::bit_vector]
// proof fn set_bit64_proof(bv_new: usize, bv_old: usize, index: usize, bit: bool)
//     requires
//         bv_new == set_bit64!(bv_old, index, bit),
//         index < usize::BITS,
//     ensures
//         get_bit64!(bv_new, index) == bit,
//         forall|loc2: usize|
//             (loc2 < usize::BITS && loc2 != index) ==> (get_bit64!(bv_new, loc2) == get_bit64!(bv_old, loc2)),
// {
// }

// #[verifier::bit_vector]
// proof fn bit_or_64_proof(bv1: usize, bv2: usize, bv_new: usize)
//     requires
//         bv_new == bv1 | bv2,
//     ensures
//         forall|i: usize|
//             (i < 64) ==> get_bit64!(bv_new, i) == (get_bit64!(bv1, i) || get_bit64!(bv2, i)),
// {
// }

// proof fn bit_or_64_view_proof(u1: usize, u2: usize, bv_new: usize)
//     requires
//         bv_new == u1 | u2,
//     ensures
//         u64_view(bv_new) =~= Seq::new(64, |i: int| u64_view(u1).index(i) || u64_view(u2).index(i)),
// {
//     bit_or_64_proof(u1, u2, bv_new);
// }

// spec fn or_u64_relation(u1: usize, u2: usize, or_int: usize) -> bool {
//     u64_view(or_int) =~= Seq::new(usize::BITS, |i: int| u64_view(u1).index(i) || u64_view(u2).index(i))
// }

#[verifier::bit_vector]
proof fn get_bits_u16_correctness(bv_gets: u16, bits: u16, st:u16, ed:u16)
    requires
        bv_gets == get_bits16!(bits, st, ed),
        st < 16,
        ed <= 16,
        st < ed,
    ensures
        forall|i: u16| 0 <= i < (ed - st) ==> ((get_bit16!(bv_gets, i)) == get_bit16!(bits, (st + i) as u16)),
{
}

pub struct BitAlloc16 {
    pub bits: u16,
}

impl BitAlloc16{
    /// Specification function to view the internal u16 as a sequence of booleans.
    pub open spec fn view(&self) -> Seq<bool> {
        let width = 16;
        Seq::new(width, |i: int| u16_view(self.bits@)[i])
    }

    /// Gets the boolean value of a specific bit at `index`.
    fn get_bit(&self, index: u16) -> (bit: bool)
        requires
            index < self@.len(),
        ensures
            bit == self@[index as int],
    {
        let bit_index: u16 = index % 16;
        get_bit16_macro!(self.bits, bit_index as u16)
    }

    /// Extracts a range of bits from the bitmap as a u16 value.
    fn get_bits(&self, range:Range<u16>) -> (bits:u16)
        requires
            range.start < self@.len(),
            range.end <= self@.len(),
            range.start < range.end,
        ensures
            forall|i: int| 0 <= i < (range.end - range.start) ==> (u16_view(bits)[i]) == self@[range.start + i],
    {
        let bv_gets = get_bits16_macro!(self.bits, range.start, range.end);
        proof {
            get_bits_u16_correctness(bv_gets, self.bits, range.start, range.end);
        };
        bv_gets
    }

    // fn set_bit(&mut self, index: usize, bit: bool)
    //     requires
    //         index < old(self)@.len(),
    //     ensures
    //         self@ == old(self)@.update(index as int, bit),
    // {
    //     // REVEIW: Same problem here with above regarding `usize`.
    //     let seq_index: usize = index / usize::BITS;
    //     let bit_index: usize = index % usize::BITS;
    //     let bv_old: usize = self.bits[seq_index];
    //     let bv_new: usize = set_bit64_macro!(bv_old, bit_index, bit);
    //     proof {
    //         set_bit64_proof(bv_new, bv_old, bit_index, bit);
    //     }
    //     ;
    //     self.bits.set(seq_index, bv_new);
    //     proof {
    //         assert_seqs_equal!(
    //             self.view(),
    //             old(self).view().update(index as int, bit)
    //         );
    //     }
    //     ;
    // }
}

pub struct BitMap {
    bits: Vec<usize>,
}

impl BitMap {
    fn fa() {
        assert(usize::BITS == 32);
        // assert(usize::BITS == 64);

        // assert(usize::BITS == 1);
        // assert(index == 10);
    }
    spec fn view(&self) -> Seq<bool> {
        let width = self.bits@.len() * usize::BITS as nat;
        Seq::new(width, |i: int| u64_view(self.bits@[(i / usize::BITS.try_into().unwrap()) as int])[(i % usize::BITS.try_into().unwrap()) as int])
    }

    fn from(v: Vec<usize>) -> BitMap {
        BitMap { bits: v }
    }

    fn get_bit(&self, index: usize) -> (bit: bool)
        requires
            index < self@.len(),
        ensures
            bit == self@[index as int],
    {
        // REVIEW: at this moment, usize is assumed to be 32 or 64.
        // Therefore, if `index` is usize, verification fails due to the possibility of truncation
        // when we begin to consider `usize` smaller than 32, this might fail again.

        let seq_index: usize = index / usize::BITS;
        let bit_index: usize = index % usize::BITS;
        let bucket: usize = self.bits[seq_index];

        get_bit64_macro!(bucket, bit_index)
    }

    fn set_bit(&mut self, index: usize, bit: bool)
        requires
            index < old(self)@.len(),
        ensures
            self@ == old(self)@.update(index as int, bit),
    {
        // REVEIW: Same problem here with above regarding `usize`.
        let seq_index: usize = index / usize::BITS;
        let bit_index: usize = index % usize::BITS;
        let bv_old: usize = self.bits[seq_index];
        let bv_new: usize = set_bit64_macro!(bv_old, bit_index, bit);
        proof {
            set_bit64_proof(bv_new, bv_old, bit_index, bit);
        }
        ;
        self.bits.set(seq_index, bv_new);
        proof {
            assert_seqs_equal!(
                self.view(),
                old(self).view().update(index as int, bit)
            );
        }
        ;
    }

    bitwise-OR for bitmap
    fn or(&self, bm: &BitMap) -> (ret: BitMap)
        requires
            self@.len() == bm@.len(),
        ensures
            self@.len() == ret@.len(),
            forall|i: int| 0 <= i < ret@.len() ==> ret@[i] == (self@[i] || bm@[i]),
    {
        let n: usize = self.bits.len();
        let mut i: usize = 0;
        let mut res_bits: Vec<usize> = Vec::new();
        let mut result = BitMap { bits: res_bits };
        while i < n
            invariant
                i <= n,
                n == self.bits@.len(),
                n == bm.bits@.len(),
                i == result.bits.len(),
                forall|k: int|
                    0 <= k < i ==> or_u64_relation(self.bits@[k], bm.bits@[k], result.bits@[k]),
                forall|k: int| 0 <= k < i * 64 ==> result@[k] == (self@[k] || bm@[k]),
        {
            res_bits = result.bits;
            let u1: usize = self.bits[i];
            let u2: usize = bm.bits[i];
            let or_int: usize = u1 | u2;
            proof {
                bit_or_64_view_proof(u1, u2, or_int);
            }
            res_bits.push(or_int);
            result = BitMap { bits: res_bits };
            i = i + 1;
        }
        result
    }
}

} // verus!
#[verifier::external]
fn main() {}
