#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use core::ops::Range;
use vstd::{invariant, prelude::*, seq::*, seq_lib::*};

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

/// Converts a u16 value into a sequence of boolean bits.
pub open spec fn u16_view(u: u16) -> Seq<bool> {
    Seq::new(16, |i: int| get_bit16!(u, i as u16))
}

#[verifier::bit_vector]
proof fn set_bit_u16_preserves_others(bv_new: u16, bv_old: u16, index: u16, bit: bool)
    requires
        bv_new == set_bit16!(bv_old, index, bit),
        index < 16,
    ensures
        get_bit16!(bv_new, index) == bit,
        forall|loc2: u16|
            (loc2 < 16 && loc2 != index) ==> (get_bit16!(bv_new, loc2) == get_bit16!(bv_old, loc2)),
{
}

#[verifier::bit_vector]
proof fn set_bits_u16_preserves_others(bv_new: u16, bv_old: u16, st:u16, ed:u16, val: u16)
    requires
        st < 16,
        ed <= 16,
        st < ed,
        // Ensure `val` fits within the specified bit range (ed - st).
        val << ((u16::BITS) as u16 - (ed - st)) as usize >>
            ((u16::BITS) as u16 - (ed - st)) as usize == val,
        bv_new == set_bits16!(bv_old, st, ed, val),
    ensures
        get_bits16!(bv_new, st, ed) == val,
        forall|loc2: u16|
            (0 <= loc2 < st || ed <= loc2 < 16) ==> (get_bit16!(bv_new, loc2) == get_bit16!(bv_old, loc2)),
{
}

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

/// A generic trait which provides methods for extracting and setting specific bits or ranges of
/// bits.
pub trait BitField {
    /// Specification function to view the internal u16 as a sequence of booleans.
    spec fn view(&self) -> Seq<bool>;

    /// Returns the length, eg number of bits, in this bit field.
    fn bit_length() -> u16;

    /// Gets the boolean value of a specific bit at `index`.
    fn get_bit(&self, index: u16) -> bool;

    /// Extracts a range of bits from the bitmap as a u16 value.
    fn get_bits(&self, range: Range<u16>) -> u16;

    /// Sets the boolean value of a specific bit at `index`.
    fn set_bit(&mut self, index: u16, value: bool);

    /// Sets a range of bits in the bitmap to a given u16 value.
    fn set_bits(&mut self, range: Range<u16>, value: u16);
}

impl BitField for u16{
    /// Specification function to view the internal u16 as a sequence of booleans.
    open spec fn view(&self) -> Seq<bool> {
        Seq::new(16, |i: int| *self & (1u16 << i) != 0)
    }

    /// Returns the length, eg number of bits, in this bit field.
    fn bit_length() -> u16 { 16 }

    /// Gets the boolean value of a specific bit at `index`.
    fn get_bit(&self, index: u16) -> (bit: bool)
        requires
            index < BitField::view(&self).len(),
        ensures
            bit == BitField::view(&self)[index as int],
    {
        let bit_index: u16 = index % 16;

        get_bit16_macro!(*self, bit_index as u16)
    }

    /// Extracts a range of bits from the bitmap as a u16 value.
    fn get_bits(&self, range:Range<u16>) -> (bits:u16)
        requires
            range.start < BitField::view(&self).len(),
            range.end <= BitField::view(&self).len(),
            range.start < range.end,
        ensures
            forall|i: int| 0 <= i < (range.end - range.start) ==> bits.get_bit(i) == BitField::view(&self)[range.start + i],
    {
        let bv_gets = get_bits16_macro!(*self, range.start, range.end);
        proof {
            get_bits_u16_correctness(bv_gets, *self, range.start, range.end);
        };
        bv_gets
    }

    /// Sets the boolean value of a specific bit at `index`.
    fn set_bit(&mut self, index: u16, bit: bool)
        requires
            index < BitField::view(old(self)).len(),
        ensures
            BitField::view(&self) == BitField::view(old(self)).update(index as int, bit),
    {
        let bit_index: u16 = index % 16;
        let bv_old: u16 = *self;
        let bv_new: u16 = set_bit16_macro!(bv_old, bit_index as u16, bit);
        proof {
            set_bit_u16_preserves_others(bv_new, bv_old, bit_index as u16, bit);
        }
        ;
        *self = bv_new;
        proof {
            assert_seqs_equal!(
                self.view(),
                old(self).view().update(index as int, bit)
            );
        }
        ;
    }

    /// Sets a range of bits in the bitmap to a given u16 value.
    fn set_bits(&mut self, range: Range<u16>, value: u16)
        requires
            range.start < BitField::view(old(self)).len(),
            range.end <= BitField::view(old(self)).len(),
            range.start < range.end,
            // Ensure `value` fits within the specified bit range.
            value << ((u16::BITS) as u16 - (range.end - range.start)) as usize >>
                ((u16::BITS) as u16 - (range.end - range.start)) as usize == value,
        ensures
            get_bits16!(*self, range.start, range.end) == value,
            forall|loc2: int|
                (0 <= loc2 < range.start || range.end <= loc2  < 16) ==> BitField::view(&self)[loc2] == BitField::view(old(self))[loc2],
    {
        let bv_old: u16 = *self;
        let bv_new: u16 = set_bits16_macro!(bv_old, range.start, range.end, value);
        proof {
            set_bits_u16_preserves_others(bv_new, bv_old, range.start, range.end, value);
        }
        *self = bv_new;
        assert(get_bits16!(bv_new, range.start, range.end) == value);
    }
}
}

#[verifier::external]
fn main() {}
