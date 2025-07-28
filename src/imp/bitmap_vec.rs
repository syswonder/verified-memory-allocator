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
spec fn u16_view(u: u16) -> Seq<bool> {
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

/// Proof that if a u16 value is non-zero, its `trailing_zeros()` count must be less than 16.
pub proof fn prove_nonzero_has_trailing_zeros(bits: u16)
    requires bits != 0,
    ensures bits.trailing_zeros() < 16,
{
}

/// Represents a 16-bit bitmap allocator.
pub struct BitAlloc16 {
    bits: u16,
}

impl BitAlloc16 {
    /// The maximum capacity of the bitmap (16 bits).
    fn cap(&self) -> (res:u16)
        ensures res == self.spec_cap(),
    {
        16
    }

    pub open spec fn spec_cap(&self) -> (res:u16){
        16
    }

    /// Creates a new `BitmapAllocator16` with all bits set to 0 (all free).
    fn default() -> Self {
        BitAlloc16 { bits: 0 }
    }

    /// Specification function to view the internal u16 as a sequence of booleans.
    spec fn view(&self) -> Seq<bool> {
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

    /// Sets the boolean value of a specific bit at `index`.
    fn set_bit(&mut self, index: u16, bit: bool)
        requires
            index < old(self)@.len(),
        ensures
            self@ == old(self)@.update(index as int, bit),
    {
        let bit_index: u16 = index % 16;
        let bv_old: u16 = self.bits;
        let bv_new: u16 = set_bit16_macro!(bv_old, bit_index as u16, bit);
        proof {
            set_bit_u16_preserves_others(bv_new, bv_old, bit_index as u16, bit);
        }
        ;
        self.bits = bv_new;
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
            range.start < old(self)@.len(),
            range.end <= old(self)@.len(),
            range.start < range.end,
            // Ensure `value` fits within the specified bit range.
            value << ((u16::BITS) as u16 - (range.end - range.start)) as usize >>
                ((u16::BITS) as u16 - (range.end - range.start)) as usize == value,
        ensures
            get_bits16!(self.bits, range.start, range.end) == value,
            forall|loc2: int|
                (0 <= loc2 < range.start || range.end <= loc2  < 16) ==> self@[loc2] == old(self)@[loc2],
    {
        let bv_old: u16 = self.bits;
        let bv_new: u16 = set_bits16_macro!(bv_old, range.start, range.end, value);
        proof {
            set_bits_u16_preserves_others(bv_new, bv_old, range.start, range.end, value);
        }
        self.bits = bv_new;
        assert(get_bits16!(bv_new, range.start, range.end) == value);
    }

    /// Allocates a single free bit (represented by 1) and sets it to 0 (allocated).
    /// Returns `Some(index)` if successful, `None` if no free bits are available.
    fn alloc(&mut self) -> (res: Option<u16>)
        ensures match res {
            Some(i) => {
                // If successful, a previously free index `i` is now allocated (set to false).
                // Other indices remain unchanged.
                self@ == old(self)@.update(i as int, false)
            },
            None => {
                // If failed, all bits were already allocated (self.bits is 0), and the state is unchanged.
                self.bits == 0
            },
        },
    {
        if !self.any() {
            return None;
        }
        proof {
            prove_nonzero_has_trailing_zeros(self.bits);  // Prove that if self.bits != 0, trailing_zeros() < 16.
        }
        // Find the first free bit (least significant 1-bit).
        let i = self.bits.trailing_zeros() as u16;
        assert(i<16);

        let bv_old: u16 = self.bits;
        let bv_new: u16 = set_bit16_macro!(bv_old, i as u16, false);
        proof {
            set_bit_u16_preserves_others(bv_new, bv_old, i as u16, false);
        }
        ;
        self.bits = bv_new;
        proof {
            assert_seqs_equal!(
                self.view(),
                old(self).view().update(i as int, false)
            );
        }
        Some(i)
    }

    /// Allocates a contiguous block of `size` bits with specified `align_log2` alignment.
    /// Returns `Some(base_index)` if successful, `None` if no suitable block is found.
    fn alloc_contiguous(&mut self, size: u16, align_log2: u16) -> (res: Option<u16>)
        requires
            0 < size <= old(self)@.len(),
            align_log2 <= 4, // 0 <= align_log2 <= 4, meaning alignment is 1, 2, 4, 8 or 16.
        ensures match res {
            Some(base) => {
                // If successful, a contiguous block from `base` to `base + size` is allocated (set to false).
                // Other indices remain unchanged.
                get_bits16!(self.bits, base as u16, (base + size) as u16) == 0 &&
                forall|loc2: int|
                    (0 <= loc2 < base || (base + size) <= loc2  < 16) ==> self@[loc2] == old(self)@[loc2]
            },
            None => {
                // If failed, no suitable space was found, and the state is unchanged.
                // This implies either no free bits, or all free contiguous blocks are too small or misaligned.
                self.bits == 0 || self.spec_cap() < (1u16 << align_log2) ||
                forall|i: int| (0 <= i <= (self.spec_cap() - size) as int) ==> has_obstruction(self@, i, size as int,(1u16 << align_log2) as int)
                    // ==> exists |k: int| 0 <= k < size && #[trigger] self@[i+k] == false
                // true
            }
        },
    {
        assert(self.spec_cap() == 16);
        if let Some(base) = find_contiguous(self, self.cap(), size, align_log2) {
            let start = base as u16;
            let end = (base + size) as u16;
            self.remove(start..end);
            Some(base)
        } else {
            None
        }
    }

    /// Deallocates a single bit at `index` by setting it to 1 (free).
    fn dealloc(&mut self, index: u16)
        requires
            index < old(self)@.len(),
        ensures
            self@ == old(self)@.update(index as int, true),
    {
        self.set_bit(index, true);
    }

    /// Marks a range of bits as free (sets them to 1).
    fn insert(&mut self, range: Range<u16>)
        requires
            range.start < old(self)@.len(),
            range.end <= old(self)@.len(),
            range.start < range.end,
        ensures
            get_bits16!(self.bits, range.start, range.end) == (0xffffu16 >> (16 - (range.end - range.start))),
            forall|loc2: int|
                (0 <= loc2 < range.start || range.end <= loc2  < 16) ==> self@[loc2] == old(self)@[loc2],
    {
        let width = range.end - range.start;
        let insert_val = 0xffffu16 >> (16 - width);

        // Proof that insert_val's higher (16 - width) bits are zero.
        assert((0xffffu16 >> (16 - width) as u16) << ((u16::BITS) as u16 - width) as u16 >>
        ((u16::BITS) as u16 - width) as u16 == (0xffffu16 >> (16 - width) as u16)) by (bit_vector);

        self.set_bits(range, insert_val);
    }

    /// Marks a range of bits as allocated (sets them to 0).
    fn remove(&mut self, range: Range<u16>)
        requires
            range.start < old(self)@.len(),
            range.end <= old(self)@.len(),
            range.start < range.end,
        ensures
            forall|loc2: int|
                (0 <= loc2 < range.start || range.end <= loc2 < 16) ==> self@[loc2] == old(self)@[loc2],
            get_bits16!(self.bits, range.start, range.end) == 0,

    {
        let value:u16 = 0;
        let width = range.end - range.start;
        assert(((u16::BITS) as u16 - width) >= 0);
        assert(0u16 << ((u16::BITS) as u16 - width) as usize >>
        ((u16::BITS) as u16 - width) as usize == 0u16) by (bit_vector);
        self.set_bits(range, value);
    }

    /// Checks if there are any free bits (bits set to 1) in the bitmap.
    fn any(&self) -> (res:bool)
        ensures
            // res == (self.bits != 0),
            res == self.spec_any(),
    {
        self.bits != 0
    }

    spec fn spec_any(&self) -> bool{
        self.bits != 0
    }

    /// Tests if a specific bit at `index` is free (1) or allocated (0).
    fn test(&self, index: u16) -> (res:bool)
        requires
            index < self@.len(),
        ensures
            res == (get_bit16_macro!(self.bits, index as u16)),
    {
        self.get_bit(index)
    }

    /// Finds the next free bit (1) starting from `key` (inclusive).
    /// Returns `Some(index)` of the next free bit, or `None` if no free bits are found.
    fn next(&self, key: u16) -> (res: Option<u16>)
        requires
            key < self@.len(),
        ensures match res {
            Some(re) => {
                // If successful, returns the first free index `re` that is not less than `key`.
                // All indices between `key` and `re` (exclusive) must be allocated (false).
                &&& self@[re as int] == true
                &&& re < self@.len()
                &&& re >= key
                &&& forall|i: int| key <= i < re ==> self@[i] == false
            },
            None => {
                // If failed, all indices from `key` to the end are allocated (false).
                forall|i: int| key <= i < self@.len() ==> self@[i] == false
            }
        },
    {
        let n = u16::BITS as u16;
        let mut result = None;
        let mut i = key;
        assert(i<n);
        while i < n
            invariant_except_break
                result.is_none(),
            invariant
                key <= i <= n,
                n == self@.len(),
                forall|k: int|
                    key <= k < i ==> self@[k] == false,
            ensures
                (i == n && result.is_none()) ||  (i < n && result.is_some() && (result.unwrap() == i) && self@[i as int] == true),
            decreases
                n-i,
        {
            if self.get_bit(i) {
                result = Some(i);
                break;
            }
            i += 1;
        }
        result
    }
}

/// Specification function to check if a contiguous block starting at `i` of `size` contains any allocated bits (false).
/// or `i` is not a multiple of `align`
spec fn has_obstruction(ba: Seq<bool>, i: int, size: int, align: int) -> bool {
    (i % align != 0) ||
    exists |k: int| i <= k < i + size && #[trigger] ba[k] == false
}

#[verifier::bit_vector]
proof fn safe_shr_u16_lemma(x: u16, shift: u16)
    requires shift < 16
    ensures (x >> shift) <= x,
{
}

/// Finds a contiguous block of `size` free bits within the bitmap, respecting `align_log2`.
/// Returns the base index of the found block, or `None` if no such block exists.
fn find_contiguous(ba: &BitAlloc16, capacity: u16, size: u16, align_log2: u16,) -> (res: Option<u16>)
    requires
        capacity == ba.spec_cap(),
        align_log2 <= 4,
        0 < size <= capacity,
    ensures
        match res {
            Some(base) => {
                // If successful, a block of `size` free bits is found starting at `base`.
                // The block must be within capacity, aligned, and all bits within the block must be free (true).
                &&& base + size <= capacity
                &&& base % (1u16 << align_log2) == 0
                &&& forall|i: int| base <= i < base + size ==> ba@[i] == true //ba.next(i) != None
            },
            None => {
                // If failed, no suitable block exists.
                // This implies either no free bits, or all potential blocks are obstructed or misaligned.
                // ba.bits == 0 || capacity < (1u16 << align_log2) ||
                !ba.spec_any() || capacity < (1u16 << align_log2) ||
                forall|i: int| (0 <= i <= capacity - size) ==> has_obstruction(ba@, i, size as int,(1u16 << align_log2) as int)
            }
        }
{
    // assert(capacity==16);
    assert(capacity == ba.spec_cap());
    if capacity < (1 << align_log2) || !ba.any() {
        return None;
    }

    assert(ba.bits != 0);
    let mut base = 0;
    // Proof that initial base (0) is aligned.
    assert(base % (1u16 << align_log2) == 0) by (bit_vector)
        requires
            base == 0,
            align_log2 <= 4,
    ;

    let mut offset = base;
    let mut res = None;
    while offset < capacity
        invariant
            offset <= capacity,
            offset - base < size,
            forall|i: int| (0 <= i < base) ==> has_obstruction(ba@, i, size as int, (1u16 << align_log2) as int),
            forall|i: int| (0 <= i < capacity) && (i % (1u16 << align_log2) as int != 0) ==> has_obstruction(ba@, i, size as int, (1u16 << align_log2) as int),
            capacity == 16,
            align_log2 <= 4,
            0 < size <= capacity,
            0 <= base <= offset,
            base % (1u16 << align_log2) == 0,
            forall|i: int| base <= i < offset ==> ba@.index(i),
        decreases
            capacity - offset,
    {
        if let Some(next) = ba.next(offset) {
            assert(next < 16);
            assert(offset - base < size);
            assert(next >= offset);
            assert(ba@[next as int] == true);
            if next != offset {
                assert(next > offset);
                assert(offset<=capacity);
                // it can be guarenteed that no bit in (offset..next) is free
                // move to next aligned position after next-1
                assert(next > 0);

                assert(ba@[offset as int] == false);
                assert(forall|i: u16| (offset - size < i <= offset) ==> has_obstruction(ba@, i as int, size as int, (1u16 << align_log2) as int));

                assert(((next - 1u16) as u16) >= 0);
                proof{
                    safe_shr_u16_lemma(((next - 1u16) as u16),align_log2);
                }
                base = (((((next - 1u16) as u16) >> align_log2) + 1u16) as u16) << align_log2;
                proof{
                    lemma_up_align_ge_original(next, align_log2);
                }
                assert(base >= next);

                assert(forall|i: int| (offset <= i < next) ==> (ba@[i] == false));
                // lemma_bit_false_implies_has_obstruction(ba@,);
                assert forall|i: u16| (offset <= i < next) implies has_obstruction(ba@, i as int, size as int, (1u16 << align_log2) as int) by{
                    assert(ba@[i as int] == false);
                }

                offset = base;
                assert(offset >= next); // decreases
                assert(base % (1u16 << align_log2) == 0) by (bit_vector)
                    requires
                        base == (((((next - 1u16) as u16) >> align_log2) + 1u16) as u16) << align_log2,
                        align_log2 <= 4,
                ;
                proof{
                    lemma_up_align_le_capacity(next,align_log2);
                }
                assert(base <= capacity);
                assert(offset - base < size);
                assert forall|i: u16| (next <= i < base) implies has_obstruction(ba@, i as int, size as int, (1u16 << align_log2) as int) by{
                    assert(i % (1u16 << align_log2) != 0) by (bit_vector)
                        requires
                            next <= i < base,
                            0 < next <= base,
                            base == (((((next - 1u16) as u16) >> align_log2) + 1u16) as u16) << align_log2,
                            0 <= align_log2 <= 4,
                    ;
                }
                continue;
            }
            assert(offset == next);

        } else {
            // No more free bits found from `offset` to `capacity`.
            assert(ba@[offset as int] == false);
            assert(forall|i: u16| (offset - size < i <= offset) ==> has_obstruction(ba@, i as int, size as int, (1u16 << align_log2) as int));
            assert forall|i: u16| (offset <= i < capacity) implies has_obstruction(ba@, i as int, size as int, (1u16 << align_log2) as int) by{
                assert(ba@[i as int] == false);
            }
            return None;
        }
        assert(size > 0);
        assert(offset - base < size);
        offset += 1;
        assert(offset > base);
        if offset - base == size {
            assert(offset - base == size);
            assert(base + size == offset);
            res = Some(base);
            return res;
        }
    }
    None
}

/// Lemma to prove that aligning `next` upwards results in a value greater than or equal to `next`.
#[verifier::bit_vector]
proof fn lemma_up_align_ge_original(next:u16, align_log2:u16)
    requires 0 < next < 16, align_log2 <= 4,
    ensures (((((next - 1u16) as u16) >> align_log2) + 1u16) as u16) << align_log2 >= next
{
}

/// Lemma to prove that aligning `next` upwards results in a value less than or equal to the capacity (16).
#[verifier::bit_vector]
proof fn lemma_up_align_le_capacity(next:u16, align_log2:u16)
    requires 0 < next < 16, align_log2 <= 4,
    ensures (((((next - 1u16) as u16) >> align_log2) + 1u16) as u16) << align_log2 <= 16
{
}

}
#[verifier::external]
fn main() {}
