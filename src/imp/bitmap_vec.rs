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
        ensures res == 16,
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
    // fn alloc_contiguous(&mut self, size: u16, align_log2: u16) -> (res: Option<u16>)
    //     requires
    //         0 < size <= old(self)@.len(),
    //         align_log2 <= 4, // 0 <= align_log2 <= 4, meaning alignment is 1, 2, 4, 8 or 16.
    //     ensures match res {
    //         Some(base) => {
    //             // If successful, a contiguous block from `base` to `base + size` is allocated (set to false).
    //             // Other indices remain unchanged.
    //             get_bits16!(self.bits, base as u16, (base + size) as u16) == 0 &&
    //             forall|loc2: int|
    //                 (0 <= loc2 < base || (base + size) <= loc2  < 16) ==> self@[loc2] == old(self)@[loc2]
    //         },
    //         None => {
    //             // If failed, no suitable space was found, and the state is unchanged.
    //             // This implies either no free bits, or all free contiguous blocks are too small or misaligned.
    //             self.bits == 0 || self.spec_cap() < (1u16 << align_log2) ||
    //             forall|i: int| (0 <= i <= (16u16 - size) as int) && (i as u16 % (1u16 << align_log2) == 0)
    //                 ==> has_obstruction(self@, i, size as int)
    //                 // ==> exists |k: int| 0 <= k < size && #[trigger] self@[i+k] == false
    //             // true
    //         }
    //     },
    // {
    //     assert(self.spec_cap() == 16);
    //     if let Some(base) = find_contiguous(self, self.cap(), size, align_log2) {
    //         let start = base as u16;
    //         let end = (base + size) as u16;
    //         self.remove(start..end);
    //         Some(base)
    //     } else {
    //         None
    //     }
    // }

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
            res == (self.bits != 0),
    {
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
spec fn has_obstruction(ba: Seq<bool>, i: int, size: int, align: int) -> bool {
    (i % align != 0) ||
    exists |k: int| i <= k < i + size && #[trigger] ba[k] == false
}

/// If ba[k] == false, then for any i in (k - size, k],
/// the range [i, i + size) contains k, which is false.
/// So has_obstruction(ba, i, size) holds.
// proof fn lemma_bit_false_implies_has_obstruction(ba: Seq<bool>, size: int, k: int)
//     requires
//         ba[k] == false,
//     ensures
//         forall|i: int| k - size < i <= k ==> has_obstruction(ba, i, size),
// {
//     // Construct witness k
//     // assert(#[trigger] ba[k] == false);
//     // Therefore, exists k => has_obstruction
// }

// spec fn g(ba: Seq<bool>,j:int) -> bool {
//     ba[j] == false
// }
proof fn lemma_bit_false(ba: Seq<bool>, i: int, size: int, align: int)
    requires
        i % align != 0,
        // forall|j: int| start <= j <= end ==> #[trigger] ba[j] == false,
    ensures
        has_obstruction(ba,i,size,align),
{
}


// proof fn lemma_bit_false_implies_has_obstruction(ba: Seq<bool>, size: int, i: int, j: int)
//     requires
//         i <= j < i + size && ba[j] == false,
//     ensures
//         has_obstruction(ba, i, size),
// {
//     // Construct witness k
//     // assert(#[trigger] ba[k] == false);
//     // Therefore, exists k => has_obstruction
// }

// proof fn test_bit_false_implies_has_obstruction(ba: Seq<bool>, size: int, i: int)
//     requires
//         exists |j: int| i <= j < i + size && ba[j] == false
//     ensures
//         has_obstruction(ba, i, size)
// {
//     // Construct witness k
//     // lemma_bit_false_implies_has_obstruction(ba, size, i, choose|j: int| i <= j < i + size && ba[j] == false);
//     // Therefore, exists k => has_obstruction
// }


// spec fn has_obstruction_for_range(ba: Seq<bool>, k: int, size: int) -> bool {
//     // exists |k: int| 0 <= k < size && #[trigger] ba[i + k] == false
//     (forall|i: int| k - size < i <= k ==> #[trigger] has_obstruction(ba, i, size))
// // }

// proof fn prove_obstruction_for_range(
//     ba: Seq<bool>,
//     size: int,
//     start_k: int,
//     end_k: int,
// )
//     requires
//         0 <= start_k <= end_k < ba.len(), // 确保范围有效
//         forall|k: int| start_k <= k <= end_k ==> ba[k] == false, // 假设此范围内的所有 ba[k] 都为 false
//     ensures
//         forall|k: int| start_k <= k <= end_k ==> ba[k]== false
//         ==> (forall|i: int| k - size < i <= k ==> #[trigger] has_obstruction(ba, i, size)),
// {
//     // 在这里，您不需要显式地“调用” lemma_bit_false_implies_has_obstruction。
//     // Verus 的 SMT 求解器会自动利用已知的 proof fn 来证明 forall 语句。
//     // 如果需要，您可以使用 assert_by 来引导证明：
//     assert (forall|k: int| start_k <= k <= end_k ==>
//         ba[k]== false ==>
//         (forall|i: int| k - size < i <= k ==> has_obstruction(ba, i, size)));

//     // 通常，如果 lemma 的前置条件满足，Verus 会自动应用它。
// }

// proof fn lemma_all_aligned_windows_have_obstruction(
//     ba: Seq<bool>,
//     start: int,
//     end: int,
//     size: int,
//     align_log2: int,
//     capacity: int,
// )
//     requires
//         0 < size <= capacity,
//         0 <= align_log2 < 4,
//         start <= end,
//         ba.len() >= end + size,
//         forall |i: int|
//             start <= i < end + size ==> ba[i] == false,
//     ensures
//         forall |j: int|
//             start <= j < end &&
//             j as u16 % (1u16 << align_log2) == 0
//             ==> has_obstruction(ba, j, size),
// {
//     assert(forall |j: int|
//         start <= j < end &&
//         j as u16 % (1u16 << align_log2) == 0
//         ==>
//         {
//             lemma_bit_false_implies_has_obstruction(ba, j, size, j);
//             true
//         }
//     );
// }

spec fn is_even(i: int) -> bool {
    i % 2 == 0
}

proof fn test_use_forall_succeeds2(s: Seq<int>)
    requires
        5 <= s.len(),
        forall|i: int| 0 <= i < s.len() ==> is_even(#[trigger] s[i]),
{
    assert(is_even(s[3]));
    // assert(s[3] % 2 == 0);  // succeeds by triggering s[3]
}

// proof fn lemma_has_obstruction_all(ba: Seq<bool>, capacity: int, size: int, ali: int)
//     requires
//         has_obstruction(ba, 0, size),
//         has_obstruction(ba, 4, size),
//         has_obstruction(ba, 8, size),
//         0 < size <= capacity,
//         ali == 4,
//         capacity == 16,
//     ensures
//         forall|i: int| ((0 <= i < capacity - size) && (i % ali == 0)) ==> has_obstruction(ba, i, size),
// {
// }

// forall|i: int| (0 <= i <= capacity - size) && (i as u16 % (1u16 << align_log2) == 0)
//                 ==> has_obstruction(ba@, i, size as int)
// proof fn test_has_obstruction_subset() {
//     let ba = Seq::<bool>::new(16, |idx: int| idx != 3 && idx != 4 && idx != 5 && idx != 8 && idx != 9 && idx != 10 && idx !=15);
//     //  && idx != 4 && idx != 5 && idx != 8 && idx != 9 && idx != 10
//     // ba = [true, ..., true, false, true, ...]
//     // assert(ba[3int]== false);
//     // let m:int = 5int + 2int;
//     // let n:int = 7int;
//     let capacity:int = 16;
//     let size:int = 5;
//     let align_log2:u16 = 2;
//     // assert(ba[idx(5int,2int)] == false);
//     // lemma_bit_false_implies_has_obstruction(ba, 6, size, 8);
//     // assert forall|i: int| (3 <= i <= 5 || 8 <= i <= 10) implies ba[i]==false by {
//     //     assert(ba[i] == false);
//     // }
//     // // assert(forall|i: int| (3 <= i <= 5 || 8 <= i <= 10) ==> #[trigger] ba[i]==false);
//     // // assert(ba[9]== false);
//     // assert forall|i: int| (3 <= i <= 5 || 8 <= i <= 10) implies has_obstruction(ba, i, size) by {
//     //     assert(ba[i] == false);
//     // }
//     // lemma_bit_false_implies_has_obstruction(ba, 6, size, 8);
//     // lemma_bit_false_implies_has_obstruction(ba, 0, size, 5);
//     // lemma_bit_false_implies_has_obstruction(ba, 4, size, 5);
//     // assert forall|i: int| (3 <= i <= 5 || 8 <= i <= 10) implies has_obstruction(ba, i, size) by {
//     //     assert(ba[i] == false);
//     //     lemma_bit_false_implies_has_obstruction(ba,size,i);
//     // }
//     // assert(forall|i: int| ((0 <= i < 0) && (i as u16 % (1u16 << align_log2) == 0)) ==> #[trigger] has_obstruction(ba, i, size));
//     // assert(
//     //     forall |i: int| (3 <= i < 6 && ba[i] == false) ==> {
//     //         lemma_bit_false_implies_has_obstruction(ba, size, i);
//     //         true
//     //     }
//     // );

//     // assert(forall|k: int| 3 <= k < 6 ==> ba[k]== false
//     //     ==> (forall|i: int| k - size < i <= k ==> #[trigger] has_obstruction(ba, i, size)));
//     // prove_obstruction_for_range(ba,size,2,6);
//     // lemma_bit_false_implies_has_obstruction(ba,size,3);
//     // lemma_bit_false_implies_has_obstruction(ba,size,4);
//     // lemma_bit_false_implies_has_obstruction(ba,size,5);

//     // lemma_bit_false_implies_has_obstruction(ba,size,);
//     // assert(has_obstruction(ba, 0, size)) by {
//     //     assert(ba[3] == false);
//     // };
//     // assert(has_obstruction(ba, 1, size)) by {
//     //     assert(ba[3] == false);
//     // };
//     // assert(has_obstruction(ba, 2, size)) by {
//     //     assert(ba[3] == false);
//     // };

//     // assert forall|k: int| (3 <= k <= 5 && ba[k]== false) implies
//     //     (forall|i: int| k - size < i <= k ==> has_obstruction(ba, i, size)) by{
//     //         lemma_bit_false_implies_has_obstruction(ba,size,k);
//     //     }
//     // assert(has_obstruction(ba, 0, size));
//     // assert(has_obstruction(ba, 1, size));
//     // assert(has_obstruction(ba, 2, size));
//     // assert(has_obstruction(ba, 3, size));
//     // assert(has_obstruction(ba, 4, size));
//     // assert(has_obstruction(ba, 5, size));
//     // assert(has_obstruction(ba, 6, size));
//     // assert(has_obstruction(ba, 7, size));
//     // assert(align_log2 == 2);

//     // let align_log2:u16 = 2;
//     // let align:u16 = (1u16 << align_log2);
//     // assert(align == (1u16 << align_log2)) by(bit_vector)
//     //     requires
//     //         align == (1u16 << align_log2),
//     //         align_log2 <= 4;
//     // assert(forall|i: int| ((0 <= i < 8) && ((i % align as int) == 0)) ==> #[trigger] has_obstruction(ba, i, size));
//     // assert(forall|i: int| ((0 <= i < 8) && (i % 4 as int) == 0) ==> #[trigger] has_obstruction(ba, i, size));

//     // assert(4 == (1 << align_log2)) by (bit_vector);
//     // assert(ali == 4);
//     // assert forall|i: u16| ((0 <= i < 8) && (i % (1u16 << align_log2) == 0)) ==> #[trigger] has_obstruction(ba, i as int, size) by{
//     //     assert(i % (1u16 << align_log2) == 0) by (bit_vector)
//     //         requires
//     //             i % (1u16 << align_log2) == 0,
//     //             align_log2 <= 4,
//     //     ;
//     // };
//     // assert(forall|i: int| ((0 <= i < 8) && (i % ali == 0)) ==> #[trigger] has_obstruction(ba, i, size));

//     // lemma_bit_false_implies_has_obstruction(ba,size,10);
//     // assert(forall|i: int| ((0 <= i < 8) && (i % ali == 0)) ==> #[trigger] has_obstruction(ba, i, size));
//     // assert(forall|i: int| ((0 <= i < 12) && (i as u16 % (1u16 << align_log2) == 0)) ==> #[trigger] has_obstruction(ba, i, size));
//     // assert(has_obstruction(ba, 8, size));
//     // assert(has_obstruction(ba, 9, size));
//     // assert(has_obstruction(ba, 10, size));
//     // assert(has_obstruction(ba, 8, size));
//     // assert(0 <= 2 && 2 < 5 && ba[5int + 2int] == false);
//     // assert(exists |k: int|  3 <= #[trigger] k < 4);
//     // assert(!is_all_free(ba, 5, 5)); // 证明子范围 [5, 10) 不是所有位都空闲
//     // assert(has_obstruction_redefined(ba, 5, 5));

//     // let ali:int = (1 << 2) as int;
//     // assert(4 == (1 << 2)) by (compute);
//     // assert(ali == 4);
//     // lemma_has_obstruction_all(ba,capacity,size,ali);
//     assert(forall|j: int| 3 <= j <= 5 ==> #[trigger] ba[j] == false);
//     // assert(ba[3int] == false);
//     // assert(exists|j: int| 3 <= j <= 5 && #[trigger] ba[j] == false);


//     // test_bit_false_implies_has_obstruction(ba,size,3);
//     // assert(has_obstruction(ba, 0, size));
//     // assert(has_obstruction(ba, 1, size));
//     // assert(has_obstruction(ba, 2, size));
//     // assert(has_obstruction(ba, 3, size));
//     // assert(has_obstruction(ba, 4, size));

//     assert forall|i: int| ((0 <= i <= capacity - size) && (i as u16 % (1u16 << align_log2) == 0)) implies has_obstruction(ba, i, size) by {
//         assert(ba[3int]==false);
//         assert(ba[4int]==false);
//         assert(ba[5int]==false);
//         assert(ba[8int]==false);
//         assert(ba[9int]==false);
//         assert(ba[10int]==false);
//         assert(ba[15int]==false);
//         // assert(forall|j: int| 3 <= j <= 5 && ba[j] == false ==> #[trigger] ba[j] == false);
//         test_bit_false_implies_has_obstruction(ba,size,i);
//     };
//     // assert forall|i: int| ((0 <= i < capacity - size) && (i % ali == 0)) implies has_obstruction(ba, i, size) by {
//     //     assert forall|j: int| (3 <= j <= 5 || 8 <= j <= 10) implies has_obstruction(ba, i, size) by {
//     //         assert(ba[j] == false);
//     //     }
//     // }


//     // assert(forall|i: int| ((0 <= i < capacity - size) && (i % ali == 0)) ==> #[trigger] has_obstruction(ba, i, size));
//     // assert(forall|i: int| ((0 <= i <= capacity - size) && (i as u16 % (1u16 << align_log2) == 0)) ==> #[trigger] has_obstruction(ba, i, size));
// }

// spec fn is_all_free(ba: Seq<bool>, i: int, size: int) -> bool {
//     let all_true: bool = forall |k: int| 0 <= k < size ==> #[trigger] ba[i + k] == true;
//     all_true
// }

// spec fn has_obstruction_redefined(ba: Seq<bool>, i: int, size: int) -> bool {
//     !is_all_free(ba, i, size)
// }

// spec fn idx(i: int, k: int) -> int {
//     i + k
// }



// proof fn test_has_obstruction_false() {
//     let ba = Seq::<bool>::new(5, |idx: int| true);
//     // ba = [true, true, true, true, true]
//     let ans = has_obstruction(ba, 0, 5);
//     assert(!ans); // 证明所有位都空闲
// }

// proof fn test_has_obstruction_true() {
//     let ba = Seq::<bool>::new(5, |idx: int| idx != 2);
//     // ba = [true, true, false, true, true]
//     // assert(ba == [true, true, false, true, true]);
//     // assert(0 <= 2 && 2 < 5 && ba[0int + 2int] == false);
//     assert(ba[2int] == false);
//     // assert(ba[0int + 2int] == false);
//     // assert(ba[2int+0int] == false);
//     let ans = has_obstruction(ba, 0, 5);
//     // lemma_bit_false_implies_has_obstruction(ba, 0, 5, 2);
//     // assert(!ans);
//     assert(ans); // 证明不是所有位都空闲
// }



// proof fn test_is_all_free_false_with_witness() {
//     let ba = Seq::<bool>::new(5, |idx: int| idx != 2);
//     // ba = [true, true, false, true, true]
//     // To prove !forall P, we need to prove exists !P.
//     // In this case, we need to prove exists k such that !(0 <= k < 5 ==> ba[0 + k] == true)
//     // which simplifies to exists k such that (0 <= k < 5 && ba[0 + k] == false).
//     // We know k=2 is such a witness.
//     assert(0 <= 2 && 2 < 5 && ba[0int + 2int] == false);
//     assert(!is_all_free(ba, 0, 5));
// }

// spec fn has_obs2(ba: Seq<bool>, i: int, size: int) -> bool {
//     exists |i: int, k: int| ((0 <= i <= capacity - size) && (i as u16 % (1u16 << align_log2) == 0) && (0 <= k < size) && (#[trigger] ba[i+k] == false))
// }

// proof fn has_obs(ba: Seq<bool>, i: int, size: int)
//     requires
//         (0 <= i <= capacity - size) && (i as u16 % (1u16 << align_log2) == 0)
//     ensures
//         exists |k: int| 0 <= k < size && #[trigger] ba[i + k] == false
// {

// }

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
        capacity == 16,
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
            ba.bits == 0 || capacity < (1u16 << align_log2) ||
            // forall|i: int| (0 <= i <= capacity - size) && (i as u16 % (1u16 << align_log2) == 0)
            //     ==> has_obstruction(ba@, i, size as int)
            forall|i: int| (0 <= i <= capacity - size) ==> has_obstruction(ba@, i, size as int,(1u16 << align_log2) as int)
                // ==> exists |k: int| i <= k < i + size && #[trigger] ba@[k] == false
        }
    }
{
    assert(capacity==16);
    assert(capacity == ba@.len());
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
    // let mut next = base;
    while offset < capacity
        // invariant_except_break
        //     offset <= capacity,
        //     offset - base < size,
        //     forall|i: int| (0 <= i < base) && (i as u16 % (1u16 << align_log2) == 0)
        //         ==> has_obstruction(ba@, i, size as int)
        invariant
            offset <= capacity,
            offset - base < size,
            // forall|i: int| (0 <= i < base) && (i as u16 % (1u16 << align_log2) == 0)
            //     ==> has_obstruction(ba@, i, size as int),
            forall|i: int| (0 <= i < base) ==> has_obstruction(ba@, i, size as int, (1u16 << align_log2) as int),
            forall|i: int| (0 <= i < capacity) && (i % (1u16 << align_log2) as int != 0) ==> has_obstruction(ba@, i, size as int, (1u16 << align_log2) as int),
            capacity == 16,
            align_log2 <= 4,
            0 < size <= capacity,
            0 <= base <= offset,
            base % (1u16 << align_log2) == 0,
            forall|i: int| base <= i < offset ==> ba@.index(i),
        // ensures
        //     // offset == capacity && res.is_none() && (forall|i: int| (0 <= i <= capacity - size) && (i as u16 % (1u16 << align_log2) == 0) ==> has_obstruction(ba@, i, size as int))||
        //     // offset == capacity && res.is_some() && offset - base == size && (res.unwrap() == base) && forall|i: int| base <= i < base + size ==> ba@[i] == true ||
        //     // res.is_none() && (forall|i: int| (0 <= i <= capacity - size) && (i as u16 % (1u16 << align_log2) == 0) ==> has_obstruction(ba@, i, size as int))||
        //     (res.is_some() && offset - base == size && (res.unwrap() == base) && forall|i: int| base <= i < base + size ==> ba@[i] == true) ||
        //     (res.is_none() && forall|i: int| (0 <= i <= capacity - size) && (i as u16 % (1u16 << align_log2) == 0)
        //         ==> has_obstruction(ba@, i, size as int))

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
                // assert(forall|i: u16| (offset - size < i <= offset) ==> has_obstruction(ba@, i as int, size as int));
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
                // old_base = next;
                // assert(forall|i: int| (next <= i < base) ==> (i as u16 % #[trigger] (1u16 << align_log2) != 0));
                // assert((1u16 << align_log2)==4) by(bit_vector)
                //     requires
                //         align_log2 <= 4;
                // assume((1u16 << align_log2) <= base);
                // assert(old_base == next);

                // assert(forall|i: int| (0 <= i < capacity) && (i % (1u16 << align_log2) as int != 0) ==> has_obstruction(ba@, i, size as int, (1u16 << align_log2) as int));
                // assert forall|i: u16| (next <= i < base) implies has_obstruction(ba@, i as int, size as int, (1u16 << align_log2) as int) by{
                //     // assert(ba@[i as int] == false);
                //     assert(has_obstruction(ba@, i as int, size as int,(1u16 << align_log2) as int));
                // }


                // assert(forall|i: int| (0 <= i < base) && (i as u16 % (1u16 << align_log2) == 0)
                //     ==> has_obstruction(ba@, i, size as int, (1u16 << align_log2) as int));

                assert forall|i: u16| (next <= i < base) implies has_obstruction(ba@, i as int, size as int, (1u16 << align_log2) as int) by{
                    // assume(i % (1u16 << align_log2) != 0);
                    assert(i % (1u16 << align_log2) != 0) by (bit_vector)
                        requires
                            next <= i < base,
                            0 < next <= base,
                            base == (((((next - 1u16) as u16) >> align_log2) + 1u16) as u16) << align_log2,
                            0 <= align_log2 <= 4,
                    ;
                    // lemma_bit_false(ba@, i as int, size as int, (1u16 << align_log2) as int);
                    // assume(has_obstruction(ba@, i as int, size as int));
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

/// Finds a contiguous block of `size` free bits within the bitmap, respecting `align_log2`.
/// Returns the base index of the found block, or `None` if no such block exists.
// fn find_contiguous(ba: &BitAlloc16, capacity: u16, size: u16, align_log2: u16,) -> (res: Option<u16>)
//     requires
//         capacity == 16,
//         align_log2 <= 4,
//         0 < size <= capacity,
//     ensures
//     match res {
//         Some(base) => {
//             // If successful, a block of `size` free bits is found starting at `base`.
//             // The block must be within capacity, aligned, and all bits within the block must be free (true).
//             &&& base + size <= capacity
//             &&& base % (1u16 << align_log2) == 0
//             &&& forall|i: int| base <= i < base + size ==> ba@[i] == true //ba.next(i) != None
//         },
//         None => {
//             // If failed, no suitable block exists.
//             // This implies either no free bits, or all potential blocks are obstructed or misaligned.
//             // true
//             (ba.bits == 0) || (capacity < (1u16 << align_log2)) ||
//             forall|i: int| #![auto] ((0 <= i <= capacity - size) && (i as u16 % (1u16 << align_log2) == 0))
//                 // ==> has_obstruction(ba@, i, size as int)
//                 // ==> true
//                 ==>  exists |k: int| ((0 <= k < size) && (#[trigger] ba@[i+k] == false))
//             //这里貌似有问题！TODO
//         }
//     }
// {
//     if capacity < (1 << align_log2) || !ba.any() {
//         return None;
//     }

//     assert(ba.bits != 0);
//     let mut base = 0;
//     // Proof that initial base (0) is aligned.
//     assert(base % (1u16 << align_log2) == 0) by (bit_vector)
//         requires
//             base == 0,
//             align_log2 <= 4,
//     ;

//     let mut offset = base;
//     let mut res = None;
//     // let mut old_base = base;
//     while offset < capacity
//         invariant_except_break
//             offset - base < size,
//             res.is_none(),
//             forall|i: int| ((0 <= i < base) && (i as u16 % (1u16 << align_log2) == 0))
//                 ==> has_obstruction(ba@, i, size as int),
//             // exists |k: int| ((0 <= k < size) && (#[trigger] ba@[old_base+k] == false)),
//         invariant
//             capacity == 16,
//             align_log2 <= 4,
//             size > 0,
//             base % (1u16 << align_log2) == 0,
//             0 <= base,
//             base <= offset,
//             offset <= capacity,
//             forall|i: int| base <= i < offset ==> ba@.index(i),
//         ensures
//             //循环自然结束
//             (res.is_none() && offset == capacity && (forall|i: int| ((0 <= i < base) && (i as u16 % (1u16 << align_log2) == 0))
//                 ==> has_obstruction(ba@, i, size as int))) ||
//             //循环走的return None
//             (res.is_none() && offset < capacity && (forall|i: int| offset <= i < ba@.len() ==> ba@[i] == false)) ||
//             //循环走的return res
//             (res.is_some() && offset - base == size && (res.unwrap() == base) && forall|i: int| base <= i < base + size ==> ba@[i] == true)
//         decreases
//             capacity - offset,
//     {
//         if let Some(next) = ba.next(offset) {
//             assert(next < 16);
//             assert(offset - base < size);
//             assert(next >= offset);
//             assert(ba@[next as int] == true);
//             assert(forall|i: int| offset <= i < next ==> ba@[i] == false);
//             if next != offset {
//                 // assert(exists |k: int| ((0 <= k < size) && (#[trigger] ba@[i+k] == false)));
//                 // old_base = base;
//                 assert(next > offset);
//                 assert(forall|i: int| offset <= i < next ==> ba@[i] == false);
//                 assert(exists|i: int| offset <= i < next ==> ba@[i] == false);
//                 // assert(ba@[offset as int] == false);
//                 // assert(exists|i: int| ba@[i] == false);
//                 // (0 <= i <= capacity - size) && (i as u16 % (1u16 << align_log2) == 0)
//                 // assert(ba@[offset as int] == false);
//                 // assert(ba@[(offset as int) + 0] == false);
//                 assert(offset < base + size);

//                 let k = offset - base;
//                 assert(0 <= k < size);
//                 assert(ba@[(base as int) + k] == false);
//                 assert(exists |k: int|
//                     0 <= k < size && #[trigger] ba@[(base as int) + k] == false);
//                 assert(has_obstruction(ba@, base as int, size as int));
//                 assert(forall|i: int| ((0 <= i < base) && (i as u16 % (1u16 << align_log2) == 0))
//                     ==> has_obstruction(ba@, i, size as int));
//                 // assert(forall|i: int| ((0 <= i < base) && (i as u16 % (1u16 << align_log2) == 0))
//                 //     ==> has_obs2(ba@, i, size as int));
//                 // assert(exists |k: int| #[trigger] ba@[offset as int] == false);
//                 // assert(
//                 //     exists |k: int|
//                 //         0 <= k < size &&
//                 //         #[trigger] ba@[(offset as int) + k] == false
//                 // );
//                 // assert(
//                 //     exists |k: int|
//                 //         0 <= k < size &&
//                 //         #[trigger] ba@[(base as int) + k] == false
//                 // );
//                 // assume((0 <= base <= capacity - size) && (base as u16 % (1u16 << align_log2) == 0));
//                 // assert(exists |k: int| ((0 <= k < size) && (#[trigger] ba@[base+k] == false)));

//                 // forall|i: int| ((0 <= i < old_base) && (i as u16 % (1u16 << align_log2) == 0))
//                 // ==> has_obstruction(ba@, i, size as int),

//                 // assume(exists |k: int| ((0 <= k < size) && (#[trigger] ba@[base+k] == false)));
//                 // assert(has_obstruction(ba@, base as int, size as int));
//                 // assert(forall|i: int| ((0 <= i <= offset) && (i as u16 % (1u16 << align_log2) == 0))
//                 // ==> has_obstruction(ba@, i, size as int));

//                 assert(next > offset);
//                 assert(offset<=capacity);
//                 // it can be guarenteed that no bit in (offset..next) is free
//                 // move to next aligned position after next-1
//                 assert(next > 0);
//                 assert(((next - 1u16) as u16) >= 0);
//                 proof{
//                     safe_shr_u16_lemma(((next - 1u16) as u16),align_log2);
//                 }
//                 base = (((((next - 1u16) as u16) >> align_log2) + 1u16) as u16) << align_log2;
//                 // (((next - 1) >> align_log2) + 1) << align_log2 >= next
//                 proof{
//                     lemma_up_align_ge_original(next, align_log2);
//                 }
//                 assert(base >= next);
//                 offset = base;
//                 assert(offset >= next); // decreases
//                 assert(base % (1u16 << align_log2) == 0) by (bit_vector)
//                     requires
//                         base == (((((next - 1u16) as u16) >> align_log2) + 1u16) as u16) << align_log2,
//                         align_log2 <= 4,
//                 ;
//                 proof{
//                     lemma_up_align_le_capacity(next,align_log2);
//                 }
//                 assert(base <= capacity);
//                 assert(offset - base < size);


//                 // assume(forall|i: int| ((0 <= i < base) && (i as u16 % (1u16 << align_log2) == 0))
//                 //     ==> has_obstruction(ba@, i, size as int));
//                 continue;
//             }
//             assert(offset == next);

//         } else {
//             // No more free bits found from `offset` to `capacity`.
//             // forall|i: int| key <= i < self@.len() ==> self@[i] == false
//             assert(forall|i: int| offset <= i < ba@.len() ==> ba@[i] == false);
//             assert(res.is_none());
//             // assume((0 <= base <= capacity - size) && (base as u16 % (1u16 << align_log2) == 0));
//             // assert(exists |k: int| ((0 <= k < size) && (#[trigger] ba@[base+k] == false)));
//             // assume(exists |k: int| ((0 <= k < size) && (#[trigger] ba@[base+k] == false)));
//             // assert(has_obstruction(ba@, base as int, size as int));

//             // let k = offset - base;
//             // assert(0 <= k < size);
//             // assert(ba@[(base as int) + k] == false);
//             // assert(exists |k: int|
//             //     0 <= k < size && #[trigger] ba@[(base as int) + k] == false);
//             // assert(has_obstruction(ba@, base as int, size as int));

//             // assert(forall|i: int| ((0 <= i < capacity) && (i as u16 % (1u16 << align_log2) == 0))
//             //     ==> has_obstruction(ba@, i as int, size as int));
//             // assert(ba@[offset as int] == true);
//             assume(forall|i: int| ((0 <= i < base) && (i as u16 % (1u16 << align_log2) == 0))
//                 ==> has_obstruction(ba@, i, size as int));
//             return None;
//         }
//         assert(size > 0);
//         assert(offset - base < size);
//         offset += 1;
//         assert(offset > base);
//         if offset - base == size {
//             assert(offset - base == size);
//             assert(base + size == offset);
//             res = Some(base);
//             return res;
//         }
//     }
//     assume(forall|i: int| ((0 <= i < base) && (i as u16 % (1u16 << align_log2) == 0))
//         ==> has_obstruction(ba@, i, size as int));
//     // assume(forall|i: int| ((0 <= i <= capacity - size) && (i as u16 % (1u16 << align_log2) == 0))
//     //     ==> has_obstruction(ba@, i, size as int));
//     None
// }

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
