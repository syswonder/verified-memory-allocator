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
global layout usize is size == 8;

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

// proof fn
/*
/// Allocator of a bitmap, able to allocate / free bits.
pub trait BitAlloc: BitAllocView{
    /// Allocate a free bit.
    fn alloc(&mut self) -> Option<usize>;

    /// Allocate a free block with a given size, and return the first bit position.
    fn alloc_contiguous(&mut self, size: usize, align_log2: usize) -> Option<usize>
        requires
            0 < size <= old(self).spec_cap(),
            align_log2 < 64,
    ;

    /// Free an allocated bit.
    fn dealloc(&mut self, key: usize)
        requires
            key < old(self).spec_cap(),
    ;

    /// Mark bits in the range as unallocated (available)
    fn insert(&mut self, range: Range<usize>)
        requires
            range.start < old(self).spec_cap(),
            range.end <= old(self).spec_cap(),
            range.start < range.end,
    ;

    /// Reverse of insert
    fn remove(&mut self, range: Range<usize>)
        requires
            range.start < old(self).spec_cap(),
            range.end <= old(self).spec_cap(),
            range.start < range.end,
    ;
}
 */
pub trait BitAllocView {
    /// Specification function to view the internal u16 as a sequence of booleans.
    spec fn view(&self) -> Seq<bool> ;

    /// The bitmap has a total of CAP bits, numbered from 0 to CAP-1 inclusively.
    fn cap() -> (res:usize)
        requires
            Self::cascade_not_overflow(),
        ensures
            res == Self::spec_cap(),
    ;

    spec fn spec_cap() -> (res:usize);

    spec fn cascade_not_overflow() -> bool;

    /// The default value. Workaround for `const fn new() -> Self`.
    fn default() -> Self where Self: Sized;

    /// Find a index not less than a given key, where the bit is free.
    fn next(&self, key: usize) -> (res: Option<usize>)
        requires
            Self::cascade_not_overflow(),
            key < Self::spec_cap(),
        ensures match res {
            Some(re) => {
                // If successful, returns the first free index `re` that is not less than `key`.
                // All indices between `key` and `re` (exclusive) must be allocated (false).
                &&& self@[re as int] == true
                &&& re < Self::spec_cap()
                &&& re >= key
                &&& forall|i: int| key <= i < re ==> self@[i] == false
            },
            None => {
                // If failed, all indices from `key` to the end are allocated (false).
                forall|i: int| key <= i < Self::spec_cap() ==> self@[i] == false
            }
        },
    ;

    /// Whether there are free bits remaining
    fn any(&self) -> (res:bool)
        ensures res == self.spec_any();

    spec fn spec_any(&self) -> bool;

    /// Whether a specific bit is free
    fn test(&self, key: usize) -> bool
        requires
            Self::cascade_not_overflow(),
            key < Self::spec_cap(),
    ;
}

/// A bitmap of 256 bits
pub type BitAlloc256 = BitAllocCascade16<BitAlloc16>; //8
/// A bitmap of 4K bits
pub type BitAlloc4K = BitAllocCascade16<BitAlloc256>; //12
/// A bitmap of 64K bits
pub type BitAlloc64K = BitAllocCascade16<BitAlloc4K>; //16
/// A bitmap of 1M bits
pub type BitAlloc1M = BitAllocCascade16<BitAlloc64K>; //20

/// Implement the bit allocator by segment tree algorithm.    BitAlloc +
pub struct BitAllocCascade16<T:BitAllocView> {
    pub bitset: BitAlloc16, // for each bit, 1 indicates available, 0 indicates inavailable
    pub sub: [T; 16],
}

impl<T: BitAllocView + std::marker::Copy> BitAllocView for BitAllocCascade16<T> {
    open spec fn view(&self) -> Seq<bool> {
        // 把 16 个子分配器的 view 拼接在一起
        let sub_len = self.sub[0].view().len() as int;
        Seq::new((sub_len * 16) as nat, |idx: int| {
            let i   = idx / sub_len;                   // 第几个子分配器
            let off = idx % sub_len;                   // 子分配器内偏移
            self.sub[i as int].view()[off as int]           // 取对应 bit
        })
    }

    // 每个子分配器的容量都是固定且相等的
    fn cap() -> (res:usize) {
        (T::cap() * 16) as usize
    }

    open spec fn spec_cap() -> (res:usize){
        (T::spec_cap() * 16) as usize
    }

    open spec fn cascade_not_overflow() -> bool {
        T::cascade_not_overflow() && T::spec_cap() * 16 < usize::MAX
    }

    /// Creates a new `BitAllocCascade16` with all bits set to 0 (all free).
    fn default() -> Self {
        BitAllocCascade16 {
            bitset: BitAlloc16 { bits: 0 },
            sub: [T::default(); 16], // need the trait "std::marker::Copy"
        }
    }

    /// Checks if there are any free bits (bits set to 1) in the bitmap.
    fn any(&self) -> (res:bool){
        self.bitset.any()
    }

    open spec fn spec_any(&self) -> bool{
        self.bitset.spec_any()
    }

    /// Tests if a specific bit at `index` is free (1) or allocated (0).
    fn test(&self, index: usize) -> (res:bool)
    {
        let seq_index: usize = index / T::cap(); //证明seq_index < 16

        assert(seq_index < 16) by(nonlinear_arith)
            requires
                seq_index == index / T::spec_cap(),
                Self::spec_cap() == T::spec_cap() * 16,
                index < Self::spec_cap(),
                index < (T::spec_cap() * 16),
                T::spec_cap() > 0,
        ;

        let bit_index: usize = index % T::cap();
        self.sub[seq_index].test(bit_index)
    }

    /// Finds the next free bit (1) starting from `key` (inclusive).
    /// Returns `Some(index)` of the next free bit, or `None` if no free bits are found.
    fn next(&self, key: usize) -> (res: Option<usize>){
        let idx: usize = key / T::cap();

        assert(idx < 16) by(nonlinear_arith)
            requires
                idx == key / T::spec_cap(),
                Self::spec_cap() == T::spec_cap() * 16,
                key < Self::spec_cap(),
                key < (T::spec_cap() * 16),
                T::spec_cap() > 0,
        ;

        let mut i = idx;
        while i < 16
            invariant
                i <= 16,
                Self::cascade_not_overflow(),
                key < Self::spec_cap(),
                forall|k: int|
                    idx <= k < i ==> self.bitset@[k] == false,
        {
            if self.bitset.get_bit(i as u16) {
                let key = if i == idx {
                    assert(i == idx);
                    assume(key >= T::spec_cap() * idx);
                    key - T::cap() * idx
                } else {
                    0
                };
                assume(key < T::spec_cap());
                // if let Some(offset) = self.sub[i].next(key) {
                //     assert(offset >= key);
                //     assert(i<=15);
                //     assume(offset < T::spec_cap());
                //     assume((offset + T::spec_cap() * i) < Self::spec_cap());
                //     return Some(offset + T::cap() * i)
                // }
                // let Some(offset) = self.sub[i].next(key);// 这里要先保证16叉树成型，即上一层有空闲位，则下一层必能返回Some
                return Some((self.sub[i].next(key)).unwrap() + T::cap() * i);
                // self.sub[i].next(key).map(|x| x + T::cap() * i)
            }
            i += 1;
        }
        None

        // let n = u16::BITS as u16;
        // let mut result = None;
        // let mut i = key as u16;
        // assert(i<n);
        // while i < n
        //     invariant_except_break
        //         result.is_none(),
        //     invariant
        //         key <= i <= n,
        //         n == Self::spec_cap(),
        //         forall|k: int|
        //             key <= k < i ==> self@[k] == false,
        //     ensures
        //         (i == n && result.is_none()) ||  (i < n && result.is_some() && (result.unwrap() == i as usize) && self@[i as int] == true),
        //     decreases
        //         n-i,
        // {
        //     if self.get_bit(i) {
        //         result = Some(i as usize);
        //         break;
        //     }
        //     i += 1;
        // }
        // result
    }
}
/// Represents a 16-bit bitmap allocator.
pub struct BitAlloc16 {
    pub bits: u16,
}

impl BitAlloc16 {
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
}

impl BitAllocView for BitAlloc16 {
    /// Specification function to view the internal u16 as a sequence of booleans.
    open spec fn view(&self) -> Seq<bool> {
        let width = Self::spec_cap() as nat;
        Seq::new(width, |i: int| u16_view(self.bits@)[i])
    }

    /// The maximum capacity of the bitmap (16 bits).
    fn cap() -> (res:usize) {
        // Some(16)
        16
    }

    open spec fn spec_cap() -> (res:usize){
        // Some(16)
        16
    }

    open spec fn cascade_not_overflow() -> bool {
        true
    }

    /// Creates a new `BitmapAllocator16` with all bits set to 0 (all free).
    fn default() -> Self {
        BitAlloc16 { bits: 0 }
    }

    /// Checks if there are any free bits (bits set to 1) in the bitmap.
    fn any(&self) -> (res:bool){
        self.bits != 0
    }

    open spec fn spec_any(&self) -> bool{
        self.bits != 0
    }

    /// Tests if a specific bit at `index` is free (1) or allocated (0).
    fn test(&self, index: usize) -> (res:bool)
        ensures
            res == (get_bit16_macro!(self.bits, index as u16)),
    {
        // let bit_index = (index % 16) as u16;
        self.get_bit(index as u16)
    }

    /// Finds the next free bit (1) starting from `key` (inclusive).
    /// Returns `Some(index)` of the next free bit, or `None` if no free bits are found.
    fn next(&self, key: usize) -> (res: Option<usize>){
        let n = u16::BITS as u16;
        let mut result = None;
        let mut i = key as u16;
        assert(i<n);
        while i < n
            invariant_except_break
                result.is_none(),
            invariant
                key <= i <= n,
                n == Self::spec_cap(),
                forall|k: int|
                    key <= k < i ==> self@[k] == false,
            ensures
                (i == n && result.is_none()) ||  (i < n && result.is_some() && (result.unwrap() == i as usize) && self@[i as int] == true),
            decreases
                n-i,
        {
            if self.get_bit(i) {
                result = Some(i as usize);
                break;
            }
            i += 1;
        }
        result
    }
}
/*
impl BitAlloc for BitAlloc16 {
    /// Allocates a single free bit (represented by 1) and sets it to 0 (allocated).
    /// Returns `Some(index)` if successful, `None` if no free bits are available.
    fn alloc(&mut self) -> (res: Option<usize>)
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
        // Find the first free bit (least significant 1-bit).
        let i = self.bits.trailing_zeros() as u16;
        assert(i < u16::BITS) by{
            assert(self.bits != 0); // Prove that if self.bits != 0, trailing_zeros() < 16.
        };

        let bv_old: u16 = self.bits;
        let bv_new: u16 = set_bit16_macro!(bv_old, i, false);
        proof {
            set_bit_u16_preserves_others(bv_new, bv_old, i, false);
        }
        ;
        self.bits = bv_new;
        proof {
            assert_seqs_equal!(
                self.view(),
                old(self).view().update(i as int, false)
            );
        }
        Some(i as usize)
    }

    /// Allocates a contiguous block of `size` bits with specified `align_log2` alignment.
    /// Returns `Some(base_index)` if successful, `None` if no suitable block is found.
    fn alloc_contiguous(&mut self, size: usize, align_log2: usize) -> (res: Option<usize>)
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
                self.bits == 0 || self.spec_cap() < (1usize << align_log2) ||
                forall|i: int| (0 <= i <= (self.spec_cap() - size) as int) ==> has_obstruction(self@, i, size as int,(1usize << align_log2) as int)
                    // ==> exists |k: int| 0 <= k < size && #[trigger] self@[i+k] == false
                // true
            }
        },
    {
        assert(self.spec_cap() == 16);
        // let i = self.cap().trailing_zeros() as usize;
        assert(is_pow16(self.spec_cap())) by (compute);
        assert(self.spec_cap() % 16 == 0);
        if let Some(base) = find_contiguous(self, self.cap(), size, align_log2) {
            let start = base;
            let end = base + size;
            self.remove(start..end);
            Some(base)
        } else {
            None
        }
    }

    /// Deallocates a single bit at `index` by setting it to 1 (free).
    fn dealloc(&mut self, index: usize)
        ensures
            self@ == old(self)@.update(index as int, true),
    {
        self.set_bit(index as u16, true);
    }

    /// Marks a range of bits as free (sets them to 1).
    fn insert(&mut self, range: Range<usize>)
        ensures
            get_bits16!(self.bits, range.start as u16, range.end as u16) == (0xffffu16 >> (16 - (range.end as u16 - range.start as u16))),
            forall|loc2: int|
                (0 <= loc2 < range.start || range.end <= loc2  < 16) ==> self@[loc2] == old(self)@[loc2],
    {
        let width = (range.end - range.start) as u16;
        let insert_val = 0xffffu16 >> (16 - width);

        // Proof that insert_val's higher (16 - width) bits are zero.
        assert((0xffffu16 >> (16 - width) as u16) << ((u16::BITS) as u16 - width) as u16 >>
        ((u16::BITS) as u16 - width) as u16 == (0xffffu16 >> (16 - width) as u16)) by (bit_vector);
        let range_u16 = (range.start as u16)..(range.end as u16);
        self.set_bits(range_u16, insert_val);
    }

    /// Marks a range of bits as allocated (sets them to 0).
    fn remove(&mut self, range: Range<usize>)
        ensures
            forall|loc2: int|
                (0 <= loc2 < range.start || range.end <= loc2 < 16) ==> self@[loc2] == old(self)@[loc2],
            get_bits16!(self.bits, range.start as u16, range.end as u16) == 0,

    {
        let value:u16 = 0;
        let width:u16 = (range.end - range.start) as u16;
        assert(((u16::BITS) as u16 - width) >= 0);
        assert(0u16 << ((u16::BITS) as u16 - width) as usize >>
        ((u16::BITS) as u16 - width) as usize == 0u16) by (bit_vector);
        let range_u16 = (range.start as u16)..(range.end as u16);
        self.set_bits(range_u16, value);
    }


}

/// Specification function to check if a contiguous block starting at `i` of `size` contains any allocated bits (false).
/// or `i` is not a multiple of `align`
pub open spec fn has_obstruction(ba: Seq<bool>, i: int, size: int, align: int) -> bool {
    (i % align != 0) ||
    exists |k: int| i <= k < i + size && #[trigger] ba[k] == false
}

#[verifier::bit_vector]
proof fn safe_shr_lemma(x: usize, shift: usize)
    requires shift < 64
    ensures (x >> shift) <= x,
{
}

/// The capacity is an exponential multiple of 16.
/// and the current bitmap only supports the maximum allocatable page size of 1M.
spec fn is_pow16(cap: usize) -> bool {
    cap == 16 || cap == 256 || cap == 4096 || cap == 65536 || cap == 1048576
}

// /// The capacity is an exponential multiple of 16.
// /// cap == 16 || cap == 256 || cap == 4096 || cap == 65536 || cap == 1048576
// spec fn is_pow16(cap: usize) -> bool {
//     cap >= 16 &&
//     (cap & (cap-1usize) as usize) == 0 &&
//     (cap % 15usize == 1)
// }

/// Finds a contiguous block of `size` free bits within the bitmap, respecting `align_log2`.
/// Returns the base index of the found block, or `None` if no such block exists.
fn find_contiguous(ba: &impl BitAllocView, capacity: usize, size: usize, align_log2: usize) -> (res: Option<usize>)
    requires
        capacity == ba.spec_cap(),
        align_log2 < 64,
        0 < size <= capacity,
        capacity < 0x10000,
        is_pow16(capacity),
    ensures
        match res {
            Some(base) => {
                // If successful, a block of `size` free bits is found starting at `base`.
                // The block must be within capacity, aligned, and all bits within the block must be free (true).
                &&& base + size <= capacity
                &&& base % (1usize << align_log2) == 0
                &&& forall|i: int| base <= i < base + size ==> ba@[i] == true //ba.next(i) != None
            },
            None => {
                // If failed, no suitable block exists.
                // This implies either no free bits, or all potential blocks are obstructed or misaligned.
                capacity < (1usize << align_log2) || !ba.spec_any() ||
                forall|i: int| (0 <= i <= capacity - size) ==> has_obstruction(ba@, i, size as int,(1usize << align_log2) as int)
            }
        }
{
    // assert(capacity==16);
    assert(capacity == ba.spec_cap());
    if (capacity < (1usize << align_log2)) || !ba.any() {
        return None;
    }
    assert(capacity >= (1usize << align_log2));
    assert(ba.spec_any() == true);
    let mut base:usize = 0;
    // Proof that initial base (0) is aligned.
    assert(base % (1usize << align_log2) == 0) by (bit_vector)
        requires
            base == 0,
            align_log2 < 64,
    ;

    let mut offset:usize = base;
    let mut res:Option<usize> = None;
    while offset < capacity
        invariant
            capacity < 0x10000,
            is_pow16(capacity),
            capacity >= (1usize << align_log2),
            offset <= capacity,
            offset - base < size,
            forall|i: int| (0 <= i < base) ==> has_obstruction(ba@, i, size as int, (1usize << align_log2) as int),
            forall|i: int| (0 <= i < capacity) && (i % (1usize << align_log2) as int != 0) ==> has_obstruction(ba@, i, size as int, (1usize << align_log2) as int),
            capacity == ba.spec_cap(),
            align_log2 < 64,
            0 < size <= capacity,
            0 <= base <= offset,
            base % (1usize << align_log2) == 0,
            forall|i: int| base <= i < offset ==> ba@.index(i),
        decreases
            capacity - offset,
    {
        if let Some(next) = ba.next(offset) {
            assert(next < ba.spec_cap());
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
                assert(forall|i: usize| (offset - size < i <= offset) ==> has_obstruction(ba@, i as int, size as int, (1usize << align_log2) as int));

                assert(((next - 1) as usize) >= 0);
                proof{
                    safe_shr_lemma(((next - 1) as usize),align_log2);
                }
                base = (((((next - 1) as usize) >> align_log2) + 1) as usize) << align_log2;
                proof{
                    lemma_up_align_ge_original(next, capacity, align_log2);
                }
                assert(base >= next);

                assert(forall|i: int| (offset <= i < next) ==> (ba@[i] == false));
                // lemma_bit_false_implies_has_obstruction(ba@,);
                assert forall|i: usize| (offset <= i < next) implies has_obstruction(ba@, i as int, size as int, (1usize << align_log2) as int) by{
                    assert(ba@[i as int] == false);
                }

                offset = base;
                assert(offset >= next); // decreases
                assert(base % (1usize << align_log2) == 0) by (bit_vector)
                    requires
                        base == (((((next - 1) as usize) >> align_log2) + 1) as usize) << align_log2,
                        align_log2 < 64,
                        capacity < 0x10000,
                        0 < next < capacity,
                        (1usize << align_log2) <= capacity,
                ;
                proof{
                    lemma_up_align_le_capacity(next, capacity, align_log2);
                }
                assert(base <= capacity);
                assert(offset - base < size);
                assert forall|i: usize| (next <= i < base) implies has_obstruction(ba@, i as int, size as int, (1usize << align_log2) as int) by{
                    assert(i % (1usize << align_log2) != 0) by (bit_vector)
                        requires
                            next <= i < base,
                            0 < next <= base,
                            base == (((((next - 1) as usize) >> align_log2) + 1) as usize) << align_log2,
                            base <= capacity,
                            align_log2 < 64,
                            capacity < 0x10000,
                            (1usize << align_log2) <= capacity,
                    ;
                }
                continue;
            }
            assert(offset == next);

        } else {
            // No more free bits found from `offset` to `capacity`.
            assert(ba@[offset as int] == false);
            assert(forall|i: usize| (offset - size < i <= offset) ==> has_obstruction(ba@, i as int, size as int, (1usize << align_log2) as int));
            assert forall|i: usize| (offset <= i < capacity) implies has_obstruction(ba@, i as int, size as int, (1usize << align_log2) as int) by{
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
proof fn lemma_up_align_ge_original(next:usize, capacity:usize, align_log2:usize)
    requires
        capacity < 0x10000,
        0 < next < capacity,
        align_log2 < 64,
        (1usize << align_log2) <= capacity,
    ensures
        (((((next - 1) as usize) >> align_log2) + 1) as usize) << align_log2 >= next
{
    // assert(align_log2 <= 4);
}

// /// Lemma to prove that aligning `next` upwards results in a value less than or equal to the capacity (16).
#[verifier::bit_vector]
proof fn lemma_up_align_le_capacity(next:usize, capacity:usize, align_log2:usize)
    requires
        capacity <= 0x10000,
        0 < next < capacity,
        align_log2 < 64,
        (1usize << align_log2) <= capacity,
        capacity == 16 || capacity == 256 || capacity == 4096 || capacity == 65536 || capacity == 1048576,
        // is_pow16(capacity),
    ensures
        (((((next - 1usize) as usize) >> align_log2) + 1usize) as usize) << align_log2 <= capacity
{
}
*/
}
#[verifier::external]
fn main() {}
