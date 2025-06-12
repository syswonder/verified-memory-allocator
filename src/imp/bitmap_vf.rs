#[allow(unused_imports)]
// use builtin::*;
// use builtin_macros::*;
use core::ops::Range;

// use crate::imp::bitfield::*;

// use super::bitfield::*;
use vstd::{prelude::*, seq::*, seq_lib::*};

verus! {
    // spec const CAP:usize;
    // pub open spec const PAGE_SIZE: nat = 4096;
    // pub open spec const MAX_FRAMES: nat = 1024 * 1024; // 支持最多 1M 个页

    // /// 物理帧编号
    // type FrameIdx = nat;

    // struct FrameAllocator {
    //     pub base: nat,
    //     pub used: Set<FrameIdx>, // 表示已分配帧编号 idx ∈ [0, MAX_FRAMES)
    // }


    /// Allocator of a bitmap, able to allocate / free bits.
    pub trait BitAlloc{
        // spec fn view(&self) -> Seq<bool>;

        /// The bitmap has a total of CAP bits, numbered from 0 to CAP-1 inclusively.
        // fn cap(&self) -> (res: usize)
        //     ensures
        //         self.spec_cap() == res,
        // ;

        // /// The bitmap has a total of CAP bits, numbered from 0 to CAP-1 inclusively.(spec mode)
        // spec fn spec_cap(self) -> usize;
        // fn cap(&self) -> (res:usize)
        //     ensures
        //         res < 65536,
        // {
        //     self.cap()*16
        // }
        fn CAP() -> usize;

        // fn cap(&self) -> (res: usize);

        /// The default value. Workaround for `const fn new() -> Self`.

        fn default() -> Self where Self: Sized;

        /// Allocate a free bit.
        fn alloc(&mut self) -> Option<usize>;

        /// Allocate a free block with a given size, and return the first bit position.
        //fn alloc_contiguous(&mut self, size: usize, align_log2: usize) -> Option<usize>;

        /// Find a index not less than a given key, where the bit is free.
        // fn next(&self, key: usize) -> Option<usize>;

        /// Free an allocated bit.
        //fn dealloc(&mut self, key: usize);

        /// Mark bits in the range as unallocated (available)
        // fn insert(&mut self, range: Range<usize>) -> (res: usize);

        /// Reverse of insert
        fn remove(&mut self, range: Range<usize>) -> (res: usize)
            requires
                range.start < usize::BITS as usize,
                range.end <= usize::BITS as usize,
                range.start < range.end,
        ;

        /// Whether there are free bits remaining
        fn any(&self) -> bool;

        // /// Whether a specific bit is free
        // fn test(&self, key: usize) -> bool;

        // fn from(&self) -> BitAllocCascade16;
    }

    // spec fn u64_view(u: u64) -> Seq<bool> {
    //     Seq::new(64, |i: int| get_bit64!(u, i as u64))
    // }
    // struct BitAlloc {

    // }

    pub struct BitMap {
        bits: Vec<u64>,
    }

    // impl BitMap {
    //     // spec fn view(&self) -> Seq<bool> {
    //     //     let width = self.bits@.len() * 64;
    //     //     Seq::new(width, |i: int| u64_view(self.bits@[i / 64])[i % 64])
    //     // }

    //     fn from(v: Vec<u64>) -> BitMap {
    //         BitMap { bits: v }
    //     }

    //     fn alloc(&mut self)
    // }

    pub struct BitAllocCascade16<T: BitAlloc> {
        bitset: u16, // for each bit, 1 indicates available, 0 indicates inavailable
        sub: [T; 16],
    }

    // impl<T: BitAlloc> BitAlloc for BitAllocCascade16<T> {
    //     // const CAP: usize = T::CAP * 16;
    //     // fn cap(&self) -> usize

    //     // {
    //     //     self.cap()*16
    //     // }


    //     fn CAP() -> usize
    //         requires (T::CAP() * 16 < usize::MAX)
    //     {
    //         T::CAP() * 16
    //     }

    //     // fn cap(&self) -> (res: usize)
    //     // {
    //     //     Self::CAP() * 16
    //     // }

    //     fn default() -> Self {
    //         BitAllocCascade16{
    //             bitset: 0,
    //             sub: [T::default(); 16],
    //         }
    //     }

    //     // const DEFAULT: Self = BitAllocCascade16 {
    //     //     bitset: 0,
    //     //     sub: [T::DEFAULT; 16],
    //     // };

    //     // fn from(T: BitAlloc) -> BitAllocCascade16 {
    //     //     BitAllocCascade16 {
    //     //         bitset:0,
    //     //         sub: [T; 16],
    //     //     }
    //     // }

    //     // fn alloc(&mut self) -> Option<usize>

    //     // {
    //     //     if self.any() {

    //     //         let i = self.bitset.trailing_zeros() as usize; //找到 bitset 中第一个为 1 的 bit 的索引 i
    //     //         // let res = self.sub[i].alloc().unwrap() + i * T::CAP;
    //     //         // self.bitset.set_bit(i, self.sub[i].any());
    //     //         Some(i)
    //     //     } else {
    //     //         None
    //     //     }
    //     // }

    //     fn any(&self) -> bool {
    //         self.bitset != 0
    //     }
    //     // spec fn view(&self) -> Seq<bool> {
    //     //     Seq::flatten(Seq::map_range(0..16, |i: int| self.sub[i as usize].view()))
    //     // }

    //     // spec fn inv(&self) -> bool {
    //     //     &&& forall|i: int| 0 <= i < 16 ==> self.sub[i as usize].inv()
    //     //     &&& forall|i: int| 0 <= i < 16 ==> (
    //     //         self.sub[i as usize].view().any(|b| !b)
    //     //         <==> bitvector::get(self.bitset, i as nat)
    //     //     )
    //     // }
    // }

    // #[derive(Default)]
    pub struct BitAlloc16{
        pub val: u16,
    }

    impl BitAlloc16 {
        fn CAP() -> usize {
            16
        }

        fn default() -> Self {
            BitAlloc16 { val: 0 }
        }

        fn alloc(&mut self) -> (res: Option<u32>)
        //如果成功，则分配了一个没被占用的索引，其它索引位的值保持不变；
        //新分配的索引要小于16，并且get_bit(i)获取的值最初为1，alloc之后为0，表示当前位已分配;

        //如果失败，则说明全部满了，状态不变，self.val的值应为0

        ensures match res {
            Some(i) => {
                old(self).val != 0
                && i<16
                // && get_bit_spec(old(self).val, i) == true
                // && get_bit_spec(self.val, i) == false
                // && get_bit_spec(old(self).val, i) == !get_bit_spec(self.val, i)


                && old(self).val & self.val == self.val
            },
            None => self.val == 0,
        },

        {
            if self.any() {
                return None;
            }
            proof {
                ensure_val_nonzero(self.val);  // 验证 self.val != 0 时 trailing_zeros() 有效
            }
            // let i = self.val.trailing_zeros();
            // assert(i>=0);
            // assert(i<16);
            // let val = self.val;

            // let a = get_bit_exec(val, i);
            // let new_val = set_bit_exec(self.val, i, false);
            // self.val = new_val;
            // let b = get_bit_exec(new_val, i);
            // assert(a != b);
            let test_num:u16 = 0b1111111111111111;
            let i = test_num.trailing_zeros();
            // proof {
            //     assert(trailing_zeros_spec(test_num) == test_num.trailing_zeros());
            // }

            assert(i>=0);
            assert(i<16);
            // assert(i<1);
            // assert(i==0);
            // assert((val & self.val) == self.val);
            Some(i)

            // if ba.any() {
            //     let i = ba.val.trailing_zeros() as usize;
            //     ba.val = set_bit_exec(ba.val.into(), i, false) as u16;
            //     Some(i)
            // } else {
            //     None
            // }
        }


        fn alloc_contiguous(&mut self, size: usize, align_log2: usize) -> (res: Option<usize>)
        //如果成功，则分配了一段大小为size的空间，其它索引位的值保持不变；
        //新分配的索引base+size要小于16，并且get_bits(range)获取的值在该范围内的bit位都为1，alloc_contiguous之后都为0；

        //如果失败，则说明没有符合要求的空间，状态不变
        {
            if let Some(base) = find_contiguous(self, Self::CAP, size, align_log2) {
                self.remove(base..base + size);
                Some(base)
            } else {
                None
            }
        }
        fn dealloc(&mut self, key: usize)
        //释放前该索引位置得是0，释放后是1，其它索引位的值保持不变；
        //key得小于16
        {
            assert!(!self.test(key));
            self.0.set_bit(key, true);
        }

        fn insert(&mut self, range: Range<usize>) -> (res: usize)
        //执行后的结果16位全为1；
        {
            self.val.set_bits(range.clone(), 0xffff.get_bits(range))
        }
        fn remove(&mut self, range: Range<usize>) -> (res: usize)
        //执行后的结果16位全为0；
        {
            set_bits_exec(self.val.into(), range, 0)
        }
        fn any(&self) -> (res:bool)
            ensures
                res == (self.val == 0),
        {
            self.val == 0
        }
        fn test(&self, key: usize) -> bool {
            self.0.get_bit(key)
        }
        fn next(&self, key: usize) -> (res:Option<usize>)
        // 如果成功，则返回第一个不小于key且没被占用的索引，key至res之间的索引位的值都为0，所有索引位的值保持不变；
        // 如果失败，表示key到结尾索引位的值都为0，所有索引位的值保持不变；
        {
            (key..16).find(|&i| self.0.get_bit(i))
        }
    }

    pub proof fn ensure_val_nonzero(val: u16)
        requires val != 0,
        ensures val.trailing_zeros() < 16,
    {
        // 证明 trailing_zeros() < 16
    }

    // proof fn lemma_and_not_mask_zero(val: u16, index: u32)
    //     requires
    //         index < 16,
    //     ensures
    //         ((val & !(1u16 << index)) & (1u16 << index)) == 0,
    // {
    //     // 显式构造 mask
    //     let mask = 1u16 << index;

    //     // 对布尔恒等式进行逐步引导
    //     let not_mask = !mask;
    //     let a = val & not_mask;
    //     let result = a & mask;

    //     // 你可以在这里一步步写明计算
    //     // SMT 会接受这样的辅助信息作为提示

    //     assert(result == 0);
    // }


    // proof fn lemma_bit_clear(val: u16, index: u32)
    //     requires
    //         index < 16,
    //     ensures
    //         get_bit_spec(val & !(1u16 << index), index) == false,
    // {
    //     let mask = 1u16 << index;
    //     assert(((val & !mask) & mask) == 0);
    //     assert(get_bit_spec(val & !mask, index) == false);
    // }


    pub proof fn ensure_setbit(val: u16, index: u32)
        requires
            index < 16,
            get_bit_spec(val, index) == true,
        ensures
            get_bit_spec(set_bit_spec(val,index,false),index) == false,
    {
        let mask: u16 = 1u16 << index;
        let cleared: u16 = val & !mask;
        assert(set_bit_spec(val, index, false) == cleared);
        assert(get_bit_spec(cleared, index) == false);
    }

// // 显式展开表达式
// assert forall |x: u16, m: u16| m & !m == 0 by {
//     assert((x & !m) & m == 0);
// };
// assert(get_bit_spec(cleared, index) == ((cleared & mask) != 0));
// assert((cleared & mask) == 0); // 引导 Verus 推理为 0

// // 证明 (val & !mask) & mask == 0
// assert((val & !mask) & mask == 0);

// // 最后推出目标结论
// assert(get_bit_spec(cleared, index) == false);

    // spec fn trailing_zeros_spec(x: u16) -> u32 {
    //     decreases(x);
    //     if x & 1 == 1 {
    //         0
    //     } else {
    //         (1u32 + trailing_zeros_spec(x >> 1u32)) as u32
    //     }
    // }

    // fn find_contiguous(
    //     ba: &impl BitAlloc,
    //     capacity: usize,
    //     size: usize,
    //     align_log2: usize,
    // ) -> Option<usize> {
    //     if capacity < (1 << align_log2) || !ba.any() {
    //         return None;
    //     }
    //     let mut base = 0;
    //     let mut offset = base;
    //     while offset < capacity {
    //         if let Some(next) = ba.next(offset) {
    //             if next != offset {
    //                 // it can be guarenteed that no bit in (offset..next) is free
    //                 // move to next aligned position after next-1
    //                 assert!(next > offset);
    //                 base = (((next - 1) >> align_log2) + 1) << align_log2;
    //                 assert_ne!(offset, next);
    //                 offset = base;
    //                 continue;
    //             }
    //         } else {
    //             return None;
    //         }
    //         offset += 1;
    //         if offset - base == size {
    //             return Some(base);
    //         }
    //     }
    //     None
    // }

    // impl<T: BitAlloc> View for BitAllocCascade16<T> {
    //     type V = Seq<bool>;

    //     open spec fn view(&self) -> Seq<bool> {
    //         // 每个子分配器 view 拼接成整体 view
    //         Seq::flatten(self.sub.map(|s: &T| s@))
    //     }
    // }

    pub open spec fn get_bit_spec(bit: u16, index:u32) -> bool {
        (bit & (1u16 << index)) != 0
    }

    pub fn get_bit_exec(bit: u16, index:u32) -> (value: bool)
        requires
            index < 16,
        ensures
            value == get_bit_spec(bit, index)
    {
        (bit & (1u16 << index)) != 0
    }

    spec fn get_bits_spec(bit: usize, range: Range<usize>) -> (res: usize) {
        let bit_length = (usize::BITS) as usize;
        // shift away high bits
        let bits = bit << (bit_length - range.end) >> (bit_length - range.end);

        // shift away low bits
        bits >> range.start
    }

    fn get_bits_exec(bit: usize, range: Range<usize>) -> (res: usize)
        requires
            range.start < (usize::BITS) as usize,
            range.end <= (usize::BITS) as usize,
            range.start < range.end,
        ensures
            res == get_bits_spec(bit, range)
    {
        let bit_length = (usize::BITS) as usize;
        // shift away high bits
        let bits = bit << (bit_length - range.end) >> (bit_length - range.end);

        // shift away low bits
        bits >> range.start
    }

    pub open spec fn set_bit_spec(bit: u16, index: u32, value: bool) -> u16 {
        if value {
            bit | (1u16 << index)
        } else {
            bit & !(1u16 << index)
        }
    }

    pub fn set_bit_exec(bit: u16, index: u32, value: bool) -> (res: u16)
        requires
            index < 16,
        ensures
            res == set_bit_spec(bit, index, value)
    {
        if value {
            bit | (1u16 << index)
        } else {
            bit & !(1u16 << index)
        }
    }

    spec fn set_bits_spec(bit: usize, range: Range<usize>, value: usize) -> usize
    {
        let bit_width = (usize::BITS) as usize;

        let bitmask:usize = !(!0usize << (bit_width - range.end) >>
                            (bit_width - range.end) >>
                            range.start << range.start);

        // set bits
        (bit & bitmask) | (value << range.start)
    }

    fn set_bits_exec(bit: usize, range: Range<usize>, value: usize) -> (res: usize)
        requires
            range.start < (usize::BITS) as usize,
            range.end <= (usize::BITS) as usize,
            range.start < range.end,
            // value << ((usize::BITS) as usize - (range.end - range.start)) >>
            //     ((usize::BITS) as usize - (range.end - range.start)) == value,
        ensures
            res == set_bits_spec(bit, range, value)
    {

        let bit_width = (usize::BITS) as usize;

        let bitmask:usize = !(!0usize << (bit_width - range.end) >>
                            (bit_width - range.end) >>
                            range.start << range.start);

        // set bits
        (bit & bitmask) | (value << range.start)
    }

    fn main() {
        // assert(set_bit_spec(0b11, 2, true) == 0b111) by (compute);
    }


}
