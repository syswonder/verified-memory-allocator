#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use core::ops::Range;
use vstd::{prelude::*, seq::*, seq_lib::*};

macro_rules! get_bit16_macro {
    ($a:expr, $b:expr) => {{ (0x1u16 & ($a >> $b)) == 1 }};
}

// since this wraps with `verus_proof_macro_exprs`, should use the above `get_bit16_macro` if it is going to be executable.
macro_rules! get_bit16 {
    ($($a:tt)*) => {
        verus_proof_macro_exprs!(get_bit16_macro!($($a)*))
    }
}

macro_rules! get_bits16_macro {
    ($a:expr, $st:expr, $ed:expr) => {{
        let bitlen = 16;
        let bits = ($a << (bitlen - $ed)) >> (bitlen - $ed);
        bits >> $st
    }};
}

macro_rules! get_bits16 {
    ($($a:tt)*) => {
        verus_proof_macro_exprs!(get_bits16_macro!($($a)*))
    }
}

macro_rules! set_bit16_macro {
    ($a:expr,$b:expr, $c:expr) => {{
        if $c {
            $a | 1u16 << $b
        } else {
            $a & (!(1u16 << $b))
        }
    }};
}

// since this wraps with `verus_proof_macro_exprs`, should use the above `set_bit16_macro` if it is going to be executable.
macro_rules! set_bit16 {
    ($($a:tt)*) => {
        verus_proof_macro_exprs!(set_bit16_macro!($($a)*))
    }
}

macro_rules! set_bits16_macro {
    ($a:expr, $st:expr, $ed:expr, $val:expr) => {{
        let bitlen = 16;

        let mask = !(!0u16 << (bitlen - $ed) >> (bitlen - $ed) >> $st << $st);

        ($a & mask) | ($val << $st)
    }};
}

macro_rules! set_bits16 {
    ($($a:tt)*) => {
        verus_proof_macro_exprs!(set_bits16_macro!($($a)*))
    }
}

verus! {

spec fn u16_view(u: u16) -> Seq<bool> {
    Seq::new(16, |i: int| get_bit16!(u, i as u16))
}

#[verifier::bit_vector]
proof fn set_bit16_proof(bv_new: u16, bv_old: u16, index: u16, bit: bool)
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
proof fn set_bits16_proof(bv_new: u16, bv_old: u16, st:u16, ed:u16, val: u16)
    requires
        st < 16,
        ed <= 16,
        st < ed,
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
proof fn get_bits16_proof(bv_gets: u16, bits: u16, st:u16, ed:u16)
    requires
        bv_gets == get_bits16!(bits, st, ed),
        st < 16,
        ed <= 16,
        st < ed,
    ensures
        forall|i: u16| 0 <= i < (ed - st) ==> ((get_bit16!(bv_gets, i)) == get_bit16!(bits, (st + i) as u16)),
{
}

pub proof fn ensure_val_nonzero(bits: u16)
    requires bits != 0,
    ensures bits.trailing_zeros() < 16,
{
    // 证明 trailing_zeros() < 16
}

// #[verifier::bit_vector]
// proof fn shift_is_reversible(val: u16, width: u16)
//     requires width <= 16,
//         val == val & ((1u16 << width) - 1) as u16,
//     ensures ((val << (16 - width)) >> (16 - width)) == val
// {

// }


pub struct BitAlloc16 {
    bits: u16,
}

impl BitAlloc16 {
    fn CAP() -> u16 {
        16
    }

    fn default() -> Self {
        BitAlloc16 { bits: 0 }
    }

    spec fn view(&self) -> Seq<bool> {
        let width = 16;
        Seq::new(width, |i: int| u16_view(self.bits@)[i])
    }

    fn get_bit(&self, index: u16) -> (bit: bool)
        requires
            index < self@.len(),
        ensures
            bit == self@[index as int],
    {
        let bit_index: u16 = index % 16;
        get_bit16_macro!(self.bits, bit_index as u16)
    }

    fn get_bits(&self, range:Range<u16>) -> (bits:u16)
        requires
            range.start < self@.len(),
            range.end <= self@.len(),
            range.start < range.end,
        ensures
            forall|i: int| 0 <= i < (range.end - range.start) ==> (u16_view(bits)[i]) == self@[range.start + i],
            // forall|i: u16| 0 <= i < (range.end - range.start) ==> ((get_bit16!(bits, i)) == get_bit16!(self.bits, (range.start as u16 + i) as u16)),
    {
        let bv_gets = get_bits16_macro!(self.bits, range.start, range.end);
        // assert((bv_gets & (1u16)) == 0 || (bv_gets & (1u16)) == 1) by (bit_vector);
        proof {
            get_bits16_proof(bv_gets, self.bits, range.start, range.end);
        };
        bv_gets
    }

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
            set_bit16_proof(bv_new, bv_old, bit_index as u16, bit);
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

    fn set_bits(&mut self, range: Range<u16>, value: u16)
        requires
            range.start < old(self)@.len(),
            range.end <= old(self)@.len(),
            range.start < range.end,
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
            set_bits16_proof(bv_new, bv_old, range.start, range.end, value);
        }
        ;
        self.bits = bv_new;
        assert(get_bits16!(bv_new, range.start, range.end) == value);
    }

    fn alloc(&mut self) -> (res: Option<u16>)
    //如果成功，则分配了一个没被占用的索引，其它索引位的值保持不变；
    //新分配的索引要小于16，并且get_bit(i)获取的值最初为1，alloc之后为0，表示当前位已分配;

    //如果失败，则说明全部满了，状态不变，self.val的值应为0
        ensures match res {
            Some(i) => {
                self@ == old(self)@.update(i as int, false)
            },
            None => self.bits == 0,
        },
    {
        if !self.any() {
            return None;
        }
        proof {
            ensure_val_nonzero(self.bits);  // 验证 self.bits != 0 时 trailing_zeros() < 16
        }
        let i = self.bits.trailing_zeros() as u16; // 保证了i为低位起的第一个1
        assert(i>=0);
        assert(i<16);
        let bv_old: u16 = self.bits;
        let bv_new: u16 = set_bit16_macro!(bv_old, i as u16, false);
        proof {
            set_bit16_proof(bv_new, bv_old, i as u16, false);
        }
        ;
        self.bits = bv_new;
        proof {
            assert_seqs_equal!(
                self.view(),
                old(self).view().update(i as int, false)
            );
        }
        ;
        Some(i)
    }

    // fn alloc_contiguous(&mut self, size: u16, align_log2: u16) -> (res: Option<u32>)
    // //如果成功，则分配了一段大小为size的空间，其它索引位的值保持不变；
    // //新分配的索引base+size要小于16，并且get_bits(range)获取的值在该范围内的bit位都为1，alloc_contiguous之后都为0；

    // //如果失败，则说明没有符合要求的空间，状态不变
    // {
    //     if let Some(base) = find_contiguous(self, Self::CAP, size, align_log2) {
    //         self.remove(base..base + size);
    //         Some(base)
    //     } else {
    //         None
    //     }
    // }

    fn dealloc(&mut self, key: u16)
    //释放前该索引位置得是0，释放后是1，其它索引位的值保持不变；
    //key得小于16
        requires
            key < old(self)@.len(),
        ensures
            self@ == old(self)@.update(key as int, true),
    {
        self.set_bit(key, true);
    }

    fn insert(&mut self, range: Range<u16>)
    //执行后的指定范围内bit位的值全为1；
        requires
            range.start < old(self)@.len(),
            range.end <= old(self)@.len(),
            range.start < range.end,
        ensures
            // forall|loc1: int|
            //     (range.start <= loc1 < range.end) ==> self@[loc1] == true,
            // get_bits16!(self.bits, range.start, range.end) == get_bits16!(0xffffu16, range.start, range.end),
            get_bits16!(self.bits, range.start, range.end) == (0xffffu16 >> (16 - (range.end - range.start))),
            forall|loc2: int|
                (0 <= loc2 < range.start || range.end <= loc2  < 16) ==> self@[loc2] == old(self)@[loc2],
    {
        let width = range.end - range.start;
        let insert_val = 0xffffu16 >> (16 - width);

        // shift_is_reversible(insert_val, width); 等价于下面的assert

        // assert(width<=16);
        // assert(((u16::BITS) as u16 - width) == (16 - width));
        // assert(insert_val == 0xffffu16 >> (16 - width) as u16);

        //确保insert_val的高（16 - width）位为0
        // assert(0xffffu16 >> (16 - width) as u16 == 0xffffu16 >> (16 - width) as u16 & ((1u16 << width) - 1) as u16) by (bit_vector);

        // 确保insert_val的高（16 - width）位为0
        assert((0xffffu16 >> (16 - width) as u16) << ((u16::BITS) as u16 - width) as u16 >>
        ((u16::BITS) as u16 - width) as u16 == (0xffffu16 >> (16 - width) as u16)) by (bit_vector);

        self.set_bits(range, insert_val);
        // assert(get_bits16!(self.bits, range.start, range.end) == insert_val);

        // self.val.set_bits(range.clone(), 0xffff.get_bits(range));
    }

    fn remove(&mut self, range: Range<u16>)
    //执行后的指定范围内bit位的值全为0；
        requires
            range.start < old(self)@.len(),
            range.end <= old(self)@.len(),
            range.start < range.end,
        ensures
            get_bits16!(self.bits, range.start, range.end) == 0,
            forall|loc2: int|
                (0 <= loc2 < range.start || range.end <= loc2  < 16) ==> self@[loc2] == old(self)@[loc2],
    {
        let value:u16 = 0;
        let width = range.end - range.start;
        assert(((u16::BITS) as u16 - width) >= 0);
        assert(0u16 << ((u16::BITS) as u16 - width) as usize >>
        ((u16::BITS) as u16 - width) as usize == 0u16) by (bit_vector);
        self.set_bits(range, value);
    }

    fn any(&self) -> (res:bool)
        ensures
            res == (self.bits != 0),
    {
        self.bits != 0
    }


    fn test(&self, key: u16) -> (res:bool)
        requires
            key < self@.len(),
        ensures
            res == (get_bit16_macro!(self.bits, key as u16)),
    {
        self.get_bit(key)
    }

    fn next(&self, key: u16) -> (res: Option<u16>)
        requires
            key < self@.len(),
        ensures match res {
            Some(re) => {
                // 如果成功，则返回第一个不小于key且没被占用的索引，key至res之间的索引位的值都为0，所有索引位的值保持不变；
                re < self@.len() &&
                re >= key &&
                forall|i: int| key <= i < re ==> self@[i] == false
            },
            None => {
                // 如果失败，表示key到结尾索引位的值都为0，所有索引位的值保持不变；
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
                (i == n && result.is_none()) ||  (i < n && result.is_some() && (result.unwrap() == i)),
        {
            if self.get_bit(i) {
                result = Some(i);
                assert(i<n);
                assert(i < n &&
                i >= key &&
                forall|k: int| key <= k < i ==> self@[k] == false);
                break;
            }
            i += 1;
        }
        result

        // (key..16).find(|i| self.get_bit(*i))
    }
}

fn find_contiguous(ba: &mut BitAlloc16, capacity: u16, size: u16, align_log2: u16,) -> (res: Option<u16>)
    requires
        capacity <=16,
        0 < size,
    ensures match res {
        Some(i) => {
            //如果成功，则分配了一段大小为size的空间，其它索引位的值保持不变；
            //新分配的索引base+size要小于16，并且get_bits(range)获取的值在该范围内的bit位都为1，alloc_contiguous之后都为0；
            i + size <= capacity &&
            i % (1 << align_log2) == 0 &&
            

        },
        None => {
            //如果失败，则说明没有符合要求的空间，状态不变
            //所有连续空间的内存小于要求分配的空间 || 连续空间的内存大于要求分配的空间但是不满足对齐
            //满足对齐时 连续空间的内存小于要求分配内存的空间
            ba == 0 ||
            forall|i: int| 0 <= i < 16
        }
    },
{

    if capacity < (1 << align_log2) || !ba.any() {
        return None;
    }
    let mut base = 0;
    let mut offset = base;
    while offset < capacity {
        if let Some(next) = ba.next(offset) {
            if next != offset {
                // it can be guarenteed that no bit in (offset..next) is free
                // move to next aligned position after next-1
                assert!(next > offset);
                base = (((next - 1) >> align_log2) + 1) << align_log2;
                assert_ne!(offset, next);
                offset = base;
                continue;
            }
        } else {
            return None;
        }
        offset += 1;
        if offset - base == size {
            return Some(base);
        }
    }
    None
}


}
#[verifier::external]
fn main() {}
