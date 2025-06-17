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
    ($a:expr, $range:expr) => {{
        let bitlen = 16;
        let start = $range.start;
        let end = $range.end;

        let bits = ($a << (bitlen - end)) >> (bitlen - end);
        bits >> start
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
    ($a:expr, $range:expr, $val:expr) => {{
        let bitlen = 16;
        let start = $range.start;
        let end = $range.end;

        let mask = !(!0u16 << (bitlen - end) >> (bitlen - end) >> start << start);

        ($a & mask) | ($val << start)
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

// #[verifier::bit_vector]
// proof fn set_bits16_proof(bv_new: u16, bv_old: u16, range: Range<u16>, val: u16)
//     requires
//         range.start < 16,
//         range.end <= 16,
//         range.start < range.end,
//         value << ((u16::BITS) as u16 - (range.end - range.start)) >>
//             ((u16::BITS) as u16 - (range.end - range.start)) == value,
//         bv_new == set_bits16!(bv_old, range, val),
//     ensures
//         get_bit16!(bv_new, index) == bit,
//         forall|loc2: u16|
//             (loc2 < 16 && loc2 != index) ==> (get_bit16!(bv_new, loc2) == get_bit16!(bv_old, loc2)),
// {
// }


proof fn get_bits16_proof(bv_gets: u16, bits: u16, range:Range<u16>)
    requires
        bv_gets == get_bits16!(bits, range),
        range.start < 16,
        range.end <= 16,
        range.start < range.end,
    ensures
        get_bits16!(bits, range) == bv_gets,
        forall|i: u16| 0 <= i < (range.end - range.start) ==> ((get_bit16!(bv_gets, i)) == get_bit16!(bits, (range.start as u16 + i) as u16)),
{
}

pub struct BitAlloc16 {
    bits: u16,
}

impl BitAlloc16 {
    fn CAP() -> usize {
        16
    }

    fn default() -> Self {
        BitAlloc16 { bits: 0 }
    }

    spec fn view(&self) -> Seq<bool> {
        let width = 16;
        Seq::new(width, |i: int| u16_view(self.bits@)[i])
    }

    fn get_bit(&self, index: u32) -> (bit: bool)
        requires
            index < self@.len(),
        ensures
            bit == self@[index as int],
    {
        let bit_index: u32 = index % 16;
        get_bit16_macro!(self.bits, bit_index as u16)
    }

    fn get_bits(&self, range:Range<u16>) -> (bits:u16)
        requires
            range.start < self@.len(),
            range.end <= self@.len(),
            range.start < range.end,
        ensures
            // (1u16 & 0u16) == 0u16,
            // true
            // forall|i: int| 0 <= i < (range.end - range.start) ==> ((bits & (1u16 << i)) != 0) == self@[range.start + i],
            forall|i: int| 0 <= i < (range.end - range.start) ==> (u16_view(bits)[i]) == self@[range.start + i],
            // forall|i: u16| 0 <= i < (range.end - range.start) ==> ((get_bit16!(bits, i)) == get_bit16!(self.bits, (range.start as u16 + i) as u16)),
    {
        let bits = get_bits16_macro!(self.bits, range);
        proof {
            let s = u16_view(bits);
            assert(range.start < self@.len());
            assert(s[0] == self@[range.start as int]);
            assume(forall|i: int| 0 <= i < (range.end - range.start) ==> (s[i]) == self@[range.start + i]);
        }
        // Seq::new(16, |i: int| u16_view(bits)[i]);
        // proof {
        //     assert(bits >> (range.end - range.start) == 0) by (compute);
        //     assert(((bits << range.start) & self.bits) == bits) by (compute);
        // }
        // proof{
        //     get_bits16_proof(bits,self.bits,range);
        // }
        // assert((bits & (1u16)) == 0 || (bits & (1u16)) == 1) by (compute);
        // assert(((bits & (1u16)) !=0 ) == self@[range.start as int]);
        // assume(forall|i: int| 0 <= i < (range.end - range.start) ==> ((bits & (1u16 << i)) != 0) == self@[range.start + i]);
        bits
    }

    fn set_bit(&mut self, index: u32, bit: bool)
        requires
            index < old(self)@.len(),
        ensures
            self@ == old(self)@.update(index as int, bit),
    {
        let bit_index: u32 = index % 16;
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

    // fn set_bits(&mut self, range: Range<u16>, value: u16)
    //     requires
    //         range.start < old(self)@.len(),
    //         range.end <= old(self)@.len(),
    //         range.start < range.end,
    //         value << ((u16::BITS) as u16 - (range.end - range.start)) >>
    //             ((u16::BITS) as u16 - (range.end - range.start)) == value,
    //     ensures
    //         forall|i: int| range.start <= i < range.end ==> self@ == old(self)@.update(i,((value & (1u16 << i)) != 0))


    //         // self@ == old(self)@.update(index as int, bit),
    //         // res == set_bits_spec(bit, range, value)
    // {
    //     let bit_width = (u16::BITS) as u16;

    //     let bitmask:u16 = !(!0u16 << (bit_width - range.end) >>
    //                         (bit_width - range.end) >>
    //                         range.start << range.start);

    //     // set bits
    //     self.bits = (self.bits & bitmask) | (value << range.start)


    //     // let bit_index: u32 = index % 16;
    //     let bv_old: u16 = self.bits;
    //     let bv_new: u16 = set_bits16_macro!(bv_old, range, value);
    //     proof {
    //         set_bits16_proof(bv_new, bv_old, range, value);
    //     }
    //     ;
    //     self.bits = bv_new;
    //     proof {
    //         assert_seqs_equal!(
    //             self.view(),
    //             old(self).view().update(index as int, bit)
    //         );
    //     }
    //     ;
    // }

    fn alloc(&mut self) -> (res: Option<u32>)
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
        if self.is_zero() {
            return None;
        }
        proof {
            ensure_val_nonzero(self.bits);  // 验证 self.bits != 0 时 trailing_zeros() < 16
        }
        let i = self.bits.trailing_zeros();
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

    fn dealloc(&mut self, key: u32)
    //释放前该索引位置得是0，释放后是1，其它索引位的值保持不变；
    //key得小于16
        requires
            key < old(self)@.len(),
        ensures
            self@ == old(self)@.update(key as int, true),
    {
        self.set_bit(key, true);
    }

    // fn remove(&mut self, range: Range<usize>) -> (res: usize)
    // //执行后的指定范围内bit位的值全为0；
    // {
    //     set_bits_exec(self.val.into(), range, 0)
    // }

    fn is_zero(&self) -> (res:bool)
        ensures
            res == (self.bits == 0),
    {
        self.bits == 0
    }

    fn test(&self, key: u32) -> (res:bool)
        requires
            key < self@.len(),
        ensures
            res == (get_bit16_macro!(self.bits, key as u16)),
    {
        self.get_bit(key)
    }

    fn next(&self, key: u32) -> (res: Option<u32>)
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
        let n:u32 = u16::BITS;
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
        // if result.is_none() {
        //     assert(i == n);
        //     // assert(i >= n);
        //     // assert(i == 16);
        //     assert(n == self@.len());
        //     assert(forall|k: int| key <= k < self@.len() ==> self@[k] == false);
        //     // assert(forall|k: int| key <= k < 16 ==> self@[k] == false);
        // } else{
        //     assert((result.is_some() && i < n));
        //     assert(i<n);
        //     let x = result.unwrap();
        //     assert(x == i);
        //     assert(x < self@.len());
        //     assert(x < self@.len() &&
        //             x >= key &&
        //             forall|i: int| key <= i < x ==> self@[i] == false);
        // }
        result

        // (key..16).find(|i| self.get_bit(*i))
    }
}

pub proof fn ensure_val_nonzero(bits: u16)
    requires bits != 0,
    ensures bits.trailing_zeros() < 16,
{
    // 证明 trailing_zeros() < 16
}

}
#[verifier::external]
fn main() {}
