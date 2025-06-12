#[allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
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
        if self.is_none() {
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

    fn is_none(&self) -> (res:bool)
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
            index < self@.len(),
        ensures match res {
            Some(i) => {
                // 如果成功，则返回第一个不小于key且没被占用的索引，key至res之间的索引位的值都为0，所有索引位的值保持不变；
            },
            None => {
                // 如果失败，表示key到结尾索引位的值都为0，所有索引位的值保持不变；
            }
        },
    {
        (key..16).find(|&i| self.get_bit(i))
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
