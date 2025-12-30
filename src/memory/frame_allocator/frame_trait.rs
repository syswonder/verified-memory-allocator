use vstd::prelude::*;
use crate::addr::{PAddr, PAddrExec};

verus! {

/// 2^k（数学意义），用于对齐约束（按“页下标”对齐）。
pub open spec fn pow2(k: nat) -> nat
    decreases k
{
    if k == 0 { 1 } else { 2 * pow2(k - 1) }
}

/// 将“页下标 idx”映射到物理地址：base + idx * page_size
pub open spec fn idx_to_paddr(base: PAddr, idx: nat, page_size: nat) -> PAddr {
    PAddr(base.0 + idx * page_size)
}

/// 将物理地址映射回“页下标”（需要对齐且在范围内）
pub open spec fn paddr_to_idx(base: PAddr, addr: PAddr, page_size: nat) -> nat
    recommends
        addr.0 >= base.0,
        page_size > 0,
        (addr.0 - base.0) % page_size == 0,
{
    (addr.0 - base.0) / page_size
}

/// Frame Allocator 的“观察接口”（view + 不变量）
pub trait FrameAllocView {
    /// 基地址（spec）
    spec fn base(&self) -> PAddr;

    /// 当前管理的页数（动态，<= cap_pages）
    spec fn region_pages(&self) -> nat;

    /// bits[i] == true 表示第 i 页空闲；false 表示不可用/已分配
    /// bits 的长度固定为 cap_pages（实现可大于 region_pages）
    spec fn bits(&self) -> Seq<bool>;

    /// 页大小（架构相关但对组件是参数）：比如 4096
    spec fn page_size() -> nat;

    /// 分配器“总容量”（比如 BitAlloc1M 的 cap）
    spec fn cap_pages() -> nat;

    /// 健全性不变量：对齐/长度/边界/region 外永远 false
    spec fn wf(&self) -> bool {
        &&& self.base().aligned(Self::page_size())
        &&& self.bits().len() == Self::cap_pages()
        &&& self.region_pages() <= Self::cap_pages()
        &&& forall|i: int|
                self.region_pages() <= i < Self::cap_pages()
                ==> self.bits()[i] == false
    }
}

/// Frame Allocator 的“执行接口”（init/alloc/dealloc...）
pub trait FrameAllocator: FrameAllocView {

    /// 初始化为管理 [base, base+size) 这一段连续物理内存（按页管理）
    fn init(&mut self, base: PAddrExec, size: usize)
        requires
            base.view().aligned(Self::page_size()),
            size as nat % Self::page_size() == 0,
            (size as nat / Self::page_size()) <= Self::cap_pages(),
        ensures
            self.wf(),
            self.base() == base.view(),
            self.region_pages() == size as nat / Self::page_size(),
            // init 后：region 内全部 free
            forall|i: int| 0 <= i < self.region_pages() ==> self.bits()[i] == true,
    ;

    /// 分配 1 页（unsafe：需要调用者负责回收）
    unsafe fn alloc(&mut self) -> (res: Option<PAddrExec>)
        requires
            old(self).wf(),
        ensures
            self.wf(),
            match res {
                Some(p) => {
                    let addr = p.view();
                    let ps = Self::page_size();
                    let idx = paddr_to_idx(old(self).base(), addr, ps);

                    &&& addr.aligned(ps)
                    &&& addr.within(old(self).base(), old(self).region_pages() * ps)
                    &&& idx < old(self).region_pages()
                    &&& old(self).bits()[idx as int] == true
                    &&& self.bits() == old(self).bits().update(idx as int, false)
                }
                None => {
                    // 没空闲页：region 内全是 false，状态不变
                    &&& self.bits() == old(self).bits()
                    &&& forall|i: int| 0 <= i < old(self).region_pages() ==> old(self).bits()[i] == false
                }
            }
    ;

    /// 分配连续 count 页（unsafe：需要调用者负责回收）
    unsafe fn alloc_contiguous(&mut self, count: usize, align_log2: usize) -> (res: Option<PAddrExec>)
        requires
            old(self).wf(),
            0 < count as nat <= old(self).region_pages(),
            align_log2 < 64,
        ensures
            self.wf(),
            match res {
                Some(p) => {
                    let addr = p.view();
                    let ps = Self::page_size();
                    let base_idx = paddr_to_idx(old(self).base(), addr, ps);
                    let n = count as nat;

                    &&& addr.within(old(self).base(), old(self).region_pages() * ps)
                    &&& base_idx + n <= old(self).region_pages()
                    // “按页下标”对齐（更通用，不强绑定 addr 的算术溢出问题）
                    &&& base_idx % pow2(align_log2 as nat) == 0

                    // 分配区间内全部变成 false
                    &&& forall|j: int| base_idx <= j < base_idx + n ==> self.bits()[j] == false
                    // 区间外保持不变
                    &&& forall|j: int|
                        (0 <= j < base_idx || base_idx + n <= j < Self::cap_pages())
                        ==> self.bits()[j] == old(self).bits()[j]
                }
                None => {
                    // 找不到合适区间：状态不变（足够弱，便于不同算法实现）
                    self.bits() == old(self).bits()
                }
            }
    ;

    /// 释放 1 页（unsafe：要求该页此前确实由 alloc 分配）
    unsafe fn dealloc(&mut self, p: PAddrExec)
        requires
            old(self).wf(),
            p.view().aligned(Self::page_size()),
            p.view().within(old(self).base(), old(self).region_pages() * Self::page_size()),
            old(self).bits()[paddr_to_idx(old(self).base(), p.view(), Self::page_size()) as int] == false,
        ensures
            self.wf(),
            {
                let idx = paddr_to_idx(old(self).base(), p.view(), Self::page_size());
                self.bits() == old(self).bits().update(idx as int, true)
            }
    ;

    /// 释放连续 count 页（unsafe：要求此前确实由 alloc_contiguous 分配）
    unsafe fn dealloc_contiguous(&mut self, p: PAddrExec, count: usize)
        requires
            old(self).wf(),
            0 < count as nat,
            p.view().aligned(Self::page_size()),
            p.view().within(old(self).base(), old(self).region_pages() * Self::page_size()),
            {
                let base_idx = paddr_to_idx(old(self).base(), p.view(), Self::page_size());
                let n = count as nat;
                &&& base_idx + n <= old(self).region_pages()
                &&& forall|j: int| base_idx <= j < base_idx + n ==> old(self).bits()[j] == false
            },
        ensures
            self.wf(),
            {
                let base_idx = paddr_to_idx(old(self).base(), p.view(), Self::page_size());
                let n = count as nat;
                // 释放区间内全部变成 true
                &&& forall|j: int| base_idx <= j < base_idx + n ==> self.bits()[j] == true
                // 区间外保持不变
                &&& forall|j: int|
                    (0 <= j < base_idx || base_idx + n <= j < Self::cap_pages())
                    ==> self.bits()[j] == old(self).bits()[j]
            }
    ;
}

} // verus!
