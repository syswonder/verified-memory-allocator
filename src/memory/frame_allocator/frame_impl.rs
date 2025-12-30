use vstd::prelude::*;
use crate::addr::{PAddr, PAddrExec};
use crate::bitalloc_verus::{BitAlloc, BitAllocView, BitAlloc1M}; // 你 bitalloc_verus.rs 里提供的

use crate::frame_alloc::r#trait::{FrameAllocView, FrameAllocator, idx_to_paddr, paddr_to_idx, pow2};

verus! {

pub struct BitmapFrameAllocator {
    base: PAddrExec,
    region_pages_exec: usize,
    inner: BitAlloc1M,
}

impl BitmapFrameAllocator {
    pub fn empty() -> Self {
        Self { base: PAddrExec(0), region_pages_exec: 0, inner: BitAlloc1M::default() }
    }

    ///（可选）运行时查询
    pub fn region_pages_usize(&self) -> usize { self.region_pages_exec }
}

impl FrameAllocView for BitmapFrameAllocator {
    spec fn base(&self) -> PAddr { self.base.view() }

    spec fn region_pages(&self) -> nat { self.region_pages_exec as nat }

    spec fn bits(&self) -> Seq<bool> { self.inner@ }

    spec fn page_size() -> nat {
        // 你也可以改成：crate::consts::PAGE_SIZE as nat
        4096
    }

    spec fn cap_pages() -> nat {
        // BitAlloc1M::spec_cap() 是 usize，这里转成 nat
        BitAlloc1M::spec_cap() as nat
    }

    // wf() 使用 trait 默认定义即可（如果你想加强，也可以在这里重写）
}

impl FrameAllocator for BitmapFrameAllocator {

    fn init(&mut self, base: PAddrExec, size: usize) {
        let ps = Self::page_size() as usize;
        let pages: usize = size / ps;

        // reset
        self.base = base;
        self.region_pages_exec = pages;
        self.inner = BitAlloc1M::default();

        // 只把 [0, pages) 标记为 free；其余保持 false（不可用）
        self.inner.insert(0..pages);
    }

    unsafe fn alloc(&mut self) -> (res: Option<PAddrExec>) {
        match self.inner.alloc() {
            Some(idx) => {
                let ps = Self::page_size() as usize;
                Some(PAddrExec(self.base.0 + idx * ps))
            }
            None => None
        }
    }

    unsafe fn alloc_contiguous(&mut self, count: usize, align_log2: usize) -> (res: Option<PAddrExec>) {
        match self.inner.alloc_contiguous(count, align_log2) {
            Some(base_idx) => {
                let ps = Self::page_size() as usize;
                Some(PAddrExec(self.base.0 + base_idx * ps))
            }
            None => None
        }
    }

    unsafe fn dealloc(&mut self, p: PAddrExec) {
        let ps = Self::page_size() as usize;
        let idx = (p.0 - self.base.0) / ps;
        self.inner.dealloc(idx);
    }

    unsafe fn dealloc_contiguous(&mut self, p: PAddrExec, count: usize) {
        let ps = Self::page_size() as usize;
        let base_idx = (p.0 - self.base.0) / ps;

        // 用 while 写，后续你要做 Verus 证明时更好加 invariant
        let mut k: usize = 0;
        while k < count
            invariant
                k <= count,
                self.wf(), // 需要的话也可写更细的循环不变量
        {
            self.inner.dealloc(base_idx + k);
            k = k + 1;
        }
    }
}

} // verus!
