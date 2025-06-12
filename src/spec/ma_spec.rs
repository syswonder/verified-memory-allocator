use vstd::prelude::*;

verus! {

    pub open spec const PAGE_SIZE: nat = 4096;
    pub open spec const MAX_FRAMES: nat = 1024 * 1024; // 支持最多 1M 个页

    /// 物理帧编号
    type FrameIdx = nat;

    pub struct FrameAllocator {
        pub base: nat,
        pub used: Set<FrameIdx>, // 表示已分配帧编号 idx ∈ [0, MAX_FRAMES)
    }

    impl FrameAllocator {
        /// 不变量
        pub open spec fn inv(&self) -> bool {
            forall |i: FrameIdx| self.used.contains(i) ==> i < MAX_FRAMES
        }

        /// 某帧是否未分配
        pub open spec fn is_free(&self, i: FrameIdx) -> bool {
            i < MAX_FRAMES && !self.used.contains(i)
        }

        /// 帧编号转物理地址
        pub open spec fn to_phys(&self, i: FrameIdx) -> nat {
            self.base + i * PAGE_SIZE
        }


        // pub open spec fn alloc(
        //     m1: Self,
        //     m2: Self,
        //     ret: Option<nat>,
        // ) -> bool{
        //     &&& m1.inv()
        //     &&& m2.inv()
        //     &&& match ret {
        //             Some(pa) => {
        //                 exists |i: FrameIdx|
        //                     m1.is_free(i) &&
        //                     pa == m1.to_phys(i) &&
        //                     m2.used == m1.used.insert(i)
        //             },
        //             None => {
        //                 forall |i: FrameIdx| !m1.is_free(i) &&
        //                 m2.used == m1.used
        //             }
        //         }
        // }
    }


    // proof fn prove_alloc_return_valid(
    //     m1: FrameAllocatorState,
    //     m2: FrameAllocatorState,
    //     ret: Option<nat>,
    // )
    //     requires
    //         FrameAllocatorState::alloc(m1, m2, ret),
    //     ensures
    //         m2.inv(),
    //         match ret {
    //             Some(pa) => pa >= m1.base && (pa - m1.base) % PAGE_SIZE as int == 0 && pa < m1.base + PAGE_SIZE * MAX_FRAMES,
    //             None => forall |i: nat| i < MAX_FRAMES ==> m1.used.contains(i),
    //         }
    // {
    //     match ret {
    //         Some(pa) => {
    //             let i = choose |i: FrameIdx|
    //                 m1.is_free(i) &&
    //                 pa == m1.to_phys(i) &&
    //                 m2.used == m1.used.insert(i);

    //             assert(i < MAX_FRAMES);
    //             assert(!m1.used.contains(i));
    //             assert(pa == m1.base + i * PAGE_SIZE);
    //             assert(pa >= m1.base);
    //             assert((pa - m1.base) % PAGE_SIZE as int == 0);
    //             assert(pa < m1.base + MAX_FRAMES * PAGE_SIZE);
    //         },
    //         None => {
    //             assert(forall |i: FrameIdx| i < MAX_FRAMES ==> m1.used.contains(i));
    //         }
    //     }
    // }


}

fn main() {}
