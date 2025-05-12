use vstd::prelude::*;

verus! {

    pub open spec const PAGE_SIZE: nat = 4096;
    pub open spec const MAX_FRAMES: nat = 1024 * 1024; // 支持最多 1M 个页
    
    /// 物理帧编号
    type FrameIdx = nat;

    pub struct FrameAllocatorState {
        pub base: nat,
        pub used: Set<FrameIdx>, // 表示已分配帧编号 idx ∈ [0, MAX_FRAMES)
    }
    
    impl FrameAllocatorState {
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
        
        
        #[verifier(external_body)]
        pub open spec fn alloc(
            s1: Self,
            s2: Self,
            ret: Option<nat>,
        ) -> bool{
            &&& s1.inv()
            &&& s2.inv()
            &&& match ret {
                    Some(pa) => {
                        exists |i: FrameIdx| 
                            s1.is_free(i) &&
                            pa == s1.to_phys(i) &&
                            s2.used == s1.used.insert(i)
                    },
                    None => {
                        forall |i: FrameIdx| !s1.is_free(i) &&
                        s2.used == s1.used
                    }
                }
        }               
    }
    
}