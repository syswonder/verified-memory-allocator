use vstd::{prelude::*, seq_lib::*};

verus!{
global layout usize is size == 8;

/// The capacity is an exponential multiple of 16.
/// and the current bitmap only supports the maximum allocatable page size of 1M.
pub open spec fn is_pow16(cap: usize) -> bool {
    cap == 16 || cap == 256 || cap == 4096 || cap == 65536 || cap == 1048576
}

pub trait BitAllocView {
    /// Specification function to view the internal u16 as a sequence of booleans.
    spec fn view(&self) -> Seq<bool>;

    /// The bitmap has a total of CAP bits, numbered from 0 to CAP-1 inclusively.
    fn cap() -> (res:usize)
        requires
            Self::cascade_not_overflow(),
        ensures
            res == Self::spec_cap(),
    ;

    spec fn spec_cap() -> (res:usize);

    spec fn cascade_not_overflow() -> bool;

    spec fn lemma_cap_is_pow16_pre() -> bool;

    /// The capacity is an exponential multiple of 16.
    /// and the current bitmap only supports the maximum allocatable page size of 1M.
    proof fn lemma_cap_is_pow16()
        requires
            Self::lemma_cap_is_pow16_pre(),
            Self::cascade_not_overflow(),
        ensures
            is_pow16(Self::spec_cap()),
    ;

    /// The default value. Workaround for `const fn new() -> Self`.
    fn default() -> Self where Self: Sized;

    /// Structure is well_formed
    spec fn wf(&self) -> bool;

    // /// Find a index not less than a given key, where the bit is free.
    // fn next(&self, key: usize) -> (res: Option<usize>)
    //     requires
    //         self.wf(),
    //         key < Self::spec_cap(),
    //     ensures
    //         self.wf(),
    //         match res {
    //             Some(re) => {
    //                 // If successful, returns the first free index `re` that is not less than `key`.
    //                 // All indices between `key` and `re` (exclusive) must be allocated (false).
    //                 &&& self@[re as int] == true
    //                 &&& re < Self::spec_cap()
    //                 &&& re >= key
    //                 &&& forall|i: int| key <= i < re ==> self@[i] == false
    //             },
    //             None => {
    //                 // If failed, all indices from `key` to the end are allocated (false).
    //                 forall|i: int| key <= i < Self::spec_cap() ==> self@[i] == false
    //             }
    //         },
    // ;

    /// Lemma: When self is well-formed, spec_any() is equivalent to
    /// “there exists an index j such that self@[j] == true”,
    /// linking the abstract semantics with the concrete boolean bits.
    proof fn lemma_bits_nonzero_implies_exists_true(&self)
        requires
            self.wf(),
        ensures
            self.wf(),
            self.spec_any() == exists|j:int| 0 <= j < Self::spec_cap() && self@[j] == true,
    ;

    /// Whether there are free bits remaining
    fn any(&self) -> (res: bool)
        ensures
            res == self.spec_any(),
    ;

    spec fn spec_any(&self) -> bool;

    // /// Whether a specific bit is free
    // fn test(&self, key: usize) -> (res: bool)
    //     requires
    //         self.wf(),
    //         key < Self::spec_cap(),
    //     ensures
    //         self.wf(),
    //         res == self@[key as int],
    // ;
}

/// Represents a 16-bit bitmap allocator.
#[derive(Clone, Copy)]
pub struct BitAlloc16 {
    pub bits: u16,
}

fn main() {}

} // verus