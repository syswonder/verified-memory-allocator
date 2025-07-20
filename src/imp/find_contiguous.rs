use vstd::prelude::*;

verus! {

// Define the BitAlloc trait
pub trait BitAlloc {
    spec fn is_free(&self, idx: nat) -> bool;
    spec fn capacity(&self) -> nat;

    // next(offset) returns the index of the next free bit at or after offset
    // or None if no such bit exists within capacity.
    spec fn next_spec(&self, offset: nat) -> Option<nat>;

    // any() returns true if there is at least one free bit within capacity.
    spec fn any_spec(&self) -> bool;

    // Invariants for the trait methods
    proof fn next_spec_properties(&self) {
        ensures({
            let res = self.next_spec(0);
            (res.is_Some() ==> self.is_free(res.get_Some()))
            && (res.is_Some() ==> res.get_Some() < self.capacity())
            && (res.is_None() ==> forall|i: nat| i < self.capacity() ==> !self.is_free(i))
        });
    }

    proof fn any_spec_properties(&self) {
        ensures(
            self.any_spec() <==> exists|i: nat| i < self.capacity() && self.is_free(i)
        );
    }
}

// The find_contiguous function
pub fn find_contiguous<BA: BitAlloc>(
    ba: &BA,
    capacity: usize,
    size: usize,
    align_log2: usize,
) -> (result: Option<usize>)
    requires
        capacity == ba.capacity(),
        // The BitAlloc trait methods must satisfy their properties
        ba.next_spec_properties(),
        ba.any_spec_properties(),
    ensures({
        let (result) = result;
        match result {
            Some(base) => {
                // The returned base is within capacity
                base + size <= capacity
                // The block is aligned
                && base % (1usize << align_log2) == 0
                // All bits in the block are free
                && forall|i: nat| base <= i && i < base + size ==> ba.is_free(i)
            },
            None => {
                // If None is returned, no such block exists
                forall|base_candidate: nat| {
                    (base_candidate + size <= capacity
                    && base_candidate % (1usize << align_log2) == 0)
                    ==>
                    exists|i: nat| base_candidate <= i && i < base_candidate + size && !ba.is_free(i)
                }
            },
        }
    })
{
    if capacity < (1usize << align_log2) || !ba.any_spec() {
        return None;
    }

    let mut base: usize = 0;
    let mut offset: usize = base;

    while offset < capacity
        invariant
            base <= offset,
            offset <= capacity,
            // All bits before `base` are either allocated or not aligned correctly for a block of `size`
            forall|k: nat| {
                (k < base as nat
                && k + size <= capacity as nat
                && k % (1usize << align_log2) == 0)
                ==>
                exists|i: nat| k <= i && i < k + size && !ba.is_free(i)
            },
            // If `offset` is not `base`, then the bits from `base` to `offset-1` are free
            // and `offset - base` is the current length of the contiguous free block starting at `base`
            (base <= offset && offset <= capacity && base % (1usize << align_log2) == 0
            && forall|i: nat| base <= i && i < offset ==> ba.is_free(i))
            || (base > offset),

    {
        let next_free_bit = ba.next_spec(offset as int);

        match next_free_bit {
            Some(next) => {
                if next != offset as nat {
                    // it can be guaranteed that no bit in (offset..next) is free
                    // move to next aligned position after next-1
                    assert(next > offset as nat);
                    base = (((next - 1) as usize >> align_log2) + 1) << align_log2;
                    offset = base;
                    continue;
                }
            }
            None => {
                // No more free bits, so no block can be found
                // We need to prove that no such block exists from `offset` to `capacity`
                // and combine it with the invariant about `base`
                assert(forall|k: nat| {
                    (k >= offset as nat
                    && k + size <= capacity as nat
                    && k % (1usize << align_log2) == 0)
                    ==>
                    exists|i: nat| k <= i && i < k + size && !ba.is_free(i)
                });
                return None;
            }
        }

        offset = offset + 1;

        if offset - base == size {
            // We found a block of `size` free bits starting at `base`
            assert(base + size <= capacity);
            assert(base % (1usize << align_log2) == 0);
            assert(forall|i: nat| base <= i && i < base + size ==> ba.is_free(i));
            return Some(base);
        }
    }
    // If the loop finishes, it means no block was found
    assert(forall|base_candidate: nat| {
        (base_candidate + size <= capacity as nat
        && base_candidate % (1usize << align_log2) == 0)
        ==>
        exists|i: nat| base_candidate <= i && i < base_candidate + size && !ba.is_free(i)
    });
    None
}

}
