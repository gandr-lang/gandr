//! The small vector: its items in place and in one block, each operation
//! against a `Vec`, a refused grow, and each item's one drop.
#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        primitive_signature,
        reason = "the fixtures pass a count of items and the index of the item whose drop panics"
    )
)]

use alloc::alloc::Global;
use core::alloc::AllocError;
use core::alloc::Allocator;
use core::alloc::Layout;
use core::cell::Cell;
use core::hash::BuildHasher as _;
use core::mem::size_of;
use core::panic::AssertUnwindSafe;
use core::ptr::NonNull;
use core::sync::atomic::AtomicUsize;
use core::sync::atomic::Ordering;
use std::hash::RandomState;
use std::panic::catch_unwind;

use gandr_kernel_data::Count;
use gandr_kernel_data::Refused;
use gandr_kernel_data::SmallVec;
use proptest::prelude::Just;
use proptest::prelude::ProptestConfig;
use proptest::prelude::Strategy;
use proptest::prelude::TestCaseError;
use proptest::prelude::any;
use proptest::prelude::prop;
use proptest::prop_assert;
use proptest::prop_assert_eq;
use proptest::prop_oneof;
use proptest::proptest;

/// The global allocator, which counts the blocks it draws and refuses each
/// draw past `limit`.
#[derive(Clone, Copy)]
struct Counting<'count>
{
    /// The blocks drawn so far.
    drawn: &'count Cell<usize>,
    /// The blocks the allocator draws before it refuses.
    limit: usize,
}

/// # Safety
/// - unsafe invariants: each block comes from `Global` and returns to it, so
///   the allocator keeps `Global`'s own.
// SAFETY: each block comes from `Global` and returns to it.
unsafe impl Allocator for Counting<'_>
{
    /// A block of `layout` from `Global` while fewer than `limit` blocks are
    /// drawn, and a refusal past that.
    ///
    /// # Specification
    /// trivial.
    fn allocate(
        &self,
        layout: Layout,
    ) -> Result<NonNull<[u8]>, AllocError>
    {
        if self.drawn.get() >= self.limit {
            return Err(AllocError);
        }
        self.drawn.set(self.drawn.get().saturating_add(1));
        Global.allocate(layout)
    }

    /// # Safety
    /// - unsafe invariants: the caller's, as `Allocator::deallocate` states.
    ///
    /// # Specification
    /// trivial.
    unsafe fn deallocate(
        &self,
        ptr: NonNull<u8>,
        layout: Layout,
    )
    {
        // SAFETY: the caller's block came from `allocate`, which drew it from
        // `Global` with `layout`.
        unsafe {
            Global.deallocate(ptr, layout);
        }
    }
}

/// An item that counts its drops, and panics in the drop that `explodes`
/// names.
struct Bomb<'count>
{
    /// The drops so far.
    drops: &'count Cell<usize>,
    /// Whether this item's drop panics.
    explodes: bool,
}

impl Drop for Bomb<'_>
{
    /// Counts the drop, and panics when the item explodes.
    ///
    /// # Specification
    /// trivial.
    fn drop(&mut self)
    {
        self.drops.set(self.drops.get().saturating_add(1));
        assert!(!self.explodes, "the item's drop panics");
    }
}

/// `count` items, of which the one at `at` panics in its drop.
///
/// # Specification
/// trivial.
fn bombs<const N: usize>(
    drops: &Cell<usize>,
    count: usize,
    at: usize,
) -> SmallVec<Bomb<'_>, N, Global>
{
    (0_usize .. count)
        .map(|index| Bomb {
            drops,
            explodes: index == at,
        })
        .collect()
}

/// One operation of the model test.
#[derive(Clone, Debug)]
enum Operation
{
    /// Push the item.
    Push(u16),
    /// Pop the last item.
    Pop,
    /// Truncate to the length.
    Truncate(usize),
    /// Clear the vector.
    Clear,
    /// Extend by the items.
    Extend(Vec<u16>),
    /// Drain the range, clamped to the length.
    Drain(usize, usize),
    /// Write the item at the index, if the vector holds one there.
    Write(usize, u16),
    /// Keep the items below the bound.
    Retain(u16),
    /// Remove the item at the index by a swap, if the vector holds one there.
    SwapRemove(usize),
    /// Remove the item at the index, if the vector holds one there.
    Remove(usize),
    /// Pop the last item if it is below the bound.
    PopIf(u16),
}

/// Any operation, over lengths up to about three times the largest `N`.
///
/// # Specification
/// trivial.
fn operation() -> impl Strategy<Value = Operation>
{
    prop_oneof![
        any::<u16>().prop_map(Operation::Push),
        Just(Operation::Pop),
        (0_usize .. 24_usize).prop_map(Operation::Truncate),
        Just(Operation::Clear),
        prop::collection::vec(any::<u16>(), 0_usize .. 12_usize).prop_map(Operation::Extend),
        (0_usize .. 24_usize, 0_usize .. 24_usize)
            .prop_map(|(first, second)| Operation::Drain(first.min(second), first.max(second))),
        (0_usize .. 24_usize, any::<u16>()).prop_map(|(at, item)| Operation::Write(at, item)),
        any::<u16>().prop_map(Operation::Retain),
        (0_usize .. 24_usize).prop_map(Operation::SwapRemove),
        (0_usize .. 24_usize).prop_map(Operation::Remove),
        any::<u16>().prop_map(Operation::PopIf),
    ]
}

/// Applies `operations` to a vector of `N` in place and to a `Vec`, and
/// compares the two after each. The clone, its items by value and a vector
/// collected from the model then match the model's final items.
///
/// # Specification
/// trivial.
fn agree<const N: usize>(operations: &[Operation]) -> Result<(), TestCaseError>
{
    let mut small = SmallVec::<u16, N, Global>::new();
    let mut model = Vec::new();
    for operation in operations {
        match *operation {
            Operation::Push(item) => {
                small.push(item);
                model.push(item);
            },
            Operation::Pop => prop_assert_eq!(small.pop(), model.pop()),
            Operation::Truncate(len) => {
                small.truncate(Count::from(len));
                model.truncate(len);
            },
            Operation::Clear => {
                small.clear();
                model.clear();
            },
            Operation::Extend(ref items) => {
                small.extend(items.iter().copied());
                model.extend(items.iter().copied());
            },
            Operation::Drain(start, end) => {
                let (start, end) = (start.min(model.len()), end.min(model.len()));
                prop_assert!(
                    small.drain(start .. end).eq(model.drain(start .. end)),
                    "the drain yields the model's range"
                );
            },
            Operation::Write(at, item) => {
                if let (Some(slot), Some(kept)) =
                    (small.as_mut_slice().get_mut(at), model.get_mut(at))
                {
                    *slot = item;
                    *kept = item;
                }
            },
            Operation::Retain(bound) => {
                small.retain(|&item| item < bound);
                model.retain(|&item| item < bound);
            },
            Operation::SwapRemove(at) => {
                if at < model.len() {
                    prop_assert_eq!(small.swap_remove(Count::from(at)), model.swap_remove(at));
                }
            },
            Operation::Remove(at) => {
                if at < model.len() {
                    prop_assert_eq!(small.remove(Count::from(at)), model.remove(at));
                }
            },
            Operation::PopIf(bound) => {
                prop_assert_eq!(
                    small.pop_if(|item| *item < bound),
                    model.pop_if(|item| *item < bound)
                );
            },
        }
        prop_assert_eq!(small.as_slice(), model.as_slice());
        prop_assert_eq!(
            (small.len(), small.is_empty()),
            (model.len(), model.is_empty())
        );
    }
    prop_assert!(
        small.clone().into_iter().eq(model.iter().copied()),
        "the clone yields the model's items by value"
    );
    let collected: SmallVec<u16, N, Global> = model.iter().copied().collect();
    prop_assert_eq!(collected.as_slice(), model.as_slice());
    Ok(())
}

/// The model test's configuration: fewer cases under Miri, and no file of
/// failures, which Miri's isolation refuses.
///
/// # Specification
/// trivial.
fn config() -> ProptestConfig
{
    ProptestConfig {
        cases: if cfg!(miri) { 4_u32 } else { 256_u32 },
        failure_persistence: None,
        ..ProptestConfig::default()
    }
}

proptest! {
    #![proptest_config(config())]

    /// Each sequence of operations leaves the small vector and a `Vec` with
    /// the same items, at `N` of 0, 1, 4 and 8.
    #[test]
    fn each_operation_agrees_with_a_vec(operations in prop::collection::vec(operation(), 0_usize .. 48_usize))
    {
        agree::<0>(&operations)?;
        agree::<1>(&operations)?;
        agree::<4>(&operations)?;
        agree::<8>(&operations)?;
    }
}

/// Pushes items past `N` and answers whether they read back in order.
///
/// # Specification
/// trivial.
fn pushed<const N: usize>() -> bool
{
    let count = N.saturating_mul(3).saturating_add(2);
    let mut vec = SmallVec::<usize, N, Global>::new();
    (0_usize .. count).for_each(|item| vec.push(item));
    vec.iter().copied().eq(0_usize .. count)
}

/// Vectors of one set of items in place, spilled and of two capacities
/// compare equal, hash alike and order as their slices.
#[test]
fn vectors_compare_and_hash_as_their_slices()
{
    let items = [3_u16, 1, 4, 1, 5];
    let inline: SmallVec<u16, 8, Global> = items.into_iter().collect();
    let spilled: SmallVec<u16, 2, Global> = items.into_iter().collect();
    assert!(
        inline == spilled,
        "the same items compare equal across capacities"
    );
    let shorter: SmallVec<u16, 8, Global> = [3_u16, 1, 4].into_iter().collect();
    assert!(shorter != inline, "a prefix is not the whole");
    assert_eq!(
        (shorter.cmp(&inline), shorter.partial_cmp(&inline)),
        (
            [3_u16, 1, 4].as_slice().cmp(items.as_slice()),
            [3_u16, 1, 4].as_slice().partial_cmp(items.as_slice())
        ),
        "a vector orders as its slice"
    );
    let state = RandomState::new();
    assert_eq!(
        state.hash_one(&inline),
        state.hash_one(items.to_vec()),
        "a vector hashes as a `Vec` of its items"
    );
    assert_eq!(
        state.hash_one(&inline),
        state.hash_one(&spilled),
        "a vector in place and a spilled one hash alike"
    );
}

/// Up to `N` items lie in place and draw no block. The push past `N` moves
/// all the items into one block, and a capacity past `N` draws one block.
#[test]
fn a_vector_holds_its_items_in_place_up_to_n_and_in_one_block_past_it()
{
    let drawn = Cell::new(0_usize);
    let counting = Counting {
        drawn: &drawn,
        limit: usize::MAX,
    };
    let mut vec = SmallVec::<u64, 4, _>::new_in(counting);
    (0_u64 .. 4_u64).for_each(|item| vec.push(item));
    assert_eq!(
        (usize::from(vec.capacity()), drawn.get()),
        (4_usize, 0_usize),
        "four items lie in place and draw no block"
    );
    vec.push(4_u64);
    assert_eq!(drawn.get(), 1_usize, "the fifth item draws one block");
    assert_eq!(
        vec.as_slice(),
        [0_u64, 1_u64, 2_u64, 3_u64, 4_u64],
        "the block holds each item in order"
    );
    let _fits = SmallVec::<u64, 4, _>::with_capacity_in(Count::from(4_usize), counting);
    assert_eq!(drawn.get(), 1_usize, "a capacity of four draws no block");
    let past = SmallVec::<u64, 4, _>::with_capacity_in(Count::from(5_usize), counting);
    assert_eq!(
        (drawn.get(), usize::from(past.capacity()) >= 5_usize),
        (2_usize, true),
        "a capacity of five draws one block"
    );
    assert!(
        pushed::<0>() && pushed::<1>() && pushed::<4>() && pushed::<8>(),
        "pushes at N of 0, 1, 4 and 8 read back in order across the spill"
    );
}

/// The drops of the zero-sized `Token`.
static TOKEN_DROPS: AtomicUsize = AtomicUsize::new(0);

/// A zero-sized item that counts its drops.
struct Token;

impl Drop for Token
{
    /// Counts the drop.
    ///
    /// # Specification
    /// trivial.
    fn drop(&mut self)
    {
        TOKEN_DROPS.fetch_add(1_usize, Ordering::Relaxed);
    }
}

/// A vector of zero-sized items counts them, never spills, and drops each
/// once, whether it pops, drains or drops it.
#[test]
fn a_zero_sized_item_takes_no_storage()
{
    let mut vec = SmallVec::<Token, 0, Global>::new();
    (0_usize .. 1_000_usize).for_each(|_| vec.push(Token));
    assert_eq!(
        (vec.len(), usize::from(vec.capacity())),
        (1_000_usize, isize::MAX.cast_unsigned()),
        "a thousand tokens never fill the capacity"
    );
    drop(vec.pop());
    assert_eq!(
        vec.drain(.. 9_usize).count(),
        9_usize,
        "the drain yields nine tokens"
    );
    drop(vec);
    assert_eq!(
        TOKEN_DROPS.load(Ordering::Relaxed),
        1_000_usize,
        "each token drops once"
    );
    assert_eq!(
        size_of::<SmallVec<Token, 0, Global>>(),
        size_of::<usize>().saturating_mul(3),
        "a vector of tokens is its length and the empty pair"
    );
}

/// An allocator that refuses each block leaves the vector whole, a spilled
/// vector whose grow is refused keeps its block, and a length past
/// `isize::MAX` is refused, by `try_reserve` as an error and by `extend` as a
/// panic.
#[test]
fn a_grow_past_the_length_or_the_allocator_is_refused_and_the_vector_stays()
{
    let drawn = Cell::new(0_usize);
    let mut vec = SmallVec::<u64, 2, _>::new_in(Counting {
        drawn: &drawn,
        limit: 0_usize,
    });
    vec.extend([1_u64, 2_u64]);
    let four = Layout::array::<u64>(4_usize).expect("four items have a layout");
    assert_eq!(
        vec.try_reserve(Count::from(1_usize)),
        Err(Refused::Allocator(four)),
        "the allocator refuses the first block"
    );
    assert_eq!(
        (vec.as_slice(), usize::from(vec.capacity())),
        (&[1_u64, 2_u64][..], 2_usize),
        "the refused vector stays in place"
    );
    assert_eq!(
        vec.try_reserve(Count::from(usize::MAX)),
        Err(Refused::Overflow),
        "a length past isize::MAX is refused"
    );
    let unwound = catch_unwind(AssertUnwindSafe(|| {
        vec.extend(core::iter::repeat_n(0_u64, usize::MAX));
    }));
    assert!(
        unwound.is_err() && vec.as_slice() == [1_u64, 2_u64],
        "an extend past isize::MAX panics and leaves the vector whole"
    );
    let once = Cell::new(0_usize);
    let mut spilled = SmallVec::<u64, 2, _>::new_in(Counting {
        drawn: &once,
        limit: 1_usize,
    });
    spilled.extend([1_u64, 2_u64, 3_u64]);
    let eight = Layout::array::<u64>(8_usize).expect("eight items have a layout");
    assert_eq!(
        spilled.try_reserve(Count::from(2_usize)),
        Err(Refused::Allocator(eight)),
        "the allocator refuses the second block"
    );
    assert_eq!(
        (spilled.as_slice(), usize::from(spilled.capacity())),
        (&[1_u64, 2_u64, 3_u64][..], 4_usize),
        "the refused vector keeps its block and its items"
    );
}

/// A drain yields its range in order and closes the gap, spilled and in
/// place, and a drain dropped part way drops the rest of its range.
#[test]
fn a_drain_yields_its_range_and_closes_the_gap()
{
    let mut spilled: SmallVec<u32, 4, Global> = (0_u32 .. 8_u32).collect();
    assert_eq!(
        spilled.drain(2_usize .. 5_usize).collect::<Vec<u32>>(),
        [2_u32, 3_u32, 4_u32],
        "the drain yields its range"
    );
    assert_eq!(
        spilled.as_slice(),
        [0_u32, 1_u32, 5_u32, 6_u32, 7_u32],
        "the items past the range close the gap"
    );
    let mut inline: SmallVec<u32, 8, Global> = (0_u32 .. 6_u32).collect();
    let mut drain = inline.drain(1_usize ..= 3_usize);
    assert_eq!(drain.next(), Some(1_u32), "the drain yields its first item");
    drop(drain);
    assert_eq!(
        inline.as_slice(),
        [0_u32, 4_u32, 5_u32],
        "a drain dropped part way drops the rest of its range"
    );
    assert_eq!(
        inline.drain(..).count(),
        3_usize,
        "a full drain yields each item"
    );
    assert!(inline.is_empty(), "a full drain empties the vector");
}

/// A panic in one item's drop leaves each other item dropped once, and the
/// block returned, for the vector's drop, `truncate`, an iterator by value
/// and a drain.
#[test]
fn an_item_whose_drop_panics_leaves_each_other_item_dropped_once()
{
    let drops = Cell::new(0_usize);
    let vec = bombs::<4>(&drops, 6_usize, 2_usize);
    let unwound = catch_unwind(AssertUnwindSafe(move || drop(vec)));
    assert_eq!(
        (unwound.is_err(), drops.get()),
        (true, 6_usize),
        "the vector's drop drops each item once"
    );

    let drops = Cell::new(0_usize);
    let mut items = bombs::<4>(&drops, 6_usize, 3_usize).into_iter();
    drop(items.next());
    let unwound = catch_unwind(AssertUnwindSafe(move || drop(items)));
    assert_eq!(
        (unwound.is_err(), drops.get()),
        (true, 6_usize),
        "an iterator dropped part way drops each item once"
    );

    let drops = Cell::new(0_usize);
    let mut vec = bombs::<8>(&drops, 6_usize, 4_usize);
    let unwound = catch_unwind(AssertUnwindSafe(|| vec.truncate(Count::from(2_usize))));
    assert_eq!(
        (unwound.is_err(), drops.get(), vec.len()),
        (true, 4_usize, 2_usize),
        "truncate drops each item past the length once"
    );
    drop(vec);
    assert_eq!(drops.get(), 6_usize, "the rest drop with the vector");

    let drops = Cell::new(0_usize);
    let mut vec = bombs::<4>(&drops, 7_usize, 3_usize);
    let unwound = catch_unwind(AssertUnwindSafe(|| drop(vec.drain(1_usize .. 5_usize))));
    assert_eq!(
        (unwound.is_err(), drops.get(), vec.len()),
        (true, 4_usize, 3_usize),
        "a drain drops its range once and closes the gap"
    );
    drop(vec);
    assert_eq!(drops.get(), 7_usize, "the rest drop with the vector");
}

/// An array converts in place, and the conversion's error is the never type,
/// so the match takes `Ok` alone.
#[test]
#[expect(
    clippy::unnecessary_fallible_conversions,
    reason = "the test reads the conversion's error type, the never type"
)]
fn an_array_converts_with_no_error_arm()
{
    let Ok(vec) = SmallVec::<u8, 3, Global>::try_from([1_u8, 2_u8, 3_u8]);
    assert_eq!(
        (vec.as_slice(), usize::from(vec.capacity())),
        (&[1_u8, 2_u8, 3_u8][..], 3_usize),
        "the array's items lie in place"
    );
}

/// A vector is one word of length beside the larger of its inline array and
/// the block's pointer and capacity.
#[test]
fn the_size_is_one_word_beside_the_larger_half()
{
    let word = size_of::<usize>();
    assert_eq!(
        [
            size_of::<SmallVec<u64, 0, Global>>(),
            size_of::<SmallVec<u64, 1, Global>>(),
            size_of::<SmallVec<u64, 2, Global>>(),
            size_of::<SmallVec<u64, 4, Global>>(),
            size_of::<SmallVec<u64, 8, Global>>(),
            size_of::<SmallVec<u8, 16, Global>>(),
        ],
        [
            word.saturating_mul(3),
            word.saturating_mul(3),
            word.saturating_mul(3),
            word.saturating_add(32_usize),
            word.saturating_add(64_usize),
            word.saturating_add(16_usize),
        ],
        "the length word beside the larger half"
    );
}
