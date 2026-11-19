//! The small vector: up to `N` items in place, and past `N` all of them in one
//! block of the allocator below. One word holds the length, and its high bit
//! is the tag: clear while the items lie in place, set once they move to the
//! block. A union holds the inline array or the block's pointer and capacity,
//! and the tag names the live half. So an access branches once, on the tag.
//!
//! `N` is a parameter of the type, so each site sets its own, and `N` of zero
//! is a plain heap vector. At `N` of zero, the tag is set from the start, so
//! no access tests it, and an empty vector holds a dangling block of capacity
//! zero, as an empty `Vec` does.
//!
//! A zero-sized item takes no storage, so a vector of them counts its items
//! and never draws a block. A grow that the allocator refuses is an error of
//! [`SmallVec::try_reserve`], and the vector stays as it was. The length, the
//! emptiness, the index and the iterators come from the slice that the vector
//! dereferences to.
//!
//! | `N` and `T` | Size | Storage |
//! | ----------- | ---- | ------- |
//! | two words of items or fewer | three words | in place up to `N` |
//! | more than two words of items | one word and the array | in place up to `N` |
//! | `N` of zero | three words | a plain heap vector |
//! | a zero-sized `T` | three words | a count, and never a block |
//!
//! # Safety
//! - unsafe invariants: the tag names the live half. With the tag clear, the
//!   inline array is live. With the tag set, the pair is live. Its pointer is a
//!   block of the vector's allocator with the array layout of its capacity, or
//!   a dangling pointer at a capacity of zero, which no allocator holds. The
//!   first `len` slots of the live half hold items, and no other slot does. A
//!   vector of zero-sized items never sets the tag. A vector of `N` zero and
//!   items of a size always sets it.

use alloc::alloc::Global;
use alloc::alloc::handle_alloc_error;
use alloc::boxed::Box;
use alloc::vec::Vec;
use core::alloc::Allocator;
use core::alloc::Layout;
use core::borrow::Borrow;
use core::borrow::BorrowMut;
use core::cmp::Ordering;
use core::fmt;
use core::hash::Hash;
use core::hash::Hasher;
use core::marker::PhantomData;
use core::mem::DropGuard;
use core::mem::ManuallyDrop;
use core::mem::MaybeUninit;
use core::mem::conjure_zst;
use core::mem::size_of;
use core::ops::Bound;
use core::ops::Deref;
use core::ops::DerefMut;
use core::ops::RangeBounds;
use core::ptr;
use core::ptr::NonNull;
use core::slice;

use anodized::spec;

/// The bits of the length word that count items.
const LENGTH: usize = isize::MAX.cast_unsigned();

/// The tag: the high bit of the length word, set while the block holds the
/// items.
const SPILLED: usize = !LENGTH;

/// The capacity of the first block of items of `T`, unless a grow asks for
/// more. It is the first capacity of `Vec`: eight items of one byte, four
/// items of up to a kibibyte, and one larger item. So a vector draws a block
/// and grows it as often as a `Vec` of its items does.
///
/// # Specification
/// trivial.
const fn first_block<T>() -> Count
{
    let size = size_of::<T>();
    if size == 1 {
        Count(8)
    }
    else if size <= 1024 {
        Count(4)
    }
    else {
        Count(1)
    }
}

/// A number of items of a vector: its length, its capacity, or the room to
/// reserve. As a place, it names the slot past that many items.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Count(usize);

impl From<usize> for Count
{
    /// # Specification
    /// trivial.
    #[inline]
    fn from(items: usize) -> Self
    {
        Self(items)
    }
}

impl From<Count> for usize
{
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: Count) -> Self
    {
        count.0
    }
}

/// The live half of a vector's storage.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Live
{
    /// The inline array holds the items.
    Inline,
    /// The block holds the items.
    Block,
}

/// The two halves of a vector's storage. The tag in the length names the live
/// one.
#[repr(C)]
union Raw<T, const N: usize>
{
    /// Up to `N` items in place.
    inline: ManuallyDrop<MaybeUninit<[T; N]>>,
    /// The block of the items, and its capacity in items.
    heap: (NonNull<T>, usize),
}

/// A vector that holds up to `N` items in place, and past `N` holds all of
/// them in one block of `A`.
///
/// # Specification
/// - requires: `N` is at most `isize::MAX`, which each constructor checks when
///   it compiles.
/// - ensures: the module's unsafe invariants hold between each two calls.
pub struct SmallVec<T, const N: usize, A>
where
    A: Allocator,
{
    /// The length, with the tag in its high bit.
    tagged: usize,
    /// The inline array or the block: the tag names the live half.
    raw: Raw<T, N>,
    /// The allocator of the block.
    alloc: A,
    /// The vector owns its items, for the drop check.
    items: PhantomData<T>,
}

/// The refusal of an allocation: a grow of a vector, or the block of a shared
/// value. A vector stays as it was, and the build of a shared value gives no
/// block.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Refused
{
    /// The length passes `isize::MAX`, or the block's bytes do.
    Overflow,
    /// The allocator refuses a block of this layout.
    Allocator(Layout),
}

impl Refused
{
    /// Ends the call as a grow of `Vec` ends it: a length past `isize::MAX`
    /// panics, and the allocator's refusal goes to its error handler.
    ///
    /// # Specification
    /// - ensures: the call does not return.
    /// - panics: on [`Refused::Overflow`].
    /// - executable: none — the function returns no value to read.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — an extend whose size hint passes `isize::MAX` panics,
    ///   and the vector before it stays whole.
    /// - witness: `tests::small_vec::a_grow_past_the_length_or_the_allocator_is_refused_and_the_vector_stays`
    #[expect(
        clippy::panic,
        reason = "a length past `isize::MAX` names no layout for the error handler, so it panics as `Vec` does"
    )]
    pub(crate) fn raise(self) -> !
    {
        match self {
            Self::Overflow => panic!("a length passes isize::MAX, or the bytes of its block do"),
            Self::Allocator(layout) => handle_alloc_error(layout),
        }
    }
}

impl<T, const N: usize> SmallVec<T, N, Global>
{
    /// An empty vector over the global allocator.
    ///
    /// # Specification
    /// - ensures: the vector is empty, and holds no block.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the model test starts each run from this vector.
    /// - witness: `tests::small_vec::each_operation_agrees_with_a_vec`
    #[spec(ensures: |ret| ret.count().0 == 0)]
    #[inline]
    #[must_use]
    pub const fn new() -> Self
    {
        Self::new_in(Global)
    }

    /// An empty vector over the global allocator, with room for `capacity`
    /// items.
    ///
    /// # Specification
    /// - ensures: the vector is empty, and holds room for `capacity` items.
    /// - panics: when `capacity` passes `isize::MAX`; the allocator's refusal
    ///   goes to its error handler.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a capacity up to `N` draws no block, and one past it
    ///   draws one.
    /// - witness: `tests::small_vec::a_vector_holds_its_items_in_place_up_to_n_and_in_one_block_past_it`
    #[spec(ensures: |ret| ret.count() == Count(0) && ret.capacity() >= capacity)]
    #[inline]
    #[must_use]
    pub fn with_capacity(capacity: Count) -> Self
    {
        Self::with_capacity_in(capacity, Global)
    }
}

impl<T, const N: usize, A> SmallVec<T, N, A>
where
    A: Allocator,
{
    /// Whether the block holds the items from the start: `N` of zero and
    /// items of a size. The tag is then set from the start, and each access
    /// reads the block with no test of the tag.
    const BLOCK_ONLY: bool = N == 0 && size_of::<T>() != 0;

    /// An empty vector over `alloc`.
    ///
    /// # Specification
    /// - requires: `N` is at most `isize::MAX`; the build refuses a larger `N`.
    /// - ensures: the vector is empty, and holds no block.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a vector over a counting allocator draws no block
    ///   while its items fit in place.
    /// - witness: `tests::small_vec::a_vector_holds_its_items_in_place_up_to_n_and_in_one_block_past_it`
    #[spec(ensures: |ret| ret.count().0 == 0)]
    #[inline]
    #[must_use]
    pub const fn new_in(alloc: A) -> Self
    {
        const {
            assert!(
                N <= LENGTH,
                "the inline array holds more items than the length counts"
            );
        };
        if Self::BLOCK_ONLY {
            return Self {
                tagged: SPILLED,
                raw: Raw {
                    heap: (NonNull::dangling(), 0),
                },
                alloc,
                items: PhantomData,
            };
        }
        Self {
            tagged: 0,
            raw: Raw {
                inline: ManuallyDrop::new(MaybeUninit::uninit()),
            },
            alloc,
            items: PhantomData,
        }
    }

    /// An empty vector over `alloc`, with room for `capacity` items.
    ///
    /// # Specification
    /// - ensures: the vector is empty, and holds room for `capacity` items.
    /// - panics: when `capacity` passes `isize::MAX`; the allocator's refusal
    ///   goes to its error handler.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a capacity up to `N` draws no block, and one past it
    ///   draws one.
    /// - witness: `tests::small_vec::a_vector_holds_its_items_in_place_up_to_n_and_in_one_block_past_it`
    #[spec(ensures: |ret| ret.count() == Count(0) && ret.capacity() >= capacity)]
    #[inline]
    #[must_use]
    pub fn with_capacity_in(
        capacity: Count,
        alloc: A,
    ) -> Self
    {
        let mut vec = Self::new_in(alloc);
        if let Err(refused) = vec.try_reserve(capacity) {
            refused.raise();
        }
        vec
    }

    /// The half that holds the items, as the tag names it. At `N` of zero
    /// with items of a size, the block, with no test of the tag.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    const fn live(&self) -> Live
    {
        if Self::BLOCK_ONLY || (self.tagged & SPILLED) != 0 {
            Live::Block
        }
        else {
            Live::Inline
        }
    }

    /// The number of items.
    ///
    /// # Specification
    /// - ensures: at most `isize::MAX`.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the model test compares the length with a `Vec`'s
    ///   after each operation.
    /// - witness: `tests::small_vec::each_operation_agrees_with_a_vec`
    #[spec(ensures: |ret| ret.0 <= LENGTH)]
    #[inline]
    const fn count(&self) -> Count
    {
        Count(self.tagged & LENGTH)
    }

    /// The items the vector holds before it grows: `N` in place, the block's
    /// capacity once it spills, and `isize::MAX` for a zero-sized item.
    ///
    /// # Specification
    /// - ensures: at least the length.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the capacity is `N` until the push past `N`, and a
    ///   vector of zero-sized items never spills.
    /// - witness: `tests::small_vec::a_vector_holds_its_items_in_place_up_to_n_and_in_one_block_past_it`
    /// - witness: `tests::small_vec::a_zero_sized_item_takes_no_storage`
    #[spec(ensures: |ret| ret >= self.count())]
    #[inline]
    #[must_use]
    pub fn capacity(&self) -> Count
    {
        if size_of::<T>() == 0 {
            return Count(LENGTH);
        }
        match self.live() {
            // SAFETY: the tag names the pair live.
            Live::Block => Count(unsafe { self.raw.heap.1 }),
            Live::Inline => Count(N),
        }
    }

    /// The first slot of the live half.
    ///
    /// # Specification
    /// - ensures: the block's pointer when the vector spills, and a pointer to
    ///   the inline array when it does not.
    /// - panics: none.
    /// - executable: none — a pointer's provenance is no value that a predicate
    ///   reads.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — Miri refuses a read of the dead half, and the model
    ///   test reads each item after each operation.
    /// - witness: `tests::small_vec::each_operation_agrees_with_a_vec`
    #[inline]
    fn as_ptr(&self) -> *const T
    {
        match self.live() {
            // SAFETY: the tag names the pair live.
            Live::Block => unsafe { self.raw.heap.0 }.as_ptr().cast_const(),
            Live::Inline => (&raw const self.raw.inline).cast::<T>(),
        }
    }

    /// The first slot of the live half, for a write.
    ///
    /// # Specification
    /// - ensures: as [`SmallVec::as_ptr`].
    /// - panics: none.
    /// - executable: none — as [`SmallVec::as_ptr`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`SmallVec::as_ptr`].
    /// - witness: `tests::small_vec::each_operation_agrees_with_a_vec`
    #[inline]
    fn as_mut_ptr(&mut self) -> *mut T
    {
        match self.live() {
            // SAFETY: the tag names the pair live.
            Live::Block => unsafe { self.raw.heap.0 }.as_ptr(),
            Live::Inline => (&raw mut self.raw.inline).cast::<T>(),
        }
    }

    /// The items, as a slice.
    ///
    /// # Specification
    /// - ensures: the slice holds the length's items.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the model test compares the slice with a `Vec`'s
    ///   after each operation.
    /// - witness: `tests::small_vec::each_operation_agrees_with_a_vec`
    #[spec(ensures: |ret| Count(ret.len()) == self.count())]
    #[inline]
    #[must_use]
    pub fn as_slice(&self) -> &[T]
    {
        // SAFETY: the first `len` slots of the live half hold items, and the
        // borrow of `self` keeps them.
        unsafe { slice::from_raw_parts(self.as_ptr(), self.count().0) }
    }

    /// The allocator of the vector's block.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn allocator(&self) -> &A
    {
        &self.alloc
    }

    /// The items, as a slice to write through.
    ///
    /// # Specification
    /// - ensures: the slice holds the length's items.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a write through the slice reads back from the vector,
    ///   in place and spilled.
    /// - witness: `tests::small_vec::each_operation_agrees_with_a_vec`
    #[spec(captures: len = self.count(), ensures: |ret| Count(ret.len()) == len)]
    #[inline]
    #[must_use]
    pub fn as_mut_slice(&mut self) -> &mut [T]
    {
        let len = self.count().0;
        // SAFETY: the first `len` slots of the live half hold items, and the
        // borrow of `self` keeps them and excludes each other borrow.
        unsafe { slice::from_raw_parts_mut(self.as_mut_ptr(), len) }
    }

    /// Sets the length to `len`, and keeps the tag.
    ///
    /// # Specification
    /// - requires: `len` is at most the capacity.
    /// - ensures: the length is `len`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each push, pop, truncate and drain sets the length
    ///   that the model test compares.
    /// - witness: `tests::small_vec::each_operation_agrees_with_a_vec`
    #[spec(requires: len <= self.capacity(), ensures: self.count() == len)]
    #[inline]
    fn set_len(
        &mut self,
        len: Count,
    )
    {
        self.tagged = len.0 | (self.tagged & SPILLED);
    }

    /// Room for `additional` more items, or the refusal of the grow.
    ///
    /// The first block holds as many items as the first block of a `Vec`, or
    /// the room asked for if that is more. Each later grow at least doubles
    /// the capacity. A vector of zero-sized items never draws a block.
    ///
    /// # Errors
    /// [`Refused::Overflow`] when the length would pass `isize::MAX`, and
    /// [`Refused::Allocator`] when the allocator refuses the block.
    ///
    /// # Specification
    /// - ensures: the length stays; on `Ok`, the capacity holds `additional`
    ///   more items; on `Err`, the capacity and the items stay.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an allocator that refuses each block leaves the
    ///   vector whole, a reserve past `isize::MAX` is refused, and a spill
    ///   moves each item into the block.
    /// - witness: `tests::small_vec::a_grow_past_the_length_or_the_allocator_is_refused_and_the_vector_stays`
    /// - witness: `tests::small_vec::a_vector_holds_its_items_in_place_up_to_n_and_in_one_block_past_it`
    #[spec(
        captures: [before = self.count(), had = self.capacity()],
        ensures: |ret| self.count() == before
            && if ret.is_ok() { self.capacity().0 >= before.0.saturating_add(additional.0) } else { self.capacity() == had },
    )]
    #[inline]
    pub fn try_reserve(
        &mut self,
        additional: Count,
    ) -> Result<(), Refused>
    {
        let len = self.count().0;
        let needed = len
            .checked_add(additional.0)
            .filter(|&needed| needed <= LENGTH)
            .ok_or(Refused::Overflow)?;
        let capacity = self.capacity().0;
        if needed <= capacity {
            return Ok(());
        }
        let grown = needed
            .max(capacity.saturating_mul(2))
            .clamp(first_block::<T>().0, LENGTH);
        let layout = Layout::array::<T>(grown).map_err(|_overflow| Refused::Overflow)?;
        let block = match self.live() {
            Live::Block => {
                // SAFETY: the tag names the pair live.
                let (old, old_capacity) = unsafe { self.raw.heap };
                if old_capacity == 0 {
                    // A block of capacity zero dangles, and no allocator holds
                    // it, so the grow draws a new block.
                    self.alloc
                        .allocate(layout)
                        .map_err(|_refusal| Refused::Allocator(layout))?
                }
                else {
                    let old_layout =
                        Layout::array::<T>(old_capacity).map_err(|_overflow| Refused::Overflow)?;
                    // SAFETY: `old` is a block of `self.alloc` with
                    // `old_layout`, and `layout` is larger, with the same
                    // alignment.
                    unsafe { self.alloc.grow(old.cast(), old_layout, layout) }
                        .map_err(|_refusal| Refused::Allocator(layout))?
                }
            },
            Live::Inline => {
                let block = self
                    .alloc
                    .allocate(layout)
                    .map_err(|_refusal| Refused::Allocator(layout))?;
                // SAFETY: the inline array holds `len` items, the new block
                // holds room for `grown` items, more than `len`, and the two
                // do not overlap.
                unsafe {
                    ptr::copy_nonoverlapping(self.as_ptr(), block.cast::<T>().as_ptr(), len);
                }
                block
            },
        };
        self.raw = Raw {
            heap: (block.cast(), grown),
        };
        self.tagged = len | SPILLED;
        Ok(())
    }

    /// Gives the spare room of the block back to the allocator, as
    /// `Vec::shrink_to_fit` does. A vector whose items fit in place moves them
    /// back in place, and its block returns.
    ///
    /// # Specification
    /// - ensures: the items stay in their order. The capacity is `N` when the
    ///   length is at most `N`, and the length otherwise. A vector of
    ///   zero-sized items stays as it is.
    /// - panics: none; the allocator's refusal goes to its error handler.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the model test shrinks vectors in place and spilled,
    ///   and Miri reports a leak or a double free of the block.
    /// - witness: `tests::small_vec::each_operation_agrees_with_a_vec`
    #[spec(
        captures: before = self.count(),
        ensures: self.count() == before
            && (size_of::<T>() == 0 || self.capacity().0 == before.0.max(N)),
    )]
    #[inline]
    pub fn shrink_to_fit(&mut self)
    {
        if size_of::<T>() == 0 || self.live() == Live::Inline {
            return;
        }
        // SAFETY: the tag names the pair live.
        let (block, capacity) = unsafe { self.raw.heap };
        let len = self.count().0;
        if (len > N || Self::BLOCK_ONLY) && len == capacity {
            return;
        }
        let Ok(held) = Layout::array::<T>(capacity)
        else {
            Refused::Overflow.raise()
        };
        if len <= N && Self::BLOCK_ONLY {
            self.raw = Raw {
                heap: (NonNull::dangling(), 0),
            };
            // SAFETY: `block` is a block of `self.alloc` with `held`, since its
            // capacity is not zero, and it holds no item. The dangling pair
            // names it no more, so it returns once.
            unsafe {
                self.alloc.deallocate(block.cast(), held);
            }
            return;
        }
        if len <= N {
            let mut inline = MaybeUninit::<[T; N]>::uninit();
            // SAFETY: the first `len` slots of the block hold the items, the
            // array holds room for `N` items, at least `len`, and the two do
            // not overlap.
            unsafe {
                ptr::copy_nonoverlapping(block.as_ptr(), inline.as_mut_ptr().cast::<T>(), len);
            }
            self.raw = Raw {
                inline: ManuallyDrop::new(inline),
            };
            self.tagged = len;
            // SAFETY: `block` is a block of `self.alloc` with `held`, its items
            // moved out, and the cleared tag names it no more, so it returns
            // once.
            unsafe {
                self.alloc.deallocate(block.cast(), held);
            }
            return;
        }
        let Ok(kept) = Layout::array::<T>(len)
        else {
            Refused::Overflow.raise()
        };
        // SAFETY: `block` is a block of `self.alloc` with `held`, and `kept` is
        // smaller, with the same alignment.
        match unsafe { self.alloc.shrink(block.cast(), held, kept) } {
            Ok(shrunk) => {
                self.raw = Raw {
                    heap: (shrunk.cast(), len),
                };
            },
            Err(_refusal) => handle_alloc_error(kept),
        }
    }

    /// Adds `item` past the last item.
    ///
    /// # Specification
    /// - ensures: the length grows by one, and the last item is `item`.
    /// - panics: when the length passes `isize::MAX`; the allocator's refusal
    ///   goes to its error handler.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — pushes at `N` of 0, 1, 4 and 8 read back in order
    ///   across the spill, and the model test pushes before each check.
    /// - witness: `tests::small_vec::each_operation_agrees_with_a_vec`
    /// - witness: `tests::small_vec::a_vector_holds_its_items_in_place_up_to_n_and_in_one_block_past_it`
    #[spec(captures: before = self.count(), ensures: self.count().0 == before.0.saturating_add(1))]
    #[inline]
    pub fn push(
        &mut self,
        item: T,
    )
    {
        let len = self.count();
        if len == self.capacity() {
            self.grow_one();
        }
        // SAFETY: `len` is below the capacity, so the slot lies in the live
        // half's allocation.
        let slot = unsafe { self.as_mut_ptr().add(len.0) };
        // SAFETY: the slot holds no item, since the length does not count it.
        unsafe {
            slot.write(item);
        }
        self.set_len(Count(len.0.wrapping_add(1)));
    }

    /// Grows the vector by room for one item, the slow path of
    /// [`SmallVec::push`]. It stays out of line, so the fast path of a push
    /// inlines, as `Vec::push` keeps its grow apart.
    ///
    /// # Specification
    /// - ensures: the capacity passes the length.
    /// - panics: when the length passes `isize::MAX`; the allocator's refusal
    ///   goes to its error handler.
    #[cold]
    #[inline(never)]
    fn grow_one(&mut self)
    {
        if let Err(refused) = self.try_reserve(Count(1)) {
            refused.raise();
        }
    }

    /// Moves the item out of the slot past `at` items.
    ///
    /// # Safety
    /// - unsafe invariants: the slot lies in the live half and holds an item
    ///   that no owner reads again, since the length or the iterator counts it
    ///   no more.
    ///
    /// # Specification
    /// - ensures: the item of the slot; a zero-sized item comes from no
    ///   storage.
    /// - panics: none.
    /// - executable: none — the slot's state is no value that a predicate
    ///   reads.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each item that `pop`, a drain and an iterator yield
    ///   drops once, which Miri checks.
    /// - witness: `tests::small_vec::an_item_whose_drop_panics_leaves_each_other_item_dropped_once`
    /// - witness: `tests::small_vec::a_zero_sized_item_takes_no_storage`
    #[inline]
    unsafe fn take(
        &mut self,
        at: Count,
    ) -> T
    {
        if size_of::<T>() == 0 {
            // SAFETY: `T` is zero-sized, and the slot held one, which moves out
            // here, so the item that this conjures is that one.
            return unsafe { conjure_zst::<T>() };
        }
        // SAFETY: the slot lies in the live half, as the caller states, so the
        // offset stays in its allocation.
        let slot = unsafe { self.as_mut_ptr().add(at.0) };
        // SAFETY: the slot holds an item that no owner reads again.
        unsafe { slot.read() }
    }

    /// Removes the last item.
    ///
    /// # Specification
    /// - ensures: the last item, and the length one less; `None` on an empty
    ///   vector, which stays empty.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the model test pops after each kind of operation, and
    ///   the pop of the last item reads it.
    /// - witness: `tests::small_vec::each_operation_agrees_with_a_vec`
    #[spec(
        captures: before = self.count(),
        ensures: |ret| ret.is_some() == (before.0 > 0) && self.count().0 == before.0.saturating_sub(1),
    )]
    #[inline]
    pub fn pop(&mut self) -> Option<T>
    {
        let last = Count(self.count().0.checked_sub(1)?);
        self.set_len(last);
        // SAFETY: the slot past `last` items holds an item, and the length
        // counts it no more.
        Some(unsafe { self.take(last) })
    }

    /// Removes the last item when `predicate` answers `true` for it.
    ///
    /// # Specification
    /// - ensures: the last item, and the length one less, when the vector holds
    ///   an item and `predicate` answers `true` for it; `None` otherwise, and
    ///   the length does not change.
    /// - panics: when `predicate` panics; the vector keeps each item.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the model test pops the last item below a bound after
    ///   each kind of operation, against `Vec::pop_if`.
    /// - witness: `tests::small_vec::each_operation_agrees_with_a_vec`
    #[spec(
        captures: before = self.count(),
        ensures: |ret| self.count().0.checked_add(usize::from(ret.is_some())) == Some(before.0),
    )]
    #[inline]
    pub fn pop_if<F>(
        &mut self,
        predicate: F,
    ) -> Option<T>
    where
        F: FnOnce(&mut T) -> bool,
    {
        let last = self.as_mut_slice().last_mut()?;
        if predicate(last) { self.pop() } else { None }
    }

    /// Removes the item at `index`, and moves the last item into its place.
    ///
    /// # Specification
    /// - ensures: the item that stood at `index`, and the length one less; the
    ///   item that stood last stands at `index` when `index` is not the last.
    /// - panics: when `index` is not below the length.
    ///
    /// # Panics
    /// When `index` is not below the length, as `Vec::swap_remove` panics.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the model test removes an item at each index in range
    ///   after each kind of operation, against `Vec::swap_remove`.
    /// - witness: `tests::small_vec::each_operation_agrees_with_a_vec`
    #[spec(captures: before = self.count(), ensures: self.count().0.checked_add(1) == Some(before.0))]
    #[inline]
    pub fn swap_remove(
        &mut self,
        index: Count,
    ) -> T
    {
        let len = self.count().0;
        assert!(
            index.0 < len,
            "the index {} of `swap_remove` is not below the length {len}",
            index.0
        );
        let last = Count(len.wrapping_sub(1));
        self.as_mut_slice().swap(index.0, last.0);
        self.set_len(last);
        // SAFETY: the slot past `last` items holds an item, and the length
        // counts it no more.
        unsafe { self.take(last) }
    }

    /// Removes the item at `index`, and moves each item past it down by one.
    ///
    /// # Specification
    /// - ensures: the item that stood at `index`, and the length one less; the
    ///   other items keep their order.
    /// - panics: when `index` is not below the length.
    /// - intension: one move of each item past `index`.
    ///
    /// # Panics
    /// When `index` is not below the length, as `Vec::remove` panics.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the model test removes an item at each index in range
    ///   after each kind of operation, against `Vec::remove`.
    /// - witness: `tests::small_vec::each_operation_agrees_with_a_vec`
    #[spec(captures: before = self.count(), ensures: self.count().0.checked_add(1) == Some(before.0))]
    #[inline]
    pub fn remove(
        &mut self,
        index: Count,
    ) -> T
    {
        let len = self.count().0;
        assert!(
            index.0 < len,
            "the index {} of `remove` is not below the length {len}",
            index.0
        );
        let last = Count(len.wrapping_sub(1));
        if let Some(tail) = self.as_mut_slice().get_mut(index.0 ..) {
            tail.rotate_left(1);
        }
        self.set_len(last);
        // SAFETY: the slot past `last` items holds the item that stood at
        // `index`, and the length counts it no more.
        unsafe { self.take(last) }
    }

    /// Drops each item past the first `len`.
    ///
    /// # Specification
    /// - ensures: the length is the smaller of `len` and the length before, and
    ///   each item past it drops once.
    /// - panics: when an item's drop panics; each other item past `len` drops
    ///   first, and the vector holds the first `len`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the model test truncates to lengths below, at and
    ///   past the length, and a panic in an item's drop drops each other item
    ///   once.
    /// - witness: `tests::small_vec::each_operation_agrees_with_a_vec`
    /// - witness: `tests::small_vec::an_item_whose_drop_panics_leaves_each_other_item_dropped_once`
    #[spec(captures: before = self.count(), ensures: self.count() == before.min(len))]
    #[inline]
    pub fn truncate(
        &mut self,
        len: Count,
    )
    {
        let old = self.count();
        if len >= old {
            return;
        }
        self.set_len(len);
        let tail = ptr::slice_from_raw_parts_mut(
            self.as_mut_ptr().wrapping_add(len.0),
            old.0.wrapping_sub(len.0),
        );
        // SAFETY: the slots from `len` to `old` hold items, and the length
        // counts them no more, so each drops once.
        unsafe {
            ptr::drop_in_place(tail);
        }
    }

    /// Drops each item.
    ///
    /// # Specification
    /// - ensures: the vector is empty, and keeps its block.
    /// - panics: as [`SmallVec::truncate`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the model test clears the vector in place and
    ///   spilled.
    /// - witness: `tests::small_vec::each_operation_agrees_with_a_vec`
    #[spec(captures: had = self.capacity(), ensures: self.count() == Count(0) && self.capacity() == had)]
    #[inline]
    pub fn clear(&mut self)
    {
        self.truncate(Count(0));
    }

    /// Keeps the items for which `keep` answers `true`, in their order, and
    /// drops the others.
    ///
    /// The vector moves each kept item down by a swap, and then truncates.
    /// So `keep` reads each item once, in order, and the dropped items drop
    /// after the last read, not in their order.
    ///
    /// # Specification
    /// - ensures: the vector holds the items that `keep` kept, in their order,
    ///   and each other item drops once.
    /// - panics: when `keep` panics, or an item's drop panics. A panic in
    ///   `keep` leaves each item in the vector, in some order.
    /// - intension: one read of each item and at most one swap of each.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the model test keeps the items below a bound, in
    ///   place and spilled, against `Vec::retain`.
    /// - witness: `tests::small_vec::each_operation_agrees_with_a_vec`
    #[spec(captures: before = self.count(), ensures: self.count() <= before)]
    #[inline]
    pub fn retain<F>(
        &mut self,
        mut keep: F,
    ) where
        F: FnMut(&T) -> bool,
    {
        let items = self.as_mut_slice();
        let mut kept = 0_usize;
        for index in 0 .. items.len() {
            if items.get(index).is_some_and(&mut keep) {
                items.swap(kept, index);
                kept = kept.saturating_add(1);
            }
        }
        self.truncate(Count(kept));
    }

    /// Removes the items of `range`, and yields them in order. When the
    /// drain drops, the items past the range move down to close the gap.
    ///
    /// # Specification
    /// - ensures: the drain yields the items of `range`; once it drops, the
    ///   vector holds the items before `range` and then the items past it.
    /// - panics: when `range` lies outside the vector.
    /// - executable: none — the vector's state lands when the drain drops, past
    ///   this call.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the model test drains ranges in place and spilled,
    ///   and a drain that yields part of its range closes the gap.
    /// - witness: `tests::small_vec::each_operation_agrees_with_a_vec`
    /// - witness: `tests::small_vec::a_drain_yields_its_range_and_closes_the_gap`
    #[inline]
    pub fn drain<R>(
        &mut self,
        range: R,
    ) -> Drain<'_, T, N, A>
    where
        R: RangeBounds<usize>,
    {
        let len = self.count();
        let (start, end) = bounds(&range, len);
        self.set_len(start);
        Drain {
            vec: self,
            next: start.0,
            end: end.0,
            back: end.0,
            tail_len: len.0.wrapping_sub(end.0),
        }
    }

    /// Puts `item` at `index`, and moves each item from `index` on up by one.
    ///
    /// # Specification
    /// - ensures: the length grows by one; `item` stands at `index`, and the
    ///   other items keep their order.
    /// - panics: when `index` is past the length, or the length passes
    ///   `isize::MAX`; the allocator's refusal goes to its error handler.
    /// - intension: one move of each item from `index` on.
    ///
    /// # Panics
    /// When `index` is past the length, as `Vec::insert` panics.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the model test inserts at each index up to the
    ///   length, in place and spilled, against `Vec::insert`.
    /// - witness: `tests::small_vec::each_operation_agrees_with_a_vec`
    #[spec(captures: before = self.count(), ensures: self.count().0 == before.0.saturating_add(1))]
    #[inline]
    pub fn insert(
        &mut self,
        index: Count,
        item: T,
    )
    {
        let len = self.count().0;
        assert!(
            index.0 <= len,
            "the index {} of `insert` is past the length {len}",
            index.0
        );
        self.push(item);
        if let Some(tail) = self.as_mut_slice().get_mut(index.0 ..) {
            tail.rotate_right(1);
        }
    }

    /// Adds a clone of each item of `items` past the last item, in order.
    ///
    /// # Specification
    /// - ensures: the length grows by the length of `items`, and the last items
    ///   are clones of `items`, in order.
    /// - panics: when a clone panics, or the length passes `isize::MAX`; the
    ///   allocator's refusal goes to its error handler.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the model test extends by a slice, in place and
    ///   spilled, against `Vec::extend_from_slice`.
    /// - witness: `tests::small_vec::each_operation_agrees_with_a_vec`
    #[spec(captures: before = self.count(), ensures: self.count().0 == before.0.saturating_add(items.len()))]
    #[inline]
    pub fn extend_from_slice(
        &mut self,
        items: &[T],
    ) where
        T: Clone,
    {
        self.extend(items.iter().cloned());
    }

    /// Sets the length to `len`: drops the items past `len`, or adds clones
    /// of `value` past the last item until the length is `len`.
    ///
    /// # Specification
    /// - ensures: the length is `len`; the items before the old length stay,
    ///   and each item past it is a clone of `value`.
    /// - panics: when a clone or an item's drop panics, or the length passes
    ///   `isize::MAX`; the allocator's refusal goes to its error handler.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the model test resizes to lengths below and past the
    ///   length, in place and spilled, against `Vec::resize`.
    /// - witness: `tests::small_vec::each_operation_agrees_with_a_vec`
    #[spec(ensures: self.count() == len)]
    #[inline]
    pub fn resize(
        &mut self,
        len: Count,
        value: T,
    ) where
        T: Clone,
    {
        let had = self.count().0;
        if len.0 <= had {
            self.truncate(len);
        }
        else {
            self.extend(core::iter::repeat_n(value, len.0.wrapping_sub(had)));
        }
    }

    /// Replaces the items of `range` with the items of `items`, in order, and
    /// drops the items of `range`.
    ///
    /// The vector drains the range, adds the new items past the last item, and
    /// then rotates them into place before the items past the range.
    ///
    /// # Specification
    /// - ensures: the vector holds the items before `range`, then the items of
    ///   `items`, then the items past `range`.
    /// - panics: when `range` lies outside the vector, the iterator or an
    ///   item's drop panics, or the length passes `isize::MAX`.
    /// - intension: one move of each item past `range` to close the gap, and
    ///   one rotation of the items from the start of `range`.
    /// - executable: none — the predicate reads the items of an iterator that
    ///   the call consumes.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the model test replaces ranges by runs of each
    ///   length, in place and spilled, against `Vec::splice`.
    /// - witness: `tests::small_vec::each_operation_agrees_with_a_vec`
    #[inline]
    pub fn replace_range<R, I>(
        &mut self,
        range: R,
        items: I,
    ) where
        R: RangeBounds<usize>,
        I: IntoIterator<Item = T>,
    {
        let (start, end) = bounds(&range, self.count());
        drop(self.drain(start.0 .. end.0));
        let tail = self.count().0.wrapping_sub(start.0);
        self.extend(items);
        if let Some(moved) = self.as_mut_slice().get_mut(start.0 ..) {
            moved.rotate_left(tail);
        }
    }

    /// Splits the vector at `at`: the vector keeps the items before `at`, and
    /// a new vector over a clone of its allocator holds the rest, in order.
    ///
    /// # Specification
    /// - ensures: the length is `at`, and the new vector holds the items that
    ///   stood from `at` on, in order.
    /// - panics: when `at` is past the length; the allocator's refusal goes to
    ///   its error handler.
    /// - intension: one move of each item from `at` on.
    ///
    /// # Panics
    /// When `at` is past the length, as `Vec::split_off` panics.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the model test splits at each index up to the length,
    ///   in place and spilled, against `Vec::split_off`.
    /// - witness: `tests::small_vec::each_operation_agrees_with_a_vec`
    #[spec(captures: before = self.count(),
        ensures: |ret| self.count() == at && ret.count().0.saturating_add(at.0) == before.0)]
    #[inline]
    #[must_use]
    pub fn split_off(
        &mut self,
        at: Count,
    ) -> Self
    where
        A: Clone,
    {
        let len = self.count().0;
        assert!(
            at.0 <= len,
            "the index {} of `split_off` is past the length {len}",
            at.0
        );
        let mut rest = Self::with_capacity_in(Count(len.wrapping_sub(at.0)), self.alloc.clone());
        rest.extend(self.drain(at.0 ..));
        rest
    }

    /// Moves each item of `other` past the last item, in order, and leaves
    /// `other` empty.
    ///
    /// # Specification
    /// - ensures: the length grows by the length of `other`, and `other` is
    ///   empty.
    /// - panics: when the length passes `isize::MAX`; the allocator's refusal
    ///   goes to its error handler.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the model test appends runs of each length, in place
    ///   and spilled, against `Vec::append`.
    /// - witness: `tests::small_vec::each_operation_agrees_with_a_vec`
    #[spec(captures: [before = self.count(), moved = other.count()],
        ensures: self.count().0 == before.0.saturating_add(moved.0) && other.count() == Count(0))]
    #[inline]
    pub fn append<const M: usize, B>(
        &mut self,
        other: &mut SmallVec<T, M, B>,
    ) where
        B: Allocator,
    {
        self.extend(other.drain(..));
    }

    /// Drops each item that equals the item kept before it, so each run of
    /// equal items keeps its first.
    ///
    /// The vector moves each kept item down by a swap, and then truncates, as
    /// [`SmallVec::retain`] does.
    ///
    /// # Specification
    /// - ensures: no two neighbouring items are equal, and the items keep their
    ///   order.
    /// - panics: when a comparison or an item's drop panics. A panic in a
    ///   comparison leaves each item in the vector, in some order.
    /// - intension: one comparison of each item and at most one swap of each.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the model test drops runs of equal items, in place
    ///   and spilled, against `Vec::dedup`.
    /// - witness: `tests::small_vec::each_operation_agrees_with_a_vec`
    #[spec(captures: before = self.count(), ensures: self.count() <= before)]
    #[inline]
    pub fn dedup(&mut self)
    where
        T: PartialEq,
    {
        let items = self.as_mut_slice();
        let mut kept = 0_usize;
        for index in 0 .. items.len() {
            let fresh = kept == 0 || items.get(kept.wrapping_sub(1)) != items.get(index);
            if fresh {
                items.swap(kept, index);
                kept = kept.saturating_add(1);
            }
        }
        self.truncate(Count(kept));
    }

    /// The items as a boxed slice over the vector's allocator.
    ///
    /// A vector whose block holds its items hands the block to the box, shrunk
    /// to the length, as `Vec::into_boxed_slice` does. A vector in place, or an
    /// empty one, gives its items to a new box.
    ///
    /// # Specification
    /// - ensures: the box holds the items, in order.
    /// - panics: none; the allocator's refusal goes to its error handler.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the model test boxes its final items, in place and
    ///   spilled, and Miri reports a leak or a double free of the block.
    /// - witness: `tests::small_vec::each_operation_agrees_with_a_vec`
    #[spec(captures: before = self.count(), ensures: |ret| ret.len() == before.0)]
    #[inline]
    #[must_use]
    pub fn into_boxed_slice(self) -> Box<[T], A>
    {
        let vec = ManuallyDrop::new(self);
        let len = vec.count().0;
        // SAFETY: `vec` never drops, so its allocator moves out once.
        let alloc = unsafe { ptr::read(&raw const vec.alloc) };
        let Ok(kept) = Layout::array::<T>(len)
        else {
            Refused::Overflow.raise()
        };
        if vec.live() == Live::Block {
            // SAFETY: the tag names the pair live.
            let (block, capacity) = unsafe { vec.raw.heap };
            let Ok(held) = Layout::array::<T>(capacity)
            else {
                Refused::Overflow.raise()
            };
            if len > 0 {
                let block = if capacity == len {
                    block
                }
                else {
                    // SAFETY: `block` is a block of `alloc` with `held`, and
                    // `kept` is no larger, with the same alignment.
                    match unsafe { alloc.shrink(block.cast(), held, kept) } {
                        Ok(shrunk) => shrunk.cast(),
                        Err(_refusal) => handle_alloc_error(kept),
                    }
                };
                // SAFETY: `block` is a block of `alloc` with the array layout
                // of `len` items, which the first `len` slots hold, and `vec`
                // names it no more, so the box owns it.
                return unsafe {
                    Box::from_raw_in(ptr::slice_from_raw_parts_mut(block.as_ptr(), len), alloc)
                };
            }
            if capacity > 0 {
                // SAFETY: `block` is a block of `alloc` with `held`, since its
                // capacity is not zero, and it holds no item. `vec` names it
                // no more, so it returns once.
                unsafe {
                    alloc.deallocate(block.cast(), held);
                }
            }
        }
        let block: NonNull<T> = if kept.size() == 0 {
            NonNull::dangling()
        }
        else {
            match alloc.allocate(kept) {
                Ok(block) => block.cast(),
                Err(_refusal) => handle_alloc_error(kept),
            }
        };
        if vec.live() == Live::Inline {
            // SAFETY: the inline array holds `len` items, `block` holds room
            // for `len`, the two do not overlap, and `vec` never drops its
            // items, so each moves once.
            unsafe {
                ptr::copy_nonoverlapping(vec.as_ptr(), block.as_ptr(), len);
            }
        }
        // SAFETY: `block` is a block of `alloc` with the array layout of `len`
        // items, or a dangling pointer for a layout of no bytes, which a box
        // never returns; its first `len` slots hold the items.
        unsafe { Box::from_raw_in(ptr::slice_from_raw_parts_mut(block.as_ptr(), len), alloc) }
    }

    /// Gives the block back to the allocator if the vector holds one, and
    /// leaves the vector empty and in place.
    ///
    /// # Specification
    /// - ensures: the vector is empty and in place, and its block returns to
    ///   the allocator once.
    /// - panics: none.
    /// - executable: none — a returned block is no value that a predicate
    ///   reads.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — Miri reports a leak of a block that the drop keeps,
    ///   and a double free of one that it returns twice.
    /// - witness: `tests::small_vec::an_item_whose_drop_panics_leaves_each_other_item_dropped_once`
    #[inline]
    fn release(&mut self)
    {
        if self.live() == Live::Block {
            // SAFETY: the tag names the pair live.
            let (block, capacity) = unsafe { self.raw.heap };
            if Self::BLOCK_ONLY {
                self.raw = Raw {
                    heap: (NonNull::dangling(), 0),
                };
                self.tagged = SPILLED;
            }
            else {
                self.tagged = 0;
            }
            if capacity > 0
                && let Ok(layout) = Layout::array::<T>(capacity)
            {
                // SAFETY: `block` is a block of `self.alloc` with `layout`,
                // since its capacity is not zero. The cleared tag or the
                // dangling pair names it no more, so it returns once.
                unsafe {
                    self.alloc.deallocate(block.cast(), layout);
                }
            }
        }
    }
}

/// The start and the end of `range` in a vector of `len` items.
///
/// # Specification
/// - ensures: the start is at most the end, and the end is at most `len`.
/// - panics: when `range` lies outside the vector.
///
/// # Adequacy
/// - hypothesis: L3 — the model test drains bounded, half-open and full ranges.
/// - witness: `tests::small_vec::each_operation_agrees_with_a_vec`
#[spec(ensures: |ret| ret.0 <= ret.1 && ret.1 <= len)]
#[expect(
    clippy::panic,
    reason = "a range outside the vector is the caller's defect, and it panics as `Vec::drain` does"
)]
fn bounds<R>(
    range: &R,
    len: Count,
) -> (Count, Count)
where
    R: RangeBounds<usize>,
{
    let start = match range.start_bound() {
        Bound::Included(&start) => Some(start),
        Bound::Excluded(&start) => start.checked_add(1),
        Bound::Unbounded => Some(0),
    };
    let end = match range.end_bound() {
        Bound::Included(&end) => end.checked_add(1),
        Bound::Excluded(&end) => Some(end),
        Bound::Unbounded => Some(len.0),
    };
    if let (Some(start), Some(end)) = (start, end)
        && start <= end
        && end <= len.0
    {
        return (Count(start), Count(end));
    }
    panic!("the range lies outside the small vector");
}

impl<T, const N: usize, A> Drop for SmallVec<T, N, A>
where
    A: Allocator,
{
    /// # Specification
    /// - ensures: each item drops once, and the block returns to the allocator
    ///   once, after the items and when an item's drop panics too.
    /// - panics: when an item's drop panics; each other item drops first.
    /// - executable: none — a dropped vector has no state that a predicate
    ///   could read.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — counted drops at `N` of 0, 1, 4 and 8, and a panic in
    ///   one item's drop, under Miri, which reports a leak and a double drop.
    /// - witness: `tests::small_vec::an_item_whose_drop_panics_leaves_each_other_item_dropped_once`
    #[inline]
    fn drop(&mut self)
    {
        let mut vec = DropGuard::new(self, Self::release);
        let len = vec.count().0;
        let items = ptr::slice_from_raw_parts_mut(vec.as_mut_ptr(), len);
        // SAFETY: the first `len` slots of the live half hold items, and the
        // vector ends here, so each drops once.
        unsafe {
            ptr::drop_in_place(items);
        }
    }
}

/// The items of a range, out of a vector. When it drops, the items past the
/// range move down to close the gap.
///
/// # Specification
/// - requires: the vector's length is the start of the range, and the slots
///   from `next` to `back` hold the items not yet yielded; the slots from
///   `back` to `end` hold none.
pub struct Drain<'vec, T, const N: usize, A>
where
    A: Allocator,
{
    /// The vector, whose length is the start of the range.
    vec: &'vec mut SmallVec<T, N, A>,
    /// The slot of the next item to yield.
    next: usize,
    /// The end of the range, where the items past it start.
    end: usize,
    /// The slot past the last item not yet yielded.
    back: usize,
    /// The items past the range.
    tail_len: usize,
}

impl<T, const N: usize, A> Drain<'_, T, N, A>
where
    A: Allocator,
{
    /// Moves the items past the range down to the vector's length, and counts
    /// them.
    ///
    /// # Specification
    /// - ensures: the vector's length grows by the items past the range.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a drain of a middle range leaves the items past it in
    ///   order, in place and spilled.
    /// - witness: `tests::small_vec::a_drain_yields_its_range_and_closes_the_gap`
    #[spec(captures: start = self.vec.count(), ensures: self.vec.count().0 == start.0.saturating_add(self.tail_len))]
    #[inline]
    fn close(&mut self)
    {
        let start = self.vec.count().0;
        if self.tail_len > 0 && self.end != start {
            let base = self.vec.as_mut_ptr();
            // SAFETY: the items past the range lie in the live half from the
            // range's end, and their new place lies in it from the vector's
            // length; `ptr::copy` admits the overlap.
            unsafe {
                ptr::copy(
                    base.wrapping_add(self.end),
                    base.wrapping_add(start),
                    self.tail_len,
                );
            }
        }
        self.vec.set_len(Count(start.wrapping_add(self.tail_len)));
    }

    /// The items that the drain has not yet yielded, in order.
    ///
    /// # Specification
    /// - ensures: the slice holds the items from `next` to the end of the
    ///   range.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the model test reads a drain's items before it yields
    ///   them, against the model's range.
    /// - witness: `tests::small_vec::each_operation_agrees_with_a_vec`
    #[spec(ensures: |ret| ret.len() == self.back.wrapping_sub(self.next))]
    #[inline]
    #[must_use]
    pub fn as_slice(&self) -> &[T]
    {
        // SAFETY: the slots from `next` to `back` of the live half hold the
        // items not yet yielded, and the borrow of `self` keeps them.
        unsafe {
            slice::from_raw_parts(
                self.vec.as_ptr().wrapping_add(self.next),
                self.back.wrapping_sub(self.next),
            )
        }
    }
}

impl<T, const N: usize, A> Iterator for Drain<'_, T, N, A>
where
    A: Allocator,
{
    type Item = T;

    /// # Specification
    /// - ensures: the next item of the range, or `None` at its end.
    /// - panics: none.
    /// - executable: none — the slot's state is no value that a predicate
    ///   reads.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a drain yields the items of its range in order.
    /// - witness: `tests::small_vec::a_drain_yields_its_range_and_closes_the_gap`
    #[inline]
    fn next(&mut self) -> Option<T>
    {
        if self.next == self.back {
            return None;
        }
        let at = self.next;
        self.next = at.wrapping_add(1);
        // SAFETY: the slot past `at` items lies between the vector's length
        // and the range's end, holds an item, and the drain passes it, so it
        // moves out once.
        Some(unsafe { self.vec.take(Count(at)) })
    }

    /// # Specification
    /// trivial.
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>)
    {
        let left = self.back.wrapping_sub(self.next);
        (left, Some(left))
    }
}

impl<T, const N: usize, A> DoubleEndedIterator for Drain<'_, T, N, A>
where
    A: Allocator,
{
    /// # Specification
    /// - ensures: the last item of the range not yet yielded, or `None` once
    ///   each is.
    /// - panics: none.
    /// - executable: none — the slot's state is no value that a predicate
    ///   reads.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the model test drains a range from its back, in place
    ///   and spilled, against `Vec::drain`.
    /// - witness: `tests::small_vec::each_operation_agrees_with_a_vec`
    #[inline]
    fn next_back(&mut self) -> Option<T>
    {
        if self.next == self.back {
            return None;
        }
        let at = self.back.wrapping_sub(1);
        self.back = at;
        // SAFETY: the slot past `at` items lies between the vector's length
        // and the range's end, holds an item, and the drain passes it, so it
        // moves out once.
        Some(unsafe { self.vec.take(Count(at)) })
    }
}

impl<T, const N: usize, A> ExactSizeIterator for Drain<'_, T, N, A> where A: Allocator
{
}

impl<T, const N: usize, A> Drop for Drain<'_, T, N, A>
where
    A: Allocator,
{
    /// # Specification
    /// - ensures: each item not yet yielded drops once, and the items past the
    ///   range then close the gap, when an item's drop panics too.
    /// - panics: when an item's drop panics; each other item drops first.
    /// - executable: none — a dropped drain has no state that a predicate could
    ///   read.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a drain that yields part of its range drops the rest
    ///   and closes the gap, and a panic in one item's drop drops each other
    ///   item once.
    /// - witness: `tests::small_vec::a_drain_yields_its_range_and_closes_the_gap`
    /// - witness: `tests::small_vec::an_item_whose_drop_panics_leaves_each_other_item_dropped_once`
    #[inline]
    fn drop(&mut self)
    {
        let mut drain = DropGuard::new(self, Self::close);
        let rest = ptr::slice_from_raw_parts_mut(
            drain.vec.as_mut_ptr().wrapping_add(drain.next),
            drain.back.wrapping_sub(drain.next),
        );
        drain.next = drain.back;
        // SAFETY: the slots of `rest` hold the items that the drain did not
        // yield, and the drain passes them now, so each drops once.
        unsafe {
            ptr::drop_in_place(rest);
        }
    }
}

/// The items of a vector, by value, in order.
///
/// # Specification
/// - requires: the vector's length is zero, and the slots from `next` to `end`
///   hold the items not yet yielded.
pub struct IntoIter<T, const N: usize, A>
where
    A: Allocator,
{
    /// The vector, with its length at zero: its drop returns the block alone.
    vec: SmallVec<T, N, A>,
    /// The slot of the next item to yield.
    next: usize,
    /// The end of the items.
    end: usize,
}

impl<T, const N: usize, A> Iterator for IntoIter<T, N, A>
where
    A: Allocator,
{
    type Item = T;

    /// # Specification
    /// - ensures: the next item, or `None` past the last.
    /// - panics: none.
    /// - executable: none — the slot's state is no value that a predicate
    ///   reads.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the model test collects the items by value and
    ///   compares them with a `Vec`'s.
    /// - witness: `tests::small_vec::each_operation_agrees_with_a_vec`
    #[inline]
    fn next(&mut self) -> Option<T>
    {
        if self.next == self.end {
            return None;
        }
        let at = self.next;
        self.next = at.wrapping_add(1);
        // SAFETY: the slot past `at` items lies below the items' end, holds an
        // item, and the iterator passes it, so it moves out once.
        Some(unsafe { self.vec.take(Count(at)) })
    }

    /// # Specification
    /// trivial.
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>)
    {
        let left = self.end.wrapping_sub(self.next);
        (left, Some(left))
    }
}

impl<T, const N: usize, A> DoubleEndedIterator for IntoIter<T, N, A>
where
    A: Allocator,
{
    /// # Specification
    /// - ensures: the last item not yet yielded, or `None` once each is.
    /// - panics: none.
    /// - executable: none — the slot's state is no value that a predicate
    ///   reads.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the model test takes the items by value from the
    ///   back, against a `Vec`'s.
    /// - witness: `tests::small_vec::each_operation_agrees_with_a_vec`
    #[inline]
    fn next_back(&mut self) -> Option<T>
    {
        if self.next == self.end {
            return None;
        }
        let at = self.end.wrapping_sub(1);
        self.end = at;
        // SAFETY: the slot past `at` items lies below the items' end, holds an
        // item, and the iterator passes it, so it moves out once.
        Some(unsafe { self.vec.take(Count(at)) })
    }
}

impl<T, const N: usize, A> ExactSizeIterator for IntoIter<T, N, A> where A: Allocator
{
}

impl<T, const N: usize, A> Drop for IntoIter<T, N, A>
where
    A: Allocator,
{
    /// # Specification
    /// - ensures: each item not yet yielded drops once; the vector then returns
    ///   its block, when an item's drop panics too.
    /// - panics: when an item's drop panics; each other item drops first.
    /// - executable: none — a dropped iterator has no state that a predicate
    ///   could read.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an iterator dropped part way drops the rest, and a
    ///   panic in one item's drop drops each other item once and returns the
    ///   block, under Miri.
    /// - witness: `tests::small_vec::an_item_whose_drop_panics_leaves_each_other_item_dropped_once`
    #[inline]
    fn drop(&mut self)
    {
        let rest = ptr::slice_from_raw_parts_mut(
            self.vec.as_mut_ptr().wrapping_add(self.next),
            self.end.wrapping_sub(self.next),
        );
        self.next = self.end;
        // SAFETY: the slots of `rest` hold the items that the iterator did not
        // yield, and the iterator passes them now, so each drops once.
        unsafe {
            ptr::drop_in_place(rest);
        }
    }
}

impl<T, const N: usize, A> IntoIterator for SmallVec<T, N, A>
where
    A: Allocator,
{
    type IntoIter = IntoIter<T, N, A>;
    type Item = T;

    /// # Specification
    /// trivial.
    #[inline]
    fn into_iter(mut self) -> IntoIter<T, N, A>
    {
        let end = self.count().0;
        self.set_len(Count(0));
        IntoIter {
            vec: self,
            next: 0,
            end,
        }
    }
}

impl<'vec, T, const N: usize, A> IntoIterator for &'vec SmallVec<T, N, A>
where
    A: Allocator,
{
    type IntoIter = slice::Iter<'vec, T>;
    type Item = &'vec T;

    /// # Specification
    /// trivial.
    #[inline]
    fn into_iter(self) -> slice::Iter<'vec, T>
    {
        self.as_slice().iter()
    }
}

impl<'vec, T, const N: usize, A> IntoIterator for &'vec mut SmallVec<T, N, A>
where
    A: Allocator,
{
    type IntoIter = slice::IterMut<'vec, T>;
    type Item = &'vec mut T;

    /// # Specification
    /// trivial.
    #[inline]
    fn into_iter(self) -> slice::IterMut<'vec, T>
    {
        self.as_mut_slice().iter_mut()
    }
}

impl<T, const N: usize, A> Deref for SmallVec<T, N, A>
where
    A: Allocator,
{
    type Target = [T];

    /// # Specification
    /// trivial.
    #[inline]
    fn deref(&self) -> &[T]
    {
        self.as_slice()
    }
}

impl<T, const N: usize, A> DerefMut for SmallVec<T, N, A>
where
    A: Allocator,
{
    /// # Specification
    /// trivial.
    #[inline]
    fn deref_mut(&mut self) -> &mut [T]
    {
        self.as_mut_slice()
    }
}

impl<'item, T, const N: usize, A> Extend<&'item T> for SmallVec<T, N, A>
where
    T: Copy + 'item,
    A: Allocator,
{
    /// Adds a copy of each item past the last item, in order, as `Vec`
    /// extends by references to `Copy` items.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn extend<I>(
        &mut self,
        iter: I,
    ) where
        I: IntoIterator<Item = &'item T>,
    {
        self.extend(iter.into_iter().copied());
    }
}

impl<T, const N: usize, A> Extend<T> for SmallVec<T, N, A>
where
    A: Allocator,
{
    /// # Specification
    /// - ensures: the items follow the vector's own, in order.
    /// - panics: as [`SmallVec::push`], and when the size hint passes
    ///   `isize::MAX`.
    /// - executable: none — the items are consumed, so no predicate reads them
    ///   after.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the model test extends the vector in place and across
    ///   the spill, and an extend whose size hint passes `isize::MAX` panics.
    /// - witness: `tests::small_vec::each_operation_agrees_with_a_vec`
    /// - witness: `tests::small_vec::a_grow_past_the_length_or_the_allocator_is_refused_and_the_vector_stays`
    #[inline]
    fn extend<I>(
        &mut self,
        iter: I,
    ) where
        I: IntoIterator<Item = T>,
    {
        let mut items = iter.into_iter();
        if let Err(refused) = self.try_reserve(Count(items.size_hint().0)) {
            refused.raise();
        }
        let capacity = self.capacity().0;
        let mut written = Written {
            len: self.count().0,
            vec: self,
        };
        let start = written.vec.as_mut_ptr();
        while written.len < capacity {
            let Some(item) = items.next()
            else {
                return;
            };
            // SAFETY: `written.len` is below the capacity, so the slot lies in
            // the live half, and it holds no item, since no length counts it.
            unsafe {
                start.add(written.len).write(item);
            }
            written.len = written.len.wrapping_add(1);
        }
        drop(written);
        items.for_each(|item| self.push(item));
    }
}

/// The length of a vector while an extend writes past it: the drop sets the
/// length, so the items written before an unwind drop once with the vector.
///
/// # Specification
/// - requires: the first `len` slots of the live half of `vec` hold items.
struct Written<'vec, T, const N: usize, A>
where
    A: Allocator,
{
    /// The vector that the extend writes.
    vec: &'vec mut SmallVec<T, N, A>,
    /// The items that its slots hold so far.
    len: usize,
}

impl<T, const N: usize, A> Drop for Written<'_, T, N, A>
where
    A: Allocator,
{
    /// Sets the vector's length to the items written.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn drop(&mut self)
    {
        self.vec.set_len(Count(self.len));
    }
}

impl<T, const N: usize, A> FromIterator<T> for SmallVec<T, N, A>
where
    A: Allocator + Default,
{
    /// # Specification
    /// trivial.
    #[inline]
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = T>,
    {
        let mut vec = Self::new_in(A::default());
        vec.extend(iter);
        vec
    }
}

impl<T, const N: usize, A> From<[T; N]> for SmallVec<T, N, A>
where
    A: Allocator + Default,
{
    /// The array, in place. The blanket `TryFrom` of this conversion has the
    /// never type as its error, so its caller matches `Ok` alone. At `N` of
    /// zero with items of a size, the empty array gives the empty vector, in
    /// its dangling block.
    ///
    /// # Specification
    /// - ensures: the vector holds the array's items in order, and draws no
    ///   block.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an array converts with no error arm and reads back in
    ///   place.
    /// - witness: `tests::small_vec::an_array_converts_with_no_error_arm`
    #[spec(ensures: |ret| ret.count() == Count(N) && (Self::BLOCK_ONLY || ret.live() == Live::Inline))]
    #[inline]
    fn from(value: [T; N]) -> Self
    {
        let mut vec = Self::new_in(A::default());
        if Self::BLOCK_ONLY {
            return vec;
        }
        vec.raw = Raw {
            inline: ManuallyDrop::new(MaybeUninit::new(value)),
        };
        vec.tagged = N;
        vec
    }
}

impl<T, const N: usize, A> Clone for SmallVec<T, N, A>
where
    T: Clone,
    A: Allocator + Clone,
{
    /// # Specification
    /// - ensures: a vector of clones of the items, in order, over a clone of
    ///   the allocator.
    /// - panics: as [`SmallVec::push`], and when an item's clone panics.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the model test clones the vector in place and
    ///   spilled, and compares the clone with a `Vec`'s.
    /// - witness: `tests::small_vec::each_operation_agrees_with_a_vec`
    #[spec(ensures: |ret| ret.count() == self.count())]
    #[inline]
    fn clone(&self) -> Self
    {
        let mut copy = Self::with_capacity_in(self.count(), self.alloc.clone());
        copy.extend(self.iter().cloned());
        copy
    }
}

impl<T, const N: usize, A> From<SmallVec<T, N, A>> for Box<[T], A>
where
    A: Allocator,
{
    /// The items, as [`SmallVec::into_boxed_slice`] gives them.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(vec: SmallVec<T, N, A>) -> Self
    {
        vec.into_boxed_slice()
    }
}

impl<T, const N: usize, A> From<SmallVec<T, N, A>> for Vec<T, A>
where
    A: Allocator,
{
    /// The items as a vector over the same allocator.
    ///
    /// A vector whose block holds its items hands the block to the result
    /// with no copy, as `Vec::from(Box<[T]>)` does. A vector in place moves
    /// its items into a new block.
    ///
    /// # Specification
    /// - ensures: the result holds the items, in order.
    /// - panics: none; the allocator's refusal goes to its error handler.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the model test converts its final items, in place and
    ///   spilled, and Miri reports a leak or a double free of the block.
    /// - witness: `tests::small_vec::each_operation_agrees_with_a_vec`
    #[spec(captures: before = vec.count(), ensures: |ret| ret.len() == before.0)]
    #[inline]
    fn from(vec: SmallVec<T, N, A>) -> Self
    {
        let vec = ManuallyDrop::new(vec);
        let len = vec.count().0;
        // SAFETY: `vec` never drops, so its allocator moves out once.
        let alloc = unsafe { ptr::read(&raw const vec.alloc) };
        if vec.live() == Live::Block {
            // SAFETY: the tag names the pair live.
            let (block, capacity) = unsafe { vec.raw.heap };
            // SAFETY: `block` is a block of `alloc` with the array layout of
            // `capacity` items, its first `len` slots hold the items, and
            // `vec` names it no more, so the result owns it.
            return unsafe { Self::from_raw_parts_in(block.as_ptr(), len, capacity, alloc) };
        }
        let mut moved = Self::with_capacity_in(len, alloc);
        // SAFETY: the inline array holds `len` items, `moved` holds room for
        // `len`, the two do not overlap, and `vec` never drops its items, so
        // each moves once.
        unsafe {
            ptr::copy_nonoverlapping(vec.as_ptr(), moved.as_mut_ptr(), len);
        }
        // SAFETY: the copy above initializes the first `len` slots of `moved`.
        unsafe {
            moved.set_len(len);
        }
        moved
    }
}

impl<T, const N: usize, A> Default for SmallVec<T, N, A>
where
    A: Allocator + Default,
{
    /// # Specification
    /// trivial.
    #[inline]
    fn default() -> Self
    {
        Self::new_in(A::default())
    }
}

impl<T, const N: usize, A> fmt::Debug for SmallVec<T, N, A>
where
    T: fmt::Debug,
    A: Allocator,
{
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.debug_list().entries(self.iter()).finish()
    }
}

impl<T, U, const N: usize, const M: usize, A, B> PartialEq<SmallVec<U, M, B>> for SmallVec<T, N, A>
where
    T: PartialEq<U>,
    A: Allocator,
    B: Allocator,
{
    /// Two vectors are equal when their items are, in order, whatever their
    /// capacities, their allocators and where their items lie.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn eq(
        &self,
        other: &SmallVec<U, M, B>,
    ) -> bool
    {
        self.as_slice() == other.as_slice()
    }
}

impl<T, U, const N: usize, A> PartialEq<[U]> for SmallVec<T, N, A>
where
    T: PartialEq<U>,
    A: Allocator,
{
    /// A vector equals a slice of equal items in the same order, as a `Vec`
    /// does.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn eq(
        &self,
        other: &[U],
    ) -> bool
    {
        self.as_slice() == other
    }
}

impl<T, U, const N: usize, A> PartialEq<&[U]> for SmallVec<T, N, A>
where
    T: PartialEq<U>,
    A: Allocator,
{
    /// A vector equals a borrowed slice of equal items in the same order, as
    /// a `Vec` does.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn eq(
        &self,
        other: &&[U],
    ) -> bool
    {
        self.as_slice() == *other
    }
}

impl<T, U, const N: usize, const M: usize, A> PartialEq<[U; M]> for SmallVec<T, N, A>
where
    T: PartialEq<U>,
    A: Allocator,
{
    /// A vector equals an array of equal items in the same order, as a `Vec`
    /// does.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn eq(
        &self,
        other: &[U; M],
    ) -> bool
    {
        self.as_slice() == other
    }
}

impl<T, U, const N: usize, A> PartialEq<SmallVec<U, N, A>> for [T]
where
    T: PartialEq<U>,
    A: Allocator,
{
    /// A slice equals a vector of equal items in the same order, as it equals
    /// a `Vec`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn eq(
        &self,
        other: &SmallVec<U, N, A>,
    ) -> bool
    {
        self == other.as_slice()
    }
}

impl<T, U, const N: usize, A> PartialEq<SmallVec<U, N, A>> for &[T]
where
    T: PartialEq<U>,
    A: Allocator,
{
    /// A borrowed slice equals a vector of equal items in the same order, as
    /// it equals a `Vec`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn eq(
        &self,
        other: &SmallVec<U, N, A>,
    ) -> bool
    {
        *self == other.as_slice()
    }
}

impl<T, U, const N: usize, const M: usize, A> PartialEq<SmallVec<U, N, A>> for [T; M]
where
    T: PartialEq<U>,
    A: Allocator,
{
    /// An array equals a vector of equal items in the same order, as it
    /// equals a `Vec`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn eq(
        &self,
        other: &SmallVec<U, N, A>,
    ) -> bool
    {
        self == other.as_slice()
    }
}

impl<T, const N: usize, A> AsRef<[T]> for SmallVec<T, N, A>
where
    A: Allocator,
{
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &[T]
    {
        self.as_slice()
    }
}

impl<T, const N: usize, A> AsMut<[T]> for SmallVec<T, N, A>
where
    A: Allocator,
{
    /// # Specification
    /// trivial.
    #[inline]
    fn as_mut(&mut self) -> &mut [T]
    {
        self.as_mut_slice()
    }
}

impl<T, const N: usize, A> Borrow<[T]> for SmallVec<T, N, A>
where
    A: Allocator,
{
    /// The items, as a `Vec` lends them. The vector compares, orders and
    /// hashes as this slice does, as `Borrow` asks.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn borrow(&self) -> &[T]
    {
        self.as_slice()
    }
}

impl<T, const N: usize, A> BorrowMut<[T]> for SmallVec<T, N, A>
where
    A: Allocator,
{
    /// # Specification
    /// trivial.
    #[inline]
    fn borrow_mut(&mut self) -> &mut [T]
    {
        self.as_mut_slice()
    }
}

impl<T, const N: usize, A> Eq for SmallVec<T, N, A>
where
    T: Eq,
    A: Allocator,
{
}

impl<T, const N: usize, A> PartialOrd for SmallVec<T, N, A>
where
    T: PartialOrd,
    A: Allocator,
{
    /// The slices' lexicographic order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn partial_cmp(
        &self,
        other: &Self,
    ) -> Option<Ordering>
    {
        self.as_slice().partial_cmp(other.as_slice())
    }
}

impl<T, const N: usize, A> Ord for SmallVec<T, N, A>
where
    T: Ord,
    A: Allocator,
{
    /// The slices' lexicographic order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn cmp(
        &self,
        other: &Self,
    ) -> Ordering
    {
        self.as_slice().cmp(other.as_slice())
    }
}

impl<T, const N: usize, A> Hash for SmallVec<T, N, A>
where
    T: Hash,
    A: Allocator,
{
    /// A vector hashes as its slice does, so it hashes as a `Vec` of the same
    /// items.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn hash<H>(
        &self,
        state: &mut H,
    ) where
        H: Hasher,
    {
        self.as_slice().hash(state);
    }
}

/// # Safety
/// - unsafe invariants: a vector owns its items and its block, as `Vec` does,
///   so it moves to another thread where its items and its allocator move.
#[expect(
    clippy::non_send_fields_in_send_ty,
    reason = "the union's pointer is the vector's own block, which moves with it"
)]
// SAFETY: the vector shares no item and no block with another owner, so a
// move of it moves all of them.
unsafe impl<T, const N: usize, A> Send for SmallVec<T, N, A>
where
    T: Send,
    A: Allocator + Send,
{
}

/// # Safety
/// - unsafe invariants: a shared vector hands out shared borrows of its items
///   alone, as `Vec` does, so it is shared across threads where its items and
///   its allocator are.
// SAFETY: each method of a shared borrow reads the items and the tag, and
// writes neither.
unsafe impl<T, const N: usize, A> Sync for SmallVec<T, N, A>
where
    T: Sync,
    A: Allocator + Sync,
{
}
