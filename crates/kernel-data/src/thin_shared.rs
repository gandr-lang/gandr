//! The thin shared pointer, on `triomphe`'s `ThinArc` and `HeaderSlice`. A
//! [`ThinShared`] is one word. It points at one block of its allocator, which
//! holds the count of holders, the length, a header and the items. So a
//! holder of a slice is half the size of a fat pointer, and the header and
//! the items share one allocation.
//!
//! The count is the shared pointer's, with its orderings. The last holder
//! drops the header first, then the items, and then it returns the block. A
//! drop that panics leaves the rest to drop and the block to return.
//!
//! # Safety
//! - unsafe invariants: the pointer of a [`ThinShared`] names a block that its
//!   allocator gave with the layout that [`layout`] gives for the block's
//!   length, or the static empty block. The header is initialised, and the
//!   first `len` slots past the head hold items. The count equals the number of
//!   live holders, and the holder that takes it from one to zero frees the
//!   block, once. The static empty block is the one exception: its count holds
//!   one more than its live holders, so no holder takes it to zero, and no
//!   holder frees it.

use alloc::alloc::Global;
use core::alloc::Allocator;
use core::alloc::Layout;
use core::cmp::Ordering;
use core::fmt;
use core::hash::Hash;
use core::hash::Hasher;
use core::marker::PhantomData;
use core::mem::DropGuard;
use core::mem::align_of;
use core::mem::offset_of;
use core::ops::Deref;
use core::ptr;
use core::ptr::NonNull;
use core::slice;

use anodized::spec;

use crate::shared::Counter;
use crate::shared::Departure;
use crate::shared::Holding;
use crate::shared::Identity;
use crate::small_vec::Count;
use crate::small_vec::Refused;
use crate::small_vec::SmallVec;

/// The head of a thin block: the count, the length and the header. The items
/// follow it, at the offset of `items`.
///
/// # Specification
/// trivial.
#[repr(C)]
struct Head<H, T>
{
    /// The number of live holders.
    count: Counter,
    /// The number of items past the head.
    len: usize,
    /// The header.
    header: H,
    /// The place of the first item, with the items' alignment.
    items: [T; 0],
}

/// An item of the greatest alignment that the static empty block serves. A
/// head over any item has the count and the length where a head over it has
/// them. A head over an item of an alignment up to 16 places its items within
/// the static block or at its end, at an offset of that alignment.
///
/// # Specification
/// trivial.
#[repr(align(16))]
struct Aligned;

/// The block that each empty default over the global allocator shares, as
/// `std` shares one block for each empty `Arc` of a slice. Its count starts
/// at one, the block's own hold, which never leaves. So no holder takes the
/// count to zero, and no holder returns the block.
///
/// # Specification
/// trivial.
#[cfg(not(loom))]
static EMPTY: Head<(), Aligned> = Head {
    count: Counter::resident(),
    len: 0,
    header: (),
    items: [],
};

/// The layout of a thin block of `len` items.
///
/// # Specification
/// - ensures: the head, then `len` items from the offset of the head's `items`
///   field, padded to the head's alignment.
/// - fails: [`Refused::Overflow`] when the bytes pass `isize::MAX`.
/// - panics: none.
///
/// # Errors
/// - [`Refused::Overflow`]: the block's bytes pass `isize::MAX`.
///
/// # Adequacy
/// - hypothesis: L2 — a counting allocator reads the block's bytes for a header
///   and a slice, and a length past `isize::MAX` items is refused.
/// - witness: `tests::thin_shared::a_thin_block_holds_the_count_the_length_the_header_and_the_items`
#[spec(ensures: |ret| ret.is_err() || ret.is_ok_and(|whole| whole.align() >= align_of::<Head<H, T>>()))]
#[inline]
fn layout<H, T>(len: Count) -> Result<Layout, Refused>
{
    let Ok(items) = Layout::array::<T>(usize::from(len))
    else {
        return Err(Refused::Overflow);
    };
    let Some(size) = offset_of!(Head<H, T>, items).checked_add(items.size())
    else {
        return Err(Refused::Overflow);
    };
    let Ok(whole) = Layout::from_size_align(size, align_of::<Head<H, T>>())
    else {
        return Err(Refused::Overflow);
    };
    Ok(whole.pad_to_align())
}

/// The place of the first item of the block at `head`.
///
/// # Specification
/// - requires: `head` names a thin block.
/// - ensures: a pointer with the block's provenance, at the offset of the
///   head's `items` field.
/// - panics: none.
/// - executable: none — the pointer names memory that no safe predicate reads.
///
/// # Adequacy
/// - hypothesis: L2 — the items read back in order, under Miri with strict
///   provenance.
/// - witness: `tests::thin_shared::a_thin_block_holds_the_count_the_length_the_header_and_the_items`
#[inline]
const fn first<H, T>(head: NonNull<Head<H, T>>) -> *mut T
{
    // SAFETY: `head` names a thin block, so the field's place lies in it.
    unsafe { (&raw mut (*head.as_ptr()).items).cast::<T>() }
}

/// A thin block in the middle of its build: the header and `written` items
/// are in place. When it drops before the build ends, it drops them and
/// returns the block.
///
/// # Specification
/// - requires: `head` names a block that `alloc` gave with `layout`, with its
///   header and its first `written` items initialised.
struct Partial<'alloc, H, T, A>
where
    A: Allocator,
{
    /// The block.
    head: NonNull<Head<H, T>>,
    /// The number of items in place.
    written: usize,
    /// The layout that the block has.
    layout: Layout,
    /// The allocator that gave the block.
    alloc: &'alloc A,
}

impl<H, T, A> Partial<'_, H, T, A>
where
    A: Allocator,
{
    /// Drops the header and the items in place, and returns the block.
    ///
    /// # Specification
    /// - ensures: the header and each written item drop once, and the block
    ///   returns once, when a drop panics too.
    /// - panics: when a drop panics.
    /// - executable: none — the build ends, so no state stays to read.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an iterator that yields fewer items than its length
    ///   leaves each written item dropped and no block allocated, under Miri.
    /// - witness: `tests::thin_shared::an_iterator_short_of_its_length_panics_and_leaves_nothing`
    #[inline]
    fn abandon(self)
    {
        let free = DropGuard::new(self.head, |head| {
            // SAFETY: `alloc` gave the block with `layout`, and the drops
            // below end its use.
            unsafe {
                self.alloc.deallocate(head.cast(), self.layout);
            }
        });
        let items = DropGuard::new(
            ptr::slice_from_raw_parts_mut(first(self.head), self.written),
            |items| {
                // SAFETY: the first `written` slots hold items, which drop
                // once, here.
                unsafe {
                    ptr::drop_in_place(items);
                }
            },
        );
        let head = free.as_ptr();
        // SAFETY: the count's place lies in the live block.
        let count = unsafe { &raw mut (*head).count };
        // SAFETY: the count drops once, here.
        unsafe {
            ptr::drop_in_place(count);
        }
        // SAFETY: the header's place lies in the live block.
        let header = unsafe { &raw mut (*head).header };
        // SAFETY: the header drops once, here, before the items.
        unsafe {
            ptr::drop_in_place(header);
        }
        drop(items);
        drop(free);
    }
}

/// Ends a build whose iterator yields fewer items than its length.
///
/// # Specification
/// - ensures: the call does not return.
/// - panics: always, as `triomphe` does on an iterator that misreports its
///   length.
/// - executable: none — the function returns no value to read.
///
/// # Adequacy
/// - hypothesis: L2 — a short iterator panics, and the build leaves nothing.
/// - witness: `tests::thin_shared::an_iterator_short_of_its_length_panics_and_leaves_nothing`
#[expect(
    clippy::panic,
    reason = "an iterator that yields fewer items than its exact length breaks its own trait, and the build cannot fill the block"
)]
fn short() -> !
{
    panic!("the iterator of a thin shared block yields fewer items than its length");
}

/// Ends a collect whose iterator yields more items than its exact size hint.
///
/// # Specification
/// - ensures: the call does not return.
/// - panics: always, as [`short`] does on an iterator that misreports its
///   length.
/// - executable: none — the function returns no value to read.
///
/// # Adequacy
/// - hypothesis: L2 — an iterator past its exact size hint panics.
/// - witness: `tests::thin_shared::an_iterator_off_its_exact_hint_panics`
#[expect(
    clippy::panic,
    reason = "an iterator that yields more items than its exact size hint breaks its own trait, and the block has no room for them"
)]
fn long() -> !
{
    panic!("the iterator of a thin shared block yields more items than its exact size hint");
}

/// The iterator of a collect whose size hint is exact, with that hint as its
/// length.
///
/// # Specification
/// trivial.
struct Hinted<'iter, I>
{
    /// The iterator, which the collect reads again after the block is full.
    items: &'iter mut I,
    /// The exact size hint of the iterator.
    len: usize,
}

impl<I> Iterator for Hinted<'_, I>
where
    I: Iterator,
{
    type Item = I::Item;

    /// The next item of the iterator.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn next(&mut self) -> Option<I::Item>
    {
        self.items.next()
    }

    /// The exact size hint that the collect read.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>)
    {
        (self.len, Some(self.len))
    }
}

impl<I> ExactSizeIterator for Hinted<'_, I> where I: Iterator
{
}

/// A holder of a thin shared block: one word that points at the count, the
/// length, a header and the items.
///
/// # Specification
/// - ensures: the module's unsafe invariants hold between each two calls.
pub struct ThinShared<H, T, A>
where
    A: Allocator,
{
    /// The block, which this holder holds with the others that the count
    /// counts.
    head: NonNull<Head<H, T>>,
    /// The allocator that gave the block.
    alloc: A,
    /// The header and the items belong to the holders.
    contents: PhantomData<(H, T)>,
}

impl<H, T> ThinShared<H, T, Global>
{
    /// A block of `header` and the items of `items` over the global
    /// allocator, with one holder.
    ///
    /// # Specification
    /// - ensures: as [`ThinShared::from_header_and_iter_in`].
    /// - fails: a block past `isize::MAX` bytes panics, and the global
    ///   allocator's refusal goes to its error handler, as a vector's grow
    ///   does; [`ThinShared::from_header_and_iter_in`] returns both.
    /// - panics: as [`ThinShared::from_header_and_iter_in`].
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the header and the items read back.
    /// - witness: `tests::thin_shared::a_thin_block_holds_the_count_the_length_the_header_and_the_items`
    #[spec(ensures: |ret| usize::from(ret.head().count.holders()) == 1)]
    #[inline]
    #[must_use]
    pub fn from_header_and_iter<I>(
        header: H,
        items: I,
    ) -> Self
    where
        I: IntoIterator<Item = T>,
        I::IntoIter: ExactSizeIterator,
    {
        match Self::from_header_and_iter_in(header, items, Global) {
            Ok(thin) => thin,
            Err(refused) => refused.raise(),
        }
    }
}

impl<H, T, A> ThinShared<H, T, A>
where
    A: Allocator,
{
    /// A block of `header` and the items of `items` in `alloc`, with one
    /// holder, or the refusal of its block.
    ///
    /// # Specification
    /// - requires: the iterator yields at least as many items as its length.
    /// - ensures: one holder of a block of `header` and the first `len` items,
    ///   in order, where `len` is the iterator's length.
    /// - fails: [`Refused::Overflow`] when the block passes `isize::MAX` bytes,
    ///   and [`Refused::Allocator`] when the allocator refuses it. The header
    ///   and the iterator then drop, and no item moves.
    /// - panics: when the iterator yields fewer items than its length, or when
    ///   it panics. The header and the items in place drop, and the block
    ///   returns, first.
    ///
    /// # Errors
    /// - [`Refused::Overflow`]: the block's bytes pass `isize::MAX`.
    /// - [`Refused::Allocator`]: the allocator refuses the block's layout.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the header and the items read back, a short iterator
    ///   panics and leaves nothing, under Miri, and each refusal draws no block
    ///   and drops the header once.
    /// - witness: `tests::thin_shared::a_thin_block_holds_the_count_the_length_the_header_and_the_items`
    /// - witness: `tests::thin_shared::an_iterator_short_of_its_length_panics_and_leaves_nothing`
    /// - witness: `tests::thin_shared::a_refused_block_gives_the_refusal_and_drops_the_header`
    #[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|thin| usize::from(thin.head().count.holders()) == 1))]
    #[inline]
    pub fn from_header_and_iter_in<I>(
        header: H,
        items: I,
        alloc: A,
    ) -> Result<Self, Refused>
    where
        I: IntoIterator<Item = T>,
        I::IntoIter: ExactSizeIterator,
    {
        let mut items = items.into_iter();
        let len = items.len();
        let layout = layout::<H, T>(Count::from(len))?;
        let Ok(bytes) = alloc.allocate(layout)
        else {
            return Err(Refused::Allocator(layout));
        };
        let head = bytes.cast::<Head<H, T>>();
        // SAFETY: the allocator gave `layout`'s bytes, which fit the head.
        unsafe {
            head.as_ptr().write(Head {
                count: Counter::one(),
                len,
                header,
                items: [],
            });
        }
        let mut partial = DropGuard::new(
            Partial {
                head,
                written: 0,
                layout,
                alloc: &alloc,
            },
            Partial::abandon,
        );
        while partial.written < len {
            let Some(item) = items.next()
            else {
                short();
            };
            // SAFETY: the slot lies in the block, past the items in place.
            let slot = unsafe { first(head).add(partial.written) };
            // SAFETY: the slot holds no item yet, so the write overwrites
            // nothing.
            unsafe {
                slot.write(item);
            }
            partial.written = partial.written.saturating_add(1);
        }
        let _built = DropGuard::dismiss(partial);
        Ok(Self {
            head,
            alloc,
            contents: PhantomData,
        })
    }

    /// The head of the block.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn head(&self) -> &Head<H, T>
    {
        // SAFETY: this holder keeps the block live for the borrow.
        unsafe { self.head.as_ref() }
    }

    /// The header.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn header(&self) -> &H
    {
        &self.head().header
    }

    /// The items.
    ///
    /// # Specification
    /// - ensures: the block's items, in the order that the build wrote them.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the items read back in order, and an empty slice
    ///   reads empty.
    /// - witness: `tests::thin_shared::a_thin_block_holds_the_count_the_length_the_header_and_the_items`
    #[spec(ensures: |ret| Count::from(ret.len()) == Count::from(self.head().len))]
    #[inline]
    #[must_use]
    pub fn slice(&self) -> &[T]
    {
        // SAFETY: the first `len` slots hold items, and the borrow of `self`
        // keeps them.
        unsafe { slice::from_raw_parts(first(self.head), self.head().len) }
    }

    /// Whether two holders share one block.
    ///
    /// # Specification
    /// - ensures: [`Identity::Same`] exactly when both point at one block.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a clone is the same, and the copy of a mutable borrow
    ///   is distinct.
    /// - witness: `tests::thin_shared::a_mutable_borrow_writes_a_sole_block_in_place_and_copies_a_shared_one`
    #[spec(ensures: |ret| (ret == Identity::Same) == ptr::addr_eq(this.head.as_ptr(), other.head.as_ptr()))]
    #[inline]
    #[must_use]
    pub fn ptr_eq(
        this: &Self,
        other: &Self,
    ) -> Identity
    {
        if ptr::addr_eq(this.head.as_ptr(), other.head.as_ptr()) {
            Identity::Same
        }
        else {
            Identity::Distinct
        }
    }

    /// The items, borrowed mutably, after a copy of the header and the items
    /// to a block of their own when other holders share them.
    ///
    /// # Specification
    /// - ensures: `this` is the only holder of its block. A block that other
    ///   holders share stays theirs, and `this` holds a clone of its header and
    ///   its items.
    /// - fails: a copy that the allocator refuses goes to its error handler, as
    ///   `Box`'s does.
    /// - panics: when a clone panics; `this` then stays as it was.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a sole block takes the write in place, and a shared
    ///   block moves to a new block while the other holder reads the old items.
    /// - witness: `tests::thin_shared::a_mutable_borrow_writes_a_sole_block_in_place_and_copies_a_shared_one`
    #[spec(ensures: usize::from(this.head().count.holders()) == 1)]
    #[inline]
    pub fn make_mut(this: &mut Self) -> &mut [T]
    where
        H: Clone,
        T: Clone,
        A: Clone,
    {
        if this.head().count.holding() == Holding::WithOthers {
            let copy = match Self::from_header_and_iter_in(
                this.header().clone(),
                this.slice().iter().cloned(),
                this.alloc.clone(),
            ) {
                Ok(thin) => thin,
                Err(refused) => refused.raise(),
            };
            *this = copy;
        }
        let len = this.head().len;
        // SAFETY: `this` is the only holder, and the mutable borrow of it is
        // the only borrow. The `Acquire` load ordered each dropped holder's
        // use before this write. The first `len` slots hold items.
        unsafe { slice::from_raw_parts_mut(first(this.head), len) }
    }
}

impl<H, T, A> Clone for ThinShared<H, T, A>
where
    A: Allocator + Clone,
{
    /// # Specification
    /// - ensures: one more holder of the same block.
    /// - panics: when the count would pass `isize::MAX`.
    /// - executable: none — another thread can move the count between two
    ///   reads, so no predicate on this thread reads a fixed value.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a clone reads the same header and items, and each
    ///   drop of a clone frees nothing until the last.
    /// - witness: `tests::thin_shared::the_last_holder_drops_the_header_before_the_items`
    #[inline]
    fn clone(&self) -> Self
    {
        let alloc = self.alloc.clone();
        self.head().count.join();
        Self {
            head: self.head,
            alloc,
            contents: PhantomData,
        }
    }
}

impl<H, T, A> Drop for ThinShared<H, T, A>
where
    A: Allocator,
{
    /// # Specification
    /// - ensures: one holder fewer. The last holder drops the header, then each
    ///   item once, and returns the block to the allocator once.
    /// - panics: when the header's or an item's drop panics; the rest drops,
    ///   and the block returns, first.
    /// - executable: none — a dropped holder has no state that a predicate
    ///   could read.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the drops record the header before the items, and a
    ///   header whose drop panics leaves each item dropped and the block freed,
    ///   under Miri.
    /// - witness: `tests::thin_shared::the_last_holder_drops_the_header_before_the_items`
    #[inline]
    fn drop(&mut self)
    {
        if self.head().count.leave() == Departure::Others {
            return;
        }
        let len = self.head().len;
        let layout = match layout::<H, T>(Count::from(len)) {
            Ok(layout) => layout,
            Err(refused) => refused.raise(),
        };
        Partial {
            head: self.head,
            written: len,
            layout,
            alloc: &self.alloc,
        }
        .abandon();
    }
}

impl<H, T, A> fmt::Debug for ThinShared<H, T, A>
where
    H: fmt::Debug,
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
        f.debug_struct("ThinShared")
            .field("header", self.header())
            .field("items", &self.slice())
            .finish()
    }
}

impl<T> Default for ThinShared<(), T, Global>
{
    /// A holder of no item under a unit header, as `Arc::default` gives an
    /// empty slice. Each default takes the static empty block, so the call
    /// draws no block. An item of an alignment past 16 does not compile, so no
    /// default has a path that allocates. No item of the kernel has one.
    ///
    /// # Specification
    /// - requires: an item of an alignment up to 16, which the compiler checks.
    /// - ensures: a holder of no item. Two defaults share one block.
    /// - panics: when the static block's count would pass `isize::MAX`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two defaults share the static block, a mutable borrow
    ///   of one moves it to a block of its own, and the drops leave the static
    ///   block whole, under Miri.
    /// - witness: `tests::thin_shared::an_empty_default_shares_the_static_block`
    #[spec(ensures: |ret| ret.slice().is_empty())]
    #[inline]
    fn default() -> Self
    {
        const {
            assert!(
                align_of::<T>() <= align_of::<Aligned>()
                    && offset_of!(Head<(), T>, items) <= size_of::<Head<(), Aligned>>(),
                "the static empty block serves an item of an alignment up to 16"
            );
        }
        #[cfg(not(loom))]
        {
            EMPTY.count.join();
            // The pointer keeps the provenance of the whole static. A head over
            // `T` reads the count and the length where the static holds them.
            // Its items, of which there are none, lie within the static or at
            // its end. A target of 32 bits places them before the static's own.
            Self {
                head: NonNull::from(&EMPTY).cast(),
                alloc: Global,
                contents: PhantomData,
            }
        }
        #[cfg(loom)]
        {
            Self::from_header_and_iter((), core::iter::empty())
        }
    }
}

impl<T, const N: usize, A> From<SmallVec<T, N, A>> for ThinShared<(), T, Global>
where
    A: Allocator,
{
    /// A block of the vector's items, in order, under a unit header, as an
    /// `Arc` of a slice takes a `Vec`. An empty vector takes the static block
    /// of the default, so it draws no block.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(items: SmallVec<T, N, A>) -> Self
    {
        if items.is_empty() {
            return Self::default();
        }
        Self::from_header_and_iter((), items)
    }
}

impl<T> FromIterator<T> for ThinShared<(), T, Global>
{
    /// A block of the items, in order, under a unit header. An iterator whose
    /// size hint is exact writes its items into one block of that length, as
    /// an `Arc` of a slice takes an iterator of a trusted length. An empty
    /// one takes the static block of the default. Any other iterator gathers
    /// its items in a vector first, since the block needs their count before
    /// it holds them.
    ///
    /// # Specification
    /// - ensures: the block holds the items of the iterator, in order.
    /// - panics: when an iterator with an exact size hint yields another count
    ///   of items, and when the iterator panics.
    /// - executable: none — the items are consumed, so no predicate reads them
    ///   after.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an iterator with an exact hint and one without give
    ///   the same items, an empty collect shares the static block, and an
    ///   iterator off its exact hint panics.
    /// - witness: `tests::thin_shared::a_collect_holds_the_items_with_or_without_an_exact_hint`
    /// - witness: `tests::thin_shared::an_iterator_off_its_exact_hint_panics`
    #[inline]
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = T>,
    {
        let mut items = iter.into_iter();
        let (lower, upper) = items.size_hint();
        if upper != Some(lower) {
            let gathered: SmallVec<T, 0, Global> = items.collect();
            return Self::from(gathered);
        }
        let thin = if lower == 0 {
            Self::default()
        }
        else {
            Self::from_header_and_iter((), Hinted {
                items: &mut items,
                len: lower,
            })
        };
        if items.next().is_some() {
            long();
        }
        thin
    }
}

impl<H, T, A> Deref for ThinShared<H, T, A>
where
    A: Allocator,
{
    type Target = [T];

    /// The items, as [`ThinShared::slice`] gives them, so a block of a unit
    /// header reads as an `Arc` of a slice reads.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn deref(&self) -> &[T]
    {
        self.slice()
    }
}

impl<H, T, A> PartialEq for ThinShared<H, T, A>
where
    H: PartialEq,
    T: PartialEq,
    A: Allocator,
{
    /// Two holders are equal when their headers and their items are, whether
    /// or not they share one block.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn eq(
        &self,
        other: &Self,
    ) -> bool
    {
        self.header() == other.header() && self.slice() == other.slice()
    }
}

impl<H, T, A> Eq for ThinShared<H, T, A>
where
    H: Eq,
    T: Eq,
    A: Allocator,
{
}

impl<H, T, A> PartialOrd for ThinShared<H, T, A>
where
    H: PartialOrd,
    T: PartialOrd,
    A: Allocator,
{
    /// The order of the headers, and then the slices' lexicographic order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn partial_cmp(
        &self,
        other: &Self,
    ) -> Option<Ordering>
    {
        match self.header().partial_cmp(other.header()) {
            Some(Ordering::Equal) => self.slice().partial_cmp(other.slice()),
            order => order,
        }
    }
}

impl<H, T, A> Ord for ThinShared<H, T, A>
where
    H: Ord,
    T: Ord,
    A: Allocator,
{
    /// The order of the headers, and then the slices' lexicographic order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn cmp(
        &self,
        other: &Self,
    ) -> Ordering
    {
        self.header()
            .cmp(other.header())
            .then_with(|| self.slice().cmp(other.slice()))
    }
}

impl<H, T, A> Hash for ThinShared<H, T, A>
where
    H: Hash,
    T: Hash,
    A: Allocator,
{
    /// The header, and then the items as their slice hashes them.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn hash<S>(
        &self,
        state: &mut S,
    ) where
        S: Hasher,
    {
        self.header().hash(state);
        self.slice().hash(state);
    }
}

/// # Safety
/// - unsafe invariants: holders on two threads read one header and one slice
///   and drop them on either, so both are `Send` and `Sync`.
// SAFETY: the count is atomic, and the header and the items are `Send` and
// `Sync`.
unsafe impl<H, T, A> Send for ThinShared<H, T, A>
where
    H: Send + Sync,
    T: Send + Sync,
    A: Allocator + Send,
{
}

/// # Safety
/// - unsafe invariants: a shared borrow of a holder clones it on another
///   thread, so the header and the items are `Send` and `Sync`.
// SAFETY: the count is atomic, and the header and the items are `Send` and
// `Sync`.
unsafe impl<H, T, A> Sync for ThinShared<H, T, A>
where
    H: Send + Sync,
    T: Send + Sync,
    A: Allocator + Sync,
{
}
