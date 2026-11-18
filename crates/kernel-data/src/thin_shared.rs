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
//!   length. The header is initialised, and the first `len` slots past the head
//!   hold items. The count equals the number of live holders, and the holder
//!   that takes it from one to zero frees the block, once.

use alloc::alloc::Global;
use core::alloc::Allocator;
use core::alloc::Layout;
use core::fmt;
use core::marker::PhantomData;
use core::mem::DropGuard;
use core::mem::align_of;
use core::mem::offset_of;
use core::ptr;
use core::ptr::NonNull;
use core::slice;

use anodized::spec;

use crate::shared::Counter;
use crate::shared::Departure;
use crate::small_vec::Count;
use crate::small_vec::Refused;

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
