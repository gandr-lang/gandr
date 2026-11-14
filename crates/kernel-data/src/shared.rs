//! The shared pointer with one count, on `triomphe`'s design. A [`Shared`]
//! points at one block of its allocator, and the block holds the count of
//! holders and the value. No weak count stands beside it, so
//! [`Shared::make_mut`] and [`Shared::get_mut`] read the count with one load
//! and a branch. A [`Unique`] owns its block alone: it builds a value before
//! the share, and it turns into a [`Shared`] with no atomic operation.
//!
//! The orderings are `std`'s. A clone adds a holder with `Relaxed`, since it
//! comes from a holder that the caller already has. A drop takes a holder away
//! with `Release`, and the holder that takes the count to zero loads it with
//! `Acquire` before it frees the block. So each use by an earlier holder
//! happens before the free. A mutable borrow loads the count with `Acquire`,
//! so the uses of each holder that dropped happen before the write. Under
//! `cfg(loom)`, the count is `loom`'s atomic, and the crate's model explores
//! each interleaving of the clones, the drops and the mutable borrows on two
//! and three threads:
//!
//! ```sh
//! RUSTFLAGS="--cfg loom" CARGO_TARGET_DIR=target/loom cargo test -p gandr-kernel-data --test tests --release model
//! ```
//!
//! | Pointer | Holder | Block |
//! | ------- | ------ | ----- |
//! | [`Shared<T>`] | one word | one word and `T` |
//! | `std`'s `Arc<T>` | one word | two words and `T` |
//! | [`ThinShared<H, T>`](crate::ThinShared) | one word | two words, `H` and the items |
//! | `std`'s `Arc<[T]>` | two words | two words and the items |
//!
//! # Safety
//! - unsafe invariants: the pointer of a [`Shared`] or a [`Unique`] names a
//!   block that its allocator gave with the layout of [`Block`], and the
//!   block's value is initialised. The count equals the number of live holders
//!   of the block. A [`Unique`] is the one holder of its block. The holder that
//!   takes the count from one to zero frees the block, once.

use alloc::alloc::Global;
use core::alloc::Allocator;
use core::alloc::Layout;
use core::fmt;
use core::marker::PhantomData;
use core::mem::DropGuard;
use core::mem::ManuallyDrop;
use core::ops::Deref;
use core::ops::DerefMut;
use core::ptr;
use core::ptr::NonNull;
#[cfg(not(loom))]
use core::sync::atomic::AtomicUsize;
use core::sync::atomic::Ordering::Acquire;
use core::sync::atomic::Ordering::Relaxed;
use core::sync::atomic::Ordering::Release;

use anodized::spec;
#[cfg(loom)]
use loom::sync::atomic::AtomicUsize;
use quenchant_shape::shape::Maybe;

use crate::small_vec::Refused;

/// The most holders that one block counts. A clone past it is refused.
const MOST: usize = isize::MAX.cast_unsigned();

/// A number of holders of one block.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Holders(usize);

impl From<Holders> for usize
{
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: Holders) -> Self
    {
        value.0
    }
}

/// Why a holder cannot borrow the value mutably.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Held
{
    /// Another holder shares the block.
    ByOthers,
}

/// Whether two holders point at one block.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Identity
{
    /// The two holders share one block.
    Same,
    /// The two holders point at two blocks.
    Distinct,
}

/// What a holder that leaves reads from the count.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Departure
{
    /// The holder was the last, and the block is free to release.
    Last,
    /// Other holders stay.
    Others,
}

/// Whether one holder is the only holder of its block.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Holding
{
    /// The holder is the only one.
    Alone,
    /// Other holders share the block.
    WithOthers,
}

/// The count of holders of one block, with the orderings of each step. The
/// shared pointer and the thin shared pointer both count through it.
///
/// # Specification
/// - ensures: the count is the number of live holders, from one at the block's
///   build to zero at its release.
#[repr(transparent)]
pub struct Counter(AtomicUsize);

impl Counter
{
    /// The count of a block that one holder builds.
    ///
    /// # Specification
    /// - ensures: one holder.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a new pointer reads one holder.
    /// - witness: `tests::shared::the_count_follows_each_clone_and_each_drop`
    #[spec(ensures: |ret| ret.holders() == Holders(1))]
    #[inline]
    pub fn one() -> Self
    {
        Self(AtomicUsize::new(1))
    }

    /// Adds a holder for a clone of an existing holder.
    ///
    /// # Specification
    /// - requires: the caller holds the block.
    /// - ensures: the count is one more than before.
    /// - panics: when the count would pass `isize::MAX`. The count then stays
    ///   as it was, so it never wraps to zero.
    /// - executable: none — another thread can move the count between two
    ///   reads, so no predicate on this thread reads a fixed value.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the count reads each clone, and the `loom` model
    ///   clones on two and three threads.
    /// - witness: `tests::shared::the_count_follows_each_clone_and_each_drop`
    #[expect(
        clippy::panic,
        reason = "a count past `isize::MAX` holders takes that many leaked clones, and it panics after it backs out, so the count never wraps"
    )]
    #[inline]
    pub fn join(&self)
    {
        let before = self.0.fetch_add(1, Relaxed);
        if before > MOST {
            self.0.fetch_sub(1, Relaxed);
            panic!("a shared block passes isize::MAX holders");
        }
    }

    /// Takes a holder away, and says whether it was the last.
    ///
    /// # Specification
    /// - requires: the caller holds the block and stops holding it.
    /// - ensures: the count is one less than before. On [`Departure::Last`],
    ///   each use by each earlier holder happens before the return.
    /// - panics: none.
    /// - executable: none — another thread can move the count between two
    ///   reads, so no predicate on this thread reads a fixed value.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — counted drops free the block once, and the `loom`
    ///   model drops on two and three threads.
    /// - witness: `tests::shared::each_value_drops_once_and_each_block_frees_once`
    #[inline]
    pub fn leave(&self) -> Departure
    {
        if self.0.fetch_sub(1, Release) != 1 {
            return Departure::Others;
        }
        let _last = self.0.load(Acquire);
        Departure::Last
    }

    /// Whether the caller is the only holder.
    ///
    /// # Specification
    /// - requires: the caller holds the block, borrowed mutably, so no clone of
    ///   the caller's holder can start meanwhile.
    /// - ensures: on [`Holding::Alone`], each use by each holder that dropped
    ///   happens before the return.
    /// - panics: none.
    /// - executable: none — another thread can drop a holder between two reads,
    ///   so no predicate on this thread reads a fixed value.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a mutable borrow copies a shared value and writes a
    ///   sole one in place, and the `loom` model races it with drops.
    /// - witness: `tests::shared::a_mutable_borrow_writes_a_sole_value_in_place_and_copies_a_shared_one`
    #[inline]
    fn holding(&self) -> Holding
    {
        if self.0.load(Acquire) == 1 {
            Holding::Alone
        }
        else {
            Holding::WithOthers
        }
    }

    /// The number of holders, as one read sees it.
    ///
    /// # Specification
    /// - ensures: a count that the block held at the read.
    /// - panics: none.
    /// - executable: none — another thread can move the count between two
    ///   reads, so no predicate on this thread reads a fixed value.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the count reads each clone and each drop.
    /// - witness: `tests::shared::the_count_follows_each_clone_and_each_drop`
    #[inline]
    pub(crate) fn holders(&self) -> Holders
    {
        Holders(self.0.load(Relaxed))
    }
}

/// The block of a shared value: the count of holders, and the value.
///
/// # Specification
/// trivial.
#[repr(C)]
struct Block<T>
{
    /// The number of live holders.
    count: Counter,
    /// The shared value.
    value: T,
}

/// Builds a block of `value` in `alloc`, with one holder.
///
/// # Specification
/// - ensures: a block of the allocator, with one holder and `value`.
/// - fails: [`Refused::Allocator`] with the block's layout when the allocator
///   refuses it; the value then drops.
/// - panics: none.
/// - executable: none — the pointer names memory that no safe predicate reads.
///
/// # Errors
/// - [`Refused::Allocator`]: the allocator refuses the block's layout.
///
/// # Adequacy
/// - hypothesis: L2 — a counting allocator reads one allocation of the block's
///   layout for each new pointer, and a refusing one gives the layout back.
/// - witness: `tests::shared::a_block_holds_one_count_and_the_value`
/// - witness: `tests::shared::a_refused_block_gives_the_refusal_and_drops_the_value`
#[inline]
fn build<T, A>(
    value: T,
    alloc: &A,
) -> Result<NonNull<Block<T>>, Refused>
where
    A: Allocator,
{
    let layout = Layout::new::<Block<T>>();
    let Ok(bytes) = alloc.allocate(layout)
    else {
        return Err(Refused::Allocator(layout));
    };
    let block = bytes.cast::<Block<T>>();
    // SAFETY: the allocator gave `layout`'s bytes, which fit one block.
    unsafe {
        block.as_ptr().write(Block {
            count: Counter::one(),
            value,
        });
    }
    Ok(block)
}

/// Drops the block's count and value, and returns its bytes to `alloc`.
///
/// # Safety
/// - unsafe invariants: the caller is the last holder of `block`, and `alloc`
///   gave it. No holder of `block` stays after the call.
///
/// # Specification
/// - requires: the caller was the last holder of `block`, which `alloc` gave.
/// - ensures: the value drops once, and the bytes return to the allocator once,
///   when the value's drop panics too.
/// - panics: when the value's drop panics.
/// - executable: none — the block ends, so no state stays to read.
///
/// # Adequacy
/// - hypothesis: L3 — a value whose drop panics still frees its block, under
///   Miri, which reports a leak and a double free.
/// - witness: `tests::shared::each_value_drops_once_and_each_block_frees_once`
#[inline]
unsafe fn release<T, A>(
    block: NonNull<Block<T>>,
    alloc: &A,
) where
    A: Allocator,
{
    let free = DropGuard::new(block, |block| {
        // SAFETY: `alloc` gave the block with this layout, and the drop below
        // ends its use.
        unsafe {
            alloc.deallocate(block.cast(), Layout::new::<Block<T>>());
        }
    });
    // SAFETY: the caller was the last holder, so the block's fields drop
    // once, here.
    unsafe {
        ptr::drop_in_place(free.as_ptr());
    }
}

/// The one holder of a block: it builds a value before the share.
///
/// # Specification
/// - ensures: the module's unsafe invariants hold between each two calls.
pub struct Unique<T, A>
where
    A: Allocator,
{
    /// The block, which this holder alone holds.
    block: NonNull<Block<T>>,
    /// The allocator that gave the block.
    alloc: A,
    /// The block's value belongs to this holder.
    value: PhantomData<Block<T>>,
}

impl<T> Unique<T, Global>
{
    /// A block of `value` over the global allocator.
    ///
    /// # Specification
    /// - ensures: the one holder of a block of `value`.
    /// - fails: the global allocator's refusal goes to its error handler, as
    ///   `Box::new`'s does; [`Unique::new_in`] returns it.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the value reads back.
    /// - witness: `tests::shared::a_unique_value_builds_in_place_and_shares_with_one_holder`
    #[spec(ensures: |ret| ret.block().count.holders() == Holders(1))]
    #[inline]
    #[must_use]
    pub fn new(value: T) -> Self
    {
        match Self::new_in(value, Global) {
            Ok(unique) => unique,
            Err(refused) => refused.raise(),
        }
    }
}

impl<T, A> Unique<T, A>
where
    A: Allocator,
{
    /// A block of `value` in `alloc`, or the allocator's refusal.
    ///
    /// # Specification
    /// - ensures: the one holder of a block of `value`.
    /// - fails: [`Refused::Allocator`] when the allocator refuses the block;
    ///   the value then drops.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`Refused::Allocator`]: the allocator refuses the block's layout.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a counting allocator reads one allocation, and a
    ///   refusing one gives its refusal and drops the value once.
    /// - witness: `tests::shared::a_block_holds_one_count_and_the_value`
    /// - witness: `tests::shared::a_refused_block_gives_the_refusal_and_drops_the_value`
    #[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|unique| unique.block().count.holders() == Holders(1)))]
    #[inline]
    pub fn new_in(
        value: T,
        alloc: A,
    ) -> Result<Self, Refused>
    {
        let block = build(value, &alloc)?;
        Ok(Self {
            block,
            alloc,
            value: PhantomData,
        })
    }

    /// The block.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn block(&self) -> &Block<T>
    {
        // SAFETY: this holder keeps the block live for the borrow.
        unsafe { self.block.as_ref() }
    }

    /// The shared pointer of this block, with no atomic operation: the count
    /// is one already.
    ///
    /// # Specification
    /// - ensures: one holder of the same block.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the shared pointer reads one holder and the value
    ///   that the unique holder wrote.
    /// - witness: `tests::shared::a_unique_value_builds_in_place_and_shares_with_one_holder`
    #[spec(ensures: |ret| Shared::strong_count(&ret) == Holders(1))]
    #[inline]
    #[must_use]
    pub fn into_shared(self) -> Shared<T, A>
    {
        let this = ManuallyDrop::new(self);
        // SAFETY: `this` never drops, so its allocator moves out once.
        let alloc = unsafe { ptr::read(&raw const this.alloc) };
        Shared {
            block: this.block,
            alloc,
            value: PhantomData,
        }
    }
}

impl<T, A> Deref for Unique<T, A>
where
    A: Allocator,
{
    type Target = T;

    /// # Specification
    /// trivial.
    #[inline]
    fn deref(&self) -> &T
    {
        &self.block().value
    }
}

impl<T, A> DerefMut for Unique<T, A>
where
    A: Allocator,
{
    /// # Specification
    /// trivial.
    #[inline]
    fn deref_mut(&mut self) -> &mut T
    {
        // SAFETY: this holder is the block's only holder, and the mutable
        // borrow of it is the only borrow.
        unsafe { &mut (*self.block.as_ptr()).value }
    }
}

impl<T, A> Drop for Unique<T, A>
where
    A: Allocator,
{
    /// # Specification
    /// - ensures: the value drops once, and the block returns to the allocator
    ///   once.
    /// - panics: when the value's drop panics; the block returns first.
    /// - executable: none — a dropped holder has no state that a predicate
    ///   could read.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — counted drops and frees, under Miri.
    /// - witness: `tests::shared::each_value_drops_once_and_each_block_frees_once`
    #[inline]
    fn drop(&mut self)
    {
        // SAFETY: a unique holder is the last holder of its block.
        unsafe { release(self.block, &self.alloc) }
    }
}

impl<T, A> fmt::Debug for Unique<T, A>
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
        fmt::Debug::fmt(&**self, f)
    }
}

/// A holder of a shared block, with one count and no weak count.
///
/// # Specification
/// - ensures: the module's unsafe invariants hold between each two calls.
pub struct Shared<T, A>
where
    A: Allocator,
{
    /// The block, which this holder holds with the others that the count
    /// counts.
    block: NonNull<Block<T>>,
    /// The allocator that gave the block.
    alloc: A,
    /// The block's value belongs to its holders.
    value: PhantomData<Block<T>>,
}

impl<T> Shared<T, Global>
{
    /// A block of `value` over the global allocator, with one holder.
    ///
    /// # Specification
    /// - ensures: one holder of a block of `value`.
    /// - fails: as [`Unique::new_in`].
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the value reads back with one holder.
    /// - witness: `tests::shared::the_count_follows_each_clone_and_each_drop`
    #[spec(ensures: |ret| Self::strong_count(&ret) == Holders(1))]
    #[inline]
    #[must_use]
    pub fn new(value: T) -> Self
    {
        Unique::new(value).into_shared()
    }
}

impl<T, A> Shared<T, A>
where
    A: Allocator,
{
    /// The block.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn block(&self) -> &Block<T>
    {
        // SAFETY: this holder keeps the block live for the borrow.
        unsafe { self.block.as_ref() }
    }

    /// The value, borrowed mutably, after a copy of it to a block of its own
    /// when other holders share it.
    ///
    /// # Specification
    /// - ensures: `this` is the only holder of its block. A value that other
    ///   holders share stays theirs, and `this` holds a clone of it.
    /// - fails: a copy that the allocator refuses goes to its error handler, as
    ///   `Box`'s does.
    /// - panics: when the value's clone panics; `this` then stays as it was.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a sole value keeps its block, a shared value moves to
    ///   a new block, and the other holder reads the old value; the `loom`
    ///   model races the borrow with drops on two and three threads.
    /// - witness: `tests::shared::a_mutable_borrow_writes_a_sole_value_in_place_and_copies_a_shared_one`
    #[spec(ensures: this.block().count.holders() == Holders(1))]
    #[inline]
    pub fn make_mut(this: &mut Self) -> &mut T
    where
        T: Clone,
        A: Clone,
    {
        if this.block().count.holding() == Holding::WithOthers {
            let copy = match Unique::new_in(T::clone(this), this.alloc.clone()) {
                Ok(unique) => unique.into_shared(),
                Err(refused) => refused.raise(),
            };
            *this = copy;
        }
        // SAFETY: `this` is the only holder, and the mutable borrow of it is
        // the only borrow. The `Acquire` load ordered each dropped holder's
        // use before this write.
        unsafe { &mut (*this.block.as_ptr()).value }
    }

    /// The value, borrowed mutably, when `this` is the only holder.
    ///
    /// # Specification
    /// - ensures: a mutable borrow when no other holder shares the block, and
    ///   [`Held::ByOthers`] otherwise.
    /// - provides: [`Held::ByOthers`]: another holder shares the block, so the
    ///   value stays shared.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a sole holder borrows, and a shared holder reads the
    ///   reason.
    /// - witness: `tests::shared::a_mutable_borrow_writes_a_sole_value_in_place_and_copies_a_shared_one`
    #[spec(
        captures: holders = this.block().count.holders(),
        ensures: |ret| matches!(ret, Maybe::Present(_)) == (holders == Holders(1)),
    )]
    #[inline]
    pub fn get_mut(this: &mut Self) -> Maybe<&mut T, Held>
    {
        match this.block().count.holding() {
            // SAFETY: as in `make_mut`, with the count read at one.
            Holding::Alone => Maybe::Present(unsafe { &mut (*this.block.as_ptr()).value }),
            Holding::WithOthers => Maybe::Absent(Held::ByOthers),
        }
    }

    /// The value, out of its block, when `this` is the only holder.
    ///
    /// # Specification
    /// - ensures: the value and the block's release when no other holder shares
    ///   the block. Otherwise `this` comes back, as it was.
    /// - panics: none.
    ///
    /// # Errors
    /// - `this`: another holder shares the block, so the value stays in it.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a sole holder takes its value out, and a shared
    ///   holder comes back with the count unchanged.
    /// - witness: `tests::shared::a_sole_holder_takes_its_value_out`
    #[spec(captures: holders = this.block().count.holders(), ensures: |ret| ret.is_ok() == (holders == Holders(1)))]
    #[inline]
    pub fn try_unwrap(this: Self) -> Result<T, Self>
    {
        if this.block().count.holding() == Holding::WithOthers {
            return Err(this);
        }
        let this = ManuallyDrop::new(this);
        // SAFETY: `this` never drops, so its allocator moves out once, and it
        // drops at the end of this call, after the bytes return to it.
        let alloc = unsafe { ptr::read(&raw const this.alloc) };
        let free = DropGuard::new(this.block, |block| {
            // SAFETY: `this` was the last holder, and its allocator gave the
            // block with this layout.
            unsafe {
                alloc.deallocate(block.cast(), Layout::new::<Block<T>>());
            }
        });
        let block = free.as_ptr();
        // SAFETY: `this` is the last holder, so the count's place lies in a
        // live block.
        let count = unsafe { &raw mut (*block).count };
        // SAFETY: the count drops once, here.
        unsafe {
            ptr::drop_in_place(count);
        }
        // SAFETY: the value's place lies in the same live block.
        let place = unsafe { &raw const (*block).value };
        // SAFETY: the value moves out once, here, before the bytes return.
        let value = unsafe { ptr::read(place) };
        drop(free);
        Ok(value)
    }

    /// Whether two holders share one block.
    ///
    /// # Specification
    /// - ensures: [`Identity::Same`] exactly when both point at one block.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a clone is the same, and two builds of one value are
    ///   distinct.
    /// - witness: `tests::shared::the_count_follows_each_clone_and_each_drop`
    #[spec(ensures: |ret| (ret == Identity::Same) == ptr::addr_eq(this.block.as_ptr(), other.block.as_ptr()))]
    #[inline]
    #[must_use]
    pub fn ptr_eq(
        this: &Self,
        other: &Self,
    ) -> Identity
    {
        if ptr::addr_eq(this.block.as_ptr(), other.block.as_ptr()) {
            Identity::Same
        }
        else {
            Identity::Distinct
        }
    }

    /// The number of holders of the block, as one read sees it.
    ///
    /// # Specification
    /// - ensures: a count that the block held at the read, at least one.
    /// - panics: none.
    /// - executable: none — another thread can move the count between two
    ///   reads, so no predicate on this thread reads a fixed value.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the count reads each clone and each drop.
    /// - witness: `tests::shared::the_count_follows_each_clone_and_each_drop`
    #[inline]
    #[must_use]
    pub fn strong_count(this: &Self) -> Holders
    {
        this.block().count.holders()
    }
}

impl<T, A> Clone for Shared<T, A>
where
    A: Allocator + Clone,
{
    /// # Specification
    /// - ensures: one more holder of the same block.
    /// - panics: when the count would pass `isize::MAX`, as [`Counter::join`]
    ///   does.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the count reads each clone, and the `loom` model
    ///   clones on two and three threads.
    /// - witness: `tests::shared::the_count_follows_each_clone_and_each_drop`
    #[spec(ensures: |ret| Self::ptr_eq(&ret, self) == Identity::Same)]
    #[inline]
    fn clone(&self) -> Self
    {
        let alloc = self.alloc.clone();
        self.block().count.join();
        Self {
            block: self.block,
            alloc,
            value: PhantomData,
        }
    }
}

impl<T, A> Deref for Shared<T, A>
where
    A: Allocator,
{
    type Target = T;

    /// # Specification
    /// trivial.
    #[inline]
    fn deref(&self) -> &T
    {
        &self.block().value
    }
}

impl<T, A> Drop for Shared<T, A>
where
    A: Allocator,
{
    /// # Specification
    /// - ensures: one holder fewer. The last holder drops the value once and
    ///   returns the block to the allocator once.
    /// - panics: when the last holder's value drop panics; the block returns
    ///   first.
    /// - executable: none — a dropped holder has no state that a predicate
    ///   could read.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — counted drops and frees under Miri, and the `loom`
    ///   model drops on two and three threads.
    /// - witness: `tests::shared::each_value_drops_once_and_each_block_frees_once`
    #[inline]
    fn drop(&mut self)
    {
        if self.block().count.leave() == Departure::Last {
            // SAFETY: this holder took the count to zero, so it is the last
            // holder, and its allocator gave the block.
            unsafe { release(self.block, &self.alloc) }
        }
    }
}

impl<T, A> fmt::Debug for Shared<T, A>
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
        fmt::Debug::fmt(&**self, f)
    }
}

/// # Safety
/// - unsafe invariants: a unique holder owns its value as a `Box` does, so it
///   moves to another thread where its value and its allocator move.
// SAFETY: the holder is the block's only holder, and no other thread reads
// the block.
unsafe impl<T, A> Send for Unique<T, A>
where
    T: Send,
    A: Allocator + Send,
{
}

/// # Safety
/// - unsafe invariants: a shared borrow of a unique holder reads the value
///   alone, as a shared borrow of a `Box` does.
// SAFETY: a shared borrow reads the value, which is `Sync`.
unsafe impl<T, A> Sync for Unique<T, A>
where
    T: Sync,
    A: Allocator + Sync,
{
}

/// # Safety
/// - unsafe invariants: holders on two threads read one value and drop it on
///   either, so the value is `Send` and `Sync`, as `std`'s `Arc` asks.
// SAFETY: the count is atomic, and the value is `Send` and `Sync`.
unsafe impl<T, A> Send for Shared<T, A>
where
    T: Send + Sync,
    A: Allocator + Send,
{
}

/// # Safety
/// - unsafe invariants: a shared borrow of a holder clones it on another
///   thread, so the value is `Send` and `Sync`, as `std`'s `Arc` asks.
// SAFETY: the count is atomic, and the value is `Send` and `Sync`.
unsafe impl<T, A> Sync for Shared<T, A>
where
    T: Send + Sync,
    A: Allocator + Sync,
{
}
