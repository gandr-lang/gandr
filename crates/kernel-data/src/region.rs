//! A region: values in buckets under a budget, whose ids carry the region's
//! brand. A scope brands the region, so no id leaves the scope. Three
//! crossings move an id between regions, and nothing else does: [`Adopt`] at a
//! fork, the fold's translation at a join, and the export of a durable [`Key`]
//! with its checked import, [`Region::seat`].
//!
//! The scope hands its body the region and one [`Mint`]. Each id takes the
//! mint, and [`Region::fork`] borrows it for the fork's whole life. So the
//! parent makes no id while a child lives. Each id of the parent that a child
//! can name thus lies in the child's frozen prefix, and `adopt` is the id
//! itself.
//!
//! A region takes the allocator below it as a parameter, `Global` by default,
//! and draws its buckets from it. A borrow of a region is itself an
//! allocator: it draws chunks of bytes from the allocator below under the same
//! budget, and frees them all when the region ends. So the vectors, tables and
//! strings of one check live inside the region.

use alloc::alloc::Global;
use alloc::boxed::Box;
use alloc::vec::Vec;
use core::alloc::AllocError;
use core::alloc::Allocator;
use core::alloc::Layout;
use core::cell::Cell;
use core::cell::OnceCell;
use core::cell::RefCell;
use core::fmt;
use core::marker::PhantomData;
use core::mem::size_of;
use core::num::NonZero;
use core::ptr::NonNull;

use anodized::spec;

/// An invariant brand: no region's ids read as another region's.
type Brand<'region> = PhantomData<fn(&'region ()) -> &'region ()>;

/// The slots of the first bucket of a layer. Each later bucket doubles it.
const FIRST: u32 = 64;

/// The binary logarithm of [`FIRST`].
const FIRST_LOG: u32 = 6;

/// The buckets of a layer: enough for each relative index that a `u32`
/// holds.
const BUCKETS: usize = 27;

/// The bytes of a chunk of the allocator face, unless one block needs more.
const CHUNK: usize = 4_096;

/// The alignment of each chunk of the allocator face, unless one block needs
/// more.
const CHUNK_ALIGN: usize = 16;

/// The bytes that a region may draw for its buckets.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Budget(usize);

impl From<usize> for Budget
{
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bytes: usize) -> Self
    {
        Self(bytes)
    }
}

/// A region's refusal: its budget or its offsets cannot hold one more value.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Exhausted
{
    /// The budget of the region that refuses.
    budget: Budget,
}

impl fmt::Display for Exhausted
{
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(
            f,
            "the region's budget of {} bytes holds no more values",
            self.budget.0
        )
    }
}

impl core::error::Error for Exhausted
{
}

/// A value's offset in the id space of its region.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Offset(u32);

/// A count of the values of a layer, or a value's index among them.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Count(u32);

/// A bucket's index among the buckets of a layer.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Bucket(u32);

/// Where a layer keeps the value of one index: its bucket, and the slot in
/// it.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Place
{
    /// The bucket.
    bucket: Bucket,
    /// The slot in the bucket.
    within: usize,
}

impl Place
{
    /// The place of the value at `index` in a layer. Bucket `b` holds
    /// `FIRST << b` slots, and starts past the slots of each bucket before
    /// it.
    ///
    /// # Specification
    /// - ensures: two indices give two places, and the slot lies inside its
    ///   bucket.
    /// - panics: none.
    /// - executable: none — the first clause ranges over every pair of indices.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — values minted across two buckets read back at their
    ///   ids, which a place map that sends two indices to one slot refuses.
    /// - witness: `tests::region::a_region_reads_each_value_at_its_id_and_refuses_past_its_budget`
    fn of(index: Count) -> Option<Self>
    {
        let shifted = index.0.checked_add(FIRST)?;
        let top = shifted.checked_ilog2()?;
        let bucket = top.checked_sub(FIRST_LOG)?;
        let within = shifted.checked_sub(1_u32.checked_shl(top)?)?;
        Some(Self {
            bucket: Bucket(bucket),
            within: usize::try_from(within).ok()?,
        })
    }
}

impl Bucket
{
    /// The slots of this bucket.
    ///
    /// # Specification
    /// trivial.
    fn slots(self) -> Option<Count>
    {
        FIRST.checked_shl(self.0).map(Count)
    }
}

/// The durable key of a value: its offset, with no brand. It is the one form
/// of an id that outlives its scope. [`Region::seat`] reads it back, and a key
/// that the region does not hold is refused.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Key(u32);

impl From<u32> for Key
{
    /// # Specification
    /// trivial.
    #[inline]
    fn from(offset: u32) -> Self
    {
        Self(offset)
    }
}

impl From<Key> for u32
{
    /// # Specification
    /// trivial.
    #[inline]
    fn from(key: Key) -> Self
    {
        key.0
    }
}

/// The id of a value in the region of brand `'region`.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Id<'region>
{
    /// The value's offset in the region's id space.
    offset: Offset,
    /// The region's brand.
    brand: Brand<'region>,
}

impl Id<'_>
{
    /// The durable key of the value: the export, which is always safe.
    ///
    /// # Specification
    /// - ensures: the key holds the id's offset, so [`Region::seat`] of it in
    ///   this region gives this id.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a key of each of two values seats back as its own id,
    ///   and a key past the region is refused.
    /// - witness: `tests::region::a_key_seats_back_in_its_region_and_a_key_past_it_is_refused`
    #[spec(ensures: |ret| ret.0 == self.offset.0)]
    #[inline]
    #[must_use]
    pub fn key(self) -> Key
    {
        Key(self.offset.0)
    }
}

/// The one right to make ids of brand `'region`. It is neither `Copy` nor
/// `Clone`, and only [`scoped`] and [`Region::fork`] make one.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Debug)]
pub struct Mint<'region>
{
    /// The region's brand.
    brand: Brand<'region>,
}

/// The crossing at a fork: an id of the parent, read as the child's.
///
/// A fork hands one to its child. The parent makes no id while the child
/// lives, so each id of the parent lies below the child's mark, in its frozen
/// prefix.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct Adopt<'parent, 'child>
{
    /// The two brands.
    brands: PhantomData<(Brand<'parent>, Brand<'child>)>,
}

impl<'parent, 'child> Adopt<'parent, 'child>
{
    /// The parent's id under the child's brand: the id itself.
    ///
    /// # Specification
    /// - ensures: the result keeps the offset of `id`, so the child reads at it
    ///   the value that the parent reads at `id`.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a child reads a value of the parent through the
    ///   adopted id, and the child's own first id is apart from it.
    /// - witness: `tests::region::a_child_reads_a_value_of_its_parent_through_adopt`
    #[spec(ensures: |ret| ret.offset == id.offset)]
    #[inline]
    #[must_use]
    pub fn adopt(
        self,
        id: Id<'parent>,
    ) -> Id<'child>
    {
        Id {
            offset: id.offset,
            brand: PhantomData,
        }
    }
}

/// A family of values indexed by a brand: the same value under each brand.
/// A fork's result is such a value, and the join reads it under the parent's
/// brand.
///
/// # Specification
/// - requires: `rebrand` reads each id of the value through `translate` and
///   changes nothing else.
pub trait Branded
{
    /// The value under the brand `'region`.
    type Of<'region>;

    /// The value under the brand `'to`, each id read through `translate`.
    ///
    /// # Specification
    /// - ensures: the value with each of its ids read through `translate`, and
    ///   nothing else changed.
    /// - panics: none.
    /// - executable: none — the body is each implementor's, and no predicate
    ///   compares a value across two brands.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an id that a child answers reads in the parent the
    ///   value the child minted at it.
    /// - witness: `tests::region::a_fork_that_agrees_folds_its_suffix_at_the_offsets_it_minted`
    fn rebrand<'from, 'to, Translate>(
        value: Self::Of<'from>,
        translate: &Translate,
    ) -> Self::Of<'to>
    where
        Translate: Fn(Id<'from>) -> Id<'to>;
}

impl Branded for ()
{
    type Of<'region> = ();

    /// # Specification
    /// trivial.
    #[inline]
    fn rebrand<'from, 'to, Translate>(
        (): Self::Of<'from>,
        _translate: &Translate,
    ) -> Self::Of<'to>
    where
        Translate: Fn(Id<'from>) -> Id<'to>,
    {
    }
}

impl Branded for Id<'static>
{
    type Of<'region> = Id<'region>;

    /// # Specification
    /// trivial.
    #[inline]
    fn rebrand<'from, 'to, Translate>(
        value: Id<'from>,
        translate: &Translate,
    ) -> Id<'to>
    where
        Translate: Fn(Id<'from>) -> Id<'to>,
    {
        translate(value)
    }
}

impl<Family> Branded for Option<Family>
where
    Family: Branded,
{
    type Of<'region> = Option<Family::Of<'region>>;

    /// # Specification
    /// trivial.
    #[inline]
    fn rebrand<'from, 'to, Translate>(
        value: Self::Of<'from>,
        translate: &Translate,
    ) -> Self::Of<'to>
    where
        Translate: Fn(Id<'from>) -> Id<'to>,
    {
        value.map(|inner| Family::rebrand(inner, translate))
    }
}

/// The free bytes of the newest chunk of an allocator face: its next byte,
/// and the address past its last byte.
#[derive(Clone, Copy, Debug)]
struct Cursor
{
    /// The next free byte.
    next: NonNull<u8>,
    /// The address past the chunk's last byte.
    end: NonNull<u8>,
}

/// The chunks of one layer's allocator face, each drawn from the allocator
/// below, and each released when the layer drops.
struct Bytes<Below>
where
    Below: Allocator + Clone,
{
    /// The allocator below: it draws each chunk and each bucket.
    allocator: Below,
    /// The free bytes of the newest chunk; `None` before the first.
    cursor: Cell<Option<Cursor>>,
    /// Each chunk with its layout, for its release.
    chunks: RefCell<Vec<(NonNull<u8>, Layout), Below>>,
}

impl<Below> Bytes<Below>
where
    Below: Allocator + Clone,
{
    /// No chunk yet, over `allocator`.
    ///
    /// # Specification
    /// trivial.
    fn new(allocator: Below) -> Self
    {
        Self {
            chunks: RefCell::new(Vec::new_in(allocator.clone())),
            allocator,
            cursor: Cell::new(None),
        }
    }

    /// A block of `layout` from the free bytes of the newest chunk.
    ///
    /// # Specification
    /// - ensures: on `Some`, a block of `layout` that lies in the newest chunk
    ///   past each block before it, and the cursor past the block; on `None`,
    ///   the cursor unchanged.
    /// - panics: none.
    /// - executable: none — a block is an address range, and no predicate reads
    ///   the blocks before it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a vector grown in the region keeps each element it
    ///   holds, which a block that overlaps an earlier one breaks under Miri.
    /// - witness: `tests::region::a_vector_in_a_region_lives_in_its_bytes_and_is_refused_past_its_budget`
    fn carve(
        &self,
        layout: Layout,
    ) -> Option<NonNull<[u8]>>
    {
        let cursor = self.cursor.get()?;
        let start = cursor
            .next
            .addr()
            .get()
            .checked_next_multiple_of(layout.align())?;
        let end = start.checked_add(layout.size())?;
        if end > cursor.end.addr().get() {
            return None;
        }
        self.cursor.set(Some(Cursor {
            next: cursor.next.with_addr(NonZero::new(end)?),
            end: cursor.end,
        }));
        Some(NonNull::slice_from_raw_parts(
            cursor.next.with_addr(NonZero::new(start)?),
            layout.size(),
        ))
    }

    /// Draw a chunk of `layout` from the allocator below, and set the cursor
    /// at its first byte.
    ///
    /// # Specification
    /// - ensures: on `Ok`, the chunk recorded for its release and the cursor
    ///   over its bytes.
    /// - fails: [`AllocError`] when the allocator below refuses the chunk, or
    ///   the record of chunks cannot grow.
    /// - panics: none.
    /// - executable: none — the chunk is a fresh allocation, which no predicate
    ///   reads before the call.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a vector that outgrows one chunk keeps its elements,
    ///   and Miri finds no leak of a chunk.
    /// - witness: `tests::region::a_vector_in_a_region_lives_in_its_bytes_and_is_refused_past_its_budget`
    fn draw(
        &self,
        layout: Layout,
    ) -> Result<(), AllocError>
    {
        let mut chunks = self.chunks.try_borrow_mut().ok().ok_or(AllocError)?;
        chunks.try_reserve(1_usize).ok().ok_or(AllocError)?;
        let chunk = self.allocator.allocate(layout)?.cast::<u8>();
        chunks.push((chunk, layout));
        let end = chunk
            .addr()
            .get()
            .checked_add(layout.size())
            .and_then(NonZero::new)
            .ok_or(AllocError)?;
        self.cursor.set(Some(Cursor {
            next: chunk,
            end: chunk.with_addr(end),
        }));
        Ok(())
    }
}

impl<Below> Drop for Bytes<Below>
where
    Below: Allocator + Clone,
{
    /// # Specification
    /// - ensures: each chunk returns to the allocator below, once.
    /// - panics: none.
    /// - executable: none — a released chunk has no state that a predicate
    ///   could read.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — Miri reports a leak of a chunk that the drop keeps,
    ///   and a double release of one that it frees twice.
    /// - witness: `tests::region::a_vector_in_a_region_lives_in_its_bytes_and_is_refused_past_its_budget`
    fn drop(&mut self)
    {
        for &(chunk, layout) in &*self.chunks.get_mut() {
            // SAFETY: `Bytes::draw` drew `chunk` from `self.allocator` with
            // `layout`, and only this drop releases it, once. Each block of
            // the chunk is borrowed from a `&Region` whose borrow ends before
            // the layer that owns these bytes drops.
            unsafe {
                self.allocator.deallocate(chunk, layout);
            }
        }
    }
}

/// The storage of one region: its own values from `base` on, over the frozen
/// prefix of the region it forked from.
struct Layer<'below, Value, Below>
where
    Below: Allocator + Clone,
{
    /// The frozen prefix: every offset below `base`.
    below: Option<&'below Self>,
    /// The first offset of this layer's own values.
    base: Offset,
    /// The values this layer holds.
    len: Cell<Count>,
    /// The bytes this layer may draw.
    budget: Budget,
    /// The bytes this layer drew.
    drawn: Cell<Budget>,
    /// The buckets, each drawn at its first value.
    buckets: [OnceCell<Box<[OnceCell<Value>], Below>>; BUCKETS],
    /// The allocator face's chunks, over the allocator below.
    bytes: Bytes<Below>,
}

impl<'below, Value, Below> Layer<'below, Value, Below>
where
    Below: Allocator + Clone,
{
    /// An empty layer from `base` on, over `below`, that draws from
    /// `allocator`.
    ///
    /// # Specification
    /// trivial.
    fn new(
        below: Option<&'below Self>,
        base: Offset,
        budget: Budget,
        allocator: Below,
    ) -> Self
    {
        Self {
            below,
            base,
            len: Cell::new(Count(0_u32)),
            budget,
            drawn: Cell::new(Budget(0_usize)),
            buckets: [const { OnceCell::new() }; BUCKETS],
            bytes: Bytes::new(allocator),
        }
    }

    /// A block of `layout` for the allocator face: from the newest chunk, or
    /// from a fresh chunk under the budget.
    ///
    /// # Specification
    /// - ensures: on `Ok`, a block of `layout` that no other live block
    ///   overlaps, and that lives until the layer drops; the drawn bytes grow
    ///   by each fresh chunk's.
    /// - fails: [`AllocError`] when a fresh chunk passes the remaining budget,
    ///   or the allocator below refuses it.
    /// - panics: none.
    /// - executable: none — a block is an address range, and no predicate reads
    ///   the blocks before it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a vector grown in the region keeps its elements, and
    ///   a reserve past the budget is refused.
    /// - witness: `tests::region::a_vector_in_a_region_lives_in_its_bytes_and_is_refused_past_its_budget`
    fn block(
        &self,
        layout: Layout,
    ) -> Result<NonNull<[u8]>, AllocError>
    {
        if let Some(block) = self.bytes.carve(layout) {
            return Ok(block);
        }
        let bytes = layout
            .size()
            .checked_add(layout.align())
            .ok_or(AllocError)?
            .max(CHUNK);
        let chunk = Layout::from_size_align(bytes, layout.align().max(CHUNK_ALIGN))
            .ok()
            .ok_or(AllocError)?;
        if Budget(bytes) > self.remaining() {
            return Err(AllocError);
        }
        self.bytes.draw(chunk)?;
        self.drawn
            .set(Budget(self.drawn.get().0.saturating_add(bytes)));
        self.bytes.carve(layout).ok_or(AllocError)
    }

    /// The refusal of this layer.
    ///
    /// # Specification
    /// trivial.
    const fn exhausted(&self) -> Exhausted
    {
        Exhausted {
            budget: self.budget,
        }
    }

    /// The first offset past every value this layer reads.
    ///
    /// # Specification
    /// trivial.
    fn extent(&self) -> Result<Offset, Exhausted>
    {
        self.base
            .0
            .checked_add(self.len.get().0)
            .map(Offset)
            .ok_or_else(|| self.exhausted())
    }

    /// The bytes this layer may still draw.
    ///
    /// # Specification
    /// trivial.
    fn remaining(&self) -> Budget
    {
        Budget(self.budget.0.saturating_sub(self.drawn.get().0))
    }

    /// The value at `offset`: in the first layer, from this one down, whose
    /// base is at most `offset`.
    ///
    /// # Specification
    /// - ensures: the value that [`Layer::push`] stored at `offset`, in this
    ///   layer or in its frozen prefix; `None` past every value.
    /// - panics: none.
    /// - executable: none — the predicate would repeat the lookup it checks.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — values minted across two buckets read back at their
    ///   ids, and a child reads its parent's value below its base.
    /// - witness: `tests::region::a_region_reads_each_value_at_its_id_and_refuses_past_its_budget`
    /// - witness: `tests::region::a_child_reads_a_value_of_its_parent_through_adopt`
    fn get(
        &self,
        offset: Offset,
    ) -> Option<&Value>
    {
        let layer = core::iter::successors(Some(self), |layer| layer.below)
            .find(|layer| layer.base <= offset)?;
        let place = Place::of(Count(offset.0.checked_sub(layer.base.0)?))?;
        layer
            .buckets
            .get(usize::try_from(place.bucket.0).ok()?)?
            .get()?
            .get(place.within)?
            .get()
    }

    /// The bytes that the buckets for `count` more values draw.
    ///
    /// # Specification
    /// - ensures: the bytes of each bucket that the next `count` values reach
    ///   and that this layer has not drawn; `None` when they overflow.
    /// - panics: none.
    /// - executable: none — the predicate would repeat the sum it checks.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a budget that holds one bucket refuses the value that
    ///   needs the second.
    /// - witness: `tests::region::a_region_reads_each_value_at_its_id_and_refuses_past_its_budget`
    fn draw_for(
        &self,
        count: Count,
    ) -> Option<Budget>
    {
        let first = self.len.get().0;
        let last = first.checked_add(count.0)?.checked_sub(1_u32)?;
        let from = Place::of(Count(first))?.bucket.0;
        let to = Place::of(Count(last))?.bucket.0;
        let mut bytes = 0_usize;
        for bucket in from ..= to {
            let drawn = self
                .buckets
                .get(usize::try_from(bucket).ok()?)?
                .get()
                .is_some();
            if !drawn {
                let slots = usize::try_from(Bucket(bucket).slots()?.0).ok()?;
                bytes = bytes.checked_add(slots.checked_mul(size_of::<OnceCell<Value>>())?)?;
            }
        }
        Some(Budget(bytes))
    }

    /// Append `value` at the next offset and answer the offset.
    ///
    /// # Specification
    /// - ensures: on `Ok(offset)`, [`Layer::get`] of `offset` gives `value` and
    ///   the layer holds one value more.
    /// - fails: [`Exhausted`] when the budget cannot draw the value's bucket,
    ///   or the offsets are full.
    /// - panics: none.
    /// - executable: none — the value moves into the layer, and `Value` has no
    ///   equality that a predicate could compare it by.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — values minted in order read back at their ids, and
    ///   the value past the budget is refused.
    /// - witness: `tests::region::a_region_reads_each_value_at_its_id_and_refuses_past_its_budget`
    fn push(
        &self,
        value: Value,
    ) -> Result<Offset, Exhausted>
    {
        let index = self.len.get();
        let offset = self.extent()?;
        let next = index
            .0
            .checked_add(1_u32)
            .map(Count)
            .ok_or_else(|| self.exhausted())?;
        let place = Place::of(index).ok_or_else(|| self.exhausted())?;
        let cell = usize::try_from(place.bucket.0)
            .ok()
            .and_then(|bucket| self.buckets.get(bucket))
            .ok_or_else(|| self.exhausted())?;
        let slots = cell
            .get()
            .map(AsRef::as_ref)
            .map_or_else(|| self.draw(cell, place.bucket), Ok)?;
        let slot = slots.get(place.within).ok_or_else(|| self.exhausted())?;
        let _stored: &Value = slot.get_or_init(|| value);
        self.len.set(next);
        Ok(offset)
    }

    /// Draw `bucket` into `cell` under the budget, and answer its slots.
    ///
    /// # Specification
    /// - ensures: on `Ok`, the bucket's empty slots, and the layer's drawn
    ///   bytes grow by the bucket's.
    /// - fails: [`Exhausted`] when the bucket's bytes pass the remaining
    ///   budget.
    /// - panics: none.
    /// - fails: [`Exhausted`] also when the allocator below refuses the bucket.
    /// - executable: none — the slots are a fresh allocation, which no
    ///   predicate reads before the call.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a budget that holds one bucket refuses the value that
    ///   needs the second.
    /// - witness: `tests::region::a_region_reads_each_value_at_its_id_and_refuses_past_its_budget`
    fn draw<'cell>(
        &self,
        cell: &'cell OnceCell<Box<[OnceCell<Value>], Below>>,
        bucket: Bucket,
    ) -> Result<&'cell [OnceCell<Value>], Exhausted>
    {
        let bytes = self
            .draw_for(Count(1_u32))
            .ok_or_else(|| self.exhausted())?;
        if bytes > self.remaining() {
            return Err(self.exhausted());
        }
        let count = bucket
            .slots()
            .and_then(|count| usize::try_from(count.0).ok())
            .ok_or_else(|| self.exhausted())?;
        let mut fresh = Vec::new_in(self.bytes.allocator.clone());
        fresh
            .try_reserve_exact(count)
            .ok()
            .ok_or_else(|| self.exhausted())?;
        fresh.extend(core::iter::repeat_with(OnceCell::new).take(count));
        let fresh = fresh.into_boxed_slice();
        self.drawn
            .set(Budget(self.drawn.get().0.saturating_add(bytes.0)));
        Ok(cell.get_or_init(|| fresh))
    }

    /// This layer's own values, in the order of their offsets. Each filled
    /// slot lies below `len`, and each slot past it is empty.
    ///
    /// # Specification
    /// - ensures: each value of the layer once, in the order of its offset.
    /// - panics: none.
    /// - executable: none — the opaque iterator cannot be named by the
    ///   postcondition, or consumed without a change of its output.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a child's two values read in the parent at the
    ///   offsets the child minted them at.
    /// - witness: `tests::region::a_fork_that_agrees_folds_its_suffix_at_the_offsets_it_minted`
    fn into_values(self) -> impl Iterator<Item = Value>
    {
        self.buckets
            .into_iter()
            .filter_map(OnceCell::into_inner)
            .flat_map(|slots| {
                slots
                    .into_vec()
                    .into_iter()
                    .filter_map(OnceCell::into_inner)
            })
    }
}

/// A region of values of type `Value` under the brand `'region`.
///
/// A region draws its buckets under a budget, and refuses a value past it. It
/// hands out `&Value` for each of its ids, and no value moves while the region
/// lives.
///
/// # Specification
/// - requires: none.
/// - ensures: each id of brand `'region` names a value of this region or of its
///   frozen prefix.
/// - panics: none.
/// - executable: none — a data declaration has no call boundary; the brand
///   states the clause, and the constructors keep it.
///
/// # Adequacy
/// - hypothesis: L3 — values minted in order read back at their ids, and a
///   budget that holds one bucket refuses the value past it.
/// - witness: `tests::region::a_region_reads_each_value_at_its_id_and_refuses_past_its_budget`
pub struct Region<'region, Value, Below = Global>
where
    Below: Allocator + Clone,
{
    /// The values and the frozen prefix, owned by the scope or the fork that
    /// made the region, so a join can take them after the child's body.
    layer: &'region Layer<'region, Value, Below>,
    /// The region's brand.
    brand: Brand<'region>,
}

/// Brand a region under `budget` for `body`, with its one mint.
///
/// No id of the region leaves the scope:
///
/// ```compile_fail
/// use gandr_kernel_data::Budget;
/// use gandr_kernel_data::scoped;
///
/// let leaked = scoped(Budget::from(4096_usize), |region, mut mint| {
///     region.mint(&mut mint, 7_u64)
/// });
/// ```
///
/// # Specification
/// - ensures: the body's answer, which names no id of the region.
/// - panics: none.
/// - executable: none — the answer is generic, and the brand states the clause
///   at compile time.
///
/// # Adequacy
/// - hypothesis: L3 — a scope reads back what its body minted, and the example
///   above, which returns an id from the scope, does not compile.
/// - witness: `tests::region::a_region_reads_each_value_at_its_id_and_refuses_past_its_budget`
#[inline]
pub fn scoped<Value, Answer, Body>(
    budget: Budget,
    body: Body,
) -> Answer
where
    Body: for<'region> FnOnce(&'region Region<'region, Value>, Mint<'region>) -> Answer,
{
    scoped_in(budget, Global, body)
}

/// Brand a region under `budget` for `body`, with its one mint, over the
/// allocator `below`: each bucket and each chunk of the region's bytes comes
/// from `below`.
///
/// # Specification
/// - ensures: the body's answer, which names no id of the region; each
///   allocation of the region returns to `below` when the scope ends.
/// - panics: none.
/// - executable: none — the answer is generic, and the brand states the clause
///   at compile time.
///
/// # Adequacy
/// - hypothesis: L3 — a region over a region draws its buckets from the region
///   below, and the budget below refuses the bucket past it.
/// - witness: `tests::region::a_region_over_a_region_draws_its_buckets_from_the_region_below`
#[inline]
pub fn scoped_in<Value, Below, Answer, Body>(
    budget: Budget,
    below: Below,
    body: Body,
) -> Answer
where
    Below: Allocator + Clone,
    Body: for<'region> FnOnce(&'region Region<'region, Value, Below>, Mint<'region>) -> Answer,
{
    let layer = Layer::new(None, Offset(0_u32), budget, below);
    let region = Region {
        layer: &layer,
        brand: PhantomData,
    };
    body(&region, Mint { brand: PhantomData })
}

impl<'region, Value, Below> Region<'region, Value, Below>
where
    Below: Allocator + Clone,
{
    /// Append `value` and answer its id.
    ///
    /// # Specification
    /// - ensures: on `Ok(id)`, [`Region::get`] of the id gives `value`.
    /// - fails: [`Exhausted`] when the budget cannot draw the bucket the value
    ///   needs, or the region's offsets are full.
    /// - panics: none.
    /// - executable: none — the value moves into the region, and `Value` has no
    ///   equality that a predicate could compare it by.
    ///
    /// # Errors
    /// [`Exhausted`] past the budget or past the last offset.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — values minted in order read back at their ids, and
    ///   the value past the budget is refused.
    /// - witness: `tests::region::a_region_reads_each_value_at_its_id_and_refuses_past_its_budget`
    #[inline]
    pub fn mint(
        &self,
        _mint: &mut Mint<'region>,
        value: Value,
    ) -> Result<Id<'region>, Exhausted>
    {
        let offset = self.layer.push(value)?;
        Ok(Id {
            offset,
            brand: PhantomData,
        })
    }

    /// The value at `id`. An id of this region always names a value; the
    /// option is the lookup's, and the brand keeps it `Some`.
    ///
    /// # Specification
    /// - ensures: the value that [`Region::mint`] stored at `id`, in this
    ///   region or its frozen prefix.
    /// - panics: none.
    /// - executable: none — the predicate would repeat the lookup it checks.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each of the values minted across two buckets reads
    ///   back at its id.
    /// - witness: `tests::region::a_region_reads_each_value_at_its_id_and_refuses_past_its_budget`
    #[inline]
    #[must_use]
    pub fn get(
        &self,
        id: Id<'region>,
    ) -> Option<&Value>
    {
        self.layer.get(id.offset)
    }

    /// The checked import: the id of `key` when this region holds it.
    ///
    /// # Specification
    /// - ensures: `Some` of the id whose key is `key` when its offset is below
    ///   the region's extent; `None` otherwise, a refusal.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a key of each of two values seats back as its own id,
    ///   and a key past the region is refused.
    /// - witness: `tests::region::a_key_seats_back_in_its_region_and_a_key_past_it_is_refused`
    #[spec(ensures: |ret| ret.is_none_or(|id| id.key() == key))]
    #[inline]
    #[must_use]
    pub fn seat(
        &self,
        key: Key,
    ) -> Option<Id<'region>>
    {
        let extent = self.layer.extent().ok()?;
        (key.0 < extent.0).then_some(Id {
            offset: Offset(key.0),
            brand: PhantomData,
        })
    }

    /// Fork a child region over this region's frozen prefix, and fold its
    /// suffix back when its body agrees.
    ///
    /// The fork borrows `mint` for its whole life, so this region makes no id
    /// while the child lives. The child takes this region's remaining budget,
    /// its own mint and an [`Adopt`]. A body that answers `None` disagrees,
    /// and the child's suffix drops whole. A body that answers `Some` agrees:
    /// the join appends the child's suffix at the offsets the child minted it
    /// at, and reads the answer under this region's brand.
    ///
    /// No id of the child leaves the fork but through the join:
    ///
    /// ```compile_fail
    /// use gandr_kernel_data::Budget;
    /// use gandr_kernel_data::scoped;
    ///
    /// scoped(Budget::from(4096_usize), |region, mut mint| {
    ///     let mut leaked = None;
    ///     let _ = region.fork::<(), _>(&mut mint, |child, mut own, _adopt| {
    ///         leaked = child.mint(&mut own, 7_u64).ok();
    ///         Some(())
    ///     });
    /// });
    /// ```
    ///
    /// # Specification
    /// - ensures: `Ok(None)` and this region unchanged when the body answers
    ///   `None`; `Ok(Some(answer))` when it answers `Some`, each value of the
    ///   child at its own offset in this region, and each id of the answer at
    ///   the offset it had.
    /// - fails: [`Exhausted`] when this region's budget cannot draw the buckets
    ///   the suffix needs; the suffix then drops whole.
    /// - panics: none.
    /// - executable: none — the answer is generic, and the child's values have
    ///   no equality that a predicate could compare them by.
    ///
    /// # Errors
    /// [`Exhausted`] when the join cannot hold the child's suffix.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an agreeing child's values read in the parent at the
    ///   ids the join gives, and the parent's next id follows them; a
    ///   disagreeing child leaves the parent's next id at the mark.
    /// - witness: `tests::region::a_fork_that_agrees_folds_its_suffix_at_the_offsets_it_minted`
    /// - witness: `tests::region::a_fork_that_disagrees_drops_its_suffix_whole`
    #[inline]
    pub fn fork<Family, Body>(
        &self,
        _mint: &mut Mint<'region>,
        body: Body,
    ) -> Result<Option<Family::Of<'region>>, Exhausted>
    where
        Family: Branded,
        Body: for<'child> FnOnce(
            &'child Region<'child, Value, Below>,
            Mint<'child>,
            Adopt<'region, 'child>,
        ) -> Option<Family::Of<'child>>,
    {
        let mark = self.layer.extent()?;
        let layer = Layer::new(
            Some(self.layer),
            mark,
            self.layer.remaining(),
            self.layer.bytes.allocator.clone(),
        );
        let child = Region {
            layer: &layer,
            brand: PhantomData,
        };
        let Some(answer) = body(&child, Mint { brand: PhantomData }, Adopt {
            brands: PhantomData,
        })
        else {
            return Ok(None);
        };
        let joined = Family::rebrand(answer, &Self::join());
        self.fold(layer)?;
        Ok(Some(joined))
    }

    /// The fold's translation at a join: an id of the child, read as this
    /// region's. This region made no id while the child lived, so its next
    /// offset at the join is the child's mark, and each value of the child
    /// keeps its offset.
    ///
    /// # Specification
    /// trivial.
    fn join<'child>() -> impl Fn(Id<'child>) -> Id<'region>
    {
        |id| Id {
            offset: id.offset,
            brand: PhantomData,
        }
    }

    /// Append the child's own values, whole or not at all.
    ///
    /// # Specification
    /// - ensures: on `Ok`, each value of `child` at the offset the child minted
    ///   it at; on `Err`, this region unchanged.
    /// - fails: [`Exhausted`] when this region's remaining budget cannot draw
    ///   the buckets of the child's values.
    /// - panics: none.
    /// - executable: none — the values move, and `Value` has no equality that a
    ///   predicate could compare them by.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a child's values read in the parent at the offsets
    ///   the child minted them at, and the parent's next id follows them.
    /// - witness: `tests::region::a_fork_that_agrees_folds_its_suffix_at_the_offsets_it_minted`
    fn fold(
        &self,
        child: Layer<'_, Value, Below>,
    ) -> Result<(), Exhausted>
    {
        let count = child.len.get();
        if count == Count(0_u32) {
            return Ok(());
        }
        let bytes = self
            .layer
            .draw_for(count)
            .ok_or_else(|| self.layer.exhausted())?;
        if bytes > self.layer.remaining() {
            return Err(self.layer.exhausted());
        }
        for value in child.into_values() {
            let _offset: Offset = self.layer.push(value)?;
        }
        Ok(())
    }
}

// SAFETY: each block lies in a chunk of the region's layer, and the layer
// outlives each borrow `&Region` of it, so a block stays valid while any copy
// of this allocator lives. The cursor only moves forward, so no two live
// blocks overlap. A copy of `&Region` is the same region, so a block from one
// copy may return through another.
unsafe impl<Value, Below> Allocator for &Region<'_, Value, Below>
where
    Below: Allocator + Clone,
{
    /// A block of `layout` from the region's bytes, under its budget.
    ///
    /// # Specification
    /// - ensures: on `Ok`, a block of `layout` that no other live block
    ///   overlaps, and that lives until the region ends.
    /// - fails: [`AllocError`] when a fresh chunk passes the remaining budget,
    ///   or the allocator below refuses it.
    /// - panics: none.
    /// - executable: none — a block is an address range, and no predicate reads
    ///   the blocks before it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a vector grown in the region keeps its elements, and
    ///   a reserve past the budget is refused.
    /// - witness: `tests::region::a_vector_in_a_region_lives_in_its_bytes_and_is_refused_past_its_budget`
    #[inline]
    fn allocate(
        &self,
        layout: Layout,
    ) -> Result<NonNull<[u8]>, AllocError>
    {
        self.layer.block(layout)
    }

    /// Keep the block: the region frees each of its chunks when it ends.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    unsafe fn deallocate(
        &self,
        _block: NonNull<u8>,
        _layout: Layout,
    )
    {
    }
}
