//! A region: values in buckets under a budget, whose ids carry the region's
//! brand. A scope brands the region, so no id leaves the scope. Three
//! crossings move an id between regions, and nothing else does: [`Adopt`] at a
//! fork, the fold's [`Translation`] at a join, and the export of a durable
//! [`Key`] with its checked import, [`Region::seat`].
//!
//! A region holds the values of one or more families in one id space. An id
//! names its family by a phantom kind, so an id of one family is not an id of
//! another, and each family crosses by the same three crossings.
//!
//! The scope hands its body the region and one [`Mint`]. Each id takes the
//! mint, and [`Region::forks`] borrows it for the fork's whole life. So the
//! parent makes no id while a child lives. Each id of the parent that a child
//! can name thus lies in the frozen prefix, and `adopt` is the id itself. The
//! children of one fork read that prefix by reference, each on its own
//! thread, and the glue moves each agreeing suffix past the ones before it.
//!
//! A region takes the allocator below it as a parameter, `Global` by default,
//! and draws its buckets from it. A borrow of a region is itself an
//! allocator: it draws chunks of bytes from the allocator below under the same
//! budget, and frees them all when the region ends. So the vectors, tables and
//! strings of one check live inside the region.
//!
//! # Items
//!
//! | Crossing | Where | Form |
//! | -------- | ----- | ---- |
//! | [`Adopt::adopt`] | a fork | the parent's id, read as the child's: the id itself |
//! | [`Translation::translate`] | a join | the child's id, read as the parent's: below the mark the same offset, past it the offset that the glue moved its value to |
//! | [`Id::key`] and [`Region::seat`] | the end of a scope | the durable key's export, and its checked import |
//!
//! # References
//!
//! - `vault:01a178ab-17e5-7352-bc0b-3caa7f1e476c` — anchor: §
//!   storage-programme-region-is-an-allocator. The frozen prefix and a child's
//!   suffix are two regions, and the join folds or drops the suffix. One
//!   allocator with a budget refuses and never aborts. Its handle is one
//!   pointer, with `Global` as the default.
//! - `vault:01a1d7fd-eeb5-7010-80e7-df4d768b6583` — anchor: lines 1 to 3 and 5
//!   of the performance picture. A worker owns its region, what is shared is
//!   frozen, each crossing is explicit, and what was written apart glues again
//!   at the cost of what differs.

use alloc::alloc::Global;
use alloc::boxed::Box;
use alloc::vec;
use alloc::vec::Vec;
use core::alloc::AllocError;
use core::alloc::Allocator;
use core::alloc::Layout;
use core::cell::Cell;
use core::cell::OnceCell;
use core::cell::RefCell;
use core::cmp::Ordering;
use core::convert::Infallible;
use core::fmt;
use core::hash::Hash;
use core::hash::Hasher;
use core::iter::Chain;
use core::iter::Once;
use core::iter::once;
use core::marker::PhantomData;
use core::mem::size_of;
use core::num::NonZero;
use core::num::NonZeroUsize;
use core::ptr::NonNull;
use core::slice;

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

/// The number of children of a fork over one frozen prefix: one or more.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Width(NonZeroUsize);

impl Width
{
    /// The width of the one-child fork.
    pub const ONE: Self = Self(NonZeroUsize::MIN);
}

impl From<NonZeroUsize> for Width
{
    /// # Specification
    /// trivial.
    #[inline]
    fn from(children: NonZeroUsize) -> Self
    {
        Self(children)
    }
}

impl From<Width> for NonZeroUsize
{
    /// # Specification
    /// trivial.
    #[inline]
    fn from(width: Width) -> Self
    {
        width.0
    }
}

/// A child's place among the children of one fork, from zero. The glue
/// folds the suffixes of the children in this order.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Sibling(usize);

impl From<Sibling> for usize
{
    /// # Specification
    /// trivial.
    #[inline]
    fn from(sibling: Sibling) -> Self
    {
        sibling.0
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

/// The move of one child's suffix at the glue: each offset at or past the
/// fork's mark moves past the suffixes that the siblings before the child
/// folded, and each offset below the mark stays.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Shift
{
    /// The first offset of every child's suffix.
    mark: Offset,
    /// The values that the siblings before the child folded.
    by: Count,
}

impl Shift
{
    /// The offset `offset` after the move.
    ///
    /// # Specification
    /// - ensures: `offset` itself below the mark; past it, `offset` moved by
    ///   the folded values. The glue checks that each moved offset fits, so the
    ///   sum does not saturate.
    /// - panics: none.
    /// - executable: none — the predicate would repeat the comparison and the
    ///   sum it checks.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the second of two agreeing children reads in the
    ///   parent past the first child's suffix, and a value of the parent that
    ///   it adopted keeps its offset.
    /// - witness: `tests::region::siblings_over_one_frozen_prefix_glue_their_suffixes_in_order`
    const fn offset(
        self,
        offset: Offset,
    ) -> Offset
    {
        if offset.0 < self.mark.0 {
            offset
        }
        else {
            Offset(offset.0.saturating_add(self.by.0))
        }
    }

    /// The key `key` after the move: what a value of a child's suffix names
    /// at the offset `key`, read where the glue moves it.
    ///
    /// # Specification
    /// - ensures: `key` itself below the mark; past it, `key` moved by the
    ///   values that the siblings before the child folded.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a value of the second agreeing child names a value of
    ///   its own suffix, and reads it in the parent past the first child's
    ///   suffix.
    /// - witness: `tests::region::siblings_over_one_frozen_prefix_glue_their_suffixes_in_order`
    #[spec(ensures: |ret| (key.0 < self.mark.0) == (ret == key) || self.by.0 == 0_u32)]
    #[inline]
    #[must_use]
    pub fn key(
        self,
        key: Key,
    ) -> Key
    {
        Key(self.offset(Offset(key.0)).0)
    }
}

/// A value that names offsets of its own region, by [`Key`].
///
/// The glue of a fork moves each value of a child's suffix past the suffixes
/// of the siblings before it. It reads each key that the value names through
/// the same [`Shift`].
///
/// # Specification
/// - requires: `rebase` reads each key of the value through the shift and
///   changes nothing else.
pub trait Rebase
{
    /// The value with each key it names read through `shift`.
    ///
    /// # Specification
    /// - ensures: the value with each of its keys read through [`Shift::key`],
    ///   and nothing else changed.
    /// - panics: none.
    /// - executable: none — the body is each implementor's, and the trait asks
    ///   no equality of the value.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a value of the second agreeing child names a value of
    ///   its own suffix, and reads it in the parent past the first child's
    ///   suffix.
    /// - witness: `tests::region::siblings_over_one_frozen_prefix_glue_their_suffixes_in_order`
    #[must_use]
    fn rebase(
        self,
        shift: Shift,
    ) -> Self;
}

impl Rebase for ()
{
    /// # Specification
    /// trivial.
    #[inline]
    fn rebase(
        self,
        _shift: Shift,
    ) -> Self
    {
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

/// The id of a value of the family `Kind` in the region of brand `'region`.
///
/// The kind is a phantom. A region of one family takes the kind `()`. In a
/// region of more families, an id of one family does not stand for an id of
/// another:
///
/// ```compile_fail,E0308
/// use gandr_kernel_data::Budget;
/// use gandr_kernel_data::Id;
/// use gandr_kernel_data::scoped;
///
/// #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
/// enum Term {}
/// #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
/// enum Type {}
///
/// scoped(Budget::from(4096_usize), |region, mut mint| {
///     let term: Id<'_, Term> = region.mint(&mut mint, 7_u64).ok()?;
///     let as_type: Id<'_, Type> = term;
///     region.get(as_type).copied()
/// });
/// ```
///
/// # Specification
/// trivial.
pub struct Id<'region, Kind = ()>
{
    /// The value's offset in the region's id space.
    offset: Offset,
    /// The region's brand.
    brand: Brand<'region>,
    /// The value's family: a phantom that asks nothing of `Kind`.
    kind: PhantomData<fn() -> Kind>,
}

// The kind is a phantom, so each trait below reads the offset alone and asks
// nothing of `Kind`, as `PhantomData` asks nothing of its parameter.
impl<Kind> Clone for Id<'_, Kind>
{
    /// # Specification
    /// trivial.
    #[inline]
    fn clone(&self) -> Self
    {
        *self
    }
}

impl<Kind> Copy for Id<'_, Kind>
{
}

impl<Kind> PartialEq for Id<'_, Kind>
{
    /// # Specification
    /// trivial.
    #[inline]
    fn eq(
        &self,
        other: &Self,
    ) -> bool
    {
        self.offset == other.offset
    }
}

impl<Kind> Eq for Id<'_, Kind>
{
}

impl<Kind> PartialOrd for Id<'_, Kind>
{
    /// # Specification
    /// trivial.
    #[inline]
    fn partial_cmp(
        &self,
        other: &Self,
    ) -> Option<Ordering>
    {
        Some(self.cmp(other))
    }
}

impl<Kind> Ord for Id<'_, Kind>
{
    /// # Specification
    /// trivial.
    #[inline]
    fn cmp(
        &self,
        other: &Self,
    ) -> Ordering
    {
        self.offset.cmp(&other.offset)
    }
}

impl<Kind> Hash for Id<'_, Kind>
{
    /// # Specification
    /// trivial.
    #[inline]
    fn hash<State>(
        &self,
        state: &mut State,
    ) where
        State: Hasher,
    {
        self.offset.hash(state);
    }
}

impl<Kind> fmt::Debug for Id<'_, Kind>
{
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.debug_struct("Id").field("offset", &self.offset).finish()
    }
}

impl<Kind> Id<'_, Kind>
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
/// `Clone`, and only [`scoped`] and [`Region::forks`] make one.
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
/// A fork hands one to each child. The parent makes no id while a child
/// lives, so each id of the parent lies below the children's mark, in their
/// frozen prefix.
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
    pub fn adopt<Kind>(
        self,
        id: Id<'parent, Kind>,
    ) -> Id<'child, Kind>
    {
        Id {
            offset: id.offset,
            brand: PhantomData,
            kind: PhantomData,
        }
    }
}

/// The crossing at a join: an id of the child, read as the parent's.
///
/// The glue hands one to [`Branded::rebrand`]. The parent makes no id while
/// the children live, so each id below the mark keeps its offset, and each id
/// of the child's suffix moves past the suffixes that the siblings before it
/// folded.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug)]
pub struct Translation<'child, 'parent>
{
    /// The move of the child's suffix.
    shift: Shift,
    /// The two brands.
    brands: PhantomData<(Brand<'child>, Brand<'parent>)>,
}

impl<'child, 'parent> Translation<'child, 'parent>
{
    /// The child's id under the parent's brand: the id at the offset where the
    /// glue moved its value.
    ///
    /// # Specification
    /// - ensures: the offset of `id` below the mark, so the parent reads at it
    ///   the value it adopted; past the mark, the offset moved by the shift, so
    ///   the parent reads at it the value that the child minted at `id`.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an id that a child answers reads in the parent the
    ///   value the child minted at it, and the second of two agreeing children
    ///   reads past the first child's suffix.
    /// - witness: `tests::region::a_fork_that_agrees_folds_its_suffix_at_the_offsets_it_minted`
    /// - witness: `tests::region::siblings_over_one_frozen_prefix_glue_their_suffixes_in_order`
    #[spec(ensures: |ret| (id.offset < self.shift.mark) == (ret.offset == id.offset) || self.shift.by.0 == 0_u32)]
    #[inline]
    #[must_use]
    pub fn translate<Kind>(
        self,
        id: Id<'child, Kind>,
    ) -> Id<'parent, Kind>
    {
        Id {
            offset: self.shift.offset(id.offset),
            brand: PhantomData,
            kind: PhantomData,
        }
    }
}

/// A family of values indexed by a brand: the same value under each brand.
/// A fork's result is such a value, and the join reads it under the parent's
/// brand.
///
/// # Specification
/// - requires: `rebrand` reads each id of the value through `translation` and
///   changes nothing else.
pub trait Branded
{
    /// The value under the brand `'region`.
    type Of<'region>;

    /// The value under the brand `'to`, each id read through `translation`.
    ///
    /// # Specification
    /// - ensures: the value with each of its ids read through `translation`,
    ///   and nothing else changed.
    /// - panics: none.
    /// - executable: none — the body is each implementor's, and no predicate
    ///   compares a value across two brands.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an id that a child answers reads in the parent the
    ///   value the child minted at it.
    /// - witness: `tests::region::a_fork_that_agrees_folds_its_suffix_at_the_offsets_it_minted`
    fn rebrand<'from, 'to>(
        value: Self::Of<'from>,
        translation: Translation<'from, 'to>,
    ) -> Self::Of<'to>;
}

impl Branded for ()
{
    type Of<'region> = ();

    /// # Specification
    /// trivial.
    #[inline]
    fn rebrand<'from, 'to>(
        (): Self::Of<'from>,
        _translation: Translation<'from, 'to>,
    ) -> Self::Of<'to>
    {
    }
}

impl<Kind> Branded for Id<'static, Kind>
{
    type Of<'region> = Id<'region, Kind>;

    /// # Specification
    /// trivial.
    #[inline]
    fn rebrand<'from, 'to>(
        value: Id<'from, Kind>,
        translation: Translation<'from, 'to>,
    ) -> Id<'to, Kind>
    {
        translation.translate(value)
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
    fn rebrand<'from, 'to>(
        value: Self::Of<'from>,
        translation: Translation<'from, 'to>,
    ) -> Self::Of<'to>
    {
        value.map(|inner| Family::rebrand(inner, translation))
    }
}

impl Branded for Infallible
{
    type Of<'region> = Self;

    /// # Specification
    /// trivial.
    #[inline]
    fn rebrand<'from, 'to>(
        value: Self::Of<'from>,
        _translation: Translation<'from, 'to>,
    ) -> Self::Of<'to>
    {
        match value {}
    }
}

/// A block that the allocator face hands out: an address range inside one
/// chunk of a layer.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Block(NonNull<[u8]>);

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
    ) -> Option<Block>
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
        Some(Block(NonNull::slice_from_raw_parts(
            cursor.next.with_addr(NonZero::new(start)?),
            layout.size(),
        )))
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
    ) -> Result<Block, AllocError>
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
pub struct Region<'region, Value, Below>
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
///     region.mint::<()>(&mut mint, 7_u64)
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
    Body: for<'region> FnOnce(&'region Region<'region, Value, Global>, Mint<'region>) -> Answer,
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
    /// Append `value` and answer its id, of the family `Kind`.
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
    pub fn mint<Kind>(
        &self,
        _mint: &mut Mint<'region>,
        value: Value,
    ) -> Result<Id<'region, Kind>, Exhausted>
    {
        let offset = self.layer.push(value)?;
        Ok(Id {
            offset,
            brand: PhantomData,
            kind: PhantomData,
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
    pub fn get<Kind>(
        &self,
        id: Id<'region, Kind>,
    ) -> Option<&Value>
    {
        self.layer.get(id.offset)
    }

    /// The checked import: the id of `key` when this region holds it.
    ///
    /// The import checks the offset and not the family. A region of more
    /// families checks the family where it reads the value.
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
    pub fn seat<Kind>(
        &self,
        key: Key,
    ) -> Option<Id<'region, Kind>>
    {
        let extent = self.layer.extent().ok()?;
        (key.0 < extent.0).then_some(Id {
            offset: Offset(key.0),
            brand: PhantomData,
            kind: PhantomData,
        })
    }

    /// Fork `width` children over this region's frozen prefix, and glue the
    /// suffixes of the children that keep their answers.
    ///
    /// The fork borrows `mint` for its whole life, so this region makes no id
    /// while a child lives, and each value below the mark stays as it is: the
    /// children's frozen prefix. Each child holds a suffix of its own, an equal
    /// share of this region's remaining budget, its own mint and an [`Adopt`].
    /// `run` enters each child on the threads that it chooses. The glue enters
    /// on the calling thread each child that `run` leaves. A child reads the
    /// frozen prefix by reference and writes only its own suffix, so no child
    /// takes a lock.
    ///
    /// A body that answers `Err` drops its child's suffix whole and hands back
    /// its reason. `Dropped` is fixed outside the child's brand, so a reason
    /// names no id of the child. A body that answers `Ok` keeps its answer, and
    /// the glue appends its child's suffix, in the order of the siblings. Each
    /// suffix moves past the suffixes before it by a [`Shift`]: [`Rebase`]
    /// reads each value through it, and [`Branded::rebrand`] reads the kept
    /// answer through it. A fork whose children only drop takes the family
    /// [`Infallible`]. The one-child fork is the width [`Width::ONE`], and its
    /// one answer is [`Siblings::into_first`].
    ///
    /// A rollback is a fork of [`Width::ONE`], where the shift moves nothing. A
    /// transaction keeps its suffix when its body answers `Ok`. A speculation
    /// drops its suffix always: its family is [`Infallible`], and its verdict
    /// is the reason of the drop.
    ///
    /// No id of a child leaves the fork but through the glue. Neither a cell
    /// nor a reason can hold one:
    ///
    /// ```compile_fail
    /// use core::cell::Cell;
    ///
    /// use gandr_kernel_data::Budget;
    /// use gandr_kernel_data::Child;
    /// use gandr_kernel_data::Width;
    /// use gandr_kernel_data::scoped;
    ///
    /// scoped(Budget::from(4096_usize), |region, mut mint| {
    ///     let leaked = Cell::new(None);
    ///     let _ = region.forks::<(), (), _, _>(
    ///         &mut mint,
    ///         Width::ONE,
    ///         &|_sibling, child, mut own, _adopt| {
    ///             leaked.set(child.mint::<()>(&mut own, ()).ok());
    ///             Ok(())
    ///         },
    ///         |children| children.iter_mut().for_each(Child::enter),
    ///     );
    /// });
    /// ```
    ///
    /// ```compile_fail
    /// use core::convert::Infallible;
    ///
    /// use gandr_kernel_data::Budget;
    /// use gandr_kernel_data::Child;
    /// use gandr_kernel_data::Id;
    /// use gandr_kernel_data::Width;
    /// use gandr_kernel_data::scoped;
    ///
    /// scoped(Budget::from(4096_usize), |region, mut mint| {
    ///     let _ = region.forks::<Infallible, Option<Id<'_>>, _, _>(
    ///         &mut mint,
    ///         Width::ONE,
    ///         &|_sibling, child, mut own, _adopt| Err(child.mint::<()>(&mut own, ()).ok()),
    ///         |children| children.iter_mut().for_each(Child::enter),
    ///     );
    /// });
    /// ```
    ///
    /// # Specification
    /// - ensures: one answer for each child, in the order of the siblings: the
    ///   reason of a child that drops, and the kept answer of a child that
    ///   keeps. Each value of a keeping child then reads in this region past
    ///   the suffixes of the keeping children before it, and each id of its
    ///   answer reads the value that the child minted at it.
    /// - fails: [`Exhausted`] when this region's budget cannot draw the buckets
    ///   that the kept suffixes need, or the list of the children; the suffixes
    ///   then drop whole.
    /// - panics: none.
    /// - executable: none — the answers are generic, and the children's values
    ///   have no equality that a predicate could compare them by.
    ///
    /// # Errors
    /// [`Exhausted`] when the glue cannot hold the kept suffixes.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a keeping child's values read in the parent at the
    ///   ids the glue gives, and the parent's next id follows them; a dropping
    ///   child leaves the parent's next id at the mark and hands back its
    ///   reason; a child that `run` leaves runs once on the calling thread;
    ///   four children on four threads read one frozen value at one address,
    ///   and the two that keep glue in the order of the siblings.
    /// - witness: `tests::region::a_fork_that_agrees_folds_its_suffix_at_the_offsets_it_minted`
    /// - witness: `tests::region::a_fork_that_disagrees_drops_its_suffix_whole`
    /// - witness: `tests::region::a_speculation_hands_back_its_verdict_and_drops_its_suffix`
    /// - witness: `tests::region::a_child_that_the_run_leaves_runs_once_on_the_calling_thread`
    /// - witness: `tests::region::siblings_over_one_frozen_prefix_glue_their_suffixes_in_order`
    #[inline]
    pub fn forks<'body, Family, Dropped, Body, Run>(
        &self,
        _mint: &mut Mint<'region>,
        width: Width,
        body: &'body Body,
        run: Run,
    ) -> Result<Siblings<Result<Family::Of<'region>, Dropped>>, Exhausted>
    where
        Value: Rebase,
        Family: Branded,
        Body: for<'child> Fn(
            Sibling,
            &'child Region<'child, Value, Below>,
            Mint<'child>,
            Adopt<'region, 'child>,
        ) -> Result<Family::Of<'child>, Dropped>,
        Run: FnOnce(&mut Siblings<Child<'region, 'body, Value, Below, Family, Dropped, Body>>),
    {
        let mark = self.layer.extent()?;
        let count = NonZeroUsize::from(width).get();
        let share = Budget(
            self.layer
                .remaining()
                .0
                .checked_div(count)
                .unwrap_or(0_usize),
        );
        let child = |sibling| Child {
            layer: Layer::new(
                Some(self.layer),
                mark,
                share,
                self.layer.bytes.allocator.clone(),
            ),
            sibling: Sibling(sibling),
            body,
            answer: None,
        };
        let mut rest = Vec::new();
        rest.try_reserve_exact(count.saturating_sub(1))
            .ok()
            .ok_or_else(|| self.layer.exhausted())?;
        rest.extend((1 .. count).map(child));
        let mut children = Siblings {
            first: child(0),
            rest,
        };
        run(&mut children);
        self.glue(mark, children)
    }

    /// Append the suffix of each child that keeps its answer, in the order of
    /// the siblings, and read each kept answer through the move of its suffix.
    /// A child that the run left runs first, on the calling thread.
    ///
    /// # Specification
    /// - ensures: on `Ok`, one answer for each child in order: the reason of a
    ///   child that drops, and for a keeping child its answer, with its values
    ///   past the suffixes of the keeping children before it. On a refusal of
    ///   the budget, this region is unchanged.
    /// - fails: [`Exhausted`] when this region's remaining budget cannot draw
    ///   the buckets of the kept suffixes, their values pass the last offset,
    ///   or the lists of the answers cannot be drawn. The check comes before
    ///   the first value moves.
    /// - panics: none.
    /// - executable: none — the values move, and `Value` has no equality that a
    ///   predicate could compare them by.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a child's values read in the parent at the offsets
    ///   the glue gives them, and the parent's next id follows them; the second
    ///   keeping child reads past the first child's suffix.
    /// - witness: `tests::region::a_fork_that_agrees_folds_its_suffix_at_the_offsets_it_minted`
    /// - witness: `tests::region::siblings_over_one_frozen_prefix_glue_their_suffixes_in_order`
    fn glue<Family, Dropped, Body>(
        &self,
        mark: Offset,
        children: Siblings<Child<'region, '_, Value, Below, Family, Dropped, Body>>,
    ) -> Result<Siblings<Result<Family::Of<'region>, Dropped>>, Exhausted>
    where
        Value: Rebase,
        Family: Branded,
        Body: for<'child> Fn(
            Sibling,
            &'child Region<'child, Value, Below>,
            Mint<'child>,
            Adopt<'region, 'child>,
        ) -> Result<Family::Of<'child>, Dropped>,
    {
        let ended = children.try_map(self.layer.exhausted(), |child| Ok(child.ended()))?;
        let kept = ended
            .iter()
            .filter(|child| child.answer.is_ok())
            .try_fold(Count(0_u32), |sum, child| {
                sum.0.checked_add(child.layer.len.get().0).map(Count)
            })
            .ok_or_else(|| self.layer.exhausted())?;
        if kept != Count(0_u32) {
            let bytes = self
                .layer
                .draw_for(kept)
                .ok_or_else(|| self.layer.exhausted())?;
            let fits = mark.0.checked_add(kept.0).is_some();
            if !fits || bytes > self.layer.remaining() {
                return Err(self.layer.exhausted());
            }
        }
        ended.try_map(self.layer.exhausted(), |child| {
            let Ended { layer, answer } = child;
            let kept = match answer {
                Ok(kept) => kept,
                Err(dropped) => return Ok(Err(dropped)),
            };
            let by = self
                .layer
                .extent()?
                .0
                .checked_sub(mark.0)
                .map(Count)
                .ok_or_else(|| self.layer.exhausted())?;
            let shift = Shift { mark, by };
            for value in layer.into_values() {
                let _offset: Offset = self.layer.push(value.rebase(shift))?;
            }
            Ok(Ok(Family::rebrand(kept, Translation {
                shift,
                brands: PhantomData,
            })))
        })
    }
}

/// The children of one fork, or their answers, in the order of the siblings.
///
/// A fork has at least one child, so the first always stands, and a fork of
/// [`Width::ONE`] draws no list for the siblings after it.
///
/// # Specification
/// trivial.
pub struct Siblings<Item>
{
    /// The first sibling's item.
    first: Item,
    /// The item of each sibling after the first, in order.
    rest: Vec<Item>,
}

impl<Item> Siblings<Item>
{
    /// The first sibling's item: the one item of a fork of [`Width::ONE`].
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn into_first(self) -> Item
    {
        self.first
    }

    /// Each sibling's item, in order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn iter(&self) -> Chain<Once<&Item>, slice::Iter<'_, Item>>
    {
        once(&self.first).chain(self.rest.iter())
    }

    /// Each sibling's item, in order, to change.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn iter_mut(&mut self) -> Chain<Once<&mut Item>, slice::IterMut<'_, Item>>
    {
        once(&mut self.first).chain(self.rest.iter_mut())
    }

    /// Each item read through `read`, in order. The list after the first takes
    /// one block, drawn before the first read.
    ///
    /// # Specification
    /// - ensures: on `Ok`, the item of each sibling read in order.
    /// - fails: `refused` when the list cannot be drawn, or the first error of
    ///   `read`.
    /// - panics: none.
    /// - executable: none — `read` is generic and may move what it reads.
    ///
    /// # Errors
    /// `refused`, or the first error of `read`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the glue reads each child once and in order.
    /// - witness: `tests::region::siblings_over_one_frozen_prefix_glue_their_suffixes_in_order`
    fn try_map<Mapped, Read>(
        self,
        refused: Exhausted,
        mut read: Read,
    ) -> Result<Siblings<Mapped>, Exhausted>
    where
        Read: FnMut(Item) -> Result<Mapped, Exhausted>,
    {
        let mut rest = Vec::new();
        rest.try_reserve_exact(self.rest.len())
            .ok()
            .ok_or(refused)?;
        let first = read(self.first)?;
        for item in self.rest {
            rest.push(read(item)?);
        }
        Ok(Siblings { first, rest })
    }
}

impl<Item> IntoIterator for Siblings<Item>
{
    type IntoIter = Chain<Once<Item>, vec::IntoIter<Item>>;
    type Item = Item;

    /// # Specification
    /// trivial.
    #[inline]
    fn into_iter(self) -> Self::IntoIter
    {
        once(self.first).chain(self.rest)
    }
}

impl<'siblings, Item> IntoIterator for &'siblings Siblings<Item>
{
    type IntoIter = Chain<Once<&'siblings Item>, slice::Iter<'siblings, Item>>;
    type Item = &'siblings Item;

    /// # Specification
    /// trivial.
    #[inline]
    fn into_iter(self) -> Self::IntoIter
    {
        self.iter()
    }
}

impl<'siblings, Item> IntoIterator for &'siblings mut Siblings<Item>
{
    type IntoIter = Chain<Once<&'siblings mut Item>, slice::IterMut<'siblings, Item>>;
    type Item = &'siblings mut Item;

    /// # Specification
    /// trivial.
    #[inline]
    fn into_iter(self) -> Self::IntoIter
    {
        self.iter_mut()
    }
}

/// One child of [`Region::forks`]: a suffix of its own over the frozen
/// prefix, its place among its siblings, and its answer once
/// [`Child::enter`] runs it.
///
/// # Specification
/// trivial.
pub struct Child<'region, 'body, Value, Below, Family, Dropped, Body>
where
    Below: Allocator + Clone,
    Family: Branded,
{
    /// The child's suffix, over the parent's frozen layer.
    layer: Layer<'region, Value, Below>,
    /// The child's place among its siblings.
    sibling: Sibling,
    /// The body that each child of the fork runs.
    body: &'body Body,
    /// `None` until the child runs. Then the body's answer: a kept answer
    /// under the parent's brand at the offsets that the child minted, which
    /// the glue moves, or the reason of a drop.
    answer: Option<Result<Family::Of<'region>, Dropped>>,
}

/// A child of a fork once it runs: its suffix, and its answer.
///
/// # Specification
/// trivial.
struct Ended<'region, Value, Below, Answer>
where
    Below: Allocator + Clone,
{
    /// The child's suffix.
    layer: Layer<'region, Value, Below>,
    /// The child's answer.
    answer: Answer,
}

impl<'region, Value, Below, Family, Dropped, Body>
    Child<'region, '_, Value, Below, Family, Dropped, Body>
where
    Below: Allocator + Clone,
    Family: Branded,
    Body: for<'child> Fn(
        Sibling,
        &'child Region<'child, Value, Below>,
        Mint<'child>,
        Adopt<'region, 'child>,
    ) -> Result<Family::Of<'child>, Dropped>,
{
    /// Run the body on this child, under a brand of its own, and keep its
    /// answer for the glue. A child runs once: a second entry does nothing.
    ///
    /// # Specification
    /// - ensures: the child holds an answer; the body ran once over the child's
    ///   suffix.
    /// - panics: none of its own; a panic of the body passes through.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — four children on four threads each write a suffix of
    ///   their own, and the glue reads the two that keep.
    /// - witness: `tests::region::siblings_over_one_frozen_prefix_glue_their_suffixes_in_order`
    #[spec(ensures: self.answer.is_some())]
    #[inline]
    pub fn enter(&mut self)
    {
        if self.answer.is_none() {
            self.answer = Some(self.answered());
        }
    }

    /// The body's answer over this child's suffix, with a kept answer read
    /// under the parent's brand at the offsets that the child minted.
    ///
    /// # Specification
    /// trivial.
    fn answered(&self) -> Result<Family::Of<'region>, Dropped>
    {
        let region = Region {
            layer: &self.layer,
            brand: PhantomData,
        };
        let answer = (self.body)(self.sibling, &region, Mint { brand: PhantomData }, Adopt {
            brands: PhantomData,
        });
        let shift = Shift {
            mark: self.layer.base,
            by: Count(0_u32),
        };
        answer.map(|kept| {
            Family::rebrand(kept, Translation {
                shift,
                brands: PhantomData,
            })
        })
    }

    /// This child with its answer. A child that no run entered runs now.
    ///
    /// # Specification
    /// trivial.
    fn ended(self) -> Ended<'region, Value, Below, Result<Family::Of<'region>, Dropped>>
    {
        let answer = match self.answer {
            Some(answer) => answer,
            None => self.answered(),
        };
        Ended {
            layer: self.layer,
            answer,
        }
    }
}

/// A child crosses to the thread that enters it.
///
/// # Safety
/// - unsafe invariants: the child's own layer moves whole, and `Send` lets its
///   values and the chunks it draws from `Below` cross. Its one shared borrow
///   is of the frozen prefix, which the child reads through `Layer::get` alone.
///   [`Region::forks`] keeps the parent's mint borrowed until each child ends,
///   and so does the fork of each layer below it, so no push writes a count or
///   a bucket of the prefix while a child reads it. The parent's allocator face
///   writes only its cursor, its chunks and its drawn bytes, which no child
///   reads. `Value: Sync` lets each thread read the prefix's values, `Below:
///   Sync` lets each thread draw from one allocator, `Body: Sync` lets each
///   thread run the one body, and the answer that moves back is `Send`.
#[expect(
    clippy::non_send_fields_in_send_ty,
    reason = "the layer's one shared borrow is the frozen prefix, which a child only reads, and \
              its chunks are its own; the invariants above state why it crosses"
)]
// SAFETY: the invariants above hold: `Child` exposes its layer only to the
// body through `Child::enter`, and `Layer::get` writes nothing.
unsafe impl<'region, Value, Below, Family, Dropped, Body> Send
    for Child<'region, '_, Value, Below, Family, Dropped, Body>
where
    Value: Send + Sync,
    Below: Allocator + Clone + Send + Sync,
    Family: Branded,
    Family::Of<'region>: Send,
    Dropped: Send,
    Body: Sync,
{
}

/// The allocator face of a region: a borrow of the region hands out blocks
/// from its chunks.
///
/// # Safety
/// - unsafe invariants: each block lies in a chunk of the region's layer, and
///   the layer outlives each borrow `&Region` of it, so a block stays valid
///   while any copy of this allocator lives. The cursor only moves forward, so
///   no two live blocks overlap. A copy of `&Region` is the same region, so a
///   block from one copy may return through another.
// SAFETY: the invariants above hold: `Bytes::carve` hands out each block
// past the last, and `Bytes` frees its chunks only when the layer drops.
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
        self.layer.block(layout).map(|block| block.0)
    }

    /// Keep the block: the region frees each of its chunks when it ends.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Safety
    /// - unsafe invariants: the caller's, as `Allocator::deallocate` states;
    ///   this body reads neither argument, so no argument can break it.
    #[inline]
    unsafe fn deallocate(
        &self,
        _block: NonNull<u8>,
        _layout: Layout,
    )
    {
    }
}
