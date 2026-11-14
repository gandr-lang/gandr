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

use alloc::boxed::Box;
use core::cell::Cell;
use core::cell::OnceCell;
use core::fmt;
use core::marker::PhantomData;
use core::mem::size_of;

/// An invariant brand: no region's ids read as another region's.
type Brand<'region> = PhantomData<fn(&'region ()) -> &'region ()>;

/// The slots of the first bucket of a layer. Each later bucket doubles it.
const FIRST: u32 = 64;

/// The binary logarithm of [`FIRST`].
const FIRST_LOG: u32 = 6;

/// The buckets of a layer: enough for each relative index that a `u32`
/// holds.
const BUCKETS: usize = 27;

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
    offset: u32,
    /// The region's brand.
    brand: Brand<'region>,
}

impl Id<'_>
{
    /// The durable key of the value: the export, which is always safe.
    ///
    /// # Specification
    /// - ensures: [`Region::seat`] of the key in this region gives this id.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a key of each of two values seats back as its own id,
    ///   and a key past the region is refused.
    /// - witness: `tests::region::a_key_seats_back_in_its_region_and_a_key_past_it_is_refused`
    #[inline]
    #[must_use]
    pub const fn key(self) -> Key
    {
        Key(self.offset)
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
    /// - ensures: the child reads at the result the value that the parent reads
    ///   at `id`.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a child reads a value of the parent through the
    ///   adopted id, and the child's own first id is apart from it.
    /// - witness: `tests::region::a_child_reads_a_value_of_its_parent_through_adopt`
    #[inline]
    #[must_use]
    pub const fn adopt(
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

/// The bucket of a layer's relative index, and the slot within it.
///
/// # Specification
/// - ensures: two relative indices give two places; bucket `b` holds `FIRST <<
///   b` slots.
/// - panics: none.
fn place(index: u32) -> Option<(u32, u32)>
{
    let shifted = index.checked_add(FIRST)?;
    let top = shifted.checked_ilog2()?;
    let bucket = top.checked_sub(FIRST_LOG)?;
    let within = shifted.checked_sub(1_u32.checked_shl(top)?)?;
    Some((bucket, within))
}

/// The slots of a bucket.
///
/// # Specification
/// trivial.
fn bucket_slots(bucket: u32) -> Option<u32>
{
    FIRST.checked_shl(bucket)
}

/// The storage of one region: its own values from `base` on, over the frozen
/// prefix of the region it forked from.
struct Layer<'below, Value>
{
    /// The frozen prefix: every offset below `base`.
    below: Option<&'below Self>,
    /// The first offset of this layer's own values.
    base: u32,
    /// The values this layer holds.
    len: Cell<u32>,
    /// The bytes this layer may draw.
    budget: Budget,
    /// The bytes this layer drew.
    drawn: Cell<Budget>,
    /// The buckets, each drawn at its first value.
    buckets: [OnceCell<Box<[OnceCell<Value>]>>; BUCKETS],
}

impl<'below, Value> Layer<'below, Value>
{
    /// An empty layer from `base` on, over `below`.
    fn new(
        below: Option<&'below Self>,
        base: u32,
        budget: Budget,
    ) -> Self
    {
        Self {
            below,
            base,
            len: Cell::new(0_u32),
            budget,
            drawn: Cell::new(Budget(0_usize)),
            buckets: [const { OnceCell::new() }; BUCKETS],
        }
    }

    /// The refusal of this layer.
    const fn exhausted(&self) -> Exhausted
    {
        Exhausted {
            budget: self.budget,
        }
    }

    /// The first offset past every value this layer reads.
    fn extent(&self) -> Result<u32, Exhausted>
    {
        self.base
            .checked_add(self.len.get())
            .ok_or_else(|| self.exhausted())
    }

    /// The bytes this layer may still draw.
    fn remaining(&self) -> Budget
    {
        Budget(self.budget.0.saturating_sub(self.drawn.get().0))
    }

    /// The value at `offset`, in this layer or in its frozen prefix.
    fn get(
        &self,
        offset: u32,
    ) -> Option<&Value>
    {
        match offset.checked_sub(self.base) {
            Some(index) => {
                let (bucket, within) = place(index)?;
                self.buckets
                    .get(usize::try_from(bucket).ok()?)?
                    .get()?
                    .get(usize::try_from(within).ok()?)?
                    .get()
            },
            None => self.below?.get(offset),
        }
    }

    /// The bytes that the buckets for `count` more values draw.
    fn draw_for(
        &self,
        count: u32,
    ) -> Option<Budget>
    {
        let first = self.len.get();
        let last = first.checked_add(count)?.checked_sub(1_u32)?;
        let (from, _) = place(first)?;
        let (to, _) = place(last)?;
        let mut bytes = 0_usize;
        for bucket in from ..= to {
            let drawn = self
                .buckets
                .get(usize::try_from(bucket).ok()?)?
                .get()
                .is_some();
            if !drawn {
                let slots = usize::try_from(bucket_slots(bucket)?).ok()?;
                bytes = bytes.checked_add(slots.checked_mul(size_of::<OnceCell<Value>>())?)?;
            }
        }
        Some(Budget(bytes))
    }

    /// Append `value` at the next offset and answer the offset.
    fn push(
        &self,
        value: Value,
    ) -> Result<u32, Exhausted>
    {
        let index = self.len.get();
        let offset = self.extent()?;
        let next = index.checked_add(1_u32).ok_or_else(|| self.exhausted())?;
        let (bucket, within) = place(index).ok_or_else(|| self.exhausted())?;
        let cell = usize::try_from(bucket)
            .ok()
            .and_then(|bucket| self.buckets.get(bucket))
            .ok_or_else(|| self.exhausted())?;
        let slots = cell
            .get()
            .map(AsRef::as_ref)
            .map_or_else(|| self.draw(cell, bucket), Ok)?;
        let slot = usize::try_from(within)
            .ok()
            .and_then(|within| slots.get(within))
            .ok_or_else(|| self.exhausted())?;
        let _stored: &Value = slot.get_or_init(|| value);
        self.len.set(next);
        Ok(offset)
    }

    /// Draw `bucket` into `cell` under the budget, and answer its slots.
    fn draw<'cell>(
        &self,
        cell: &'cell OnceCell<Box<[OnceCell<Value>]>>,
        bucket: u32,
    ) -> Result<&'cell [OnceCell<Value>], Exhausted>
    {
        let bytes = self.draw_for(1_u32).ok_or_else(|| self.exhausted())?;
        if bytes > self.remaining() {
            return Err(self.exhausted());
        }
        let count = bucket_slots(bucket)
            .and_then(|count| usize::try_from(count).ok())
            .ok_or_else(|| self.exhausted())?;
        let fresh: Box<[OnceCell<Value>]> =
            core::iter::repeat_with(OnceCell::new).take(count).collect();
        self.drawn
            .set(Budget(self.drawn.get().0.saturating_add(bytes.0)));
        Ok(cell.get_or_init(|| fresh))
    }

    /// This layer's own values, in the order of their offsets. Each filled
    /// slot lies below `len`, and each slot past it is empty.
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
///
/// # Adequacy
/// - hypothesis: L3 — values minted in order read back at their ids, and a
///   budget that holds one bucket refuses the value past it.
/// - witness: `tests::region::a_region_reads_each_value_at_its_id_and_refuses_past_its_budget`
pub struct Region<'region, Value>
{
    /// The values and the frozen prefix, owned by the scope or the fork
    /// that made the region, so a join can take them after the child's body.
    layer: &'region Layer<'region, Value>,
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
/// - ensures: the body's result, which names no id of the region.
/// - panics: none.
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
    let layer = Layer::new(None, 0_u32, budget);
    let region = Region {
        layer: &layer,
        brand: PhantomData,
    };
    body(&region, Mint { brand: PhantomData })
}

impl<'region, Value> Region<'region, Value>
{
    /// Append `value` and answer its id.
    ///
    /// # Specification
    /// - ensures: [`Region::get`] of the id gives `value`.
    /// - fails: [`Exhausted`] when the budget cannot draw the bucket the value
    ///   needs, or the region's offsets are full.
    /// - panics: none.
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
    #[inline]
    #[must_use]
    pub fn seat(
        &self,
        key: Key,
    ) -> Option<Id<'region>>
    {
        let extent = self.layer.extent().ok()?;
        (key.0 < extent).then_some(Id {
            offset: key.0,
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
            &'child Region<'child, Value>,
            Mint<'child>,
            Adopt<'region, 'child>,
        ) -> Option<Family::Of<'child>>,
    {
        let mark = self.layer.extent()?;
        let layer = Layer::new(Some(self.layer), mark, self.layer.remaining());
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
    fn join<'child>() -> impl Fn(Id<'child>) -> Id<'region>
    where
        'region: 'child,
    {
        |id| Id {
            offset: id.offset,
            brand: PhantomData,
        }
    }

    /// Append the child's own values, whole or not at all.
    fn fold(
        &self,
        child: Layer<'_, Value>,
    ) -> Result<(), Exhausted>
    {
        let count = child.len.get();
        if count == 0_u32 {
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
            let _offset: u32 = self.layer.push(value)?;
        }
        Ok(())
    }
}
