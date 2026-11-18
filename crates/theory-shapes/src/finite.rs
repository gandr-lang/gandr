//! Decidable finite subshapes: complements, meets and unions, inclusions
//! presented with their complements, and the outer pushout square of two
//! subshapes over their meet.

use alloc::vec;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;

use crate::error::ShapeError;
use crate::index::Point;
use crate::index::PointCount;

/// Membership of one point in a decidable subshape.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Membership
{
    /// The point belongs to the subshape.
    Inside,
    /// The point belongs to its complement.
    Outside,
}

/// A decidable subshape of the finite carrier `0 .. ambient`.
///
/// # Specification
/// - ensures: every carrier point has exactly one membership decision, so the
///   subshape and its complement partition the carrier.
/// - provides: the decidable-complement presentation of a finite subset,
///   including the subsets of the empty carrier.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — every subset pair of every carrier up to four points,
///   against an independent bit-mask reading, distinguishes a lost point, a
///   swapped set operation and a wrong complement.
/// - witness: `tests::finite::all_small_union_squares`
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Subshape
{
    /// One membership decision per carrier point, in carrier order.
    membership: Vec<Membership>,
}

impl Subshape
{
    /// Builds the subshape of `ambient` holding exactly the given points.
    ///
    /// # Specification
    /// - ensures: the carrier is `ambient`; a point is inside exactly when it
    ///   is listed; a repeated point is listed once.
    /// - fails: a listed point outside the carrier is refused by name.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`ShapeError::PointOutside`]: a listed point is not below `ambient`.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every subset of every carrier up to four points is
    ///   built from its bit mask and read back point by point; L3 — the first
    ///   point past the carrier, an empty carrier and a repeated point separate
    ///   the bound and the duplicate handling.
    /// - witness: `tests::finite::all_small_union_squares`
    /// - witness: `tests::finite::finite_boundaries_are_checked`
    #[inline]
    #[spec(ensures: |ref ret| match *ret {
        Ok(ref shape) => shape.ambient() == ambient
            && points.iter().all(|point| shape.contains(*point) == Ok(Membership::Inside))
            && shape.decisions().iter().filter(|decision| **decision == Membership::Inside).count() <= points.len(),
        Err(ShapeError::PointOutside(point)) => points.contains(&point) && usize::from(point) >= usize::from(ambient),
        Err(_) => false,
    })]
    pub fn new(
        ambient: PointCount,
        points: &[Point],
    ) -> Result<Self, ShapeError>
    {
        let mut membership = vec![Membership::Outside; usize::from(ambient)];
        for &point in points {
            let entry = membership
                .get_mut(usize::from(point))
                .ok_or(ShapeError::PointOutside(point))?;
            *entry = Membership::Inside;
        }
        Ok(Self { membership })
    }

    /// The number of points of the carrier.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn ambient(&self) -> PointCount
    {
        PointCount::from(self.membership.len())
    }

    /// Every membership decision, in carrier order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn decisions(&self) -> &[Membership]
    {
        &self.membership
    }

    /// Decides whether a carrier point is inside the subshape.
    ///
    /// # Specification
    /// - provides: the decision stored for `point`.
    /// - fails: a point outside the carrier is refused by name.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`ShapeError::PointOutside`]: `point` is not below the carrier's size.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the first point past a carrier and the empty carrier
    ///   separate the bound; L2 — every point of every small subset separates a
    ///   wrong decision.
    /// - witness: `tests::finite::finite_boundaries_are_checked`
    /// - witness: `tests::finite::all_small_union_squares`
    #[inline]
    #[spec(ensures: |ref ret| match *ret {
        Ok(decision) => self.membership.get(usize::from(point)) == Some(&decision),
        Err(error) => error == ShapeError::PointOutside(point) && usize::from(point) >= self.membership.len(),
    })]
    pub fn contains(
        &self,
        point: Point,
    ) -> Result<Membership, ShapeError>
    {
        self.membership
            .get(usize::from(point))
            .copied()
            .ok_or(ShapeError::PointOutside(point))
    }

    /// The decidable complement in the same carrier.
    ///
    /// # Specification
    /// - ensures: the carrier is unchanged and every decision is reversed.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every subset of every carrier up to four points, read
    ///   point by point against its complement, separates the identity and a
    ///   partial reversal.
    /// - witness: `tests::finite::all_small_union_squares`
    /// - witness: `tests::finite::finite_boundaries_are_checked`
    #[inline]
    #[must_use]
    #[spec(ensures: |ref ret| ret.membership.len() == self.membership.len()
        && ret.membership.iter().zip(&self.membership).all(|(after, before)| after != before))]
    pub fn complement(&self) -> Self
    {
        Self {
            membership: self
                .membership
                .iter()
                .map(|decision| match *decision {
                    Membership::Inside => Membership::Outside,
                    Membership::Outside => Membership::Inside,
                })
                .collect(),
        }
    }

    /// Meets or joins two subshapes of one carrier, point by point.
    ///
    /// # Specification
    /// - ensures: a point is inside the meet when it is inside both, and inside
    ///   the union when it is inside either; the carrier is unchanged.
    /// - fails: subshapes of different carriers are refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`ShapeError::DifferentAmbient`]: the carriers differ in size.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every subset pair of every carrier up to four points,
    ///   against independent conjunction and disjunction of the bit masks,
    ///   separates the two operations and a lost point; L3 — carriers of sizes
    ///   zero and one separate the carrier check.
    /// - witness: `tests::finite::all_small_union_squares`
    /// - witness: `tests::finite::finite_boundaries_are_checked`
    #[inline]
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body combines every pair of decisions once; the check recombines each once"
        )
    )]
    #[spec(ensures: |ref ret| match *ret {
        Ok(ref shape) => shape.membership.len() == self.membership.len()
            && shape.membership.iter().zip(self.membership.iter().zip(&other.membership)).all(|(result, (left, right))| {
                let inside = match operation {
                    SetOperation::Meet => *left == Membership::Inside && *right == Membership::Inside,
                    SetOperation::Union => *left == Membership::Inside || *right == Membership::Inside,
                };
                (*result == Membership::Inside) == inside
            }),
        Err(error) => error == ShapeError::DifferentAmbient && self.membership.len() != other.membership.len(),
    })]
    pub fn combine(
        &self,
        other: &Self,
        operation: SetOperation,
    ) -> Result<Self, ShapeError>
    {
        if self.ambient() != other.ambient() {
            return Err(ShapeError::DifferentAmbient);
        }
        let membership = self
            .membership
            .iter()
            .zip(&other.membership)
            .map(|(left, right)| match (operation, *left, *right) {
                (SetOperation::Meet, Membership::Inside, Membership::Inside)
                | (SetOperation::Union, Membership::Inside, _)
                | (SetOperation::Union, Membership::Outside, Membership::Inside) => {
                    Membership::Inside
                },
                (SetOperation::Meet, Membership::Outside, _)
                | (SetOperation::Meet, Membership::Inside, Membership::Outside)
                | (SetOperation::Union, Membership::Outside, Membership::Outside) => {
                    Membership::Outside
                },
            })
            .collect();
        Ok(Self { membership })
    }

    /// Decides whether this subshape is included in `target`, naming the
    /// first point that escapes when it is not.
    ///
    /// # Specification
    /// - ensures: `Included` exactly when every point inside `self` is inside
    ///   `target`; otherwise `Escapes` names the least point inside `self` and
    ///   outside `target`.
    /// - fails: subshapes of different carriers are refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`ShapeError::DifferentAmbient`]: the carriers differ in size.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every subset pair of every carrier up to four points,
    ///   against the least escaping bit computed from the masks, separates a
    ///   missed escape, a later escape and a reversed inclusion; L3 — carriers
    ///   of sizes zero and one separate the carrier check.
    /// - witness: `tests::finite::all_small_union_squares`
    /// - witness: `tests::finite::finite_boundaries_are_checked`
    #[inline]
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body compares the two tables up to the first escape; the check compares them once more"
        )
    )]
    #[spec(ensures: |ref ret| match *ret {
        Ok(Inclusion::Included) => self.membership.len() == target.membership.len()
            && self.membership.iter().zip(&target.membership).all(|pair| *pair.0 == Membership::Outside || *pair.1 == Membership::Inside),
        Ok(Inclusion::Escapes(point)) => self.contains(point) == Ok(Membership::Inside)
            && target.contains(point) == Ok(Membership::Outside)
            && self.membership.iter().zip(&target.membership).take(usize::from(point))
                .all(|pair| *pair.0 == Membership::Outside || *pair.1 == Membership::Inside),
        Err(error) => error == ShapeError::DifferentAmbient && self.membership.len() != target.membership.len(),
    })]
    pub fn included(
        &self,
        target: &Self,
    ) -> Result<Inclusion, ShapeError>
    {
        if self.ambient() != target.ambient() {
            return Err(ShapeError::DifferentAmbient);
        }
        let escape = self
            .membership
            .iter()
            .zip(&target.membership)
            .position(|pair| *pair.0 == Membership::Inside && *pair.1 == Membership::Outside);
        Ok(escape.map_or(Inclusion::Included, |point| {
            Inclusion::Escapes(Point::from(point))
        }))
    }
}

/// The two lattice operations on the subshapes of one carrier.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum SetOperation
{
    /// Intersection.
    Meet,
    /// Union.
    Union,
}

/// Whether one subshape lies inside another.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Inclusion
{
    /// Every point of the source is a point of the target.
    Included,
    /// This point, the least such, is in the source and not in the target.
    Escapes(Point),
}

/// An inclusion of subshapes presented with its complement in the target.
///
/// # Specification
/// - ensures: source and complement are disjoint and their union is the target,
///   all three in one carrier.
/// - provides: the decidable inclusion a finite cofibration is: its complement
///   is itself a subshape, so a map out of the target is a map out of the
///   source together with one out of the complement.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — every subset pair of every carrier up to four points
///   separates a false admission, a missing complement point and an extra one.
/// - witness: `tests::finite::all_small_union_squares`
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Cofibration
{
    /// The included subshape.
    source: Subshape,
    /// The subshape it is included in.
    target: Subshape,
    /// The target's points outside the source.
    complement: Subshape,
}

impl Cofibration
{
    /// Admits an inclusion and computes its complement in the target.
    ///
    /// # Specification
    /// - ensures: source and complement are disjoint and their union is the
    ///   target.
    /// - fails: subshapes of different carriers are refused, and so is a source
    ///   with a point outside the target, named by the least such point.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`ShapeError::DifferentAmbient`]: the carriers differ in size.
    /// - [`ShapeError::NotIncluded`]: the named point is in the source and not
    ///   in the target.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every subset pair of every carrier up to four points,
    ///   against the least escaping bit of the masks, separates a false
    ///   admission, a wrong escaping point and a wrong complement; L3 —
    ///   carriers of sizes zero and one separate the carrier check.
    /// - witness: `tests::finite::all_small_union_squares`
    /// - witness: `tests::finite::finite_boundaries_are_checked`
    #[inline]
    #[spec(
        captures: [given_source = source.clone(), given_target = target.clone()],
        ensures: |ref ret| match *ret {
            Ok(ref inclusion) => inclusion.source == given_source && inclusion.target == given_target
                && inclusion.source.combine(&inclusion.complement, SetOperation::Union).as_ref() == Ok(&inclusion.target)
                && inclusion.source.combine(&inclusion.complement, SetOperation::Meet)
                    .is_ok_and(|meet| meet.decisions().iter().all(|decision| *decision == Membership::Outside)),
            Err(ShapeError::NotIncluded(point)) => given_source.contains(point) == Ok(Membership::Inside)
                && given_target.contains(point) == Ok(Membership::Outside),
            Err(error) => error == ShapeError::DifferentAmbient && given_source.ambient() != given_target.ambient(),
        },
    )]
    pub fn new(
        source: Subshape,
        target: Subshape,
    ) -> Result<Self, ShapeError>
    {
        let inclusion = source.included(&target)?;
        if let Inclusion::Escapes(point) = inclusion {
            return Err(ShapeError::NotIncluded(point));
        }
        let complement = target.combine(&source.complement(), SetOperation::Meet)?;
        Ok(Self {
            source,
            target,
            complement,
        })
    }

    /// Borrows the source, the target and the complement, in that order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn presentation(&self) -> (&Subshape, &Subshape, &Subshape)
    {
        (&self.source, &self.target, &self.complement)
    }
}

/// The block a carrier point falls in, for a pair of subshapes.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Block
{
    /// Inside both: their meet.
    Both,
    /// Inside the left subshape only.
    Left,
    /// Inside the right subshape only.
    Right,
    /// Outside their union.
    Neither,
}

/// One leg of a union square: the left or the right subshape.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Leg
{
    /// The left subshape.
    Left,
    /// The right subshape.
    Right,
}

impl fmt::Display for Leg
{
    /// Renders the leg's name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match *self {
            Self::Left => "left",
            Self::Right => "right",
        })
    }
}

/// The outer pushout square of two subshapes over their meet.
///
/// # Specification
/// - ensures: blocks `B, L, R, N` present the carrier as `((B+L)+R)+N`, the
///   left subshape as `B+L`, the right as `B+R`, their meet as `B` and their
///   union as `(B+L)+R`, every inclusion keeping carrier point identities. Two
///   maps out of the legs that agree on `B` extend to exactly one map out of
///   the union: the left map on `B+L` and the right on `R`.
/// - provides: the square as finite outer data; [`Self::mediator`] computes its
///   universal map.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — every subset pair of every carrier up to four points
///   separates swapped or conflated blocks; every pair of maps into a two-point
///   carrier, against every candidate map out of the union, up to three points,
///   separates a missing, a wrong and a second mediator.
/// - witness: `tests::finite::all_small_union_squares`
/// - witness: `tests::finite::union_square_has_unique_mediators`
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct UnionSquare
{
    /// One block per carrier point, in carrier order.
    blocks: Vec<Block>,
}

impl UnionSquare
{
    /// Partitions the carrier of two subshapes into the four blocks.
    ///
    /// # Specification
    /// - ensures: a point's block is the pair of its two membership decisions.
    /// - fails: subshapes of different carriers are refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`ShapeError::DifferentAmbient`]: the carriers differ in size.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every subset pair of every carrier up to four points
    ///   separates swapped or conflated blocks; L3 — carriers of sizes zero and
    ///   one separate the carrier check.
    /// - witness: `tests::finite::all_small_union_squares`
    /// - witness: `tests::finite::finite_boundaries_are_checked`
    #[inline]
    #[spec(ensures: |ref ret| match *ret {
        Ok(ref square) => square.blocks.len() == left.decisions().len()
            && square.blocks.iter().zip(left.decisions().iter().zip(right.decisions())).all(|(block, (l, r))| *block == match (*l, *r) {
                (Membership::Inside, Membership::Inside) => Block::Both,
                (Membership::Inside, Membership::Outside) => Block::Left,
                (Membership::Outside, Membership::Inside) => Block::Right,
                (Membership::Outside, Membership::Outside) => Block::Neither,
            }),
        Err(error) => error == ShapeError::DifferentAmbient && left.ambient() != right.ambient(),
    })]
    pub fn new(
        left: &Subshape,
        right: &Subshape,
    ) -> Result<Self, ShapeError>
    {
        if left.ambient() != right.ambient() {
            return Err(ShapeError::DifferentAmbient);
        }
        let blocks = left
            .membership
            .iter()
            .zip(&right.membership)
            .map(|pair| match (*pair.0, *pair.1) {
                (Membership::Inside, Membership::Inside) => Block::Both,
                (Membership::Inside, Membership::Outside) => Block::Left,
                (Membership::Outside, Membership::Inside) => Block::Right,
                (Membership::Outside, Membership::Outside) => Block::Neither,
            })
            .collect();
        Ok(Self { blocks })
    }

    /// Borrows the blocks, in carrier order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn blocks(&self) -> &[Block]
    {
        &self.blocks
    }

    /// The universal map out of the union: glues a map out of each leg that
    /// agree on the meet.
    ///
    /// A map out of a subshape is its table of values, one per point of the
    /// subshape in carrier order; the result is the table of the union.
    ///
    /// # Specification
    /// - requires: `left` holds one value per point of the left subshape and
    ///   `right` one per point of the right, each in carrier order.
    /// - ensures: the result has one value per point of the union, in carrier
    ///   order; restricted to the left subshape it is `left`, and restricted to
    ///   the right it is `right`. It is the only such table.
    /// - fails: the walk over the carrier refuses its first defect: a leg's
    ///   table running out names that leg, the left first at a meet point, and
    ///   two values differing at a meet point name the point; after the walk, a
    ///   table with values left over names its leg, the left first.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`ShapeError::MapLength`]: the named leg's table does not have one
    ///   value per point of that leg.
    /// - [`ShapeError::Disagreement`]: the two maps differ at the named point
    ///   of the meet.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every subset pair of every carrier up to three points
    ///   and every pair of maps into a two-point carrier, against every
    ///   candidate map out of the union enumerated independently, separate a
    ///   mediator that drops a block, takes the wrong leg on the meet, or
    ///   exists for disagreeing maps; L3 — tables one short and one long on
    ///   either leg separate the length checks.
    /// - witness: `tests::finite::union_square_has_unique_mediators`
    /// - witness: `tests::finite::finite_boundaries_are_checked`
    #[inline]
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body reads every block once; the check reads each once more to restrict the result to each leg"
        )
    )]
    #[spec(ensures: |ref ret| match *ret {
        Ok(ref glued) => {
            let left_of_union = self.blocks.iter().filter(|block| matches!(**block, Block::Both | Block::Left | Block::Right))
                .zip(glued.iter()).filter(|pair| matches!(*pair.0, Block::Both | Block::Left)).map(|pair| pair.1);
            let right_of_union = self.blocks.iter().filter(|block| matches!(**block, Block::Both | Block::Left | Block::Right))
                .zip(glued.iter()).filter(|pair| matches!(*pair.0, Block::Both | Block::Right)).map(|pair| pair.1);
            glued.len() == self.blocks.iter().filter(|block| **block != Block::Neither).count()
                && left_of_union.eq(left.iter())
                && right_of_union.eq(right.iter())
        },
        Err(ShapeError::MapLength(Leg::Left)) => left.len() != self.blocks.iter().filter(|block| matches!(**block, Block::Both | Block::Left)).count(),
        Err(ShapeError::MapLength(Leg::Right)) => right.len() != self.blocks.iter().filter(|block| matches!(**block, Block::Both | Block::Right)).count(),
        Err(ShapeError::Disagreement(point)) => self.blocks.get(usize::from(point)) == Some(&Block::Both),
        Err(_) => false,
    })]
    pub fn mediator<Value>(
        &self,
        left: &[Value],
        right: &[Value],
    ) -> Result<Vec<Value>, ShapeError>
    where
        Value: Clone + PartialEq,
    {
        let mut glued = Vec::with_capacity(left.len().saturating_add(right.len()));
        let mut lefts = left.iter();
        let mut rights = right.iter();
        for (point, block) in self.blocks.iter().enumerate() {
            let value = match *block {
                Block::Both => match (lefts.next(), rights.next()) {
                    (Some(from_left), Some(from_right)) => {
                        if from_left != from_right {
                            return Err(ShapeError::Disagreement(Point::from(point)));
                        }
                        from_left
                    },
                    (None, _) => return Err(ShapeError::MapLength(Leg::Left)),
                    (Some(_), None) => return Err(ShapeError::MapLength(Leg::Right)),
                },
                Block::Left => match lefts.next() {
                    Some(from_left) => from_left,
                    None => return Err(ShapeError::MapLength(Leg::Left)),
                },
                Block::Right => match rights.next() {
                    Some(from_right) => from_right,
                    None => return Err(ShapeError::MapLength(Leg::Right)),
                },
                Block::Neither => continue,
            };
            glued.push(value.clone());
        }
        if lefts.next().is_some() {
            return Err(ShapeError::MapLength(Leg::Left));
        }
        if rights.next().is_some() {
            return Err(ShapeError::MapLength(Leg::Right));
        }
        Ok(glued)
    }
}
