//! Decidable finite subshapes, complement presentations, and outer union
//! squares.

use alloc::vec;
use alloc::vec::Vec;

use anodized::spec;

use crate::boundary::Point;
use crate::boundary::PointCount;
use crate::boundary::ShapeError;

/// Membership of one point in a decidable subshape.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Membership
{
    /// The point belongs to the subshape.
    Inside,
    /// The point belongs to its complement.
    Outside,
}

/// A subset of the skeletal finite carrier `0..ambient`.
///
/// # Specification
/// - ensures: every carrier point has exactly one membership decision.
/// - provides: a decidable-complement presentation, including empty carriers.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 exhaustive finite subset pairs distinguish lost points,
///   swapped set operations, and incorrect complement presentations.
/// - witness: `tests::finite::all_small_union_squares`
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Subshape
{
    /// One membership decision per ambient point, in carrier order.
    membership: Vec<Membership>,
}

impl Subshape
{
    /// Constructs a subset, ignoring duplicate points.
    ///
    /// # Specification
    /// - ensures: precisely the supplied points are inside the resulting
    ///   subset.
    /// - fails: a point outside `ambient` is refused by identity.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`ShapeError::PointOutside`] for an out-of-range point.
    ///
    /// # Adequacy
    /// - hypothesis: L2 exhaustive subsets and L3 invalid points distinguish
    ///   range mistakes and changed membership.
    /// - witness: `tests::finite::all_small_union_squares`
    /// - witness: `tests::finite::finite_boundaries_are_checked`
    #[inline]
    #[spec(ensures: |ret| ret.as_ref().is_ok_and(|shape| shape.ambient() == ambient)
        || ret.is_err())]
    pub fn new(
        ambient: PointCount,
        points: &[Point],
    ) -> Result<Self, ShapeError>
    {
        let mut membership = vec![Membership::Outside; ambient.0];
        for &point in points {
            let entry = membership
                .get_mut(point.0)
                .ok_or(ShapeError::PointOutside(point))?;
            *entry = Membership::Inside;
        }
        Ok(Self { membership })
    }

    /// Reads the ambient cardinality.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn ambient(&self) -> PointCount
    {
        PointCount(self.membership.len())
    }

    /// Reads all membership decisions in carrier order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn decisions(&self) -> &[Membership]
    {
        &self.membership
    }

    /// Decides membership of a carrier point.
    ///
    /// # Specification
    /// - provides: the stored decision for the given point.
    /// - fails: a point outside the ambient carrier is refused.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`ShapeError::PointOutside`] on an invalid point.
    ///
    /// # Adequacy
    /// - hypothesis: L3 endpoint and empty-carrier reads distinguish bounds
    ///   errors.
    /// - witness: `tests::finite::finite_boundaries_are_checked`
    #[inline]
    #[spec(ensures: |ret| ret.is_ok() == (point.0 < self.membership.len()))]
    pub fn contains(
        &self,
        point: Point,
    ) -> Result<Membership, ShapeError>
    {
        self.membership
            .get(point.0)
            .copied()
            .ok_or(ShapeError::PointOutside(point))
    }

    /// Returns the decidable complement in the same ambient carrier.
    ///
    /// # Specification
    /// - ensures: every membership decision is reversed.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 all small subsets distinguish identity from complement.
    /// - witness: `tests::finite::all_small_union_squares`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.membership.iter().zip(&self.membership).all(|(a,b)| a != b)
        && ret.ambient() == self.ambient())]
    pub fn complement(&self) -> Self
    {
        Self {
            membership: self
                .membership
                .iter()
                .map(|entry| match *entry {
                    | Membership::Inside => Membership::Outside,
                    | Membership::Outside => Membership::Inside,
                })
                .collect(),
        }
    }

    /// Combines two subsets pointwise in the same ambient carrier.
    ///
    /// # Specification
    /// - ensures: meet is intersection and union is union at every point.
    /// - fails: different ambient cardinalities are refused.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`ShapeError::DifferentAmbient`] for different carriers.
    ///
    /// # Adequacy
    /// - hypothesis: L2 exhaustive subset pairs distinguish both lattice
    ///   operations.
    /// - witness: `tests::finite::all_small_union_squares`
    /// - witness: `tests::finite::finite_boundaries_are_checked`
    #[inline]
    #[spec(ensures: |ret| ret.is_ok() == (self.ambient() == other.ambient()))]
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
            .map(|(a, b)| {
                let inside = match operation {
                    | SetOperation::Meet => *a == Membership::Inside && *b == Membership::Inside,
                    | SetOperation::Union => *a == Membership::Inside || *b == Membership::Inside,
                };
                if inside {
                    Membership::Inside
                }
                else {
                    Membership::Outside
                }
            })
            .collect();
        Ok(Self { membership })
    }
}

/// The two finite lattice operations.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SetOperation
{
    /// Intersection.
    Meet,
    /// Union.
    Union,
}

/// An inclusion presented with its finite complement inside the target.
///
/// # Specification
/// - ensures: source and complement partition target in one ambient carrier.
/// - provides: the finite data supporting the 2LTT cofibration argument.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 all small inclusion pairs distinguish missing complements.
/// - witness: `tests::finite::all_small_union_squares`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Cofibration
{
    /// The included subshape.
    source: Subshape,
    /// The containing subshape.
    target: Subshape,
    /// Target minus source.
    complement: Subshape,
}

impl Cofibration
{
    /// Admits an inclusion and computes its complement.
    ///
    /// # Specification
    /// - ensures: source and complement are disjoint and their union is target.
    /// - fails: different carriers or a source point outside target are
    ///   refused.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`ShapeError::DifferentAmbient`] or [`ShapeError::NotIncluded`].
    ///
    /// # Adequacy
    /// - hypothesis: L2 exhaustive subset pairs distinguish false admission and
    ///   incorrect complement; L3 checks carrier mismatch.
    /// - witness: `tests::finite::all_small_union_squares`
    /// - witness: `tests::finite::finite_boundaries_are_checked`
    #[inline]
    #[spec(ensures: |ret| ret.as_ref().is_ok_and(|map| map.source.ambient() == map.target.ambient())
        || ret.is_err())]
    pub fn new(
        source: Subshape,
        target: Subshape,
    ) -> Result<Self, ShapeError>
    {
        if source.ambient() != target.ambient() {
            return Err(ShapeError::DifferentAmbient);
        }
        let mut membership = Vec::with_capacity(source.membership.len());
        for (index, (a, b)) in source.membership.iter().zip(&target.membership).enumerate() {
            if *a == Membership::Inside && *b == Membership::Outside {
                return Err(ShapeError::NotIncluded(Point(index)));
            }
            membership.push(if *a == Membership::Outside && *b == Membership::Inside {
                Membership::Inside
            }
            else {
                Membership::Outside
            });
        }
        Ok(Self {
            source,
            target,
            complement: Subshape { membership },
        })
    }

    /// Borrows source, target and complement, respectively.
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

/// One block of the decidable presentation of two subsets.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Block
{
    /// Their intersection.
    Both,
    /// Only the first subset.
    Left,
    /// Only the second subset.
    Right,
    /// Outside their union.
    Neither,
}

/// The outer pushout square of two subshapes over their intersection.
///
/// # Specification
/// - ensures: blocks `I,L,R,N` present ambient `((I+L)+R)+N`, left `I+L`, right
///   `I+R`, meet `I`, and union `(I+L)+R`. All five inclusions keep ambient
///   point identities. Compatible maps out of left and right extend uniquely by
///   taking the left map on `I+L` and the right map on `R`.
/// - provides: finite outer-type data, not a pushout in a graphical site.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 all small pairs and compatible Boolean maps distinguish the
///   four blocks and the pushout's existence and uniqueness.
/// - witness: `tests::finite::all_small_union_squares`
/// - witness: `tests::finite::union_square_has_unique_mediators`
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct UnionSquare
{
    /// One block for each ambient point.
    blocks: Vec<Block>,
}

impl UnionSquare
{
    /// Partitions two decidable subshapes into their four blocks.
    ///
    /// # Specification
    /// - ensures: block membership is precisely the pair of subset decisions.
    /// - fails: different ambient cardinalities are refused.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`ShapeError::DifferentAmbient`] for different carriers.
    ///
    /// # Adequacy
    /// - hypothesis: L2 exhaustive pairs distinguish swapped or conflated
    ///   blocks.
    /// - witness: `tests::finite::all_small_union_squares`
    /// - witness: `tests::finite::finite_boundaries_are_checked`
    #[inline]
    #[spec(ensures: |ret| ret.is_ok() == (left.ambient() == right.ambient()))]
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
            .map(|(a, b)| match (*a, *b) {
                | (Membership::Inside, Membership::Inside) => Block::Both,
                | (Membership::Inside, Membership::Outside) => Block::Left,
                | (Membership::Outside, Membership::Inside) => Block::Right,
                | (Membership::Outside, Membership::Outside) => Block::Neither,
            })
            .collect();
        Ok(Self { blocks })
    }

    /// Borrows the four-block presentation in ambient point order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn blocks(&self) -> &[Block]
    {
        &self.blocks
    }
}
