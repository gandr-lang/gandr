//! Named carriers: a boundary's names in, `Fin(m)` out.
//!
//! A [`Boundary`] is a carrier as a store of names: a register store of
//! `gandr-theory-nominal-automata`, one register per point, every register
//! holding its point's name. The store refuses a name it would hold twice, so
//! the names are the carrier's points without repetition. The registers run in
//! name order, so every ordering of one list of names builds one boundary, and
//! a problem stated over it decides to one answer.
//!
//! The nominal reading is the carrier's. A face fixed is a set of names the
//! store retains. An inclusion of faces releases the names its target holds
//! and its source does not: the complement a [`crate::Cofibration`] presents.
//! The union square's mediator glues two maps that agree on the names of the
//! meet, and refuses the first name where they differ. A name a boundary never
//! held is refused by name, as an unknown register is refused by the store.
//!
//! The decision reads subshapes over `Fin(m)`, as membership tables. A
//! subshape as a sub-store costs 1.8 to 17.6 times a meet over the table, at
//! 8 to 1024 points, and 16 bytes a point against 1. So the names stop at
//! the boundary, and the decision path keeps its tables.
//!
//! # References
//!
//! - `vault:01a1897b-d199-7d10-a325-587b76db2508` — lineage: the shape
//!   parameter is a store of names, read from the nominal crate.

use alloc::vec::Vec;
use core::cmp::Ordering;
use core::fmt;

use anodized::spec;
use gandr_theory_nominal_automata::handle::Register;
use gandr_theory_nominal_automata::handle::Store;
use quenchant_shape::shape::Maybe;

use crate::error::ShapeError;
use crate::finite::Subshape;
use crate::finite::UnionSquare;
use crate::index::Point;
use crate::index::PointCount;

/// Why a boundary refused a name, or a map read through it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum BoundaryError<A>
{
    /// The boundary's list holds this name twice.
    Repeated(A),
    /// A face names this name, which the boundary does not hold.
    Unbound(A),
    /// The two maps out of a union square's legs differ at this name of
    /// their meet.
    Disagreement(A),
    /// A refusal of the shape operations, which names no name.
    Shape(ShapeError),
}

impl<A: fmt::Debug> fmt::Display for BoundaryError<A>
{
    /// Describes the refusal by its kind, without rendering a caller's name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::Repeated(_) => f.write_str("a boundary lists one name twice"),
            Self::Unbound(_) => f.write_str("a face names a name outside its boundary"),
            Self::Disagreement(_) => {
                f.write_str("the two maps differ at a name of the union square's meet")
            },
            Self::Shape(ref error) => error.fmt(f),
        }
    }
}

impl<A: fmt::Debug> core::error::Error for BoundaryError<A>
{
}

/// A carrier as a store of names, one register per point in name order.
///
/// # Specification
/// - ensures: register `i` holds the `i`-th least name, and no name twice.
/// - provides: the names a problem is stated in, read as the points of
///   `Fin(m)`.
/// - panics: none.
/// - executable: none — the store's own invariant carries the injectivity, and
///   the clauses of [`Self::new`] and [`Self::point`] read the order.
///
/// # Adequacy
/// - hypothesis: L3 — two orderings of one list build one boundary, and
///   `decide` answers both copies of a problem with one derivation and one
///   countermodel; a repeated name and an unbound one are refused by name.
/// - witness: `tests::boundary::permuted_copies_of_one_problem_decide_alike`
/// - witness: `tests::boundary::names_outside_or_twice_are_refused_by_name`
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Boundary<A>
{
    /// One register per point, holding its name, in name order.
    names: Store<A>,
}

impl<A: Copy + Ord> Boundary<A>
{
    /// The boundary holding exactly `names`.
    ///
    /// # Specification
    /// - ensures: the carrier has one point per name, and the points run in
    ///   name order.
    /// - fails: a name listed twice is refused by that name.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`BoundaryError::Repeated`]: the list holds the named name twice.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two orderings of one list build equal boundaries, and
    ///   a list repeating one name is refused by it.
    /// - witness: `tests::boundary::permuted_copies_of_one_problem_decide_alike`
    /// - witness: `tests::boundary::names_outside_or_twice_are_refused_by_name`
    #[inline]
    #[spec(
        captures: [given = names.clone()],
        ensures: |ref ret| match *ret {
            Ok(ref boundary) => usize::from(boundary.carrier()) == given.len()
                && given.iter().all(|name| boundary.point(*name).is_ok()),
            Err(BoundaryError::Repeated(name)) => given.iter().filter(|held| **held == name).count() > 1,
            Err(_) => false,
        },
    )]
    pub fn new(mut names: Vec<A>) -> Result<Self, BoundaryError<A>>
    {
        names.sort_unstable();
        Store::try_new(names.into_iter().map(Maybe::Present).collect())
            .map(|names| Self { names })
            .map_err(|refused| BoundaryError::Repeated(refused.atom))
    }

    /// The carrier's size: one point per name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn carrier(&self) -> PointCount
    {
        PointCount::from(usize::from(self.names.arity()))
    }

    /// The point `name` is.
    ///
    /// # Specification
    /// - ensures: the point's name is `name`.
    /// - fails: a name the boundary does not hold is refused by it.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`BoundaryError::Unbound`]: the boundary does not hold `name`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every name of a boundary reads back as itself, and a
    ///   name it lacks is refused by name.
    /// - witness: `tests::boundary::names_outside_or_twice_are_refused_by_name`
    #[inline]
    #[spec(ensures: |ref ret| match *ret {
        Ok(point) => self.name(point) == Ok(name),
        Err(refused) => refused == BoundaryError::Unbound(name),
    })]
    pub fn point(
        &self,
        name: A,
    ) -> Result<Point, BoundaryError<A>>
    {
        let (mut low, mut high) = (0_usize, usize::from(self.names.arity()));
        while low < high {
            let middle = usize::midpoint(low, high);
            let Maybe::Present(held) = self.names.name(Register::from(middle))
            else {
                break;
            };
            match held.cmp(&name) {
                Ordering::Less => low = middle.saturating_add(1),
                Ordering::Greater => high = middle,
                Ordering::Equal => return Ok(Point::from(middle)),
            }
        }
        Err(BoundaryError::Unbound(name))
    }

    /// The name of `point`.
    ///
    /// # Specification
    /// - ensures: the name the point's register holds.
    /// - fails: a point outside the carrier is refused by it.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`BoundaryError::Shape`] holding [`ShapeError::PointOutside`]: the
    ///   point is not below the carrier's size.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every point of a boundary names itself back through
    ///   [`Self::point`], and the first point past the carrier is refused.
    /// - witness: `tests::boundary::names_outside_or_twice_are_refused_by_name`
    #[inline]
    #[spec(ensures: |ref ret| match *ret {
        Ok(name) => self.names.name(Register::from(usize::from(point))) == Maybe::Present(name),
        Err(refused) => refused == BoundaryError::Shape(ShapeError::PointOutside(point))
            && usize::from(point) >= usize::from(self.carrier()),
    })]
    pub fn name(
        &self,
        point: Point,
    ) -> Result<A, BoundaryError<A>>
    {
        match self.names.name(Register::from(usize::from(point))) {
            Maybe::Present(name) => Ok(name),
            Maybe::Absent(_) => Err(BoundaryError::Shape(ShapeError::PointOutside(point))),
        }
    }

    /// The face holding exactly `names`, as a subshape of the carrier.
    ///
    /// # Specification
    /// - ensures: the subshape's carrier is the boundary's, and a point is
    ///   inside exactly when its name is listed.
    /// - fails: the first listed name the boundary does not hold is refused by
    ///   it.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`BoundaryError::Unbound`]: the boundary does not hold the name.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a face read through two orderings of one boundary
    ///   decides alike, and a face naming a name outside it is refused by that
    ///   name.
    /// - witness: `tests::boundary::permuted_copies_of_one_problem_decide_alike`
    /// - witness: `tests::boundary::names_outside_or_twice_are_refused_by_name`
    #[inline]
    #[spec(ensures: |ref ret| match *ret {
        Ok(ref face) => face.ambient() == self.carrier()
            && names.iter().all(|name| self.point(*name).is_ok_and(|point| face.contains(point) == Ok(crate::finite::Membership::Inside))),
        Err(BoundaryError::Unbound(name)) => names.contains(&name) && self.point(name).is_err(),
        Err(_) => false,
    })]
    pub fn face(
        &self,
        names: &[A],
    ) -> Result<Subshape, BoundaryError<A>>
    {
        let points = names
            .iter()
            .map(|name| self.point(*name))
            .collect::<Result<Vec<Point>, _>>()?;
        Subshape::new(self.carrier(), &points).map_err(BoundaryError::Shape)
    }

    /// The universal map out of `square`'s union, glued from a map out of
    /// each leg, with a disagreement refused by its name.
    ///
    /// # Specification
    /// - requires: `square` partitions this boundary's carrier.
    /// - ensures: the table [`UnionSquare::mediator`] glues.
    /// - fails: a disagreement is refused by the name of the point where the
    ///   maps differ; every other refusal is the square's.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`BoundaryError::Disagreement`]: the maps differ at the named name of
    ///   the meet.
    /// - [`BoundaryError::Shape`]: the square's carrier is not the boundary's,
    ///   or a table's length is the square's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two maps agreeing on the meet glue as the square
    ///   glues them, and two differing at one name of the meet are refused by
    ///   that name.
    /// - witness: `tests::boundary::the_mediator_refuses_a_disagreement_by_its_name`
    #[inline]
    #[spec(ensures: |ref ret| match *ret {
        Ok(ref glued) => square.mediator(left, right).as_ref() == Ok(glued),
        Err(BoundaryError::Disagreement(name)) => self.point(name).is_ok_and(|point| square.mediator(left, right) == Err(ShapeError::Disagreement(point))),
        Err(BoundaryError::Shape(error)) => square.mediator(left, right) == Err(error) || error == ShapeError::DifferentAmbient,
        Err(_) => false,
    })]
    pub fn mediator<Value>(
        &self,
        square: &UnionSquare,
        left: &[Value],
        right: &[Value],
    ) -> Result<Vec<Value>, BoundaryError<A>>
    where
        Value: Clone + PartialEq,
    {
        if square.blocks().len() != usize::from(self.carrier()) {
            return Err(BoundaryError::Shape(ShapeError::DifferentAmbient));
        }
        square.mediator(left, right).map_err(|refused| {
            if let ShapeError::Disagreement(point) = refused {
                self.name(point)
                    .map_or_else(|error| error, BoundaryError::Disagreement)
            }
            else {
                BoundaryError::Shape(refused)
            }
        })
    }
}
