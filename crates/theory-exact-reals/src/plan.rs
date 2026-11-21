//! The scoped plan DAG: the plan language that every stage of exact real
//! computation reads.
//!
//! A program over the reals cannot run as a loop over real numbers, because
//! no machine holds a real number. It is held as a plan instead. A plan is a
//! finite DAG of nodes, and each node has one of three [`Sort`]s. A
//! [`Real`] node denotes a real number: a bound variable, a dyadic constant,
//! an arithmetic operation, a cut, a builtin or the sum of a [`Recurrence`].
//! An [`Open`] node denotes an open
//! proposition, a semidecision: the two constants, a strict comparison, the
//! lower or the upper cut of a cut at a real, a finite meet or join, or a
//! bounded quantifier. A [`Domain`] node denotes a bounded set that a
//! quantifier ranges over. Every later stage reads the
//! plan: validation, approximation, the refinement machine and the
//! certificate checker.
//!
//! # Items
//!
//! A binder holds no name. A cut and the two quantifiers each bind one real
//! variable, and [`Real::Bound`] refers to it by its de Bruijn index: zero is
//! the innermost binder, and a larger index walks outward. So two plans that
//! differ only in the names of their variables are equal.
//!
//! A child is an edge, a [`NodeId`] into the same plan, never a copy. A
//! [`PlanBuilder`] appends nodes, and each node refers only to nodes before
//! it, so a builder holds a DAG by construction. [`PlanBuilder::finish`]
//! brings the nodes that the root reaches to one canonical form. Two nodes
//! of equal structure become one node, and the nodes stand in the order of a
//! depth-first walk from the root that visits children in field order and
//! places each node after its children. So a [`Plan`] holds each distinct
//! subterm once, and two plans of equal structure are equal, whatever order
//! and whatever sharing built them. A node that the root does not reach
//! leaves the plan.
//!
//! A cut, a division and a quantifier name their evidence by an [`Evidence`]
//! reference. The certificates that such a reference names, and the checks
//! that the plan is well scoped and that its evidence matches its domains,
//! are the work of later units. This module holds the data model alone.

use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
use num_bigint::BigInt;

use crate::codec::Entry;
use crate::dyadic::Dyadic;
use crate::dyadic::Exponent;
use crate::interval::NumericInterval;

/// The position of a node in a plan or in a builder.
///
/// A position names a node only in the plan or the builder that gave it. A
/// builder's positions do not name the nodes of the plan that it finishes.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct NodeId(u32);

impl TryFrom<usize> for NodeId
{
    type Error = PlanError;

    /// The position `index`, when a position counts it.
    ///
    /// # Specification
    /// - ensures: returns the position `index`.
    /// - fails: returns [`PlanError::TooManyNodes`] when `index` exceeds
    ///   `u32::MAX`.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`PlanError::TooManyNodes`]: the index exceeds `u32::MAX`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every builder and every decoded plan takes its
    ///   positions through it.
    /// - witness: `tests::plan::encoding_round_trips_generated_plans`
    #[inline]
    #[spec(ensures: |ref result| result.as_ref().map_or(true, |id| usize::try_from(id.0).ok() == Some(index)))]
    fn try_from(index: usize) -> Result<Self, PlanError>
    {
        return u32::try_from(index)
            .map(Self)
            .map_err(|_wide| PlanError::TooManyNodes);
    }
}

impl From<NodeId> for usize
{
    /// The position as an index into the nodes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(id: NodeId) -> Self
    {
        // A target narrower than 32 bits cannot hold a plan's nodes, so the
        // saturated index then names no node.
        return Self::try_from(id.0).unwrap_or(Self::MAX);
    }
}

impl From<NodeId> for u32
{
    /// The position as the codec writes it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(id: NodeId) -> Self
    {
        return id.0;
    }
}

impl From<u32> for NodeId
{
    /// The position that the codec reads.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: u32) -> Self
    {
        return Self(index);
    }
}

/// A node of sort real.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct RealId(NodeId);

/// A node of sort open.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct OpenId(NodeId);

/// A node of sort domain.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct DomainId(NodeId);

impl RealId
{
    /// The real node at `node`, for the codec that reads it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) const fn at(node: NodeId) -> Self
    {
        return Self(node);
    }

    /// The node's position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn node(self) -> NodeId
    {
        return self.0;
    }
}

impl OpenId
{
    /// The open node at `node`, for the codec that reads it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) const fn at(node: NodeId) -> Self
    {
        return Self(node);
    }

    /// The node's position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn node(self) -> NodeId
    {
        return self.0;
    }
}

impl DomainId
{
    /// The domain node at `node`, for the codec that reads it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) const fn at(node: NodeId) -> Self
    {
        return Self(node);
    }

    /// The node's position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn node(self) -> NodeId
    {
        return self.0;
    }
}

/// A de Bruijn index: zero names the innermost binder.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct DeBruijn(u32);

impl From<u32> for DeBruijn
{
    /// The index `index`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: u32) -> Self
    {
        return Self(index);
    }
}

impl From<DeBruijn> for u32
{
    /// The index as a number.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: DeBruijn) -> Self
    {
        return index.0;
    }
}

/// A natural-number exponent of a power.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Power(u32);

impl From<u32> for Power
{
    /// The exponent `power`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(power: u32) -> Self
    {
        return Self(power);
    }
}

impl From<Power> for u32
{
    /// The exponent as a number.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(power: Power) -> Self
    {
        return power.0;
    }
}

/// The most coefficients of a [`Polynomial`].
pub(crate) const COEFFICIENTS: usize = 5;

/// An integer coefficient of a [`Polynomial`].
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Coefficient(i32);

impl From<i32> for Coefficient
{
    /// The coefficient `value`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: i32) -> Self
    {
        return Self(value);
    }
}

impl From<Coefficient> for i32
{
    /// The coefficient as a number.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(coefficient: Coefficient) -> Self
    {
        return coefficient.0;
    }
}

/// A polynomial in the index of a series, with integer coefficients.
///
/// The constant coefficient is first. A polynomial holds one to five
/// coefficients, and its leading coefficient is not zero, so its degree is
/// at most four and each polynomial has one form.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Polynomial(Box<[Coefficient]>);

impl Polynomial
{
    /// The coefficients, the constant first.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn coefficients(&self) -> &[Coefficient]
    {
        return &self.0;
    }
}

impl TryFrom<Vec<Coefficient>> for Polynomial
{
    type Error = PlanError;

    /// The polynomial whose coefficients are `coefficients`, the constant
    /// first.
    ///
    /// # Specification
    /// - ensures: returns the polynomial of the coefficients.
    /// - fails: refuses no coefficients, more than five, or a last coefficient
    ///   of zero, as [`PlanError::Polynomial`].
    /// - panics: none.
    ///
    /// # Errors
    /// - [`PlanError::Polynomial`]: the coefficients are not the form of one
    ///   polynomial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an empty list, six coefficients and a zero leading
    ///   coefficient, at the builder and in the bytes.
    /// - witness: `tests::recurrence::a_malformed_ratio_is_refused_by_name`
    #[inline]
    #[spec(ensures: |ref result| result.as_ref().map_or(true, |polynomial| polynomial.0.last().is_some_and(|&leading| leading != Coefficient(0))))]
    fn try_from(coefficients: Vec<Coefficient>) -> Result<Self, PlanError>
    {
        if coefficients.len() > COEFFICIENTS {
            return Err(PlanError::Polynomial);
        }
        return match coefficients.last() {
            Some(&leading) if leading != Coefficient(0) => {
                Ok(Self(coefficients.into_boxed_slice()))
            },
            Some(_) | None => Err(PlanError::Polynomial),
        };
    }
}

/// The count `k` of squarings in the plan of `exp`: the series runs at
/// `x · 2^-k`, and its sum is raised to the power `2^k`.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Squarings(u32);

impl From<u32> for Squarings
{
    /// The count `count`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: u32) -> Self
    {
        return Self(count);
    }
}

impl From<Squarings> for u32
{
    /// The count as a number.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(squarings: Squarings) -> Self
    {
        return squarings.0;
    }
}

/// A reference to a certificate that a later unit's certificate table holds:
/// the laws of a cut, the proof that a divisor is not zero, or the evidence
/// that a domain is overt or compact.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Evidence(u32);

impl From<u32> for Evidence
{
    /// The reference `index`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: u32) -> Self
    {
        return Self(index);
    }
}

impl From<Evidence> for u32
{
    /// The reference as a number.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(evidence: Evidence) -> Self
    {
        return evidence.0;
    }
}

/// Evidence that a node may carry and need not.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum EvidenceSlot
{
    /// The plan states no evidence here.
    Absent,
    /// The plan states this evidence.
    Given(Evidence),
}

/// A real number defined as a cut: the reals strictly below it and the reals
/// strictly above it, each an open proposition about the variable that the
/// cut binds.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Cut
{
    /// An interval that contains the real.
    pub hull: NumericInterval,
    /// The lower cut: holds of the bound variable exactly below the real.
    pub lower: OpenId,
    /// The upper cut: holds of the bound variable exactly above the real.
    pub upper: OpenId,
    /// The certificate of the cut's laws.
    pub laws: Evidence,
}

/// A bounded quantifier: an open proposition about the variable that it
/// binds, over a domain.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Quantifier
{
    /// The domain that the variable ranges over.
    pub domain: DomainId,
    /// The body, with the variable at de Bruijn index zero.
    pub body: OpenId,
    /// The evidence that the quantifier needs: overtness of the domain for an
    /// existential, compactness for a universal.
    pub evidence: Evidence,
    /// The evidence of the other modality, which a negative answer needs.
    pub dual: EvidenceSlot,
}

/// A real defined as the sum of a series whose term ratio is a rational
/// function of the index.
///
/// The first term is one. The term after the term `t_n` is
/// `t_n · a · p(n) / q(n)`, for the argument `a`, the numerator `p` and the
/// denominator `q`.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Recurrence
{
    /// The argument `a`.
    pub argument: RealId,
    /// The numerator `p` of the term ratio.
    pub numerator: Polynomial,
    /// The denominator `q` of the term ratio.
    pub denominator: Polynomial,
}

/// A node of sort real.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Real
{
    /// The variable of a binder.
    Bound(DeBruijn),
    /// A dyadic constant.
    Constant(Dyadic),
    /// The sum.
    Add(RealId, RealId),
    /// The difference of the first and the second.
    Sub(RealId, RealId),
    /// The product.
    Mul(RealId, RealId),
    /// The quotient, with evidence that the divisor is not zero.
    Div
    {
        /// The dividend.
        numerator: RealId,
        /// The divisor.
        denominator: RealId,
        /// The certificate that the divisor is not zero.
        nonzero: Evidence,
    },
    /// A natural power.
    Power(RealId, Power),
    /// A real defined by its cut, which binds one variable.
    Cut(Cut),
    /// π, a builtin whose enclosure rule is the series of Machin.
    Pi,
    /// The cosine of a real, a builtin.
    Cos(RealId),
    /// The sine of a real, a builtin.
    Sin(RealId),
    /// The angle of the point `(x, y)`, a builtin: from `−π` to `π`, and `0`
    /// at the origin. The first child is `x`, the second `y`.
    Arg(RealId, RealId),
    /// The sum of a series whose term ratio is a rational function of the
    /// index. Its one rule serves `exp`, `log` and each later function of
    /// that form.
    Recurrence(Recurrence),
}

/// A node of sort open: an open proposition, which a refinement can confirm
/// and never refutes by a failed search.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Open
{
    /// The proposition that holds.
    Top,
    /// The proposition that never holds.
    Bottom,
    /// The first real lies strictly below the second.
    Less(RealId, RealId),
    /// The second real lies in the lower cut of the first, a cut, so it lies
    /// strictly below the cut's value.
    LowerCut(RealId, RealId),
    /// The second real lies in the upper cut of the first, a cut, so it lies
    /// strictly above the cut's value.
    UpperCut(RealId, RealId),
    /// Both hold: a finite meet.
    Meet(OpenId, OpenId),
    /// One holds: a finite join.
    Join(OpenId, OpenId),
    /// The body holds for some point of the domain.
    Exists(Quantifier),
    /// The body holds for every point of the domain.
    Forall(Quantifier),
}

/// A node of sort domain: a bounded set that a quantifier ranges over.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Domain
{
    /// The points of an interval.
    Interval
    {
        /// The interval.
        hull: NumericInterval,
        /// The evidence that the set is overt.
        overt: EvidenceSlot,
        /// The evidence that the set is compact.
        compact: EvidenceSlot,
    },
    /// The product of two domains.
    Product
    {
        /// The first factor.
        left: DomainId,
        /// The second factor.
        right: DomainId,
        /// The certificate of the product's modality.
        evidence: Evidence,
    },
    /// The points of a domain where an open proposition holds.
    Subdomain
    {
        /// The domain that the subdomain lies in.
        parent: DomainId,
        /// The proposition, with the point at de Bruijn index zero.
        classifier: OpenId,
        /// The certificate of the subdomain's modality.
        evidence: Evidence,
    },
}

/// The sort of a node.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Sort
{
    /// A real number.
    Real,
    /// An open proposition.
    Open,
    /// A bounded set.
    Domain,
}

/// A node of a plan.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Node
{
    /// A node of sort real.
    Real(Real),
    /// A node of sort open.
    Open(Open),
    /// A node of sort domain.
    Domain(Domain),
}

/// The root of a plan: a real to enclose, or an open proposition to decide.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Root
{
    /// A real number.
    Real(RealId),
    /// An open proposition.
    Open(OpenId),
}

impl Root
{
    /// The root's position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn node(self) -> NodeId
    {
        return match self {
            Self::Real(id) => id.0,
            Self::Open(id) => id.0,
        };
    }

    /// The sort of the root.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn sort(self) -> Sort
    {
        return match self {
            Self::Real(_) => Sort::Real,
            Self::Open(_) => Sort::Open,
        };
    }
}

/// Whether a child stands in its parent's scope or under one more binder.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Scope
{
    /// The child sees the variables its parent sees.
    Same,
    /// The child sees one more variable, at de Bruijn index zero: the lower
    /// and upper cut of a cut, the body of a quantifier, the classifier of a
    /// subdomain.
    Inner,
}

/// An edge of a node: the child's position, the sort its slot takes, and
/// the scope it stands in.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Edge
{
    /// The child.
    pub node: NodeId,
    /// The sort that the slot takes.
    pub sort: Sort,
    /// The scope that the child stands in.
    pub scope: Scope,
}

/// The edges of one node, in field order.
#[derive(Clone, Debug)]
pub struct Edges
{
    /// The edges; the first `count` are the node's.
    slots: [Edge; 3],
    /// How many edges the node has.
    count: EdgeCount,
    /// The next edge to yield.
    next: EdgeCount,
}

/// A count of edges, at most three.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
struct EdgeCount(usize);

impl Edges
{
    /// The edges in `slots`, the first `count` of them.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    const fn of(
        slots: [Edge; 3],
        count: EdgeCount,
    ) -> Self
    {
        return Self {
            slots,
            count,
            next: EdgeCount(0),
        };
    }
}

impl Iterator for Edges
{
    type Item = Edge;

    /// The next edge, in field order.
    ///
    /// # Specification
    /// - ensures: yields the node's edges in field order, each once, then none.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each node kind's edges in the sort and order its
    ///   fields give, read by the builder's checks and the canonical walk.
    /// - witness: `tests::plan::builder_refuses_a_foreign_or_missorted_child`
    /// - witness: `tests::plan::canonical_form_ignores_order_sharing_and_dead_nodes`
    #[inline]
    #[spec(ensures: |ref result| result.is_none() || self.next <= self.count)]
    fn next(&mut self) -> Option<Edge>
    {
        if self.next >= self.count {
            return None;
        }
        let edge = self.slots.get(self.next.0).copied()?;
        self.next = EdgeCount(self.next.0.saturating_add(1));
        return Some(edge);
    }
}

impl Node
{
    /// The sort of the node.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn sort(&self) -> Sort
    {
        return match *self {
            Self::Real(_) => Sort::Real,
            Self::Open(_) => Sort::Open,
            Self::Domain(_) => Sort::Domain,
        };
    }

    /// The node's edges, in field order.
    ///
    /// # Specification
    /// - ensures: one edge per child field, in declaration order, each with the
    ///   sort that its field's type names.
    /// - panics: none.
    /// - executable: none — the clause restates the match.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Edges`].
    /// - witness: `tests::plan::builder_refuses_a_foreign_or_missorted_child`
    /// - witness: `tests::plan::canonical_form_ignores_order_sharing_and_dead_nodes`
    #[inline]
    #[must_use]
    pub fn edges(&self) -> Edges
    {
        let real = |id: RealId| Edge {
            node: id.0,
            sort: Sort::Real,
            scope: Scope::Same,
        };
        let open = |id: OpenId, scope: Scope| Edge {
            node: id.0,
            sort: Sort::Open,
            scope,
        };
        let domain = |id: DomainId| Edge {
            node: id.0,
            sort: Sort::Domain,
            scope: Scope::Same,
        };
        let none = Edge {
            node: NodeId(0),
            sort: Sort::Real,
            scope: Scope::Same,
        };
        let (edges, count) = match *self {
            Self::Real(Real::Bound(_) | Real::Constant(_) | Real::Pi)
            | Self::Open(Open::Top | Open::Bottom)
            | Self::Domain(Domain::Interval { .. }) => ([none, none, none], 0),
            Self::Real(Real::Power(base, _) | Real::Cos(base) | Real::Sin(base)) => {
                ([real(base), none, none], 1)
            },
            Self::Real(Real::Recurrence(ref recurrence)) => {
                ([real(recurrence.argument), none, none], 1)
            },
            Self::Real(
                Real::Add(left, right)
                | Real::Sub(left, right)
                | Real::Mul(left, right)
                | Real::Arg(left, right),
            )
            | Self::Open(
                Open::Less(left, right) | Open::LowerCut(left, right) | Open::UpperCut(left, right),
            ) => ([real(left), real(right), none], 2),
            Self::Real(Real::Div {
                numerator,
                denominator,
                ..
            }) => ([real(numerator), real(denominator), none], 2),
            Self::Real(Real::Cut(ref cut)) => (
                [
                    open(cut.lower, Scope::Inner),
                    open(cut.upper, Scope::Inner),
                    none,
                ],
                2,
            ),
            Self::Open(Open::Meet(left, right) | Open::Join(left, right)) => {
                ([open(left, Scope::Same), open(right, Scope::Same), none], 2)
            },
            Self::Open(Open::Exists(quantifier) | Open::Forall(quantifier)) => (
                [
                    domain(quantifier.domain),
                    open(quantifier.body, Scope::Inner),
                    none,
                ],
                2,
            ),
            Self::Domain(Domain::Product { left, right, .. }) => {
                ([domain(left), domain(right), none], 2)
            },
            Self::Domain(Domain::Subdomain {
                parent, classifier, ..
            }) => ([domain(parent), open(classifier, Scope::Inner), none], 2),
        };
        return Edges::of(edges, EdgeCount(count));
    }

    /// The node with each child moved to the position that `place` gives it.
    ///
    /// # Specification
    /// - ensures: the same node kind and payload, each child replaced by
    ///   `place` of it, the children visited in field order.
    /// - fails: returns the first error that `place` returns.
    /// - panics: none.
    /// - executable: none — the clause restates the match.
    ///
    /// # Errors
    /// The first error that `place` returns.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every node kind passes through the canonical walk,
    ///   and the round trip reads each back with its children in place.
    /// - witness: `tests::plan::encoding_round_trips_generated_plans`
    /// - witness: `tests::plan::canonical_form_ignores_order_sharing_and_dead_nodes`
    pub(crate) fn moved<Place>(
        self,
        mut place: Place,
    ) -> Result<Self, PlanError>
    where
        Place: FnMut(NodeId) -> Result<NodeId, PlanError>,
    {
        return Ok(match self {
            Self::Real(node) => Self::Real(match node {
                Real::Bound(_) | Real::Constant(_) | Real::Pi => node,
                Real::Cos(argument) => Real::Cos(RealId(place(argument.0)?)),
                Real::Sin(argument) => Real::Sin(RealId(place(argument.0)?)),
                Real::Arg(x, y) => Real::Arg(RealId(place(x.0)?), RealId(place(y.0)?)),
                Real::Recurrence(recurrence) => Real::Recurrence(Recurrence {
                    argument: RealId(place(recurrence.argument.0)?),
                    ..recurrence
                }),
                Real::Add(left, right) => {
                    Real::Add(RealId(place(left.0)?), RealId(place(right.0)?))
                },
                Real::Sub(left, right) => {
                    Real::Sub(RealId(place(left.0)?), RealId(place(right.0)?))
                },
                Real::Mul(left, right) => {
                    Real::Mul(RealId(place(left.0)?), RealId(place(right.0)?))
                },
                Real::Div {
                    numerator,
                    denominator,
                    nonzero,
                } => Real::Div {
                    numerator: RealId(place(numerator.0)?),
                    denominator: RealId(place(denominator.0)?),
                    nonzero,
                },
                Real::Power(base, power) => Real::Power(RealId(place(base.0)?), power),
                Real::Cut(cut) => {
                    let lower = OpenId(place(cut.lower.0)?);
                    let upper = OpenId(place(cut.upper.0)?);
                    Real::Cut(Cut {
                        hull: cut.hull,
                        lower,
                        upper,
                        laws: cut.laws,
                    })
                },
            }),
            Self::Open(node) => Self::Open(match node {
                Open::Top | Open::Bottom => node,
                Open::Less(left, right) => {
                    Open::Less(RealId(place(left.0)?), RealId(place(right.0)?))
                },
                Open::LowerCut(cut, point) => {
                    Open::LowerCut(RealId(place(cut.0)?), RealId(place(point.0)?))
                },
                Open::UpperCut(cut, point) => {
                    Open::UpperCut(RealId(place(cut.0)?), RealId(place(point.0)?))
                },
                Open::Meet(left, right) => {
                    Open::Meet(OpenId(place(left.0)?), OpenId(place(right.0)?))
                },
                Open::Join(left, right) => {
                    Open::Join(OpenId(place(left.0)?), OpenId(place(right.0)?))
                },
                Open::Exists(quantifier) => {
                    let domain = DomainId(place(quantifier.domain.0)?);
                    let body = OpenId(place(quantifier.body.0)?);
                    Open::Exists(Quantifier {
                        domain,
                        body,
                        ..quantifier
                    })
                },
                Open::Forall(quantifier) => {
                    let domain = DomainId(place(quantifier.domain.0)?);
                    let body = OpenId(place(quantifier.body.0)?);
                    Open::Forall(Quantifier {
                        domain,
                        body,
                        ..quantifier
                    })
                },
            }),
            Self::Domain(node) => Self::Domain(match node {
                Domain::Interval { .. } => node,
                Domain::Product {
                    left,
                    right,
                    evidence,
                } => Domain::Product {
                    left: DomainId(place(left.0)?),
                    right: DomainId(place(right.0)?),
                    evidence,
                },
                Domain::Subdomain {
                    parent,
                    classifier,
                    evidence,
                } => Domain::Subdomain {
                    parent: DomainId(place(parent.0)?),
                    classifier: OpenId(place(classifier.0)?),
                    evidence,
                },
            }),
        });
    }
}

/// A count of nodes.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct NodeCount(usize);

impl From<usize> for NodeCount
{
    /// The count `count`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: usize) -> Self
    {
        return Self(count);
    }
}

impl From<NodeCount> for usize
{
    /// The count as a number.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: NodeCount) -> Self
    {
        return count.0;
    }
}

/// Where a refusal points: the input as a whole, or one node of it.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Site
{
    /// The input as a whole: its header, its length, its root or its
    /// canonical form.
    Input,
    /// The node at this position.
    Node(NodeId),
}

/// A failed plan operation.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum PlanError
{
    /// A node names a position that holds no node.
    UnknownNode,
    /// A node names a node of another sort than its slot takes.
    WrongSort,
    /// The plan holds more nodes than a position counts.
    TooManyNodes,
    /// A list of coefficients is empty, longer than five, or ends in zero.
    Polynomial,
    /// The plan of `exp` squares more often than a power counts.
    Squarings,
}

impl fmt::Display for PlanError
{
    /// Write the failure as one line.
    ///
    /// # Specification
    /// - ensures: writes one fixed phrase per variant, no two alike.
    /// - fails: propagates the formatter's own write failure unchanged.
    /// - panics: none.
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Errors
    /// Propagates the formatter's write failure.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every variant renders a distinct phrase.
    /// - witness: `tests::plan::failures_render_distinct_phrases`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        return f.write_str(match *self {
            Self::UnknownNode => "a node names a position that holds no node",
            Self::WrongSort => "a node names a node of another sort than its slot takes",
            Self::TooManyNodes => "the plan holds more nodes than a position counts",
            Self::Polynomial => "a polynomial's coefficients are empty, past five, or end in zero",
            Self::Squarings => "the plan of exp squares more often than a power counts",
        });
    }
}

impl core::error::Error for PlanError
{
}

/// An arena that a plan is built in: each node is appended after the nodes
/// that it names.
#[repr(transparent)]
#[derive(Clone, Debug, Default)]
pub struct PlanBuilder
{
    /// The nodes, each after its children.
    nodes: Vec<Node>,
}

/// The state of a builder node in the canonical walk.
#[derive(Clone, Copy, Debug)]
enum Visit
{
    /// The walk has not finished the node.
    Pending,
    /// The walk placed the node, or a node of equal structure, here.
    Placed(NodeId),
}

/// A node on the canonical walk's stack, with the next edge to follow.
#[derive(Clone, Copy, Debug)]
struct Frame
{
    /// The builder node.
    node: NodeId,
    /// How many of its edges the walk has followed.
    followed: EdgeCount,
}

impl PlanBuilder
{
    /// An empty builder.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new() -> Self
    {
        return Self { nodes: Vec::new() };
    }

    /// An empty builder with room for `capacity` nodes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn with_capacity(capacity: NodeCount) -> Self
    {
        return Self {
            nodes: Vec::with_capacity(capacity.0),
        };
    }

    /// How many nodes the builder holds.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn node_count(&self) -> NodeCount
    {
        return NodeCount(self.nodes.len());
    }

    /// The sort of the node at `id`.
    ///
    /// # Specification
    /// - ensures: returns the sort of the node at `id`.
    /// - fails: returns [`PlanError::UnknownNode`] when the builder holds no
    ///   node there.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`PlanError::UnknownNode`]: no node stands at `id`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a position past the last node and one of each sort.
    /// - witness: `tests::plan::builder_refuses_a_foreign_or_missorted_child`
    #[inline]
    #[spec(ensures: |ref result| result.is_ok() == (usize::from(id) < self.nodes.len()))]
    pub fn sort_of(
        &self,
        id: NodeId,
    ) -> Result<Sort, PlanError>
    {
        return self
            .nodes
            .get(usize::from(id))
            .map(Node::sort)
            .ok_or(PlanError::UnknownNode);
    }

    /// Append a node of sort real.
    ///
    /// # Specification
    /// - ensures: as [`PlanBuilder::push`].
    /// - fails: as [`PlanBuilder::push`].
    /// - panics: none.
    /// - executable: none — [`PlanBuilder::push`] carries the clause.
    ///
    /// # Errors
    /// As [`PlanBuilder::push`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`PlanBuilder::push`].
    /// - witness: `tests::plan::builder_refuses_a_foreign_or_missorted_child`
    #[inline]
    pub fn real(
        &mut self,
        node: Real,
    ) -> Result<RealId, PlanError>
    {
        return self.push(Node::Real(node)).map(RealId);
    }

    /// Append the plan of `exp x`: the series of ratio `1 / (n + 1)` at
    /// `x · 2^-k`, raised to the power `2^k`.
    ///
    /// # Specification
    /// - ensures: appends the constant `2^-k`, the product, the recurrence and
    ///   the power, and returns the power. With `k` zero it appends the
    ///   recurrence at `x` alone.
    /// - fails: refuses `k` past 31 as [`PlanError::Squarings`], and each
    ///   failure of [`PlanBuilder::push`].
    /// - panics: none.
    /// - executable: none — the clause speaks of the nodes appended.
    ///
    /// # Errors
    /// - [`PlanError::Squarings`]: `2^k` does not fit a power.
    /// - Each error of [`PlanBuilder::push`].
    ///
    /// # Adequacy
    /// - hypothesis: L2 — `exp 1` against `e`, and `exp (log 3)` against `3`,
    ///   each with and without squarings.
    /// - witness: `tests::recurrence::exp_of_one_encloses_e_and_its_certificate_replays`
    /// - witness: `tests::recurrence::exp_of_log_three_holds_three`
    #[inline]
    pub fn exp(
        &mut self,
        x: RealId,
        squarings: Squarings,
    ) -> Result<RealId, PlanError>
    {
        let power = 1_u32.checked_shl(squarings.0).ok_or(PlanError::Squarings)?;
        let argument = if power == 1 {
            x
        }
        else {
            let exponent = i32::try_from(squarings.0).map_err(|_wide| PlanError::Squarings)?;
            let scale = Dyadic::new(
                BigInt::from(1_u8),
                Exponent::from(exponent.saturating_neg()),
            )
            .map_err(|_overflow| PlanError::Squarings)?;
            let scale = self.real(Real::Constant(scale))?;
            self.real(Real::Mul(x, scale))?
        };
        let series = self.real(Real::Recurrence(Recurrence {
            argument,
            numerator: Polynomial::try_from(alloc::vec![Coefficient(1)])?,
            denominator: Polynomial::try_from(alloc::vec![Coefficient(1), Coefficient(1)])?,
        }))?;
        if power == 1 {
            return Ok(series);
        }
        return self.real(Real::Power(series, Power(power)));
    }

    /// Append the plan of `log x`: `2z` times the series of ratio
    /// `(2n + 1) / (2n + 3)` at `z²`, where `z = (x − 1) / (x + 1)`.
    ///
    /// # Specification
    /// - ensures: appends the plan and returns its root. Its quotient carries
    ///   `nonzero` as the evidence that `x + 1` is not zero. For each positive
    ///   `x`, `z²` lies below one, so the series converges, and the root is
    ///   `log x`.
    /// - fails: as [`PlanBuilder::push`].
    /// - panics: none.
    /// - executable: none — the clause speaks of the nodes appended.
    ///
    /// # Errors
    /// Each error of [`PlanBuilder::push`].
    ///
    /// # Adequacy
    /// - hypothesis: L2 — `log 2` against its digits, and `exp (log 3)` against
    ///   `3`.
    /// - witness: `tests::recurrence::log_of_two_encloses_its_digits_and_its_certificate_replays`
    /// - witness: `tests::recurrence::exp_of_log_three_holds_three`
    #[inline]
    pub fn log(
        &mut self,
        x: RealId,
        nonzero: Evidence,
    ) -> Result<RealId, PlanError>
    {
        let one = self.real(Real::Constant(Dyadic::ONE))?;
        let two = self.real(Real::Constant(Dyadic::from(2_i64)))?;
        let below = self.real(Real::Sub(x, one))?;
        let above = self.real(Real::Add(x, one))?;
        let z = self.real(Real::Div {
            numerator: below,
            denominator: above,
            nonzero,
        })?;
        let square = self.real(Real::Mul(z, z))?;
        let series = self.real(Real::Recurrence(Recurrence {
            argument: square,
            numerator: Polynomial::try_from(alloc::vec![Coefficient(1), Coefficient(2)])?,
            denominator: Polynomial::try_from(alloc::vec![Coefficient(3), Coefficient(2)])?,
        }))?;
        let twice = self.real(Real::Mul(two, z))?;
        return self.real(Real::Mul(twice, series));
    }

    /// Append a node of sort open.
    ///
    /// # Specification
    /// - ensures: as [`PlanBuilder::push`].
    /// - fails: as [`PlanBuilder::push`].
    /// - panics: none.
    /// - executable: none — [`PlanBuilder::push`] carries the clause.
    ///
    /// # Errors
    /// As [`PlanBuilder::push`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`PlanBuilder::push`].
    /// - witness: `tests::plan::builder_refuses_a_foreign_or_missorted_child`
    #[inline]
    pub fn open(
        &mut self,
        node: Open,
    ) -> Result<OpenId, PlanError>
    {
        return self.push(Node::Open(node)).map(OpenId);
    }

    /// Append a node of sort domain.
    ///
    /// # Specification
    /// - ensures: as [`PlanBuilder::push`].
    /// - fails: as [`PlanBuilder::push`].
    /// - panics: none.
    /// - executable: none — [`PlanBuilder::push`] carries the clause.
    ///
    /// # Errors
    /// As [`PlanBuilder::push`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`PlanBuilder::push`].
    /// - witness: `tests::plan::builder_refuses_a_foreign_or_missorted_child`
    #[inline]
    pub fn domain(
        &mut self,
        node: Domain,
    ) -> Result<DomainId, PlanError>
    {
        return self.push(Node::Domain(node)).map(DomainId);
    }

    /// Append `node` after every node it names.
    ///
    /// # Specification
    /// - ensures: appends the node and returns its position, the first position
    ///   past the nodes before it.
    /// - fails: refuses the node, the builder unchanged, when a child names no
    ///   node of the builder ([`PlanError::UnknownNode`]), a node of another
    ///   sort than its slot takes ([`PlanError::WrongSort`]), or when the
    ///   builder already holds `u32::MAX + 1` nodes
    ///   ([`PlanError::TooManyNodes`]).
    /// - panics: none.
    ///
    /// # Errors
    /// - [`PlanError::UnknownNode`]: a child names no node of the builder.
    /// - [`PlanError::WrongSort`]: a child's node has another sort than its
    ///   slot takes.
    /// - [`PlanError::TooManyNodes`]: no position counts another node.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a child past the last node, a child of each wrong
    ///   sort, and every node kind appended with children in range.
    /// - witness: `tests::plan::builder_refuses_a_foreign_or_missorted_child`
    /// - witness: `tests::plan::encoding_round_trips_generated_plans`
    #[spec(
        captures: before = self.nodes.len(),
        ensures: |ref result| match *result {
            Ok(id) => usize::from(id) == before && self.nodes.len() == before.saturating_add(1),
            Err(_) => self.nodes.len() == before,
        }
    )]
    pub(crate) fn push(
        &mut self,
        node: Node,
    ) -> Result<NodeId, PlanError>
    {
        for edge in node.edges() {
            if self.sort_of(edge.node)? != edge.sort {
                return Err(PlanError::WrongSort);
            }
        }
        let id = NodeId::try_from(self.nodes.len())?;
        self.nodes.push(node);
        return Ok(id);
    }

    /// The plan of the nodes that `root` reaches, in canonical form.
    ///
    /// The walk is depth first from the root. It follows each node's edges
    /// in field order and places a node after its children. A node whose
    /// structure equals a node already placed takes that node's position. So
    /// the plan holds each distinct subterm once, the nodes that the root
    /// does not reach are gone, and the order depends on the structure
    /// alone. The walk keeps its own stack, so a deep plan uses no machine
    /// stack.
    ///
    /// # Specification
    /// - ensures: the plan's nodes are the distinct structures that the root
    ///   reaches, each once, each after its children, in the order in which a
    ///   depth-first walk from the root in field order first finishes each; the
    ///   root stands last.
    /// - fails: returns [`PlanError::UnknownNode`] or [`PlanError::WrongSort`]
    ///   when `root` names no node of its sort.
    /// - panics: none.
    /// - executable: none — the clause restates the walk.
    ///
    /// # Errors
    /// - [`PlanError::UnknownNode`]: `root` names no node.
    /// - [`PlanError::WrongSort`]: `root` names a node of the other sort.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one DAG built in two orders, with and without shared
    ///   children and with dead nodes, gives one plan; a chain of squares keeps
    ///   one node per square; a foreign root is refused.
    /// - witness: `tests::plan::canonical_form_ignores_order_sharing_and_dead_nodes`
    /// - witness: `tests::plan::shared_subterms_serialize_once`
    /// - witness: `tests::plan::builder_refuses_a_foreign_or_missorted_child`
    #[inline]
    pub fn finish(
        self,
        root: Root,
    ) -> Result<Plan, PlanError>
    {
        return self.canonical(root).map(|(plan, _visits)| plan);
    }

    /// The plan of the nodes that `root` reaches, in canonical form, as
    /// [`Self::finish`] gives it, and the position in it of each node of the
    /// builder.
    ///
    /// # Specification
    /// - ensures: the plan that [`Self::finish`] gives. The place at index `i`
    ///   is the plan's position of the builder's node at `i`, or `None` when
    ///   the root does not reach it.
    /// - fails: as [`Self::finish`].
    /// - panics: none.
    /// - executable: none — the clause restates the walk.
    ///
    /// # Errors
    /// - [`PlanError::UnknownNode`]: `root` names no node.
    /// - [`PlanError::WrongSort`]: `root` names a node of the other sort.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every comparison of the generated plans that the
    ///   elimination rewrites keeps its place in the rewritten plan.
    /// - witness: `tests::elimination::generated_plans_answer_alike_after_the_elimination`
    pub(crate) fn finish_placed(
        self,
        root: Root,
    ) -> Result<(Plan, Vec<Option<NodeId>>), PlanError>
    {
        let (plan, visits) = self.canonical(root)?;
        let places = visits
            .into_iter()
            .map(|visit| match visit {
                Visit::Placed(position) => Some(position),
                Visit::Pending => None,
            })
            .collect();
        return Ok((plan, places));
    }

    /// The canonical walk of [`Self::finish`], and the visit of each node of
    /// the builder.
    ///
    /// # Specification
    /// trivial.
    fn canonical(
        self,
        root: Root,
    ) -> Result<(Plan, Vec<Visit>), PlanError>
    {
        if self.sort_of(root.node())? != root.sort() {
            return Err(PlanError::WrongSort);
        }
        let Self { mut nodes } = self;
        let mut visits = Vec::new();
        visits.resize(nodes.len(), Visit::Pending);
        let mut placed: Vec<Node> = Vec::with_capacity(nodes.len());
        let mut by_content: BTreeMap<Entry, NodeId> = BTreeMap::new();
        let mut entry = Entry::default();
        let mut stack = Vec::from([Frame {
            node: root.node(),
            followed: EdgeCount(0),
        }]);
        while let Some(frame) = stack.last_mut() {
            let node = nodes
                .get(usize::from(frame.node))
                .ok_or(PlanError::UnknownNode)?;
            if let Some(edge) = node.edges().nth(frame.followed.0) {
                frame.followed = EdgeCount(frame.followed.0.saturating_add(1));
                if matches!(visits.get(usize::from(edge.node)), Some(Visit::Pending)) {
                    stack.push(Frame {
                        node: edge.node,
                        followed: EdgeCount(0),
                    });
                }
                continue;
            }
            // Every child is placed: place the node, or find its equal.
            let id = frame.node;
            let _finished = stack.pop();
            let slot = nodes
                .get_mut(usize::from(id))
                .ok_or(PlanError::UnknownNode)?;
            let taken = core::mem::replace(slot, Node::Open(Open::Top));
            let moved = taken.moved(|child| {
                return match visits.get(usize::from(child)) {
                    Some(&Visit::Placed(position)) => Ok(position),
                    Some(&Visit::Pending) | None => Err(PlanError::UnknownNode),
                };
            })?;
            entry.clear();
            entry.node(&moved);
            let position = if let Some(&existing) = by_content.get(&entry) {
                existing
            }
            else {
                let fresh = NodeId::try_from(placed.len())?;
                let _absent = by_content.insert(entry.clone(), fresh);
                placed.push(moved);
                fresh
            };
            let visit = visits
                .get_mut(usize::from(id))
                .ok_or(PlanError::UnknownNode)?;
            *visit = Visit::Placed(position);
        }
        let last = NodeId::try_from(placed.len().saturating_sub(1))?;
        let root = match root {
            Root::Real(_) => Root::Real(RealId(last)),
            Root::Open(_) => Root::Open(OpenId(last)),
        };
        return Ok((
            Plan {
                nodes: placed,
                root,
            },
            visits,
        ));
    }
}

/// A plan in canonical form: the distinct nodes that its root reaches, each
/// once, each after its children, the root last.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Plan
{
    /// The nodes, in canonical order.
    nodes: Vec<Node>,
    /// The root, the last node.
    root: Root,
}

impl Plan
{
    /// The root.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn root(&self) -> Root
    {
        return self.root;
    }

    /// How many distinct nodes the plan holds.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn node_count(&self) -> NodeCount
    {
        return NodeCount(self.nodes.len());
    }

    /// The node at `id`.
    ///
    /// # Specification
    /// - ensures: returns the node at `id`.
    /// - fails: returns [`PlanError::UnknownNode`] when the plan holds no node
    ///   there.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`PlanError::UnknownNode`]: no node stands at `id`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the cut of the square root of two read node by node,
    ///   and a position past its last node.
    /// - witness: `tests::plan::the_square_root_of_two_is_a_small_cut`
    #[inline]
    #[spec(ensures: |ref result| result.is_ok() == (usize::from(id) < self.nodes.len()))]
    pub fn node(
        &self,
        id: NodeId,
    ) -> Result<&Node, PlanError>
    {
        return self
            .nodes
            .get(usize::from(id))
            .ok_or(PlanError::UnknownNode);
    }

    /// The nodes with their positions, in canonical order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn nodes(&self) -> impl Iterator<Item = (NodeId, &Node)>
    {
        return self
            .nodes
            .iter()
            .enumerate()
            .map_while(|(index, node)| NodeId::try_from(index).ok().map(|id| (id, node)));
    }

    /// The plan that the node at `node` roots, in canonical form, and the
    /// position in this plan of each of its nodes.
    ///
    /// The walk is depth first from `node`, in field order, as
    /// [`PlanBuilder::finish`] walks. This plan holds each distinct subterm
    /// once, so the nodes that `node` reaches are distinct too. The result is
    /// the plan that `finish` gives for the same root.
    ///
    /// # Specification
    /// - ensures: the result's nodes are the nodes that `node` reaches, each
    ///   once, each after its children, the root last. The node at position `i`
    ///   of the result is the node at the `i`-th position that the map names,
    ///   its children moved to their new positions.
    /// - fails: returns [`PlanError::UnknownNode`] when no node stands at
    ///   `node`, and [`PlanError::WrongSort`] for a domain node, which roots no
    ///   plan.
    /// - panics: none.
    /// - executable: none — the clause restates the walk.
    /// - intension: one walk of the nodes that `node` reaches, one copy of
    ///   each, and one table of this plan's nodes.
    ///
    /// # Errors
    /// - [`PlanError::UnknownNode`]: no node stands at `node`.
    /// - [`PlanError::WrongSort`]: the node is a domain.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the node of each obligation of the machine's test
    ///   corpus roots a plan whose cached certificate answers it again. L3 — a
    ///   subterm that two plans hold at other positions roots one plan in both.
    /// - witness: `tests::cache::the_corpus_answers_alike_cached_and_uncached`
    /// - witness: `tests::cache::a_subterm_shared_by_two_plans_shares_its_entry`
    pub(crate) fn rooted(
        &self,
        node: NodeId,
    ) -> Result<(Self, Vec<NodeId>), PlanError>
    {
        let root = match *self.node(node)? {
            Node::Real(_) => Root::Real(RealId(node)),
            Node::Open(_) => Root::Open(OpenId(node)),
            Node::Domain(_) => return Err(PlanError::WrongSort),
        };
        let mut placed: Vec<Option<NodeId>> = alloc::vec![None; self.nodes.len()];
        let mut nodes: Vec<Node> = Vec::new();
        let mut origin: Vec<NodeId> = Vec::new();
        let mut stack = Vec::from([Frame {
            node,
            followed: EdgeCount(0),
        }]);
        while let Some(frame) = stack.last_mut() {
            let current = self.node(frame.node)?;
            if let Some(edge) = current.edges().nth(frame.followed.0) {
                frame.followed = EdgeCount(frame.followed.0.saturating_add(1));
                if matches!(placed.get(usize::from(edge.node)), Some(&None)) {
                    stack.push(Frame {
                        node: edge.node,
                        followed: EdgeCount(0),
                    });
                }
                continue;
            }
            // Every child is placed: place the node.
            let id = frame.node;
            let _finished = stack.pop();
            let moved = current.clone().moved(|child| {
                return placed
                    .get(usize::from(child))
                    .copied()
                    .flatten()
                    .ok_or(PlanError::UnknownNode);
            })?;
            let fresh = NodeId::try_from(nodes.len())?;
            nodes.push(moved);
            origin.push(id);
            let slot = placed
                .get_mut(usize::from(id))
                .ok_or(PlanError::UnknownNode)?;
            *slot = Some(fresh);
        }
        let last = NodeId::try_from(nodes.len().saturating_sub(1))?;
        let root = match root {
            Root::Real(_) => Root::Real(RealId(last)),
            Root::Open(_) => Root::Open(OpenId(last)),
        };
        return Ok((Self { nodes, root }, origin));
    }
}
