//! Flat positive face formulas over mixed finite and affine coordinates.

use alloc::vec::Vec;

use anodized::spec;

use crate::affine::Endpoint;
use crate::boundary::Case;
use crate::boundary::NodeId;
use crate::boundary::Point;
use crate::boundary::PointCount;
use crate::boundary::ShapeError;
use crate::boundary::Variable;
use crate::finite::Membership;
use crate::finite::Subshape;

/// A shape pseudotype in the mixed context.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Shape
{
    /// The affine bridge pseudotype, distinct from every finite carrier.
    Bridge,
    /// A finite outer carrier with decidable subshapes.
    Finite(PointCount),
}

impl Shape
{
    /// Counts the complete observation cases of this shape.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn cases(self) -> Case
    {
        Case(match self {
            | Self::Bridge => 3,
            | Self::Finite(count) => count.0,
        })
    }

    /// Decodes one observation case, with generic first for the bridge.
    ///
    /// # Specification
    /// - provides: every finite point once, or generic, zero, one for a bridge.
    /// - fails: cases outside the observation domain are refused.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`ShapeError::CaseOutside`] for an invalid case.
    ///
    /// # Adequacy
    /// - hypothesis: L3 all bridge cases, empty finite domains, and finite
    ///   endpoints distinguish omissions and off-by-one boundaries.
    /// - witness: `tests::faces::input_boundaries_are_checked`
    #[inline]
    #[spec(ensures: |ret| ret.is_ok() == (case.0 < self.cases().0))]
    pub fn value(
        self,
        case: Case,
    ) -> Result<Value, ShapeError>
    {
        match (self, case.0) {
            | (Self::Bridge, 0) => Ok(Value::Generic),
            | (Self::Bridge, 1) => Ok(Value::Endpoint(Endpoint::Zero)),
            | (Self::Bridge, 2) => Ok(Value::Endpoint(Endpoint::One)),
            | (Self::Finite(count), point) if point < count.0 => Ok(Value::Point(Point(point))),
            | _ => Err(ShapeError::CaseOutside),
        }
    }
}

/// An observed coordinate, including an unassigned position during search.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Value
{
    /// Not yet split; rejected in a countermodel.
    Unassigned,
    /// A fresh bridge variable, at neither endpoint.
    Generic,
    /// A bridge endpoint.
    Endpoint(Endpoint),
    /// A finite carrier point.
    Point(Point),
}

/// One node in a formula table; children must precede their parent.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Node
{
    /// Truth.
    Top,
    /// Falsity.
    Bottom,
    /// An endpoint face `variable = endpoint`.
    Endpoint(Variable, Endpoint),
    /// Membership of a finite variable in a decidable subshape.
    Member(Variable, Subshape),
    /// Conjunction.
    And(NodeId, NodeId),
    /// Disjunction.
    Or(NodeId, NodeId),
}

/// A nonempty, topologically ordered formula DAG, rooted at its last node.
///
/// # Specification
/// - ensures: every child index is strictly earlier than its parent.
/// - provides: finite, stack-safe syntax; coordinate sorts are checked by
///   [`Problem::new`]. Repeated occurrences of an atom are permitted.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 generated formulas distinguish connective semantics; L3
///   malformed tables distinguish cycles, missing roots, and forward edges.
/// - witness: `tests::faces::generated_queries_agree_with_brute_force`
/// - witness: `tests::faces::input_boundaries_are_checked`
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Formula
{
    /// The root follows every node it references.
    nodes: Vec<Node>,
}

impl Formula
{
    /// Admits a topologically ordered formula table.
    ///
    /// # Specification
    /// - ensures: a root exists and all child references point backwards.
    /// - fails: empty, cyclic or forward-referencing tables are refused.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`ShapeError::MalformedFormula`] on invalid syntax.
    ///
    /// # Adequacy
    /// - hypothesis: L3 malformed tables distinguish acceptance without
    ///   checking both children, and L2 exercises valid shared subformulas.
    /// - witness: `tests::faces::input_boundaries_are_checked`
    /// - witness: `tests::faces::generated_queries_agree_with_brute_force`
    #[inline]
    #[spec(ensures: |ret| ret.as_ref().is_ok_and(|face| !face.nodes.is_empty()) || ret.is_err())]
    pub fn new(nodes: Vec<Node>) -> Result<Self, ShapeError>
    {
        if nodes.is_empty() {
            return Err(ShapeError::MalformedFormula);
        }
        for (index, node) in nodes.iter().enumerate() {
            if let Node::And(a, b) | Node::Or(a, b) = *node
                && (a.0 >= index || b.0 >= index)
            {
                return Err(ShapeError::MalformedFormula);
            }
        }
        Ok(Self { nodes })
    }

    /// Borrows the flat formula table, including its final root.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn nodes(&self) -> &[Node]
    {
        &self.nodes
    }

    /// Checks every atom against its context's variable and shape declarations.
    ///
    /// # Specification
    /// - ensures: all endpoint atoms have bridge variables and all membership
    ///   atoms have finite variables of the subset's ambient cardinality.
    /// - fails: missing variables and mismatched shapes are refused by
    ///   variable.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`ShapeError::VariableOutside`] or [`ShapeError::WrongShape`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 malformed atoms distinguish shape and scope checks.
    /// - witness: `tests::faces::input_boundaries_are_checked`
    // executable: none — successful validation has no output data beyond unit;
    // the independent input-boundary witnesses exercise each refusal.
    fn check_context(
        &self,
        context: &[Shape],
    ) -> Result<(), ShapeError>
    {
        for node in &self.nodes {
            let (variable, expected) = match *node {
                | Node::Endpoint(var, _) => (var, Shape::Bridge),
                | Node::Member(var, ref subset) => (var, Shape::Finite(subset.ambient())),
                | Node::Top | Node::Bottom | Node::And(..) | Node::Or(..) => continue,
            };
            let actual = context
                .get(variable.0)
                .ok_or(ShapeError::VariableOutside(variable))?;
            if *actual != expected {
                return Err(ShapeError::WrongShape(variable));
            }
        }
        Ok(())
    }

    /// Computes sound truth bounds under a partial assignment.
    ///
    /// # Specification
    /// - requires: atom shapes agree with the context; assigned coordinates
    ///   have that shape. These invariants are established by problem admission
    ///   and the search or evidence validator before evaluation.
    /// - ensures: `Yes` means every completion satisfies the formula, `No`
    ///   means no completion satisfies it; a total assignment never gives
    ///   `Open`.
    /// - fails: broken table, assignment or point invariants are refused.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`ShapeError::MalformedFormula`],
    /// [`ShapeError::VariableOutside`], [`ShapeError::WrongShape`] or
    /// [`ShapeError::PointOutside`] for broken invariants.
    ///
    /// # Adequacy
    /// - hypothesis: L2 independent full-assignment evaluation detects unsound
    ///   pruning; L3 excludes bridge endpoint coverage at a generic coordinate.
    /// - witness: `tests::faces::generated_queries_agree_with_brute_force`
    /// - witness: `tests::faces::generic_coordinates_refute_endpoint_coverage`
    // executable: none — the truth-bound obligation quantifies over completions;
    // checking it here would rerun an exponential oracle on every search step.
    pub(crate) fn evaluate(
        &self,
        assignment: &[Value],
        scratch: &mut Vec<Truth>,
    ) -> Result<Truth, ShapeError>
    {
        scratch.clear();
        for node in &self.nodes {
            let truth = match *node {
                | Node::Top => Truth::Yes,
                | Node::Bottom => Truth::No,
                | Node::Endpoint(var, endpoint) => match assignment.get(var.0).copied() {
                    | Some(Value::Unassigned) => Truth::Open,
                    | Some(Value::Generic) => Truth::No,
                    | Some(Value::Endpoint(actual)) => {
                        if actual == endpoint {
                            Truth::Yes
                        }
                        else {
                            Truth::No
                        }
                    },
                    | Some(Value::Point(_)) => return Err(ShapeError::WrongShape(var)),
                    | None => return Err(ShapeError::VariableOutside(var)),
                },
                | Node::Member(var, ref subset) => match assignment.get(var.0).copied() {
                    | Some(Value::Unassigned) => {
                        if subset.decisions().iter().all(|v| *v == Membership::Outside) {
                            Truth::No
                        }
                        else if subset.decisions().iter().all(|v| *v == Membership::Inside) {
                            Truth::Yes
                        }
                        else {
                            Truth::Open
                        }
                    },
                    | Some(Value::Point(point)) => match subset.contains(point)? {
                        | Membership::Inside => Truth::Yes,
                        | Membership::Outside => Truth::No,
                    },
                    | Some(Value::Generic | Value::Endpoint(_)) => {
                        return Err(ShapeError::WrongShape(var));
                    },
                    | None => return Err(ShapeError::VariableOutside(var)),
                },
                | Node::And(a, b) | Node::Or(a, b) => {
                    let a = *scratch.get(a.0).ok_or(ShapeError::MalformedFormula)?;
                    let b = *scratch.get(b.0).ok_or(ShapeError::MalformedFormula)?;
                    match (node, a, b) {
                        | (&Node::And(..), Truth::No, _)
                        | (&Node::And(..), _, Truth::No)
                        | (&Node::Or(..), Truth::No, Truth::No) => Truth::No,
                        | (&Node::And(..), Truth::Yes, Truth::Yes)
                        | (&Node::Or(..), Truth::Yes, _)
                        | (&Node::Or(..), _, Truth::Yes) => Truth::Yes,
                        | _ => Truth::Open,
                    }
                },
            };
            scratch.push(truth);
        }
        scratch.last().copied().ok_or(ShapeError::MalformedFormula)
    }
}

/// Truth bounds for a partial assignment.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Truth
{
    /// Forced true.
    Yes,
    /// Forced false.
    No,
    /// Depends on coordinates not yet assigned, or bounds are inconclusive.
    Open,
}

/// An admitted entailment query in one mixed shape context.
///
/// # Specification
/// - ensures: both formulas are well scoped and all atoms are well sorted.
/// - provides: a reusable query for oracle, replay, and countermodel checking.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 context admission rejects ill-sorted queries on either
///   side.
/// - witness: `tests::faces::input_boundaries_are_checked`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Problem
{
    /// Coordinate declarations, in assignment order.
    context: Vec<Shape>,
    /// The assumed face.
    premise: Formula,
    /// The required face.
    conclusion: Formula,
}

impl Problem
{
    /// Admits a query after checking every atom in both formulas.
    ///
    /// # Specification
    /// - ensures: both formulas use variables of their declared shapes.
    /// - fails: an out-of-scope or wrongly shaped atom is refused.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`ShapeError::VariableOutside`] or [`ShapeError::WrongShape`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 malformed atoms on either side distinguish incomplete
    ///   context validation.
    /// - witness: `tests::faces::input_boundaries_are_checked`
    // executable: none — admission's semantic obligations are exercised by
    // independent malformed-input witnesses rather than repeating admission.
    #[inline]
    pub fn new(
        context: Vec<Shape>,
        premise: Formula,
        conclusion: Formula,
    ) -> Result<Self, ShapeError>
    {
        premise.check_context(&context)?;
        conclusion.check_context(&context)?;
        Ok(Self {
            context,
            premise,
            conclusion,
        })
    }

    /// Borrows the context and the ordered premise/conclusion pair.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn parts(&self) -> (&[Shape], &Formula, &Formula)
    {
        (&self.context, &self.premise, &self.conclusion)
    }
}
