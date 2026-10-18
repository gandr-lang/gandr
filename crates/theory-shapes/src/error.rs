//! The typed refusals of shape construction, query admission and evidence
//! checking.

use core::fmt;

use crate::finite::Leg;
use crate::index::NodeId;
use crate::index::Point;
use crate::index::Variable;

/// A malformed input or invalid evidence; never a negative entailment result.
///
/// A refuted entailment is [`Evidence::Refuted`], an answer. This type is
/// the refusal of something that is not a well-formed question or not a
/// valid answer to one.
///
/// [`Evidence::Refuted`]: crate::Evidence::Refuted
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ShapeError
{
    /// A point lies outside its finite carrier.
    PointOutside(Point),
    /// Two subshapes have different carriers.
    DifferentAmbient,
    /// The source of an inclusion holds this point, which its target lacks.
    NotIncluded(Point),
    /// A map out of one leg of a union square has a table of the wrong length.
    MapLength(Leg),
    /// The two maps out of a union square's legs differ at this point of
    /// their meet.
    Disagreement(Point),
    /// A formula table is empty, or a child does not precede its parent.
    MalformedFormula,
    /// An atom or a piece of evidence names a variable outside the context.
    VariableOutside(Variable),
    /// A membership atom's subshape lies in another carrier than its
    /// variable's.
    WrongCarrier(Variable),
    /// A query formula holds a disjunction at this node: the decided band is
    /// conjunctive.
    Disjunction(NodeId),
    /// A countermodel's assignment and the context differ in length.
    AssignmentLength,
    /// A countermodel assigns this variable a point outside its carrier.
    AssignedOutside(Variable),
    /// A countermodel does not satisfy the premise, or satisfies the
    /// conclusion.
    NotCountermodel,
    /// An empty-carrier derivation names a variable whose carrier has a point.
    CarrierInhabited(Variable),
    /// A false-premise derivation names a node that is not a reachable `⊥`
    /// of the premise.
    NotPremiseBottom(NodeId),
    /// A citation names a node that is not a reachable membership atom of the
    /// premise.
    NotPremiseMember(NodeId),
    /// A citation names a membership atom of another variable than the one
    /// it is cited for.
    CitedVariable(NodeId),
    /// A disjointness derivation's cited atoms meet in a nonempty subshape of
    /// this variable's carrier.
    NotDisjoint(Variable),
    /// A supported derivation does not carry one citation per conclusion
    /// atom.
    CitationCount,
    /// The conclusion atom at this node does not include the meet of its
    /// citation, or is `⊥`.
    Unsupported(NodeId),
}

impl fmt::Display for ShapeError
{
    /// Renders the refusal and the index it names.
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
            Self::PointOutside(point) => {
                write!(f, "point {} outside its carrier", usize::from(point))
            },
            Self::DifferentAmbient => f.write_str("subshapes of different carriers"),
            Self::NotIncluded(point) => {
                write!(
                    f,
                    "point {} outside the inclusion's target",
                    usize::from(point)
                )
            },
            Self::MapLength(leg) => write!(f, "{leg} map has the wrong length"),
            Self::Disagreement(point) => {
                write!(f, "maps disagree at meet point {}", usize::from(point))
            },
            Self::MalformedFormula => f.write_str("malformed formula table"),
            Self::VariableOutside(variable) => {
                write!(f, "variable {} outside the context", usize::from(variable))
            },
            Self::WrongCarrier(variable) => {
                write!(
                    f,
                    "atom at variable {} in another carrier",
                    usize::from(variable)
                )
            },
            Self::Disjunction(node) => {
                write!(
                    f,
                    "disjunction at node {} outside the conjunctive band",
                    usize::from(node)
                )
            },
            Self::AssignmentLength => f.write_str("assignment length differs from the context"),
            Self::AssignedOutside(variable) => {
                write!(
                    f,
                    "variable {} assigned outside its carrier",
                    usize::from(variable)
                )
            },
            Self::NotCountermodel => f.write_str("assignment is not a countermodel"),
            Self::CarrierInhabited(variable) => {
                write!(
                    f,
                    "carrier of variable {} is inhabited",
                    usize::from(variable)
                )
            },
            Self::NotPremiseBottom(node) => {
                write!(f, "node {} is not a premise bottom", usize::from(node))
            },
            Self::NotPremiseMember(node) => {
                write!(
                    f,
                    "node {} is not a premise membership atom",
                    usize::from(node)
                )
            },
            Self::CitedVariable(node) => {
                write!(f, "cited atom {} is on another variable", usize::from(node))
            },
            Self::NotDisjoint(variable) => {
                write!(f, "cited atoms meet at variable {}", usize::from(variable))
            },
            Self::CitationCount => f.write_str("one citation per conclusion atom expected"),
            Self::Unsupported(node) => {
                write!(f, "conclusion atom {} is unsupported", usize::from(node))
            },
        }
    }
}

impl core::error::Error for ShapeError
{
}
