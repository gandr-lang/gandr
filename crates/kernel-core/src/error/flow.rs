//! The refusals of the flow universe, with the certificate families and the
//! boundaries that each refusal names.

use core::fmt;

use gandr_kernel_term::AnyNode;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueTypeId;

use crate::error::replay::KernelVerdict;

/// A named refusal at admission, the covariance gate or replay.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum FlowError
{
    /// Session codes transport recorded runs, not native endpoint values.
    RecordedRunRequired,
    /// A classifier is neither `Flow` nor `Flow_U` where a flow is consumed,
    /// or a `Flow` whose carrier is no universe where a code flow is.
    ExpectedFlow(ValueTypeId),
    /// Missing term or impossible internal assembly state.
    Arena,
    /// Endpoint is not a quoted code.
    UnsupportedCode(ValueId),
    /// A code contains a former outside the vocabulary its certificate covers.
    UnsupportedType(ValueTypeId),
    /// Missing or extra constructor images.
    Coverage,
    /// An image is not a canonical shape with correctly typed source leaves.
    NonNatural(ValueId),
    /// A symbolic forward obligation did not replay positively.
    ForwardReplay
    {
        /// Source constructor whose obligation failed.
        pattern: PatternPosition,
        /// Exact kernel verdict.
        verdict: KernelVerdict,
    },
    /// Composition carriers or seam endpoints do not match.
    EndpointMismatch,
    /// An explicit feedback seam closes a cycle between these occurrences.
    Cycle
    {
        /// First occurrence, emitting to the second.
        first: ValueId,
        /// Second occurrence, emitting back to the first.
        second: ValueId,
    },
    /// No coercion crosses the family boundary.
    FamilyMismatch
    {
        /// Required classifier family.
        expected: Family,
        /// Supplied certificate family.
        actual: Family,
    },
    /// The moving binder occurs at a position other than a covariant one,
    /// inside the named former of the motive.
    NonCovariantMotive(AnyNode),
    /// A function code's boundary flow does not run in the direction its
    /// variance fixes.
    Boundary(Boundary),
    /// Construction or traversal allowance exhausted.
    Budget,
    /// A universe-path certificate's formation failed.
    Path(crate::error::path::PathError),
}

impl fmt::Display for FlowError
{
    /// Display the named refusal.
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
            Self::RecordedRunRequired => f.write_str("session transport requires a recorded run"),
            Self::ExpectedFlow(_) => f.write_str("expected a flow classifier"),
            Self::Arena => f.write_str("unresolved term arena reference"),
            Self::UnsupportedCode(_) => f.write_str("unsupported universe-flow code"),
            Self::UnsupportedType(_) => f.write_str("unsupported universe-flow type"),
            Self::Coverage => f.write_str("forward image coverage mismatch"),
            Self::NonNatural(_) => f.write_str("non-natural forward image"),
            Self::ForwardReplay { pattern, .. } => {
                write!(f, "forward replay refused at pattern {}", pattern.0)
            },
            Self::EndpointMismatch => f.write_str("composition endpoint mismatch"),
            Self::Cycle { .. } => f.write_str("a feedback seam closes a cycle"),
            Self::FamilyMismatch {
                expected: Family::Flow,
                ..
            } => f.write_str("expected Flow, found Path"),
            Self::FamilyMismatch {
                expected: Family::Path,
                ..
            } => f.write_str("expected Path, found Flow"),
            Self::NonCovariantMotive(_) => f.write_str("non-covariant directed motive"),
            Self::Boundary(Boundary::Domain) => {
                f.write_str("the domain boundary flow must run contravariantly")
            },
            Self::Boundary(Boundary::Codomain) => {
                f.write_str("the codomain boundary flow must run covariantly")
            },
            Self::Budget => f.write_str("universe-flow budget exhausted"),
            Self::Path(ref error) => write!(f, "universe-path formation: {error}"),
        }
    }
}

impl core::error::Error for FlowError
{
}

/// A constructor-pattern position in left-first, lexicographic order.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PatternPosition(pub usize);

/// The separate certificate families at a consuming boundary.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Family
{
    /// Invertible identity.
    Path,
    /// Forward-only transport.
    Flow,
}

/// A function code's boundary, marked with the variance the arrow fixes there.
///
/// # Specification
/// - provides: the boundary's position; [`Boundary::variance`] is the only
///   source of the direction a boundary flow must run.
/// - panics: none.
/// - executable: none — a position carries no behavior; admission reads its
///   variance when it orients a boundary flow.
/// # Adequacy
/// - hypothesis: L3 — a domain flow supplied covariantly and a codomain flow
///   supplied contravariantly each refuse, naming the boundary.
/// - witness: `flow_universe::tests::function::symmetry_refusal_holds_at_a_thunk_code`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Boundary
{
    /// The argument position: the arrow reverses variance here.
    Domain,
    /// The result position: the arrow preserves variance here.
    Codomain,
}

impl Boundary
{
    /// The variance the arrow fixes at this boundary, as
    /// `flow_universe::check_motive` reads an arrow.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn variance(self) -> Variance
    {
        match self {
            Self::Domain => Variance::Contravariant,
            Self::Codomain => Variance::Covariant,
        }
    }
}

/// Endpoint and boundary variance in the directed classifier.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Variance
{
    /// Consumed input; moving occurrences reverse direction here.
    Contravariant,
    /// Produced output; moving occurrences preserve direction here.
    Covariant,
}

impl Variance
{
    /// Reverse variance through an arrow domain or a flow source.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn reverse(self) -> Self
    {
        match self {
            Self::Contravariant => Self::Covariant,
            Self::Covariant => Self::Contravariant,
        }
    }
}
