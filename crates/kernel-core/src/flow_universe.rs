//! Forward-only certificates over closed first-order universe codes.
//!
//! Formation checks a closed translator and replays its action on every
//! constructor pattern with rigid Base leaves. Output patterns may rearrange,
//! duplicate or discard those leaves, but cannot manufacture or inspect them.
//! `ride` replays the forward action; `stay` returns its argument in one step.
//! The syntax is an in-memory rule language, separate from native terms and
//! from universe paths. It carries no admission receipt or reusable verdict.

use alloc::boxed::Box;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
use gandr_kernel_term::ComputationId;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueTypeId;

use crate::error::KernelError;
use crate::path_universe::Dialogue;
use crate::replay::KernelVerdict;

mod coverage;
mod motive;
mod rules;
#[cfg(test)]
mod tests;

pub use motive::Endpoint;
pub use motive::Motive;
pub use motive::MotiveId;
pub use motive::Motives;
pub use motive::check_motive;
pub use rules::CertificateType;
pub use rules::beta;
pub use rules::elaborate;
pub use rules::form;
pub use rules::form_certificate;
pub use rules::replay_ride;

/// One source constructor's proposed leaf-natural output and replay dialogue.
///
/// # Specification
/// - provides: untrusted syntax; output variables refer to source leaves in
///   left-to-right telescope order, with the last leaf at de Bruijn zero.
/// - panics: none.
/// - executable: none — raw evidence has no callable boundary; formation
///   validates its output leaves and replay dialogue.
/// # Adequacy
/// - hypothesis: L3 — literal outputs and forged leaf selections refuse.
/// - witness: `flow_universe::tests::constant_leaf_and_forged_evidence_refuse`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Image
{
    /// Canonical target pattern, using only variables at Base positions.
    pub output: ValueId,
    /// Evidence for applying the translator to the kernel's source pattern.
    pub dialogue: Dialogue,
}

/// A raw flow node's position in its append-only arena.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct FlowId(usize);

/// The connection requested between two forward certificate occurrences.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Seam
{
    /// Feed the first output into the second input: one directed edge.
    Sequence,
    /// Also feed the second output back into the first input: a two-edge cycle.
    Feedback,
}

/// Forward introductions and explicitly connected composition requests.
///
/// # Specification
/// - provides: raw rule syntax with no backward translator or round trip. Only
///   formation certifies the forward action and the composition gate.
/// - panics: none.
/// - executable: none — this syntax does not execute; formation checks each
///   translator and the requested seam.
/// # Adequacy
/// - hypothesis: L3 — a terminal map forms without an inverse; feedback
///   refuses.
/// - witness: `flow_universe::tests::terminal_ride_and_stay_compute`
/// - witness: `flow_universe::tests::composition_preserves_direction_and_refuses_feedback`
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Flow
{
    /// Directed reflexivity at a quoted closed first-order code.
    Stay(ValueId),
    /// A leaf-natural forward translator with exhaustive symbolic replay.
    Forward
    {
        /// Quoted source code.
        source: ValueId,
        /// Quoted target code.
        target: ValueId,
        /// Closed thunk of `El source -> F (El target)`.
        translator: ValueId,
        /// One output and dialogue per source constructor pattern.
        images: Vec<Image>,
    },
    /// Connect two certificate occurrences; formation checks the requested
    /// seam.
    Compose
    {
        /// First forward occurrence.
        first: FlowId,
        /// Second forward occurrence.
        second: FlowId,
        /// Explicit wiring, rather than endpoint equality as a cycle proxy.
        seam: Seam,
    },
}

/// The separate certificate families at the rule-language typing boundary.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Family
{
    /// Invertible universe identity.
    Path,
    /// Forward-only universe transport.
    Flow,
}

/// A family-tagged raw certificate; neither tag coerces to the other.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Certificate
{
    /// A native universe-path value, checked afresh at its ordinary classifier.
    Path(ValueId),
    /// A universe-flow introduction.
    Flow(FlowId),
}

/// Endpoint variance in the directed classifier.
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
    const fn reverse(self) -> Self
    {
        match self {
            | Self::Contravariant => Self::Covariant,
            | Self::Covariant => Self::Contravariant,
        }
    }
}

/// `Flow_U source target`, with input contravariant and output covariant.
///
/// # Specification
/// - provides: endpoint types only; this classifier grants no authority.
/// - panics: none.
/// - executable: none — endpoint fields alone certify no translator; the
///   formation function checks their relation to the raw syntax.
/// # Adequacy
/// - hypothesis: L3 — formation retains the direction of the terminal map.
/// - witness: `flow_universe::tests::terminal_ride_and_stay_compute`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct FlowType
{
    /// Consumed endpoint.
    pub source: ValueTypeId,
    /// Produced endpoint.
    pub target: ValueTypeId,
}

/// Append-only raw certificate syntax, with no cached formation results.
#[repr(transparent)]
#[derive(Clone, Debug, Default)]
pub struct Flows(Vec<Flow>);

impl Flows
{
    /// Create an empty rule arena.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new() -> Self
    {
        Self(Vec::new())
    }

    /// Append raw syntax, validating only that composition children exist.
    ///
    /// # Specification
    /// - ensures: children precede their parent; no formation verdict is
    ///   stored.
    /// - fails: `UnknownFlow` for a missing child, without insertion.
    /// - panics: none.
    ///
    /// # Errors
    /// `FlowError::UnknownFlow`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — composition resolves each child and retains its
    ///   order.
    /// - witness: `flow_universe::tests::composition_preserves_direction_and_refuses_feedback`
    #[spec(
        captures: before = self.0.len(),
        ensures: |ret| match ret {
            Ok(id) => id.0 == before && self.0.len() == before.saturating_add(1)
                && match self.0.get(id.0) { Some(&Flow::Compose { first, second, .. }) => first.0 < id.0 && second.0 < id.0, Some(_) => true, None => false },
            Err(FlowError::UnknownFlow(id)) => self.0.len() == before && id.0 >= before,
            Err(_) => false,
        },
    )]
    #[inline]
    pub fn push(
        &mut self,
        flow: Flow,
    ) -> Result<FlowId, FlowError>
    {
        if let Flow::Compose { first, second, .. } = flow {
            self.get(first)?;
            self.get(second)?;
        }
        let id = FlowId(self.0.len());
        self.0.push(flow);
        Ok(id)
    }

    /// Resolve raw syntax, without certifying it.
    ///
    /// # Specification
    /// - ensures: returns the exact stored node.
    /// - fails: `UnknownFlow` for an out-of-range id.
    /// - panics: none.
    ///
    /// # Errors
    /// `FlowError::UnknownFlow`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — invalid ids cannot reach replay.
    /// - witness: `flow_universe::tests::formation_boundaries_refuse`
    #[spec(ensures: |ret| match ret {
        Ok(node) => self.0.get(id.0).is_some_and(|stored| core::ptr::eq(core::ptr::from_ref(node), core::ptr::from_ref(stored))),
        Err(FlowError::UnknownFlow(named)) => named == id && id.0 >= self.0.len(),
        Err(_) => false,
    })]
    fn get(
        &self,
        id: FlowId,
    ) -> Result<&Flow, FlowError>
    {
        self.0.get(id.0).ok_or(FlowError::UnknownFlow(id))
    }
}

/// Raw directed elimination, carrying the family tag checked by elaboration.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Ride
{
    /// Only a Flow certificate is admissible here.
    pub certificate: Certificate,
    /// Input value at the certificate's source.
    pub value: ValueId,
}

/// One directed beta step, before ordinary CBPV evaluation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Reduct
{
    /// `ride (stay a) v` is `return v`, without evaluating a translator.
    Return(ValueId),
    /// Forward action as an ordinary computation, including sequential bind.
    Compute(ComputationId),
}

/// A constructor-pattern position in left-first, lexicographic order.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PatternPosition(pub usize);

/// A named refusal at formation, motive elaboration or replay.
#[derive(Debug)]
pub enum FlowError
{
    /// Missing raw certificate.
    UnknownFlow(FlowId),
    /// Missing term or impossible internal assembly state.
    Arena,
    /// Endpoint is not a quoted first-order code.
    UnsupportedCode(ValueId),
    /// A code contains a former outside Unit, Base, Sum and Product.
    UnsupportedType(ValueTypeId),
    /// Ordinary closed checking refused the translator, input or output.
    Typing(Box<KernelError>),
    /// Missing or extra constructor images.
    Coverage,
    /// Output is not a canonical shape with correctly typed source leaves.
    NonNatural(ValueId),
    /// A symbolic forward obligation did not replay positively.
    ForwardReplay
    {
        /// Source constructor whose obligation failed.
        pattern: PatternPosition,
        /// Exact kernel verdict.
        verdict: KernelVerdict,
    },
    /// Composition endpoints do not match structurally.
    EndpointMismatch,
    /// Explicit feedback closes a cycle between these occurrences.
    Cycle
    {
        /// First occurrence, emitting to the second.
        first: FlowId,
        /// Second occurrence, emitting back to the first.
        second: FlowId,
    },
    /// No coercion crosses the family boundary.
    FamilyMismatch
    {
        /// Required classifier family.
        expected: Family,
        /// Supplied certificate family.
        actual: Family,
    },
    /// Moving endpoint occurs contravariantly in the motive.
    NonCovariantMotive(MotiveId),
    /// Missing motive syntax.
    UnknownMotive(MotiveId),
    /// Construction or traversal allowance exhausted.
    Budget,
    /// Formation of a correctly tagged Path failed.
    Path(crate::path_universe::PathError),
}

impl fmt::Display for FlowError
{
    /// Display the named refusal, preserving nested checker diagnostics.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match self {
            | &Self::UnknownFlow(id) => write!(f, "unknown universe flow {}", id.0),
            | &Self::Arena => f.write_str("unresolved term arena reference"),
            | &Self::UnsupportedCode(_) => f.write_str("unsupported universe-flow code"),
            | &Self::UnsupportedType(_) => f.write_str("unsupported universe-flow type"),
            | &Self::Typing(ref error) => write!(f, "universe-flow typing: {error}"),
            | &Self::Coverage => f.write_str("forward image coverage mismatch"),
            | &Self::NonNatural(_) => f.write_str("non-natural forward image"),
            | &Self::ForwardReplay { pattern, .. } => {
                write!(f, "forward replay refused at pattern {}", pattern.0)
            },
            | &Self::EndpointMismatch => f.write_str("composition endpoint mismatch"),
            | &Self::Cycle { first, second } => write!(
                f,
                "feedback cycle: {} -> {} -> {}",
                first.0, second.0, first.0
            ),
            | &Self::FamilyMismatch {
                expected: Family::Flow,
                ..
            } => f.write_str("expected Flow, found Path"),
            | &Self::FamilyMismatch {
                expected: Family::Path,
                ..
            } => f.write_str("expected Path, found Flow"),
            | &Self::NonCovariantMotive(_) => f.write_str("non-covariant directed motive"),
            | &Self::UnknownMotive(_) => f.write_str("unknown directed motive"),
            | &Self::Budget => f.write_str("universe-flow budget exhausted"),
            | &Self::Path(ref error) => write!(f, "universe-path formation: {error}"),
        }
    }
}

impl core::error::Error for FlowError
{
}

/// Finite allowance for syntax, code and symbolic-output traversal.
#[repr(transparent)]
struct Allowance(u64);

impl Allowance
{
    /// Consume one traversal step, refusing at zero.
    ///
    /// # Specification
    /// - ensures: decrements positive allowance once.
    /// - fails: `Budget` at zero, leaving it unchanged.
    /// - panics: none.
    ///
    /// # Errors
    /// `FlowError::Budget`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — zero budget cannot form a flow.
    /// - witness: `flow_universe::tests::formation_boundaries_refuse`
    #[spec(
        captures: before = self.0,
        ensures: |ret| match ret { Ok(()) => before.checked_sub(1) == Some(self.0), Err(FlowError::Budget) => before == 0 && self.0 == 0, Err(_) => false },
    )]
    fn charge(&mut self) -> Result<(), FlowError>
    {
        self.0 = self.0.checked_sub(1).ok_or(FlowError::Budget)?;
        Ok(())
    }
}
