//! Guarded observations of identity between identities.
//!
//! A layer checks `Rel(quote(Rel(code, a, b)), p, q)` using the existing code
//! fold. Its tail observes the diagonal of that checked layer. Raw programs
//! are finite graphs: a constructor guards a recursive edge, while a cycle of
//! redirects is non-productive. Success states only the requested finite depth.
//! These arena-relative objects neither enter conversion nor admit
//! declarations.

use alloc::boxed::Box;
use alloc::collections::BTreeSet;
use alloc::vec::Vec;
use core::fmt;

use gandr_kernel_term::TermArena;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueTypeId;

use crate::conv::Convertibility;
use crate::conv::equal_values;
use crate::identity_recursion::Domain;
use crate::identity_recursion::Identity;
use crate::identity_recursion::Mode;
use crate::identity_recursion::Relation;
use crate::identity_recursion::RelationError;
use crate::identity_recursion::interpret;
use crate::path_universe::PathError;
use crate::replay::KernelVerdict;
use crate::replay::ReplayBudget;

mod certificate;
mod square;
#[cfg(test)]
mod tests;

pub use certificate::CertificateIdentity;
pub use certificate::Coherence;
pub use certificate::CoherenceEvidence;
pub use certificate::Pointwise;
pub use certificate::PointwiseEvidence;
pub use certificate::Reduction;
pub use certificate::unfold;
pub use square::Square;
pub use square::symmetry;

/// An untrusted native identity boundary and its fibre inhabitant.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Cell
{
    /// The quoted element type, retained in the original arena.
    pub code: ValueId,
    /// Source endpoint.
    pub left: ValueId,
    /// Target endpoint.
    pub right: ValueId,
    /// Native evidence, checked anew by every consuming operation.
    pub evidence: ValueId,
}

impl Cell
{
    /// Check this cell through the code-derived identity relation.
    ///
    /// # Specification
    /// - ensures: the result witnesses exactly this boundary in `context`.
    /// - fails: `Relation` for unsupported codes, indices or evidence.
    /// - panics: none.
    ///
    /// # Errors
    /// `HigherError::Relation`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — forged and cross-injection evidence refuses.
    /// - witness: `higher_field::tests::higher_fibres_preserve_boundaries`
    #[inline]
    pub fn check(
        self,
        arena: &mut TermArena,
        context: &[ValueTypeId],
    ) -> Result<Identity, HigherError>
    {
        let relation = relation(arena, self.code)?;
        let identity = relation.witness(arena, context, self.left, self.right, self.evidence)?;
        Ok(identity)
    }
}

/// A raw address in a higher-field program, including potentially invalid
/// edges.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct HigherId(pub usize);

/// One instruction of a guarded, first-order coalgebra program.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Layer
{
    /// Expose evidence for the current higher identity, then its diagonal tail.
    Guard
    {
        /// An inhabitant of the current fibre of the fibre.
        evidence: ValueId,
        /// Delayed observation of identity of this evidence with itself.
        tail: HigherId,
    },
    /// Follow an edge without exposing a constructor or advancing depth.
    Redirect(HigherId),
}

/// Finite syntax for potentially infinite higher evidence; no stored verdict.
#[derive(Clone, Debug)]
pub struct Codata
{
    /// Raw nodes; forward, cyclic and invalid references remain untrusted.
    pub nodes: Vec<Layer>,
    /// The requested starting observation.
    pub root: HigherId,
}

/// Number of constructor layers requested, starting at identity of identities.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Depth(pub u32);

/// Independent finite ceilings for higher observations and conversion replay.
#[derive(Clone, Copy, Debug)]
pub struct ObservationBudget
{
    /// Required constructor depth; zero is refused, not a vacuous proof.
    pub depth: Depth,
    /// Maximum instructions in each higher observation; also each CBPV replay.
    pub replay: ReplayBudget,
}

/// A checked finite prefix, never an assertion about an unobserved tail.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Prefix
{
    /// The first checked higher cell, with its arena-relative fibre code.
    pub head: Cell,
    /// Exactly the constructor depth actually checked.
    pub depth: Depth,
}

/// A failure at a higher-field observation boundary.
#[derive(Debug)]
pub enum HigherError
{
    /// Existing code recursion, native evidence or typing refused.
    Relation(RelationError),
    /// Existing universe-path formation refused.
    Path(Box<PathError>),
    /// The two cells or the fibre action do not share the required boundary.
    Boundary,
    /// An unguarded cycle was reached within one observation.
    NonProductive(HigherId),
    /// The instruction allowance ended before the requested constructor depth.
    DepthBound,
    /// An observation request must expose at least one constructor.
    ZeroDepth,
    /// A raw program edge does not resolve.
    UnknownLayer(HigherId),
    /// This certificate-record observation requires an equivalence
    /// introduction.
    ExpectedEquivalence,
    /// A computation's claimed reduction did not replay positively.
    Replay(KernelVerdict),
    /// The existing native family action is still neutral.
    NeutralTransport,
}

impl fmt::Display for HigherError
{
    /// Describe the refusal without erasing its class.
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
            | Self::Relation(ref error) => write!(f, "higher relation refused: {error}"),
            | Self::Path(ref error) => write!(f, "higher certificate refused: {error}"),
            | Self::Boundary => f.write_str("higher-field boundary mismatch"),
            | Self::NonProductive(id) => write!(f, "non-productive higher field at {}", id.0),
            | Self::DepthBound => f.write_str("higher-field observation depth bound reached"),
            | Self::ZeroDepth => f.write_str("higher-field observation requires positive depth"),
            | Self::UnknownLayer(id) => write!(f, "unknown higher layer {}", id.0),
            | Self::ExpectedEquivalence => f.write_str("expected equivalence certificate record"),
            | Self::Replay(KernelVerdict::Convertible) => {
                f.write_str("unexpected positive replay refusal")
            },
            | Self::Replay(KernelVerdict::NotConvertible) => {
                f.write_str("higher-field reduction not convertible")
            },
            | Self::Replay(KernelVerdict::Declined(_)) => {
                f.write_str("higher-field reduction declined")
            },
            | Self::NeutralTransport => f.write_str("higher fibre transport remains neutral"),
        }
    }
}

impl core::error::Error for HigherError
{
}

impl From<RelationError> for HigherError
{
    /// Preserve the relation's original refusal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(error: RelationError) -> Self
    {
        Self::Relation(error)
    }
}

impl From<PathError> for HigherError
{
    /// Preserve the universe path's original refusal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(error: PathError) -> Self
    {
        Self::Path(Box::new(error))
    }
}

/// Reuse the identity-mode code fold without adding another former switch.
///
/// # Specification
/// - ensures: returns precisely the existing element-identity interpretation.
/// - fails: `Relation` for a code outside that interpretation.
/// - panics: none.
///
/// # Errors
/// `HigherError::Relation`.
///
/// # Adequacy
/// - hypothesis: L3 — product fibres retain both coordinates at higher depth.
/// - witness: `higher_field::tests::higher_fibres_preserve_boundaries`
fn relation(
    arena: &TermArena,
    code: ValueId,
) -> Result<Relation, HigherError>
{
    let interpretation = interpret(arena, Mode::Identity, Domain::Elements(code))?;
    let relation = interpretation.elements()?;
    Ok(relation)
}

/// Compute the code of a checked cell's identity fibre.
///
/// # Specification
/// - ensures: rechecks the cell and quotes its native relation fibre.
/// - fails: `Relation` on invalid evidence or a neutral fibre.
/// - panics: none.
///
/// # Errors
/// `HigherError::Relation`.
///
/// # Adequacy
/// - hypothesis: L3 — a neutral fibre is retained as a refusal, not collapsed.
/// - witness: `higher_field::tests::higher_fibres_preserve_boundaries`
fn fibre_code(
    arena: &mut TermArena,
    context: &[ValueTypeId],
    cell: Cell,
) -> Result<ValueId, HigherError>
{
    let relation = relation(arena, cell.code)?;
    relation.witness(arena, context, cell.left, cell.right, cell.evidence)?;
    let fibre = relation.fiber(arena, context, cell.left, cell.right)?;
    let fibre = fibre.native(arena)?;
    Ok(arena.value_quote(fibre))
}

impl Codata
{
    /// Observe identity between parallel cells through a stated finite depth.
    ///
    /// # Specification
    /// - requires: arena nodes remain live without address reuse.
    /// - ensures: every exposed head checks by the same identity recursion on
    ///   the previous fibre code. Each tail asks for identity of that head with
    ///   itself; no equality axiom or conversion of certificates is used.
    /// - provides: only a finite prefix; an unobserved tail is not certified.
    /// - fails: `Boundary`, `Relation`, `ZeroDepth`, `DepthBound`,
    ///   `UnknownLayer`, or `NonProductive` for a constructor-free cycle.
    /// - panics: none.
    /// - intension: every visited instruction consumes one replay unit; only a
    ///   checked Guard advances depth and clears the local cycle detector.
    ///
    /// # Errors
    /// As `fails`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — guarded cycles reach an exact requested depth; direct
    ///   and indirect unguarded cycles, late corruption and exact budget
    ///   boundaries distinguish productivity from mere graph cyclicity.
    /// - witness: `higher_field::tests::non_productive_certificate_is_refused`
    /// - witness: `higher_field::tests::higher_fibres_preserve_boundaries`
    #[inline]
    pub fn observe(
        &self,
        arena: &mut TermArena,
        context: &[ValueTypeId],
        left: Cell,
        right: Cell,
        budget: ObservationBudget,
    ) -> Result<Prefix, HigherError>
    {
        if budget.depth.0 == 0 {
            return Err(HigherError::ZeroDepth);
        }
        for (left, right) in [
            (left.code, right.code),
            (left.left, right.left),
            (left.right, right.right),
        ] {
            if equal_values(arena, left, right) != Convertibility::Convertible {
                return Err(HigherError::Boundary);
            }
        }
        right.check(arena, context)?;
        let code = fibre_code(arena, context, left)?;
        let mut goal = (code, left.evidence, right.evidence);
        let mut current = self.root;
        let mut remaining = u64::from(budget.replay);
        let mut depth = 0_u32;
        let mut unguarded = BTreeSet::new();
        let mut head = None;
        loop {
            if !unguarded.insert(current) {
                return Err(HigherError::NonProductive(current));
            }
            remaining = remaining.checked_sub(1).ok_or(HigherError::DepthBound)?;
            let layer = self
                .nodes
                .get(current.0)
                .ok_or(HigherError::UnknownLayer(current))?;
            match *layer {
                | Layer::Redirect(next) => current = next,
                | Layer::Guard { evidence, tail } => {
                    let cell = Cell {
                        code: goal.0,
                        left: goal.1,
                        right: goal.2,
                        evidence,
                    };
                    depth = depth.saturating_add(1);
                    if depth == budget.depth.0 {
                        cell.check(arena, context)?;
                        let head = head.unwrap_or(cell);
                        return Ok(Prefix {
                            head,
                            depth: Depth(depth),
                        });
                    }
                    let code = fibre_code(arena, context, cell)?;
                    head.get_or_insert(cell);
                    goal = (code, evidence, evidence);
                    current = tail;
                    unguarded.clear();
                },
            }
        }
    }
}
