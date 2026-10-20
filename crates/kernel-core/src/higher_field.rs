//! Guarded observations of identity between identities.
//!
//! A layer checks `Rel(quote(Rel(code, a, b)), p, q)` using the existing code
//! fold. Its tail observes the diagonal of that checked layer. Raw programs
//! are finite graphs: a constructor guards a recursive edge, while a cycle of
//! redirects is non-productive. Success states only the requested finite depth.
//! These arena-relative objects neither enter conversion nor admit
//! declarations.
//!
//! # The field
//!
//! The module computes `Rel₂(p, q)` by quoting the native fibre of two checked
//! parallel identities and applying the same identity-mode code fold to their
//! evidence. No relation clause is duplicated. Neutral fibres retain the named
//! refusal; the field adds no equality decision on unknown indices.
//!
//! A `Codata` program is a flat graph of `Guard` and `Redirect` instructions.
//! Each guard checks an inhabitant of the current higher fibre; its tail
//! requests identity of that inhabitant with itself. The same API also
//! observes any supplied pair of parallel native cells. A guarded cycle
//! represents arbitrarily many requested diagonal layers without
//! materializing an infinite structure. A cycle of redirects returns
//! `NonProductive`. Success is a `Prefix` at exactly the requested positive
//! `Depth`, not a verdict about an unobserved tail.
//!
//! `ObservationBudget` gives each observation an instruction allowance from
//! `ReplayBudget`. Every redirect and guard consumes one unit; reaching the
//! allowance before the requested depth returns `DepthBound`. Zero depth
//! returns `ZeroDepth`. CBPV dialogues and path formation retain their
//! independent replay ceilings. Native relation checking remains a terminating
//! structural walk, not part of the instruction count. These bounds state
//! replay scope, not a global cost theorem.
//!
//! # Symmetry
//!
//! `symmetry` checks that the source diagonal and inverse fibres have the
//! same native type. It reindexes diagonal evidence into the path fibre,
//! observes its higher identity with the supplied path evidence, and
//! transports the diagonal in that fibre to produce the inverse. It then
//! checks all four square faces and observes identity between the two
//! boundary composites. Both Bool injections compute with distinct neutral
//! Unit payloads and canonical evidence. A neutral proof-index action retains
//! the transport boundary as `NeutralTransport`; this is not general
//! dependent elimination.
//!
//! # Unfolding an equivalence
//!
//! `unfold` consumes two native `Value::PathEquiv` introductions, checks each
//! through the ordinary closed-value checker and exposes the identity record:
//!
//! | Field | Observation |
//! | ----- | ----------- |
//! | Forward | Replay both translators at the input; check identity of their returned values and its higher diagonal. |
//! | Backward | The same observation in the reverse direction. |
//! | Source coherence | Replay both backward-after-forward composites to the input; observe identity between their reflected diagonal witnesses. |
//! | Target coherence | The corresponding forward-after-backward coherence. |
//!
//! The negation and case-inlined triple-negation certificates satisfy all four
//! fields at both Bool constructors, while native structural conversion
//! reports `Distinct`. This is **replay-equivalence as identity, never in
//! conversion**. The record is an identity type's observation interface: each
//! point consumes supplied evidence; observing Base samples would not prove a
//! universal field. Reflexivity and product introductions retain their native
//! path operations; record unfolding requires `PathEquiv`.
//!
//! `Identity::native_evidence` projects native fibre inhabitants only.
//! Pointwise function evidence returns `HigherEvaluationRequired`,
//! preserving the distinction between a higher-evaluation program and a
//! native value; suspended diagonals retain `NeutralFiber`. Function consumers
//! borrow identities and replay their raw evidence.
//!
//! # Decision
//!
//! **Choice.** A first-order cyclic program makes guards and back edges
//! inspectable and bounds each replay. **Alternatives.** Eager towers cannot
//! represent infinite higher data; closures hide productivity obligations and
//! allocate opaque continuations. The graph stores no checking verdict and
//! adds no dependency. Its persisted form is the kernel's guarded higher field,
//! which [`crate::element_identity`] checks to the program's depth and reads
//! back as this program; `J` is transport in the singleton family there.
//! **Reversal.** Each observed native fibre must be representable at the
//! admitted stratum; a general dependent eliminator is not provided.
//!
//! # Witnesses
//!
//! The witnesses for this module and its native-evidence projection target
//! removed guards, uncharged redirects, early depth success, forged fibre
//! evidence, dropped product coordinates, wrong square boundaries,
//! substituted translator outputs and omitted round-trip coherence, without
//! claiming a mutation campaign or a metatheorem about infinite coherence.

use alloc::boxed::Box;
use alloc::collections::BTreeSet;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
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
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |identity| matches!(identity.native_evidence(), Ok(proof) if proof == self.evidence)))]
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
            Self::Relation(ref error) => write!(f, "higher relation refused: {error}"),
            Self::Path(ref error) => write!(f, "higher certificate refused: {error}"),
            Self::Boundary => f.write_str("higher-field boundary mismatch"),
            Self::NonProductive(id) => write!(f, "non-productive higher field at {}", id.0),
            Self::DepthBound => f.write_str("higher-field observation depth bound reached"),
            Self::ZeroDepth => f.write_str("higher-field observation requires positive depth"),
            Self::UnknownLayer(id) => write!(f, "unknown higher layer {}", id.0),
            Self::ExpectedEquivalence => f.write_str("expected equivalence certificate record"),
            Self::Replay(KernelVerdict::Convertible) => {
                f.write_str("unexpected positive replay refusal")
            },
            Self::Replay(KernelVerdict::NotConvertible) => {
                f.write_str("higher-field reduction not convertible")
            },
            Self::Replay(KernelVerdict::Declined(_)) => {
                f.write_str("higher-field reduction declined")
            },
            Self::NeutralTransport => f.write_str("higher fibre transport remains neutral"),
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
#[spec(ensures: |ret| ret.as_ref().map_or(true, |relation| relation.mode() == Mode::Identity))]
fn relation(
    arena: &TermArena,
    code: ValueId,
) -> Result<Relation, HigherError>
{
    let interpretation = interpret(
        arena,
        crate::identity_recursion::Interfaces::NONE,
        Mode::Identity,
        Domain::Elements(code),
    )?;
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
#[spec(ensures: |ret| match ret {
    Ok(code) => matches!(arena.value(code), Some(&gandr_kernel_term::Value::Quote(_))),
    Err(HigherError::Relation(_)) => true,
    Err(_) => false,
})]
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
    #[spec(ensures: |ret| match ret {
        Ok(prefix) => prefix.depth == budget.depth && prefix.depth.0 > 0 && u64::from(prefix.depth.0) <= u64::from(budget.replay),
        Err(HigherError::ZeroDepth) => budget.depth.0 == 0,
        Err(HigherError::UnknownLayer(id)) => self.nodes.get(id.0).is_none(),
        Err(HigherError::NonProductive(id)) => matches!(self.nodes.get(id.0), Some(&Layer::Redirect(_))),
        Err(_) => budget.depth.0 > 0,
    })]
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
        let start = Goal {
            code,
            left: left.evidence,
            right: right.evidence,
        };
        self.walk(arena, start, budget, |arena, cell, _fibre| {
            cell.check(arena, context).map(|_identity| ())
        })
    }

    /// Walk the guarded program from `start`, handing every exposed cell and
    /// its computed fibre to `visit` before the walk relies on it.
    ///
    /// # Specification
    /// - requires: `start`'s endpoints inhabit the fibre its code denotes, and
    ///   `visit` refuses every cell whose evidence does not inhabit the fibre
    ///   it is handed, or records that obligation for a caller that discharges
    ///   it before trusting the walk.
    /// - ensures: each guard's cell is visited with the native fibre of its
    ///   code at its two endpoints, computed without a nested check; the tail
    ///   observes identity of that guard's evidence with itself. Exactly the
    ///   requested depth is reached, or the walk refuses.
    /// - provides: the one control loop behind [`Self::observe`] and the
    ///   kernel's persisted higher field, which records its cells as checking
    ///   goals instead of re-entering the checker.
    /// - fails: `ZeroDepth`, `DepthBound`, `UnknownLayer`, `NonProductive`, a
    ///   fibre refusal, or the visitor's refusal.
    /// - panics: none.
    /// - intension: every visited instruction consumes one replay unit; only a
    ///   Guard advances depth and clears the local cycle detector.
    ///
    /// # Errors
    /// As `fails`.
    ///
    /// # Termination
    /// - reason: the `loop` below over an explicit position, not recursion.
    /// - measure: the replay allowance, which every visited instruction
    ///   consumes.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::observe`]; the persisted higher field's
    ///   productive and non-productive programs reach the same verdicts.
    /// - witness: `higher_field::tests::non_productive_certificate_is_refused`
    /// - witness: `element_identity::tests::a_non_productive_higher_field_is_refused_by_name`
    #[spec(ensures: |ret| match ret {
        Ok(prefix) => prefix.depth == budget.depth && prefix.depth.0 > 0 && u64::from(prefix.depth.0) <= u64::from(budget.replay),
        Err(HigherError::ZeroDepth) => budget.depth.0 == 0,
        Err(HigherError::UnknownLayer(id)) => self.nodes.get(id.0).is_none(),
        Err(HigherError::NonProductive(id)) => matches!(self.nodes.get(id.0), Some(&Layer::Redirect(_))),
        Err(_) => budget.depth.0 > 0,
    })]
    pub(crate) fn walk<V>(
        &self,
        arena: &mut TermArena,
        start: Goal,
        budget: ObservationBudget,
        mut visit: V,
    ) -> Result<Prefix, HigherError>
    where
        V: FnMut(&mut TermArena, Cell, ValueTypeId) -> Result<(), HigherError>,
    {
        if budget.depth.0 == 0 {
            return Err(HigherError::ZeroDepth);
        }
        let mut goal = start;
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
                Layer::Redirect(next) => current = next,
                Layer::Guard { evidence, tail } => {
                    let cell = Cell {
                        code: goal.code,
                        left: goal.left,
                        right: goal.right,
                        evidence,
                    };
                    let fibre = relation(arena, cell.code)?
                        .evaluate(arena, cell.left, cell.right)?
                        .native(arena)?;
                    visit(arena, cell, fibre)?;
                    depth = depth.saturating_add(1);
                    let head = *head.get_or_insert(cell);
                    if depth == budget.depth.0 {
                        return Ok(Prefix {
                            head,
                            depth: Depth(depth),
                        });
                    }
                    goal = Goal {
                        code: arena.value_quote(fibre),
                        left: evidence,
                        right: evidence,
                    };
                    current = tail;
                    unguarded.clear();
                },
            }
        }
    }
}

/// The goal a higher observation stands at: identity between two inhabitants
/// of the fibre a code denotes.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct Goal
{
    /// The quoted fibre both endpoints inhabit.
    pub code: ValueId,
    /// Source endpoint.
    pub left: ValueId,
    /// Target endpoint.
    pub right: ValueId,
}
