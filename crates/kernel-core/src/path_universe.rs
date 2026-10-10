//! Native certificate-typed identity at closed first-order and session codes.
//!
//! `ValueType::PathUniverse`, the native path introductions and
//! `Computation::Transport` belong to the persisted term vocabulary. Admission
//! checks translators in the ordinary iterative checker and replays both
//! round trips on code-generated constructor patterns. Session introductions
//! instead replay a supplied finite bisimulation. Evidence contributes to
//! content identity, never to certificate conversion. No path inspection, K or
//! path-induction eliminator exists.

use alloc::vec::Vec;
use core::fmt;

use gandr_kernel_conversion_trace::ConversionDecision;
use gandr_kernel_term::ComputationId;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::Value;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueType;
use gandr_kernel_term::ValueTypeId;

use crate::check::check_closed_value;
use crate::error::KernelError;
use crate::replay::EngineClaim;
use crate::replay::KernelVerdict;
use crate::replay::ReplayBudget;
use crate::replay::ReplayNode;
use crate::replay::ReplaySides;
use crate::replay::Unfoldings;

pub(crate) mod coverage;
#[cfg(test)]
pub(crate) mod tests;

/// One untrusted dialogue, interpreted against a kernel-derived boundary.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Dialogue(pub Vec<ConversionDecision<ReplayNode>>);

impl Dialogue
{
    /// Pair returner dialogues, preserving both structural boundaries.
    ///
    /// # Specification
    /// - requires: both dialogues concern returner computations.
    /// - ensures: return and pair decomposition precede the two dialogues.
    /// - provides: paired evidence whose boundaries are checked by replay.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — component traces certify product transport; trailing
    ///   evidence refuses rather than disappearing.
    /// - witness: `path_universe::tests::it_computes_through_a_former`
    #[inline]
    #[must_use]
    pub fn pair(
        mut first: Self,
        mut second: Self,
    ) -> Self
    {
        first.0.reserve(second.0.len().saturating_add(2));
        first.0.splice(.. 0, [
            ConversionDecision::Decompose,
            ConversionDecision::Decompose,
        ]);
        first.0.append(&mut second.0);
        first
    }
}
/// The source or target round-trip obligation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Direction
{
    /// Backward after forward.
    Source,
    /// Forward after backward.
    Target,
}

/// A zero-based symbolic constructor-pattern position.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PatternPosition(pub usize);
/// The decoded endpoints of a native universe-path classifier.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PathType
{
    /// The type denoted by the source code.
    pub source: ValueTypeId,
    /// The type denoted by the target code.
    pub target: ValueTypeId,
}

/// A native transport's two value operands.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Transport
{
    /// A native path value, not an index in an auxiliary rule arena.
    pub path: ValueId,
    /// The value at the source endpoint.
    pub value: ValueId,
}

/// Whether a canonical transport beta rule fires.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Reduction
{
    /// The kernel-derived one-step reduct.
    Reduced(ComputationId),
    /// A neutral path or a product waiting for a canonical pair.
    Stuck,
}
/// A universe-path formation or reduction refusal.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PathError
{
    /// A finite session graph is malformed.
    Session(crate::session::SessionError),
    /// A supplied root does not resolve in the arena.
    Arena,
    /// An endpoint is not a quoted code.
    UnsupportedCode(ValueId),
    /// A code contains a former outside the closed first-order fragment.
    UnsupportedType(ValueTypeId),
    /// An equivalence annotation is not a native path classifier.
    ExpectedPath(ValueTypeId),
    /// Round-trip evidence has the wrong constructor coverage.
    Coverage(Direction),
    /// A kernel-generated round-trip claim did not replay positively.
    RoundTrip
    {
        /// The checked direction.
        direction: Direction,
        /// The constructor-pattern position.
        pattern: PatternPosition,
        /// The actual replay verdict.
        verdict: KernelVerdict,
    },
    /// A finite code or replay allowance was exhausted.
    Budget,
}

impl fmt::Display for PathError
{
    /// Render the specific path refusal.
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
            | Self::Session(ref error) => error.fmt(f),
            | Self::Arena => f.write_str("a universe-path root was unreadable"),
            | Self::UnsupportedCode(_) => f.write_str("a universe-path endpoint was not quoted"),
            | Self::UnsupportedType(_) => {
                f.write_str("a code was outside the native path vocabulary")
            },
            | Self::ExpectedPath(_) => f.write_str("an equivalence annotation was not Path_U"),
            | Self::Coverage(Direction::Source) => {
                f.write_str("incomplete source round-trip coverage")
            },
            | Self::Coverage(Direction::Target) => {
                f.write_str("incomplete target round-trip coverage")
            },
            | Self::RoundTrip {
                direction,
                pattern,
                verdict,
            } => {
                let direction = match direction {
                    | Direction::Source => "source",
                    | Direction::Target => "target",
                };
                let verdict = match verdict {
                    | KernelVerdict::Convertible => "certified equality",
                    | KernelVerdict::NotConvertible => "refuted equality",
                    | KernelVerdict::Declined(_) => "replay declined",
                };
                write!(
                    f,
                    "{direction} round trip at pattern {}: {verdict}",
                    pattern.0
                )
            },
            | Self::Budget => f.write_str("the universe-path allowance was exhausted"),
        }
    }
}

impl core::error::Error for PathError
{
}

/// Remaining steps in one code walk.
#[repr(transparent)]
pub(crate) struct Allowance(u64);

impl Allowance
{
    /// Charge one step without underflow.
    ///
    /// # Specification
    /// - ensures: consumes exactly one available step.
    /// - fails: `Budget` when no step remains.
    /// - panics: none.
    ///
    /// # Errors
    /// `PathError::Budget`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — zero budget refuses; ordinary code walks succeed.
    /// - witness: `path_universe::tests::transport_computes`
    pub(crate) fn charge(&mut self) -> Result<(), PathError>
    {
        self.0 = self.0.checked_sub(1).ok_or(PathError::Budget)?;
        Ok(())
    }
}

/// Inspect a quoted native path code and its finite session graph, if present.
///
/// # Specification
/// - ensures: accepts quoted Unit, Base, Sum, Product and guarded Session
///   shapes. Session payload typing belongs to ordinary native formation; this
///   inspection is not a certificate or admission capability.
/// - provides: the callable code walk for consumers of native universe paths.
/// - fails: unsupported codes, unreadable roots or exhausted budget.
/// - panics: none.
///
/// # Errors
/// `UnsupportedCode`, `UnsupportedType`, `Arena`, or `Budget`.
///
/// # Adequacy
/// - hypothesis: L3 — Bool and products admit; thunk codes refuse.
/// - witness: `path_universe::tests::a_non_equivalence_is_refused`
#[inline]
pub fn code(
    arena: &TermArena,
    code: ValueId,
    budget: ReplayBudget,
) -> Result<ValueTypeId, PathError>
{
    coverage::code(arena, code, &mut Allowance(u64::from(budget)))
}

/// Inspect and decode both endpoints of a native path classifier.
///
/// # Specification
/// - ensures: both endpoint shapes belong to the native path code vocabulary;
///   session graphs are finite and guarded. Ordinary checking still owes
///   session payload formation in an empty term context.
/// - fails: `ExpectedPath` for another classifier, or a code-walk refusal.
/// - panics: none.
///
/// # Errors
/// Any code-walk error or `ExpectedPath`.
///
/// # Adequacy
/// - hypothesis: L3 — malformed endpoints cannot enter through annotations.
/// - witness: `path_universe::tests::a_non_equivalence_is_refused`
#[inline]
pub fn endpoints(
    arena: &TermArena,
    classifier: ValueTypeId,
    budget: ReplayBudget,
) -> Result<PathType, PathError>
{
    let Some(&ValueType::PathUniverse(source, target)) = arena.value_type(classifier)
    else {
        return Err(PathError::ExpectedPath(classifier));
    };
    let mut allowance = Allowance(u64::from(budget));
    let source = coverage::code(arena, source, &mut allowance)?;
    let target = coverage::code(arena, target, &mut allowance)?;
    Ok(PathType { source, target })
}
/// Compute one native transport beta step, without claiming formation.
///
/// # Specification
/// - requires: admission established the path and operand types.
/// - ensures: reflexivity returns the exact operand; equivalence applies its
///   forward map; product transport sequences both components without capture.
/// - provides: a reduct derived entirely from the native syntax.
/// - fails: `Arena` on an unreadable path or product operand.
/// - panics: none.
///
/// # Errors
/// `PathError::Arena`.
///
/// # Adequacy
/// - hypothesis: L3 — the native transport witnesses distinguish map direction,
///   component order and reflexivity's one-step result.
/// - witness: `path_universe::tests::transport_computes`
/// - witness: `path_universe::tests::it_computes_through_a_former`
/// - witness: `path_universe::tests::refl_collapses`
#[inline]
pub fn beta(
    arena: &mut TermArena,
    term: Transport,
) -> Result<Reduction, PathError>
{
    let reduct = match arena.value(term.path) {
        | Some(&Value::PathRefl(_)) => arena.computation_return(term.value),
        | Some(&Value::PathEquiv { forward, .. }) => {
            let force = arena.computation_force(forward);
            arena.computation_application(force, term.value)
        },
        | Some(&Value::PathProduct(first, second)) => {
            let Some(&Value::Pair(left, right)) = arena.value(term.value)
            else {
                return if arena.value(term.value).is_some() {
                    Ok(Reduction::Stuck)
                }
                else {
                    Err(PathError::Arena)
                };
            };
            let first = arena.computation_transport(first, left);
            let second = arena.computation_transport(second, right);
            let second = crate::rewrite::shift_computation(
                arena,
                &mut crate::encoding::ContentTable::new(),
                &mut gandr_kernel_check_memo::NullMemo,
                second,
                crate::rewrite::BinderDepth::default(),
                crate::rewrite::BinderDepth::from(1_u32),
            );
            let left = arena.value_variable(gandr_kernel_term::DeBruijnIndex::from(1_u32));
            let right = arena.value_variable(gandr_kernel_term::DeBruijnIndex::from(0_u32));
            let pair = arena.value_pair(left, right);
            let result = arena.computation_return(pair);
            let result = arena.computation_bind(second, result);
            arena.computation_bind(first, result)
        },
        | Some(_) => return Ok(Reduction::Stuck),
        | None => return Err(PathError::Arena),
    };
    Ok(Reduction::Reduced(reduct))
}
/// Replay a native transport after checking its path and both computations.
///
/// # Specification
/// - requires: all roots belong to `arena` and are closed.
/// - ensures: checks formation through the ordinary checker, replays native
///   transport against `expected`, and restores the entry watermark on exit.
/// - provides: the callable closed replay boundary; admission uses `add_decl`.
/// - fails: typing, code or evidence failures as `KernelError`; invalid replay
///   dialogues return a declined verdict.
/// - panics: none.
///
/// # Errors
/// A native checking error or path-formation error.
///
/// # Adequacy
/// - hypothesis: L3 — negation and products compute; the wrong answer and
///   forged positive claims remain distinguishable.
/// - witness: `path_universe::tests::transport_computes`
/// - witness: `path_universe::tests::a_wrong_answer_is_caught`
#[inline]
pub fn replay_transport(
    arena: &mut TermArena,
    term: Transport,
    expected: ComputationId,
    claim: EngineClaim,
    dialogue: &Dialogue,
    budget: ReplayBudget,
) -> Result<KernelVerdict, KernelError>
{
    let watermark = arena.watermark();
    let result = replay_checked(arena, term, expected, claim, dialogue, budget);
    arena.truncate_to(watermark);
    result
}

/// Run the fallible interior of the restoring replay boundary.
///
/// # Specification
/// - requires: the caller restores its arena watermark on every exit.
/// - ensures: as `replay_transport`, retaining temporary nodes for the caller.
/// - fails: native checking errors or exhausted budget.
/// - panics: none.
///
/// # Errors
/// As `replay_transport`.
///
/// # Adequacy
/// - hypothesis: L3 — the public boundary exercises these checks and replay.
/// - witness: `path_universe::tests::a_wrong_answer_is_caught`
fn replay_checked(
    arena: &mut TermArena,
    term: Transport,
    expected: ComputationId,
    claim: EngineClaim,
    dialogue: &Dialogue,
    budget: ReplayBudget,
) -> Result<KernelVerdict, KernelError>
{
    Allowance(u64::from(budget))
        .charge()
        .map_err(KernelError::Path)?;
    let classifier = crate::check::synth_closed_value(arena, term.path)?;
    let endpoints = endpoints(arena, classifier, budget).map_err(KernelError::Path)?;
    let returner = arena.comp_type_returner(endpoints.target);
    let thunk_type = arena.value_type_thunk(returner);
    let transport = arena.computation_transport(term.path, term.value);
    let body = arena.value_thunk(transport);
    check_closed_value(arena, body, thunk_type)?;
    let expected_thunk = arena.value_thunk(expected);
    check_closed_value(arena, expected_thunk, thunk_type)?;
    Ok(crate::replay::replay(
        arena,
        &Unfoldings::new(Vec::new()),
        ReplaySides::Computations(transport, expected),
        claim,
        dialogue.0.iter().copied(),
        budget,
    ))
}

/// Supply ignored node hints for an arena-independent closed dialogue.
///
/// # Specification
/// - ensures: preserves each decision, side and premise position exactly.
/// - provides: no constant identity or producer-selected boundary.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — closed positive and negative round trips replay with unit
///   anchors; constant operations have no authoritative name to unfold.
/// - witness: `path_universe::tests::a_non_equivalence_is_refused`
pub(crate) fn anchor(decision: ConversionDecision<()>) -> ConversionDecision<ReplayNode>
{
    let node = ReplayNode::Other;
    match decision {
        | ConversionDecision::ReduceLeft { .. } => ConversionDecision::ReduceLeft { redex: node },
        | ConversionDecision::ReduceRight { .. } => ConversionDecision::ReduceRight { redex: node },
        | ConversionDecision::ConstShortcut { .. } => {
            ConversionDecision::ConstShortcut { constant: node }
        },
        | ConversionDecision::Unfold { .. } => ConversionDecision::Unfold { constant: node },
        | ConversionDecision::Postpone { .. } => ConversionDecision::Postpone { constant: node },
        | ConversionDecision::Freeze { side, .. } => ConversionDecision::Freeze {
            constant: node,
            side,
        },
        | ConversionDecision::EtaExpand { side, .. } => ConversionDecision::EtaExpand {
            variable: node,
            side,
        },
        | ConversionDecision::Force { .. } => ConversionDecision::Force { thunk: node },
        | ConversionDecision::ComparedShared { .. } => ConversionDecision::ComparedShared {
            left: node,
            right: node,
        },
        | ConversionDecision::Decompose => ConversionDecision::Decompose,
        | ConversionDecision::NegativeSubgoal { position } => {
            ConversionDecision::NegativeSubgoal { position }
        },
    }
}
