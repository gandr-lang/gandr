//! Certificate-typed identity at the closed first-order code universe.
//!
//! `Path_U a b` is a value type with three introductions: a replay-certified
//! equivalence, reflexivity, and a product of paths. Its sole eliminator is
//! transport. The rule language is arena-addressed and experimental: it does
//! not extend the persisted term vocabulary or the surface parser.
//!
//! Round trips are checked on every constructor pattern of Unit, Sum and
//! Product, with distinct rigid variables at Base leaves. This is symbolic
//! coverage, not sampling base literals. Translators are closed, kernel-typed
//! CBPV terms. Every pattern in each direction owes its own conversion trace.
//! The kernel builds each claim itself and replays it; no supplied verdict,
//! claimed sample set, Rust translator, or equivalence cache is authoritative.
//!
//! Transport's three beta rules expose ordinary CBPV computations. Product
//! transport pairs component dialogues in left-to-right order. There is no
//! transitive certificate graft and no path-induction or K primitive.

use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::string::String;
use alloc::vec::Vec;
use core::fmt;

use gandr_kernel_conversion_trace::ConversionDecision;
use gandr_kernel_strata::Level;
use gandr_kernel_term::ComputationId;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::Value;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueTypeId;

use crate::check::check_closed_value;
use crate::conv::Convertibility;
use crate::conv::equal_values;
use crate::error::KernelError;
use crate::replay::EngineClaim;
use crate::replay::KernelVerdict;
use crate::replay::ReplayBudget;
use crate::replay::ReplayNode;
use crate::replay::ReplaySides;
use crate::replay::Unfoldings;

mod coverage;
#[cfg(test)]
mod tests;

/// One replay dialogue, with no claimed verdict or caller-chosen boundary.
///
/// # Specification
/// - provides: untrusted decisions, interpreted only against a kernel-built
///   claim.
///
/// # Adequacy
/// - hypothesis: L3 — a wrong-answer trace cannot certify a positive claim.
/// - witness: `path_universe::tests::a_wrong_answer_is_caught`
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Dialogue(pub Vec<ConversionDecision<ReplayNode>>);

impl Dialogue
{
    /// Pair two returner dialogues without their leading shared comparison
    /// accidentally closing the enclosing pair.
    ///
    /// # Specification
    /// - requires: both dialogues certify convertible returner computations.
    /// - ensures: structural return and pair boundaries precede the left and
    ///   right component traces, in that order; replay checks every boundary.
    /// - provides: trace pairing rather than a batch of independent verdicts.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — component engine traces replay as one product claim;
    ///   a trailing structural boundary is refused rather than ignored.
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

/// The two universally quantified round-trip dialogues, decomposed by codes.
///
/// # Specification
/// - provides: source then target evidence over kernel-generated constructor
///   patterns.
///
/// # Adequacy
/// - hypothesis: L3 — missing coverage and sampled Base evidence are refused.
/// - witness: `path_universe::tests::a_non_equivalence_is_refused`
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct RoundTrips
{
    /// `g (f x) = return x`, in source-pattern order.
    pub source: Vec<Dialogue>,
    /// `f (g y) = return y`, in target-pattern order.
    pub target: Vec<Dialogue>,
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

/// A path node's index in a flat, constructor-ordered arena.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct PathId(usize);

/// A universe-path introduction; all term fields are untrusted arena roots.
///
/// # Specification
/// - provides: the three raw introductions; only [`form`] establishes their
///   typing.
///
/// # Adequacy
/// - hypothesis: L3 — bad translators cannot establish an equivalence.
/// - witness: `path_universe::tests::a_non_equivalence_is_refused`
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Path
{
    /// The canonical identity at a closed first-order code.
    Refl(ValueId),
    /// A typed pair of translators with both round-trip dialogues.
    Equiv
    {
        /// The source code.
        source: ValueId,
        /// The target code.
        target: ValueId,
        /// A thunk of `El source -> F (El target)`.
        forward: ValueId,
        /// A thunk of `El target -> F (El source)`.
        backward: ValueId,
        /// Evidence, checked afresh at every formation.
        round_trips: RoundTrips,
    },
    /// Componentwise identity between product codes.
    Product(PathId, PathId),
}

/// The value-type former `Path_U source target : Type[+, 0]`.
///
/// The closed first-order codes in this experiment all live at level zero.
/// This is a classifier, never an admission receipt or a persisted memo hit.
///
/// # Specification
/// - provides: the two first-order endpoint types; its fields carry no
///   authority.
///
/// # Adequacy
/// - hypothesis: L3 — both negation certificates form at the same Bool
///   endpoints.
/// - witness: `path_universe::tests::certificate_identity_stays_out_of_conversion`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PathType
{
    /// The type denoted by the source code.
    pub source: ValueTypeId,
    /// The type denoted by the target code.
    pub target: ValueTypeId,
}

impl PathType
{
    /// The classifier's level in the closed first-order fragment.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn level(self) -> Level
    {
        Level::zero()
    }
}

/// The raw rule syntax; no entry records that a path was previously checked.
///
/// # Specification
/// - provides: append-only acyclic raw paths; no stored formation verdict.
///
/// # Adequacy
/// - hypothesis: L3 — product formation checks its reachable introductions.
/// - witness: `path_universe::tests::it_computes_through_a_former`
#[repr(transparent)]
#[derive(Clone, Debug, Default)]
pub struct Paths(Vec<Path>);

impl Paths
{
    /// An empty rule arena.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new() -> Self
    {
        Self(Vec::new())
    }

    /// Append a constructor, checking only that path children are earlier.
    ///
    /// # Specification
    /// - requires: nothing; term roots remain untrusted until formation.
    /// - ensures: the returned id resolves to `path`; product edges point back.
    /// - provides: acyclic path syntax, without certifying its inhabitants.
    /// - fails: `PathError::UnknownPath` for an unresolved product child.
    /// - panics: none.
    ///
    /// # Errors
    /// `PathError::UnknownPath`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — product transport witnesses ordered child resolution;
    ///   malformed references are checked before insertion.
    /// - witness: `path_universe::tests::it_computes_through_a_former`
    #[inline]
    pub fn push(
        &mut self,
        path: Path,
    ) -> Result<PathId, PathError>
    {
        if let &Path::Product(first, second) = &path {
            self.get(first)?;
            self.get(second)?;
        }
        let id = PathId(self.0.len());
        self.0.push(path);
        Ok(id)
    }

    /// Resolve one raw path node.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the referenced node, or a named unresolved reference.
    /// - provides: checked access to the syntax arena.
    /// - fails: `PathError::UnknownPath` when the id is out of range.
    /// - panics: none.
    ///
    /// # Errors
    /// `PathError::UnknownPath`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the product witness separates its component ids.
    /// - witness: `path_universe::tests::it_computes_through_a_former`
    #[inline]
    fn get(
        &self,
        id: PathId,
    ) -> Result<&Path, PathError>
    {
        self.0.get(id.0).ok_or(PathError::UnknownPath(id))
    }
}

/// A transport elimination awaiting kernel reduction.
///
/// # Specification
/// - provides: a raw elimination; [`elaborate`] checks its source and
///   certificate.
///
/// # Adequacy
/// - hypothesis: L3 — transport resolves, while K has no elimination rule.
/// - witness: `path_universe::tests::no_k`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Transport
{
    /// The certificate whose forward action is used.
    pub path: PathId,
    /// The value transported from its source type.
    pub value: ValueId,
}

/// The result of exactly one universe-path beta step.
///
/// # Specification
/// - provides: one canonical beta conclusion, not a trusted conversion verdict.
///
/// # Adequacy
/// - hypothesis: L3 — reflexivity returns the original value in exactly one
///   step.
/// - witness: `path_universe::tests::refl_collapses`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Reduct
{
    /// `transport (refl a) v` becomes `return v`.
    Return(ValueId),
    /// `transport (equiv f g) v` becomes `force f v`.
    Apply(ValueId, ValueId),
    /// A product transport becomes two component transports.
    Pair(Transport, Transport),
}

/// A name at the experiment's intrinsic-elaboration boundary.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EliminatorName(pub String);

impl From<&str> for EliminatorName
{
    /// Preserve an intrinsic spelling for resolution.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(name: &str) -> Self
    {
        Self(String::from(name))
    }
}

/// A formation, elaboration, or replay failure, distinct from certified
/// falsity.
#[derive(Debug)]
pub enum PathError
{
    /// A path reference does not resolve.
    UnknownPath(PathId),
    /// A term reference does not resolve.
    Arena,
    /// An endpoint is not a quoted closed first-order value type.
    UnsupportedCode(ValueId),
    /// A quoted type has a former outside Base, Unit, Product and Sum.
    UnsupportedType(ValueTypeId),
    /// The ordinary kernel rejected a translator or transported value.
    Typing(Box<KernelError>),
    /// A round-trip direction has missing or extra component dialogues.
    Coverage(Direction),
    /// The kernel did not certify a required round trip.
    RoundTrip
    {
        /// Which composite failed.
        direction: Direction,
        /// The constructor pattern at that boundary.
        pattern: PatternPosition,
        /// The actual replay verdict, including refusal detail.
        verdict: KernelVerdict,
    },
    /// A shape walk, product expansion, or symbolic coverage exceeded its cap.
    Budget,
    /// Product transport is stuck on a neutral rather than a canonical pair.
    ExpectedPair(ValueId),
    /// The intrinsic table contains no such eliminator.
    UnknownEliminator(EliminatorName),
}

impl fmt::Display for PathError
{
    /// Display the exact failure variant and its boundary.
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
            | Self::UnknownPath(id) => write!(f, "unknown universe path {}", id.0),
            | Self::Arena => f.write_str("unresolved term arena reference"),
            | Self::UnsupportedCode(_) => {
                f.write_str("endpoint is not a quoted closed first-order code")
            },
            | Self::UnsupportedType(_) => {
                f.write_str("endpoint contains a type former outside the first-order fragment")
            },
            | Self::Typing(ref error) => write!(f, "universe-path typing failed: {error}"),
            | Self::Coverage(direction) => match direction {
                | Direction::Source => f.write_str("source round-trip dialogue coverage mismatch"),
                | Direction::Target => f.write_str("target round-trip dialogue coverage mismatch"),
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
                let outcome = match verdict {
                    | KernelVerdict::Convertible => "convertible",
                    | KernelVerdict::NotConvertible => "not convertible",
                    | KernelVerdict::Declined(_) => "declined",
                };
                write!(
                    f,
                    "{direction} round trip at pattern {}: {outcome}",
                    pattern.0
                )
            },
            | Self::Budget => f.write_str("universe-path construction budget exhausted"),
            | Self::ExpectedPair(_) => f.write_str("product transport requires a canonical pair"),
            | Self::UnknownEliminator(ref name) => {
                write!(f, "unknown universe-path eliminator {}", name.0)
            },
        }
    }
}

impl core::error::Error for PathError
{
}

/// A decreasing allowance shared by a path-syntax or coverage walk.
#[repr(transparent)]
struct Allowance(u64);

impl Allowance
{
    /// Charge one semantic construction or expansion.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one unit is removed on success; zero refuses unchanged.
    /// - provides: a finite bound independent of input depth.
    /// - fails: `PathError::Budget` at zero.
    /// - panics: none.
    ///
    /// # Errors
    /// `PathError::Budget`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — zero allowance refuses the transport claim.
    /// - witness: `path_universe::tests::transport_computes`
    fn charge(&mut self) -> Result<(), PathError>
    {
        self.0 = self.0.checked_sub(1).ok_or(PathError::Budget)?;
        Ok(())
    }
}

/// Check a path's formation, translators and round trips, retaining no memo.
///
/// # Specification
/// - requires: term and code roots refer to `arena`; path ids refer to `paths`.
/// - ensures: returns `Path_U a b` only after every reachable equivalence has
///   typed translators and replay-certified round trips on all code patterns.
///   Intermediates remain in `arena`; callers may use its watermark to discard.
/// - provides: an iterative formation judgement, including product closure.
/// - fails: `PathError` for unsupported codes, typing, evidence or resource
///   bounds.
/// - panics: none.
/// - intension: each dialogue receives `budget`; the syntax and each coverage
///   walk independently receive that same finite ceiling.
///
/// # Errors
/// Any `PathError` except `ExpectedPair` and `UnknownEliminator`.
///
/// # Adequacy
/// - hypothesis: L3 — Bool involution admits, a constant map refuses, and a
///   product requires both child equivalences rather than trusting their ids.
/// - witness: `path_universe::tests::transport_computes`
/// - witness: `path_universe::tests::a_non_equivalence_is_refused`
/// - witness: `path_universe::tests::it_computes_through_a_former`
#[inline]
pub fn form(
    arena: &mut TermArena,
    paths: &Paths,
    root: PathId,
    budget: ReplayBudget,
) -> Result<PathType, PathError>
{
    let mut allowance = Allowance(u64::from(budget));
    let mut pending = Vec::from([(root, false)]);
    let mut formed = BTreeMap::<PathId, PathType>::new();
    while let Some((id, expanded)) = pending.pop() {
        allowance.charge()?;
        if formed.contains_key(&id) {
            continue;
        }
        let path = paths.get(id)?;
        let classifier = match path {
            | &Path::Refl(code) => {
                let source = coverage::code(arena, code, &mut allowance)?;
                PathType {
                    source,
                    target: source,
                }
            },
            | &Path::Equiv {
                source,
                target,
                forward,
                backward,
                ref round_trips,
            } => {
                let source = coverage::code(arena, source, &mut allowance)?;
                let target = coverage::code(arena, target, &mut allowance)?;
                coverage::translator(arena, forward, source, target)?;
                coverage::translator(arena, backward, target, source)?;
                coverage::round_trip(
                    arena,
                    source,
                    forward,
                    backward,
                    &round_trips.source,
                    Direction::Source,
                    budget,
                )?;
                coverage::round_trip(
                    arena,
                    target,
                    backward,
                    forward,
                    &round_trips.target,
                    Direction::Target,
                    budget,
                )?;
                PathType { source, target }
            },
            | &Path::Product(first, second) => {
                if !expanded {
                    pending.push((id, true));
                    pending.push((second, false));
                    pending.push((first, false));
                    continue;
                }
                let first = formed.get(&first).ok_or(PathError::UnknownPath(first))?;
                let second = formed.get(&second).ok_or(PathError::UnknownPath(second))?;
                PathType {
                    source: arena.value_type_product(first.source, second.source),
                    target: arena.value_type_product(first.target, second.target),
                }
            },
        };
        formed.insert(id, classifier);
    }
    formed.remove(&root).ok_or(PathError::UnknownPath(root))
}

/// Resolve and typecheck the sole eliminator of a universe path.
///
/// # Specification
/// - requires: roots belong to the supplied arenas.
/// - ensures: `transport` resolves only after path formation and source-value
///   checking; every other spelling refuses without introducing a rule.
/// - provides: intrinsic elaboration, with no certificate inspection or K.
/// - fails: `UnknownEliminator`, or a formation or typing failure.
/// - panics: none.
///
/// # Errors
/// `PathError::UnknownEliminator`, `PathError::Typing`, or a `form` error.
///
/// # Adequacy
/// - hypothesis: L3 — transport elaborates and K does not resolve.
/// - witness: `path_universe::tests::no_k`
#[inline]
pub fn elaborate(
    arena: &mut TermArena,
    paths: &Paths,
    name: EliminatorName,
    term: Transport,
    budget: ReplayBudget,
) -> Result<Transport, PathError>
{
    if name.0 != "transport" {
        return Err(PathError::UnknownEliminator(name));
    }
    let classifier = form(arena, paths, term.path, budget)?;
    check_closed_value(arena, term.value, classifier.source)
        .map_err(|error| PathError::Typing(Box::new(error)))?;
    Ok(term)
}

/// Fire exactly one canonical transport rule without checking its premises.
///
/// # Specification
/// - requires: the caller has formed the path and checked the source value.
/// - ensures: reflexivity returns the same value; equivalence applies its
///   forward translator; product produces left and right component transports.
/// - provides: a one-step operational judgement, never a certified verdict.
/// - fails: `UnknownPath`, `Arena`, or `ExpectedPair` on a noncanonical
///   product.
/// - panics: none.
/// - intension: exactly one beta rule is returned; no translator is evaluated.
///
/// # Errors
/// As `fails`.
///
/// # Adequacy
/// - hypothesis: L3 — the three canonical constructors distinguish the rules;
///   reflexivity's reduct is exactly the original value in one step.
/// - witness: `path_universe::tests::refl_collapses`
/// - witness: `path_universe::tests::transport_computes`
/// - witness: `path_universe::tests::it_computes_through_a_former`
#[inline]
pub fn beta(
    arena: &TermArena,
    paths: &Paths,
    term: Transport,
) -> Result<Reduct, PathError>
{
    let path = paths.get(term.path)?;
    match path {
        | &Path::Refl(_) => Ok(Reduct::Return(term.value)),
        | &Path::Equiv { forward, .. } => Ok(Reduct::Apply(forward, term.value)),
        | &Path::Product(first, second) => match arena.value(term.value) {
            | Some(&Value::Pair(left, right)) => Ok(Reduct::Pair(
                Transport {
                    path: first,
                    value: left,
                },
                Transport {
                    path: second,
                    value: right,
                },
            )),
            | Some(_) => Err(PathError::ExpectedPair(term.value)),
            | None => Err(PathError::Arena),
        },
    }
}

/// Compare path data structurally, without quotienting by replay-equivalence.
///
/// # Specification
/// - requires: both paths are formed over `arena`.
/// - ensures: equality precisely for the same introductions with structurally
///   equal codes and translators, recursively at products; evidence is erased.
/// - provides: intensional certificate conversion, never proof irrelevance.
/// - fails: `UnknownPath` or `Budget`.
/// - panics: none.
///
/// # Errors
/// `PathError::UnknownPath`, `PathError::Budget`.
///
/// # Adequacy
/// - hypothesis: L3 — changing an inverse from negation to triple negation
///   preserves round trips but does not produce conversion of certificates.
/// - witness: `path_universe::tests::certificate_identity_stays_out_of_conversion`
#[inline]
pub fn convert(
    arena: &TermArena,
    paths: &Paths,
    left: PathId,
    right: PathId,
    budget: ReplayBudget,
) -> Result<KernelVerdict, PathError>
{
    let mut pending = Vec::from([(left, right)]);
    let mut allowance = Allowance(u64::from(budget));
    while let Some((left, right)) = pending.pop() {
        allowance.charge()?;
        let left = paths.get(left)?;
        let right = paths.get(right)?;
        match (left, right) {
            | (&Path::Refl(first), &Path::Refl(second)) => {
                if equal_values(arena, first, second) == Convertibility::Distinct {
                    return Ok(KernelVerdict::NotConvertible);
                }
            },
            | (
                &Path::Equiv {
                    source: left_source,
                    target: left_target,
                    forward: left_forward,
                    backward: left_backward,
                    ..
                },
                &Path::Equiv {
                    source: right_source,
                    target: right_target,
                    forward: right_forward,
                    backward: right_backward,
                    ..
                },
            ) => {
                for (one, other) in [
                    (left_source, right_source),
                    (left_target, right_target),
                    (left_forward, right_forward),
                    (left_backward, right_backward),
                ] {
                    if equal_values(arena, one, other) == Convertibility::Distinct {
                        return Ok(KernelVerdict::NotConvertible);
                    }
                }
            },
            | (
                &Path::Product(left_first, left_second),
                &Path::Product(right_first, right_second),
            ) => {
                pending.push((left_second, right_second));
                pending.push((left_first, right_first));
            },
            | _ => return Ok(KernelVerdict::NotConvertible),
        }
    }
    Ok(KernelVerdict::Convertible)
}

/// Replay a transport claim, deriving its path formation before any reduction.
///
/// # Specification
/// - requires: term roots belong to `arena`, path roots to `paths`.
/// - ensures: the result is the ordinary kernel replay verdict on the transport
///   reduct and `expected`; both computations check at `F (El b)`. All
///   generated terms and checker intermediates are discarded on every exit.
/// - provides: the certificate-consuming conversion boundary of the experiment.
/// - fails: formation, typing, canonical-product or budget failures as
///   `PathError`; a bad conversion dialogue returns `KernelVerdict::Declined`.
/// - panics: none.
///
/// # Errors
/// Any `PathError` except `UnknownEliminator`.
///
/// # Adequacy
/// - hypothesis: L3 — negation transports false to true, the wrong answer is
///   certified negative, and the product clause preserves component order.
/// - witness: `path_universe::tests::transport_computes`
/// - witness: `path_universe::tests::a_wrong_answer_is_caught`
/// - witness: `path_universe::tests::it_computes_through_a_former`
#[inline]
pub fn replay_transport(
    arena: &mut TermArena,
    paths: &Paths,
    term: Transport,
    expected: ComputationId,
    claim: EngineClaim,
    dialogue: &Dialogue,
    budget: ReplayBudget,
) -> Result<KernelVerdict, PathError>
{
    let watermark = arena.watermark();
    let result = replay_checked(arena, paths, term, expected, claim, dialogue, budget);
    arena.truncate_to(watermark);
    result
}

/// Typecheck the transport boundary and replay the lowered computation.
///
/// # Specification
/// - requires: the caller restores the arena's entry watermark on every exit.
/// - ensures: as `replay_transport`, leaving intermediates for that
///   restoration.
/// - provides: the fallible interior of the restoration boundary.
/// - fails: formation, typing, product shape and budget errors.
/// - panics: none.
///
/// # Errors
/// As `replay_transport`.
///
/// # Adequacy
/// - hypothesis: L3 — the public replay witnesses cover this same interior.
/// - witness: `path_universe::tests::a_wrong_answer_is_caught`
fn replay_checked(
    arena: &mut TermArena,
    paths: &Paths,
    term: Transport,
    expected: ComputationId,
    claim: EngineClaim,
    dialogue: &Dialogue,
    budget: ReplayBudget,
) -> Result<KernelVerdict, PathError>
{
    let classifier = form(arena, paths, term.path, budget)?;
    check_closed_value(arena, term.value, classifier.source)
        .map_err(|error| PathError::Typing(Box::new(error)))?;
    let returner = arena.comp_type_returner(classifier.target);
    let thunk_type = arena.value_type_thunk(returner);
    let expected_thunk = arena.value_thunk(expected);
    check_closed_value(arena, expected_thunk, thunk_type)
        .map_err(|error| PathError::Typing(Box::new(error)))?;
    let reduct = coverage::lower(arena, paths, term, budget)?;
    Ok(crate::replay::replay(
        arena,
        &Unfoldings::new(Vec::new()),
        ReplaySides::Computations(reduct, expected),
        claim,
        dialogue.0.iter().copied(),
        budget,
    ))
}
