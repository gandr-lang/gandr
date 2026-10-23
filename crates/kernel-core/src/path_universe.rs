//! Native certificate-typed identity at closed first-order and session codes.
//!
//! `ValueType::PathUniverse`, the native path introductions and
//! `Computation::Transport` belong to the persisted term vocabulary. Admission
//! checks translators in the ordinary iterative checker and replays both
//! round trips on code-generated constructor patterns. Session introductions
//! instead replay a supplied finite bisimulation. Evidence contributes to
//! content identity, never to certificate conversion. No path inspection, K or
//! path-induction eliminator exists.
//!
//! # Formation and computation
//!
//! `ValueType::PathUniverse(a, b)` forms `Path_U a b` over closed quoted Base
//! codes, products of any arity (the unit among them), sums of at least one
//! summand, lists of a code among them, and finite session codes. The empty
//! sum is outside the vocabulary. A list's coverage unfolds one cell over a
//! rigid tail, so a round trip replayed there returns every list; a list also
//! moves along a path at its element code, by element transport in a List
//! motive, one cell per step. `PathProduct` stays binary: it relates
//! two-component products only, and transport over it computes on pairs.
//! First-order endpoints remain level zero; a session forms at its payload
//! telescope's universe level.
//! `Value::PathEquiv`, `PathRefl`, `PathProduct` and `SessionPath` introduce
//! paths. `Computation::Transport` computes for the first three; session
//! evidence describes recorded action skeletons, not kernel endpoint values.
//! They participate in ordinary arena traversal, declaration admission,
//! structural conversion and artifact encoding. The surface writes the
//! equivalence, `equiv(f, g)`, which its frontend erases to `PathEquiv`;
//! univalence at a stratum, `ua[n, k](a, b, f, g)`, which it erases to a
//! `PathProduct` of `PathEquiv`s over the reflexivity at the unit; and the
//! product `pathProduct(p, q)`, which it erases to the `PathProduct` of its
//! components' certificates, a `here` at a code among them as `PathRefl`.
//!
//! | Rule | Kernel obligation or computation |
//! | ---- | -------------------------------- |
//! | Formation | Both endpoints decode to the admitted value-code vocabulary and pass ordinary type formation. Session payload codes are checked in an empty term context. |
//! | Equivalence | Closed translators check at opposite CBPV arrows; every source and target round trip replays. |
//! | Reflexivity | The endpoint code forms. |
//! | Product | Both component paths form; endpoints are their products. |
//! | Transport | The input checks at the source and the comparison target at the target returner. |
//! | Equivalence beta | `transport (equiv f g) v` becomes `force f v`. |
//! | Reflexivity beta | `transport (refl a) v` becomes `return v` in one step. |
//! | Product beta | Pair input becomes left and right component transports. |
//! | Path conversion | Codes and translators compare structurally; round-trip evidence grants no certificate equality. |
//!
//! Round-trip coverage is symbolic: sums enumerate both injections, products
//! enumerate constructor combinations, and Base leaves introduce distinct
//! rigid variables rather than sample literals. Each pattern requires a
//! dialogue. Missing, extra or invalid evidence refuses admission. A
//! shape/coverage ceiling and per-dialogue replay budget are independent
//! limits, not one global work counter.
//!
//! `Dialogue::pair` constructs one product dialogue by prefixing explicit
//! `Decompose` decisions for the returner and pair, then concatenating
//! component traces. This prevents an initial `ComparedShared` from consuming
//! a component trace at the enclosing pair. The kernel re-derives every
//! boundary and premise. There is no transitive certificate-composition
//! operation.
//!
//! # Admission
//!
//! `Environment::add_decl` checks both endpoint codes, checks translators
//! under an empty term context and replays every source and target round
//! trip, unfolding the definitions admitted before it, so a translator may be
//! a named function. Decoding and frontend typechecking grant no authority.
//! Portable evidence participates in artifact content and admission memo
//! keys, but structural certificate conversion erases evidence only: it does
//! not normalize translator syntax. A fresh admission owns the memo and
//! rechecks imported candidates.
//!
//! `code`, `Dialogue::pair` and `replay_transport` remain callable. Path
//! operands are ordinary `ValueId`s in `TermArena`; no separate path arena or
//! string-named eliminator dispatcher exists. `replay_transport` rechecks the
//! native path and transport goal before consuming its dialogue.
//!
//! **Choice.** Native syntax makes the ordinary admission boundary
//! authoritative and permits artifacts to carry untrusted candidates.
//! Transport reduces to ordinary CBPV computations; product transport
//! sequences component computations through capture-avoiding binds.
//! **Alternative.** Rust translator closures or an auxiliary path arena would
//! evade persisted admission. **Reversal.** Extend the code grammar only with
//! formation, coverage and replay rules for the new fragment. Element
//! identity, open codes, higher fields, function codes and general dependent
//! elimination remain outside this decided fragment; an identity between two
//! such codes is admitted on evidence instead, below.
//!
//! # Univalence
//!
//! `Value::Univalence(e)`, the surface's `ua(e)`, is the second route to an
//! identity between two codes of `Type`, beside the decided certificate. It is
//! admitted on evidence, at any two codes: checked at `Path(Type, a, b)`, the
//! record `e` checks at the bi-invertible record over the types `a` and `b`
//! denote (`univalence_record`: `T` for `⌜T⌝`, `El c` for any other code);
//! anywhere else `e` synthesises a dependent pair whose first factor is a map
//! `U (A → F B)`, the identity is `Path(Type, a, b)` at the codes of `A` and
//! `B` (`univalence_reading`), its formation checks both codes at `Type`,
//! and `e` checks at the record. The record's section and retraction are
//! fields, so a law that does not hold is a field that does not check. The
//! node carries the record alone: its type names the identity, so a
//! univalence the checker reads back crosses as the same term as the one it
//! judged. Transport along it computes by `tr(ua(e), x) ⇝ f ← e.0; f(x)`;
//! two univalences convert when their records do.
//!
//! **Choice.** The record's laws are the evidence, not a decision.
//! **Alternative.** Extending the decided enumeration to every code was
//! declined: finite constructor coverage exists only on the first-order
//! stratum, and a code like `Path(Circle, base, base)` has none.
//! **Reversal.** Univalence proved as a theorem of the kernel (#520), after
//! which `ua` is a definition and this rule a derived one.
//!
//! # Witnesses
//!
//! The seven witnesses in this module's tests submit native declarations and
//! use independent `gandr-core-nbe` dialogues for Bool negation, product
//! transport, reflexivity, wrong-answer refusal, non-equivalence refusal,
//! intensional certificate conversion and absent K. The K witness applies
//! ordinary force and case eliminators to a path and observes their typing
//! refusals; it is not a theorem about future language extensions. Triple
//! negation retains its two sequencing seams and is compared with direct
//! composition at both Bool constructors. They distinguish omitted coverage,
//! swapped maps or product legs, accepted bad dialogues, reflexivity
//! reduction, evidence omitted from memo keys, and translator syntax erased by
//! conversion; no mutation score is claimed. The univalence witness admits
//! `ua` over lists of booleans, a code the decided stratum refuses, by
//! checking a record literal and by synthesis from an admitted record under a
//! transport, and refuses a record whose section does not hold.
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
use gandr_kernel_conversion_trace::ConversionDecision;
use gandr_kernel_term::ComputationId;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::Value;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueType;
use gandr_kernel_term::ValueTypeId;

use crate::check::check_closed_value;
use crate::env::AdmittedDeclaration;
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
    #[spec(
        captures: count = first.0.len().saturating_add(second.0.len()).saturating_add(2),
        ensures: |ret| ret.0.len() == count
            && matches!(ret.0.first(), Some(ConversionDecision::Decompose))
            && matches!(ret.0.get(1), Some(ConversionDecision::Decompose)),
    )]
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
    /// A univalence's record synthesises no dependent pair whose first factor
    /// is the thunk of a map `U (A → F B)`.
    ExpectedEquivalence(ValueTypeId),
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
            Self::Session(ref error) => error.fmt(f),
            Self::Arena => f.write_str("a universe-path root was unreadable"),
            Self::UnsupportedCode(_) => f.write_str("a universe-path endpoint was not quoted"),
            Self::UnsupportedType(_) => {
                f.write_str("a code was outside the native path vocabulary")
            },
            Self::ExpectedPath(_) => f.write_str("an equivalence annotation was not Path_U"),
            Self::ExpectedEquivalence(_) => {
                f.write_str("a univalence's record was not a bi-invertible map")
            },
            Self::Coverage(Direction::Source) => {
                f.write_str("incomplete source round-trip coverage")
            },
            Self::Coverage(Direction::Target) => {
                f.write_str("incomplete target round-trip coverage")
            },
            Self::RoundTrip {
                direction,
                pattern,
                verdict,
            } => {
                let direction = match direction {
                    Direction::Source => "source",
                    Direction::Target => "target",
                };
                let verdict = match verdict {
                    KernelVerdict::Convertible => "certified equality",
                    KernelVerdict::NotConvertible => "refuted equality",
                    KernelVerdict::Declined(_) => "replay declined",
                };
                write!(
                    f,
                    "{direction} round trip at pattern {}: {verdict}",
                    pattern.0
                )
            },
            Self::Budget => f.write_str("the universe-path allowance was exhausted"),
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
    #[spec(
        captures: before = self.0,
        ensures: |ret| match ret {
            Ok(()) => before.checked_sub(1) == Some(self.0),
            Err(PathError::Budget) => before == 0 && self.0 == 0,
            Err(_) => false,
        },
    )]
    pub(crate) fn charge(&mut self) -> Result<(), PathError>
    {
        self.0 = self.0.checked_sub(1).ok_or(PathError::Budget)?;
        Ok(())
    }
}

/// Inspect a quoted native path code and its finite session graph, if present.
///
/// # Specification
/// - ensures: accepts quoted Unit, Base, Sum, Product, List, the data types
///   `entries` admits that a coverage reads, and guarded Session shapes.
///   Session payload typing belongs to ordinary native formation; this
///   inspection is not a certificate or admission capability.
/// - provides: the callable code walk for consumers of native universe paths.
/// - fails: unsupported codes, unreadable roots or exhausted budget.
/// - panics: none.
///
/// # Errors
/// `UnsupportedCode`, `UnsupportedType`, `Arena`, or `Budget`.
///
/// # Adequacy
/// - hypothesis: L3 — Bool, products, lists and data types admit; thunk codes
///   refuse.
/// - witness: `path_universe::tests::a_non_equivalence_is_refused`
/// - witness: `path_universe::tests::a_list_code_covers_one_cell_over_a_rigid_tail`
/// - witness: `path_universe::coverage::tests::a_data_code_covers_as_its_constructors`
#[spec(ensures: |ret| match ret {
    Ok(root) => matches!(arena.value(code), Some(&Value::Quote(quoted)) if root == quoted),
    Err(PathError::UnsupportedCode(named)) => named == code && !matches!(arena.value(code), Some(&Value::Quote(_))),
    Err(PathError::Budget | PathError::Arena) => true,
    Err(PathError::UnsupportedType(root)) => arena.value_type(root).is_some_and(|node| !matches!(node, &ValueType::Base(_) | &ValueType::Product(..) | &ValueType::List(_)) && node.summands().is_none_or(<[_]>::is_empty)),
    Err(_) => false,
})]
#[inline]
pub fn code(
    arena: &TermArena,
    entries: &[AdmittedDeclaration],
    code: ValueId,
    budget: ReplayBudget,
) -> Result<ValueTypeId, PathError>
{
    coverage::code(arena, code, entries, &mut Allowance(u64::from(budget)))
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
#[spec(ensures: |ret| match ret {
    Ok(path) => matches!(arena.value_type(classifier), Some(&ValueType::PathUniverse(source, target))
        if matches!(arena.value(source), Some(&Value::Quote(root)) if root == path.source)
            && matches!(arena.value(target), Some(&Value::Quote(root)) if root == path.target)),
    Err(PathError::ExpectedPath(named)) => named == classifier && !matches!(arena.value_type(classifier), Some(&ValueType::PathUniverse(..))),
    Err(_) => true,
})]
#[inline]
pub fn endpoints(
    arena: &TermArena,
    entries: &[AdmittedDeclaration],
    classifier: ValueTypeId,
    budget: ReplayBudget,
) -> Result<PathType, PathError>
{
    let Some(&ValueType::PathUniverse(source, target)) = arena.value_type(classifier)
    else {
        return Err(PathError::ExpectedPath(classifier));
    };
    let mut allowance = Allowance(u64::from(budget));
    let source = coverage::code(arena, source, entries, &mut allowance)?;
    let target = coverage::code(arena, target, entries, &mut allowance)?;
    Ok(PathType { source, target })
}
/// Compute one native transport beta step, without claiming formation.
///
/// # Specification
/// - requires: admission established the path and operand types.
/// - ensures: reflexivity returns the exact operand; equivalence applies its
///   forward map; univalence applies its record's forward map; product
///   transport sequences both components without capture.
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
#[spec(ensures: |ret| match (arena.value(term.path), &ret) {
    (Some(&Value::PathRefl(_)), &Ok(Reduction::Reduced(result))) => matches!(arena.computation(result), Some(&gandr_kernel_term::Computation::Return(value)) if value == term.value),
    (Some(&Value::PathEquiv { forward, .. }), &Ok(Reduction::Reduced(result))) => matches!(arena.computation(result), Some(&gandr_kernel_term::Computation::Application(head, value)) if value == term.value && matches!(arena.computation(head), Some(&gandr_kernel_term::Computation::Force(map)) if map == forward)),
    (Some(&Value::Univalence { .. }), &Ok(Reduction::Reduced(result))) => matches!(arena.computation(result), Some(&gandr_kernel_term::Computation::Bind(..))),
    (Some(&Value::PathProduct(..)), &Ok(Reduction::Reduced(result))) => arena.value(term.value).and_then(Value::components).is_some_and(|components| components.len() == 2_usize) && matches!(arena.computation(result), Some(&gandr_kernel_term::Computation::Bind(..))),
    (Some(&Value::PathProduct(..)), &Ok(Reduction::Stuck)) => arena.value(term.value).is_some_and(|value| value.components().is_none_or(|components| components.len() != 2_usize)),
    (Some(&Value::PathProduct(..)), &Err(PathError::Arena)) => arena.value(term.value).is_none(),
    (None, &Err(PathError::Arena)) => true,
    (Some(value), &Ok(Reduction::Stuck)) => !matches!(value, &Value::PathRefl(_) | &Value::PathEquiv { .. } | &Value::Univalence { .. } | &Value::PathProduct(..)),
    _ => false,
})]
#[inline]
pub fn beta(
    arena: &mut TermArena,
    term: Transport,
) -> Result<Reduction, PathError>
{
    let reduct = match arena.value(term.path) {
        Some(&Value::PathRefl(_)) => arena.computation_return(term.value),
        Some(&Value::PathEquiv { forward, .. }) => {
            let force = arena.computation_force(forward);
            arena.computation_application(force, term.value)
        },
        // `tr(ua(e), x) ⇝ f ← e.0; f(x)`: the record's first component is
        // its forward map.
        Some(&Value::Univalence(equivalence)) => {
            let forward = arena.computation_tuple_projection(
                equivalence,
                gandr_kernel_term::Component::from(0_usize),
            );
            let map = arena.value_variable(gandr_kernel_term::DeBruijnIndex::from(0_u32));
            let force = arena.computation_force(map);
            let value = crate::rewrite::shift_value(
                arena,
                &mut crate::encoding::ContentTable::new(),
                &mut gandr_kernel_check_memo::NullMemo,
                term.value,
                crate::rewrite::BinderDepth::default(),
                crate::rewrite::BinderDepth::from(1_u32),
            );
            let applied = arena.computation_application(force, value);
            arena.computation_bind(forward, applied)
        },
        Some(&Value::PathProduct(first, second)) => {
            let Some(&[left, right]) = arena.value(term.value).and_then(Value::components)
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
            let pair = arena.value_tuple(&[left, right]);
            let result = arena.computation_return(pair);
            let result = arena.computation_bind(second, result);
            arena.computation_bind(first, result)
        },
        Some(_) => return Ok(Reduction::Stuck),
        None => return Err(PathError::Arena),
    };
    Ok(Reduction::Reduced(reduct))
}

/// The two codes of `path_type` when it is an identity between codes of the
/// level-zero value universe, under either reading: `Path(Type, a, b)` or the
/// native `Path_U(a, b)`. These are the identities `ua(e)` checks against, so a
/// univalence pays a bisimilarity's payload pair, whose obligation is native.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the endpoints `a` and `b`, in order, when `path_type` resolves to
///   a path type whose domain resolves to the level-zero universe of value
///   codes, or to `Path_U(a, b)`.
/// - fails: [`PathError::ExpectedPath`] naming `path_type` otherwise.
/// - panics: none.
///
/// # Errors
/// As `fails`.
///
/// # Adequacy
/// - hypothesis: L3 — a record literal checks against `Path(Type, ⌜List Bool⌝,
///   ⌜List Bool⌝)` and against `Path_U` at the same codes, and an identity at
///   the booleans is refused by name.
/// - witness: `path_universe::tests::univalence_is_admitted_on_its_record`
#[spec(ensures: |ret| match ret {
    Ok((left, right)) => match arena.value_type(path_type) {
        Some(&ValueType::Path { left: written, right: other, .. } | &ValueType::PathUniverse(written, other)) => written == left && other == right,
        _ => false,
    },
    Err(PathError::ExpectedPath(named)) => named == path_type,
    Err(_) => false,
})]
pub(crate) fn identity_codes(
    arena: &TermArena,
    path_type: ValueTypeId,
) -> Result<(ValueId, ValueId), PathError>
{
    let refused = PathError::ExpectedPath(path_type);
    let (domain, left, right) = match arena.value_type(path_type) {
        Some(&ValueType::PathUniverse(left, right)) => return Ok((left, right)),
        Some(&ValueType::Path {
            domain,
            left,
            right,
            ..
        }) => (domain, left, right),
        _ => return Err(refused),
    };
    if matches!(
        arena.value_type(domain),
        Some(&ValueType::Universe { sort: gandr_kernel_term::GroundSort::Value, ref level }) if *level == gandr_kernel_strata::Level::zero()
    ) {
        Ok((left, right))
    }
    else {
        Err(refused)
    }
}

/// The bi-invertible record `ua(e)` at `path_type` is admitted on: `Σ (to :
/// U (A → F B)). (Σ (g : U (B → F A)). sect) × (Σ (h : U (B → F A)). retr)`,
/// with `A` and `B` the types the identity's two codes denote.
///
/// # Specification
/// - requires: nothing; formation of `path_type` is the caller's.
/// - ensures: for `path_type = Path(Type, a, b)` at the level-zero value
///   universe, or `Path_U(a, b)`, the record over `A` and `B`, where a quoted
///   code `⌜T⌝` denotes `T` and any other code `c` the decode `El c`; `sect` is
///   `(x : A) → F Path(A, g(to(x)), x)` and `retr` is `(y : B) → F Path(B,
///   to(h(y)), y)`, each application the value its computation returns and each
///   type shifted past the binders it stands under.
/// - provides: the one statement of the laws the kernel admits univalence on;
///   the checker's record is the same tree, so the bridge passes it unchanged.
/// - fails: [`PathError::ExpectedPath`] naming `path_type` when it is no
///   identity at the level-zero value universe; [`PathError::Arena`] when a
///   node does not resolve.
/// - panics: none.
///
/// # Errors
/// As `fails`.
///
/// # Adequacy
/// - hypothesis: L3 — a record over two bound codes checks against the record a
///   source states for `A ≃ B`, and an identity at a type other than the
///   universe is refused by name.
/// - witness: `path_universe::tests::univalence_is_admitted_on_its_record`
#[spec(ensures: |ret| match ret {
    Ok(record) => matches!(arena.value_type(record), Some(&ValueType::Sigma { .. })),
    Err(PathError::ExpectedPath(named)) => named == path_type,
    Err(_) => true,
})]
pub(crate) fn univalence_record(
    arena: &mut TermArena,
    path_type: ValueTypeId,
) -> Result<ValueTypeId, PathError>
{
    let (left, right) = identity_codes(arena, path_type)?;
    let source = denoted(arena, left)?;
    let target = denoted(arena, right)?;
    let one = crate::rewrite::BinderDepth::from(1_u32);
    let past = |arena: &mut TermArena, subject, amount| {
        crate::rewrite::shift_value_type(
            arena,
            &mut crate::encoding::ContentTable::new(),
            &mut gandr_kernel_check_memo::NullMemo,
            subject,
            crate::rewrite::BinderDepth::default(),
            amount,
        )
    };
    let forward = map_type(arena, source, target);
    let source_past = past(arena, source, one);
    let target_past = past(arena, target, one);
    let left_map = map_type(arena, target_past, source_past);
    let source_laws = past(arena, source, one.deeper());
    let section = round_trip(arena, source_laws, Trip::Section);
    let left = arena.value_type_sigma(left_map, section);
    let right_map = map_type(arena, target_past, source_past);
    let target_laws = past(arena, target, one.deeper());
    let retraction = round_trip(arena, target_laws, Trip::Retraction);
    let right = arena.value_type_sigma(right_map, retraction);
    let inverses = arena.value_type_product(&[left, right]);
    Ok(arena.value_type_sigma(forward, inverses))
}

/// The identity `ua(e)` synthesises from the type `classifier` its record
/// synthesised, with the record type the record then checks against.
///
/// # Specification
/// - requires: nothing; `classifier` is the type the record synthesised.
/// - ensures: for `classifier` a dependent pair whose first factor is the thunk
///   `U (A → F B)` of a non-dependent arrow, the identity `Path(Type, a, b)` at
///   the level-zero value universe between the codes of `A` and `B` — `c` for
///   `El c`, the quote of any other type — and the record type
///   [`univalence_record`] states at it, in that order.
/// - provides: the synthesising reading of `ua(e)`: the record's own type names
///   the two codes, so the node carries nothing else.
/// - fails: [`PathError::ExpectedEquivalence`] naming `classifier` when it is
///   no such pair.
/// - panics: none.
///
/// # Errors
/// As `fails`.
///
/// # Adequacy
/// - hypothesis: L3 — a record of `Path(Circle, base, base) ≃ Int` names both
///   codes as quotes and a record over two bound codes names the variables;
///   reading the codes off the wrong side of the map, or quoting a decode,
///   synthesises an identity the checker's does not convert with.
/// - witness: `path_universe::tests::univalence_is_admitted_on_its_record`
#[spec(ensures: |ret| match ret {
    Ok((path_type, record)) => matches!(arena.value_type(path_type), Some(&ValueType::Path { .. })) && matches!(arena.value_type(record), Some(&ValueType::Sigma { .. })),
    Err(PathError::ExpectedEquivalence(named)) => named == classifier,
    Err(_) => true,
})]
pub(crate) fn univalence_reading(
    arena: &mut TermArena,
    classifier: ValueTypeId,
) -> Result<(ValueTypeId, ValueTypeId), PathError>
{
    let refused = PathError::ExpectedEquivalence(classifier);
    let Some(&ValueType::Sigma { first, .. }) = arena.value_type(classifier)
    else {
        return Err(refused);
    };
    let Some(&ValueType::Thunk(map)) = arena.value_type(first)
    else {
        return Err(refused);
    };
    let Some(&gandr_kernel_term::CompType::Arrow { domain, codomain }) = arena.comp_type(map)
    else {
        return Err(refused);
    };
    let Some(&gandr_kernel_term::CompType::Returner(target)) = arena.comp_type(codomain)
    else {
        return Err(refused);
    };
    let source = code_of(arena, domain);
    let target = code_of(arena, target);
    let universe = arena.value_type_universe(
        gandr_kernel_term::GroundSort::Value,
        gandr_kernel_strata::Level::zero(),
    );
    let path_type = arena.value_type_path(universe, source, target);
    let record = univalence_record(arena, path_type)?;
    Ok((path_type, record))
}

/// The code of the value type `carrier`: `c` for `El c`, the quote of any
/// other type.
///
/// # Specification
/// trivial.
fn code_of(
    arena: &mut TermArena,
    carrier: ValueTypeId,
) -> ValueId
{
    match arena.value_type(carrier) {
        Some(&ValueType::Element { code, .. }) => code,
        Some(_) | None => arena.value_quote(carrier),
    }
}

/// The type a code of the level-zero value universe denotes: `T` for `⌜T⌝`,
/// `El c` for any other code `c`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the quoted type, or a fresh decode at level zero.
/// - fails: [`PathError::Arena`] when `code` does not resolve.
/// - panics: none.
///
/// # Errors
/// As `fails`.
///
/// # Adequacy
/// - hypothesis: L3 — as [`univalence_record`].
/// - witness: `path_universe::tests::univalence_is_admitted_on_its_record`
#[spec(ensures: |ret| match ret {
    Ok(ty) => arena.value_type(ty).is_some(),
    Err(PathError::Arena) => true,
    Err(_) => false,
})]
fn denoted(
    arena: &mut TermArena,
    code: ValueId,
) -> Result<ValueTypeId, PathError>
{
    match arena.value(code) {
        Some(&Value::Quote(quoted)) => Ok(quoted),
        Some(_) => Ok(arena.value_type_element(code, gandr_kernel_strata::Level::zero())),
        None => Err(PathError::Arena),
    }
}

/// The type `U (from → F to)` of a map.
///
/// # Specification
/// trivial.
fn map_type(
    arena: &mut TermArena,
    from: ValueTypeId,
    to: ValueTypeId,
) -> ValueTypeId
{
    let returned = arena.comp_type_returner(to);
    let arrow = arena.comp_type_arrow(from, returned);
    arena.value_type_thunk(arrow)
}

/// Which law of a bi-invertible record a round trip states.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Trip
{
    /// `g(to(x)) = x`, the inverse the forward map's.
    Section,
    /// `to(h(y)) = y`, the forward map the inverse's.
    Retraction,
}

/// The law `U ((x : C) → F Path(C, outer(inner(x)), x))` over `carrier`,
/// standing past the forward map and the inverse.
///
/// # Specification
/// - requires: `carrier` already stands past the two maps.
/// - ensures: the thunk of the dependent arrow over `carrier`, returning the
///   path over `carrier` shifted past its binder from the outer map applied to
///   the inner one applied to the bound point, to the bound point: under the
///   binder the point is `#0`, the inverse `#1` and the forward map `#2`.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`univalence_record`].
/// - witness: `path_universe::tests::univalence_is_admitted_on_its_record`
#[spec(ensures: |ret| matches!(arena.value_type(ret), Some(&ValueType::Thunk(_))))]
fn round_trip(
    arena: &mut TermArena,
    carrier: ValueTypeId,
    trip: Trip,
) -> ValueTypeId
{
    let (inner, outer) = match trip {
        Trip::Section => (2_u32, 1_u32),
        Trip::Retraction => (1_u32, 2_u32),
    };
    let over = crate::rewrite::shift_value_type(
        arena,
        &mut crate::encoding::ContentTable::new(),
        &mut gandr_kernel_check_memo::NullMemo,
        carrier,
        crate::rewrite::BinderDepth::default(),
        crate::rewrite::BinderDepth::from(1_u32),
    );
    let point = arena.value_variable(gandr_kernel_term::DeBruijnIndex::from(0_u32));
    let first = arena.value_variable(gandr_kernel_term::DeBruijnIndex::from(inner));
    let forced = arena.computation_force(first);
    let applied = arena.computation_application(forced, point);
    let midway = arena.value_returned(applied);
    let second = arena.value_variable(gandr_kernel_term::DeBruijnIndex::from(outer));
    let forced = arena.computation_force(second);
    let applied = arena.computation_application(forced, midway);
    let there = arena.value_returned(applied);
    let path = arena.value_type_path(over, there, point);
    let returned = arena.comp_type_returner(path);
    let dependent = arena.comp_type_pi(carrier, returned);
    arena.value_type_thunk(dependent)
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
#[spec(
    captures: before = arena.watermark(),
    ensures: arena.watermark() == before,
)]
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
#[spec(ensures: |ret| u64::from(budget) != 0 || matches!(ret, Err(KernelError::Path(PathError::Budget))))]
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
    let endpoints = endpoints(arena, &[], classifier, budget).map_err(KernelError::Path)?;
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
#[spec(ensures: |ret| match (decision, ret) {
    (ConversionDecision::Freeze { side: first, .. }, ConversionDecision::Freeze { side: second, .. })
    | (ConversionDecision::EtaExpand { side: first, .. }, ConversionDecision::EtaExpand { side: second, .. })
    | (ConversionDecision::ReturnEta { side: first }, ConversionDecision::ReturnEta { side: second })
    | (ConversionDecision::Reassociate { side: first }, ConversionDecision::Reassociate { side: second })
    | (ConversionDecision::Discard { side: first }, ConversionDecision::Discard { side: second }) => first == second,
    (ConversionDecision::NegativeSubgoal { position: first }, ConversionDecision::NegativeSubgoal { position: second }) => first == second,
    (ConversionDecision::ReduceLeft { .. }, ConversionDecision::ReduceLeft { .. })
    | (ConversionDecision::ReduceRight { .. }, ConversionDecision::ReduceRight { .. })
    | (ConversionDecision::ConstShortcut { .. }, ConversionDecision::ConstShortcut { .. })
    | (ConversionDecision::Unfold { .. }, ConversionDecision::Unfold { .. })
    | (ConversionDecision::Postpone { .. }, ConversionDecision::Postpone { .. })
    | (ConversionDecision::Force { .. }, ConversionDecision::Force { .. })
    | (ConversionDecision::ComparedShared { .. }, ConversionDecision::ComparedShared { .. })
    | (ConversionDecision::Decompose, ConversionDecision::Decompose) => true,
    _ => false,
})]
pub(crate) fn anchor(decision: ConversionDecision<()>) -> ConversionDecision<ReplayNode>
{
    decision.map(|()| ReplayNode::Other)
}
