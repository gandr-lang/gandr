//! The directed family: `Flow_U`, `Flow(A, x, y)`, their introductions,
//! composition and `ride`, as native kernel syntax.
//!
//! `Flow(A, x, y)` says only that `x` transports into `y`; `Flow_U(a, b)` is
//! its native classifier at the level-zero value universe, over quoted
//! first-order, function and session codes. Every introduction is a value
//! node and every eliminator a computation node in `gandr-kernel-term`'s
//! table, so a declaration stating a flow persists it in an artifact and
//! readmits it by replaying what this module decides. No stored node or
//! classifier is an admission receipt: each admission rechecks.
//!
//! # The family
//!
//! The vocabulary is quoted Base codes, products of any arity (the unit among
//! them), sums of at least one summand, function codes `U (A → F B)` whose
//! argument and result are among those, and finite session codes, which only a
//! session simulation relates. The empty sum is outside it. Path and Flow are
//! independent families: no rule coerces one into the other.
//!
//! | Node | Byte | Classifier | Admission replays |
//! | ---- | ---- | ---------- | ----------------- |
//! | `ValueType::FlowUniverse(a, b)` | `0x48` | — | both endpoints in the vocabulary ([`endpoints`]) |
//! | `Value::SessionFlow` | `0x49` | `Flow_U(a, b)` at session codes | the supplied simulation and its payload paths |
//! | `ValueType::Flow { domain, source, target }` | `0x4A` | — | both endpoints at the domain |
//! | `Value::Stay { point, dialogues }` | `0x4B` | `Flow(A, c, c)`; checks at `Flow(A, x, y)` and `Flow_U(x, y)` | the point converts with both endpoints, or each side's dialogue replays |
//! | `Value::ForwardFlow { flow_type, translator, outputs, dialogues }` | `0x4C` | `Flow_U(a, b)` at first-order codes | the closed translator checks; one image per source pattern, leaf-natural, its dialogue replayed |
//! | `Value::FunctionFlow { flow_type, domain, codomain }` | `0x4D` | `Flow_U(f, g)` at function codes | each boundary flow runs the way its variance fixes |
//! | `Value::Then { first, second, seam }` | `0x4E` | `Flow(A, x, z)`, or `Flow_U(x, z)` when either side is | the carriers agree, the seam's endpoints meet, the seam is a sequence |
//! | `Value::FlowProduct(first, second)` | `0x69` | `Flow_U(⌜A × B⌝, ⌜A' × B'⌝)` | each component reads as a universe flow, `Flow_U(A, A')` then `Flow_U(B, B')`, under either reading; both pairs are codes of the vocabulary |
//! | `Computation::Ride { motive, flow, value }` | `0x4F` | `F P[y]` | the motive passes [`check_motive`]; the value checks at `P[x]` |
//! | `Computation::TelescopeRide { motive, flow, start, over, value }` | `0x68` | `F C[b, end]` | both entries pass the gate; `over` lies over `flow` |
//!
//! At the level-zero value universe `Flow(U₀, x, y)` and `Flow_U(x, y)` are
//! two readings of one classifier: a flow synthesizing either checks at the
//! other, and a flow is consumed — by `ride`, by `then`, by a function flow's
//! boundary — under either. Elsewhere `stay`, composition and neutrals inhabit
//! `Flow(A, x, y)`.
//!
//! # Computation
//!
//! The replay reads a ride by the first row of [`reduce`]'s table that
//! applies: `stay` returns the value; a sequential composition rides its first
//! flow, then its second; a motive that ignores its binder returns the value;
//! products, sums and lists ride constructorwise, each part's ride bound
//! before the next and the constructor returned last; at `El(x)` a forward
//! flow applies its translator, a function flow wraps the function in its
//! boundaries and a flow product rides a pair's left component along its
//! first flow, then its right along its second; at a singleton motive
//! `Flow(D, l, x)` a `stay` value returns the flow and any other value
//! composes with it. A session simulation relates recorded runs, not endpoint
//! values: a ride along one is stuck, and [`replay_ride`] refuses it as
//! `RecordedRunRequired`. A telescope ride along `stay` in its carrier rides
//! in the fibre; along `stay` in both entries it returns the value. That row
//! is directed J's computation rule.
//!
//! The table itself is δ-free: no row unfolds a definition. A ride met inside
//! an endpoint dialogue is reduced by the table, and every definition it
//! needs unfolds where the checker's recorded dialogue names it, never by
//! search. A ride along a named flow is stuck on that flow, so the flow heads
//! the ride and the dialogue's unfolding on its side reaches it; two rides
//! stuck on one flow compare their motives, then their values. A translator
//! named by a definition unfolds where the row's bind leaves its application
//! at the head: under a flow product or a constructor motive, after every part
//! bound before it. A telescope ride stays unreadable to the replay and its
//! flows δ-free: the checker produces none, so no recorded dialogue runs
//! through one.
//!
//! # Refusals
//!
//! | Refusal | Raised when |
//! | ------- | ----------- |
//! | `NonCovariantMotive` | the moving binder occurs at a contravariant or invariant position of a ride's motive: the symmetry motive `Flow_U(x, a)` among them |
//! | `NonNatural` | a forward image is not a canonical target shape over correctly typed source leaves: a constant literal at an infinite Base leaf among them |
//! | `Coverage` | a forward flow carries more or fewer images than its source has constructor patterns |
//! | `ForwardReplay` | a forward image's dialogue does not replay to convertible |
//! | `UnsupportedCode`, `UnsupportedType` | an endpoint leaves the vocabulary a certificate covers |
//! | `EndpointMismatch` | a composition's carriers or seam endpoints differ |
//! | `Cycle` | a composition requests a feedback seam |
//! | `Boundary` | a function flow's boundary runs against its variance |
//! | `FamilyMismatch`, `ExpectedFlow` | a certificate of the other family, or of neither, stands where a flow is consumed |
//! | `RecordedRunRequired` | a ride along a session simulation reaches [`replay_ride`] |
//!
//! No node reverses a flow. A flow checked at its reversed classifier, a value
//! ridden from the target, and a composition of a flow with itself the wrong
//! way round each refuse by the names above: `back` has no directed reading.
//!
//! **Leaf naturality.** Each source Base position is a distinct rigid
//! variable, including equal-typed positions in a product. An image is
//! `thunk(λ…λ. return o)`, one binder per leaf, so the proposed output `o`
//! names leaves by index and stays closed under every rewrite; it contains
//! only canonical constructors and correctly typed leaf variables. The kernel
//! replays the translator on these symbolic inputs; a trace generated at a
//! literal sample has no authority over that obligation. Literals nested
//! beneath sums or products, fresh variables, wrong-typed selections and
//! sample-only constant maps refuse. The witnesses cover diagonals, both
//! injections, codiagonals, product identity and terminal projection to Unit.
//! The native CBPV vocabulary has no general product eliminator, so these
//! witnesses do not establish generation of every projection or fullness of
//! the one-way alphabet.
//!
//! **The gate reads wiring.** Sequence has one edge between two occurrences;
//! feedback adds the reverse edge and closes a cycle. Equal endpoint codes do
//! not identify occurrences. Injection followed by fold forms and rides as
//! identity, and terminal followed by injection forms a constant Bool endomap.
//! Neither composite grants inverse evidence.
//!
//! # Directed funext
//!
//! **The arrow's action is the statement.** `Flow_U` at a function code is a
//! forward flow of results over a forward flow of arguments, the argument flow
//! running from the target's domain to the source's. Variance is data:
//! [`Boundary::variance`] is all the formation rule reads to orient a
//! boundary, and it is the reversal [`check_motive`] applies at an arrow's
//! domain. No modality, polarity-annotated context or internal hom object
//! enters. The statement binds no variable, since its boundaries are flows of
//! codes, so the divariant variable that keeps directed function
//! extensionality out of a polarity calculus does not arise (Jacob Neumann, *A
//! Generalized Algebraic Theory of Directed Equality*, doctoral thesis,
//! University of Nottingham, 2025, §0.2 and §4.4). Riding a flow through a
//! function's argument is the motive `U (El x → F El a)`, which
//! [`check_motive`] refuses as it refuses symmetry: the argument boundary is
//! consumed only contravariantly, by this clause.
//!
//! **Leaves at a function code.** Both boundary flows are leaf-natural
//! certificates and the ride only composes them with its argument, so it
//! manufactures no leaf: a constant result boundary refuses as `NonNatural`
//! before the function flow forms. The arrow of two `stay`s rides a function
//! to itself by conversion replay.
//!
//! **What the clause does not state.** A flow between two functions of one
//! first-order function code would relate their outputs pointwise over related
//! inputs. First-order elements carry only identities, so that relation is
//! element identity at the thunk code, which [`crate::identity_recursion`]
//! computes; this module adds nothing there. A natural transformation between
//! code-valued functions, where an argument would occur at both variances, is
//! outside the clause.
//!
//! # Decision
//!
//! **Choice.** The directed family is native kernel syntax at parity with the
//! groupoidal one: two classifiers, six introductions and two eliminators,
//! admitted by the ordinary checking machine and computed by the ordinary
//! replay. Each certificate's obligation is the one the rule language decided:
//! exhaustive symbolic images for a forward translator, the seam gate for
//! composition, variance order for the arrow's action, reflexivity for
//! `stay`, simulation replay for a session. `ride` subsumes universe
//! transport: a flow at `Flow_U` rides with its binder at the level-zero
//! universe, so one eliminator serves both readings, and one `stay` and one
//! `then` serve both. The covariance gate walks the native motive with a sign,
//! so the condition the rule language stated over its own motive syntax now
//! binds every motive a declaration writes. `FORMAT_VERSION` holds: every byte
//! was reserved and unassigned, and an older reader refuses each by name.
//! **Alternatives.** An in-memory rule language beside native terms, which no
//! declaration could state or persist; a separate universe transport for
//! `Flow_U`, which would duplicate `ride`'s table; images as open values,
//! whose leaf variables a rewrite under an enclosing binder would capture; a
//! second evaluator; host-language translators, which would bypass the
//! obligation; deciding session subtyping in the checker alone. At function
//! codes: forward translators covered symbolically, which have no constructor
//! pattern to replay; a classifier derived from the boundary flows alone,
//! under which no direction can be refused; a polarity modality on contexts.
//! **The rule, and where it fired.** An introduction becomes a native former
//! when a declaration consumes it. It fired twice: when session subtyping
//! became a declared `Flow_U` statement of the surface language (the
//! classifier and the session simulation, `0x48` and `0x49`), and when the
//! surface family's `Flow`, `stay`, `then` and `ride` became statements a
//! declaration makes (`0x4A`–`0x4F` and `0x68`). It fired a third time for the
//! componentwise product, `0x69`, the directed twin of `Value::PathProduct`:
//! a hand-written degree-one universe flow over a telescope is a nested
//! product of `stay` and forward flows, as the groupoidal one is of
//! reflexivity and equivalences. Its obligation is its components': each
//! replays as itself, and the ride on a pair rides each component along its
//! own flow, as transport along a path product does. The function clause is
//! revisited when an argument code is itself a function or universe code,
//! where an argument variable would occur at both variances, or when a
//! translator at function codes that is not the arrow of two boundary flows
//! must be certified.
//!
//! # What a producer may assume
//!
//! The node shapes and bytes in the table above; for each certificate, the
//! checking machine's admission as its replay entry, and [`form_certificate`]
//! as the entry that synthesizes a closed certificate and names its family;
//! [`replay_ride`] as the entry that checks a closed ride and replays a
//! claimed result. Both entries answer [`crate::KernelError`], as the path
//! entries do: a flow refusal arrives as `KernelError::Flow` under the names
//! in the table above, never as a panic on tampered evidence.
//!
//! # Witnesses
//!
//! The witnesses in this module's tests use an independent conversion engine
//! and exact expected outputs; the readmission witnesses in
//! `tests/flow_readmission.rs` persist a module of every certificate kind,
//! decode and replay it, and tamper with an image, a seam and a boundary. The
//! public replay boundary restores its arena watermark on success and
//! failure, and supplies no checker memo.
use core::fmt;

use anodized::spec;
use gandr_kernel_strata::Level;
use gandr_kernel_term::AnyNode;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::Seam;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::Value;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueType;
use gandr_kernel_term::ValueTypeId;

use crate::conv::Convertibility;
use crate::conv::convert_values;
use crate::conv::convertible_value_types;
use crate::replay::KernelVerdict;
use crate::replay::ReplayBudget;

mod coverage;
mod motive;
pub(crate) mod reduce;
mod rules;
#[cfg(test)]
mod tests;

use coverage::Arrow;
pub(crate) use coverage::forward;
pub use motive::check_motive;
pub use rules::CertificateType;
pub use rules::form_certificate;
pub(crate) use rules::oriented;
pub use rules::replay_ride;

/// The separate certificate families at a consuming boundary.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Family
{
    /// Invertible identity.
    Path,
    /// Forward-only transport.
    Flow,
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
    /// The variance the arrow fixes at this boundary, as [`check_motive`]
    /// reads an arrow.
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

impl Variance
{
    /// Reverse variance through an arrow domain or a flow source.
    ///
    /// # Specification
    /// trivial.
    const fn reverse(self) -> Self
    {
        match self {
            Self::Contravariant => Self::Covariant,
            Self::Covariant => Self::Contravariant,
        }
    }
}

/// `Flow_U source target`, with input contravariant and output covariant.
///
/// # Specification
/// - provides: endpoint types only; this classifier grants no authority.
/// - panics: none.
/// - executable: none — endpoint fields alone certify no translator; admission
///   checks their relation to the certificate.
/// # Adequacy
/// - hypothesis: L3 — formation retains the direction of the terminal map.
/// - witness: `flow_universe::tests::stay_and_forward_admit_and_ride`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct FlowType
{
    /// Consumed endpoint.
    pub source: ValueTypeId,
    /// Produced endpoint.
    pub target: ValueTypeId,
}

/// Inspect and decode both endpoints of a native `Flow_U` classifier.
///
/// # Specification
/// - ensures: each endpoint is a quoted code of the `Flow_U` vocabulary: a
///   first-order code, a function code over first-order codes, or a finite
///   guarded session code. The returned roots are the quoted types. Session
///   payload typing belongs to ordinary native formation.
/// - fails: `FamilyMismatch` for a `Path_U` classifier, `ExpectedFlow` for any
///   other classifier, or a code-walk refusal.
/// - panics: none.
///
/// # Errors
/// `FamilyMismatch`, `ExpectedFlow`, `UnsupportedCode`, `UnsupportedType`,
/// `Path` for a malformed session code, `Arena` or `Budget`.
///
/// # Adequacy
/// - hypothesis: L3 — session endpoints decode; a session flow given as a path
///   and a session path given as a flow each refuse as `FamilyMismatch`; a
///   thunk of a bare returner refuses.
/// - witness: `session::tests::session_flows_persist_and_refuse_by_family`
#[spec(ensures: |ret| match ret {
    Ok(flow) => matches!(arena.value_type(classifier), Some(&ValueType::FlowUniverse(source, target))
        if matches!(arena.value(source), Some(&Value::Quote(root)) if root == flow.source)
            && matches!(arena.value(target), Some(&Value::Quote(root)) if root == flow.target)),
    Err(FlowError::FamilyMismatch { expected: Family::Flow, actual: Family::Path }) => matches!(arena.value_type(classifier), Some(&ValueType::PathUniverse(..))),
    Err(FlowError::ExpectedFlow(named)) => named == classifier && !matches!(arena.value_type(classifier), Some(&(ValueType::FlowUniverse(..) | ValueType::PathUniverse(..)))),
    Err(_) => true,
})]
#[inline]
pub fn endpoints(
    arena: &TermArena,
    classifier: ValueTypeId,
    budget: ReplayBudget,
) -> Result<FlowType, FlowError>
{
    let (source, target) = universe_codes(arena, classifier)?;
    let mut allowance = Allowance(u64::from(budget));
    let source = coverage::vocabulary(arena, source, &mut allowance, budget)?;
    let target = coverage::vocabulary(arena, target, &mut allowance, budget)?;
    Ok(FlowType { source, target })
}

/// The two codes of a `Flow_U` classifier, refusing every other classifier by
/// family.
///
/// # Specification
/// - ensures: the classifier's source and target codes, undecoded.
/// - fails: `FamilyMismatch` for a `Path_U` classifier, `ExpectedFlow`
///   otherwise.
/// - panics: none.
///
/// # Errors
/// As `fails`.
///
/// # Adequacy
/// - hypothesis: L3 — a session path given as a flow refuses by family.
/// - witness: `session::tests::session_flows_persist_and_refuse_by_family`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |&(source, target)| arena.value_type(classifier) == Some(&ValueType::FlowUniverse(source, target))))]
fn universe_codes(
    arena: &TermArena,
    classifier: ValueTypeId,
) -> Result<(ValueId, ValueId), FlowError>
{
    match arena.value_type(classifier) {
        Some(&ValueType::FlowUniverse(source, target)) => Ok((source, target)),
        Some(&ValueType::PathUniverse(..)) => Err(FlowError::FamilyMismatch {
            expected: Family::Flow,
            actual: Family::Path,
        }),
        _ => Err(FlowError::ExpectedFlow(classifier)),
    }
}

/// Decode a forward flow's classifier: `Flow_U` between two first-order codes.
///
/// # Specification
/// - ensures: both quoted types pass the first-order walk.
/// - fails: as [`endpoints`] for the classifier; `UnsupportedType` for a
///   function or session endpoint, which has no constructor pattern to cover.
/// - panics: none.
///
/// # Errors
/// As `fails`.
///
/// # Adequacy
/// - hypothesis: L3 — a forward flow at a function code refuses as
///   `UnsupportedType`.
/// - witness: `flow_universe::tests::formation_boundaries_refuse`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |flow| matches!(arena.value_type(classifier), Some(&ValueType::FlowUniverse(..))) && arena.value_type(flow.source).is_some()))]
pub(crate) fn forward_type(
    arena: &TermArena,
    classifier: ValueTypeId,
    budget: ReplayBudget,
) -> Result<FlowType, FlowError>
{
    let (source, target) = universe_codes(arena, classifier)?;
    let mut allowance = Allowance(u64::from(budget));
    let source = coverage::code(arena, source, &mut allowance)?;
    let target = coverage::code(arena, target, &mut allowance)?;
    Ok(FlowType { source, target })
}

/// Decode a function flow's classifier: `Flow_U` between two function codes
/// over first-order codes.
///
/// # Specification
/// - ensures: both endpoints decode as function codes, source first.
/// - fails: as [`endpoints`] for the classifier; `UnsupportedCode` or
///   `UnsupportedType` for an endpoint that is no such function code.
/// - panics: none.
///
/// # Errors
/// As `fails`.
///
/// # Adequacy
/// - hypothesis: L3 — a function flow between first-order codes refuses.
/// - witness: `flow_universe::tests::function::constant_map_refusal_holds_at_a_thunk_code`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |&(source, target)| arena.value_type(source.code).is_some() && arena.value_type(target.code).is_some()))]
pub(crate) fn function_type(
    arena: &TermArena,
    classifier: ValueTypeId,
    budget: ReplayBudget,
) -> Result<(Arrow, Arrow), FlowError>
{
    let (source, target) = universe_codes(arena, classifier)?;
    let mut allowance = Allowance(u64::from(budget));
    let source = coverage::function(arena, source, &mut allowance)?;
    let target = coverage::function(arena, target, &mut allowance)?;
    Ok((source, target))
}

/// Which classifier a flow was read from.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Reading
{
    /// `Flow(A, x, y)`.
    Element,
    /// `Flow_U(x, y)`, whose carrier is the level-zero value universe.
    Universe,
}

/// A flow classifier's carrier and endpoints.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct Ends
{
    /// The type both endpoints inhabit.
    pub carrier: ValueTypeId,
    /// The source endpoint.
    pub source: ValueId,
    /// The target endpoint.
    pub target: ValueId,
    /// The classifier the ends were read from.
    pub reading: Reading,
}

/// Whether a type is the level-zero value universe.
///
/// # Specification
/// trivial.
pub(crate) fn level_zero_universe(
    arena: &TermArena,
    ty: ValueTypeId,
) -> Reading
{
    match arena.value_type(ty) {
        Some(&ValueType::Universe {
            sort: GroundSort::Value,
            ref level,
        }) if *level == Level::zero() => Reading::Universe,
        _ => Reading::Element,
    }
}

/// Read a flow classifier's carrier and endpoints.
///
/// # Specification
/// - ensures: `Flow(A, x, y)` reads as its parts; `Flow_U(x, y)` reads with the
///   level-zero value universe as its carrier.
/// - fails: `FamilyMismatch` for an identity classifier, `ExpectedFlow` for any
///   other.
/// - panics: none.
///
/// # Errors
/// As `fails`.
///
/// # Adequacy
/// - hypothesis: L3 — a ride along a universe path refuses by family.
/// - witness: `flow_universe::tests::path_and_flow_never_coerce`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |ends| arena.value_type(ends.carrier).is_some()))]
pub(crate) fn ends(
    arena: &mut TermArena,
    classifier: ValueTypeId,
) -> Result<Ends, FlowError>
{
    match arena.value_type(classifier) {
        Some(&ValueType::Flow {
            domain,
            source,
            target,
        }) => Ok(Ends {
            carrier: domain,
            source,
            target,
            reading: Reading::Element,
        }),
        Some(&ValueType::FlowUniverse(source, target)) => Ok(Ends {
            carrier: arena.value_type_universe(GroundSort::Value, Level::zero()),
            source,
            target,
            reading: Reading::Universe,
        }),
        Some(&(ValueType::Path { .. } | ValueType::PathUniverse(..))) => {
            Err(FlowError::FamilyMismatch {
                expected: Family::Flow,
                actual: Family::Path,
            })
        },
        _ => Err(FlowError::ExpectedFlow(classifier)),
    }
}

/// Read a flow classifier as a universe flow and decode its endpoints.
///
/// # Specification
/// - ensures: `Flow_U(x, y)` decodes as [`endpoints`]; `Flow(U₀, x, y)` at the
///   level-zero value universe decodes as `Flow_U(x, y)`.
/// - fails: `ExpectedFlow` for a flow at any other carrier, otherwise as
///   [`ends`] and [`endpoints`].
/// - panics: none.
///
/// # Errors
/// As `fails`.
///
/// # Adequacy
/// - hypothesis: L3 — a `stay` at a code serves as a function flow's boundary.
/// - witness: `flow_universe::tests::function::stay_at_a_thunk_code_collapses`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |flow| arena.value_type(flow.source).is_some() && arena.value_type(flow.target).is_some()))]
pub(crate) fn universe_reading(
    arena: &mut TermArena,
    classifier: ValueTypeId,
    budget: ReplayBudget,
) -> Result<FlowType, FlowError>
{
    let read = ends(arena, classifier)?;
    let universe = match read.reading {
        Reading::Universe => classifier,
        Reading::Element => match level_zero_universe(arena, read.carrier) {
            Reading::Universe => arena.value_type_flow_universe(read.source, read.target),
            Reading::Element => return Err(FlowError::ExpectedFlow(classifier)),
        },
    };
    endpoints(arena, universe, budget)
}

/// Whether two flow classifiers agree as the two readings of one classifier.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Agreement
{
    /// One is `Flow(U₀, x, y)` at the level-zero value universe, the other
    /// `Flow_U(x, y)`, between convertible endpoints.
    Agree,
    /// Anything else, which ordinary conversion decides.
    Differ,
}

/// Decide whether a synthesized flow classifier checks at an expected one by
/// the level-zero universe's two readings.
///
/// # Specification
/// - ensures: [`Agreement::Agree`] exactly when the two classifiers are read
///   from different formers, their carriers convert — so the element reading's
///   carrier is the level-zero value universe — and their endpoints convert
///   pairwise.
/// - provides: the checking machine's mode switch for flows; a flow consumed or
///   produced under one reading checks under the other, so the singleton row's
///   composition and a `Flow_U` certificate stated at `Flow(U₀, x, y)` keep
///   their types.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a forward flow checks at `Flow(U₀, a, b)` and a `stay`
///   composite at `Flow_U(a, a)`, and a flow at the reversed endpoints still
///   refuses.
/// - witness: `flow_universe::tests::stay_and_forward_admit_and_ride`
/// - witness: `flow_universe::tests::back_has_no_directed_reading`
#[spec(ensures: |ret| ret == Agreement::Differ || actual != expected)]
pub(crate) fn agree(
    arena: &mut TermArena,
    presentations: &crate::presented::Presentations,
    actual: ValueTypeId,
    expected: ValueTypeId,
) -> Agreement
{
    let (Ok(synthesized), Ok(wanted)) = (ends(arena, actual), ends(arena, expected))
    else {
        return Agreement::Differ;
    };
    let agrees = synthesized.reading != wanted.reading
        && convertible_value_types(arena, synthesized.carrier, wanted.carrier)
            == Convertibility::Convertible
        && convert_values(arena, presentations, synthesized.source, wanted.source)
            == Convertibility::Convertible
        && convert_values(arena, presentations, synthesized.target, wanted.target)
            == Convertibility::Convertible;
    if agrees {
        Agreement::Agree
    }
    else {
        Agreement::Differ
    }
}

/// Compose two flows' classifiers over a seam.
///
/// # Specification
/// - ensures: the carriers agree and the first flow's target converts with the
///   second's source; the composite runs from the first's source to the
///   second's target, as `Flow_U` when either side is read from `Flow_U` and as
///   `Flow` at the shared carrier otherwise.
/// - fails: `EndpointMismatch` for differing carriers or seam endpoints;
///   `Cycle` naming both occurrences for a feedback seam whose closing
///   endpoints also meet, `EndpointMismatch` for one whose closing endpoints do
///   not; as [`ends`] for a classifier that is no flow.
/// - panics: none.
///
/// # Errors
/// As `fails`.
///
/// # Adequacy
/// - hypothesis: L3 — injection then fold composes to an endomap, a reversed
///   seam and a feedback seam each refuse by name.
/// - witness: `flow_universe::tests::composition_preserves_direction_and_refuses_feedback`
#[spec(ensures: |ret| match ret {
    Ok(composite) => arena.value_type(composite).is_some(),
    Err(FlowError::Cycle { first, second }) => (first, second) == occurrences && seam == Seam::Feedback,
    Err(_) => true,
})]
pub(crate) fn compose(
    arena: &mut TermArena,
    presentations: &crate::presented::Presentations,
    (first, second): (ValueTypeId, ValueTypeId),
    seam: Seam,
    occurrences: (ValueId, ValueId),
) -> Result<ValueTypeId, FlowError>
{
    let left = ends(arena, first)?;
    let right = ends(arena, second)?;
    if convertible_value_types(arena, left.carrier, right.carrier) != Convertibility::Convertible
        || convert_values(arena, presentations, left.target, right.source)
            != Convertibility::Convertible
    {
        return Err(FlowError::EndpointMismatch);
    }
    if seam == Seam::Feedback {
        if convert_values(arena, presentations, right.target, left.source)
            != Convertibility::Convertible
        {
            return Err(FlowError::EndpointMismatch);
        }
        return Err(FlowError::Cycle {
            first: occurrences.0,
            second: occurrences.1,
        });
    }
    Ok(
        if left.reading == Reading::Universe || right.reading == Reading::Universe {
            arena.value_type_flow_universe(left.source, right.target)
        }
        else {
            arena.value_type_flow(left.carrier, left.source, right.target)
        },
    )
}

/// A constructor-pattern position in left-first, lexicographic order.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PatternPosition(pub usize);

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
    Path(crate::path_universe::PathError),
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
