//! Forward-only certificates over closed first-order, function and session
//! codes.
//!
//! Formation checks a closed translator and replays its action on every
//! constructor pattern with rigid Base leaves. Output patterns may rearrange,
//! duplicate or discard those leaves, but cannot manufacture or inspect them.
//! At a function code, formation orients two boundary flows by the variance
//! the arrow fixes and assembles the translator from them. `ride` replays the
//! forward action; `stay` returns its argument in one step. A session
//! introduction is a native `Value::SessionFlow` at a native `Flow_U`
//! classifier; it replays a finite simulation and has a recorded-run consumer
//! rather than a CBPV endpoint-value action. The other introductions are an
//! in-memory rule language, separate from native terms and from universe
//! paths. The rule syntax carries no admission receipt or reusable verdict.
//!
//! # The family
//!
//! This module defines the `Flow_U a b` family, separate from `Path_U`, over
//! quoted Base codes, products of any arity (the unit among them), sums of at
//! least one summand, function codes `U (A → F B)` whose argument and result
//! are among those, and finite session codes, which only a session simulation
//! relates. The empty sum is outside the vocabulary. A forward
//! certificate stores one closed CBPV translator and one proposed
//! image/dialogue per source constructor pattern. It carries neither an
//! inverse nor round-trip evidence. Every consuming formation checks the
//! translator in a fresh closed checker session, validates the images, and
//! replays kernel-built positive claims. No stored node or classifier is an
//! admission receipt.
//!
//! | Boundary | Rule or refusal |
//! | -------- | --------------- |
//! | Forward formation | Exhaustive symbolic source patterns; each target Base position selects a same-typed source leaf. |
//! | Directed computation | `ride e v` exposes the checked forward application for ordinary conversion replay. |
//! | Directed reflexivity | `ride (stay a) v` returns `v` in one step, without allocating or evaluating an identity translator. |
//! | Motive formation | Moving endpoints occur only covariantly; arrow domains and Flow sources reverse variance. |
//! | Symmetry | `Flow(Moving, Fixed)` returns `NonCovariantMotive`, including when nested beneath positive formers. |
//! | Family separation | A valid equivalence at a Flow boundary, or a Flow at a Path boundary, returns `FamilyMismatch`. |
//! | Sequential composition | `Compose { seam: Sequence, .. }` checks the intermediate type and lowers in order to CBPV bind. |
//! | Feedback | Connecting the second output back into the first input returns `Cycle` with both occurrences. |
//! | Function formation | `Function` forms `Flow_U (U (A → F B)) (U (A' → F B'))` from `Flow_U A' A` at the contravariant domain and `Flow_U B B'` at the covariant codomain; a boundary flow running the other way returns `Boundary`. |
//! | Function computation | `ride` runs the domain translator, then the function, then the codomain translator; `stay` at a function code returns its function in one step. |
//! | Function stock | `Forward` refuses function endpoints with `UnsupportedType`: a function has no constructor pattern to cover. |
//!
//! **Native family boundary.** `Certificate::Path` carries a native value id.
//! `form_certificate` synthesizes that value through the ordinary closed
//! checker and decodes its checked `Path_U` endpoints; there is no auxiliary
//! path arena or trusted classifier shortcut. Missing round-trip evidence and
//! non-path classifiers refuse. `Flow::Session` likewise carries a native
//! value id: formation synthesizes it, and [`endpoints`] decodes its checked
//! `Flow_U` classifier. Matching Path and Flow families retain separate
//! formation judgements, and both cross-family directions refuse before
//! elimination, whether the family is named by the certificate tag or by the
//! native classifier.
//!
//! **Native persistence.** `Flow_U` and the session simulation are native
//! formers with wire tags `0x48` and `0x49` in `gandr-kernel-term`'s table;
//! [`endpoints`] admits the whole `Flow_U` vocabulary at `0x48` — first-order,
//! function and session codes — so later persisted introductions share the
//! classifier. Directed reflexivity, forward translators, the arrow's action
//! and composition remain rule syntax, and `0x4A`–`0x4F` stay reserved. The
//! kernel error carries a classifier refusal as the flat [`ClassifierError`]:
//! a [`FlowError`] owns the kernel error of a translator's typing, so the
//! kernel error owning it back would make the two types own each other.
//!
//! **Leaf naturality.** Each source Base position is a distinct rigid
//! variable, including equal-typed positions in a product. Proposed output
//! syntax contains only canonical constructors and those correctly typed
//! variables. The kernel replays the translator on these symbolic inputs; a
//! trace generated at a literal sample has no authority over that obligation.
//! Literals nested beneath sums or products, fresh variables, wrong-typed
//! selections, and sample-only constant maps refuse. The witnesses cover
//! diagonals, both injections, codiagonals, product identity and terminal
//! projection to Unit. The native CBPV vocabulary has no general product
//! eliminator, so these witnesses do not establish generation of every
//! projection or fullness of the one-way alphabet.
//!
//! **The gate reads wiring.** Sequence has one edge between two occurrences;
//! feedback adds the reverse edge and closes a cycle. Equal endpoint codes do
//! not identify occurrences. In particular, injection followed by fold forms
//! and replays as identity, and terminal followed by injection forms a
//! constant Bool endomap. Neither composite grants inverse evidence. This
//! closed-code gate handles explicit two-occurrence seams, not a general
//! reflected cell-support graph or invertible-core comparison.
//!
//! # Directed funext
//!
//! **The arrow's action is the statement.** `Flow_U` at a function code is a
//! forward flow of results over a forward flow of arguments, the argument flow
//! running from the target's domain to the source's. Variance is data:
//! [`Boundary::variance`] is all the formation rule reads to orient a
//! boundary, and it is the reversal [`Motive::Arrow`] applies to a motive. No
//! modality, polarity-annotated context or internal hom object enters. The
//! statement binds no variable, since its boundaries are closed certificates,
//! so the divariant variable that keeps directed function extensionality out
//! of a polarity calculus does not arise (Jacob Neumann, *A Generalized
//! Algebraic Theory of Directed Equality*, doctoral thesis, University of
//! Nottingham, 2025, §0.2 and §4.4). Riding a flow through a function's
//! argument is the motive `Arrow(El(Moving), El(Fixed))`, which
//! [`check_motive`] refuses as it refuses symmetry: the argument boundary is
//! consumed only contravariantly, by this clause.
//!
//! **Leaves at a function code.** Both boundary flows are leaf-natural
//! certificates and the assembled translator only composes them with its
//! argument, so the translator manufactures no leaf: a constant result
//! boundary refuses as `NonNatural` before the function flow forms. The arrow
//! of two `stay`s rides a function to itself by conversion replay.
//!
//! **What the clause does not state.** A flow between two functions of one
//! first-order function code would relate their outputs pointwise over
//! related inputs. First-order elements carry only identities, so that
//! relation is element identity at the thunk code, which
//! [`crate::identity_recursion`] computes; this module adds nothing there. A
//! natural transformation between code-valued functions, where an argument
//! would occur at both variances, is outside the clause.
//!
//! # Decision
//!
//! **Choice.** The rule arena reuses native closed checking and conversion
//! replay. Flat, constructor-ordered ids and bounded iterative walks avoid
//! recursive ownership; formation and lowering tables live only for one call.
//! The function clause is structural: the kernel assembles its translator
//! from formed boundary flows, and it carries both endpoint codes so a
//! misdirected boundary refuses by name. Session simulations are native
//! persisted formers: the recorded reversal — declaration admission must
//! consume Flow syntax — fired on its stated trigger when session subtyping
//! became a declared `Flow_U` statement of the surface language, which must
//! admit, persist in an artifact and readmit by replay. The classifier is
//! generic over the `Flow_U` vocabulary so the next persisted introduction
//! reuses it, and the session introduction's frame is the session path's, so
//! the two certificates encode and replay alike. `FORMAT_VERSION` holds: both
//! bytes were reserved and unassigned, and an older reader refuses them by
//! name.
//! **Alternatives.** A second evaluator; host-language translators, which
//! would bypass the obligation; deciding session subtyping in the checker
//! alone, which would leave a declared `Flow_U` statement unpersisted and the
//! kernel out of its trust path; a session-specific classifier, which every
//! later introduction would have to duplicate. At function codes: forward
//! translators covered symbolically, which have no constructor pattern to
//! replay and would need leaf-naturality redefined for exponentials; a
//! classifier derived from the boundary flows alone, under which no direction
//! can be refused; and a polarity modality on contexts.
//! **Reversal.** The remaining introductions become native formers when a
//! declaration consumes them: at that point each takes a byte of the
//! reservation under the shared classifier. Motive checking is the
//! term-structural covariance side condition over El, Flow, Arrow, Sum and
//! Product; value transport uses `El(Moving)`. General dependent directed
//! elimination and the reflected variance calculus remain outside this rule
//! language. The function clause is revisited when an argument code is itself
//! a function or universe code, where an argument variable would occur at both
//! variances, or when a translator at function codes that is not the arrow of
//! two boundary flows must be certified.
//!
//! # Witnesses
//!
//! The eleven witnesses in this module's tests use the independent conversion
//! engine and exact expected outputs. The public replay boundary restores its
//! arena watermark on success and failure. Its memo discipline is the memo's
//! six-condition discipline: no caller-supplied checker memo, persistent
//! verdict, storage policy or authority-bearing hit. A standalone mutation
//! campaign belongs over leaf aliasing and type confusion, manufactured
//! constants, omitted source coverage, forged dialogues, reversed
//! composition, missed feedback, motive sign propagation, family coercion,
//! Stay reduction, boundary orientation and boundary order in lowering; no
//! campaign or score is claimed.
use alloc::boxed::Box;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
use gandr_kernel_term::ComputationId;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::Value;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueType;
use gandr_kernel_term::ValueTypeId;

use crate::error::KernelError;
use crate::path_universe::Dialogue;
use crate::replay::KernelVerdict;
use crate::replay::ReplayBudget;

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
///   refuses; a function flow forms from two boundary flows.
/// - witness: `flow_universe::tests::terminal_ride_and_stay_compute`
/// - witness: `flow_universe::tests::composition_preserves_direction_and_refuses_feedback`
/// - witness: `flow_universe::tests::function::directed_funext_forms_and_rides_in_variance_order`
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Flow
{
    /// A finite session simulation: a native [`Value::SessionFlow`], checked
    /// afresh at its ordinary `Flow_U` classifier.
    Session(ValueId),
    /// Directed reflexivity at a quoted closed first-order or function code.
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
    /// The arrow's action at a function code `U (A → F B)` over first-order
    /// codes: a forward flow of results over a forward flow of arguments,
    /// each boundary running in the direction its variance fixes.
    Function
    {
        /// Quoted source function code `U (A → F B)`.
        source: ValueId,
        /// Quoted target function code `U (A' → F B')`.
        target: ValueId,
        /// The contravariant argument boundary, `Flow_U A' A`.
        domain: FlowId,
        /// The covariant result boundary, `Flow_U B B'`.
        codomain: FlowId,
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
/// - executable: none — a position carries no behavior; formation reads its
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
    /// The variance the arrow fixes at this boundary, as [`Motive::Arrow`]
    /// reads it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn variance(self) -> Variance
    {
        match self {
            | Self::Domain => Variance::Contravariant,
            | Self::Codomain => Variance::Covariant,
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
    /// - hypothesis: L3 — composition and function introductions resolve each
    ///   child and retain their order.
    /// - witness: `flow_universe::tests::composition_preserves_direction_and_refuses_feedback`
    /// - witness: `flow_universe::tests::function::directed_funext_forms_and_rides_in_variance_order`
    #[spec(
        captures: before = self.0.len(),
        ensures: |ret| match ret {
            Ok(id) => id.0 == before && self.0.len() == before.saturating_add(1)
                && match self.0.get(id.0) {
                    Some(&Flow::Compose { first: a, second: b, .. } | &Flow::Function { domain: a, codomain: b, .. }) => a.0 < id.0 && b.0 < id.0,
                    Some(_) => true,
                    None => false,
                },
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
        if let Flow::Compose { first, second, .. }
        | Flow::Function {
            domain: first,
            codomain: second,
            ..
        } = flow
        {
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
    #[inline]
    pub fn get(
        &self,
        id: FlowId,
    ) -> Result<&Flow, FlowError>
    {
        self.0.get(id.0).ok_or(FlowError::UnknownFlow(id))
    }
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
/// - hypothesis: L3 — session endpoints decode; a session flow tagged as a path
///   and a session path tagged as a flow each refuse as `FamilyMismatch`; a
///   List endpoint refuses.
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
    let (source, target) = match arena.value_type(classifier) {
        | Some(&ValueType::FlowUniverse(source, target)) => (source, target),
        | Some(&ValueType::PathUniverse(..)) => {
            return Err(FlowError::FamilyMismatch {
                expected: Family::Flow,
                actual: Family::Path,
            });
        },
        | _ => return Err(FlowError::ExpectedFlow(classifier)),
    };
    let mut allowance = Allowance(u64::from(budget));
    let source = coverage::vocabulary(arena, source, &mut allowance, budget)?;
    let target = coverage::vocabulary(arena, target, &mut allowance, budget)?;
    Ok(FlowType { source, target })
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
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum FlowError
{
    /// A finite session simulation failed replay.
    Session(crate::session::SessionError),
    /// Session codes transport recorded runs, not native endpoint values.
    RecordedRunRequired,
    /// A native classifier is not `Flow_U`.
    ExpectedFlow(ValueTypeId),
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
    /// A function code's boundary flow does not run in the direction its
    /// variance fixes.
    Boundary(Boundary),
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
            | &Self::Session(ref error) => error.fmt(f),
            | &Self::RecordedRunRequired => {
                f.write_str("session transport requires a recorded run")
            },
            | &Self::ExpectedFlow(_) => f.write_str("expected a universe-flow classifier"),
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
            | &Self::Boundary(Boundary::Domain) => {
                f.write_str("the domain boundary flow must run contravariantly")
            },
            | &Self::Boundary(Boundary::Codomain) => {
                f.write_str("the codomain boundary flow must run covariantly")
            },
            | &Self::UnknownMotive(_) => f.write_str("unknown directed motive"),
            | &Self::Budget => f.write_str("universe-flow budget exhausted"),
            | &Self::Path(ref error) => write!(f, "universe-path formation: {error}"),
        }
    }
}

impl core::error::Error for FlowError
{
}

/// A native `Flow_U` classifier's refusal, as the kernel's own error carries
/// it.
///
/// A [`FlowError`] owns the [`KernelError`] of a translator's typing, so the
/// kernel error owns this flat projection instead: a typing, path or session
/// refusal keeps the kernel's own name, and the classifier's names stay here.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ClassifierError
{
    /// No coercion crosses the family boundary.
    FamilyMismatch
    {
        /// Required classifier family.
        expected: Family,
        /// Supplied classifier family.
        actual: Family,
    },
    /// A native classifier is not `Flow_U`.
    ExpectedFlow(ValueTypeId),
    /// An endpoint is not a quoted code of the `Flow_U` vocabulary.
    UnsupportedCode(ValueId),
    /// A code contains a former outside the `Flow_U` vocabulary.
    UnsupportedType(ValueTypeId),
    /// The code walk's allowance ran out.
    Budget,
}

impl fmt::Display for ClassifierError
{
    /// Display the named refusal as [`FlowError`] spells it.
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
            | Self::FamilyMismatch {
                expected: Family::Flow,
                ..
            } => f.write_str("expected Flow, found Path"),
            | Self::FamilyMismatch {
                expected: Family::Path,
                ..
            } => f.write_str("expected Path, found Flow"),
            | Self::ExpectedFlow(_) => f.write_str("expected a universe-flow classifier"),
            | Self::UnsupportedCode(_) => f.write_str("unsupported universe-flow code"),
            | Self::UnsupportedType(_) => f.write_str("unsupported universe-flow type"),
            | Self::Budget => f.write_str("universe-flow budget exhausted"),
        }
    }
}

impl core::error::Error for ClassifierError
{
}

/// The kernel's refusal for a `Flow_U` classifier [`endpoints`] refused.
///
/// # Specification
/// - ensures: a classifier refusal keeps its name under `KernelError::Flow`; a
///   typing, path or session refusal is the kernel's own; every other flow
///   refusal, which [`endpoints`] never returns, is `ArenaFault`.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a session flow forged at a `Path_U` classifier and a List
///   endpoint each keep their classifier refusal's name.
/// - witness: `session::tests::session_flows_persist_and_refuse_by_family`
#[spec(captures: family = matches!(error, FlowError::FamilyMismatch { .. }),
    ensures: |ret| !family || matches!(ret, KernelError::Flow(ClassifierError::FamilyMismatch { .. })))]
pub(crate) fn classifier_refusal(error: FlowError) -> KernelError
{
    let refusal = match error {
        | FlowError::FamilyMismatch { expected, actual } => {
            ClassifierError::FamilyMismatch { expected, actual }
        },
        | FlowError::ExpectedFlow(classifier) => ClassifierError::ExpectedFlow(classifier),
        | FlowError::UnsupportedCode(code) => ClassifierError::UnsupportedCode(code),
        | FlowError::UnsupportedType(ty) => ClassifierError::UnsupportedType(ty),
        | FlowError::Budget => ClassifierError::Budget,
        | FlowError::Typing(error) => return *error,
        | FlowError::Path(error) => return KernelError::Path(error),
        | FlowError::Session(error) => return KernelError::Session(error),
        | FlowError::RecordedRunRequired
        | FlowError::UnknownFlow(_)
        | FlowError::Arena
        | FlowError::Coverage
        | FlowError::NonNatural(_)
        | FlowError::ForwardReplay { .. }
        | FlowError::EndpointMismatch
        | FlowError::Cycle { .. }
        | FlowError::NonCovariantMotive(_)
        | FlowError::Boundary(_)
        | FlowError::UnknownMotive(_) => return KernelError::ArenaFault,
    };
    KernelError::Flow(refusal)
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
