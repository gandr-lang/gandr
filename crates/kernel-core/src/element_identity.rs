//! Element identity as kernel syntax: the identity type `Path(A, a, b)`, its
//! reflexivity `here(a)`, transport in a dependent motive, the guarded higher
//! field, higher evaluation and related application.
//!
//! Every judgement here reads the one identity fold in
//! [`crate::identity_recursion`]; this module adds no clause of its own. It
//! computes the fibre a persisted identity denotes, turns the evidence a
//! persisted node carries into goals for the checking machine, and supplies the
//! replay's reductions.
//!
//! # Decisions
//!
//! **Identity is one former whose fibre is computed.** At a closed type `A`,
//! `Path(A, a, b)` reads the fold at the quoted `A` and the two endpoints: Unit
//! is Unit; a Sum is Empty across injections and the summand's fibre within
//! one; a Product pairs its coordinates' fibres; a Base is discrete equality;
//! the level-zero universe is the native path classifier `Path_U(a, b)`; a pure
//! thunk code relates functions by related application. An introduction form
//! other than `here` inhabits the identity when it inhabits that native fibre.
//! `here(c)` is the one introduction the fold does not supply, and it checks by
//! the kernel's own conversion: `c` must convert with both endpoints, and a
//! refusal names both endpoints by content digest. An iterated identity reads
//! its inner identity's fibre first and treats a `here` endpoint as that
//! fibre's diagonal evidence. A neutral, a variable or a constant, inhabits an
//! identity by the type it synthesizes: conversion stays structural, so a
//! neutral of the fibre type does not inhabit the identity. `here(c)`
//! synthesizes the diagonal at the type `c` synthesizes, so like every
//! annotation-free introduction it is inferable only where its point is; an
//! eliminator whose path is the `here` of an injection or a λ takes it through
//! a binder or a constant.
//!
//! - alternatives: an inductive identity family eliminated by J, which needs a
//!   computation rule on reflexivity that the fold's Sum and universe fibres do
//!   not supply without a second equality; identity as a producer-chosen
//!   relation, which hands fibre selection to an untrusted party.
//! - reversal: a type the fold does not cover (dependent arrows, quantified
//!   functions) needs a fold clause first; the evidence tags `0x3A` and `0x3B`
//!   are reserved by name for its quantified and dependent evaluations.
//!
//! **Identity at an open type is a neutral fibre.** A domain that mentions a
//! bound variable or reaches a sealed atom has no fold clause: its fibre would
//! depend on a neutral or on a hidden representation, so the identity stays
//! the type `Path(A, a, b)` itself, as a higher observational type theory
//! leaves the identity of a neutral type. It forms wherever its domain and
//! endpoints do; `here(c)` synthesizes and checks at it by the same endpoint
//! conversion as at a closed domain; transport along it is stuck except on
//! `here`, where the first row of the table below reduces it; two such
//! identities convert structurally, childwise. An introduction that needs the
//! fold, native evidence, a higher field or a higher evaluation, refuses there
//! as [`IdentityError::NeutralFibre`], the refusal a neutral fibre at a closed
//! domain already gives. No wire node is needed: the neutral fibre is the
//! persisted `Path` node over an open domain, so `0x3A` stays reserved for the
//! quantified evaluation alone.
//!
//! - alternatives: refusing identity at formation and at `here`'s synthesis,
//!   which left every law over an abstract carrier unstatable; refusing it at
//!   the bridge, which let a `here` inside a body reach the kernel and fault.
//! - reversal: a fold clause for type variables (parametricity), or the
//!   interface a sealed atom declares, computes the fibre where this leaves it
//!   neutral; neither removes a rule stated here.
//!
//! **The checking machine never re-enters itself.** Every value the fold would
//! check, a guard's evidence or a higher evaluation's returned values and
//! output evidence, becomes a goal on the machine's own stack. The fold is read
//! through its unchecked evaluators, and the universe diagonal reuses the
//! universe codes the machine already formed. A guard's fibre is computed from
//! the previous guard's evidence before that evidence's goal is discharged;
//! the computation is total and deterministic, and acceptance needs every goal,
//! so an ill-typed index refuses at its own goal.
//!
//! **Transport computes by replay.** The motive is a value type under one
//! value binder. Transport's input checks at the motive instantiated at the
//! source endpoint and its result is a returner of the motive at the target;
//! instantiation is the rewrite machine's capture-avoiding substitution, so the
//! substitution law holds of every motive. `J` is transport in the singleton
//! family `x ↦ Path(A, a, x)`, so it needs no former of its own; its
//! computation on `here` is the first row below and its unit law the last. The
//! replay reduces:
//!
//! | path or motive                      | reduct                                     |
//! | ----------------------------------- | ------------------------------------------ |
//! | the path is `here(_)`               | `return v`                                 |
//! | the motive ignores its binder       | `return v`                                 |
//! | a Product motive at a tuple         | each component transported, then the tuple |
//! | a Sum motive at an injection        | the injection of the summand's transport   |
//! | `El(x)` at level zero               | native universe transport                  |
//! | `Path(D, l, x)` at a `here` value   | `return p`                                 |
//!
//! Anything else stays neutral. The checker's conversion is structural and
//! compares a stuck transport childwise; the replay refuses one as unreadable,
//! since its trace alphabet has no transport elimination.
//!
//! - alternatives: transport reduced inside the checker's conversion, which
//!   would make conversion search; a motive under a code binder, which would
//!   need a second universe walk for every reduction.
//! - reversal: a trace decision that compares neutral transports would let the
//!   replay certify them instead of refusing.
//!
//! **Higher fields replay to a finite depth.** `Higher` is a guarded program
//! whose layers expose evidence or redirect. Its check walks the program from
//! the identity of the two given identities, each guard owing evidence at the
//! fibre of the previous goal, through exactly the program's depth; an
//! unguarded cycle is refused as [`IdentityError::NonProductive`],
//! "non-productive higher field". An unobserved tail is not certified.
//! [`higher_codata`] reads a persisted field back as the program
//! [`crate::higher_field`]'s observations take, so square symmetry computes
//! from persisted evidence.
//!
//! **Related application eliminates function identity.** Given `p` relating
//! `f` and `g`, two arguments and evidence relating them, its body runs under
//! the two results and an identity between them. It computes when `p` is
//! `here(f)` and the arguments convert: the body sees one result twice and its
//! reflexivity. A higher evaluation is the function clause's introduction; its
//! check replays every component's dialogues over the kernel-generated
//! coverage. Its elimination stays neutral, because the application site
//! carries no pointwise evaluation; the fold's own reading of that case is
//! [`crate::identity_recursion::Application::Suspended`].
//!
//! **The bridge reading stays in memory.**
//! [`crate::identity_recursion::Mode::Bridge`] has no persisted node: a bridge
//! relation is a reading of the fold for producers, not a kernel judgement, and
//! nothing here forms one.

use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
use gandr_kernel_check_memo::CheckMemo;
use gandr_kernel_check_memo::ContentDigest;
use gandr_kernel_strata::Level;
use gandr_kernel_term::AnyNode;
use gandr_kernel_term::ComputationId;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::EvaluationComponent;
use gandr_kernel_term::EvaluationDialogues;
use gandr_kernel_term::HigherLayer;
use gandr_kernel_term::HigherProgram;
use gandr_kernel_term::LayerPosition;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::Value;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueType;
use gandr_kernel_term::ValueTypeId;

use crate::conv::Convertibility;
use crate::conv::equal_values;
use crate::encoding::ContentTable;
use crate::encoding::content_digest;
use crate::error::ExpectedValueShape;
use crate::error::KernelError;
use crate::error::ValueTypeWitness;
use crate::higher_field::Codata;
use crate::higher_field::Depth;
use crate::higher_field::Goal;
use crate::higher_field::HigherError;
use crate::higher_field::HigherId;
use crate::higher_field::Layer;
use crate::higher_field::ObservationBudget;
use crate::identity_recursion::Component;
use crate::identity_recursion::ComponentObligation;
use crate::identity_recursion::Domain;
use crate::identity_recursion::Evaluation;
use crate::identity_recursion::EvaluationSide;
use crate::identity_recursion::Fibers;
use crate::identity_recursion::HigherEvaluation;
use crate::identity_recursion::Interpretation;
use crate::identity_recursion::Mode;
use crate::identity_recursion::Pointwise;
use crate::identity_recursion::RelationError;
use crate::identity_recursion::interpret;
use crate::path_universe::Dialogue;
use crate::path_universe::Reduction;
use crate::path_universe::anchor;
use crate::replay::KernelVerdict;
use crate::replay::ReplayBudget;
use crate::rewrite::BinderDepth;
use crate::rewrite::RewriteOutcome;
use crate::rewrite::RewriteSupport;
use crate::rewrite::shift_value;
use crate::rewrite::shift_value_type;
use crate::rewrite::substitute_computation;
use crate::rewrite::substitute_value;
use crate::rewrite::substitute_value_type;
use crate::support::LooseDepths;
use crate::witness::value_type_witness;

#[cfg(test)]
mod tests;

/// A refusal of the element-identity rules.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum IdentityError
{
    /// The domain is closed but has no clause in the identity fold.
    OutsideFold(ValueTypeWitness),
    /// A reflexivity's point does not convert with both endpoints.
    EndpointsDiffer
    {
        /// The source endpoint's content digest.
        left: ContentDigest,
        /// The target endpoint's content digest.
        right: ContentDigest,
    },
    /// The fibre is neutral: the domain is open, or the endpoints are not
    /// canonical, so no introduction but `here` inhabits it.
    NeutralFibre,
    /// The fibre is empty, so it has no diagonal evidence.
    EmptyFibre,
    /// An identity of universe paths is observed only through a higher field.
    HigherFieldRequired,
    /// An identity of functions is introduced only by a higher evaluation.
    HigherEvaluationRequired,
    /// A list identity needs a guarded observation.
    RecursiveObservation,
    /// A universe identity between distinct codes needs certificate evidence.
    CertificateOperation,
    /// Endpoints of an identity operation do not share a boundary.
    Boundary,
    /// A higher field requests no layer.
    ZeroDepth,
    /// A higher field reached an unguarded cycle at this layer.
    NonProductive(LayerPosition),
    /// A higher field exhausted its instruction allowance.
    DepthBound,
    /// A higher field names a layer it does not have.
    UnknownLayer(LayerPosition),
    /// A higher field's evidence count differs from its guard count.
    GuardEvidence,
    /// A higher evaluation's component count differs from its coverage.
    Coverage,
    /// Coverage generation exhausted its allowance.
    CoverageBudget,
    /// A higher evaluation's dialogue did not certify its returned value.
    Evaluation
    {
        /// The component, in coverage order.
        component: Component,
        /// The function whose evaluation failed.
        side: EvaluationSide,
        /// The replay's verdict.
        verdict: KernelVerdict,
    },
    /// A higher evaluation relates functions that mention bound variables.
    OpenFunctions,
}

impl fmt::Display for IdentityError
{
    /// Name the refusal class.
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
            | Self::OutsideFold(_) => f.write_str("identity at a type outside the identity fold"),
            | Self::EndpointsDiffer { .. } => {
                f.write_str("reflexivity between differing endpoints")
            },
            | Self::NeutralFibre => f.write_str("an identity fibre is neutral"),
            | Self::EmptyFibre => f.write_str("an identity fibre is empty"),
            | Self::HigherFieldRequired => {
                f.write_str("an identity of universe paths needs a higher field")
            },
            | Self::HigherEvaluationRequired => {
                f.write_str("an identity of functions needs a higher evaluation")
            },
            | Self::RecursiveObservation => {
                f.write_str("a list identity needs a guarded observation")
            },
            | Self::CertificateOperation => {
                f.write_str("a universe identity needs certificate evidence")
            },
            | Self::Boundary => f.write_str("identity endpoints do not share a boundary"),
            | Self::ZeroDepth => f.write_str("a higher field requests no layer"),
            | Self::NonProductive(_) => f.write_str("non-productive higher field"),
            | Self::DepthBound => f.write_str("a higher field exhausted its allowance"),
            | Self::UnknownLayer(_) => f.write_str("a higher field names an absent layer"),
            | Self::GuardEvidence => {
                f.write_str("a higher field's evidence does not match its guards")
            },
            | Self::Coverage => f.write_str("a higher evaluation does not match its coverage"),
            | Self::CoverageBudget => {
                f.write_str("higher-evaluation coverage exhausted its allowance")
            },
            | Self::Evaluation { .. } => {
                f.write_str("a higher evaluation's dialogue did not replay")
            },
            | Self::OpenFunctions => f.write_str("a higher evaluation relates open functions"),
        }
    }
}

impl core::error::Error for IdentityError
{
}

/// Require a domain the identity fold reads: closed and reaching no sealed
/// atom.
///
/// # Specification
/// - requires: nothing.
/// - ensures: success exactly when the domain mentions no bound variable and
///   reaches no sealed atom.
/// - provides: the guard every reading of the fold shares; at an open domain
///   the identity is its own neutral fibre, which no fold introduction
///   inhabits.
/// - fails: [`IdentityError::NeutralFibre`] at an open domain; `ArenaFault` for
///   a domain the arena does not hold.
/// - panics: none.
///
/// # Errors
/// As `fails`.
///
/// # Adequacy
/// - hypothesis: L3 — native evidence at the decode of a variable code and at a
///   sealed atom refuses as a neutral fibre, while the same evidence at a
///   closed Bool checks.
/// - witness: `element_identity::tests::identity_at_an_open_type_is_a_neutral_fibre`
#[spec(ensures: |ret| ret.as_ref().map_or_else(
    |error| matches!(error, &(KernelError::Identity(IdentityError::NeutralFibre) | KernelError::ArenaFault)),
    |&()| arena.value_type(domain).is_some()))]
fn require_folded(
    arena: &TermArena,
    domain: ValueTypeId,
) -> Result<(), KernelError>
{
    if arena.value_type(domain).is_none() {
        return Err(KernelError::ArenaFault);
    }
    let reach = u32::from(LooseDepths::new().value_type_reach(arena, domain));
    if reach != 0 || !crate::env::projected_atoms(arena, domain).is_empty() {
        return Err(KernelError::Identity(IdentityError::NeutralFibre));
    }
    Ok(())
}

/// The refusal for a reflexivity whose point does not reach both endpoints.
///
/// # Specification
/// trivial.
#[must_use]
pub(crate) fn endpoints_differ(
    arena: &TermArena,
    left: ValueId,
    right: ValueId,
) -> KernelError
{
    KernelError::Identity(IdentityError::EndpointsDiffer {
        left: content_digest(arena, AnyNode::Value(left)),
        right: content_digest(arena, AnyNode::Value(right)),
    })
}

/// The native type an identity's non-diagonal evidence inhabits.
///
/// # Specification
/// - requires: both endpoints inhabit the domain; the checking machine
///   discharges those goals itself.
/// - ensures: the fold's native fibre at the domain and endpoints. A domain
///   that is itself an identity reads its own fibre first, innermost out, and a
///   `here` endpoint stands for that fibre's diagonal evidence.
/// - provides: the type the checking machine redirects native evidence to.
/// - fails: an identity refusal for a domain outside the fold, a neutral fibre
///   (an open innermost domain, or endpoints that are not canonical), an empty
///   fibre, or a fibre that needs a higher form.
/// - panics: none.
///
/// # Errors
/// As `fails`, and `ArenaFault` on an unreadable node.
///
/// # Termination
/// - reason: two `while` loops over the finite chain of nested identity
///   domains, not recursion.
/// - measure: the chain length, which the first loop records and the second
///   consumes.
///
/// # Adequacy
/// - hypothesis: L3 — a product of Bool and Unit pairs its fibres, a universe
///   identity is a native path classifier, an iterated identity at a diagonal
///   is the unit fibre's identity, and an open domain is a neutral fibre.
/// - witness: `element_identity::tests::native_evidence_checks_against_the_fold_fibre`
/// - witness: `element_identity::tests::identity_at_an_open_type_is_a_neutral_fibre`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |&fibre| arena.value_type(fibre).is_some()))]
pub(crate) fn fibre(
    arena: &mut TermArena,
    domain: ValueTypeId,
    left: ValueId,
    right: ValueId,
) -> Result<ValueTypeId, KernelError>
{
    native_fibre(arena, domain, left, right).map(|(fibre, _fibers)| fibre)
}

/// The native fibre and the fibre graph it was read from.
///
/// # Specification
/// - requires: as [`fibre`].
/// - ensures: as [`fibre`], also returning the graph whose diagonal an
///   enclosing identity reads.
/// - fails: as [`fibre`].
/// - panics: none.
///
/// # Errors
/// As [`fibre`].
///
/// # Termination
/// - reason: as [`fibre`].
/// - measure: as [`fibre`].
///
/// # Adequacy
/// - hypothesis: L3 — as [`fibre`].
/// - witness: `element_identity::tests::a_higher_field_checks_and_computes_square_symmetry`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |&(fibre, _)| arena.value_type(fibre).is_some()))]
fn native_fibre(
    arena: &mut TermArena,
    domain: ValueTypeId,
    left: ValueId,
    right: ValueId,
) -> Result<(ValueTypeId, Fibers), KernelError>
{
    let mut enclosing = Vec::new();
    let mut base = (domain, left, right);
    while let Some(&ValueType::Path {
        domain,
        left,
        right,
    }) = arena.value_type(base.0)
    {
        enclosing.push((base.1, base.2));
        base = (domain, left, right);
    }
    require_folded(arena, base.0)?;
    let (mut fibre, mut fibers) = fold_fibre(arena, base)?;
    while let Some((left, right)) = enclosing.pop() {
        let left = diagonal_endpoint(arena, &fibers, left)?;
        let right = diagonal_endpoint(arena, &fibers, right)?;
        (fibre, fibers) = fold_fibre(arena, (fibre, left, right))?;
    }
    Ok((fibre, fibers))
}

/// Read the fold at one closed, non-identity domain.
///
/// # Specification
/// - requires: the endpoints inhabit the domain.
/// - ensures: the native fibre and its graph.
/// - fails: as [`fibre`].
/// - panics: none.
///
/// # Errors
/// As [`fibre`].
///
/// # Adequacy
/// - hypothesis: L3 — as [`fibre`].
/// - witness: `element_identity::tests::native_evidence_checks_against_the_fold_fibre`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |&(fibre, _)| arena.value_type(fibre).is_some()))]
fn fold_fibre(
    arena: &mut TermArena,
    (domain, left, right): (ValueTypeId, ValueId, ValueId),
) -> Result<(ValueTypeId, Fibers), KernelError>
{
    let code = arena.value_quote(domain);
    let fibers = interpret(arena, Mode::Identity, Domain::Elements(code))
        .and_then(Interpretation::elements)
        .and_then(|relation| relation.evaluate(arena, left, right))
        .map_err(|error| relation_refusal(arena, error))?;
    let fibre = fibers
        .native(arena)
        .map_err(|error| relation_refusal(arena, error))?;
    Ok((fibre, fibers))
}

/// Read a `here` endpoint as the diagonal evidence of the fibre it stands in.
///
/// # Specification
/// - requires: `fibers` is the fibre graph of the identity `endpoint` inhabits.
/// - ensures: a `here` endpoint becomes that graph's diagonal evidence; any
///   other endpoint is returned unchanged.
/// - fails: an identity refusal when the graph has no diagonal.
/// - panics: none.
///
/// # Errors
/// As `fails`, and `ArenaFault` on an unreadable endpoint.
///
/// # Adequacy
/// - hypothesis: L3 — the identity of `here(true)` with itself at Bool reads
///   the unit fibre's diagonal.
/// - witness: `element_identity::tests::a_higher_field_checks_and_computes_square_symmetry`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |&value| arena.value(value).is_some()))]
fn diagonal_endpoint(
    arena: &mut TermArena,
    fibers: &Fibers,
    endpoint: ValueId,
) -> Result<ValueId, KernelError>
{
    match arena.value(endpoint) {
        | Some(&Value::Here(_)) => fibers
            .diagonal(arena)
            .map(|diagonal| diagonal.value)
            .map_err(|error| relation_refusal(arena, error)),
        | Some(_) => Ok(endpoint),
        | None => Err(KernelError::ArenaFault),
    }
}

/// The goals a persisted higher field owes, one per guard, in walk order.
///
/// # Specification
/// - requires: `expected` is an identity of identities whose endpoints the
///   checking machine has formed.
/// - ensures: each guard's evidence paired with the native fibre it must
///   inhabit. The walk starts at identity of the two given identities and runs
///   exactly the program's depth; every later goal observes the previous
///   guard's evidence against itself.
/// - provides: the checking machine's reading of a higher field, with no nested
///   check.
/// - fails: a shape mismatch when `expected` is not an identity of identities;
///   the walk's refusals by name.
/// - panics: none.
///
/// # Errors
/// As `fails`, and `ArenaFault` on an unreadable node.
///
/// # Adequacy
/// - hypothesis: L3 — a productive square over Bool checks; a redirect cycle
///   refuses as non-productive at its layer.
/// - witness: `element_identity::tests::a_higher_field_checks_and_computes_square_symmetry`
/// - witness: `element_identity::tests::a_non_productive_higher_field_is_refused_by_name`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |owed| u64::try_from(owed.len()).is_ok_and(|owed| owed == u64::from(program.depth.0))))]
pub(crate) fn higher_obligations(
    arena: &mut TermArena,
    expected: ValueTypeId,
    program: &HigherProgram,
    evidence: &[ValueId],
) -> Result<Vec<(ValueId, ValueTypeId)>, KernelError>
{
    let (inner, left, right) = path_parts(arena, expected)?;
    let (base, base_left, base_right) = path_parts(arena, inner)?;
    let (fibre, fibers) = native_fibre(arena, base, base_left, base_right)?;
    let left = diagonal_endpoint(arena, &fibers, left)?;
    let right = diagonal_endpoint(arena, &fibers, right)?;
    let codata = higher_codata(program, evidence)?;
    let start = Goal {
        code: arena.value_quote(fibre),
        left,
        right,
    };
    let budget = ObservationBudget {
        depth: Depth(program.depth.0),
        replay: ReplayBudget::DEFAULT,
    };
    let mut owed = Vec::new();
    codata
        .walk(arena, start, budget, |_arena, cell, fibre| {
            owed.push((cell.evidence, fibre));
            Ok(())
        })
        .map_err(|error| higher_refusal(arena, error))?;
    Ok(owed)
}

/// Read a persisted higher field as the in-memory guarded program.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one in-memory layer per persisted layer, in order, each guard
///   carrying the next evidence value in layer order; the root and every target
///   keep their positions.
/// - provides: the persisted field's reading for [`crate::higher_field`]'s
///   observations, such as square symmetry.
/// - fails: [`IdentityError::GuardEvidence`] when the evidence count differs
///   from the guard count.
/// - panics: none.
///
/// # Errors
/// As `fails`, and `ArenaFault` for a position past the address space.
///
/// # Adequacy
/// - hypothesis: L3 — the persisted square over Bool reads back as a program
///   whose symmetry computes.
/// - witness: `element_identity::tests::a_higher_field_checks_and_computes_square_symmetry`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |codata| codata.nodes.len() == program.layers.len()))]
#[inline]
pub fn higher_codata(
    program: &HigherProgram,
    evidence: &[ValueId],
) -> Result<Codata, KernelError>
{
    let mut guards = evidence.iter().copied();
    let mut nodes = Vec::with_capacity(program.layers.len());
    for layer in &program.layers {
        nodes.push(match *layer {
            | HigherLayer::Guard { tail } => Layer::Guard {
                evidence: guards
                    .next()
                    .ok_or(KernelError::Identity(IdentityError::GuardEvidence))?,
                tail: higher_id(tail)?,
            },
            | HigherLayer::Redirect(target) => Layer::Redirect(higher_id(target)?),
        });
    }
    if guards.next().is_some() {
        return Err(KernelError::Identity(IdentityError::GuardEvidence));
    }
    Ok(Codata {
        nodes,
        root: higher_id(program.root)?,
    })
}

/// The in-memory address of a persisted layer position.
///
/// # Specification
/// trivial.
fn higher_id(position: LayerPosition) -> Result<HigherId, KernelError>
{
    usize::try_from(position.0)
        .map(HigherId)
        .map_err(|_overflow| KernelError::ArenaFault)
}

/// The goals a persisted higher evaluation owes, grouped by component.
///
/// # Specification
/// - requires: `expected` is the identity the evaluation is checked against.
/// - ensures: one obligation per kernel-generated coverage pattern, after every
///   component's two dialogues replayed positively.
/// - provides: the checking machine's reading of a higher evaluation, with no
///   nested check.
/// - fails: a shape mismatch when `expected` is not an identity; a neutral
///   fibre at an open domain; open functions, coverage and replay refusals by
///   name.
/// - panics: none.
///
/// # Errors
/// As `fails`, and `ArenaFault` on an unreadable node.
///
/// # Adequacy
/// - hypothesis: L1/L3 — `not ∘ not` and the identity on Bool relate through
///   both branches; a wrong component count refuses as coverage.
/// - witness: `element_identity::tests::a_higher_evaluation_proves_function_extensionality`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |owed| owed.len() == components.len()))]
pub(crate) fn evaluation_obligations(
    arena: &mut TermArena,
    expected: ValueTypeId,
    dialogues: &[EvaluationDialogues],
    components: &[EvaluationComponent],
) -> Result<Vec<ComponentObligation>, KernelError>
{
    let (domain, left, right) = path_parts(arena, expected)?;
    require_folded(arena, domain)?;
    let mut reach = LooseDepths::new();
    if u32::from(reach.value_reach(arena, left)) != 0
        || u32::from(reach.value_reach(arena, right)) != 0
    {
        return Err(KernelError::Identity(IdentityError::OpenFunctions));
    }
    if dialogues.len() != components.len() {
        return Err(KernelError::Identity(IdentityError::Coverage));
    }
    let mut pointwise = Vec::with_capacity(components.len());
    for (dialogue, component) in dialogues.iter().zip(components) {
        pointwise.push(Pointwise::Return {
            left: Evaluation {
                value: component.left,
                dialogue: Dialogue(dialogue.left.iter().copied().map(anchor).collect()),
            },
            right: Evaluation {
                value: component.right,
                dialogue: Dialogue(dialogue.right.iter().copied().map(anchor).collect()),
            },
            proof: component.evidence,
        });
    }
    let code = arena.value_quote(domain);
    interpret(arena, Mode::Identity, Domain::Elements(code))
        .and_then(Interpretation::elements)
        .and_then(|relation| {
            relation.evaluation_obligations(
                arena,
                (left, right),
                &HigherEvaluation(pointwise),
                ReplayBudget::DEFAULT,
            )
        })
        .map_err(|error| relation_refusal(arena, error))
}

/// How a checking goal against an identity reads its value.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum GoalReading
{
    /// An introduction form of the fold's fibres: it checks at the fibre.
    Fibre,
    /// Anything else checks against the type as written.
    Written,
}

/// How a checking goal reads its value: as native fibre evidence or against
/// the type as written.
///
/// # Specification
/// - requires: nothing.
/// - ensures: [`GoalReading::Fibre`] exactly when `expected` is an identity
///   type and `value` is an introduction form of the fold's fibres: neither an
///   identity form (`here`, a higher field, a higher evaluation) nor a neutral
///   that synthesizes its own type (a variable, a constant, a static
///   application).
/// - provides: the checking machine's redirect of fibre evidence. A neutral
///   inhabits an identity by its synthesized type, so conversion stays
///   structural and never computes a fibre.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the empty tuple inhabits identity at Bool between equal
///   endpoints and a variable of identity type checks by its own type.
/// - witness: `element_identity::tests::native_evidence_checks_against_the_fold_fibre`
#[spec(ensures: |ret| ret == GoalReading::Written || matches!(arena.value_type(expected), Some(&ValueType::Path { .. })))]
#[must_use]
pub(crate) fn goal_reading(
    arena: &TermArena,
    value: ValueId,
    expected: ValueTypeId,
) -> GoalReading
{
    let fibre = matches!(arena.value_type(expected), Some(&ValueType::Path { .. }))
        && !matches!(
            arena.value(value),
            None | Some(
                &(Value::Here(_)
                    | Value::Higher { .. }
                    | Value::HigherEvaluation { .. }
                    | Value::Variable(_)
                    | Value::Constant(_)
                    | Value::StaticApplication(..))
            )
        );
    if fibre {
        GoalReading::Fibre
    }
    else {
        GoalReading::Written
    }
}

/// The domain and endpoints of an identity type.
///
/// # Specification
/// - ensures: the three parts of a `Path` type.
/// - fails: a value-shape mismatch naming the type otherwise.
/// - panics: none.
///
/// # Errors
/// As `fails`.
///
/// # Adequacy
/// - hypothesis: L3 — a higher field against a non-identity refuses by shape.
/// - witness: `element_identity::tests::a_non_productive_higher_field_is_refused_by_name`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |&(domain, left, right)|
    matches!(arena.value_type(ty), Some(&ValueType::Path { domain: d, left: l, right: r }) if d == domain && l == left && r == right)))]
pub(crate) fn path_parts(
    arena: &TermArena,
    ty: ValueTypeId,
) -> Result<(ValueTypeId, ValueId, ValueId), KernelError>
{
    match arena.value_type(ty) {
        | Some(&ValueType::Path {
            domain,
            left,
            right,
        }) => Ok((domain, left, right)),
        | _ => Err(KernelError::ValueShapeMismatch {
            expected: ExpectedValueShape::Path,
            actual: value_type_witness(arena, ty),
        }),
    }
}

/// Translate a fold refusal into the kernel's refusal vocabulary.
///
/// # Specification
/// - ensures: every fold refusal reachable from the readings this module uses
///   maps to a named identity refusal, the underlying kernel or path refusal,
///   or `ArenaFault` for a fault no well-formed arena produces.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a closed Bool between two variables reaches the neutral
///   fibre's name through this translation.
/// - witness: `element_identity::tests::identity_at_an_open_type_is_a_neutral_fibre`
#[spec(captures: unsupported = matches!(error, RelationError::UnsupportedType(_)),
    ensures: |ret| !unsupported || matches!(ret, KernelError::Identity(IdentityError::OutsideFold(_))))]
fn relation_refusal(
    arena: &TermArena,
    error: RelationError,
) -> KernelError
{
    let refusal = match error {
        | RelationError::UnsupportedType(ty) => {
            IdentityError::OutsideFold(value_type_witness(arena, ty))
        },
        // The fold refuses a sealed atom for want of its interface; every
        // reading here meets that domain as open first, where the identity is
        // its own neutral fibre.
        | RelationError::AbstractInterface(_) | RelationError::NeutralFiber => {
            IdentityError::NeutralFibre
        },
        | RelationError::Typing(error) | RelationError::Pointwise(_, error) => return *error,
        | RelationError::Path(error) => return KernelError::Path(*error),
        | RelationError::Evidence => IdentityError::EmptyFibre,
        | RelationError::HigherFieldRequired => IdentityError::HigherFieldRequired,
        | RelationError::HigherEvaluationRequired => IdentityError::HigherEvaluationRequired,
        | RelationError::RecursiveObservationRequired => IdentityError::RecursiveObservation,
        | RelationError::CertificateOperationRequired => IdentityError::CertificateOperation,
        | RelationError::Boundary => IdentityError::Boundary,
        | RelationError::Coverage => IdentityError::Coverage,
        | RelationError::Budget => IdentityError::CoverageBudget,
        | RelationError::Evaluation(component, side, verdict) => IdentityError::Evaluation {
            component,
            side,
            verdict,
        },
        | RelationError::Arena
        | RelationError::UnsupportedCode(_)
        | RelationError::NonFibrant
        | RelationError::Classifier => return KernelError::ArenaFault,
    };
    KernelError::Identity(refusal)
}

/// Translate a higher-field refusal into the kernel's refusal vocabulary.
///
/// # Specification
/// - ensures: the walk's refusals keep their names and layer positions; a
///   position past `u32` is an arena fault.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the non-productive witness reaches its name and layer.
/// - witness: `element_identity::tests::a_non_productive_higher_field_is_refused_by_name`
#[spec(captures: cycle = matches!(error, HigherError::NonProductive(_)),
    ensures: |ret| !cycle || matches!(ret, KernelError::Identity(IdentityError::NonProductive(_)) | KernelError::ArenaFault))]
fn higher_refusal(
    arena: &TermArena,
    error: HigherError,
) -> KernelError
{
    let position = |id: HigherId| u32::try_from(id.0).map(LayerPosition);
    let refusal = match error {
        | HigherError::Relation(error) => return relation_refusal(arena, error),
        | HigherError::Path(error) => return KernelError::Path(*error),
        | HigherError::Boundary => IdentityError::Boundary,
        | HigherError::NonProductive(id) => match position(id) {
            | Ok(layer) => IdentityError::NonProductive(layer),
            | Err(_) => return KernelError::ArenaFault,
        },
        | HigherError::UnknownLayer(id) => match position(id) {
            | Ok(layer) => IdentityError::UnknownLayer(layer),
            | Err(_) => return KernelError::ArenaFault,
        },
        | HigherError::DepthBound => IdentityError::DepthBound,
        | HigherError::ZeroDepth => IdentityError::ZeroDepth,
        | HigherError::ExpectedEquivalence
        | HigherError::Replay(_)
        | HigherError::NeutralTransport => return KernelError::ArenaFault,
    };
    KernelError::Identity(refusal)
}

/// An element transport as the replay reads it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct ElementTransport
{
    /// The family, under one value binder for the endpoint.
    pub motive: ValueTypeId,
    /// The identity transported along.
    pub path: ValueId,
    /// The value at the source endpoint.
    pub value: ValueId,
}

/// One transport step, by the first rule of the module table that applies.
///
/// # Specification
/// - requires: nothing; an ill-typed term reduces or sticks without panicking.
/// - ensures: a reduct by the module's transport table, or `Stuck`.
/// - provides: the replay's δ-free transport computation.
/// - fails: `ArenaFault` on an unreadable path, motive or component.
/// - panics: none.
///
/// # Errors
/// As `fails`.
///
/// # Adequacy
/// - hypothesis: L3 — `here` transports to the value; a product and a sum
///   motive compute componentwise; the universe clause reaches native
///   transport; a neutral path over a dependent motive sticks.
/// - witness: `element_identity::tests::transport_on_here_is_the_identity_by_replay`
/// - witness: `element_identity::tests::transport_computes_through_the_fold_clauses`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |reduction| match *reduction {
    Reduction::Reduced(reduct) => arena.computation(reduct).is_some(),
    Reduction::Stuck => true,
}))]
pub(crate) fn transport_beta<M>(
    arena: &mut TermArena,
    table: &mut ContentTable,
    memo: &mut M,
    term: ElementTransport,
) -> Result<Reduction, KernelError>
where
    M: CheckMemo<RewriteSupport, RewriteOutcome>,
{
    let ElementTransport {
        motive,
        path,
        value,
    } = term;
    match arena.value(path) {
        | Some(&Value::Here(_)) => return Ok(Reduction::Reduced(arena.computation_return(value))),
        | Some(_) => {},
        | None => return Err(KernelError::ArenaFault),
    }
    if binder_use(arena, table, memo, Family::Type(motive)) == BinderUse::Ignored {
        return Ok(Reduction::Reduced(arena.computation_return(value)));
    }
    let family = arena
        .value_type(motive)
        .cloned()
        .ok_or(KernelError::ArenaFault)?;
    match family {
        | ValueType::Product(parts) => {
            let components = match arena.value(value) {
                | Some(&Value::Tuple(ref components)) if components.len() == parts.len() => {
                    components.clone()
                },
                | Some(_) => return Ok(Reduction::Stuck),
                | None => return Err(KernelError::ArenaFault),
            };
            Ok(Reduction::Reduced(transport_product(
                arena,
                table,
                memo,
                (&parts, &components),
                path,
            )?))
        },
        | ValueType::Sum(parts) => {
            let (summand, payload) = match arena.value(value) {
                | Some(&Value::Injection(summand, payload)) => (summand, payload),
                | Some(_) => return Ok(Reduction::Stuck),
                | None => return Err(KernelError::ArenaFault),
            };
            let Some(&part) = parts.get(usize::from(summand))
            else {
                return Ok(Reduction::Stuck);
            };
            let step = arena.computation_path_transport(part, path, payload);
            let bound = arena.value_variable(DeBruijnIndex::from(0_u32));
            let injected = arena.value_injection(summand, bound);
            let returned = arena.computation_return(injected);
            Ok(Reduction::Reduced(arena.computation_bind(step, returned)))
        },
        | ValueType::Element { code, target } => {
            let universe_family = matches!(arena.value(code), Some(&Value::Variable(index)) if index == DeBruijnIndex::from(0_u32))
                && target == Level::zero();
            Ok(if universe_family {
                Reduction::Reduced(arena.computation_transport(path, value))
            }
            else {
                Reduction::Stuck
            })
        },
        | ValueType::Path {
            domain,
            left,
            right,
        } => {
            let singleton = matches!(arena.value(right), Some(&Value::Variable(index)) if index == DeBruijnIndex::from(0_u32))
                && matches!(arena.value(value), Some(&Value::Here(_)))
                && binder_use(arena, table, memo, Family::Type(domain)) == BinderUse::Ignored
                && binder_use(arena, table, memo, Family::Value(left)) == BinderUse::Ignored;
            Ok(if singleton {
                Reduction::Reduced(arena.computation_return(path))
            }
            else {
                Reduction::Stuck
            })
        },
        | _ => Ok(Reduction::Stuck),
    }
}

/// Transport a tuple componentwise: one bind per component, then the tuple of
/// the bound results.
///
/// # Specification
/// - requires: one component per motive part.
/// - ensures: `x₀ ← transport(P₀, p, v₀); …; return (x₀, …)`, each step's path
///   and component shifted past the binds outside it, and each part's outer
///   variables shifted past them as well.
/// - fails: `ArenaFault` for a component count past `u32`.
/// - panics: none.
///
/// # Errors
/// As `fails`.
///
/// # Adequacy
/// - hypothesis: L3 — a pair of a Bool and a universe element transports
///   componentwise.
/// - witness: `element_identity::tests::transport_computes_through_the_fold_clauses`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |&reduct| arena.computation(reduct).is_some()))]
fn transport_product<M>(
    arena: &mut TermArena,
    table: &mut ContentTable,
    memo: &mut M,
    (parts, components): (&[ValueTypeId], &[ValueId]),
    path: ValueId,
) -> Result<ComputationId, KernelError>
where
    M: CheckMemo<RewriteSupport, RewriteOutcome>,
{
    let count = u32::try_from(components.len()).map_err(|_overflow| KernelError::ArenaFault)?;
    let mut bound = Vec::with_capacity(components.len());
    for position in (0 .. count).rev() {
        bound.push(arena.value_variable(DeBruijnIndex::from(position)));
    }
    let tuple = arena.value_tuple(&bound);
    let mut reduct = arena.computation_return(tuple);
    for (position, (&part, &component)) in (0 .. count).zip(parts.iter().zip(components)).rev() {
        let outside = BinderDepth::from(position);
        let part = shift_value_type(arena, table, memo, part, BinderDepth::from(1_u32), outside);
        let path = shift_value(arena, table, memo, path, BinderDepth::NONE, outside);
        let component = shift_value(arena, table, memo, component, BinderDepth::NONE, outside);
        let step = arena.computation_path_transport(part, path, component);
        reduct = arena.computation_bind(step, reduct);
    }
    Ok(reduct)
}

/// A family node whose innermost binder may be read.
#[derive(Clone, Copy, Debug)]
enum Family
{
    /// A value type under the binder.
    Type(ValueTypeId),
    /// A value under the binder.
    Value(ValueId),
}

/// What a family does with its innermost binder.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum BinderUse
{
    /// The family provably ignores variable zero.
    Ignored,
    /// The family may read variable zero.
    Read,
}

/// Whether a family reads its innermost binder.
///
/// # Specification
/// - requires: nothing.
/// - ensures: [`BinderUse::Ignored`] only when the family provably ignores
///   variable zero: instantiating it at a variable past the family's reach
///   leaves no variable at or past that reach. A saturated reach answers
///   [`BinderUse::Read`].
/// - provides: the constant-motive rule, decided without a dedicated occurrence
///   walk.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a Bool motive and one over an outer variable are
///   constant; `El(x)` reads its binder.
/// - witness: `element_identity::tests::transport_computes_through_the_fold_clauses`
#[spec(captures: closed = match family {
        Family::Type(ty) => u32::from(LooseDepths::new().value_type_reach(arena, ty)) == 0,
        Family::Value(value) => u32::from(LooseDepths::new().value_reach(arena, value)) == 0,
    },
    ensures: |ret| !closed || ret == BinderUse::Ignored)]
fn binder_use<M>(
    arena: &mut TermArena,
    table: &mut ContentTable,
    memo: &mut M,
    family: Family,
) -> BinderUse
where
    M: CheckMemo<RewriteSupport, RewriteOutcome>,
{
    let mut reach = LooseDepths::new();
    let before = u32::from(match family {
        | Family::Type(ty) => reach.value_type_reach(arena, ty),
        | Family::Value(value) => reach.value_reach(arena, value),
    });
    if before == 0 {
        return BinderUse::Ignored;
    }
    if before == u32::MAX {
        return BinderUse::Read;
    }
    let fresh = arena.value_variable(DeBruijnIndex::from(before));
    let mut reach = LooseDepths::new();
    let after = u32::from(match family {
        | Family::Type(ty) => {
            let instantiated = substitute_value_type(arena, table, memo, ty, fresh);
            reach.value_type_reach(arena, instantiated)
        },
        | Family::Value(value) => {
            let instantiated = substitute_value(arena, table, memo, value, fresh);
            reach.value_reach(arena, instantiated)
        },
    });
    if after > before {
        BinderUse::Read
    }
    else {
        BinderUse::Ignored
    }
}

/// A related application as the replay reads it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct RelatedStep
{
    /// The function identity.
    pub path: ValueId,
    /// The source argument.
    pub left: ValueId,
    /// The target argument.
    pub right: ValueId,
    /// The body, under the source result, the target result, and their
    /// identity, innermost last.
    pub body: ComputationId,
}

/// One related-application step.
///
/// # Specification
/// - requires: nothing; an ill-typed term reduces or sticks without panicking.
/// - ensures: when the path is `here(f)` and the arguments convert, the reduct
///   `x ← force f left; body[x, x, here(x)]`; `Stuck` otherwise.
/// - provides: the replay's computation of function identity on reflexivity.
/// - fails: `ArenaFault` on an unreadable path.
/// - panics: none.
///
/// # Errors
/// As `fails`.
///
/// # Adequacy
/// - hypothesis: L3 — a related application on `here(not)` at equal arguments
///   computes, and on a higher evaluation it sticks.
/// - witness: `element_identity::tests::a_higher_evaluation_proves_function_extensionality`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |reduction| match *reduction {
    Reduction::Reduced(reduct) => arena.computation(reduct).is_some(),
    Reduction::Stuck => true,
}))]
pub(crate) fn related_beta<M>(
    arena: &mut TermArena,
    table: &mut ContentTable,
    memo: &mut M,
    term: RelatedStep,
) -> Result<Reduction, KernelError>
where
    M: CheckMemo<RewriteSupport, RewriteOutcome>,
{
    let function = match arena.value(term.path) {
        | Some(&Value::Here(function)) => function,
        | Some(_) => return Ok(Reduction::Stuck),
        | None => return Err(KernelError::ArenaFault),
    };
    if equal_values(arena, term.left, term.right) != Convertibility::Convertible {
        return Ok(Reduction::Stuck);
    }
    let target = arena.value_variable(DeBruijnIndex::from(0_u32));
    let diagonal = arena.value_here(target);
    let body = substitute_computation(arena, table, memo, term.body, diagonal);
    let source = arena.value_variable(DeBruijnIndex::from(0_u32));
    let body = substitute_computation(arena, table, memo, body, source);
    let forced = arena.computation_force(function);
    let applied = arena.computation_application(forced, term.left);
    Ok(Reduction::Reduced(arena.computation_bind(applied, body)))
}
