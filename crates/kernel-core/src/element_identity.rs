//! Element identity as kernel syntax.
//!
//! The identity type `Path(A, a, b)`, its reflexivity `here(a)`, the returned
//! endpoint, transport in a dependent motive, the guarded higher field, higher
//! evaluation and related application.
//!
//! Every judgement here reads the one identity fold in
//! [`crate::identity_recursion`], beside one rule of its own, the identity at
//! a dependent pair. It computes the fibre a persisted identity denotes,
//! turns the evidence a persisted node carries into goals for the checking
//! machine, and supplies the replay's reductions.
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
//! the kernel's own term conversion: `c` must convert with both endpoints by
//! α-equality or by the rules a conversion is forced to fire, the η laws and
//! the two laws of bind among them (the crate's trusted-equality section), and
//! a refusal names both endpoints by content digest. An iterated identity reads
//! its inner identity's fibre first and treats a `here` endpoint as that
//! fibre's diagonal evidence. A neutral, a variable or a constant, inhabits an
//! identity by the type it synthesizes: type conversion stays structural, so a
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
//! - reversal: a type the fold does not cover (dependent arrows) needs a fold
//!   clause first. A higher-order argument needed none: higher evaluation's own
//!   coverage binds it, two functions and their identity, and the quantified
//!   evaluation (`0x3A`) decides a body that applies it. The evidence tag
//!   `0x3B` stays reserved for the dependent evaluation.
//!
//! **A path between dependent pairs is a pair of paths.** At `Σ (x : A). B`
//! the identity between `l` and `r` is [`sigma_fibre`]'s `Σ (p : Path(A, l₀,
//! r₀)). Path(B[r₀], ⟨tr(x. B, p, l₁)⟩, r₁)`, the components read from a
//! written pair or as the projections `⟨l.0⟩`, `⟨l.1⟩` of any other
//! endpoint. A pair checked at such an identity checks at that Σ, so the
//! first path joins the first components and the second ends at the right
//! second component over it. The rule reads only the Σ's factors, so an
//! open Σ has the same fibre. Transport along it reduces by the first two
//! rows of the table below and is neutral otherwise.
//!
//! - alternatives: a fold clause for the Σ, whose fibre graph would need a
//!   coordinate typed by the transport of another; the identity at a Σ left
//!   neutral, which makes a path between pairs unwritable but by `here`.
//! - reversal: a fold clause that types a coordinate by a transport moves this
//!   rule into the fold and lets transport along a non-reflexive path at a Σ
//!   compute componentwise.
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
//! fold, native evidence, a higher field or a higher or quantified evaluation,
//! refuses there as [`IdentityError::NeutralFibre`], the refusal a neutral
//! fibre at a closed domain already gives. No wire node is needed: the neutral
//! fibre is the persisted `Path` node over an open domain.
//!
//! - alternatives: refusing identity at formation and at `here`'s synthesis,
//!   which left every law over an abstract carrier unstatable; refusing it at
//!   the bridge, which let a `here` inside a body reach the kernel and fault.
//! - reversal: a fold clause for type variables (parametricity), or the
//!   interface a sealed atom declares, computes the fibre where this leaves it
//!   neutral; neither removes a rule stated here.
//!
//! **A returned endpoint stands for what its computation returns.** An
//! endpoint like `mul(neutral, x)` is a call, not a value former: the returned
//! endpoint over a computation `c` synthesizes `A` when `c` synthesizes the
//! returner `F A`. Every returner is pure, since no computation type here
//! carries an effect row; a computation of any other type has no value to
//! stand for and is refused as [`IdentityError::ReturnedNonReturner`], "a
//! returned endpoint over a non-returner". An impure endpoint is not
//! representable: the producer refuses it before it would reach the kernel.
//! Two returned endpoints convert by their computations, a stuck one
//! structurally. Where the conversion leaves a returned endpoint against
//! another value at a mode switch, the kernel reads it: normalizes it by its
//! own evaluator and converts the normal form by the one conversion
//! ([`mod@crate::replay`] § The returned endpoint). A reading that reaches a
//! different value, or none, keeps the refusal it would have had.
//!
//! - alternatives: an effect row on the kernel returner, which nothing in the
//!   kernel would read; endpoints restricted to value formers, which strands
//!   every law whose sides are calls; δ-normalizing under binders in the
//!   kernel, a second equality beside the replayed one.
//! - reversal: an effectful kernel computation type would need its own refusal
//!   beside the non-returner one.
//!
//! **Reflexivity replays the engine's conversion.** `here(c)` checks at
//! `Path(A, a, b)` when `c` converts with each endpoint. The forced conversion
//! is tried first; an endpoint it leaves apart is related by the dialogue the
//! `here` carries for that side, replayed with the admitted definitions
//! unfoldable ([`reflexive_endpoints`]). The engine's conversion holds a
//! returned endpoint at the definition it calls, so every δ-step the endpoint
//! needs, under a thunk or not, is a decision of the dialogue: the replay
//! unfolds only the constant it names, at the side it names. A dialogue naming
//! another constant or side, or fewer unfoldings than the endpoint needs, is
//! refused as [`IdentityError::EndpointsDiffer`], naming the side and the
//! replay's verdict.
//!
//! - alternatives: the kernel's own reading at reflexivity too, which stops at
//!   the first thunk because evaluation does not reduce under binders; a δ rule
//!   in the forced loop, which makes the trusted conversion a search over
//!   unfoldings.
//! - reversal: a judgement other than reflexivity that needs a δ-step under a
//!   binder carries its own dialogue the same way; the forced loop stays
//!   δ-free.
//!
//! **A definition's conversions replay the dialogues it carries.** A
//! definition whose declared type and body's type are path types with compound
//! endpoints, `Path(H, comp(p, p, q, id(p), f), f)` against `Path(H, comp(p,
//! q, q, f, id(q)), f)`, converts them only through a definition's body under
//! a binder: the δ-step the reflexivity paragraph above routes through a
//! dialogue. The definition carries a related pair per endpoint pair the
//! producer's conversion related, each with its dialogue
//! ([`RelatedEndpoints`]), and a mode switch whose forced reading leaves the
//! types apart reads them ([`related_endpoints`]): the walk sets every path
//! type's endpoint pair aside, a pair the forced reading relates passes, and
//! any other is matched by α-equality, in either orientation, to a related
//! pair whose dialogue is replayed with the admitted definitions unfoldable. A
//! pair no relation matches keeps the mismatch it had; a matched dialogue that
//! does not replay is refused as [`IdentityError::RelatedEndpointsDiffer`],
//! naming its verdict. The forced loop stays δ-free and nothing is searched: a
//! definition relating nothing is checked exactly as before.
//!
//! - alternatives: matching relations by their order in the walk, which ties
//!   the wire to the order two different conversions visit a type; replaying
//!   each relation at each pair until one replays, a search whose cost and
//!   verdict depend on the producer's ordering; a relation per mode switch
//!   inside the body's term, which needs a site on every node a conversion can
//!   meet.
//! - reversal: a conversion between terms other than path endpoints — two codes
//!   under an element type, a data index — that needs a δ-step under a binder
//!   sets its pairs aside the same way and is matched the same way.
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
//! substitution law holds of every motive. Its last row below is the
//! singleton's computation, transport in `x ↦ Path(A, a, x)` carrying
//! `here(a)` to the path. The replay reduces:
//!
//! | path or motive                      | reduct                                     |
//! | ----------------------------------- | ------------------------------------------ |
//! | the path is `here(_)`               | `return v`                                 |
//! | the motive ignores its binder       | `return v`                                 |
//! | a Product motive at a tuple         | each component transported, then the tuple |
//! | a Sum motive at an injection        | the injection of the summand's transport   |
//! | a List motive at `nil`              | `return nil`                               |
//! | a List motive at a cell             | the head transported, then the tail        |
//! | `El(x)` at level zero               | native universe transport                  |
//! | `Path(D, l, x)` at a `here` value   | `return p`                                 |
//!
//! A cell's tail is transported by a computation the reduct binds after the
//! head, so one replay step unfolds one cell and a list costs the budget its
//! length: a list past the budget declines as
//! [`crate::replay::ReplayDecline::Budget`], never as an inequality.
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
//! **A dependent motive is a telescope over the path and an identity over
//! it.** The telescope transport `tr₂(M, p, z₀, q, v)` takes the motive
//! `Π (y : A). Π (z : B). F C`, read by [`telescope`] or refused as a
//! computation-shape mismatch naming the telescope. `z₀` checks at `B[a]`; `q`
//! must synthesize `Path(B[b], ⟨tr(y. B, p, z₀)⟩, z₁)` — the identity over the
//! path from the start transported along it — or is refused as
//! [`IdentityError::NotOver`]; `v` checks at `C[a, z₀]` and the result returns
//! `C[b, z₁]`. Both instances are [`telescope_instance`]'s iterated single
//! substitution, outer binder first, so the substitution law is the one-binder
//! law twice and is replayed, never assumed. The replay reduces:
//!
//! | path and identity over it        | reduct                                       |
//! | -------------------------------- | -------------------------------------------- |
//! | both `here(_)`                   | `return v`                                   |
//! | the path `here(c)`               | `tr(z. C[c, z], q, v)`, the one-binder rows  |
//!
//! Anything else stays neutral. `J` is this transport in the singleton,
//! `tr₂(Π y. Π q : Path(A, a, y). F C, p, here(a), here(p), d)`: the identity
//! over the path checks because the singleton row carries `here(a)` to `p`,
//! and on `here(a)` it computes by the first row, so it needs no former of
//! its own.
//!
//! - alternatives: a motive under two binders of the one-binder node, which
//!   would change what a persisted node means; a primitive `J`.
//! - reversal: the one-binder transport in the Σ of the two entries replaces
//!   this once transport along a path at a Σ computes when it is not `here`.
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
//! coverage. A quantified evaluation is the same introduction for a body that
//! applies its function argument: it replays each application step's
//! dialogues to the normal forms it carries, reads the applied premise from
//! them, and checks every branch beneath it over the inner result's coverage.
//! Their elimination stays neutral, because the application site carries no
//! pointwise evaluation; the fold's own reading of that case is
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
use gandr_kernel_term::CompType;
use gandr_kernel_term::CompTypeId;
use gandr_kernel_term::ComputationId;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::EndpointDialogues;
use gandr_kernel_term::EvaluationComponent;
use gandr_kernel_term::EvaluationDialogues;
use gandr_kernel_term::HigherLayer;
use gandr_kernel_term::HigherProgram;
use gandr_kernel_term::LayerPosition;
use gandr_kernel_term::QuantifiedStep;
use gandr_kernel_term::RelatedEndpoints;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::Value;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueType;
use gandr_kernel_term::ValueTypeId;
use quenchant_shape::shape::Maybe;

use crate::conv::Convertibility;
use crate::conv::equal_values;
use crate::encoding::ContentTable;
use crate::encoding::content_digest;
use crate::error::CompTypeWitness;
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
use crate::identity_recursion::NormalForm;
use crate::identity_recursion::Pointwise;
use crate::identity_recursion::Quantified;
use crate::identity_recursion::RelationError;
use crate::identity_recursion::interpret;
use crate::path_universe::Dialogue;
use crate::path_universe::Reduction;
use crate::path_universe::anchor;
use crate::replay::EngineClaim;
use crate::replay::KernelVerdict;
use crate::replay::ReplayBudget;
use crate::replay::ReplaySides;
use crate::replay::Unfoldings;
use crate::rewrite::BinderDepth;
use crate::rewrite::RewriteOutcome;
use crate::rewrite::RewriteSupport;
use crate::rewrite::shift_value;
use crate::rewrite::shift_value_type;
use crate::rewrite::substitute_computation;
use crate::rewrite::substitute_outer_value_type;
use crate::rewrite::substitute_value;
use crate::rewrite::substitute_value_type;
use crate::support::LooseDepths;
use crate::witness::value_type_witness;

#[cfg(test)]
mod tests;

/// The endpoint of an identity a reflexivity refusal names.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum EndpointSide
{
    /// The source endpoint, `a` in `Path(A, a, b)`.
    Left,
    /// The target endpoint, `b` in `Path(A, a, b)`.
    Right,
}

/// A refusal of the element-identity rules.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum IdentityError
{
    /// The domain is closed but has no clause in the identity fold.
    OutsideFold(ValueTypeWitness),
    /// A reflexivity's point does not reach an endpoint: the forced
    /// conversion leaves them apart, and the dialogue the reflexivity carries
    /// for that endpoint does not replay as their convertibility.
    EndpointsDiffer
    {
        /// The source endpoint's content digest.
        left: ContentDigest,
        /// The target endpoint's content digest.
        right: ContentDigest,
        /// The endpoint the point did not reach.
        side: EndpointSide,
        /// That endpoint's dialogue's replay verdict.
        verdict: KernelVerdict,
    },
    /// A definition's type conversion meets two path endpoints its forced
    /// reading leaves apart, and the dialogue the definition carries for that
    /// pair does not replay as their convertibility.
    RelatedEndpointsDiffer
    {
        /// The expected type's endpoint's content digest.
        left: ContentDigest,
        /// The synthesized type's endpoint's content digest.
        right: ContentDigest,
        /// The pair's dialogue's replay verdict.
        verdict: KernelVerdict,
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
    /// A quantified evaluation's step does not apply the two functions its
    /// premise relates at one input.
    QuantifiedStep
    {
        /// The component, in coverage order.
        component: Component,
    },
    /// A quantified evaluation applies a function whose own domain binds a
    /// function: the fragment boundary, since related inputs there would need
    /// function identity between them.
    HigherOrderDomain
    {
        /// The component, in coverage order.
        component: Component,
    },
    /// A returned endpoint's computation synthesizes no returner.
    ReturnedNonReturner(CompTypeWitness),
    /// A telescope transport's second identity does not lie over its first:
    /// it does not synthesize the identity, in the family's fibre at the
    /// path's target, from the start transported along the path.
    NotOver
    {
        /// The identity over the path the transport owes.
        expected: ValueTypeWitness,
        /// The identity the second component synthesizes.
        actual: ValueTypeWitness,
    },
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
            | Self::RelatedEndpointsDiffer { .. } => {
                f.write_str("a definition's related endpoints do not replay")
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
            | Self::QuantifiedStep { .. } => {
                f.write_str("a quantified step does not apply its premise's functions at one input")
            },
            | Self::HigherOrderDomain { .. } => f.write_str(
                "a quantified evaluation applies a function whose domain is higher order",
            ),
            | Self::ReturnedNonReturner(_) => {
                f.write_str("a returned endpoint over a non-returner")
            },
            | Self::NotOver { .. } => f.write_str("an identity that does not lie over its path"),
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

/// Relate a reflexivity's point to both endpoints of the identity it is
/// checked at: by the forced conversion, or else by replaying the dialogue the
/// reflexivity carries for that endpoint.
///
/// # Specification
/// - requires: `point`, both endpoints and every body in `unfoldings` live in
///   `arena`, the endpoints in the point's context.
/// - ensures: `Ok(())` exactly when, for each endpoint, the forced conversion
///   [`crate::conv::convert_values`] relates the point to it, or that side's
///   dialogue in `dialogues` replays, under `unfoldings` and within
///   [`ReplayBudget::DEFAULT`], as a derivation of their convertibility.
///   `arena` holds what it held on entry.
/// - provides: the `here` rule's endpoint check. A constant unfolds only where
///   the dialogue names it, at the head and side it names, so a δ-step under a
///   binder is a recorded step and never the kernel's own search.
/// - fails: [`IdentityError::EndpointsDiffer`] at the first endpoint neither
///   relates, naming that side and its replay's verdict.
/// - panics: none.
///
/// # Errors
/// As `fails`.
///
/// # Adequacy
/// - hypothesis: L3 — endpoints related by the laws of bind need no dialogue;
///   an endpoint unfolding a definition under a thunk is admitted by the
///   dialogue that names the unfolding, and refused by name when the dialogue
///   names the wrong constant, the wrong side, or fewer unfoldings than the
///   endpoint needs.
/// - witness: `element_identity::tests::reflexivity_converts_its_endpoints_by_the_laws_of_bind`
/// - witness: `element_identity::tests::an_endpoint_unfolding_under_a_thunk_replays_its_dialogue`
/// - witness: `element_identity::tests::a_dialogue_naming_the_wrong_unfolding_is_refused_by_name`
#[spec(
    captures: before = arena.watermark(),
    ensures: |ret| arena.watermark() == before && ret.as_ref().err().is_none_or(|error| matches!(
        error,
        &KernelError::Identity(IdentityError::EndpointsDiffer { verdict, .. })
            if verdict != KernelVerdict::Convertible
    )),
)]
pub(crate) fn reflexive_endpoints(
    arena: &mut TermArena,
    unfoldings: &Unfoldings,
    point: ValueId,
    (left, right): (ValueId, ValueId),
    dialogues: &EndpointDialogues,
) -> Result<(), KernelError>
{
    for (side, endpoint, dialogue) in [
        (EndpointSide::Left, left, &dialogues.left),
        (EndpointSide::Right, right, &dialogues.right),
    ] {
        if crate::conv::convert_values(arena, point, endpoint) == Convertibility::Convertible {
            continue;
        }
        let verdict = crate::replay::replay(
            arena,
            unfoldings,
            ReplaySides::Values(point, endpoint),
            EngineClaim::Convertible,
            dialogue.iter().copied().map(anchor),
            ReplayBudget::DEFAULT,
        );
        if verdict != KernelVerdict::Convertible {
            return Err(KernelError::Identity(IdentityError::EndpointsDiffer {
                left: content_digest(arena, AnyNode::Value(left)),
                right: content_digest(arena, AnyNode::Value(right)),
                side,
                verdict,
            }));
        }
    }
    Ok(())
}

/// Read a type conversion the forced reading left apart through the endpoint
/// pairs a definition relates: every path type's endpoints and every returned
/// endpoint the conversion meets are set aside, each pair the forced reading
/// does not relate is matched by α-equality to a related pair, and that pair's
/// dialogue is replayed.
///
/// # Specification
/// - requires: `goal`'s roots, every related pair and every body in
///   `unfoldings` live in `arena`, each related pair in the context the
///   conversion meets it in.
/// - ensures: [`crate::replay::EndpointReading::Apart`] when the structure
///   outside the set-aside pairs diverges, or a set-aside pair is neither
///   related by the forced reading nor α-equal, in either orientation, to a
///   related pair; [`crate::replay::EndpointReading::Converts`] when every
///   set-aside pair is related by the forced reading or its related pair's
///   dialogue replays, under `unfoldings` and within [`ReplayBudget::DEFAULT`],
///   as a derivation of convertibility. `arena` holds what it held on entry.
/// - provides: the mode switches' reading of a definition's relations. The
///   match is content equality, never a search: soundness rests on the replay
///   alone, and a pair matched to the wrong relation cannot replay. Every
///   δ-step is a decision of the dialogue, so the forced loop stays δ-free.
/// - fails: [`IdentityError::RelatedEndpointsDiffer`] at the first pair whose
///   related dialogue does not replay, naming the pair and the replay's
///   verdict.
/// - panics: none.
///
/// # Errors
/// As `fails`.
///
/// # Termination
/// - reason: the `for` loop over the set-aside pairs and the `find` over the
///   related pairs, not recursion.
/// - measure: the pairs left; each replay is bounded by its budget.
///
/// # Adequacy
/// - hypothesis: L3 — two path types whose compound endpoints relate only
///   through a definition's body convert by the definition's dialogue, and a
///   dialogue naming the wrong side or an unrelated definition is refused by
///   name; a definition relating nothing keeps the forced reading's verdict.
/// - witness: `element_identity::tests::a_definition_relating_compound_endpoints_admits`
/// - witness: `element_identity::tests::a_corrupted_relation_is_refused_by_name`
#[spec(
    captures: before = arena.watermark(),
    ensures: |ret| arena.watermark() == before && ret.as_ref().err().is_none_or(|error| matches!(
        error,
        &KernelError::Identity(IdentityError::RelatedEndpointsDiffer { verdict, .. })
            if verdict != KernelVerdict::Convertible
    )),
)]
pub(crate) fn related_endpoints(
    arena: &mut TermArena,
    unfoldings: &Unfoldings,
    related: &[RelatedEndpoints],
    goal: crate::conv::ConversionGoal,
) -> Result<crate::replay::EndpointReading, KernelError>
{
    let mut pairs = Vec::new();
    if crate::conv::related_pairs(arena, goal, &mut pairs) == Convertibility::Distinct {
        return Ok(crate::replay::EndpointReading::Apart);
    }
    for (left, right) in pairs {
        let mut pending = Vec::new();
        if crate::conv::pending_endpoints(
            arena,
            crate::conv::ConversionGoal::Value(left, right),
            &mut pending,
        ) == Convertibility::Convertible
            && crate::replay::read_endpoints(arena, unfoldings, &pending, ReplayBudget::DEFAULT)
                == crate::replay::EndpointReading::Converts
        {
            continue;
        }
        let matched = related.iter().find(|relation| {
            let forward = equal_values(arena, left, relation.left) == Convertibility::Convertible
                && equal_values(arena, right, relation.right) == Convertibility::Convertible;
            forward
                || equal_values(arena, left, relation.right) == Convertibility::Convertible
                    && equal_values(arena, right, relation.left) == Convertibility::Convertible
        });
        let Some(relation) = matched
        else {
            return Ok(crate::replay::EndpointReading::Apart);
        };
        let verdict = crate::replay::replay(
            arena,
            unfoldings,
            ReplaySides::Values(relation.left, relation.right),
            EngineClaim::Convertible,
            relation.dialogue.iter().copied().map(anchor),
            ReplayBudget::DEFAULT,
        );
        if verdict != KernelVerdict::Convertible {
            return Err(KernelError::Identity(
                IdentityError::RelatedEndpointsDiffer {
                    left: content_digest(arena, AnyNode::Value(left)),
                    right: content_digest(arena, AnyNode::Value(right)),
                    verdict,
                },
            ));
        }
    }
    Ok(crate::replay::EndpointReading::Converts)
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

/// The fibre of the identity at the dependent pair `Σ (x : first). second`
/// between `left` and `right`.
///
/// # Specification
/// - requires: `second` stands under one binder of `first`; both endpoints
///   inhabit the pair. The checking machine discharges those goals itself.
/// - ensures: `Σ (p : Path(first, l₀, r₀)). Path(second[r₀], ⟨tr(x. second, p,
///   l₁)⟩, r₁)`, reading the components of a written pair and the two
///   projections, each the value it returns, of any other endpoint. Nothing
///   about the pair's factors is read beyond their place, so an open pair has
///   the same fibre.
/// - provides: the type the checking machine redirects a pair checked at an
///   identity of a dependent pair to.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a pair of reflexivities inhabits the identity of a pair
///   with itself, and one whose second path ends elsewhere is refused.
/// - witness: `element_identity::tests::a_pair_of_paths_inhabits_the_identity_of_a_dependent_pair`
#[spec(ensures: |ret| arena.value_type(ret).is_some())]
pub(crate) fn sigma_fibre<M>(
    arena: &mut TermArena,
    (table, memo): (&mut ContentTable, &mut M),
    (first, second): (ValueTypeId, ValueTypeId),
    (left, right): (ValueId, ValueId),
) -> ValueTypeId
where
    M: CheckMemo<RewriteSupport, RewriteOutcome>,
{
    let [left_first, left_second] = pair_components(arena, left);
    let [right_first, right_second] = pair_components(arena, right);
    let paths = arena.value_type_path(first, left_first, right_first);
    let past = BinderDepth::from(1_u32);
    let at_right = substitute_value_type(arena, table, memo, second, right_first);
    let at_right = shift_value_type(arena, table, memo, at_right, BinderDepth::NONE, past);
    let motive = shift_value_type(arena, table, memo, second, past, past);
    let path = arena.value_variable(DeBruijnIndex::from(0_u32));
    let moved = shift_value(arena, table, memo, left_second, BinderDepth::NONE, past);
    let transport = arena.computation_path_transport(motive, path, moved);
    let transported = arena.value_returned(transport);
    let target = shift_value(arena, table, memo, right_second, BinderDepth::NONE, past);
    let over = arena.value_type_path(at_right, transported, target);

    arena.value_type_sigma(paths, over)
}

/// The two components of a dependent pair's inhabitant.
///
/// # Specification
/// - requires: `pair` inhabits a dependent pair.
/// - ensures: the components of a written pair of two; the projections
///   `⟨pair.0⟩` and `⟨pair.1⟩`, each the value it returns, otherwise.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`sigma_fibre`].
/// - witness: `element_identity::tests::a_pair_of_paths_inhabits_the_identity_of_a_dependent_pair`
#[spec(ensures: |ret| ret.iter().all(|&component| arena.value(component).is_some()))]
fn pair_components(
    arena: &mut TermArena,
    pair: ValueId,
) -> [ValueId; 2]
{
    if let Some(&[first, second]) = arena.value(pair).and_then(Value::components) {
        return [first, second];
    }
    [0_usize, 1_usize].map(|index| {
        let projected =
            arena.computation_tuple_projection(pair, gandr_kernel_term::Component::from(index));
        arena.value_returned(projected)
    })
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
        | Some(&Value::Here { .. }) => fibers
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
/// - requires: `expected` is the identity the evaluation is checked against;
///   every body `unfoldings` holds is closed and admitted before it.
/// - ensures: one obligation per kernel-generated coverage pattern, after every
///   component's two dialogues replayed positively, unfolding only what
///   `unfoldings` defines.
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
///   both branches; a wrong component count refuses as coverage; a composition
///   of admitted definitions replays by their bodies.
/// - witness: `element_identity::tests::a_higher_evaluation_proves_function_extensionality`
/// - witness: `element_identity::tests::a_higher_evaluation_unfolds_what_the_environment_admitted`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |owed| owed.len() == components.len()))]
pub(crate) fn evaluation_obligations(
    arena: &mut TermArena,
    unfoldings: &Unfoldings,
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
                (unfoldings, ReplayBudget::DEFAULT),
            )
        })
        .map_err(|error| relation_refusal(arena, error))
}

/// The goals a persisted quantified evaluation owes, grouped by telescope.
///
/// # Specification
/// - requires: as [`evaluation_obligations`].
/// - ensures: the obligations the function relation's quantified reading owes,
///   after every step's two dialogues replayed positively, unfolding only what
///   `unfoldings` defines; each step takes its children in step order, three
///   for a return and two for an application.
/// - provides: the checking machine's reading of a quantified evaluation, with
///   no nested check.
/// - fails: as [`evaluation_obligations`]; coverage when the children do not
///   match the steps; a quantified step that does not apply its premise's
///   functions at one input, and a higher-order domain, by name.
/// - panics: none.
///
/// # Errors
/// As `fails`, and `ArenaFault` on an unreadable node.
///
/// # Adequacy
/// - hypothesis: L1/L3 — `λf. f(true)` relates to itself and to its bind form,
///   a twice-applied body nests its branches, differing inputs, a higher-order
///   domain and a missing child each refuse by name.
/// - witness: `element_identity::tests::a_quantified_evaluation_replays_under_the_quantifier`
/// - witness: `element_identity::tests::a_quantified_evaluation_refuses_what_it_cannot_relate`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |owed| !owed.is_empty()))]
pub(crate) fn quantified_obligations(
    arena: &mut TermArena,
    unfoldings: &Unfoldings,
    expected: ValueTypeId,
    steps: &[QuantifiedStep],
    children: &[ValueId],
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
    let coverage = || KernelError::Identity(IdentityError::Coverage);
    let mut values = children.iter().copied();
    let mut quantified = Vec::with_capacity(steps.len());
    for step in steps {
        let dialogues = step.dialogues();
        let left_dialogue = Dialogue(dialogues.left.iter().copied().map(anchor).collect());
        let right_dialogue = Dialogue(dialogues.right.iter().copied().map(anchor).collect());
        let first = values.next().ok_or_else(coverage)?;
        let second = values.next().ok_or_else(coverage)?;
        quantified.push(match *step {
            | QuantifiedStep::Return(_) => Quantified::Return {
                left: Evaluation {
                    value: first,
                    dialogue: left_dialogue,
                },
                right: Evaluation {
                    value: second,
                    dialogue: right_dialogue,
                },
                proof: values.next().ok_or_else(coverage)?,
            },
            | QuantifiedStep::Apply { fibre, .. } => Quantified::Apply {
                fibre,
                left: NormalForm {
                    normal: first,
                    dialogue: left_dialogue,
                },
                right: NormalForm {
                    normal: second,
                    dialogue: right_dialogue,
                },
            },
        });
    }
    if values.next().is_some() {
        return Err(coverage());
    }
    let code = arena.value_quote(domain);
    interpret(arena, Mode::Identity, Domain::Elements(code))
        .and_then(Interpretation::elements)
        .and_then(|relation| {
            relation.quantified_obligations(
                arena,
                (left, right),
                &quantified,
                (unfoldings, ReplayBudget::DEFAULT),
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
                &(Value::Here { .. }
                    | Value::Higher { .. }
                    | Value::HigherEvaluation { .. }
                    | Value::QuantifiedEvaluation { .. }
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
        | RelationError::QuantifiedStep(component) => IdentityError::QuantifiedStep { component },
        | RelationError::HigherOrderDomain(component) => {
            IdentityError::HigherOrderDomain { component }
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
/// - hypothesis: L3 — `here` transports to the value; a product, a sum and a
///   list motive compute constructorwise, a list one cell per step; the
///   universe clause reaches native transport; a neutral path over a dependent
///   motive sticks.
/// - witness: `element_identity::tests::transport_on_here_is_the_identity_by_replay`
/// - witness: `element_identity::tests::transport_computes_through_the_fold_clauses`
/// - witness: `path_universe::tests::recursive_transport_tests::negation_moves_a_list_one_cell_at_a_time`
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
        | Some(&Value::Here { .. }) => {
            return Ok(Reduction::Reduced(arena.computation_return(value)));
        },
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
            Ok(Reduction::Reduced(componentwise(
                arena,
                table,
                memo,
                Mover::Transport,
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
            let step = Mover::Transport.step(arena, part, path, payload);
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
                && matches!(arena.value(value), Some(&Value::Here { .. }))
                && binder_use(arena, table, memo, Family::Type(domain)) == BinderUse::Ignored
                && binder_use(arena, table, memo, Family::Value(left)) == BinderUse::Ignored;
            Ok(if singleton {
                Reduction::Reduced(arena.computation_return(path))
            }
            else {
                Reduction::Stuck
            })
        },
        | ValueType::List(element) => {
            let (head, tail) = match arena.value(value) {
                | Some(&Value::ListNil) => {
                    return Ok(Reduction::Reduced(arena.computation_return(value)));
                },
                | Some(&Value::ListCons(head, tail)) => (head, tail),
                | Some(_) => return Ok(Reduction::Stuck),
                | None => return Err(KernelError::ArenaFault),
            };
            Ok(Reduction::Reduced(cell(
                arena,
                table,
                memo,
                Mover::Transport,
                (element, motive),
                path,
                (head, tail),
            )))
        },
        | _ => Ok(Reduction::Stuck),
    }
}

quenchant_shape::reason_enum! {
    /// Why a computation type reads as no telescope motive.
    mod telescope_motive {
        /// The computation type is no telescope motive.
        #[derive(Clone, Copy, Debug, Eq, PartialEq)]
        pub enum Absent {
            /// The type is not a dependent arrow whose codomain is a
            /// dependent arrow into a returner.
            Shape,
        }
    }
}

/// A telescope transport's motive, read as its three layers.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct Telescope
{
    /// The path's carrier, in the transport's context.
    pub carrier: ValueTypeId,
    /// The family over the carrier, under one value binder for its point.
    pub family: ValueTypeId,
    /// The returned type, under the point's binder and then the family
    /// element's.
    pub body: ValueTypeId,
}

/// Read a telescope transport's motive `Π (y : A). Π (z : B). F C`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the three layers of a motive of exactly that shape.
/// - provides: [`telescope_motive::Absent::Shape`] for any other computation
///   type: the checker refuses it, and the replay leaves its transport stuck.
/// - fails: `ArenaFault` on an unreadable layer.
/// - panics: none.
///
/// # Errors
/// As `fails`.
///
/// # Adequacy
/// - hypothesis: L3 — a two-arrow motive reads as its layers, and a one-arrow
///   motive is refused by its shape.
/// - witness: `element_identity::tests::a_dependent_motive_replays_its_substitution_law`
/// - witness: `element_identity::tests::a_one_entry_telescope_motive_is_refused_by_its_shape`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |reading| match *reading {
    Maybe::Present(Telescope { carrier, family, body }) => [carrier, family, body].iter().all(|&layer| arena.value_type(layer).is_some()),
    Maybe::Absent(_) => true,
}))]
pub(crate) fn telescope(
    arena: &TermArena,
    motive: CompTypeId,
) -> Result<Maybe<Telescope, telescope_motive::Absent>, KernelError>
{
    let (carrier, inner) = match arena.comp_type(motive) {
        | Some(&CompType::Pi { domain, codomain }) => (domain, codomain),
        | Some(_) => return Ok(Maybe::Absent(telescope_motive::Absent::Shape)),
        | None => return Err(KernelError::ArenaFault),
    };
    let (family, innermost) = match arena.comp_type(inner) {
        | Some(&CompType::Pi { domain, codomain }) => (domain, codomain),
        | Some(_) => return Ok(Maybe::Absent(telescope_motive::Absent::Shape)),
        | None => return Err(KernelError::ArenaFault),
    };
    let body = match arena.comp_type(innermost) {
        | Some(&CompType::Returner(body)) => body,
        | Some(_) => return Ok(Maybe::Absent(telescope_motive::Absent::Shape)),
        | None => return Err(KernelError::ArenaFault),
    };
    if [carrier, family, body]
        .iter()
        .any(|&layer| arena.value_type(layer).is_none())
    {
        return Err(KernelError::ArenaFault);
    }
    Ok(Maybe::Present(Telescope {
        carrier,
        family,
        body,
    }))
}

/// A telescope's returned type instantiated at a point and an element of the
/// family's fibre over it: `C[point, element]`.
///
/// # Specification
/// - requires: `body` stands under two binders more than `point` and `element`,
///   which share one context.
/// - ensures: the point substituted at the outer binder, then the element at
///   the kept inner one.
/// - provides: the telescope's substitution law as iterated single
///   substitution, shared by the check and its witnesses.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a body mentioning both binders instantiates each at its
///   own endpoint.
/// - witness: `element_identity::tests::a_dependent_motive_replays_its_substitution_law`
#[spec(ensures: |ret| arena.value_type(body).is_none() || arena.value_type(ret).is_some())]
pub(crate) fn telescope_instance<M>(
    arena: &mut TermArena,
    table: &mut ContentTable,
    memo: &mut M,
    body: ValueTypeId,
    (point, element): (ValueId, ValueId),
) -> ValueTypeId
where
    M: CheckMemo<RewriteSupport, RewriteOutcome>,
{
    let fibre = substitute_outer_value_type(arena, table, memo, body, point);
    substitute_value_type(arena, table, memo, fibre, element)
}

/// A telescope transport as the replay reads it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct TelescopeStep
{
    /// The motive `Π (y : A). Π (z : B). F C`.
    pub motive: CompTypeId,
    /// The identity in the carrier.
    pub path: ValueId,
    /// The family element at the path's source.
    pub start: ValueId,
    /// The identity over the path, in the fibre at its target.
    pub over: ValueId,
    /// The value at the source.
    pub value: ValueId,
}

/// One telescope transport step, by the first row of the module table that
/// applies.
///
/// # Specification
/// - requires: nothing; an ill-typed term reduces or sticks without panicking.
/// - ensures: the value when both identities are `here`; when only the path is
///   `here(c)`, the one-binder transport along the over identity in the fibre
///   family `z. C[c, z]`; otherwise `Stuck`, as for a motive that is no
///   telescope.
/// - provides: the replay's telescope transport computation.
/// - fails: `ArenaFault` on an unreadable motive layer, path or over identity.
/// - panics: none.
///
/// # Errors
/// As `fails`.
///
/// # Adequacy
/// - hypothesis: L3 — `here` along both identities returns the value; `here`
///   along the path transports in the fibre; a neutral path sticks.
/// - witness: `element_identity::tests::telescope_transport_along_here_reduces`
/// - witness: `element_identity::tests::j_derived_in_the_singleton_checks_and_computes`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |reduction| match *reduction {
    Reduction::Reduced(reduct) => arena.computation(reduct).is_some(),
    Reduction::Stuck => true,
}))]
pub(crate) fn telescope_beta<M>(
    arena: &mut TermArena,
    table: &mut ContentTable,
    memo: &mut M,
    term: TelescopeStep,
) -> Result<Reduction, KernelError>
where
    M: CheckMemo<RewriteSupport, RewriteOutcome>,
{
    let TelescopeStep {
        motive,
        path,
        over,
        value,
        ..
    } = term;
    let body = match telescope(arena, motive)? {
        | Maybe::Present(Telescope { body, .. }) => body,
        | Maybe::Absent(telescope_motive::Absent::Shape) => return Ok(Reduction::Stuck),
    };
    let point = match arena.value(path) {
        | Some(&Value::Here { point, .. }) => point,
        | Some(_) => return Ok(Reduction::Stuck),
        | None => return Err(KernelError::ArenaFault),
    };
    match arena.value(over) {
        | Some(&Value::Here { .. }) => Ok(Reduction::Reduced(arena.computation_return(value))),
        | Some(_) => {
            let fibre = substitute_outer_value_type(arena, table, memo, body, point);
            Ok(Reduction::Reduced(
                arena.computation_path_transport(fibre, over, value),
            ))
        },
        | None => Err(KernelError::ArenaFault),
    }
}

/// The eliminator a componentwise step re-applies at each part.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Mover
{
    /// Transport along an identity.
    Transport,
    /// Ride along a flow.
    Ride,
}

impl Mover
{
    /// One step of this eliminator at a motive, along an identity or flow,
    /// from a value.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn step(
        self,
        arena: &mut TermArena,
        motive: ValueTypeId,
        along: ValueId,
        value: ValueId,
    ) -> ComputationId
    {
        match self {
            | Self::Transport => arena.computation_path_transport(motive, along, value),
            | Self::Ride => arena.computation_ride(motive, along, value),
        }
    }
}

/// Move a tuple componentwise: one bind per component, then the tuple of the
/// bound results.
///
/// # Specification
/// - requires: one component per motive part.
/// - ensures: `x₀ ← step(P₀, p, v₀); …; return (x₀, …)` for the `mover`'s step,
///   each step's identity or flow and component shifted past the binds outside
///   it, and each part's outer variables shifted past them as well.
/// - fails: `ArenaFault` for a component count past `u32`.
/// - panics: none.
///
/// # Errors
/// As `fails`.
///
/// # Adequacy
/// - hypothesis: L3 — a pair of a Bool and a universe element transports
///   componentwise, and a pair rides componentwise along a forward flow.
/// - witness: `element_identity::tests::transport_computes_through_the_fold_clauses`
/// - witness: `flow_universe::tests::ride_computes_through_the_motive_rows`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |&reduct| arena.computation(reduct).is_some()))]
pub(crate) fn componentwise<M>(
    arena: &mut TermArena,
    table: &mut ContentTable,
    memo: &mut M,
    mover: Mover,
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
        let step = mover.step(arena, part, path, component);
        reduct = arena.computation_bind(step, reduct);
    }
    Ok(reduct)
}

/// Move one list cell: the head in the element motive, then the tail in the
/// whole list motive, behind the head's bind.
///
/// # Specification
/// - requires: `motive` is the List motive `element` is the element of.
/// - ensures: `h ← step(E, p, head); t ← step(List E, p, tail); return cons(h,
///   t)` for the `mover`'s step, the tail step's motive, identity or flow and
///   tail shifted past the head's bind. The tail's step is a computation,
///   reduced only when the replay reaches it, so one step unfolds one cell.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — negation moves a three-cell Bool list cell by cell; a
///   list whose cells outrun the replay budget declines, and a variable tail
///   leaves the computed head before a stuck tail.
/// - witness: `path_universe::tests::recursive_transport_tests::negation_moves_a_list_one_cell_at_a_time`
/// - witness: `flow_universe::tests::ride_computes_through_the_motive_rows`
#[spec(ensures: |reduct| arena.computation(reduct).is_some())]
pub(crate) fn cell<M>(
    arena: &mut TermArena,
    table: &mut ContentTable,
    memo: &mut M,
    mover: Mover,
    (element, motive): (ValueTypeId, ValueTypeId),
    path: ValueId,
    (head, tail): (ValueId, ValueId),
) -> ComputationId
where
    M: CheckMemo<RewriteSupport, RewriteOutcome>,
{
    let first = mover.step(arena, element, path, head);
    let past = BinderDepth::from(1_u32);
    let motive = shift_value_type(arena, table, memo, motive, past, past);
    let path = shift_value(arena, table, memo, path, BinderDepth::NONE, past);
    let tail = shift_value(arena, table, memo, tail, BinderDepth::NONE, past);
    let rest = mover.step(arena, motive, path, tail);
    let moved_head = arena.value_variable(DeBruijnIndex::from(1_u32));
    let moved_tail = arena.value_variable(DeBruijnIndex::from(0_u32));
    let cell = arena.value_list_cons(moved_head, moved_tail);
    let returned = arena.computation_return(cell);
    let rest = arena.computation_bind(rest, returned);
    arena.computation_bind(first, rest)
}

/// A family node whose innermost binder may be read.
#[derive(Clone, Copy, Debug)]
pub(crate) enum Family
{
    /// A value type under the binder.
    Type(ValueTypeId),
    /// A value under the binder.
    Value(ValueId),
}

/// What a family does with its innermost binder.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum BinderUse
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
#[cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        spec_clause_traversal,
        reason = "parity: the body computes the family's reach from a fresh table first; the capture walks the same family once"
    )
)]
#[spec(captures: closed = match family {
        Family::Type(ty) => u32::from(LooseDepths::new().value_type_reach(arena, ty)) == 0,
        Family::Value(value) => u32::from(LooseDepths::new().value_reach(arena, value)) == 0,
    },
    ensures: |ret| !closed || ret == BinderUse::Ignored)]
pub(crate) fn binder_use<M>(
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
        | Some(&Value::Here {
            point: function, ..
        }) => function,
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
