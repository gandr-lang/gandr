//! Element identity as kernel syntax.
//!
//! The identity type `Path(A, a, b)`, its reflexivity `here(a)`, the returned
//! endpoint, transport in a dependent motive, the guarded higher field, higher
//! evaluation and related application.
//!
//! Every judgement here reads the one identity fold in
//! [`crate::identity_recursion`], beside two rules of its own, the identity at
//! a dependent pair and at a tuple of a product. It computes the fibre a
//! persisted identity denotes, turns the evidence a persisted node carries into
//! goals for the checking machine, and supplies the replay's reductions.
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
//! fibre's diagonal evidence. A neutral — a variable, a constant or a returned
//! endpoint — inhabits an identity by the type it synthesizes: type conversion
//! stays structural, so a neutral of the fibre type does not inhabit the
//! identity. `here(c)` synthesizes the diagonal at the type `c` synthesizes,
//! so like every annotation-free introduction it is inferable only where its
//! point is; an eliminator whose path is the `here` of an injection or a λ
//! takes it through a binder or a constant.
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
//! r₀)). Path(B[r₀], ⟨tr(x. B, p, l₁)⟩, r₁)`. Its components are read from
//! the written pair an endpoint is, or the one a declared constant's admitted
//! body is, so a declared endpoint unfolds here as an endpoint at every other
//! former does; any other endpoint is read as its projections `⟨l.0⟩`,
//! `⟨l.1⟩`. A pair checked at such an identity checks at that Σ, so the first
//! path joins the first components and the second ends at the right second
//! component over it. The rule reads only the Σ's factors, so an open Σ has
//! the same fibre. Transport along it reduces by the first two rows of the
//! table below and is neutral otherwise.
//!
//! - alternatives: a fold clause for the Σ, whose fibre graph would need a
//!   coordinate typed by the transport of another; the identity at a Σ left
//!   neutral, which makes a path between pairs unwritable but by `here`.
//! - reversal: a fold clause that types a coordinate by a transport moves this
//!   rule into the fold and lets transport along a non-reflexive path at a Σ
//!   compute componentwise.
//!
//! **A path between tuples is a tuple of paths.** A tuple checked at the
//! identity between `l` and `r` at `A₀ × … × Aₙ` checks at [`product_fibre`]'s
//! `Path(A₀, l₀, r₀) × … × Path(Aₙ, lₙ, rₙ)`, the components read as the Σ
//! rule reads them; a tuple transported at a product motive is read as its
//! components' transports `⟨tr(x. Aᵢ, p, vᵢ)⟩`, the table's product row. The
//! fold's evidence at a product still checks, each component at its factor's
//! identity.
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
//! **A returned endpoint inhabits an identity as a neutral does.** Checked at
//! an identity type, `⟨c⟩` is read by the type `c` returns and converted with
//! the identity as written, never redirected to the fold's fibre: it is an
//! elimination, not an introduction of the fibre, and the checker's value
//! bridge reads it the same way. So a reflexive transport at a path-type
//! motive, `Path(Path(A, a, a), ⟨tr(x. Path(A, x, x), here(a), here(a))⟩,
//! here(a))`, forms: its left endpoint returns `Path(A, a, a)`, the motive at
//! the path's target, and `here(here(a))` relates its point to that endpoint
//! by the transport table's first row below. Read as fibre evidence, the
//! endpoint would be compared with the unit fibre and refused where the checker
//! accepts it.
//!
//! - alternatives: the checker's reduction of the transport recorded as a
//!   dialogue the kernel replays, which carries a step the kernel's own
//!   transport row already takes and leaves untouched the endpoint's type,
//!   where the two disagreed; the checker reading a returned endpoint as fibre
//!   evidence too, which puts the fold into its value bridge, a second equality
//!   beside its structural conversion.
//! - reversal: a fibre whose evidence only a computation produces needs a
//!   returned endpoint read at the fibre; the reading then moves into the fold,
//!   for the checker and the kernel together.
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
//! | path and identity over it                  | reduct                                        |
//! | ------------------------------------------ | --------------------------------------------- |
//! | any, with `C` reading neither entry        | `return v`, the constant row                  |
//! | both `here(_)`                             | `return v`                                    |
//! | the path `here(c)`                         | `tr(z. C[c, z], q, v)`, the one-binder rows   |
//! | any other, with `C` a `Path(Unit, l, r)`   | `return ()`, the unit fibre's one inhabitant  |
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
//! **A bridge is the fold's relation, persisted.**
//! `Bridge(A, a, b)` reads the fold in
//! [`crate::identity_recursion::Mode::Bridge`] at the quoted `A`
//! ([`bridge_fibre`]); the clause per code is the bridge
//! column of [`crate::identity_recursion`]'s table. It forms as an identity
//! does, at its domain's level with its endpoints owed, and an introduction
//! form checked at it checks at its fibre; an open domain is a neutral fibre,
//! and a function code's family is introduced only by a higher or quantified
//! evaluation over the coverage the bridge fold generates.
//!
//! A sealed atom's elements are related by the interface its declaration
//! states: a relation `R : A → A → U` and its reflexivity
//! `(x : A) → R x x`, both checked at the atom's admission over its
//! representation. A bridge between two elements of an interfaced atom is
//! `El(R a b)`, and `here a` checks at `Bridge(A, a, a)` by the reflexivity.
//! A domain reaching an atom stating no interface is refused at formation as
//! [`IdentityError::BridgeAtSealedType`].
//!
//! **An identity at an atom is its relation once the law makes the relation
//! an identity system.** The interface may state the law `(a b : Rep) → (r :
//! R a b) → Path(Σ (y : Rep). R a y, (b, r), (a, refl a))`, checked at the
//! atom's admission ([`law_type`]): every singleton at `a` contracts onto its
//! centre. A reflexive relation whose singletons contract is an identity
//! system (_Homotopy Type Theory_, Theorem 5.8.2), so an identity at such an
//! atom reads `El(R a b)` as its fibre, as a bridge does, and its eliminator
//! is the one derived in the singleton family: transport along `here`
//! returns its value, and the telescope transport over `(y : A, z : Path(A,
//! a, y))` computes to its base case at `here(a)`. An identity at an atom
//! whose interface states no law is refused as
//! [`IdentityError::AtomTransport`].
//!
//! Elsewhere a bridge has no reflexivity, transport or eliminator: `here` is
//! refused at it by shape, and a bridge never converts with a path or a flow.

use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
use gandr_kernel_check_memo::CheckMemo;
use gandr_kernel_check_memo::ContentDigest;
use gandr_kernel_conversion_trace::ConversionDecision;
use gandr_kernel_strata::Level;
use gandr_kernel_term::AnyNode;
use gandr_kernel_term::CompType;
use gandr_kernel_term::CompTypeId;
use gandr_kernel_term::Computation;
use gandr_kernel_term::ComputationId;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::DeclarationContent;
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
use crate::env::AdmittedDeclaration;
use crate::env::Entries;
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
use crate::identity_recursion::Interfaces;
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
use crate::rewrite::substitute_value_type;
use crate::witness::value_type_witness;

#[cfg(test)]
mod bridge_tests;

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
    /// A bridge's domain reaches a sealed atom whose declaration states no
    /// interface: the relation between two elements of an abstract type is the
    /// abstraction's to choose, so no fold clause reads it.
    BridgeAtSealedType(ValueTypeWitness),
    /// An identity's domain reaches a sealed atom whose interface states a
    /// relation and its reflexivity but no law contracting its singletons, so
    /// its relation is not known to be an identity system.
    AtomTransport(ValueTypeWitness),
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
            Self::OutsideFold(_) => f.write_str("identity at a type outside the identity fold"),
            Self::EndpointsDiffer { .. } => f.write_str("reflexivity between differing endpoints"),
            Self::RelatedEndpointsDiffer { .. } => {
                f.write_str("a definition's related endpoints do not replay")
            },
            Self::NeutralFibre => f.write_str("an identity fibre is neutral"),
            Self::EmptyFibre => f.write_str("an identity fibre is empty"),
            Self::HigherFieldRequired => {
                f.write_str("an identity of universe paths needs a higher field")
            },
            Self::HigherEvaluationRequired => {
                f.write_str("an identity of functions needs a higher evaluation")
            },
            Self::RecursiveObservation => {
                f.write_str("a list identity needs a guarded observation")
            },
            Self::CertificateOperation => {
                f.write_str("a universe identity needs certificate evidence")
            },
            Self::Boundary => f.write_str("identity endpoints do not share a boundary"),
            Self::ZeroDepth => f.write_str("a higher field requests no layer"),
            Self::NonProductive(_) => f.write_str("non-productive higher field"),
            Self::DepthBound => f.write_str("a higher field exhausted its allowance"),
            Self::UnknownLayer(_) => f.write_str("a higher field names an absent layer"),
            Self::GuardEvidence => {
                f.write_str("a higher field's evidence does not match its guards")
            },
            Self::Coverage => f.write_str("a higher evaluation does not match its coverage"),
            Self::CoverageBudget => {
                f.write_str("higher-evaluation coverage exhausted its allowance")
            },
            Self::Evaluation { .. } => f.write_str("a higher evaluation's dialogue did not replay"),
            Self::OpenFunctions => f.write_str("a higher evaluation relates open functions"),
            Self::QuantifiedStep { .. } => {
                f.write_str("a quantified step does not apply its premise's functions at one input")
            },
            Self::HigherOrderDomain { .. } => f.write_str(
                "a quantified evaluation applies a function whose domain is higher order",
            ),
            Self::ReturnedNonReturner(_) => f.write_str("a returned endpoint over a non-returner"),
            Self::NotOver { .. } => f.write_str("an identity that does not lie over its path"),
            Self::BridgeAtSealedType(_) => f.write_str("a bridge at a sealed type"),
            Self::AtomTransport(_) => {
                f.write_str("an identity at a sealed type whose interface states no identity law")
            },
        }
    }
}

impl core::error::Error for IdentityError
{
}

/// Require a domain the identity fold reads in `mode`: closed, and reaching a
/// sealed atom only through the interface its declaration states.
///
/// # Specification
/// - requires: nothing.
/// - ensures: success exactly when the domain mentions no bound variable and,
///   in identity mode, reaches no sealed atom; in bridge mode every atom it
///   reaches states an interface, which [`require_unsealed`] has checked.
/// - provides: the guard every reading of the fold shares; at an open domain
///   the identity is its own neutral fibre, which no fold introduction
///   inhabits.
/// - fails: [`IdentityError::NeutralFibre`] at an open domain or at an atom
///   stating no interface; [`IdentityError::AtomTransport`] at an identity
///   reaching an atom whose interface states no law; `ArenaFault` for a domain
///   the arena does not hold.
/// - panics: none.
///
/// # Errors
/// As `fails`.
///
/// # Adequacy
/// - hypothesis: L3 — native evidence at the decode of a variable code and at a
///   sealed atom refuses as a neutral fibre, at an interfaced atom stating no
///   law by its missing law, while the same evidence at a closed Bool and at a
///   lawful atom checks.
/// - witness: `element_identity::tests::identity_at_an_open_type_is_a_neutral_fibre`
/// - witness: `element_identity::bridge_tests::an_interfaced_atom_bears_its_relation_as_its_bridge`
/// - witness: `element_identity::bridge_tests::a_lawful_atom_reads_its_relation_as_its_identity`
#[spec(ensures: |ret| ret.as_ref().map_or_else(
    |error| matches!(error, &(KernelError::Identity(IdentityError::NeutralFibre | IdentityError::AtomTransport(_)) | KernelError::ArenaFault)),
    |&()| arena.value_type(domain).is_some()))]
fn require_folded(
    arena: &TermArena,
    interfaces: Interfaces<'_>,
    mode: Mode,
    domain: ValueTypeId,
) -> Result<(), KernelError>
{
    if arena.value_type(domain).is_none() {
        return Err(KernelError::ArenaFault);
    }
    let reach = u32::from(arena.value_type_support(domain).depth());
    if reach != 0 {
        return Err(KernelError::Identity(IdentityError::NeutralFibre));
    }
    let atoms = crate::env::projected_atoms(arena, domain);
    match mode {
        Mode::Bridge => Ok(()),
        Mode::Identity if atoms.is_empty() => Ok(()),
        Mode::Identity
            if atoms.iter().all(|&atom| {
                interfaces
                    .of_atom(atom)
                    .is_some_and(|(interface, _)| matches!(interface.law(), Maybe::Present(_)))
            }) =>
        {
            Ok(())
        },
        Mode::Identity if atoms.iter().any(|&atom| interfaces.of_atom(atom).is_some()) => {
            Err(KernelError::Identity(IdentityError::AtomTransport(
                value_type_witness(arena, domain),
            )))
        },
        Mode::Identity => Err(KernelError::Identity(IdentityError::NeutralFibre)),
    }
}

/// Require a bridge's domain to reach a sealed atom only where the atom's
/// declaration states an interface.
///
/// # Specification
/// - requires: nothing.
/// - ensures: success exactly when `domain` resolves and every sealed atom it
///   reaches states an interface in `interfaces`.
/// - provides: the bridge's formation guard, and the first guard of every
///   bridge reading, so a sealed atom is refused by its own name before an open
///   domain is read as a neutral fibre.
/// - fails: [`IdentityError::BridgeAtSealedType`] naming the domain;
///   `ArenaFault` for a domain the arena does not hold.
/// - panics: none.
///
/// # Errors
/// As `fails`.
///
/// # Adequacy
/// - hypothesis: L3 — a bridge at an atom, at a function into an atom and at a
///   list of atoms refuses by name at formation where the atom states no
///   interface, and forms where it states one, as a bridge at Bool forms.
/// - witness: `element_identity::bridge_tests::a_bridge_at_a_sealed_type_is_refused`
/// - witness: `element_identity::bridge_tests::an_interfaced_atom_bears_its_relation_as_its_bridge`
#[spec(ensures: |ret| ret.as_ref().map_or_else(
    |error| matches!(error, &(KernelError::Identity(IdentityError::BridgeAtSealedType(_)) | KernelError::ArenaFault)),
    |&()| arena.value_type(domain).is_some()))]
pub(crate) fn require_unsealed(
    arena: &TermArena,
    interfaces: Interfaces<'_>,
    domain: ValueTypeId,
) -> Result<(), KernelError>
{
    if arena.value_type(domain).is_none() {
        return Err(KernelError::ArenaFault);
    }
    if crate::env::projected_atoms(arena, domain)
        .into_iter()
        .any(|atom| interfaces.of_atom(atom).is_none())
    {
        return Err(KernelError::Identity(IdentityError::BridgeAtSealedType(
            value_type_witness(arena, domain),
        )));
    }
    Ok(())
}

/// Require a domain the fold reads in `mode`: [`require_folded`], after
/// [`require_unsealed`] for a bridge.
///
/// # Specification
/// - requires: nothing.
/// - ensures: success exactly when both guards the mode owes succeed.
/// - provides: the one guard every reading of an identity or a bridge runs.
/// - fails: as the guards.
/// - panics: none.
///
/// # Errors
/// As `fails`.
///
/// # Adequacy
/// - hypothesis: L3 — as the two guards.
/// - witness: `element_identity::bridge_tests::a_bridge_at_a_sealed_type_is_refused`
/// - witness: `element_identity::tests::identity_at_an_open_type_is_a_neutral_fibre`
#[spec(ensures: |ret| ret.is_err() || arena.value_type(domain).is_some())]
fn require_read(
    arena: &TermArena,
    interfaces: Interfaces<'_>,
    mode: Mode,
    domain: ValueTypeId,
) -> Result<(), KernelError>
{
    if mode == Mode::Bridge {
        require_unsealed(arena, interfaces, domain)?;
    }
    require_folded(arena, interfaces, mode, domain)
}

/// The decode of `relation`'s code at two elements, `El(⟨force relation left
/// right⟩)` at `level`: the fibre of a bridge at an interfaced atom.
///
/// # Specification
/// - requires: `relation` is closed, and `left` and `right` stand in the
///   context the type is read in.
/// - ensures: the element type of the relation's returned code.
/// - provides: the one spelling of an atom's relation applied, which the atom's
///   admission checks reflexivity against and a bridge reading checks evidence
///   against.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a relation returning the unit code reads as the unit type
///   at any two elements.
/// - witness: `element_identity::bridge_tests::an_interfaced_atom_bears_its_relation_as_its_bridge`
#[spec(ensures: |ret| matches!(arena.value_type(ret), Some(&ValueType::Element { .. })))]
pub(crate) fn related_by(
    arena: &mut TermArena,
    relation: ValueId,
    (left, right): (ValueId, ValueId),
    level: Level,
) -> ValueTypeId
{
    let forced = arena.computation_force(relation);
    let applied = arena.computation_application(forced, left);
    let applied = arena.computation_application(applied, right);
    let code = arena.value_returned(applied);
    arena.value_type_element(code, level)
}

/// The types an atom's interface is checked at: its relation's, `U(R → R → F
/// kind)`, and its reflexivity's, `U(Π (x : R). F El(⟨relation x x⟩))`, over
/// the atom's representation `R`.
///
/// # Specification
/// - requires: `kind` is the value universe at `level`; `relation` is closed.
/// - ensures: the two thunk types, in that order.
/// - provides: the obligation the atom's admission discharges inside its seal,
///   where the atom reads as its representation.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a relation of the wrong shape, and a reflexivity that
///   does not inhabit the relation's diagonal, refuse at the atom's admission.
/// - witness: `element_identity::bridge_tests::an_interface_is_checked_where_its_atom_is_admitted`
#[spec(ensures: |ret| matches!(arena.value_type(ret.0), Some(&ValueType::Thunk(_))) && matches!(arena.value_type(ret.1), Some(&ValueType::Thunk(_))))]
pub(crate) fn interface_types(
    arena: &mut TermArena,
    (kind, level): (ValueTypeId, Level),
    representation: ValueTypeId,
    relation: ValueId,
) -> (ValueTypeId, ValueTypeId)
{
    let codes = arena.comp_type_returner(kind);
    let inner = arena.comp_type_arrow(representation, codes);
    let outer = arena.comp_type_arrow(representation, inner);
    let relations = arena.value_type_thunk(outer);
    let element = arena.value_variable(gandr_kernel_term::DeBruijnIndex::from(0_u32));
    let diagonal = related_by(arena, relation, (element, element), level);
    let witnessed = arena.comp_type_returner(diagonal);
    let reflexive = arena.comp_type_pi(representation, witnessed);
    (relations, arena.value_type_thunk(reflexive))
}

/// The type an atom's identity-system law is checked at, over the atom's
/// representation `R`: `U(Π (a : R). Π (b : R). Π (r : El(⟨relation a b⟩)).
/// F Path(Σ (y : R). El(⟨relation a y⟩), (b, r), (a, ⟨reflexivity a⟩)))`,
/// every element of the singleton at `a` identified with its centre.
///
/// # Specification
/// - requires: `relation` and `reflexivity` are closed and have checked at the
///   types [`interface_types`] gives at `level`.
/// - ensures: the thunk type above.
/// - provides: the obligation that makes the relation the atom's identity: by
///   _Homotopy Type Theory_, Theorem 5.8.2, a reflexive relation whose
///   singletons are contractible is an identity system, its eliminator and
///   transport derived from the law.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a law over a representation whose singletons contract
///   checks at the atom's admission; the same law over a representation whose
///   relation holds between distinct elements is refused there.
/// - witness: `element_identity::bridge_tests::a_lawful_atom_reads_its_relation_as_its_identity`
/// - witness: `element_identity::bridge_tests::a_law_is_checked_where_its_atom_is_admitted`
#[spec(ensures: |ret| matches!(arena.value_type(ret), Some(&ValueType::Thunk(_))))]
pub(crate) fn law_type(
    arena: &mut TermArena,
    level: &Level,
    representation: ValueTypeId,
    (relation, reflexivity): (ValueId, ValueId),
) -> ValueTypeId
{
    let var = |arena: &mut TermArena, index: u32| arena.value_variable(DeBruijnIndex::from(index));
    // Under `a`, `b` and `r`, and under the pair's binder `y` beneath them.
    let (a, y) = (var(arena, 3), var(arena, 0));
    let singleton = related_by(arena, relation, (a, y), level.clone());
    let pairs = arena.value_type_sigma(representation, singleton);
    let (a, b, r) = (var(arena, 2), var(arena, 1), var(arena, 0));
    let source = arena.value_tuple(&[b, r]);
    let forced = arena.computation_force(reflexivity);
    let diagonal = arena.computation_application(forced, a);
    let centre = arena.value_returned(diagonal);
    let centre = arena.value_tuple(&[a, centre]);
    let contracted = arena.value_type_path(pairs, source, centre);
    let returns = arena.comp_type_returner(contracted);
    // Under `a` and `b`: the relation between them.
    let (a, b) = (var(arena, 1), var(arena, 0));
    let related = related_by(arena, relation, (a, b), level.clone());
    let over_r = arena.comp_type_pi(related, returns);
    let over_b = arena.comp_type_pi(representation, over_r);
    let over_a = arena.comp_type_pi(representation, over_b);
    arena.value_type_thunk(over_a)
}

/// Relate a reflexivity's point to both endpoints of the identity it is
/// checked at: by the forced conversion, by taking an admitted result where
/// `taking` takes it, by the kernel's own evaluation when the side's dialogue
/// is the one decision `Evaluate` or `Admitted`, or else by replaying the
/// dialogue the reflexivity carries for that endpoint.
///
/// # Specification
/// - requires: `point`, both endpoints and every body in `unfoldings` live in
///   `arena`, the endpoints in the point's context.
/// - ensures: `Ok(())` exactly when, for each endpoint, the forced conversion
///   [`crate::conv::convert_values`] relates the point to it, or that side's
///   dialogue in `dialogues` derives their convertibility under `unfoldings`
///   and within [`ReplayBudget::DEFAULT`]. A dialogue of the one decision
///   `Admitted` relates them when `taking` takes the pair
///   ([`crate::admitted::Taking::take`]), and is otherwise read as `Evaluate`.
///   A dialogue of the one decision `Evaluate` derives it when
///   [`crate::replay::convert_unfolding`] converts the point and the endpoint,
///   closed or open over the point's context. Any other dialogue derives it
///   when it replays. `arena` holds what it held on entry.
/// - provides: the `here` rule's endpoint check. In a replayed dialogue a
///   constant unfolds only where the dialogue names it, at the head and side it
///   names, so a δ-step under a binder is a recorded step and never the
///   kernel's own search. An evaluated pair is the kernel's own search, bound
///   by the replay's budget, each variable of the context standing for itself.
///   A taken pair is the tier's answer, which the admission policy trusts.
/// - fails: [`IdentityError::EndpointsDiffer`] at the first endpoint neither
///   relates, naming that side and its verdict.
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
///   endpoint needs. A pair evaluating to one value is admitted by `Evaluate`,
///   closed or under a binder it reads, and refused when it evaluates apart. An
///   admitted closed pair evaluating apart is taken under the policy and
///   refused without it.
/// - witness: `element_identity::tests::reflexivity_converts_its_endpoints_by_the_laws_of_bind`
/// - witness: `element_identity::tests::an_endpoint_unfolding_under_a_thunk_replays_its_dialogue`
/// - witness: `element_identity::tests::a_dialogue_naming_the_wrong_unfolding_is_refused_by_name`
/// - witness: `element_identity::tests::a_pair_is_converted_by_the_kernel_s_own_evaluation_3557`
/// - witness: `element_identity::tests::an_admitted_result_is_taken_only_under_the_policy_3558`
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
    taking: crate::admitted::Taking<'_>,
    point: ValueId,
    (left, right): (ValueId, ValueId),
    dialogues: &EndpointDialogues,
) -> Result<(), KernelError>
{
    for (side, endpoint, dialogue) in [
        (EndpointSide::Left, left, &dialogues.left),
        (EndpointSide::Right, right, &dialogues.right),
    ] {
        if crate::conv::convert_values(arena, unfoldings.presentations(), point, endpoint)
            == Convertibility::Convertible
        {
            continue;
        }
        let verdict = match *dialogue.as_slice() {
            [ConversionDecision::Admitted]
                if taking.take(arena, point, endpoint) == crate::admitted::Took::Taken =>
            {
                KernelVerdict::Convertible
            },
            [ConversionDecision::Evaluate | ConversionDecision::Admitted] => {
                crate::replay::convert_unfolding(
                    arena,
                    unfoldings,
                    ReplaySides::Values(point, endpoint),
                    ReplayBudget::DEFAULT,
                )
            },
            _ => crate::replay::replay(
                arena,
                unfoldings,
                ReplaySides::Values(point, endpoint),
                EngineClaim::Convertible,
                dialogue.iter().copied().map(anchor),
                ReplayBudget::DEFAULT,
            ),
        };
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
///   outside the set-aside pairs diverges, a set-aside decode of a returned
///   code does not read as the type it is compared with, or a set-aside pair is
///   neither related by the forced reading nor α-equal, in either orientation,
///   to a related pair; [`crate::replay::EndpointReading::Converts`] when every
///   set-aside decode reads as its other side and every set-aside pair is
///   related by the forced reading or its related pair's dialogue replays,
///   under `unfoldings` and within [`ReplayBudget::DEFAULT`], as a derivation
///   of convertibility. `arena` holds what it held on entry.
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
/// - witness: `element_identity::tests::a_definition_relating_compound_endpoints_admits_274`
/// - witness: `element_identity::tests::a_corrupted_relation_is_refused_by_name`
/// - witness: `element_identity::tests::a_decoded_endpoint_passes_exactly_where_its_code_reads_as_the_other_type`
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
    if crate::conv::related_pairs(arena, unfoldings.presentations(), goal, &mut pairs)
        == Convertibility::Distinct
    {
        return Ok(crate::replay::EndpointReading::Apart);
    }
    // One buffer for every pair's set-aside endpoints, cleared per pair.
    let mut pending = Vec::new();
    for set_aside in pairs {
        let (left, right) = match set_aside {
            crate::conv::SetAside::Values(left, right) => (left, right),
            crate::conv::SetAside::Decoded { .. } | crate::conv::SetAside::Codomains(_) => {
                if crate::replay::read_endpoints(
                    arena,
                    unfoldings,
                    &[set_aside],
                    ReplayBudget::DEFAULT,
                    crate::replay::StuckEndpoints::Structural,
                ) == crate::replay::EndpointReading::Converts
                {
                    continue;
                }
                return Ok(crate::replay::EndpointReading::Apart);
            },
        };
        pending.clear();
        if crate::conv::pending_endpoints(
            arena,
            unfoldings.presentations(),
            crate::conv::ConversionGoal::Value(left, right),
            &mut pending,
        ) == Convertibility::Convertible
            && crate::replay::read_endpoints(
                arena,
                unfoldings,
                &pending,
                ReplayBudget::DEFAULT,
                crate::replay::StuckEndpoints::Structural,
            ) == crate::replay::EndpointReading::Converts
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
///   fibre, or a fibre that needs a higher form: at a function domain, whose
///   fold fibre is the persisted identity itself, that is
///   [`IdentityError::HigherEvaluationRequired`], since redirecting to that
///   fibre would check the same goal again (#719).
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
///   is the unit fibre's identity, an open domain is a neutral fibre, and a
///   function identity has no first-order fibre.
/// - witness: `element_identity::tests::native_evidence_checks_against_the_fold_fibre`
/// - witness: `element_identity::tests::identity_at_an_open_type_is_a_neutral_fibre`
/// - witness: `element_identity::tests::a_tuple_at_a_function_identity_is_refused_719`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |&fibre| arena.value_type(fibre).is_some()))]
pub(crate) fn fibre(
    arena: &mut TermArena,
    interfaces: Interfaces<'_>,
    domain: ValueTypeId,
    left: ValueId,
    right: ValueId,
) -> Result<ValueTypeId, KernelError>
{
    let (fibre, fibers) = native_fibre(arena, interfaces, domain, left, right)?;
    if let Ok(crate::identity_recursion::Fiber::Function { .. }) = fibers.get(fibers.root()) {
        return Err(KernelError::Identity(
            IdentityError::HigherEvaluationRequired,
        ));
    }
    Ok(fibre)
}

/// The native type a bridge's evidence inhabits.
///
/// # Specification
/// - requires: both endpoints inhabit the domain; the checking machine
///   discharges those goals itself.
/// - ensures: the bridge fold's native fibre at the domain and endpoints: the
///   identity's fibre where the two readings agree, the relation type `U(El A →
///   El B → F U)` at a value universe, and one step of the relation lifting at
///   a list, its tails' bridge delayed as the persisted node.
/// - provides: the type the checking machine redirects an introduction form
///   checked at a bridge to.
/// - fails: [`IdentityError::BridgeAtSealedType`] at a domain reaching a sealed
///   atom; a neutral fibre at an open domain or at endpoints that are not
///   canonical; [`IdentityError::HigherEvaluationRequired`] at a function code,
///   whose fibre is the bridge itself, introduced only by a higher or a
///   quantified evaluation; [`IdentityError::OutsideFold`] at a domain the fold
///   has no clause for.
/// - panics: none.
///
/// # Errors
/// As `fails`, and `ArenaFault` on an unreadable node.
///
/// # Adequacy
/// - hypothesis: L3 — a pair of codes inhabits a bridge at the universe by a
///   relation thunk, two conses by their heads' fibre and their tails' bridge,
///   a function by no introduction form, and a sealed atom by none.
/// - witness: `element_identity::bridge_tests::a_bridge_at_the_universe_is_a_relation`
/// - witness: `element_identity::bridge_tests::a_bridge_at_a_recursive_code_is_the_relation_lifting`
/// - witness: `element_identity::bridge_tests::a_bridge_at_a_function_code_is_the_family_over_argument_bridges`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |&fibre| arena.value_type(fibre).is_some()))]
pub(crate) fn bridge_fibre(
    arena: &mut TermArena,
    interfaces: Interfaces<'_>,
    domain: ValueTypeId,
    left: ValueId,
    right: ValueId,
) -> Result<ValueTypeId, KernelError>
{
    require_read(arena, interfaces, Mode::Bridge, domain)?;
    let code = arena.value_quote(domain);
    let fibers = interpret(arena, interfaces, Mode::Bridge, Domain::Elements(code))
        .and_then(Interpretation::elements)
        .and_then(|relation| relation.evaluate(arena, left, right))
        .map_err(|error| read_refusal(arena, Mode::Bridge, error))?;
    if let Ok(crate::identity_recursion::Fiber::Function { .. }) = fibers.get(fibers.root()) {
        return Err(KernelError::Identity(
            IdentityError::HigherEvaluationRequired,
        ));
    }
    fibers
        .native(arena, interfaces)
        .map_err(|error| read_refusal(arena, Mode::Bridge, error))
}

/// The fibre of the identity at the dependent pair `Σ (x : first). second`
/// between `left` and `right`.
///
/// # Specification
/// - requires: `second` stands under one binder of `first`; both endpoints
///   inhabit the pair. The checking machine discharges those goals itself.
///   `entries` is the admission log the endpoints were checked under.
/// - ensures: `Σ (p : Path(first, l₀, r₀)). Path(second[r₀], ⟨tr(x. second, p,
///   l₁)⟩, r₁)`, each endpoint's components read by [`pair_components`].
///   Nothing about the pair's factors is read beyond their place, so an open
///   pair has the same fibre.
/// - provides: the type the checking machine redirects a pair checked at an
///   identity of a dependent pair to.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a pair of reflexivities inhabits the identity of a pair
///   with itself, one whose second path ends elsewhere is refused, and the
///   reflexivities of a declared pair's body's components inhabit its identity
///   with itself.
/// - witness: `element_identity::tests::a_pair_of_paths_inhabits_the_identity_of_a_dependent_pair`
#[spec(ensures: |ret| arena.value_type(ret).is_some())]
pub(crate) fn sigma_fibre<M>(
    arena: &mut TermArena,
    (table, memo): (&mut ContentTable, &mut M),
    entries: &Entries,
    (first, second): (ValueTypeId, ValueTypeId),
    (left, right): (ValueId, ValueId),
) -> ValueTypeId
where
    M: CheckMemo<RewriteSupport, RewriteOutcome>,
{
    let [left_first, left_second] = pair_components(arena, entries, left);
    let [right_first, right_second] = pair_components(arena, entries, right);
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

/// The fibre of the identity at the product of `parts` between `left` and
/// `right`, when a tuple is checked there.
///
/// # Specification
/// - requires: both endpoints inhabit the product of `parts`; `entries` is the
///   admission log the endpoints were checked under.
/// - ensures: `Path(A₀, l₀, r₀) × … × Path(Aₙ, lₙ, rₙ)`, each endpoint's
///   components read by [`tuple_components`]. Each factor's identity reads its
///   own fibre when a component is checked there, so a tuple of fold evidence
///   inhabits it as it inhabits the fold's product, and a tuple of `here`s or
///   of paths at the factors' own identities does too.
/// - provides: the type the checking machine redirects a tuple checked at an
///   identity of a product to.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a tuple of reflexivities inhabits the identity of a tuple
///   with itself, one whose path ends elsewhere is refused, and a tuple of fold
///   evidence still inhabits it.
/// - witness: `element_identity::tests::a_tuple_of_paths_inhabits_the_identity_of_a_product`
#[spec(ensures: |ret| arena.value_type(ret).is_some())]
pub(crate) fn product_fibre(
    arena: &mut TermArena,
    entries: &Entries,
    parts: &[ValueTypeId],
    (left, right): (ValueId, ValueId),
) -> ValueTypeId
{
    let lefts = tuple_components(arena, entries, left, parts);
    let rights = tuple_components(arena, entries, right, parts);
    let paths: Vec<ValueTypeId> = parts
        .iter()
        .zip(lefts.into_iter().zip(rights))
        .map(|(&part, (from, to))| arena.value_type_path(part, from, to))
        .collect();
    arena.value_type_product(&paths)
}

/// The two components of a dependent pair's inhabitant.
///
/// # Specification
/// - requires: `pair` inhabits a dependent pair; `entries` is the admission log
///   it was checked under.
/// - ensures: [`tuple_components`] of `pair` at two components.
/// - provides: the kernel's own δ-step at an endpoint, the one the checker's
///   reading of a declared pair takes: a body is admitted, so it is read, never
///   searched for.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`sigma_fibre`]; a declared pair relates by its body's
///   components, an axiom's projections do not unfold.
/// - witness: `element_identity::tests::a_pair_of_paths_inhabits_the_identity_of_a_dependent_pair`
/// - witness: `element_identity::tests::a_declared_pair_relates_by_its_body_s_components_337`
#[spec(ensures: |ret| ret.iter().all(|&component| arena.value(component).is_some()))]
fn pair_components(
    arena: &mut TermArena,
    entries: &Entries,
    pair: ValueId,
) -> [ValueId; 2]
{
    let head = admitted_head(arena, entries, pair);
    if let Some(&[first, second]) = arena.value(head).and_then(Value::components) {
        return [first, second];
    }
    [0_usize, 1_usize].map(|index| {
        let projected =
            arena.computation_tuple_projection(pair, gandr_kernel_term::Component::from(index));
        arena.value_returned(projected)
    })
}

/// The components of a tuple's inhabitant at the product of `parts`.
///
/// # Specification
/// - requires: `tuple` inhabits the product of `parts`; `entries` is the
///   admission log it was checked under.
/// - ensures: one component per factor: those of the written tuple that `tuple`
///   is, or that a declared constant's admitted body is, through a chain of
///   definitions whose bodies name a constant; when `tuple` is `⟨tr(x. A₀ × … ×
///   Aₙ, p, v)⟩` and `v` is such a tuple, its components each transported along
///   `p` in their own factor, `⟨tr(x. Aᵢ, p, vᵢ)⟩` — the product row of the
///   transport table, read at an endpoint; the projections `⟨tuple.0⟩` …
///   `⟨tuple.n⟩`, each the value it returns, otherwise.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`product_fibre`], and a tuple transported along a
///   univalence path at a product motive relates by its components' transports.
/// - witness: `element_identity::tests::a_tuple_of_paths_inhabits_the_identity_of_a_product`
#[spec(ensures: |ret| ret.len() == parts.len() && ret.iter().all(|&component| arena.value(component).is_some()))]
fn tuple_components(
    arena: &mut TermArena,
    entries: &Entries,
    tuple: ValueId,
    parts: &[ValueTypeId],
) -> Vec<ValueId>
{
    let head = admitted_head(arena, entries, tuple);
    if let Some(components) = arena.value(head).and_then(Value::components)
        && components.len() == parts.len()
    {
        return components.to_vec();
    }
    if let Some(&Value::Returned(formed)) = arena.value(head)
        && let Some(&gandr_kernel_term::Computation::PathTransport {
            motive,
            path,
            value,
        }) = arena.computation(formed)
        && let Some(&ValueType::Product(ref factors)) = arena.value_type(motive)
        && factors.len() == parts.len()
        && let moved = admitted_head(arena, entries, value)
        && let Some(components) = arena.value(moved).and_then(Value::components)
        && components.len() == factors.len()
    {
        let (factors, components) = (factors.to_vec(), components.to_vec());
        return factors
            .into_iter()
            .zip(components)
            .map(|(factor, component)| {
                let transported = arena.computation_path_transport(factor, path, component);
                arena.value_returned(transported)
            })
            .collect();
    }
    (0_usize .. parts.len())
        .map(|index| {
            let projected = arena
                .computation_tuple_projection(tuple, gandr_kernel_term::Component::from(index));
            arena.value_returned(projected)
        })
        .collect()
}

/// The value `value` is read as at an identity's endpoint: the admitted body
/// of the declared constant it names, through a chain of definitions whose
/// bodies name a constant, or itself.
///
/// # Specification
/// - requires: `entries` is the admission log `value` was checked under.
/// - ensures: `value` when it names no admitted definition; the first body
///   along the chain that is no constant otherwise.
/// - fails: never.
/// - panics: none.
///
/// # Termination
/// - reason: the `while let` loop takes one δ-step per turn, not recursion.
/// - measure: the admission position of the constant unfolded, which each step
///   must lower: a body names only declarations admitted before its own.
///
/// # Adequacy
/// - hypothesis: L3 — as [`pair_components`].
/// - witness: `element_identity::tests::a_declared_pair_relates_by_its_body_s_components_337`
#[spec(ensures: |ret| arena.value(ret).is_some() || ret == value)]
fn admitted_head(
    arena: &TermArena,
    entries: &Entries,
    value: ValueId,
) -> ValueId
{
    let mut head = value;
    let mut below = usize::from(entries.len());
    while let Some(&Value::Constant(constant)) = arena.value(head)
        && usize::from(constant) < below
        && let Some(&DeclarationContent::Def { body, .. }) = entries
            .get(usize::from(constant))
            .map(AdmittedDeclaration::content)
    {
        head = body;
        below = usize::from(constant);
    }
    head
}

/// The native fibre and the fibre graph it was read from.
///
/// # Specification
/// - requires: as [`fibre`].
/// - ensures: as [`fibre`], also returning the graph whose diagonal an
///   enclosing identity reads. A level whose fibre is the decode of a returned
///   code, a lawful atom's relation between two points, is read at the type the
///   code quotes ([`decoded_fibre`]); an identity there is read innermost out
///   in turn.
/// - fails: as [`fibre`].
/// - panics: none.
///
/// # Errors
/// As [`fibre`].
///
/// # Termination
/// - reason: `while` loops over the finite chain of nested identity domains,
///   restarted only when a decoded fibre is itself an identity; not recursion.
/// - measure: the chain length, which the inner loops record and consume; a
///   restart reads the code of a relation admitted before the atom whose fibre
///   it is, so the atoms a restart reaches descend.
///
/// # Adequacy
/// - hypothesis: L3 — as [`fibre`]; an identity of the paths of a lawful atom
///   reads the unit fibre through its relation's code.
/// - witness: `element_identity::tests::a_higher_field_checks_and_computes_square_symmetry`
/// - witness: `element_identity::bridge_tests::j_along_an_atom_s_evidence_into_an_identity_of_the_unit_type_returns_the_unit_1960`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |&(fibre, _)| arena.value_type(fibre).is_some()))]
fn native_fibre(
    arena: &mut TermArena,
    interfaces: Interfaces<'_>,
    domain: ValueTypeId,
    left: ValueId,
    right: ValueId,
) -> Result<(ValueTypeId, Fibers), KernelError>
{
    let mut enclosing = Vec::new();
    let mut base = (domain, left, right);
    loop {
        while let Some(&ValueType::Path {
            domain,
            left,
            right,
        }) = arena.value_type(base.0)
        {
            enclosing.push((base.1, base.2));
            base = (domain, left, right);
        }
        require_folded(arena, interfaces, Mode::Identity, base.0)?;
        let (mut fibre, mut fibers) = fold_fibre(arena, interfaces, base)?;
        loop {
            let Some((left, right)) = enclosing.pop()
            else {
                return Ok((fibre, fibers));
            };
            let left = diagonal_endpoint(arena, &fibers, left)?;
            let right = diagonal_endpoint(arena, &fibers, right)?;
            let domain = decoded_fibre(arena, interfaces, fibre);
            if let Some(&ValueType::Path { .. }) = arena.value_type(domain) {
                base = (domain, left, right);
                break;
            }
            (fibre, fibers) = fold_fibre(arena, interfaces, (domain, left, right))?;
        }
    }
}

/// `fibre` read at the type it quotes when it is the decode of a returned
/// code, the definitions `interfaces` admitted unfolding: the identity at a
/// lawful atom is the decode of its relation's code between the two points.
///
/// # Specification
/// - requires: `fibre` lives in `arena`, as every body `interfaces` admitted
///   does.
/// - ensures: the type the code normalizes to the quote of, by
///   [`crate::replay::read_decode`] within [`ReplayBudget::DEFAULT`], when
///   `fibre` is `El(c)` at a code `c` that is a returned computation; `fibre`
///   itself otherwise, and when the code reads to no quote.
/// - provides: the identity fold's reading of an atom's fibre as the type its
///   relation returns, which the checking machine reads the same way at an
///   identity's domain.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`native_fibre`].
/// - witness: `element_identity::bridge_tests::j_along_an_atom_s_evidence_into_an_identity_of_the_unit_type_returns_the_unit_1960`
#[spec(ensures: |ret| arena.value_type(ret).is_some() || ret == fibre)]
fn decoded_fibre(
    arena: &mut TermArena,
    interfaces: Interfaces<'_>,
    fibre: ValueTypeId,
) -> ValueTypeId
{
    let Some(&ValueType::Element { code, .. }) = arena.value_type(fibre)
    else {
        return fibre;
    };
    if !matches!(arena.value(code), Some(Value::Returned(_))) {
        return fibre;
    }
    let entries = interfaces.entries();
    let unfoldings = Unfoldings::new(
        entries
            .iter()
            .map(|entry| match *entry.content() {
                DeclarationContent::Def { body, .. } => crate::replay::Unfoldable::Body(body),
                DeclarationContent::Data { .. }
                | DeclarationContent::Codata { .. }
                | DeclarationContent::Axiom { .. }
                | DeclarationContent::AbstractType { .. } => crate::replay::Unfoldable::Opaque,
            })
            .collect(),
    )
    .identifying(entries);
    crate::replay::read_decode(arena, &unfoldings, code, ReplayBudget::DEFAULT).unwrap_or(fibre)
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
    interfaces: Interfaces<'_>,
    (domain, left, right): (ValueTypeId, ValueId, ValueId),
) -> Result<(ValueTypeId, Fibers), KernelError>
{
    let code = arena.value_quote(domain);
    let fibers = interpret(arena, interfaces, Mode::Identity, Domain::Elements(code))
        .and_then(Interpretation::elements)
        .and_then(|relation| relation.evaluate(arena, left, right))
        .map_err(|error| relation_refusal(arena, error))?;
    let fibre = fibers
        .native(arena, interfaces)
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
        Some(&Value::Here { .. }) => fibers
            .diagonal(arena)
            .map(|diagonal| diagonal.value)
            .map_err(|error| relation_refusal(arena, error)),
        Some(_) => Ok(endpoint),
        None => Err(KernelError::ArenaFault),
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
    interfaces: Interfaces<'_>,
    expected: ValueTypeId,
    program: &HigherProgram,
    evidence: &[ValueId],
) -> Result<Vec<(ValueId, ValueTypeId)>, KernelError>
{
    let (inner, left, right) = path_parts(arena, expected)?;
    let (base, base_left, base_right) = path_parts(arena, inner)?;
    let (fibre, fibers) = native_fibre(arena, interfaces, base, base_left, base_right)?;
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
            HigherLayer::Guard { tail } => Layer::Guard {
                evidence: guards
                    .next()
                    .ok_or(KernelError::Identity(IdentityError::GuardEvidence))?,
                tail: higher_id(tail)?,
            },
            HigherLayer::Redirect(target) => Layer::Redirect(higher_id(target)?),
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
/// - requires: `expected` is the identity or bridge the evaluation is checked
///   against; every body `unfoldings` holds is closed and admitted before it.
/// - ensures: one obligation per kernel-generated coverage pattern, after every
///   component's two dialogues replayed positively, unfolding only what
///   `unfoldings` defines. At a bridge the fold is read in bridge mode, so the
///   coverage binds argument bridges and the output evidence is owed at the
///   result's bridge.
/// - provides: the checking machine's reading of a higher evaluation, with no
///   nested check.
/// - fails: a shape mismatch when `expected` is neither an identity nor a
///   bridge; a bridge at a sealed type; a neutral fibre at an open domain; open
///   functions, coverage and replay refusals by name.
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
/// - witness: `element_identity::bridge_tests::a_bridge_at_a_function_code_is_the_family_over_argument_bridges`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |owed| owed.len() == components.len()))]
pub(crate) fn evaluation_obligations(
    arena: &mut TermArena,
    (unfoldings, interfaces): (&Unfoldings, Interfaces<'_>),
    expected: ValueTypeId,
    dialogues: &[EvaluationDialogues],
    components: &[EvaluationComponent],
) -> Result<Vec<ComponentObligation>, KernelError>
{
    let (mode, domain, left, right) = related_parts(arena, expected)?;
    require_read(arena, interfaces, mode, domain)?;
    if u32::from(arena.value_support(left).depth()) != 0
        || u32::from(arena.value_support(right).depth()) != 0
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
    interpret(arena, interfaces, mode, Domain::Elements(code))
        .and_then(Interpretation::elements)
        .and_then(|relation| {
            relation.evaluation_obligations(
                arena,
                (left, right),
                &HigherEvaluation(pointwise),
                (unfoldings, ReplayBudget::DEFAULT),
            )
        })
        .map_err(|error| read_refusal(arena, mode, error))
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
/// - witness: `element_identity::bridge_tests::a_quantified_evaluation_relates_under_a_bridge_premise`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |owed| !owed.is_empty()))]
pub(crate) fn quantified_obligations(
    arena: &mut TermArena,
    (unfoldings, interfaces): (&Unfoldings, Interfaces<'_>),
    expected: ValueTypeId,
    steps: &[QuantifiedStep],
    children: &[ValueId],
) -> Result<Vec<ComponentObligation>, KernelError>
{
    let (mode, domain, left, right) = related_parts(arena, expected)?;
    require_read(arena, interfaces, mode, domain)?;
    if u32::from(arena.value_support(left).depth()) != 0
        || u32::from(arena.value_support(right).depth()) != 0
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
            QuantifiedStep::Return(_) => Quantified::Return {
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
            QuantifiedStep::Apply { fibre, .. } => Quantified::Apply {
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
    interpret(arena, interfaces, mode, Domain::Elements(code))
        .and_then(Interpretation::elements)
        .and_then(|relation| {
            relation.quantified_obligations(
                arena,
                (left, right),
                &quantified,
                (unfoldings, ReplayBudget::DEFAULT),
            )
        })
        .map_err(|error| read_refusal(arena, mode, error))
}

/// How a checking goal against an identity or a bridge reads its value.
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
/// - ensures: [`GoalReading::Fibre`] exactly when `expected` is an identity or
///   a bridge type and `value` is an introduction form of the fold's fibres:
///   neither an identity form (`here`, univalence, a higher field, a higher
///   evaluation) nor a neutral that synthesizes its own type (a variable, a
///   constant, a returned endpoint, a static application).
/// - provides: the checking machine's redirect of fibre evidence. A neutral
///   inhabits an identity by its synthesized type, so conversion stays
///   structural and never computes a fibre.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the empty tuple inhabits identity at Bool between equal
///   endpoints, a variable of identity type checks by its own type, and a
///   returned path checks at its identity type where a returned unit does not;
///   a relation thunk inhabits a bridge at the universe through its fibre.
/// - witness: `element_identity::tests::native_evidence_checks_against_the_fold_fibre`
/// - witness: `element_identity::bridge_tests::a_bridge_at_the_universe_is_a_relation`
#[spec(ensures: |ret| ret == GoalReading::Written || matches!(arena.value_type(expected), Some(&(ValueType::Path { .. } | ValueType::Bridge { .. }))))]
#[must_use]
pub(crate) fn goal_reading(
    arena: &TermArena,
    value: ValueId,
    expected: ValueTypeId,
) -> GoalReading
{
    let fibre = matches!(
        arena.value_type(expected),
        Some(&(ValueType::Path { .. } | ValueType::Bridge { .. }))
    ) && !matches!(
        arena.value(value),
        None | Some(
            &(Value::Here { .. }
                | Value::Univalence { .. }
                | Value::Higher { .. }
                | Value::HigherEvaluation { .. }
                | Value::QuantifiedEvaluation { .. }
                | Value::Variable(_)
                | Value::Constant(_)
                | Value::Returned(_)
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
        Some(&ValueType::Path {
            domain,
            left,
            right,
        }) => Ok((domain, left, right)),
        _ => Err(KernelError::ValueShapeMismatch {
            expected: ExpectedValueShape::Path,
            actual: value_type_witness(arena, ty),
        }),
    }
}

/// The domain and endpoints of a type `here` checks at: an identity, or a
/// bridge at a sealed atom whose interface states reflexivity.
///
/// # Specification
/// - ensures: the three parts of a `Path` type, or of a `Bridge` type whose
///   domain is an atom stating an interface in `interfaces`.
/// - provides: the `here` rule's reading of its type: the interface's
///   reflexivity, checked at the atom's admission, is the evidence a bridge at
///   the atom between a point and itself has.
/// - fails: a value-shape mismatch naming the type otherwise.
/// - panics: none.
///
/// # Errors
/// As `fails`.
///
/// # Adequacy
/// - hypothesis: L3 — `here` checks at a bridge at an interfaced atom, and is
///   refused at a bridge at Bool by shape.
/// - witness: `element_identity::bridge_tests::an_interfaced_atom_bears_its_relation_as_its_bridge`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |&(domain, left, right)|
    matches!(arena.value_type(ty), Some(&(ValueType::Path { domain: d, left: l, right: r } | ValueType::Bridge { domain: d, left: l, right: r })) if d == domain && l == left && r == right)))]
pub(crate) fn reflexive_parts(
    arena: &TermArena,
    interfaces: Interfaces<'_>,
    ty: ValueTypeId,
) -> Result<(ValueTypeId, ValueId, ValueId), KernelError>
{
    if let Some(&ValueType::Bridge {
        domain,
        left,
        right,
    }) = arena.value_type(ty)
        && let Some(&ValueType::Abstract(atom)) = arena.value_type(domain)
        && interfaces.of_atom(atom).is_some()
    {
        return Ok((domain, left, right));
    }
    path_parts(arena, ty)
}

/// The reading, domain and endpoints of an identity or a bridge type.
///
/// # Specification
/// - ensures: [`Mode::Identity`] and the three parts of a `Path` type, or
///   [`Mode::Bridge`] and the three parts of a `Bridge` type.
/// - provides: the one dispatch the higher and quantified evaluations read, so
///   both introduce a bridge by the bridge fold and an identity by the identity
///   fold.
/// - fails: a value-shape mismatch naming the type otherwise.
/// - panics: none.
///
/// # Errors
/// As `fails`.
///
/// # Adequacy
/// - hypothesis: L3 — a higher evaluation at a bridge reads the bridge fold,
///   and one at a base type refuses by shape.
/// - witness: `element_identity::bridge_tests::a_bridge_at_a_function_code_is_the_family_over_argument_bridges`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |&(mode, domain, left, right)| match mode {
    Mode::Identity => matches!(arena.value_type(ty), Some(&ValueType::Path { domain: d, left: l, right: r }) if d == domain && l == left && r == right),
    Mode::Bridge => matches!(arena.value_type(ty), Some(&ValueType::Bridge { domain: d, left: l, right: r }) if d == domain && l == left && r == right),
}))]
pub(crate) fn related_parts(
    arena: &TermArena,
    ty: ValueTypeId,
) -> Result<(Mode, ValueTypeId, ValueId, ValueId), KernelError>
{
    match arena.value_type(ty) {
        Some(&ValueType::Path {
            domain,
            left,
            right,
        }) => Ok((Mode::Identity, domain, left, right)),
        Some(&ValueType::Bridge {
            domain,
            left,
            right,
        }) => Ok((Mode::Bridge, domain, left, right)),
        _ => Err(KernelError::ValueShapeMismatch {
            expected: ExpectedValueShape::Path,
            actual: value_type_witness(arena, ty),
        }),
    }
}

/// Translate a fold refusal read in `mode` into the kernel's refusal
/// vocabulary.
///
/// # Specification
/// - ensures: a bridge reading's sealed-atom refusal is
///   [`IdentityError::BridgeAtSealedType`] naming the atom; every other refusal
///   is [`relation_refusal`]'s.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a function into a sealed atom read in bridge mode reaches
///   the bridge's name.
/// - witness: `element_identity::bridge_tests::a_bridge_at_a_sealed_type_is_refused`
#[spec(captures: sealed = mode == Mode::Bridge && matches!(error, RelationError::AbstractInterface(_)),
    ensures: |ret| !sealed || matches!(ret, KernelError::Identity(IdentityError::BridgeAtSealedType(_))))]
fn read_refusal(
    arena: &TermArena,
    mode: Mode,
    error: RelationError,
) -> KernelError
{
    match (mode, error) {
        (Mode::Bridge, RelationError::AbstractInterface(ty)) => KernelError::Identity(
            IdentityError::BridgeAtSealedType(value_type_witness(arena, ty)),
        ),
        (Mode::Identity | Mode::Bridge, error) => relation_refusal(arena, error),
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
        RelationError::UnsupportedType(ty) => {
            IdentityError::OutsideFold(value_type_witness(arena, ty))
        },
        // The fold refuses a sealed atom for want of its interface; every
        // reading here meets that domain as open first, where the identity is
        // its own neutral fibre.
        RelationError::AbstractInterface(_) | RelationError::NeutralFiber => {
            IdentityError::NeutralFibre
        },
        RelationError::AtomTransport(ty) => {
            IdentityError::AtomTransport(value_type_witness(arena, ty))
        },
        RelationError::Typing(error) | RelationError::Pointwise(_, error) => return *error,
        RelationError::Path(error) => return KernelError::Path(*error),
        RelationError::Evidence => IdentityError::EmptyFibre,
        RelationError::HigherFieldRequired => IdentityError::HigherFieldRequired,
        RelationError::HigherEvaluationRequired => IdentityError::HigherEvaluationRequired,
        RelationError::RecursiveObservationRequired => IdentityError::RecursiveObservation,
        RelationError::CertificateOperationRequired => IdentityError::CertificateOperation,
        RelationError::Boundary => IdentityError::Boundary,
        RelationError::Coverage => IdentityError::Coverage,
        RelationError::Budget => IdentityError::CoverageBudget,
        RelationError::Evaluation(component, side, verdict) => IdentityError::Evaluation {
            component,
            side,
            verdict,
        },
        RelationError::QuantifiedStep(component) => IdentityError::QuantifiedStep { component },
        RelationError::HigherOrderDomain(component) => {
            IdentityError::HigherOrderDomain { component }
        },
        RelationError::Arena
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
        HigherError::Relation(error) => return relation_refusal(arena, error),
        HigherError::Path(error) => return KernelError::Path(*error),
        HigherError::Boundary => IdentityError::Boundary,
        HigherError::NonProductive(id) => match position(id) {
            Ok(layer) => IdentityError::NonProductive(layer),
            Err(_) => return KernelError::ArenaFault,
        },
        HigherError::UnknownLayer(id) => match position(id) {
            Ok(layer) => IdentityError::UnknownLayer(layer),
            Err(_) => return KernelError::ArenaFault,
        },
        HigherError::DepthBound => IdentityError::DepthBound,
        HigherError::ZeroDepth => IdentityError::ZeroDepth,
        HigherError::ExpectedEquivalence
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
/// - hypothesis: L3 — `here` transports to the value; a product, a record, a
///   sum and a list motive compute constructorwise, a list one cell per step;
///   the universe clause reaches native transport along any path but a returned
///   one, which sticks here for the word rows to run; a function motive along
///   `ua(e)` moves the function by the record's maps; a neutral path over a
///   dependent motive sticks.
/// - witness: `element_identity::tests::transport_on_here_is_the_identity_by_replay`
/// - witness: `element_identity::tests::transport_computes_through_the_fold_clauses`
/// - witness: `path_universe::tests::recursive_transport_tests::negation_moves_a_list_one_cell_at_a_time`
/// - witness: `element_identity::tests::a_function_moves_along_univalence_by_its_maps`
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
        Some(&Value::Here { .. }) => {
            return Ok(Reduction::Reduced(arena.computation_return(value)));
        },
        Some(_) => {},
        None => return Err(KernelError::ArenaFault),
    }
    if binder_use(arena, Family::Type(motive)) == BinderUse::Ignored {
        return Ok(Reduction::Reduced(arena.computation_return(value)));
    }
    let family = arena
        .value_type(motive)
        .cloned()
        .ok_or(KernelError::ArenaFault)?;
    match family {
        ValueType::Product(parts) => {
            let components = match arena.value(value) {
                Some(&Value::Tuple(ref components)) if components.len() == parts.len() => {
                    components.clone()
                },
                Some(_) => return Ok(Reduction::Stuck),
                None => return Err(KernelError::ArenaFault),
            };
            Ok(Reduction::Reduced(componentwise(
                arena,
                table,
                memo,
                Mover::Transport,
                (&parts, &components),
                path,
                Former::Tuple,
            )?))
        },
        ValueType::Record(parts) => {
            let components: Vec<ValueId> = match arena.value(value) {
                Some(&Value::Record(ref fields)) if fields.keys().eq(parts.keys()) => {
                    fields.values().copied().collect()
                },
                Some(_) => return Ok(Reduction::Stuck),
                None => return Err(KernelError::ArenaFault),
            };
            let labels: Vec<gandr_kernel_term::FieldLabel> = parts.keys().cloned().collect();
            let parts: Vec<ValueTypeId> = parts.values().copied().collect();
            Ok(Reduction::Reduced(componentwise(
                arena,
                table,
                memo,
                Mover::Transport,
                (&parts, &components),
                path,
                Former::Record(&labels),
            )?))
        },
        ValueType::Sum(parts) => {
            let (summand, payload) = match arena.value(value) {
                Some(&Value::Injection(summand, payload)) => (summand, payload),
                Some(_) => return Ok(Reduction::Stuck),
                None => return Err(KernelError::ArenaFault),
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
        ValueType::Element { code, target } => {
            let decoded = matches!(arena.value(code), Some(&Value::Variable(index)) if index == DeBruijnIndex::from(0_u32))
                && target == Level::zero();
            if decoded && let Some(reduct) = along_held(arena, table, memo, motive, (path, value)) {
                return Ok(Reduction::Reduced(reduct));
            }
            // A returned path is left to the word rows, which run it after
            // the rows that read a held path: native transport has no clause
            // for a returned path, and would stick on what the run returns.
            let universe_family =
                decoded && !matches!(arena.value(path), Some(&Value::Returned(_)));
            Ok(if universe_family {
                Reduction::Reduced(arena.computation_transport(path, value))
            }
            else {
                Reduction::Stuck
            })
        },
        ValueType::Path {
            domain,
            left,
            right,
        } => {
            let singleton = matches!(arena.value(right), Some(&Value::Variable(index)) if index == DeBruijnIndex::from(0_u32))
                && matches!(arena.value(value), Some(&Value::Here { .. }))
                && binder_use(arena, Family::Type(domain)) == BinderUse::Ignored
                && binder_use(arena, Family::Value(left)) == BinderUse::Ignored;
            Ok(if singleton {
                Reduction::Reduced(arena.computation_return(path))
            }
            else {
                Reduction::Stuck
            })
        },
        ValueType::List(element) => {
            let (head, tail) = match arena.value(value) {
                Some(&Value::ListNil) => {
                    return Ok(Reduction::Reduced(arena.computation_return(value)));
                },
                Some(&Value::ListCons(head, tail)) => (head, tail),
                Some(_) => return Ok(Reduction::Stuck),
                None => return Err(KernelError::ArenaFault),
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
        ValueType::Thunk(function_type) => {
            Ok(
                transported_function(arena, table, memo, function_type, (path, value))
                    .map_or(Reduction::Stuck, Reduction::Reduced),
            )
        },
        ValueType::Data { .. }
        | ValueType::Session { .. }
        | ValueType::PathUniverse(..)
        | ValueType::FlowUniverse(..)
        | ValueType::Flow { .. }
        | ValueType::Bridge { .. }
        | ValueType::Base(_)
        | ValueType::Sigma { .. }
        | ValueType::Universe { .. }
        | ValueType::Lift { .. }
        | ValueType::Abstract(_)
        | ValueType::StaticPi { .. }
        | ValueType::Staged { .. } => Ok(Reduction::Stuck),
    }
}

/// A path the transport table holds as the transport that formed it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Held
{
    /// `back(p)`: transport along `p` in `y. Path(D, y, c)` from `here(c)`.
    Back,
    /// `q then p`: transport along `p` in `y. Path(D, c, y)` from `q`.
    Then,
}

/// Read a path as a held `back` or `then` of a universe path.
///
/// # Specification
/// - requires: nothing; an ill-typed term reads as neither.
/// - ensures: `Some((shape, along, moved))` exactly when `path` is `⟨tr(P,
///   along, moved)⟩`, `P` a path type whose carrier and fixed endpoint ignore
///   the binder — the binder its left endpoint and `moved` a `here` for
///   [`Held::Back`], the binder its right endpoint and `moved` no `here` for
///   [`Held::Then`] — and `along` is `ua(e)` or a held path of its own whose
///   innermost path is.
/// - provides: the guard of the decode rows along `back` and `then`, which the
///   evaluator's held transports mirror.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — `back(ua(e))` reads as a `back` along `ua(e)`, `q then
///   ua(e)` as a `then`, and a transport along a variable as neither.
/// - witness: `element_identity::tests::transport_back_along_univalence_applies_the_left_inverse`
/// - witness: `element_identity::tests::transport_along_then_moves_along_both_paths`
#[spec(ensures: |ret| ret.is_none() || matches!(arena.value(path), Some(&Value::Returned(_))))]
fn held(
    arena: &TermArena,
    path: ValueId,
) -> Option<(Held, ValueId, ValueId)>
{
    let bound = |arena: &TermArena, endpoint| matches!(arena.value(endpoint), Some(&Value::Variable(index)) if index == DeBruijnIndex::from(0_u32));
    let mut read = None;
    let mut focus = path;
    while let Some(&Value::Returned(formed)) = arena.value(focus) {
        let Some(&gandr_kernel_term::Computation::PathTransport {
            motive,
            path: along,
            value: moved,
        }) = arena.computation(formed)
        else {
            return None;
        };
        let Some(&ValueType::Path {
            domain,
            left,
            right,
        }) = arena.value_type(motive)
        else {
            return None;
        };
        let here = matches!(arena.value(moved), Some(&Value::Here { .. }));
        let (shape, fixed) = if bound(arena, right) && !here {
            (Held::Then, left)
        }
        else if bound(arena, left) && here {
            (Held::Back, right)
        }
        else {
            return None;
        };
        if binder_use(arena, Family::Type(domain)) != BinderUse::Ignored
            || binder_use(arena, Family::Value(fixed)) != BinderUse::Ignored
        {
            return None;
        }
        read.get_or_insert((shape, along, moved));
        focus = along;
    }
    if matches!(arena.value(focus), Some(&Value::Univalence(_))) {
        read
    }
    else {
        None
    }
}

/// Transport at the universe's decode along a held `back` or `then`.
///
/// # Specification
/// - requires: `motive` is the decode of the motive's own binder at level zero.
/// - ensures: along `back(ua(e))`, the reduct `x ← e.1; l ← x.0; g ← l.0;
///   g(v)`, which applies the record's left inverse; along `back(back(p))`,
///   transport along `p` in `motive`; along `q then p`, transport along `p` in
///   `motive` of the returned transport along `q` in `motive`, which is pure,
///   so it is passed as the value it stands for. `None` for any other path.
/// - provides: the decode rows for the paths the evaluator holds as transports.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the left inverse, not the forward map, reaches the
///   operand along `back`, and the first path of a composite moves it before
///   the second; a swap changes the reduct.
/// - witness: `element_identity::tests::transport_back_along_univalence_applies_the_left_inverse`
/// - witness: `element_identity::tests::transport_along_then_moves_along_both_paths`
#[spec(ensures: |ret| ret.is_none_or(|reduct| arena.computation(reduct).is_some()))]
fn along_held<M>(
    arena: &mut TermArena,
    table: &mut ContentTable,
    memo: &mut M,
    motive: ValueTypeId,
    (path, value): (ValueId, ValueId),
) -> Option<ComputationId>
where
    M: CheckMemo<RewriteSupport, RewriteOutcome>,
{
    let (shape, along, moved) = held(arena, path)?;
    match shape {
        Held::Then => {
            let first = arena.computation_path_transport(motive, moved, value);
            let first = arena.value_returned(first);
            Some(arena.computation_path_transport(motive, along, first))
        },
        Held::Back => back_along(arena, table, memo, motive, (along, value)),
    }
}

/// Transport at the universe's decode back along a universe path.
///
/// # Specification
/// - requires: `motive` is the decode of the motive's own binder at level zero.
/// - ensures: back along `ua(e)`, the reduct `x ← e.1; l ← x.0; g ← l.0; g(v)`,
///   which applies the record's left inverse; back along a native equivalence
///   `equiv(f, g)`, the reduct `g(v)`; back along a held `back(p)`, transport
///   along `p` in `motive`. `None` for any other path.
/// - provides: the reverse half of the decode rows, which `back` and a
///   transported function's argument read.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the left inverse, not the forward map or the right
///   inverse, reaches the operand, and back along a `back` moves forward.
/// - witness: `element_identity::tests::transport_back_along_univalence_applies_the_left_inverse`
/// - witness: `element_identity::tests::a_function_moves_along_univalence_by_its_maps`
/// - witness: `element_identity::tests::a_function_moves_along_an_equivalence_by_its_maps`
#[spec(ensures: |ret| ret.is_none_or(|reduct| arena.computation(reduct).is_some()))]
fn back_along<M>(
    arena: &mut TermArena,
    table: &mut ContentTable,
    memo: &mut M,
    motive: ValueTypeId,
    (along, value): (ValueId, ValueId),
) -> Option<ComputationId>
where
    M: CheckMemo<RewriteSupport, RewriteOutcome>,
{
    match arena.value(along) {
        // `#{f, #{#{g, s}, #{h, r}}}`: the left inverse is `g`.
        Some(&Value::Univalence(record)) => {
            let bound = arena.value_variable(DeBruijnIndex::from(0_u32));
            let left = gandr_kernel_term::Component::from(0_usize);
            let inverses = arena
                .computation_tuple_projection(record, gandr_kernel_term::Component::from(1_usize));
            let section = arena.computation_tuple_projection(bound, left);
            let force = arena.computation_force(bound);
            let value = shift_value(
                arena,
                table,
                memo,
                value,
                BinderDepth::default(),
                BinderDepth::from(3_u32),
            );
            let applied = arena.computation_application(force, value);
            let applied = arena.computation_bind(section, applied);
            let applied = arena.computation_bind(section, applied);
            Some(arena.computation_bind(inverses, applied))
        },
        // A native equivalence carries its backward map.
        Some(&Value::PathEquiv { backward, .. }) => {
            let force = arena.computation_force(backward);
            Some(arena.computation_application(force, value))
        },
        _ => match held(arena, along)? {
            (Held::Back, inner, _) => Some(arena.computation_path_transport(motive, inner, value)),
            (Held::Then, ..) => None,
        },
    }
}

/// Transport of a function in `y. U(A(y) → F B(y))`, or of a suspension in
/// `y. U(F B(y))`, along a universe path.
///
/// # Specification
/// - requires: `function_type` is the motive's thunk type under its own binder.
/// - ensures: for a non-dependent arrow into a returner along `ua(e)`, a native
///   equivalence or a held `back` or `then`, the reduct `return thunk(λa. tr(B,
///   p, ⟨force f m⟩))`, the call moving as the value it returns as `then`'s
///   first leg does, or `return thunk(λa. force f m)` when `B` ignores the
///   binder; the argument `m` is `a` when `A` ignores the binder and `⟨tr(A,
///   back(p), a)⟩`, by [`back_along`], when `A` is the binder's decode and the
///   path reads back. For a returner along the same paths, `return thunk(tr(B,
///   p, ⟨force f⟩))`, or `return thunk(force f)` when `B` ignores the binder.
///   `None` for any other type, path or argument.
/// - provides: the cubical table's function row, as the evaluator's transported
///   function mirrors it.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the argument moves back by the left inverse and the
///   result forward by the forward map, a suspension's result forward alone;
///   moving the argument forward, by the right inverse, or leaving the result
///   where it is changes the reduct.
/// - witness: `element_identity::tests::a_function_moves_along_univalence_by_its_maps`
/// - witness: `element_identity::tests::a_function_moves_along_an_equivalence_by_its_maps`
#[spec(ensures: |ret| ret.is_none_or(|reduct| arena.computation(reduct).is_some()))]
fn transported_function<M>(
    arena: &mut TermArena,
    table: &mut ContentTable,
    memo: &mut M,
    function_type: CompTypeId,
    (path, function): (ValueId, ValueId),
) -> Option<ComputationId>
where
    M: CheckMemo<RewriteSupport, RewriteOutcome>,
{
    let (argument, codomain) =
        if let Some(&CompType::Arrow { domain, codomain }) = arena.comp_type(function_type) {
            (Some(domain), codomain)
        }
        else {
            (None, function_type)
        };
    let Some(&CompType::Returner(result)) = arena.comp_type(codomain)
    else {
        return None;
    };
    if !matches!(
        arena.value(path),
        Some(&(Value::Univalence(_) | Value::PathEquiv { .. }))
    ) && held(arena, path).is_none()
    {
        return None;
    }
    // A suspension runs, forced, and its result moves forward as the value
    // the run returns; no binder is crossed.
    let Some(argument) = argument
    else {
        let forced = arena.computation_force(function);
        let body = if binder_use(arena, Family::Type(result)) == BinderUse::Ignored {
            forced
        }
        else {
            let returned = arena.value_returned(forced);
            arena.computation_path_transport(result, path, returned)
        };
        let thunk = arena.value_thunk(body);
        return Some(arena.computation_return(thunk));
    };
    let one = BinderDepth::from(1_u32);
    let bound = arena.value_variable(DeBruijnIndex::from(0_u32));
    // Under `λa`, the argument moves back along the path as the value the
    // move returns.
    let moved = if binder_use(arena, Family::Type(argument)) == BinderUse::Ignored {
        bound
    }
    else {
        let decoded = matches!(
            arena.value_type(argument),
            Some(&ValueType::Element { code, ref target }) if *target == Level::zero()
                && matches!(arena.value(code), Some(&Value::Variable(index)) if index == DeBruijnIndex::from(0_u32))
        );
        if !decoded {
            return None;
        }
        let along = shift_value(arena, table, memo, path, BinderDepth::default(), one);
        let back = back_along(arena, table, memo, argument, (along, bound))?;
        arena.value_returned(back)
    };
    // The function applies to the moved argument, and the call's result
    // moves along the path as the value it returns, unless its type reads no
    // binder.
    let function = shift_value(arena, table, memo, function, BinderDepth::default(), one);
    let forced = arena.computation_force(function);
    let applied = arena.computation_application(forced, moved);
    let body = if binder_use(arena, Family::Type(result)) == BinderUse::Ignored {
        applied
    }
    else {
        let returned = arena.value_returned(applied);
        let result = shift_value_type(arena, table, memo, result, one, one);
        let forward = shift_value(arena, table, memo, path, BinderDepth::default(), one);
        arena.computation_path_transport(result, forward, returned)
    };
    let lambda = arena.computation_lambda(body);
    let thunk = arena.value_thunk(lambda);
    Some(arena.computation_return(thunk))
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
        Some(&CompType::Pi { domain, codomain }) => (domain, codomain),
        Some(_) => return Ok(Maybe::Absent(telescope_motive::Absent::Shape)),
        None => return Err(KernelError::ArenaFault),
    };
    let (family, innermost) = match arena.comp_type(inner) {
        Some(&CompType::Pi { domain, codomain }) => (domain, codomain),
        Some(_) => return Ok(Maybe::Absent(telescope_motive::Absent::Shape)),
        None => return Err(KernelError::ArenaFault),
    };
    let body = match arena.comp_type(innermost) {
        Some(&CompType::Returner(body)) => body,
        Some(_) => return Ok(Maybe::Absent(telescope_motive::Absent::Shape)),
        None => return Err(KernelError::ArenaFault),
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
/// - ensures: the value when the motive's returned type reads neither entry,
///   along any path, as the one-binder constant row; otherwise the value when
///   both identities are `here`; when only the path is `here(c)`, the
///   one-binder transport along the over identity in the fibre family `z. C[c,
///   z]`; along any other path, the unit when `C` is an identity at the unit
///   type; otherwise `Stuck`, as for a motive that is no telescope.
/// - provides: the replay's telescope transport computation.
/// - fails: `ArenaFault` on an unreadable motive layer, path or over identity.
/// - panics: none.
///
/// # Errors
/// As `fails`.
///
/// # Adequacy
/// - hypothesis: L3 — `here` along both identities returns the value; `here`
///   along the path transports in the fibre; a neutral path sticks; a closed
///   path that is no reflexivity returns the value in a motive constant in both
///   entries and sticks in one reading the endpoint at another carrier; into an
///   identity at the unit type, evidence, a variable and a constant all return
///   the unit.
/// - witness: `element_identity::tests::telescope_transport_along_here_reduces`
/// - witness: `element_identity::tests::j_derived_in_the_singleton_checks_and_computes`
/// - witness: `element_identity::tests::telescope_transport_in_a_constant_motive_returns_its_value_along_any_path`
/// - witness: `element_identity::tests::telescope_transport_into_the_unit_fibre_returns_the_unit_1886`
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
        Maybe::Present(Telescope { body, .. }) => body,
        Maybe::Absent(telescope_motive::Absent::Shape) => return Ok(Reduction::Stuck),
    };
    if binder_use(arena, Family::Type(body)) == BinderUse::Ignored {
        let unit = arena.value_unit();
        let outer = substitute_value_type(arena, table, memo, body, unit);
        if binder_use(arena, Family::Type(outer)) == BinderUse::Ignored {
            return Ok(Reduction::Reduced(arena.computation_return(value)));
        }
    }
    let point = match arena.value(path) {
        Some(&Value::Here { point, .. }) => point,
        Some(_) => {
            let carrier = match arena.value_type(body) {
                Some(&ValueType::Path { domain, .. }) => arena.value_type(domain),
                _ => None,
            };
            return Ok(match carrier {
                Some(&ValueType::Product(ref parts)) if parts.is_empty() => {
                    let centre = arena.value_unit();
                    Reduction::Reduced(arena.computation_return(centre))
                },
                _ => Reduction::Stuck,
            });
        },
        None => return Err(KernelError::ArenaFault),
    };
    match arena.value(over) {
        Some(&Value::Here { .. }) => Ok(Reduction::Reduced(arena.computation_return(value))),
        Some(_) => {
            let fibre = substitute_outer_value_type(arena, table, memo, body, point);
            Ok(Reduction::Reduced(
                arena.computation_path_transport(fibre, over, value),
            ))
        },
        None => Err(KernelError::ArenaFault),
    }
}

/// A telescope transport along a path that is no reflexivity, into a returned
/// type that reads as the unit type through the identities and lawful atoms
/// its carrier names: the unit.
///
/// # Specification
/// - requires: nothing; an ill-typed term sticks without panicking.
/// - ensures: the unit when the path is no `here` and the motive's returned
///   type is `Path(A, l, r)` at a carrier `A` whose identities
///   [`carrier_fibre`] reads as the unit type, so the fibre is the unit type at
///   every pair of endpoints; `Stuck` otherwise.
/// - provides: the replay's telescope transport row at a carrier that is an
///   identity or a lawful atom, which [`telescope_beta`] leaves stuck.
/// - fails: `ArenaFault` on an unreadable motive layer or path.
/// - panics: none.
///
/// # Errors
/// As `fails`.
///
/// # Adequacy
/// - hypothesis: L3 — evidence into the fibre of an atom whose relation returns
///   the unit type returns the unit, and into one whose relation returns an
///   identity of the unit type; the same transport over unfoldings identifying
///   no atom, or along `here`, sticks.
/// - witness: `element_identity::bridge_tests::j_along_a_lawful_atom_s_evidence_into_a_unit_fibre_returns_the_unit_1937`
/// - witness: `element_identity::bridge_tests::j_along_an_atom_s_evidence_into_an_identity_of_the_unit_type_returns_the_unit_1960`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |reduction| match *reduction {
    Reduction::Reduced(reduct) => arena.computation(reduct).is_some(),
    Reduction::Stuck => true,
}))]
pub(crate) fn unit_fibre_beta(
    arena: &mut TermArena,
    unfoldings: &crate::replay::Unfoldings,
    term: TelescopeStep,
) -> Result<Reduction, KernelError>
{
    if let Value::Here { .. } = *arena.value(term.path).ok_or(KernelError::ArenaFault)? {
        return Ok(Reduction::Stuck);
    }
    let body = match telescope(arena, term.motive)? {
        Maybe::Present(Telescope { body, .. }) => body,
        Maybe::Absent(telescope_motive::Absent::Shape) => return Ok(Reduction::Stuck),
    };
    let Some(&ValueType::Path { domain, .. }) = arena.value_type(body)
    else {
        return Ok(Reduction::Stuck);
    };
    if carrier_fibre(arena, unfoldings, domain) == Fibre::Unit {
        let centre = arena.value_unit();
        return Ok(Reduction::Reduced(arena.computation_return(centre)));
    }
    Ok(Reduction::Stuck)
}

/// What every identity at a carrier reads as, for J into its fibre.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Fibre
{
    /// The unit type: J into the fibre returns the unit.
    Unit,
    /// Any other type, or a chain the walk does not read.
    Other,
}

/// What every identity at `carrier` reads as.
///
/// # Specification
/// - requires: nothing — any type is admissible input.
/// - ensures: [`Fibre::Unit`] exactly when `carrier` is the unit type; an
///   identity whose own carrier's identities read so, since an identity of the
///   unit type is the unit type; or an atom the unfoldings identify by a
///   relation whose code [`relation_code`] reads as the unit type, or as an
///   identity at a carrier whose identities read so, each atom on the way
///   admitted before the last. The unit type itself always reads so.
/// - fails: never.
/// - panics: none.
///
/// # Termination
/// - reason: one `loop` over a chain of carriers, not recursion.
/// - measure: the identity nesting under the current carrier, which each
///   identity step lowers, and the admission position of the atom read, which
///   each atom step must lower.
///
/// # Adequacy
/// - hypothesis: L3 — as [`unit_fibre_beta`].
/// - witness: `element_identity::bridge_tests::j_along_an_atom_s_evidence_into_an_identity_of_the_unit_type_returns_the_unit_1960`
#[spec(ensures: |ret| ret == Fibre::Unit || !matches!(arena.value_type(carrier), Some(ValueType::Product(parts)) if parts.is_empty()))]
fn carrier_fibre(
    arena: &TermArena,
    unfoldings: &crate::replay::Unfoldings,
    carrier: ValueTypeId,
) -> Fibre
{
    let unit = |parts: &[ValueTypeId]| {
        if parts.is_empty() {
            Fibre::Unit
        }
        else {
            Fibre::Other
        }
    };
    let mut carrier = carrier;
    let mut ceiling = None;
    loop {
        match arena.value_type(carrier) {
            Some(&ValueType::Product(ref parts)) => return unit(parts),
            Some(&ValueType::Path { domain, .. }) => carrier = domain,
            Some(&ValueType::Abstract(atom)) => {
                if ceiling.is_some_and(|above| atom >= above) {
                    return Fibre::Other;
                }
                ceiling = Some(atom);
                let Some(code) = unfoldings
                    .identity(atom)
                    .and_then(|relation| relation_code(arena, unfoldings, relation))
                else {
                    return Fibre::Other;
                };
                match arena.value_type(code) {
                    Some(&ValueType::Product(ref parts)) => return unit(parts),
                    Some(&ValueType::Path { domain, .. }) => carrier = domain,
                    _ => return Fibre::Other,
                }
            },
            _ => return Fibre::Other,
        }
    }
}

/// The type whose code the relation `relation` returns outright: read through
/// the definitions it names, its thunk and its two λs, a body `return ⌜T⌝`
/// gives `T`.
///
/// # Specification
/// - requires: nothing — any value is admissible input.
/// - ensures: `Some(t)` exactly when `relation`, each constant it is replaced
///   by that constant's body while the positions descend, is a thunk of two λs
///   whose body returns the quote of `t`; `None` otherwise, a relation that
///   computes its code included.
/// - provides: the lawful atom row's reading of the relation, which reduces
///   nothing and so reads no term the replay would reduce.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`unit_fibre_beta`].
/// - witness: `element_identity::bridge_tests::j_along_a_lawful_atom_s_evidence_into_a_unit_fibre_returns_the_unit_1937`
/// - witness: `element_identity::bridge_tests::j_along_an_atom_s_evidence_into_an_identity_of_the_unit_type_returns_the_unit_1960`
#[spec(ensures: |ret| ret.is_none_or(|quoted| arena.value_type(quoted).is_some()))]
fn relation_code(
    arena: &TermArena,
    unfoldings: &crate::replay::Unfoldings,
    relation: ValueId,
) -> Option<ValueTypeId>
{
    let mut held = relation;
    let mut ceiling = None;
    let thunked = loop {
        if let Some(&Value::Constant(constant)) = arena.value(held) {
            if ceiling.is_some_and(|above| constant >= above) {
                return None;
            }
            ceiling = Some(constant);
            let crate::replay::Unfoldable::Body(body) = unfoldings.unfolding(constant)
            else {
                return None;
            };
            held = body;
            continue;
        }
        if let Some(&Value::Thunk(body)) = arena.value(held) {
            break body;
        }
        return None;
    };
    let Some(&Computation::Lambda(first)) = arena.computation(thunked)
    else {
        return None;
    };
    let Some(&Computation::Lambda(second)) = arena.computation(first)
    else {
        return None;
    };
    let Some(&Computation::Return(code)) = arena.computation(second)
    else {
        return None;
    };
    match arena.value(code) {
        Some(&Value::Quote(quoted)) if arena.value_type(quoted).is_some() => Some(quoted),
        _ => None,
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
            Self::Transport => arena.computation_path_transport(motive, along, value),
            Self::Ride => arena.computation_ride(motive, along, value),
        }
    }
}

/// The former a componentwise move returns its moved components in.
#[derive(Clone, Copy, Debug)]
pub(crate) enum Former<'labels>
{
    /// A tuple, the components in order.
    Tuple,
    /// A record, one label per component in field order.
    Record(&'labels [gandr_kernel_term::FieldLabel]),
}

/// Move a tuple or a record componentwise: one bind per component, then the
/// `former` of the bound results.
///
/// # Specification
/// - requires: one component per motive part, and one label per component for a
///   record.
/// - ensures: `x₀ ← step(P₀, p, v₀); …; return (x₀, …)` for the `mover`'s step,
///   or `return #{l₀ = x₀, …}` for a record, each step's identity or flow and
///   component shifted past the binds outside it, and each part's outer
///   variables shifted past them as well.
/// - fails: `ArenaFault` for a component count past `u32`.
/// - panics: none.
///
/// # Errors
/// As `fails`.
///
/// # Adequacy
/// - hypothesis: L3 — a pair of a Bool and a universe element and a record of
///   them transport componentwise, and a pair rides componentwise along a
///   forward flow.
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
    former: Former<'_>,
) -> Result<ComputationId, KernelError>
where
    M: CheckMemo<RewriteSupport, RewriteOutcome>,
{
    let count = u32::try_from(components.len()).map_err(|_overflow| KernelError::ArenaFault)?;
    let mut bound = Vec::with_capacity(components.len());
    for position in (0 .. count).rev() {
        bound.push(arena.value_variable(DeBruijnIndex::from(position)));
    }
    let assembled = match former {
        Former::Tuple => arena.value_tuple(&bound),
        Former::Record(labels) => arena.value_record(labels.iter().cloned().zip(bound).collect()),
    };
    let mut reduct = arena.computation_return(assembled);
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
/// - ensures: [`BinderUse::Ignored`] exactly when the support the family's node
///   carries from its mint lists its indices and zero is not among them
///   ([`crate::support::innermost`]); a support reading every binder answers
///   [`BinderUse::Read`].
/// - provides: the constant-motive rule, decided on the carried support with no
///   instantiation and no walk.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a Bool motive and one over an outer variable are
///   constant; `El(x)` reads its binder.
/// - witness: `element_identity::tests::transport_computes_through_the_fold_clauses`
#[spec(captures: closed = match family {
        Family::Type(ty) => u32::from(arena.value_type_support(ty).depth()) == 0,
        Family::Value(value) => u32::from(arena.value_support(value).depth()) == 0,
    },
    ensures: |ret| !closed || ret == BinderUse::Ignored)]
pub(crate) fn binder_use(
    arena: &TermArena,
    family: Family,
) -> BinderUse
{
    crate::support::innermost(match family {
        Family::Type(ty) => arena.value_type_support(ty),
        Family::Value(value) => arena.value_support(value),
    })
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
        Some(&Value::Here {
            point: function, ..
        }) => function,
        Some(_) => return Ok(Reduction::Stuck),
        None => return Err(KernelError::ArenaFault),
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
