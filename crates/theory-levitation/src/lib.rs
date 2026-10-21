//! The first-order code universe of gandr's levitated descriptions: codes,
//! the declaration table they populate, and the generic programs and checks
//! driven by it.
//!
//! A [`Code`] is one constructor's payload shape in the fragment
//! `{1, var, ×, σ}` with two leaf decorations: a field over a symbolic value
//! type ([`ValueTypeRef`]) carrying a grade and an attribute Σ, and an
//! atom-abstraction. The fragment is first-order, so code equality is
//! decidable and [`Code`] derives it. A [`TheoryDesc`] is the declaration table
//! for one signature: its minted identity, its sort set, its graded
//! parameters, its constructors (the σ tag over codes), its operations with
//! multi-output [`BridgeArity`] shapes, its rule faces ([`RuleFace`]) over
//! free terms ([`FreeTerm`]), and its circuit rules ([`CircuitRule`]), whose
//! boundary pair is derived from a wiring ([`derive_boundaries`]) and whose
//! filler elaborates to a whiskered composite ([`elaborate_body`]).
//!
//! The generic programs — [`generic_eq`], [`serialize_value`] and
//! [`serialize_desc`] — read any description, declared or retrofitted
//! ([`bool_desc`], [`option_desc`], [`list_desc`], [`pair_desc`],
//! [`sum_desc`]), uniformly. [`check_desc`] is the host-side well-formedness
//! pass, and [`TypedRuleFace`] pairs a face with a signature context decoded
//! by a caller-supplied decoder. [`theory_desc`] describes `Theory`, the
//! datatype whose values are presentations: a [`TheoryValue`] is one, and its
//! canonical bytes are the presentation's identity (the decisions are in
//! `theory`).
//!
//! The crate names no type of any other gandr crate. A field's grade is the
//! type parameter `G` of [`Code`] and [`TheoryDesc`], and a decoded type is the
//! type parameter of [`PatternContext`]; decoding a code into a core type
//! universe belongs to the consumer that owns that universe. Every recursive
//! datum — a code, a value type reference, a free term, a payload, a
//! whiskered composite — is held flat, so no walk over one recurses.
//!
//! The crate is `no_std` and depends on `core`, `alloc` and the shape
//! vocabulary of `quenchant-shape`.
//!
//! # The generalized logical framework
//!
//! Kaposi and Xie's second-order generalized algebraic theories present a
//! theory with binding by a signature; Kovács and Sattler's generalized
//! logical framework reads that one signature through two models. The crate
//! carries the fragment of that reading the rest of gandr needs first:
//!
//! - **Generation.** A signature marks each sort that may be bound
//!   ([`Representability`]) and each restricted binder (`pi+`, a port's binder
//!   telescope), and [`check_desc`] refuses a binder over a sort that is not
//!   representable. [`first_order()`] folds the signature, once, into its
//!   single-substitution first-order model: contexts and substitutions,
//!   per-sort variables, weakening, single substitution and lifting, the
//!   substitution laws for each representable sort, and each operation with its
//!   context explicit and one naturality law. The fold's own decisions are in
//!   `first_order`.
//! - **Two views.** For a simply-sorted signature, [`SimplySorted`] identifies
//!   binding syntax with the generated model's canonical terms
//!   ([`FirstOrderJudgement`]), and evaluates it into a value domain and reads
//!   it back ([`Evaluation`]), from the declarations alone (`binding`).
//! - **The face theory as a parameter.** A signature may state the finite shape
//!   its cells are stated over ([`TheoryShape`]): a size and named faces, each
//!   the subshape of the points it lists, after `FaceTT`'s shape parameter.
//!   [`check_desc`] refuses a face past its shape or named twice, `Theory`
//!   codes the shape, and [`serialize_desc`] renders it as the `theory` block's
//!   first member. Reading a face as a subshape, and deciding inclusions
//!   between faces, is `gandr-theory-shapes`'s, at the consumer: this crate is
//!   the closed tier below.
//!
//! The fragment is the framework's rule at one depth over closed finitary
//! signatures: a binder's domain is a representable sort, and a signature is
//! a finite table, never itself a term. Equality is intensional conversion
//! where the papers have extensional equality, and universes are stratified
//! levels where they have a type of types. "Internal" means the crate's own
//! code universe and evaluation machinery.
//!
//! - **Alternatives.** Two-level type theory as the organising frame puts the
//!   object theory inside a meta-level theory the kernel would have to carry;
//!   two models over one signature need only the signature table the crate
//!   already holds. An interpreter per signature (one for λ-calculus, one for
//!   computations) repeats one evaluation per signature and lets a name select
//!   a case; the one generic interpreter reads arities only, and a witness over
//!   three signatures that share no name holds it to that.
//! - **Reversal.** A binder over a sort that is not representable, or a
//!   signature that is itself a term (open or infinitary), needs the general
//!   rule and reopens the fragment; a theory that needs extensional equality at
//!   its use site needs the papers' model, not conversion.
//!
//! The model's equations are carried, not oriented: the identification is with
//! canonical terms, and deciding whether two arbitrary first-order terms are
//! equal in the model owes a normalizer the crate does not provide. A sort
//! indexed by another sort's terms is generated and checked, but its
//! evaluation waits on dependent pairs in the value domain.
//!
//! # The closed tier
//!
//! The crate depends on no other crate of the workspace, so no wrapper in its
//! signatures belongs to a crate a dependent's manifest does not name, and it
//! re-exports none. The field leaf is the one place a core notion meets the
//! code universe, and it enters as a type parameter: a field carries a grade
//! `G` the consumer supplies, and its value type stays this crate's own
//! symbolic reference (`ValueTypeRef` over `PrimTy` and declared heads), which
//! is all the generic programs, the arity naming and the rendering read. The
//! crate is `no_std`, so it cannot name a `std` collection; the compiler holds
//! that line. The kernel crates are development dependencies for one witness
//! only: a generated judgement is mapped into the kernel's arena and admitted
//! (`tests::glf::model::kernel`); the library names neither.
//!
//! - **Alternatives.** Depending on the core term crate for its grade and value
//!   types puts a core edge under a theory crate, inverting the layering, and
//!   lets a dependent reach that crate through re-exported wrappers. A
//!   whole-leaf parameter `Field(L)` would lose `PrimTy` and the symbolic value
//!   type that operation arities, the inspection rendering and the leaf-shift
//!   certificate read. A trait declared here and implemented in the core tier
//!   is an abstraction with one implementation.
//! - **Reversal.** A reordering of the categories that puts the core tier below
//!   the theory tier returns the field leaf to the core's own grade and value
//!   types.
//!
//! # The integration suites
//!
//! Three suites check the crate against the laws its consumers rely on, with
//! the machinery the crate leaves to them supplied as test support.
//!
//! - **The framework's checks** (`tests::glf`). Generation compares the fold's
//!   output with the single-substitution presentation derived by hand
//!   (`tests::glf::generation`). Identification, both views and the kernel
//!   check run 256 generated cases per signature (`tests::glf::model`), and the
//!   three-signature property runs one implementation over signatures that
//!   share no sort or operation name.
//! - **Certificates** (`tests::code_iso`). A certificate is a pair of value
//!   translators between two monomorphic descriptions, judged by replaying its
//!   round trips against `generic_eq`; its identity is replay-equivalence, the
//!   shape of a protype isomorphism. Identity, inverse and composition form a
//!   groupoid up to replay, and `generic_eq`, `serialize_value` and a
//!   content-addressed code table transport across every certificate. Two
//!   guards stand: negation and the identity share their boundary codes yet
//!   replay differently, so the identity of certificates is never code
//!   equality; and over a one-constructor description with an unbounded
//!   `Integer` leaf, the successor shift is a valid certificate distinct from
//!   the only structural one, so a completeness claim about certificates ranges
//!   over translators uniform in leaf contents.
//! - **The virtual double category dictionary** (`tests::vdc_dictionary`).
//!   Objects are tuples of real descriptions, tight arrows renamings of real
//!   symbols checked against their real codes and arities, and restriction
//!   recomputes real faces. The tight category holds strictly; cell composition
//!   and the cartesian structure hold up to replay; restriction holds in the
//!   split form by construction, with the face action split on `RuleFace`
//!   itself; units hold β on `refl`, and path induction declines on a non-empty
//!   path, which locates an obligation on a cell store: instances closed under
//!   path action. The matcher, substitution, rewriter and signature morphism
//!   the suite uses are test support; the crate ships none of them
//!   (`tests::vdc_dictionary::law3_restriction::matching_and_substitution_are_supplied_test_side`,
//!   `tests::vdc_dictionary::law1_tight::check_morphism_accepts_a_role_matched_renaming`).
//!
//! Executable specifications check structural relationships, ordering and
//! multiplicity, variable provenance, budget refusal and encoding layout. Each
//! nontrivial item's `# Adequacy` names the observations, defect classes,
//! evidence rung and boundary its witnesses establish. Contracts also cover the
//! certificate and dictionary harnesses: their composition, substitution and
//! refusal paths must not silently weaken the laws they test. Const extent
//! arithmetic checks its primitive fields directly, with constant-evaluation
//! and runtime boundary witnesses. Opaque-iterator items document the
//! instrumentation boundary; formatting documents its write-only sink. A
//! predicate over an observable projection does not claim the unobservable
//! remainder of a contract.
//!
//! Test prose names items plainly: the suites carry no intra-doc links, which
//! rustdoc does not check in a test target.
//!
//! # Consumers
//!
//! The virtual-doctrine reflection retains real `TheoryDesc<G>` values and uses
//! the public flat-tree representation for signatures, protypes, proterms and
//! derivations. It does not decode grades or introduce a second description
//! format.
//!
//! The cell layer reads the declaration table, its operations' arities, its
//! rule faces and its circuit rules: it elaborates a description into cells and
//! instantiates circuit rules at an application, through `TheoryDesc`,
//! `OperDesc`, `BridgeArity`, `DeclPolarity`, `RuleFace`, `FreeTerm`,
//! `CircuitRule`, `CircuitBody`, `WhiskeredCell`, `RedexOccurrence`,
//! `elaborate_body`, `redex_occurrences` and `derive_boundaries`. The surface's
//! description route lowers declarations into the table, runs `check_desc`, and
//! decodes codes into core types on its core side.
//!
//! # References
//!
//! - Guillaume Allais, Robert Atkey, James Chapman, Conor `McBride`, and James
//!   `McKinna`. "A Type- and Scope-Safe Universe of Syntaxes with Binding:
//!   Their Semantics and Proofs." _Journal of Functional Programming_ 31
//!   (2021), e22. `arXiv:2001.11001` — one evaluation, generic over a
//!   description of syntax with binding, which `SimplySorted` instantiates with
//!   a value domain and a readback.
//! - James Chapman, Pierre-Évariste Dagand, Conor `McBride`, and Peter Morris.
//!   "The Gentle Art of Levitation." In _Proceedings of the 15th ACM SIGPLAN
//!   International Conference on Functional Programming (ICFP '10)_, pages
//!   3–14, September 2010. `doi:10.1145/1863543.1863547` — the universe of
//!   datatype descriptions as an inductive object, generic programs driven by a
//!   description, and the staging that keeps the meta-theory functions
//!   host-side until each moves deliberately.
//! - Nicola Gambino and Joachim Kock. "Polynomial Functors and Polynomial
//!   Monads." _Mathematical Proceedings of the Cambridge Philosophical Society_
//!   154, 1 (2013), pages 153–192. `arXiv:0906.4931` — the presentation of a
//!   polynomial by finite sets and maps, `Σ_t ∘ Π_π ∘ Δ_s`, which `BridgeArity`
//!   stores as the bridge diagram `A ←s— J —π→ I —t→ B`.
//! - Ambrus Kaposi and Szumi Xie. "Second-Order Generalised Algebraic Theories:
//!   Signatures and First-Order Semantics." In _9th International Conference on
//!   Formal Structures for Computation and Deduction (FSCD 2024)_, `LIPIcs`
//!   299, paper 10. `doi:10.4230/LIPIcs.FSCD.2024.10` — the signatures with
//!   restricted binding over representable sorts, and the single-substitution
//!   first-order model `first_order` generates.
//! - András Kovács and Christian Sattler. "A Generalized Logical Framework."
//!   Extended abstract, TYPES 2025 — one signature read through a first-order
//!   and an internal model, the two views `binding` identifies.
//! - Hayato Nasu. _Logical Aspects of Virtual Double Categories_. Preprint,
//!   January 2025. `arXiv:2501.17869` — the split cartesian fibrant virtual
//!   double category (Definition 3.2.6) and its splitness lemma (Lemma 3.2.8),
//!   whose laws the dictionary suite checks on this crate's structures, and
//!   protype isomorphisms (§ 3.2.3), the shape of the certificate suite's value
//!   translators.
//! - Maximilian Schönlank, Andreas Nuyts and Dominique Devriese. "Towards
//!   `FaceTT`: a generalization of intensional type systems with glue". TYPES
//!   2026, abstract 42 — the shape parameter `ft` and its subshapes, which
//!   [`TheoryShape`] states for a signature.

// Module documentation that predates the shape lint: 26 headings outside the
// vocabulary, 10 decision records and 7 budgets exceeded. Each allow leaves
// with the rewrite that clears its count.
#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    allow(
        module_doc_heading,
        doc_decision_record,
        module_doc_budget,
        reason = "module documentation that predates the shape lint"
    )
)]
#![no_std]

extern crate alloc;

mod arity;
mod binding;
mod boundary;
mod builtin;
mod circuit;
mod code;
mod desc;
mod elaborate;
mod first_order;
mod generic;
mod rule;
mod termination;
mod theory;
pub mod tree;
mod typed_rule;
mod wellformed;

pub use crate::arity::BridgeArity;
pub use crate::arity::SortRef;
pub use crate::binding::AdmissionError;
pub use crate::binding::BindingError;
pub use crate::binding::BindingJudgement;
pub use crate::binding::BindingTerm;
pub use crate::binding::Evaluation;
pub use crate::binding::FirstOrderJudgement;
pub use crate::binding::SimplySorted;
pub use crate::boundary::AttributeEmptiness;
pub use crate::boundary::AttributePresence;
pub use crate::boundary::CircuitNodeBudget;
pub use crate::boundary::ConstructorTag;
pub use crate::boundary::ContextTotality;
pub use crate::boundary::DiagnosticMessage;
pub use crate::boundary::FirstOrderStatus;
pub use crate::boundary::GenericEquality;
pub use crate::boundary::LeafBytes;
pub use crate::boundary::MonomialCount;
pub use crate::boundary::NameRef;
pub use crate::boundary::NominalSerial;
pub use crate::boundary::PathOrderStatus;
pub use crate::boundary::PortArgumentCount;
pub use crate::boundary::RecursiveStatus;
pub use crate::boundary::RuleIndex;
pub use crate::boundary::RuleVariableLinearity;
pub use crate::boundary::SerializedDescText;
pub use crate::boundary::SerializedValueBytes;
pub use crate::boundary::ShapePoint;
pub use crate::boundary::ShapeSize;
pub use crate::boundary::SurfaceByteOffset;
pub use crate::boundary::TermPositionIndex;
pub use crate::boundary::VariableIndex;
pub use crate::builtin::bool_desc;
pub use crate::builtin::list_desc;
pub use crate::builtin::option_desc;
pub use crate::builtin::pair_desc;
pub use crate::builtin::sum_desc;
pub use crate::circuit::BoundaryReading;
pub use crate::circuit::CircuitBody;
pub use crate::circuit::CircuitDerivationError;
pub use crate::circuit::CircuitFeed;
pub use crate::circuit::CircuitFrame;
pub use crate::circuit::CircuitNode;
pub use crate::circuit::CircuitRedex;
pub use crate::circuit::CircuitRule;
pub use crate::circuit::DerivedBoundaries;
pub use crate::circuit::FrameHead;
pub use crate::circuit::derive_boundaries;
pub use crate::circuit::derive_boundaries_within;
pub use crate::circuit::derive_boundary;
pub use crate::circuit::derive_boundary_within;
pub use crate::code::AtomSort;
pub use crate::code::Attr;
pub use crate::code::Attrs;
pub use crate::code::Code;
pub use crate::code::CodeArgs;
pub use crate::code::CodeNode;
pub use crate::code::CodeView;
pub use crate::code::Name;
pub use crate::code::PrimTy;
pub use crate::code::ValueTypeArgs;
pub use crate::code::ValueTypeNode;
pub use crate::code::ValueTypeRef;
pub use crate::code::ValueTypeView;
pub use crate::code::primitive_label;
pub use crate::desc::CtorDesc;
pub use crate::desc::DeclPolarity;
pub use crate::desc::NominalId;
pub use crate::desc::OperDesc;
pub use crate::desc::ParamDesc;
pub use crate::desc::Representability;
pub use crate::desc::ShapeFace;
pub use crate::desc::SortDesc;
pub use crate::desc::SortIndex;
pub use crate::desc::SurfaceSpan;
pub use crate::desc::TheoryDesc;
pub use crate::desc::TheoryShape;
pub use crate::desc::face_escape;
pub use crate::desc::shape_parameter;
pub use crate::elaborate::ActiveCell;
pub use crate::elaborate::CircuitElaborationError;
pub use crate::elaborate::InterfacePair;
pub use crate::elaborate::PortFace;
pub use crate::elaborate::PortInstantiationError;
pub use crate::elaborate::RedexOccurrence;
pub use crate::elaborate::RewritePort;
pub use crate::elaborate::Whisker;
pub use crate::elaborate::WhiskerHead;
pub use crate::elaborate::WhiskeredCell;
pub use crate::elaborate::active_position;
pub use crate::elaborate::elaborate_body;
pub use crate::elaborate::redex_occurrences;
pub use crate::first_order::TranslationError;
pub use crate::first_order::first_order;
pub use crate::generic::DescValue;
pub use crate::generic::Payload;
pub use crate::generic::PayloadArgs;
pub use crate::generic::PayloadNode;
pub use crate::generic::PayloadView;
pub use crate::generic::Side;
pub use crate::generic::generic_eq;
pub use crate::generic::serialize_desc;
pub use crate::generic::serialize_value;
pub use crate::rule::FreeTerm;
pub use crate::rule::RuleFace;
pub use crate::rule::RuleVarMeta;
pub use crate::rule::TermArgs;
pub use crate::rule::TermNode;
pub use crate::rule::TermView;
pub use crate::rule::Variance;
pub use crate::termination::Precedence;
pub use crate::termination::Rank;
pub use crate::termination::Termination;
pub use crate::termination::orient_rules;
pub use crate::termination::orient_rules_with;
pub use crate::termination::path_greater;
pub use crate::theory::DerivedFace;
pub use crate::theory::DerivedPeak;
pub use crate::theory::IncludeClash;
pub use crate::theory::MemberPosition;
pub use crate::theory::OperationKind;
pub use crate::theory::RuleCertificate;
pub use crate::theory::RuleTurn;
pub use crate::theory::SidePlace;
pub use crate::theory::THEORY_CONSTRUCTORS;
pub use crate::theory::TheoryBinder;
pub use crate::theory::TheoryFault;
pub use crate::theory::TheoryInclusion;
pub use crate::theory::TheoryOperation;
pub use crate::theory::TheoryParts;
pub use crate::theory::TheoryPort;
pub use crate::theory::TheoryRule;
pub use crate::theory::TheorySort;
pub use crate::theory::TheoryValue;
pub use crate::theory::UndescribedTheory;
pub use crate::theory::presented_names;
pub use crate::theory::theory_desc;
pub use crate::typed_rule::PatternContext;
pub use crate::typed_rule::TypedRuleFace;
pub use crate::typed_rule::pattern_variable;
pub use crate::wellformed::RESERVED_DERIVED_MARKERS;
pub use crate::wellformed::WfDiagnostic;
pub use crate::wellformed::WfKind;
pub use crate::wellformed::check_desc;
pub use crate::wellformed::derive_cell_var_meta;
pub use crate::wellformed::diagnostic_span;

#[cfg(test)]
mod test_support
{
    /// A stand-in grade vocabulary for the unit tests: the crate is generic
    /// over the grade a field carries, and a consumer supplies its own.
    #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
    pub enum Grade
    {
        /// The linear grade.
        One,
        /// The unrestricted grade.
        Omega,
    }
}
