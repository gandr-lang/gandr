//! Element identity and bridges as a structural fold of quoted codes.
//!
//! The fold builds an indexed relation program, not an equality decision.
//! Its interpreter retains neutral fibres. Identity adds derived reflexivity
//! and transport; bridge families carry neither obligation. Universe identity
//! consumes `path_universe`; a universe bridge is a relation between the two
//! codes' elements.
//!
//! Handles refer to the original arena contents: callers must retain their
//! code and value nodes, without truncating and reusing their addresses.
//! No relation, fibre or identity handle admits a declaration.
//!
//! # The relation fold
//!
//! The fold reads a closed code vocabulary with `Mode::Identity` or
//! `Mode::Bridge`. Identity also reaches the level-zero value universe,
//! including occurrences beneath the admitted formers; a bridge reaches the
//! value universe at every level. It is the rule set behind the persisted
//! element-identity nodes: [`crate::element_identity`] reads its fibres to
//! check `Path`, `here`, the higher forms and transport in identity mode and
//! `Bridge` in bridge mode, and its clauses become their replay reductions.
//! Endpoints are ordinary typed values in an open context; unsupported codes
//! are refused before interpretation.
//!
//! `Interpretation::path` consumes an ordinary native `ValueId`, synthesizes
//! it through the declaration checker's closed-value boundary and decodes the
//! checked `PathUniverse` classifier. Native typing failures retain
//! `KernelError` inside `RelationError::Typing`; endpoint failures retain
//! `PathError`. No auxiliary path arena or formation cache participates.
//!
//! | Code | Relation clause | Identity structure | Bridge structure |
//! | ---- | --------------- | ------------------ | ---------------- |
//! | Unit | Unit fibre at every pair of indices. | Unit witness; reflexive transport returns its input. | `()`, by the clause alone. |
//! | Base | Discrete relation: identical indices give Unit; distinct canonical literals give Empty; unresolved neutral equality remains a relation. | Reflexivity is constructive; distinct variables are not assumed unequal. | The same discrete clause. |
//! | Sum | Matching injections recurse on their payloads; different injections give Empty. An unknown injection remains suspended. | Payload reflexivity and transport use the matching branch. | The matching branch's bridge. |
//! | Product | Component relations paired, including projections of neutral indices. | Componentwise reflexivity and composition; neither coordinate is dropped. | A tuple of the component bridges. |
//! | Thunk `U (A → F B)` | Suspended product `Π a₀ a₁. Rel(A,a₀,a₁) → Rel(B,force f a₀,force g a₁)`, with the same mode on both premises; it lowers to the persisted `Path` at the thunk type in identity mode and to the persisted `Bridge` in bridge mode. | `here` reflexivity, higher-evaluation (ap), quantified-evaluation and pointwise introduction; application transport replays both returners. | The family over argument bridges, introduced only by a higher or a quantified evaluation; no `here`, no related application. |
//! | List A | Lazy constructor relation; each Cons applies the already-folded element clause and delays its tail. | A complete finite observation records Unit or a distinguishing Empty fibre, depth and instruction count. | The relation lifting: Unit at two nils, Empty at a nil and a cons, and at two conses the heads' bridge beside the tails' persisted `Bridge`; a neutral list suspends. |
//! | Value universe | Identity at level zero: native `PathUniverse` of the two indexed codes. Bridge at every level: the relation `El A → El B → F U`. | Native path reflexivity and certified translator replay. | A relation thunk, supplied, never derived from the codes. |
//! | `PathUniverse` | Identity only: the higher record of two native certificates. | Pointwise forward/backward fields and both round-trip coherence obligations, observed separately. | Refused as an unsupported type. |
//! | Abstract | The relation its declaration's interface states, `El(⟨R a b⟩)`, read through [`Interfaces`]; an atom stating none is a named obstruction, even for the same nominal atom. | The interface's relation once its law contracts the relation's singletons: `here` by the reflexivity, transport and the eliminator derived in the singleton family. Refused by name, `AtomTransport`, where the interface states no law. | The interface's relation at the endpoints, with its reflexivity as `here`; `BridgeAtSealedType` at formation and at every reading where the atom states no interface. |
//! | Codes | Identity consumes existing `Path_U` formation; bridges are checked indexed families over two element types. | Existing certified-equivalence and transport semantics are reused, not redefined. | `Relation::constant` and `Relation::cases`, in memory. |
//!
//! **Base choice.** These built-in scalar codes are discrete; their canonical
//! data has decidable equality. This is not a nominal-identifier test for
//! sealed values. A different base interpretation needs an explicit relation
//! interface. A sealed Abstract likewise reads the relation and reflexivity
//! its declaration supplies; identity reads that relation only when the
//! interface also states the law that makes it an identity system. Looking
//! through the seal or treating its name as equality evidence is not an
//! alternative.
//!
//! `Relation::constant` and `Relation::cases` construct heterogeneous indexed
//! bridge families. The distinguishing witness is `Br_U Unit Bool` with fibre
//! Unit at `((), inl ())` and Empty at `((), inr ())`. These direct
//! first-order families require neither equality on arbitrary elements nor an
//! equivalence. An arbitrary span needs endpoint fibres and reindexing laws
//! before it can supply such a family. The implementation does not establish
//! the full model laws of internal parametricity without an interval (Thorsten
//! Altenkirch, Yorgo Chamoun, Ambrus Kaposi and Michael Shulman, "Internal
//! Parametricity, without an Interval", POPL 2024, `doi:10.1145/3632920`).
//! Bridge mode shares the code clauses but grants no automatic reflexivity,
//! no transport along a bridge and no J.
//!
//! Identity evidence checks against its computed fibre. `reflexivity`
//! constructs the diagonal; `compose` transports in the first-order identity
//! fibre, pairing both product components. `transport` accepts native
//! representable level-zero motives and reduces structural reflexivity to the
//! exact input. An unresolved non-reflexive transport retains its endpoints,
//! proof, motive and input as a neutral operation, not a fabricated target
//! value. Suspended sum reflexivity is a structural diagonal program. This
//! module provides no J, no arbitrary dependent motives, no general fibrancy
//! theorem and no unrestricted universe hierarchy.
//!
//! **Universe boundary.** The clause at a quoted `U₀` lowers to the native
//! `Path_U`, subject to that former's closed first-order endpoint stratum. It
//! never interprets two code values as discrete syntax equality. Its diagonal
//! is `PathRefl`; arbitrary evidence is checked as a native path, and code
//! transport uses `path_universe::replay_transport`. Equal endpoint codes do
//! not make a negation certificate reflexive: generic dependent transport
//! stays neutral unless its proof is structural reflexivity. Generic
//! first-order composition refuses code-level certificate composition with
//! `CertificateOperationRequired` rather than replacing the composite by
//! reflexivity. Explicit native certificates remain usable as evidence.
//!
//! At a quoted `PathUniverse`, the same fold yields a certificate fibre.
//! `Fibers::certificate` reuses `higher_field::unfold`, exposing the four
//! obligations without deciding them. Lowering this record to a native
//! first-order type returns `HigherFieldRequired`. This is the stopping point,
//! not a claim of infinite coherence. Universe identity above level zero and
//! an extensional conversion rule are outside the fold; a universe bridge is
//! read at every level (§ Bridges).
//!
//! **Universe choice.** Reusing the native former keeps path checking and
//! replay authoritative; a second equivalence arena or discrete comparison
//! would erase the certified map. **Reversal.** A broader native endpoint
//! stratum or a checked certificate-composition language can expand the
//! clause without changing its interpretation.
//!
//! # Function identity and funext
//!
//! At a thunk code, the fold records argument and result relations without
//! comparing functions. `apply_related` checks two independently supplied
//! arguments and their relation evidence. It crosses each `U` seam with
//! `force`, applies the function, and relates the values returned through
//! `F`. A variable or stuck application retains a function fibre and both
//! application computations. It never becomes Empty because evaluation is
//! stuck.
//!
//! `HigherEvaluation` is an untrusted introduction: each component contains
//! two claimed returned values, their `core-nbe` dialogues, and an inhabitant
//! of the computed output relation. `QuantifiedEvaluation` extends it with
//! application steps (below). The kernel constructs every replay claim
//! itself. Open component telescopes close under lambdas before replay.
//! `function_reflexivity` replays the same function on related inputs, the
//! λ's ap; structural `reflexivity` at a function is `here` of it, which the
//! persisted path type admits by conversion. `funext` stores raw evidence in
//! `Identity`, and every consuming operation checks it again. Native
//! conversion gains no function-extensionality rule.
//!
//! Universal introductions cover closed functions. Coverage uses Unit,
//! matching Sum injections, Product combinations and fresh rigid Base
//! variables; the relation premise identifies each discrete Base pair, without
//! sampling literals. A function coordinate of the argument, at a thunk type
//! `T`, binds the inner fibre itself: two functions and their identity, `f₀
//! f₁ : T` and `p : Path(T, f₀, f₁)`, with `f₀` the source argument and `f₁`
//! the target. Nothing is sampled and nothing is split, so a higher-order
//! argument is one generic pattern. A function fibre lowers to the persisted
//! `Path` at its thunk type in identity mode and to the persisted `Bridge` in
//! bridge mode, which is what makes both ends checkable: the premise is the
//! bound `p`, and a function-valued output is related by `p`, by a nested
//! higher evaluation or, in identity mode, by `here`. A bridge binds the same
//! generic input with the bridge between the two functions as its premise. A
//! universe coordinate is bridge mode's alone: two codes and a relation
//! between their elements, `X₀ X₁ : U` and `R : U (El X₀ → El X₁ → F U)`, one
//! generic pattern again, whose relation no quantified step applies. The
//! admitted function code is the non-dependent arrow `U (A → F B)`; dependent
//! arrows and arguments of a recursive code are outside this clause, and so is
//! a universe coordinate of an identity.
//!
//! A body that applies its higher-order argument, `λh. force h v`, is stuck at
//! the generic pattern: it returns no value there, so a higher evaluation's
//! component refuses as `Evaluation`. The quantified evaluation decides it
//! under the quantifier. Per pattern it is a pre-order tree of steps. A return
//! step is a higher evaluation's component. An application step names the
//! premise `p` at a de Bruijn index of its telescope and carries both sides'
//! closed normal forms `thunk (λⁿ. S)` with their dialogues: the kernel replays
//! that each side's computation converts to its normal form, reads `S` as
//! `force f₀ a` and `force f₁ a'`, bare or bound as `x ← …; K`, with `f₀ f₁`
//! the two functions `p` relates, and requires `a` and `a'` convertible. It
//! then covers the inner result `B` and continues each side at each output
//! `o` — `return o`, or `K` weakened past the output's binders and
//! instantiated at `o` — one child step per output, in coverage order. The
//! inner domain must be first order: inputs that are themselves functions
//! would need function identity between them, refused as `HigherOrderDomain`;
//! inputs that do not convert, a head no premise relates, or a step of the
//! wrong kind refuse as `QuantifiedStep`.
//!
//! `transport_application` instantiates a checked function identity at an
//! argument diagonal, `here` at a function argument, and computes the related
//! returned values. Other native motives retain `Transport::Neutral`, including
//! non-reflexive function identities. The Bool witnesses compute `not ∘ not =
//! id` at both constructors and reject `not = id` with the failing component.
//! The higher-order witnesses replay ap of a λ duplicating its argument, relate
//! two λs pairing it with `not ∘ not` and with `id` by the premise and a nested
//! higher evaluation, and refuse the pair with `not`. Double negation in those
//! witnesses is the annotation-free, case-inlined term with its return/bind
//! seam, since an inlined λ's injections do not synthesize. A persisted higher
//! evaluation names `not` instead: admission replays it with every admitted
//! definition unfoldable, and an anchor-free `Unfold` resolves its constant
//! from the head it unfolds. The independent engine checks the direct
//! composition too.
//!
//! **Higher-evaluation cost.** Each Boolean introduction has two components
//! and four application replays; a function coordinate adds one pattern and
//! three binders. Coverage and each replay have separate finite allowances;
//! implicit beta steps consume replay budget even when they emit no decision.
//! Product coverage can grow multiplicatively, so these bounds do not establish
//! a global work theorem. Traces move into identity evidence; only a retained
//! neutral transport clones that evidence to own its suspended computation.
//!
//! **Function choice.** A lazy related-input product preserves the
//! observational definition, including distinct related Unit arguments.
//! Native function conversion would impose a stronger equality test; finite
//! literal sampling would not establish the universal premise. Replaying
//! ordinary CBPV evaluation reuses the trusted machine. A higher-order argument
//! binds its inner fibre as a variable rather than covering it: the
//! alternatives were refusing it, which left the record's funext by definition
//! first-order, and sampling functions, which establishes nothing universal.
//! **Reversal.** A function argument whose own domain is higher order needs
//! function identity between the inputs it is applied at, where the step
//! would carry a nested evidence tree instead of a convertibility test;
//! complete dependent funext additionally requires its substitution and
//! fibrancy laws.
//!
//! # Bridges
//!
//! A bridge is the non-fibrant reading of the same fold. `Bridge(A, a₀, a₁)`
//! is a persisted node formed like `Path`, and its evidence checks against
//! the fibre this fold computes in bridge mode, the bridge column of the table
//! above. At a function code `U (A → F B)` it is the family over argument
//! bridges, `(a₀ a₁ : A) (ā : Br A a₀ a₁) → Br B (f a₀) (g a₁)`, introduced by
//! the higher and quantified evaluations that introduce funext, every premise
//! a bridge. At the value universe of any level it is the relation `El A → El
//! B → F U` between the codes' elements, the span the universe clause of
//! internal parametricity names, read as its fibration. At a list it is the
//! relation lifting, one constructor at a time, with the tails' bridge left as
//! the persisted node so that each step is finite.
//!
//! The clauses grant nothing else: related application and transport at a
//! bridge are refused by shape, and `here` checks at a bridge only at an atom
//! whose interface states reflexivity. A domain that reaches a sealed atom
//! stating no interface — itself, a function's result, a list's elements — is
//! refused as `BridgeAtSealedType`; the relation an atom bears is its
//! interface's to supply. Dependent arrows, functions over a list
//! argument, the path universe and a bridge at a bridge are refused by name
//! (`element_identity::bridge_tests::the_codes_outside_the_bridge_clauses_are_refused_by_name`).
//!
//! **Choice.** The clauses are those of internal parametricity without an
//! interval (Altenkirch, Chamoun, Kaposi and Shulman, POPL 2024, cited above),
//! in the identity recursion's vocabulary: one fold, with identity its fibrant
//! case and the bridge its non-fibrant one, so each code's bridge is the
//! clause its identity already has, read without reflexivity. **Alternatives.**
//! An affine bridge interval (Evan Cavallo and Robert Harper, "Internal
//! Parametricity for Cubical Type Theory", LMCS 17(4:5), 2021), or the nominal
//! name abstraction `И` of nullary internal parametricity (Antoine Van Muylder,
//! Andreas Nuyts and Dominique Devriese, "Nominal Type Theory by Nullary
//! Internal Parametricity", arXiv:2512.09464): each adds a variable sort and a
//! substructural context discipline the kernel does not have, for a diagonal
//! these clauses do not need. **Reversal.** A consumer that needs a bridge's
//! diagonal, such as the graph of a function as a bridge in the universe, or
//! transport along a bridge, needs the interval or the name.
//!
//! # Native fibres and admission
//!
//! Computed fibres lower to the native unit (the empty product), the empty
//! sum, binary products and universe-path types. The empty sum forms at level
//! zero and has no constructor; its elimination is a case of no branches,
//! which checks against any expected computation type when its scrutinee is a
//! `Sum([])` and has no beta rule. A case of no branches has nothing to
//! synthesize a type from, so synthesis refuses it as `EmptyCase`. The empty
//! sum is an output fibre here, not an input code in the fold's closed
//! vocabulary. As an ordinary native leaf it remains a legitimate
//! bounded-alias target. The fold reads the unit and binary sums and products;
//! a product or sum of another arity is refused as an unsupported type until
//! the fold is n-ary.
//!
//! Code folding, fibre evaluation and proof construction preserve DAG sharing
//! with call-local tables. Those tables grant no admission capability or
//! conversion authority. Declaration admission includes the native empty sum,
//! finite Lists with nil, cons and pure fold, universe paths, and the persisted
//! element-identity nodes: `Path`, `Bridge`, `here`, transport, higher fields,
//! higher evaluation and related application. No receipt admits an in-memory
//! relation program or a guarded list inhabitant.
//!
//! **Choice.** One code fold produces relation combinators; a shared evaluator
//! computes both modes, while only identity carries reflexivity and transport.
//! Separate per-mode recursions would duplicate the former clauses. The
//! persisted syntax over this fold, with its dependent motives and
//! substitution law, is [`crate::element_identity`]'s. **Reversal.** Accepting
//! Abstract requires its missing interface, not a default relation; in bridge
//! mode that interface is its relation.
//!
//! # Witnesses
//!
//! The witnesses in this module's tests and in `function`'s distinguish wrong
//! sum branches, dropped product coordinates, negative equality on neutrals,
//! forged identity evidence, incorrect universe classifiers, seal inspection
//! and a malformed elimination of the empty sum. Function-specific boundaries
//! include omitted or extra coverage, reused component dialogues, forged
//! returned values, unchecked argument relations, bridge transport and
//! application-motive action. The bridge witnesses in
//! `element_identity::bridge_tests` compute each bridge clause beside the
//! identity reading of the same code, and the readmission witness replays the
//! persisted node. No mutation score is claimed.

use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
use gandr_kernel_strata::Level;
use gandr_kernel_term::CompType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeclarationContent;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::Value;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueType;
use gandr_kernel_term::ValueTypeId;
use quenchant_shape::shape::Maybe;

use crate::check::check_closed_value;
use crate::conv::Convertibility;
use crate::conv::convertible_value_types;
use crate::env::AdmittedDeclaration;
use crate::error::KernelError;
use crate::path_universe;
use crate::replay::ReplayBudget;

mod evaluation;

mod evidence;

mod function;

pub mod recursive;

#[cfg(test)]
mod tests;

mod universe;

pub use evaluation::Fiber;
pub use evaluation::FiberId;
pub use evaluation::Fibers;
pub use evaluation::Index;
pub use evaluation::IndexId;
pub use evidence::Transport;
pub use function::Application;
pub use function::Component;
pub(crate) use function::ComponentObligation;
pub use function::Evaluation;
pub use function::EvaluationSide;
pub use function::HigherEvaluation;
pub(crate) use function::NormalForm;
pub use function::Pointwise;
pub(crate) use function::Quantified;
pub use function::RelatedArguments;
pub use function::RelatedPattern;
#[cfg(test)]
pub(crate) use function::tests as function_fixtures;

/// Element identity with raw evidence rechecked by every consumer.
///
/// # Specification
/// - requires: no caller-created admission authority; construction is private.
/// - ensures: only checked introductions construct this value; consumption
///   rechecks its evidence rather than trusting a stored verdict.
/// - provides: native evidence, a suspended structural diagonal or raw higher
///   evaluation, with arena-relative endpoints and no admission authority.
/// - fails: consumers refuse invalid or exhausted evidence by named errors.
/// - panics: none.
/// - executable: none — the obligation quantifies over introduction and later
///   consumption; the record itself is not an evidence validator.
///
/// # Adequacy
/// - hypothesis: L1/L3 — native transport replays higher evidence and retains
///   non-reflexive function identities as typed neutral operations.
/// - witness: `identity_recursion::function::tests::funext_computes_and_refuses_wrong_components`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Identity
{
    /// The element type.
    domain: ValueTypeId,
    /// Source element.
    left: ValueId,
    /// Target element.
    right: ValueId,
    /// The raw fibre inhabitant or evaluation rule.
    proof: Proof,
}

/// Native, structural or higher-evaluation relation evidence.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Proof
{
    /// An ordinary inhabitant of a computed native fibre.
    Native(ValueId),
    /// A structural diagonal awaiting a neutral sum index.
    Diagonal,
    /// An untrusted higher-evaluation introduction, replayed on consumption.
    HigherEvaluation(HigherEvaluation),
}

/// The fibrant or non-fibrant reading of the same structural fold.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Mode
{
    /// Element identity, with reflexivity and transport operations.
    Identity,
    /// A relation, without invertibility or transport obligations.
    Bridge,
}

/// A quoted element code, or the classifier of the closed codes themselves.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Domain
{
    /// Interpret elements of this quoted first-order type.
    Elements(ValueId),
    /// Interpret the closed code universe; this is not a nested universe code.
    Codes,
}

/// A local relation-program address, never an admission capability.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct RelationId(usize);

/// A relation combinator; children are local addresses in a flat program.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Clause
{
    /// The constantly inhabited fibre.
    Unit,
    /// The constantly empty fibre.
    Empty,
    /// Discrete equality of canonical base data, residual on neutral inputs.
    Discrete,
    /// Native certified paths between level-zero value codes.
    Universe,
    /// Identity of certificates is observed through its higher record fields.
    Certificate,
    /// Bridges between two codes of one value universe: the relations between
    /// their elements, valued in that universe. Bridge mode only, at every
    /// level.
    Relation,
    /// Related product coordinates, independently.
    Product(RelationId, RelationId),
    /// Matching injections recurse; different injections have empty fibre.
    Sum(RelationId, RelationId),
    /// Related arguments entail related values after force/application/return.
    Function(RelationId, RelationId),
    /// One list constructor, with its recursive tail delayed in guarded syntax.
    List(RelationId),
    /// Split the left endpoint; both branches share the right endpoint type.
    CaseLeft(RelationId, RelationId),
    /// Split the right endpoint; both branches share the left endpoint type.
    CaseRight(RelationId, RelationId),
    /// A sealed atom's elements, related by its interface's relation into the
    /// universe `kind` the atom inhabits. Bridge mode only.
    Atom
    {
        /// The interface's relation.
        relation: ValueId,
        /// The atom's kind, the universe the relation's codes inhabit.
        kind: ValueTypeId,
    },
}

/// The admission log a fold reads sealed atoms' interfaces from.
///
/// # Specification
/// - requires: nothing.
/// - ensures: answers the interface an admitted abstract type states, and
///   nothing for any other position.
/// - panics: none.
/// - executable: none — data declaration, not a callable boundary.
///
/// # Adequacy
/// - hypothesis: L3 — an atom stating an interface is read through it, and an
///   atom stating none, or a log without the atom, refuses by name.
/// - witness: `element_identity::bridge_tests::an_interfaced_atom_bears_its_relation_as_its_bridge`
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct Interfaces<'entries>(&'entries [AdmittedDeclaration]);

impl<'entries> Interfaces<'entries>
{
    /// No admitted atom: every sealed atom refuses.
    pub const NONE: Interfaces<'static> = Interfaces(&[]);

    /// The interfaces the admission log `entries` states.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn of(entries: &'entries [AdmittedDeclaration]) -> Self
    {
        Self(entries)
    }

    /// The interface the atom at `atom` states, with the atom's kind.
    ///
    /// # Specification
    /// - ensures: `Some` exactly when `atom` is an admitted abstract type whose
    ///   declaration states an interface.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Interfaces`].
    /// - witness: `element_identity::bridge_tests::an_interfaced_atom_bears_its_relation_as_its_bridge`
    #[spec(ensures: |ret| ret.is_none() || self.0.get(usize::from(atom)).is_some())]
    #[inline]
    #[must_use]
    pub fn of_atom(
        self,
        atom: ConstantIndex,
    ) -> Option<(gandr_kernel_term::AtomInterface, ValueTypeId)>
    {
        match *self.0.get(usize::from(atom))?.content() {
            DeclarationContent::AbstractType {
                kind,
                interface: quenchant_shape::shape::Maybe::Present(interface),
                ..
            } => Some((interface, kind)),
            DeclarationContent::AbstractType { .. }
            | DeclarationContent::Data { .. }
            | DeclarationContent::Codata { .. }
            | DeclarationContent::Def { .. }
            | DeclarationContent::Axiom { .. } => None,
        }
    }
}

/// One typed relation combinator.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Node
{
    /// Type of its left index.
    source: ValueTypeId,
    /// Type of its right index.
    target: ValueTypeId,
    /// The fibre computation.
    clause: Clause,
}

/// A finite, arena-relative indexed family, independent of its inhabitants.
///
/// # Specification
/// - requires: arena-relative endpoints remain live for an operation.
/// - ensures: identity programs arise only from the admitted code fold; bridge
///   programs can additionally be constant or case-indexed relations.
/// - provides: a flat indexed family over the admitted closed-code fragment;
///   operations recheck its endpoints before interpreting an inhabitant.
/// - fails: operations report domain, typing and evidence faults explicitly.
/// - panics: none.
/// - executable: none — construction provenance and subsequent rechecking are
///   laws across operations, not a verdict stored in this record.
///
/// # Adequacy
/// - hypothesis: L3 — a heterogeneous case-indexed bridge separates arbitrary
///   relations from equivalences and from structural equality of endpoint
///   codes.
/// - witness: `identity_recursion::tests::universe_bridge_is_an_indexed_relation`
#[derive(Clone, Debug)]
pub struct Relation
{
    /// Whether reflexivity and transport are available.
    mode: Mode,
    /// Constructor-ordered program storage.
    nodes: Vec<Node>,
    /// The final combinator.
    root: RelationId,
}

/// The result of the one code recursion, including its universe clause.
#[derive(Clone, Debug)]
pub enum Interpretation
{
    /// An indexed family over the elements of a quoted code.
    Elements(Relation),
    /// Universe identity is precisely the existing certified-equivalence
    /// former.
    UniverseIdentity,
    /// Universe bridges classify relation families, with no equality
    /// reflection.
    UniverseBridge,
}

/// A failure to form or use an experimental relation.
#[derive(Debug)]
pub enum RelationError
{
    /// An arena reference is unreadable.
    Arena,
    /// A code is not a quote.
    UnsupportedCode(ValueId),
    /// A former is outside the first-order fragment.
    UnsupportedType(ValueTypeId),
    /// A sealed type exposes no element relation or its structure.
    AbstractInterface(ValueTypeId),
    /// An identity at a sealed atom whose interface states a relation and its
    /// reflexivity but no law contracting its singletons.
    AtomTransport(ValueTypeId),
    /// Ordinary kernel formation or checking failed.
    Typing(Box<KernelError>),
    /// A universe path failed its existing formation judgement.
    Path(Box<path_universe::PathError>),
    /// Composition endpoints do not agree definitionally.
    Boundary,
    /// A bridge cannot supply fibrant operations.
    NonFibrant,
    /// A neutral fibre has no native closed type reduct yet.
    NeutralFiber,
    /// A supplied proof does not inhabit its computed fibre.
    Evidence,
    /// The requested operation uses the wrong universe interpretation.
    Classifier,
    /// A universal function proof needs a higher-evaluation introduction.
    HigherEvaluationRequired,
    /// Symbolic coverage is incomplete or contains extra components.
    Coverage,
    /// A component supplied an invalid output-relation inhabitant.
    Pointwise(Component, Box<KernelError>),
    /// An application trace did not certify its claimed returned value.
    Evaluation(Component, EvaluationSide, crate::replay::KernelVerdict),
    /// A quantified step's normal forms do not apply the two functions its
    /// premise relates at one input.
    QuantifiedStep(Component),
    /// A quantified step applies a function whose own domain binds a
    /// function: its inputs would need function identity between them, which
    /// one input up to conversion does not carry.
    HigherOrderDomain(Component),
    /// Recursive inhabitants require the guarded observation interface.
    RecursiveObservationRequired,
    /// A certificate identity requires its higher record observation.
    HigherFieldRequired,
    /// Non-discrete code identities require explicit native certificate
    /// evidence.
    CertificateOperationRequired,
    /// Symbolic coverage exhausted its work allowance.
    Budget,
}

impl fmt::Display for RelationError
{
    /// Show the exact experimental failure class.
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
            Self::Arena => f.write_str("unreadable relation arena reference"),
            Self::UnsupportedCode(_) => f.write_str("relation domain is not a quoted code"),
            Self::UnsupportedType(_) => {
                f.write_str("relation code is outside the first-order fragment")
            },
            Self::AbstractInterface(_) => {
                f.write_str("sealed type has no element-relation interface")
            },
            Self::AtomTransport(_) => f.write_str("sealed type's interface states no identity law"),
            Self::Typing(ref error) => write!(f, "relation typing failed: {error}"),
            Self::Path(ref error) => write!(f, "universe identity failed: {error}"),
            Self::Boundary => f.write_str("relation indices do not match"),
            Self::NonFibrant => f.write_str("bridge has no identity transport structure"),
            Self::NeutralFiber => f.write_str("relation fibre is neutral"),
            Self::Evidence => f.write_str("relation fibre has no constructed evidence"),
            Self::Classifier => f.write_str("wrong relation classifier"),
            Self::HigherEvaluationRequired => f.write_str("higher-evaluation evidence required"),
            Self::Coverage => f.write_str("incomplete higher-evaluation coverage"),
            Self::Pointwise(component, ref error) => {
                write!(f, "pointwise component {}: {error}", component.0)
            },
            Self::Evaluation(component, side, _) => {
                let side = match side {
                    EvaluationSide::Left => "left",
                    EvaluationSide::Right => "right",
                };
                write!(
                    f,
                    "application component {} ({side}) replay failed",
                    component.0
                )
            },
            Self::QuantifiedStep(component) => {
                write!(
                    f,
                    "quantified component {} does not apply its premise's functions at one input",
                    component.0
                )
            },
            Self::HigherOrderDomain(component) => {
                write!(
                    f,
                    "quantified component {} applies a function whose domain is higher order",
                    component.0
                )
            },
            Self::Budget => f.write_str("relation work allowance exhausted"),
            Self::HigherFieldRequired => f.write_str("certificate identity requires higher fields"),
            Self::CertificateOperationRequired => {
                f.write_str("explicit universe certificate operation required")
            },
            Self::RecursiveObservationRequired => {
                f.write_str("recursive identity requires guarded observation")
            },
        }
    }
}

impl core::error::Error for RelationError
{
}

/// Define identity and bridges together by one postorder recursion over codes.
///
/// # Specification
/// - requires: codes and their types belong to `arena`.
/// - ensures: Unit, Base, Sum, Product, List and pure function thunks each
///   contribute one clause in either mode. Identity additionally reaches the
///   level-zero value universe as native paths and path certificates as higher
///   fields; a bridge reaches every value universe as its relations, and a
///   sealed atom as the relation its interface states, which an identity
///   reaches too when the interface states its law. An atom stating no
///   interface refuses before nominal comparison, and identity at an atom whose
///   interface states no law refuses by name. Codes selects certified paths or
///   indexed relation families.
/// - provides: a flat iterative fold; it never compares endpoint elements.
/// - fails: `UnsupportedCode`, `UnsupportedType`, `AbstractInterface`,
///   `AtomTransport`, `Arena`.
/// - panics: none.
///
/// # Errors
/// As `fails`.
///
/// # Adequacy
/// - hypothesis: L3 — both modes share every constructor boundary; nested
///   sealed types refuse even when both requested endpoints would be identical.
/// - witness: `identity_recursion::tests::both_modes_compute_all_element_clauses`
/// - witness: `identity_recursion::tests::abstract_is_an_interface_obstruction`
/// - witness: `element_identity::bridge_tests::an_interfaced_atom_bears_its_relation_as_its_bridge`
/// - witness: `element_identity::bridge_tests::a_lawful_atom_reads_its_relation_as_its_identity`
/// - witness: `identity_recursion::function::tests::function_clause_retains_related_inputs_and_neutrals`
/// - witness: `path_universe::tests::universe_fold_tests::universe_clause_is_native`
#[spec(ensures: |ret| match (domain, &ret) {
    (Domain::Codes, &Ok(Interpretation::UniverseIdentity)) => mode == Mode::Identity,
    (Domain::Codes, &Ok(Interpretation::UniverseBridge)) => mode == Mode::Bridge,
    (Domain::Elements(code), &Ok(Interpretation::Elements(ref relation))) => relation.mode == mode
        && relation.nodes.get(relation.root.0).is_some_and(|root| matches!(arena.value(code), Some(&Value::Quote(ty)) if ty == root.source && root.source == root.target))
        && relation.nodes.iter().enumerate().all(|(index, node)| node.source == node.target && match node.clause {
            Clause::Product(a, b) | Clause::Sum(a, b) | Clause::Function(a, b) => a.0 < index && b.0 < index,
            Clause::List(element) => element.0 < index,
            Clause::Universe | Clause::Certificate => mode == Mode::Identity,
            Clause::Relation => mode == Mode::Bridge,
            Clause::Unit | Clause::Discrete | Clause::Atom { .. } => true,
            Clause::Empty | Clause::CaseLeft(..) | Clause::CaseRight(..) => false,
        }),
    (Domain::Elements(_), &Err(RelationError::AbstractInterface(ty) | RelationError::AtomTransport(ty))) => matches!(arena.value_type(ty), Some(&ValueType::Abstract(_))),
    (Domain::Elements(_), &Err(_)) => true,
    _ => false,
})]
#[inline]
pub fn interpret(
    arena: &TermArena,
    interfaces: Interfaces<'_>,
    mode: Mode,
    domain: Domain,
) -> Result<Interpretation, RelationError>
{
    let code = match domain {
        Domain::Codes => {
            return Ok(match mode {
                Mode::Identity => Interpretation::UniverseIdentity,
                Mode::Bridge => Interpretation::UniverseBridge,
            });
        },
        Domain::Elements(code) => code,
    };
    let root = quoted(arena, code)?;
    let mut pending = Vec::from([(root, false)]);
    let mut formed = BTreeMap::new();
    let mut nodes = Vec::new();
    while let Some((ty, expanded)) = pending.pop() {
        if formed.contains_key(&ty) {
            continue;
        }
        let node = arena.value_type(ty).ok_or(RelationError::Arena)?;
        let clause = match *node {
            ValueType::Product(ref parts) if parts.is_empty() => Clause::Unit,
            ValueType::Universe {
                sort: GroundSort::Value,
                ref level,
            } if mode == Mode::Identity && *level == Level::zero() => Clause::Universe,
            ValueType::Universe {
                sort: GroundSort::Value,
                ..
            } if mode == Mode::Bridge => Clause::Relation,
            ValueType::PathUniverse(..) if mode == Mode::Identity => Clause::Certificate,

            ValueType::Base(_) => Clause::Discrete,
            // The relation fold reads the unit and binary sums and products;
            // another arity is outside its vocabulary until the fold is n-ary.
            ValueType::Sum(ref parts) | ValueType::Product(ref parts) => {
                let &[left, right] = &**parts
                else {
                    return Err(RelationError::UnsupportedType(ty));
                };
                if !expanded {
                    pending.push((ty, true));
                    pending.push((right, false));
                    pending.push((left, false));
                    continue;
                }
                let left = *formed.get(&left).ok_or(RelationError::Arena)?;
                let right = *formed.get(&right).ok_or(RelationError::Arena)?;
                match *node {
                    ValueType::Sum(..) => Clause::Sum(left, right),
                    ValueType::Data { .. }
                    | ValueType::Record(_)
                    | ValueType::Session { .. }
                    | ValueType::PathUniverse(..)
                    | ValueType::FlowUniverse(..)
                    | ValueType::Path { .. }
                    | ValueType::Flow { .. }
                    | ValueType::Bridge { .. }
                    | ValueType::Base(_)
                    | ValueType::Product(_)
                    | ValueType::Sigma { .. }
                    | ValueType::List(_)
                    | ValueType::Thunk(_)
                    | ValueType::Universe { .. }
                    | ValueType::Lift { .. }
                    | ValueType::Element { .. }
                    | ValueType::Abstract(_)
                    | ValueType::StaticPi { .. }
                    | ValueType::Staged { .. } => Clause::Product(left, right),
                }
            },
            ValueType::List(element) => {
                if !expanded {
                    pending.push((ty, true));
                    pending.push((element, false));
                    continue;
                }
                let element = *formed.get(&element).ok_or(RelationError::Arena)?;
                Clause::List(element)
            },
            ValueType::Thunk(computation) => {
                let Some(&CompType::Arrow {
                    domain: argument,
                    codomain: result,
                }) = arena.comp_type(computation)
                else {
                    return Err(RelationError::UnsupportedType(ty));
                };
                let Some(&CompType::Returner(result)) = arena.comp_type(result)
                else {
                    return Err(RelationError::UnsupportedType(ty));
                };
                if !expanded {
                    pending.push((ty, true));
                    pending.push((result, false));
                    pending.push((argument, false));
                    continue;
                }
                let argument = *formed.get(&argument).ok_or(RelationError::Arena)?;
                let result = *formed.get(&result).ok_or(RelationError::Arena)?;
                Clause::Function(argument, result)
            },
            ValueType::Abstract(atom) => match (interfaces.of_atom(atom), mode) {
                (Some((interface, kind)), Mode::Bridge) => Clause::Atom {
                    relation: interface.relation(),
                    kind,
                },
                (Some((interface, kind)), Mode::Identity)
                    if matches!(interface.law(), Maybe::Present(_)) =>
                {
                    Clause::Atom {
                        relation: interface.relation(),
                        kind,
                    }
                },
                (Some(_), Mode::Identity) => return Err(RelationError::AtomTransport(ty)),
                (None, _) => return Err(RelationError::AbstractInterface(ty)),
            },
            ValueType::Data { .. }
            | ValueType::Record(_)
            | ValueType::Session { .. }
            | ValueType::PathUniverse(..)
            | ValueType::FlowUniverse(..)
            | ValueType::Path { .. }
            | ValueType::Flow { .. }
            | ValueType::Bridge { .. }
            | ValueType::Sigma { .. }
            | ValueType::Universe { .. }
            | ValueType::Lift { .. }
            | ValueType::Element { .. }
            | ValueType::StaticPi { .. }
            | ValueType::Staged { .. } => return Err(RelationError::UnsupportedType(ty)),
        };
        let id = RelationId(nodes.len());
        nodes.push(Node {
            source: ty,
            target: ty,
            clause,
        });
        formed.insert(ty, id);
    }
    let root = *formed.get(&root).ok_or(RelationError::Arena)?;
    Ok(Interpretation::Elements(Relation { mode, nodes, root }))
}

/// Decode a quote without guessing at a neutral code.
///
/// # Specification
/// - ensures: returns the quoted type, or `UnsupportedCode`.
/// - fails: `UnsupportedCode` for every non-quote or unreadable value.
/// - panics: none.
///
/// # Errors
/// `RelationError::UnsupportedCode`.
///
/// # Adequacy
/// - hypothesis: L3 — a value variable is not mistaken for a closed code.
/// - witness: `identity_recursion::tests::abstract_is_an_interface_obstruction`
#[spec(ensures: |ret| match ret {
    Ok(ty) => matches!(arena.value(code), Some(&Value::Quote(quoted)) if ty == quoted),
    Err(RelationError::UnsupportedCode(named)) => named == code && !matches!(arena.value(code), Some(&Value::Quote(_))),
    Err(_) => false,
})]
fn quoted(
    arena: &TermArena,
    code: ValueId,
) -> Result<ValueTypeId, RelationError>
{
    match arena.value(code) {
        Some(&Value::Quote(ty)) => Ok(ty),
        _ => Err(RelationError::UnsupportedCode(code)),
    }
}

impl Interpretation
{
    /// Extract the element-family result of the fold.
    ///
    /// # Specification
    /// - ensures: returns the element relation without reinterpreting any code.
    /// - fails: `Classifier` for either universe clause.
    /// - panics: none.
    ///
    /// # Errors
    /// `RelationError::Classifier`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a universe classifier cannot masquerade as an element
    ///   family.
    /// - witness: `identity_recursion::tests::universe_identity_consumes_path_formation`
    #[spec(
        captures: shape = match self { Self::Elements(ref relation) => Some((relation.mode, relation.root, relation.nodes.len())), Self::UniverseIdentity | Self::UniverseBridge => None },
        ensures: |ret| match ret { Ok(ref relation) => shape == Some((relation.mode, relation.root, relation.nodes.len())), Err(RelationError::Classifier) => shape.is_none(), Err(_) => false },
    )]
    #[inline]
    pub fn elements(self) -> Result<Relation, RelationError>
    {
        match self {
            Self::Elements(relation) => Ok(relation),
            Self::UniverseIdentity | Self::UniverseBridge => Err(RelationError::Classifier),
        }
    }

    /// Form universe identity by the existing certified-equivalence judgement.
    ///
    /// # Specification
    /// - ensures: synthesizes the native path through the ordinary checker,
    ///   then decodes its checked classifier.
    /// - fails: `Classifier` outside identity at Codes; `Typing` for native
    ///   checking failures; `Path` for invalid endpoints or exhausted budget.
    /// - panics: none.
    ///
    /// # Errors
    /// As `fails`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — valid reflexivity forms; malformed equivalences
    ///   refuse through the existing checker, rather than a second identity
    ///   definition.
    /// - witness: `identity_recursion::tests::universe_identity_consumes_path_formation`
    #[spec(ensures: |ret| match ret {
        Ok(endpoints) => matches!(self, Self::UniverseIdentity) && arena.value_type(endpoints.source).is_some() && arena.value_type(endpoints.target).is_some(),
        Err(RelationError::Classifier) => !matches!(self, Self::UniverseIdentity),
        Err(_) => matches!(self, Self::UniverseIdentity),
    })]
    #[inline]
    pub fn path(
        &self,
        arena: &mut TermArena,
        path: ValueId,
        budget: ReplayBudget,
    ) -> Result<path_universe::PathType, RelationError>
    {
        if !matches!(self, Self::UniverseIdentity) {
            return Err(RelationError::Classifier);
        }
        let classifier = crate::check::synth_closed_value(arena, path)
            .map_err(|error| RelationError::Typing(Box::new(error)))?;
        path_universe::endpoints(arena, classifier, budget)
            .map_err(|error| RelationError::Path(Box::new(error)))
    }

    /// Check a relation as a bridge between the two quoted endpoint codes.
    ///
    /// # Specification
    /// - ensures: both endpoints are closed first-order codes and match the
    ///   relation's index types; no equivalence or strict element equality is
    ///   owed.
    /// - fails: `Classifier`, a code-fold error, or `Boundary` for wrong
    ///   indices.
    /// - panics: none.
    ///
    /// # Errors
    /// As `fails`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — Unit-to-Bool accepts a dependent relation, and
    ///   rejects a family with a different right index type.
    /// - witness: `identity_recursion::tests::universe_bridge_is_an_indexed_relation`
    #[spec(ensures: |ret| match ret {
        Err(RelationError::Classifier) => !matches!(self, Self::UniverseBridge),
        Ok(()) | Err(_) => matches!(self, Self::UniverseBridge),
    })]
    #[inline]
    pub fn bridge(
        &self,
        arena: &TermArena,
        source: ValueId,
        target: ValueId,
        family: &Relation,
    ) -> Result<(), RelationError>
    {
        if !matches!(self, Self::UniverseBridge) {
            return Err(RelationError::Classifier);
        }
        let source = interpret(
            arena,
            Interfaces::NONE,
            Mode::Bridge,
            Domain::Elements(source),
        )?;
        let source = source.elements()?;
        let target = interpret(
            arena,
            Interfaces::NONE,
            Mode::Bridge,
            Domain::Elements(target),
        )?;
        let target = target.elements()?;
        let source = source.node(source.root)?;
        let source = source.source;
        let target = target.node(target.root)?;
        let target = target.source;
        let root = family.node(family.root)?;
        same_type(arena, source, root.source)?;
        same_type(arena, target, root.target)
    }
}

impl Relation
{
    /// The mode of the program.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn mode(&self) -> Mode
    {
        self.mode
    }

    /// Resolve a local program address.
    ///
    /// # Specification
    /// - ensures: returns the requested combinator or `Arena`.
    /// - fails: `Arena` for an unresolved address.
    /// - panics: none.
    ///
    /// # Errors
    /// `RelationError::Arena`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — nested product and sum programs preserve child
    ///   boundaries.
    /// - witness: `identity_recursion::tests::both_modes_compute_all_element_clauses`
    #[spec(ensures: |ret| match ret { Ok(node) => self.nodes.get(id.0) == Some(&node), Err(RelationError::Arena) => id.0 >= self.nodes.len(), Err(_) => false })]
    fn node(
        &self,
        id: RelationId,
    ) -> Result<Node, RelationError>
    {
        self.nodes.get(id.0).copied().ok_or(RelationError::Arena)
    }

    /// A constant Unit or Empty bridge over two independently checked codes.
    ///
    /// # Specification
    /// - ensures: constructs the selected constant family without identifying
    ///   endpoint codes or elements. `inhabited` selects Unit versus Empty.
    /// - fails: any code-fold error.
    /// - panics: none.
    ///
    /// # Errors
    /// `UnsupportedCode`, `UnsupportedType`, `AbstractInterface`, `Arena`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — both constant fibres retain heterogeneous indices.
    /// - witness: `identity_recursion::tests::universe_bridge_is_an_indexed_relation`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |relation| relation.mode == Mode::Bridge && relation.nodes.get(relation.root.0).is_some_and(|node|
        matches!((inhabited, node.clause), (Inhabitation::Unit, Clause::Unit) | (Inhabitation::Empty, Clause::Empty))
        && matches!(arena.value(source), Some(&Value::Quote(ty)) if ty == node.source)
        && matches!(arena.value(target), Some(&Value::Quote(ty)) if ty == node.target)) ))]
    #[inline]
    pub fn constant(
        arena: &TermArena,
        source: ValueId,
        target: ValueId,
        inhabited: Inhabitation,
    ) -> Result<Self, RelationError>
    {
        let source = interpret(
            arena,
            Interfaces::NONE,
            Mode::Bridge,
            Domain::Elements(source),
        )?;
        let source = source.elements()?;
        let target = interpret(
            arena,
            Interfaces::NONE,
            Mode::Bridge,
            Domain::Elements(target),
        )?;
        let target = target.elements()?;
        let source = source.node(source.root)?;
        let source = source.source;
        let target = target.node(target.root)?;
        let target = target.source;
        let clause = match inhabited {
            Inhabitation::Unit => Clause::Unit,
            Inhabitation::Empty => Clause::Empty,
        };
        Ok(Self {
            mode: Mode::Bridge,
            nodes: Vec::from([Node {
                source,
                target,
                clause,
            }]),
            root: RelationId(0),
        })
    }

    /// Build a relation by case analysis on either index, consuming both
    /// branches.
    ///
    /// # Specification
    /// - ensures: branch domains become a sum on the selected index; the other
    ///   index is shared definitionally. The resulting family is non-fibrant.
    /// - fails: `Boundary` for incompatible shared index types; `Arena` for a
    ///   malformed local program.
    /// - panics: none.
    ///
    /// # Errors
    /// As `fails`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a right-index case distinguishes both Bool
    ///   injections; the mirror left-index case retains its independent
    ///   argument.
    /// - witness: `identity_recursion::tests::universe_bridge_is_an_indexed_relation`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |relation| relation.mode == Mode::Bridge
        && relation.nodes.get(relation.root.0).is_some_and(|node| match (index, node.clause) {
            (CaseIndex::Left, Clause::CaseLeft(a, b)) => a.0 < relation.root.0 && b.0 < relation.root.0 && matches!(arena.value_type(node.source), Some(&ValueType::Sum(..))),
            (CaseIndex::Right, Clause::CaseRight(a, b)) => a.0 < relation.root.0 && b.0 < relation.root.0 && matches!(arena.value_type(node.target), Some(&ValueType::Sum(..))),
            _ => false,
        }))) ]
    #[inline]
    pub fn cases(
        arena: &mut TermArena,
        index: CaseIndex,
        mut left: Self,
        right: Self,
    ) -> Result<Self, RelationError>
    {
        let first = left.node(left.root)?;
        let second = right.node(right.root)?;
        let (source, target) = match index {
            CaseIndex::Left => {
                same_type(arena, first.target, second.target)?;
                (
                    arena.value_type_sum(&[first.source, second.source]),
                    first.target,
                )
            },
            CaseIndex::Right => {
                same_type(arena, first.source, second.source)?;
                (
                    first.source,
                    arena.value_type_sum(&[first.target, second.target]),
                )
            },
        };
        let offset = RelationOffset(left.nodes.len());
        let right_root = relocate(right.root, offset);
        for mut node in right.nodes {
            node.clause = match node.clause {
                Clause::Product(a, b) => Clause::Product(relocate(a, offset), relocate(b, offset)),
                Clause::Sum(a, b) => Clause::Sum(relocate(a, offset), relocate(b, offset)),
                Clause::List(element) => Clause::List(relocate(element, offset)),
                Clause::Function(a, b) => {
                    Clause::Function(relocate(a, offset), relocate(b, offset))
                },
                Clause::CaseLeft(a, b) => {
                    Clause::CaseLeft(relocate(a, offset), relocate(b, offset))
                },
                Clause::CaseRight(a, b) => {
                    Clause::CaseRight(relocate(a, offset), relocate(b, offset))
                },
                clause @ (Clause::Unit
                | Clause::Empty
                | Clause::Discrete
                | Clause::Universe
                | Clause::Certificate
                | Clause::Relation
                | Clause::Atom { .. }) => clause,
            };
            left.nodes.push(node);
        }
        let clause = match index {
            CaseIndex::Left => Clause::CaseLeft(left.root, right_root),
            CaseIndex::Right => Clause::CaseRight(left.root, right_root),
        };
        left.root = RelationId(left.nodes.len());
        left.nodes.push(Node {
            source,
            target,
            clause,
        });
        left.mode = Mode::Bridge;
        Ok(left)
    }
}

/// The two constant first-order relation fibres.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Inhabitation
{
    /// The unit type.
    Unit,
    /// The empty type.
    Empty,
}

/// Which argument a relation case splits.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CaseIndex
{
    /// The source index.
    Left,
    /// The target index.
    Right,
}

/// A relocation offset within an owned relation program.
#[repr(transparent)]
#[derive(Clone, Copy)]
struct RelationOffset(usize);

/// Shift an address when moving a flat program into another allocation.
///
/// # Specification
/// trivial.
fn relocate(
    id: RelationId,
    offset: RelationOffset,
) -> RelationId
{
    RelationId(id.0.saturating_add(offset.0))
}

/// Require definitional agreement of index types; never element equality.
///
/// # Specification
/// - ensures: success only for structurally convertible kernel types.
/// - fails: `Boundary` otherwise.
/// - panics: none.
///
/// # Errors
/// `RelationError::Boundary`.
///
/// # Adequacy
/// - hypothesis: L3 — mismatched relation indices cannot classify at `Br_U`.
/// - witness: `identity_recursion::tests::universe_bridge_is_an_indexed_relation`
#[spec(ensures: |ret| match ret { Ok(()) => convertible_value_types(arena, left, right) == Convertibility::Convertible, Err(RelationError::Boundary) => convertible_value_types(arena, left, right) == Convertibility::Distinct, Err(_) => false })]
fn same_type(
    arena: &TermArena,
    left: ValueTypeId,
    right: ValueTypeId,
) -> Result<(), RelationError>
{
    match convertible_value_types(arena, left, right) {
        Convertibility::Convertible => Ok(()),
        Convertibility::Distinct => Err(RelationError::Boundary),
    }
}

/// Check an open value by closing its telescope with ordinary dependent arrows.
///
/// # Specification
/// - ensures: value and expected type check in `context`, ordered outermost
///   first; every domain is formed by the ordinary kernel. Temporary wrappers
///   are removed on both outcomes.
/// - fails: `Typing` with the ordinary kernel diagnostic.
/// - panics: none.
///
/// # Errors
/// `RelationError::Typing`.
///
/// # Adequacy
/// - hypothesis: L3 — open base variables check only at their declared types;
///   no synthetic variable can smuggle in an identity assumption.
/// - witness: `identity_recursion::tests::neutral_fibres_do_not_decide_equality`
#[spec(captures: before = arena.watermark(), ensures: arena.watermark() == before)]
fn check_value(
    arena: &mut TermArena,
    context: &[ValueTypeId],
    value: ValueId,
    expected: ValueTypeId,
) -> Result<(), RelationError>
{
    let mark = arena.watermark();
    let mut body = arena.computation_return(value);
    let mut ty = arena.comp_type_returner(expected);
    for &domain in context.iter().rev() {
        body = arena.computation_lambda(body);
        ty = arena.comp_type_pi(domain, ty);
    }
    let value = arena.value_thunk(body);
    let expected = arena.value_type_thunk(ty);
    let result = check_closed_value(arena, value, expected)
        .map_err(|error| RelationError::Typing(Box::new(error)));
    arena.truncate_to(mark);
    result
}
