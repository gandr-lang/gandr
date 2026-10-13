//! The core language: [`Value`] and [`Computation`] on the term side,
//! [`ValueType`] and [`CompType`] on the type side, and the zone-qualified
//! variable reference the two-zone context is read through.
//!
//! # The alphabet is the kernel's; the grammar is this crate's
//!
//! Levels, base types, literals, sum sides, de Bruijn indices and admission
//! positions are re-used from the trusted base rather than restated, so the two
//! languages cannot disagree about what a literal or a level *is* and the
//! erasure that carries a core term down to a kernel term stays an id remapping
//! rather than a payload translation.
//!
//! The node enums are this crate's own, and that is the half that matters: the
//! elaboration-only formers — [`Value::Hole`], [`Value::Mark`], their
//! computation counterparts and the unknown types — enter here rather than
//! widening the vocabulary the kernel is obliged to represent, whose closedness
//! is one of the trusted base's stated properties. The bridge to the kernel
//! refuses every one of them by name; [`crate::hole`] states what they mean.
//!
//! # A variable names its zone
//!
//! The context carries two zones, and a de Bruijn index counts binders within
//! one zone rather than across both, so an occurrence that did not say which
//! zone it counted in would be ambiguous. [`Value::Variable`] therefore carries
//! a [`Zone`] beside its index.
//!
//! No former in the core vocabulary binds into the linear zone, so the linear
//! spelling is reachable only through a context built directly. The zone stays
//! on every occurrence, so a former that binds linearly changes no occurrence
//! site.
//!
//! # Children are ids, and the derived relations are shallow
//!
//! A node's children are typed arena ids and leaf payloads stay inline, so the
//! derived `Clone`, `Drop`, `PartialEq`, `Eq` and `Hash` do not walk term
//! depth. The derived equality is child-id equality rather than structural
//! equality: two structurally equal subterms need not share an id, so every use
//! site either compares inline leaf payloads or resolves ids explicitly.
//!
//! # Kernel alphabet and core grammar
//!
//! Levels, base types, literals, sum sides, de Bruijn indices, admission
//! positions and subterm-table entry indices come from `gandr-kernel-strata`
//! and `gandr-kernel-term`. The two languages therefore agree on what a literal
//! or a level is, and erasing a core term to a kernel term remaps ids without
//! translating payloads; the erasure itself is not in this crate. The node
//! enums, the arena and the context are this crate's own, so an
//! elaboration-only former enters the core grammar without widening the closed
//! vocabulary the kernel represents.
//!
//! ### Effect rows
//!
//! Returner rows are covariant; a shared interface must agree on every
//! operation name and on its invariant payload and reply types. Operation types
//! belong to the returner's binder scope: formation, substitution, import and
//! readback traverse them just as they traverse the result type. A bind
//! accumulates the bound computation's row, including in checking mode.
//! Nonempty rows do not cross into a kernel artifact: readmission reports
//! `UnadmittedFormer::EffectRow`.
//!
//! **Choice.** Canonically ordered, shared interface maps keep pure rows
//! allocation-free and make interface conflicts explicit. An operation carries
//! types, not merely a name, so no ambient registry can change its meaning
//! after checking. Open row variables would support row-polymorphic
//! abstractions but require a solver; revisit when such an abstraction is part
//! of the language contract.
//!
//! Witnesses: `effect::tests::operation_types_survive_substitution_and_import`,
//! `effect::tests::relocation_keeps_names_and_refuses_duplicate_interfaces`,
//! `effect::host::tests::host_interfaces_pin_names_payloads_and_replies`,
//! `formation::tests::effect_operation_types_participate_in_formation_levels_and_scope`,
//! `judgement::tests::check_mode_bind_subsumes_the_accumulated_row` and
//! `bridge::tests::effectful_declarations_are_refused_by_name_at_the_pure_boundary`.
//! The row laws `empty_is_the_bottom`,
//! `subset_is_a_preorder_with_union_as_join`,
//! `union_is_a_canonical_set_and_without_subtracts` and
//! `signature_resolves_operations_by_name` run in `effect::tests`.
//!
//! ### Control syntax
//!
//! `Stack(C, D)` classifies a first-class continuation from computation `C` to
//! `D`; `Reify` records its flat frames in execution order. Apply frames carry
//! values, Bind frames carry independent one-binder computation bodies, and
//! Project frames select a lazy pair. `With(C, D)` classifies a lazy
//! computation pair, distinct from an eager value product.
//!
//! `Perform` and `Handle` carry inline interfaces. A handler return branch
//! binds the returned value; each operation clause binds payload then
//! resumption (`#0` is the resumption). `Shift` binds its captured stack.
//! Interface annotations remain in the ambient scope. Import, substitution and
//! portable content preserve these boundaries. Execution belongs to
//! `gandr-core-sequent`'s machine, not to type conversion or kernel replay.
//!
//! **Choice.** Flat frames preserve independent scopes and make multi-shot
//! resumption explicit. A nested encoding would put later frame operands under
//! earlier binders; host closures would hide frame structure from capture and
//! readback. Revisit only if the language deliberately changes stack scoping or
//! continuation multiplicity.
//!
//! Witnesses: `control::tests::stack_literals_preserve_binder_scope`,
//! `control::tests::stack_types_rebuild_both_computation_children`,
//! `control::tests::effect_interfaces_and_clauses_rewrite_in_their_own_scopes`,
//! `control::tests::lazy_pairs_keep_their_components_and_projection_side`,
//! `tests::focus_properties::hand_built_control_cases_cover_every_former` and
//! `check::tests::control_scopes_are_local_to_each_body`.
//!
//! # Nominal data and structural records
//!
//! A `DataSignature` owns a parameter telescope, constructor field lists in tag
//! order and a positive universe bound. `ValueType::Data` retains the
//! declaration identity and term-valued arguments; `Value::Constructor` retains
//! its full classifier, tag and ordered fields. Parameter classifiers bind
//! their predecessors. Constructor fields see all parameters but do not bind
//! one another. A `DataCase` motive binds one scrutinee; its branches are
//! functions in the ambient context. Iterative rewrites preserve these distinct
//! scopes.
//!
//! Record types and values use ordered field maps. Labels identify fields, not
//! offsets, and `RecordProjection` is a computation returning the selected
//! value. `TupleProjection` is its positional counterpart over a tuple, naming
//! a `Component` by index. All native children participate in syntax equality,
//! rewriting and ownership; arities are not limited to three.
//!
//! **Choice.** Dedicated native forms rather than abstract atoms or a
//! structural sum/product encoding. Typed code parameters and value indices
//! share term-valued slots; the checker keeps every slot invariant.
//! **Reversal.** Certified definitional index conversion requires its own
//! evidence reader. The checker and kernel boundary is stated by
//! `gandr-core-checker`, and its parity floor is tracked in
//! [#199](https://github.com/gandr-lang/gandr/issues/199).
//!
//! A field may name its own declaration's family: the syntax is an ordinary
//! `ValueType::Data` at the declaration's own position, and whether that
//! occurrence is admissible is the checker's question, not the arena's.
//! `Computation::Fixpoint { body, evidence }` is `fix x. M`: its body stands
//! under one intuitionistic binder, the self thunk, so binder rewrites, shifts
//! and substitutions treat it as they treat a lambda. `FixpointEvidence` is the
//! kernel's own, `Partial` or `StructuralDescent`; the arena records the claim
//! and grants nothing, and syntax equality distinguishes the two claims.
//!
//! # N-ary products and sums
//!
//! `ValueType::Product` and `ValueType::Sum` hold their components and summands
//! as an ordered list. The unit type is the empty product, `ValueType::unit()`;
//! no separate unit former exists. Syntax equality, rewriting, import and every
//! walk compare and visit the list in order, so a product of three components
//! is a node of its own, not a nest of binary products.
//!
//! Their introductions and eliminator follow: `Value::Tuple` holds its
//! components in order, with the unit value as the empty tuple,
//! `Value::unit()`; `Value::Injection` names its summand by a `Summand`
//! position rather than a side; and `Computation::Case` holds one branch per
//! summand, in summand order. A tuple of `n` components inhabits an
//! `n`-component product and a case splits a sum of as many summands as it has
//! branches. The kernel's products and sums are n-ary too, so the checker
//! admits every arity: a tuple checks against a product of as many components,
//! an injection against a sum with its summand, and a case against a sum of as
//! many summands as it has branches; the empty sum is the empty type, its case
//! of no branches the absurd elimination. Matching the unknown type answers one
//! unknown type for every component (`hole::Components::Unknown`).
//!
//! `Computation::Split { scrutinee, arity, body }` eliminates a product by
//! binding every component at once: the body stands under one intuitionistic
//! binder per component, component zero outermost and the last innermost, so a
//! split of `n` components reads its last at index zero. The arity is stated
//! rather than read off the scrutinee's type, so that a split of no components
//! is well scoped on its own and types its scrutinee as the unit: it discards a
//! unit value without a projection to name. Syntax equality compares the arity
//! before the children, and `Binders::deeper_by` moves a walk under the body's
//! binders.
//!
//! **Choice.** A motive-less, check-only split with an explicit arity, the
//! n-ary form of the prototype's binary split, beside the positional
//! projection. **Alternatives.** Projection alone, which cannot type the
//! discard of a unit, there being no component to project; a split reading its
//! arity from the scrutinee's type, which leaves the empty split's scope
//! undetermined before checking. **Reversal.** If dependent products arrive,
//! the split gains a motive under the scrutinee binder, as the nominal case
//! has.
//!
//! **Choice.** One n-ary former per connective, with the unit as its empty
//! instance, rather than a binary former, a separate unit and nesting for wider
//! shapes. Nesting fixes an association the source never wrote and makes the
//! unit a special case of every walk. **Alternatives.** A binary former with a
//! distinct unit, the current kernel shape, which keeps every walk two-child
//! but leaves arity to an encoding; a record-only encoding, which loses the
//! positional reading. **Reversal.** If n-ary values and the n-way case cannot
//! be checked without per-arity rules that nesting avoids, return to binary
//! formers and spell wider shapes by nesting.
//!
//! # Native universe paths
//!
//! `PathUniverse(a, b)` is the classifier `Path_U a b`; reflexivity,
//! equivalence and product values introduce native paths, and `Transport`
//! eliminates them. Certificates share the kernel’s portable `PathEvidence`
//! vocabulary. Arena identity and content hashing retain evidence;
//! `equal_certificate_syntax` compares raw classifier and map syntax while
//! erasing evidence only. Computationally equivalent maps do not thereby
//! identify certificates. Binder rewrites traverse classifier codes and
//! translator bodies without reducing those maps.
//!
//! **Choice.** Native syntax in the ordinary arena, rather than a second path
//! arena with different traversal and ownership rules. Core syntax itself
//! grants no admission authority: the checker validates the closed endpoint
//! fragment and the kernel replays candidates. Element-identity, higher-field,
//! bridge-mode and `Flow_U` programs remain separate kernel APIs. **Reversal.**
//! Extending the code fragment requires corresponding formation, admission and
//! replay rules, not a syntax-only permission.
//!
//! # Static operators
//!
//! A type operator such as `\A. A * A` is a code-level function: it takes codes
//! and returns a code, and it is gone before runtime. The core spells it with
//! three value-family formers. `ValueType::StaticPi { domain, codomain }`
//! classifies operators; `Value::StaticLambda` abstracts over one
//! intuitionistic binder; `Value::StaticApplication` applies an operator to a
//! code. All three are values because codes are values (§ Universe families):
//! an operator is a code that awaits codes, so it lives where codes live, and
//! an application is a code too. It decodes through `ValueType::Element` or
//! `CompType::Element` like any other code.
//!
//! The static Pi is non-dependent: its codomain stands in the ambient context,
//! as `CompType::Arrow`'s does, not under a binder. Its domain and codomain are
//! themselves static classifiers: universes, or static Pis over them. That is
//! the simply kinded discipline of System Fω, enough for a family such as `Type
//! -> Type[-]` and for a relative monad's carrier. Dependency at the type level
//! would make classifiers mention codes, and with them the kernel's conversion
//! would have to compare open codes.
//!
//! A static application whose head is a static lambda is a redex, and the arena
//! represents it. Arena constructors do not reduce it. Static beta belongs to
//! the normalizer in `gandr-core-nbe`, which reads back static normal forms,
//! and `instantiate_value` is the one substitution step a certificate replays.
//! Keeping the redex representable means the elaborator can write a family's
//! use as it stands in the source, and the checker can name each unfolding it
//! performs.
//!
//! Alternatives:
//!
//! - a separate static-term language with its own arena family, which
//!   duplicates every walk, every binder machine and every content codec;
//! - type operators as computation-family functions over thunked codes, which
//!   puts code-level reduction under effects;
//! - reduce on mint, as decode does, which would hide the redex the certificate
//!   names and would need substitution inside the arena.
//!
//! Reversal: a family whose classifier must mention a code, at which point the
//! static Pi gains a binder and the kernel's conversion gains open codes.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_strata::Level;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::Component;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::ConstructorTag;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FieldLabel;
use gandr_kernel_term::FixpointEvidence;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Side;
use gandr_kernel_term::Summand;

use crate::arena::CompTypeId;
use crate::arena::ComputationId;
use crate::arena::ValueId;
use crate::arena::ValueTypeId;
use crate::classifier::Sort;
use crate::hole::HoleId;
use crate::hole::MarkIndex;

/// The zone of the unified context a binder or an occurrence belongs to.
///
/// The two zones are `Γ; Σ`: the intuitionistic zone, whose bindings admit
/// weakening and contraction, and the linear zone, whose bindings are consumed
/// exactly once. They are separate flat stacks with separate de Bruijn index
/// spaces, so an index alone does not identify a binder.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Zone
{
    /// The intuitionistic zone `Γ`: structural, reusable bindings.
    Intuitionistic,
    /// The linear zone `Σ`: one-shot bindings, the type-level form of "a
    /// control capture cannot be naively duplicated".
    Linear,
}

/// A value: the positive fragment of the core term vocabulary.
///
/// Values are the total, thunkable half of the polarity split; the only value
/// embedding a computation is [`Self::Thunk`], and a thunk suspends rather than
/// runs it.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Value
{
    /// A table-typed prelude thunk, with its generated curried body.
    Primitive
    {
        /// The row defining the thunk's signature.
        primitive: crate::primitive::Primitive,
        /// The generated lambda chain, ending in the saturated operation.
        body: ComputationId,
    },
    /// Reflexivity at a quoted closed code.
    PathRefl(ValueId),
    /// Componentwise product of two native path values.
    PathProduct(ValueId, ValueId),
    /// A native equivalence with untrusted, arena-independent replay evidence.
    PathEquiv
    {
        /// The native universe-path classifier.
        path_type: ValueTypeId,
        /// The closed forward translator.
        forward: ValueId,
        /// The closed backward translator.
        backward: ValueId,
        /// Both round-trip dialogues, checked again at kernel admission.
        evidence: alloc::sync::Arc<gandr_kernel_term::PathEvidence>,
    },
    /// Reflexivity `here(a)`: the canonical element of the element identity
    /// `Path(A, a, a)`, checked against a path type whose two endpoints convert
    /// to `a`.
    Here(ValueId),
    /// Function extensionality `funext(f, g)`: an element of `Path(U (A → F
    /// B), f, g)` for two closed functions that return the same value at
    /// every input the domain's coverage reaches. The checker decides it by
    /// computation, and the kernel replays it as a higher evaluation; it is
    /// inert, as a native path certificate is.
    Funext(ValueId, ValueId),
    /// A universe equivalence `equiv(f, g)`: an element of `Path(U, a, b)` for
    /// two closed translators `f : U (A → F B)` and `g : U (B → F A)`, `a` and
    /// `b` the quotes of `A` and `B`, whose round trips return their input at
    /// every pattern either code's coverage reaches. The checker decides it by
    /// computation, and the kernel admits it as the native universe path its
    /// fibre is; it is inert, as a native path certificate is.
    Equiv(ValueId, ValueId),
    /// Univalence at a stated stratum, `ua[n, k](a, b, f, g)`: an element of
    /// `Path(U, ⌜Tel a⌝, ⌜Tel b⌝)` for two descriptions read as graphical
    /// species, `Tel` the telescope of their elements at each corolla of the
    /// catalogue, and a record of translators each way keyed by generator. The
    /// checker decides it at the stratum and records the path it derives, and
    /// the kernel admits that path; it is inert, as a native path certificate
    /// is.
    Ua
    {
        /// The degree and the catalogue bound the statement is made at.
        stratum: crate::ua::Stratum,
        /// The two descriptions, the source first.
        sides: alloc::sync::Arc<crate::ua::Sides>,
        /// The forward translators: a record keyed by the source's generators.
        forward: ValueId,
        /// The backward translators: a record keyed by the target's
        /// generators.
        backward: ValueId,
    },
    /// The value a pure computation returns, standing where a value is read:
    /// a compound path endpoint such as `n + 1` or `f(x)`. It types as the
    /// computation's result when the computation is a returner with no
    /// effects, and evaluates by running the computation, so the endpoint is
    /// compared by what it computes rather than erased.
    Returned(ComputationId),
    /// A computation written where a value is read, with no keyword: before
    /// elaboration only. The checker decides it by the type expected there —
    /// against a thunk type it suspends, as a thunk does; against any other it
    /// runs, before the innermost computation enclosing it, and stands for the
    /// value it returns — and elaboration replaces it by the thunk or by the
    /// variable of the bind it mints, so neither the kernel nor the evaluator
    /// meets it. It only checks: with no expected type there is nothing to
    /// decide by.
    Nested(ComputationId),
    /// A written `run c` standing where a value is read: before elaboration
    /// only. It runs the computation before the innermost computation enclosing
    /// it and stands for the value the computation returns, which is what it
    /// synthesises; elaboration replaces it by the variable of the bind it
    /// mints.
    Run(ComputationId),
    /// A bound value variable, in a named zone of the unified context.
    Variable
    {
        /// The zone whose binder stack the index counts in.
        zone: Zone,
        /// The de Bruijn index, counting binders outward from the use site
        /// within `zone` alone.
        index: DeBruijnIndex,
    },
    /// A reference to a prior declaration by its admission position.
    Constant(ConstantIndex),
    /// A base-type literal.
    Literal(Literal),
    /// A tuple, introducing a product with one value per component, in
    /// order. The empty tuple is the unit value.
    Tuple(alloc::boxed::Box<[ValueId]>),
    /// A sum injection, introducing a sum at the given summand.
    Injection(Summand, ValueId),
    /// The empty native list, checked against its element type.
    ListNil,
    /// A native list cell with its head and list tail.
    ListCons(ValueId, ValueId),
    /// A thunk, suspending a computation into the value type `U C`.
    Thunk(ComputationId),
    /// An explicit universe lift: given `body : A` with `A`'s level strictly
    /// below `target`, this value inhabits `Lift A target`. There is no
    /// implicit cumulativity, so the lift is written rather than inferred.
    Lift
    {
        /// The target universe level of the lift.
        target: Level,
        /// The value being lifted.
        body: ValueId,
    },
    /// The quote `⌜A⌝` of a value type: the code of `A`, inhabiting
    /// `Type[+, l]` where `l` is `A`'s level.
    Quote(ValueTypeId),
    /// The quote `⌜C⌝` of a computation type: the code of `C`, inhabiting
    /// `Type[-, l]` where `l` is `C`'s level. A computation type's code is a
    /// value like any other code: quoting suspends nothing.
    QuoteComputation(CompTypeId),
    /// A static lambda `λ. v`, binding one intuitionistic value variable over
    /// a value body: a type operator, introducing a static Pi. It is static
    /// content, erased before runtime, and the kernel never represents it.
    StaticLambda(ValueId),
    /// A static application `f a` of a type operator to a value argument,
    /// eliminating a static Pi. Applied to a static lambda it is a static
    /// redex; applied to anything else it stands as a neutral spine.
    StaticApplication(ValueId, ValueId),
    /// A constructor of a nominal application, with declaration-ordered fields.
    Constructor
    {
        /// The complete nominal classifier, including its arguments.
        datatype: ValueTypeId,
        /// The constructor's ordinal in its declaration.
        tag: ConstructorTag,
        /// Ordinary field values in signature order.
        fields: Vec<ValueId>,
    },
    /// A structural record, in exact UTF-8 label order.
    Record(BTreeMap<FieldLabel, ValueId>),
    /// A typed hole: a value the author has not written yet, named so a fill
    /// can find it. It synthesises [`ValueType::Unknown`] and checks against
    /// any type.
    Hole(HoleId),
    /// A marked value: a subterm the elaborator could not type, kept in place
    /// under the mark-table entry that says why. It types as a hole does and
    /// its body is not judged.
    Mark
    {
        /// The mark-table entry recording the refusal.
        mark: MarkIndex,
        /// The subterm as written.
        body: ValueId,
    },
    /// A first-class stack, ordered from the first observation to its answer.
    Reify(alloc::sync::Arc<[crate::control::StackFrame]>),
}

impl Value
{
    /// The unit value: the tuple of no components.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `Tuple([])`.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the unit built here and the one the arena mints are
    ///   the same node, and a tuple of two components is not the unit.
    /// - witness: `syntax::tests::the_unit_is_the_empty_tuple`
    #[spec(ensures: |ret| matches!(ret, Self::Tuple(ref components) if components.is_empty()))]
    #[inline]
    #[must_use]
    pub fn unit() -> Self
    {
        Self::Tuple(alloc::boxed::Box::default())
    }

    /// The components of a tuple, in order; nothing for any other former.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the tuple's own component list for a tuple, and nothing for
    ///   every other former.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a tuple of two components, the empty tuple and an
    ///   injection separate the tuple reading from every other former.
    /// - witness: `syntax::tests::the_unit_is_the_empty_tuple`
    #[spec(ensures: |ret| match *self { Self::Tuple(ref components) => ret == Some(&**components), _ => ret.is_none() })]
    #[inline]
    #[must_use]
    pub fn components(&self) -> Option<&[ValueId]>
    {
        match *self {
            | Self::Tuple(ref components) => Some(components),
            | _ => None,
        }
    }
}

/// How many components a product elimination binds.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ComponentCount(usize);

impl From<usize> for ComponentCount
{
    /// The count of `components`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(components: usize) -> Self
    {
        Self(components)
    }
}

impl From<ComponentCount> for usize
{
    /// The number of components.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: ComponentCount) -> Self
    {
        count.0
    }
}

/// A computation: the negative fragment of the core term vocabulary.
///
/// The eliminators — application, force, bind, case — synthesize; the
/// introductions — lambda, return, fixpoint — check against an expected
/// computation type.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Computation
{
    /// A saturated native operation; currying uses ordinary lambdas.
    Primitive
    {
        /// The row defining names, signature and evaluation.
        primitive: crate::primitive::Primitive,
        /// Value arguments in source order.
        arguments: crate::primitive::Arguments,
    },
    /// Transport a value along a native universe path.
    Transport(ValueId, ValueId),
    /// Transport `tr(P, p, x)` along an element path: given `p : Path(A, a,
    /// b)` and `x : P[a]`, it returns `P[b]`. The motive `P` is a value type
    /// under one intuitionistic binder of the carrier `A`.
    PathTransport
    {
        /// The motive, under one intuitionistic binder: the moving endpoint.
        motive: ValueTypeId,
        /// The element path transported along.
        path: ValueId,
        /// The value transported, an inhabitant of the motive at the path's
        /// left endpoint.
        value: ValueId,
    },
    /// Transport over a two-entry telescope: given `p : Path(A, a, b)`, `z₀ :
    /// B[a]`, `q : Path(B[b], ⟨tr(B, p, z₀)⟩, z₁)` and `x : C[a, z₀]`, it
    /// returns `C[b, z₁]`. The motive is the dependent arrow `Π (y : A). Π (z
    /// : B). F C`: the path moves the first entry and `q`, an identity over
    /// it, the second.
    TelescopeTransport
    {
        /// The motive, whose arrows bind the telescope's two entries.
        motive: CompTypeId,
        /// The identity in the carrier.
        path: ValueId,
        /// The family element at the path's source.
        start: ValueId,
        /// The identity over the path, in the fibre at its target.
        over: ValueId,
        /// The value transported, an inhabitant of the body at the source
        /// pair.
        value: ValueId,
    },
    /// A lambda `λ. M`, binding one intuitionistic value variable; introduces
    /// `A → C`.
    Lambda(ComputationId),
    /// A fixpoint `fix x. M`, binding its own thunk `x : U C` as one
    /// intuitionistic value variable over `M : C`; it checks at any
    /// computation type and carries the termination claim it is offered
    /// with.
    Fixpoint
    {
        /// The body, under the self binder.
        body: ComputationId,
        /// The termination claim.
        evidence: FixpointEvidence,
    },
    /// An application `M v` of a computation to a value argument.
    Application(ComputationId, ValueId),
    /// A returner `return v`, introducing `F A`.
    Return(ValueId),
    /// A sequencing bind `x ← M; N`, binding the value `M` returns into `N`.
    Bind(ComputationId, ComputationId),
    /// A force `force v` of a thunk value `v : U C`, running it as `C`.
    Force(ValueId),
    /// A sum elimination, binding the injected value into the branch of its
    /// summand.
    Case
    {
        /// The scrutinee value, of a sum type.
        scrutinee: ValueId,
        /// One branch per summand, in order, each checked with its summand
        /// bound.
        branches: alloc::boxed::Box<[ComputationId]>,
    },
    /// A product elimination, binding every component of the scrutinee into
    /// the body: component zero outermost, the last innermost. The arity is
    /// the scrutinee's own, stated so that a split of no components types its
    /// scrutinee as the unit.
    Split
    {
        /// The scrutinee value, of a product type.
        scrutinee: ValueId,
        /// How many components the scrutinee has, each bound in the body.
        arity: ComponentCount,
        /// The body, under one intuitionistic binder per component.
        body: ComputationId,
    },
    /// A nominal case with a motive under one scrutinee binder.
    DataCase
    {
        /// The nominal value being eliminated.
        scrutinee: ValueId,
        /// Result type under one intuitionistic scrutinee binder.
        motive: CompTypeId,
        /// One ordinary function over the constructor's fields per tag.
        branches: Vec<ComputationId>,
    },
    /// Select a named field, returning it in the computation fragment.
    RecordProjection(ValueId, FieldLabel),
    /// Select a tuple's component by position, returning it in the
    /// computation fragment.
    TupleProjection(ValueId, Component),
    /// A typed hole in computation position. It synthesises
    /// [`CompType::Unknown`] and checks against any computation type.
    Hole(HoleId),
    /// A marked computation: a subterm the elaborator could not type, kept in
    /// place under the mark-table entry that says why.
    Mark
    {
        /// The mark-table entry recording the refusal.
        mark: MarkIndex,
        /// The subterm as written.
        body: ComputationId,
    },
    /// A pure right fold; the cell branch binds head then folded result.
    ListFold
    {
        /// Element type in the ambient context.
        element: ValueTypeId,
        /// Result type in the ambient context.
        result: ValueTypeId,
        /// Native list to eliminate.
        list: ValueId,
        /// Empty branch in the ambient context.
        on_nil: ComputationId,
        /// Cell branch beneath two intuitionistic binders.
        on_cons: ComputationId,
    },
    /// Perform an operation from an inline-carried interface.
    Perform
    {
        /// Operation names and their payload and reply types.
        signature: crate::effect::EffectSig,
        /// The selected operation.
        operation: crate::effect::OperationName,
        /// Its value payload.
        payload: ValueId,
    },
    /// Handle one interface deeply; clauses run outside the handled scope.
    Handle
    {
        /// The interface whose operations are handled.
        signature: crate::effect::EffectSig,
        /// The computation being handled.
        subject: ComputationId,
        /// Return clause beneath one intuitionistic result binder.
        on_return: ComputationId,
        /// Operation clauses beneath payload then resumption binders.
        clauses: alloc::sync::Arc<[crate::control::EffectClause]>,
    },
    /// Feed a computation to a first-class stack.
    Resume(ValueId, ComputationId),
    /// Delimit a continuation capture.
    Reset(ComputationId),
    /// Capture to the nearest reset, binding one intuitionistic stack value.
    Shift(ComputationId),
    /// A lazy negative pair; only the observed component executes.
    With(ComputationId, ComputationId),
    /// Observe one component of a negative product.
    Project(Side, ComputationId),
}

/// A value type: the positive fragment of the core type vocabulary.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum ValueType
{
    /// A generative nominal head applied to its declared parameter telescope.
    Data
    {
        /// Admission position of the defining signature; never a carrier alias.
        declaration: ConstantIndex,
        /// Quoted type or ordinary value arguments, in telescope order.
        arguments: Vec<ValueId>,
    },
    /// A structural record classifier, in exact UTF-8 label order.
    Record(BTreeMap<FieldLabel, ValueTypeId>),
    /// Certified equivalences between two quoted closed first-order codes.
    PathUniverse(ValueId, ValueId),
    /// Element identity `Path(A, a, b)`: the type of paths from `a` to `b` in
    /// the value type `A`. It is a type of its own, never unfolded into
    /// another former; the evaluator's identity recursion classifies, carrier
    /// by carrier, the type its paths correspond to.
    Path
    {
        /// The carrier the two endpoints inhabit.
        carrier: ValueTypeId,
        /// The left endpoint.
        left: ValueId,
        /// The right endpoint.
        right: ValueId,
    },
    /// A rigid base-type atom.
    Base(BaseType),
    /// The product of its components, in order: `Product([])` is the unit
    /// type, inhabited by the empty [`Value::Tuple`] alone, and
    /// `Product([A, B])` the pair type `A × B`.
    Product(alloc::boxed::Box<[ValueTypeId]>),
    /// The sum of its summands, in order: `Sum([])` is the empty type and
    /// `Sum([A, B])` the binary sum `A + B`, with left and right injections.
    Sum(alloc::boxed::Box<[ValueTypeId]>),
    /// The native finite-list type over its element type.
    List(ValueTypeId),
    /// The thunk type `U C` of a computation type `C`.
    Thunk(CompTypeId),
    /// The universe of one sort at a canonical level `l`: `Type[+, l]`
    /// classifies the value types at `l` and `Type[-, l]` the computation
    /// types. Both are value types, whose own level is `l + 1`.
    Universe
    {
        /// The family the universe classifies.
        sort: Sort,
        /// The level within that family.
        level: Level,
    },
    /// An explicit lift of a value type into a strictly higher universe.
    Lift
    {
        /// The value type being lifted.
        inner: ValueTypeId,
        /// The target universe level, which is the lifted type's level.
        target: Level,
    },
    /// The value type a code denotes: `El l v`, where `v` is a value of type
    /// `Type[+, l]`. It is one of the two formers whose child crosses from the
    /// type language into the term language, which is what lets a dependent
    /// codomain mention its binder at all.
    ///
    /// A decode of a quote is the quoted type: the arena mints the type
    /// itself rather than this node, so `El ⌜A⌝` is never represented.
    Element
    {
        /// The code: a value whose type is `Type[+, target]`.
        code: ValueId,
        /// The universe the code is read out of, which is this type's own
        /// level.
        target: Level,
    },
    /// A sealed abstract type: a nominal atom named by the admission position
    /// of the declaration that introduced it.
    Abstract(ConstantIndex),
    /// The static Pi: the classifier of a type operator, taking an operand
    /// classified by the domain to a result classified by the codomain.
    /// Formation admits only static classifiers — universes and static Pis —
    /// as either child, and a static classifier mentions no term variable, so
    /// the codomain cannot depend on the operand and stands in the ambient
    /// context: the [`CompType::Arrow`] scoping, not the [`CompType::Pi`] one.
    StaticPi
    {
        /// The classifier of the operand, in the ambient context.
        domain: ValueTypeId,
        /// The classifier of the result, in the ambient context.
        codomain: ValueTypeId,
    },
    /// The unknown value type: what a hole or a mark synthesises. It is
    /// consistent with every value type and matches every former with unknown
    /// components.
    Unknown,
    /// A first-class continuation consuming one computation and delivering
    /// another.
    Stack
    {
        /// The computation consumed by the stack.
        input: CompTypeId,
        /// The answer delivered by the stack.
        output: CompTypeId,
    },
}

impl ValueType
{
    /// The unit type: the product of no components.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `Product([])`.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the unit built here and the one the arena mints are
    ///   the same node, and a product of two components is not the unit.
    /// - witness: `syntax::tests::the_unit_is_the_empty_product`
    #[spec(ensures: |ret| matches!(ret, Self::Product(ref components) if components.is_empty()))]
    #[inline]
    #[must_use]
    pub fn unit() -> Self
    {
        Self::Product(alloc::boxed::Box::default())
    }
}

/// A computation type: the negative fragment of the core type vocabulary.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum CompType
{
    /// The returner `F^effects A` of a value type `A`.
    Returner
    {
        /// The returned value type.
        result: ValueTypeId,
        /// The closed set of interfaces this computation may perform.
        effects: crate::effect::EffectRow,
    },
    /// The non-dependent function type `A → C`: its codomain stands in the
    /// ambient context and binds nothing.
    Arrow
    {
        /// The value-type domain.
        domain: ValueTypeId,
        /// The computation-type codomain, in the ambient context.
        codomain: CompTypeId,
    },
    /// The dependent function type `Π (x : A). C`, whose codomain stands in the
    /// ambient context extended by the domain's binder.
    ///
    /// The scoping is the whole difference from [`Self::Arrow`], which is why
    /// the two are distinct nodes rather than one former with a flag: the same
    /// two children mean two different things, and a flag would make a child's
    /// meaning depend on a payload.
    Pi
    {
        /// The value-type domain, in the ambient context.
        domain: ValueTypeId,
        /// The computation-type codomain, under the domain's binder.
        codomain: CompTypeId,
    },
    /// The computation type a code denotes: `El l v`, where `v` is a value of
    /// type `Type[-, l]`.
    ///
    /// Like its value counterpart, a decode of a computation quote is the
    /// quoted computation type and is never represented as this node.
    Element
    {
        /// The code: a value whose type is `Type[-, target]`.
        code: ValueId,
        /// The universe the code is read out of, which is this type's own
        /// level.
        target: Level,
    },
    /// The unknown computation type: what a hole or a mark in computation
    /// position synthesises.
    Unknown,
    /// A lazy negative product; an observation selects one component.
    With(CompTypeId, CompTypeId),
}

/// One pair of native syntax roots awaiting structural comparison.
#[derive(Clone, Copy, Eq, Ord, PartialEq, PartialOrd)]
enum StructuralGoal
{
    /// Values.
    Value(ValueId, ValueId),
    /// Computations.
    Computation(ComputationId, ComputationId),
    /// Value types.
    ValueType(ValueTypeId, ValueTypeId),
    /// Computation types.
    CompType(CompTypeId, CompTypeId),
}

/// Result of evidence-erasing certificate syntax comparison.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CertificateEquality
{
    /// Every constructor and non-evidence payload agrees.
    Equal,
    /// Syntax differs, or a requested node is unreadable.
    Different,
}

/// Compare native certificate syntax, erasing evidence but performing no
/// reduction.
///
/// # Specification
/// - requires: nothing; unreadable roots or children fail closed.
/// - ensures: compares every constructor, leaf and child, except path evidence;
///   distinct translator programs stay distinct even if extensionally equal.
/// - provides: certificate conversion independent of allocation and proof
///   bytes.
/// - fails: returns `Different` on a dangling node.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — fresh allocations and different evidence compare equal;
///   an administrative translator redex changes the certificate.
/// - witness: `syntax::tests::certificate_syntax_erases_only_evidence`
#[spec(ensures: |ret| match (arena.value(left), arena.value(right)) {
    (Some(a), Some(b)) if matches!(*a, Value::Tuple(ref x) if x.is_empty()) && matches!(*b, Value::Tuple(ref y) if y.is_empty()) => ret == CertificateEquality::Equal,
    (Some(a), Some(b)) => ret != CertificateEquality::Equal || core::mem::discriminant(a) == core::mem::discriminant(b),
    _ => ret == CertificateEquality::Different,
})]
#[inline]
#[must_use]
pub fn equal_certificate_syntax(
    arena: &crate::CoreArena,
    left: ValueId,
    right: ValueId,
) -> CertificateEquality
{
    equal_syntax(arena, StructuralGoal::Value(left, right))
}

/// Compare signature type syntax without making allocation identity observable.
///
/// # Specification
/// - ensures: equal roots have the same former and structurally equal children.
/// - fails: unreadable roots or children compare different.
///
/// # Adequacy
/// - hypothesis: L3 — separately allocated equal signatures retain row
///   inclusion; changing an operation reply removes inclusion.
/// - witness: `effect::tests::signature_inclusion_ignores_allocation_identity`
#[spec(ensures: |ret| ret != CertificateEquality::Equal || match (arena.value_type(left), arena.value_type(right)) {
    (Some(left), Some(right)) => core::mem::discriminant(left) == core::mem::discriminant(right),
    _ => false,
})]
#[inline]
#[must_use]
pub fn equal_type_syntax(
    arena: &crate::CoreArena,
    left: ValueTypeId,
    right: ValueTypeId,
) -> CertificateEquality
{
    equal_syntax(arena, StructuralGoal::ValueType(left, right))
}

/// Queue operation type pairs after checking interface and operation
/// identities.
///
/// # Specification
/// - ensures: [`CertificateEquality::Equal`] preserves names and queues payload
///   before reply per operation; [`CertificateEquality::Different`] queues
///   nothing further for a mismatched name or arity.
/// - executable: none — this is the structural comparison's work-list rule.
///
/// # Adequacy
/// - hypothesis: L3 — reordered allocations preserve equality, changed replies
///   do not.
/// - witness: `effect::tests::signature_inclusion_ignores_allocation_identity`
fn signature_children(
    pending: &mut alloc::vec::Vec<StructuralGoal>,
    left: &crate::effect::EffectSig,
    right: &crate::effect::EffectSig,
) -> CertificateEquality
{
    if left.name() != right.name() || left.operations().len() != right.operations().len() {
        return CertificateEquality::Different;
    }
    for (left, right) in left.operations().zip(right.operations()) {
        if left.name != right.name {
            return CertificateEquality::Different;
        }
        pending.extend([
            StructuralGoal::ValueType(left.payload, right.payload),
            StructuralGoal::ValueType(left.reply, right.reply),
        ]);
    }
    CertificateEquality::Equal
}

/// Run the shared, evidence-erasing structural comparison.
///
/// # Specification
/// - ensures: returns equal exactly when every reached pair agrees in syntax
///   after path evidence is erased; no reduction is performed.
/// - executable: none — the contract is the inductive graph comparison, not a
///   second traversal pretending to be an independent postcondition.
///
/// # Adequacy
/// - hypothesis: L3 — both certificate and type roots must reach the same child
///   comparison rules without depending on allocation order.
/// - witness: `syntax::tests::certificate_syntax_erases_only_evidence`
/// - witness: `effect::tests::signature_inclusion_ignores_allocation_identity`
fn equal_syntax(
    arena: &crate::CoreArena,
    root: StructuralGoal,
) -> CertificateEquality
{
    use StructuralGoal::CompType as CT;
    use StructuralGoal::Computation as C;
    use StructuralGoal::Value as V;
    use StructuralGoal::ValueType as VT;
    let mut pending = alloc::vec![root];
    let mut visited = alloc::collections::BTreeSet::new();
    while let Some(goal) = pending.pop() {
        if !visited.insert(goal) {
            continue;
        }
        match goal {
            | V(a, b) => {
                let (Some(a), Some(b)) = (arena.value(a), arena.value(b))
                else {
                    return CertificateEquality::Different;
                };
                {
                    let (matched_left_value, matched_right_value) = (a, b);
                    if let Value::Constructor {
                        datatype: a,
                        tag: ta,
                        fields: ref fa,
                    } = *matched_left_value
                        && let Value::Constructor {
                            datatype: b,
                            tag: tb,
                            fields: ref fb,
                        } = *matched_right_value
                        && (ta == tb && fa.len() == fb.len())
                    {
                        {
                            pending.push(VT(a, b));
                            pending.extend(fa.iter().zip(fb).map(|(a, b)| V(*a, *b)));
                        }
                    }
                    else if let Value::Record(ref a) = *matched_left_value
                        && let Value::Record(ref b) = *matched_right_value
                        && (a.len() == b.len() && a.keys().eq(b.keys()))
                    {
                        {
                            pending.extend(a.values().zip(b.values()).map(|(a, b)| V(*a, *b)));
                        }
                    }
                    else if let Value::Reify(ref left) = *matched_left_value
                        && let Value::Reify(ref right) = *matched_right_value
                        && left.len() == right.len()
                    {
                        for (left, right) in left.iter().zip(right.iter()) {
                            match (*left, *right) {
                                | (
                                    crate::control::StackFrame::Apply(left),
                                    crate::control::StackFrame::Apply(right),
                                ) => pending.push(V(left, right)),
                                | (
                                    crate::control::StackFrame::Bind(left),
                                    crate::control::StackFrame::Bind(right),
                                ) => pending.push(C(left, right)),
                                | (
                                    crate::control::StackFrame::Project(left),
                                    crate::control::StackFrame::Project(right),
                                ) if left == right => {},
                                | _ => return CertificateEquality::Different,
                            }
                        }
                    }
                    else if matches!(
                        (matched_left_value, matched_right_value),
                        (&Value::ListNil, &Value::ListNil)
                    ) {
                    }
                    else if let (&Value::ListCons(a, b), &Value::ListCons(c, d)) =
                        (matched_left_value, matched_right_value)
                    {
                        pending.extend([V(a, c), V(b, d)]);
                    }
                    else if let Value::PathRefl(a) = *matched_left_value
                        && let Value::PathRefl(b) = *matched_right_value
                    {
                        pending.push(V(a, b));
                    }
                    else if let Value::Here(a) = *matched_left_value
                        && let Value::Here(b) = *matched_right_value
                    {
                        pending.push(V(a, b));
                    }
                    else if let Value::Returned(a) = *matched_left_value
                        && let Value::Returned(b) = *matched_right_value
                    {
                        pending.push(C(a, b));
                    }
                    else if let (&Value::Nested(a), &Value::Nested(b))
                    | (&Value::Run(a), &Value::Run(b)) =
                        (matched_left_value, matched_right_value)
                    {
                        pending.push(C(a, b));
                    }
                    else if let Value::StaticLambda(a) = *matched_left_value
                        && let Value::StaticLambda(b) = *matched_right_value
                    {
                        pending.push(V(a, b));
                    }
                    else if let Value::PathProduct(a, b) = *matched_left_value
                        && let Value::PathProduct(c, d) = *matched_right_value
                    {
                        {
                            pending.extend([V(a, c), V(b, d)]);
                        }
                    }
                    else if let (&Value::Funext(a, b), &Value::Funext(c, d))
                    | (&Value::Equiv(a, b), &Value::Equiv(c, d)) =
                        (matched_left_value, matched_right_value)
                    {
                        pending.extend([V(a, c), V(b, d)]);
                    }
                    else if let Value::Tuple(ref a) = *matched_left_value
                        && let Value::Tuple(ref b) = *matched_right_value
                        && a.len() == b.len()
                    {
                        pending.extend(a.iter().zip(b.iter()).map(|(a, b)| V(*a, *b)));
                    }
                    else if let Value::StaticApplication(a, b) = *matched_left_value
                        && let Value::StaticApplication(c, d) = *matched_right_value
                    {
                        {
                            pending.extend([V(a, c), V(b, d)]);
                        }
                    }
                    else if let Value::PathEquiv {
                        path_type: left_type,
                        forward: left_forward,
                        backward: left_backward,
                        ..
                    } = *matched_left_value
                        && let Value::PathEquiv {
                            path_type: right_type,
                            forward: right_forward,
                            backward: right_backward,
                            ..
                        } = *matched_right_value
                    {
                        pending.extend([
                            VT(left_type, right_type),
                            V(left_forward, right_forward),
                            V(left_backward, right_backward),
                        ]);
                    }
                    else if let Value::Ua {
                        stratum: left_stratum,
                        sides: ref left_sides,
                        forward: left_forward,
                        backward: left_backward,
                    } = *matched_left_value
                        && let Value::Ua {
                            stratum: right_stratum,
                            sides: ref right_sides,
                            forward: right_forward,
                            backward: right_backward,
                        } = *matched_right_value
                        && left_stratum == right_stratum
                        && left_sides == right_sides
                    {
                        pending.extend([
                            V(left_forward, right_forward),
                            V(left_backward, right_backward),
                        ]);
                    }
                    else if let Value::Injection(s, a) = *matched_left_value
                        && let Value::Injection(t, b) = *matched_right_value
                        && (s == t)
                    {
                        {
                            pending.push(V(a, b));
                        }
                    }
                    else if let Value::Thunk(a) = *matched_left_value
                        && let Value::Thunk(b) = *matched_right_value
                    {
                        pending.push(C(a, b));
                    }
                    else if let Value::Primitive { primitive: a, .. } = *matched_left_value
                        && let Value::Primitive { primitive: b, .. } = *matched_right_value
                        && (a == b)
                    {
                        {}
                    }
                    else if let Value::Lift { ref target, body } = *matched_left_value
                        && let Value::Lift {
                            target: ref other,
                            body: right,
                        } = *matched_right_value
                        && (target == other)
                    {
                        pending.push(V(body, right));
                    }
                    else if let Value::Quote(a) = *matched_left_value
                        && let Value::Quote(b) = *matched_right_value
                    {
                        pending.push(VT(a, b));
                    }
                    else if let Value::QuoteComputation(a) = *matched_left_value
                        && let Value::QuoteComputation(b) = *matched_right_value
                    {
                        {
                            pending.push(CT(a, b));
                        }
                    }
                    else if let Value::Mark {
                        mark: left_mark,
                        body: left_body,
                    } = *matched_left_value
                        && let Value::Mark {
                            mark: right_mark,
                            body: right_body,
                        } = *matched_right_value
                        && (left_mark == right_mark)
                    {
                        pending.push(V(left_body, right_body));
                    }
                    else if (matches!(
                        *matched_left_value,
                        Value::Variable { .. }
                            | Value::Constant(_)
                            | Value::Literal(_)
                            | Value::Hole(_)
                    ) && (a == b))
                    {
                        {}
                    }
                    else {
                        return CertificateEquality::Different;
                    }
                }
            },
            | C(a, b) => {
                let (Some(a), Some(b)) = (arena.computation(a), arena.computation(b))
                else {
                    return CertificateEquality::Different;
                };
                match (a, b) {
                    | (
                        &Computation::DataCase {
                            scrutinee: a,
                            motive: am,
                            branches: ref ab,
                        },
                        &Computation::DataCase {
                            scrutinee: b,
                            motive: bm,
                            branches: ref bb,
                        },
                    ) if ab.len() == bb.len() => {
                        pending.extend([V(a, b), CT(am, bm)]);
                        pending.extend(ab.iter().zip(bb).map(|(a, b)| C(*a, *b)));
                    },
                    | (
                        &Computation::RecordProjection(a, ref al),
                        &Computation::RecordProjection(b, ref bl),
                    ) if al == bl => pending.push(V(a, b)),
                    | (
                        &Computation::TupleProjection(a, ac),
                        &Computation::TupleProjection(b, bc),
                    ) if ac == bc => pending.push(V(a, b)),
                    | (
                        &Computation::Perform {
                            signature: ref left,
                            operation: ref left_op,
                            payload: left_payload,
                        },
                        &Computation::Perform {
                            signature: ref right,
                            operation: ref right_op,
                            payload: right_payload,
                        },
                    ) if left_op == right_op => {
                        if signature_children(&mut pending, left, right)
                            == CertificateEquality::Different
                        {
                            return CertificateEquality::Different;
                        }
                        pending.push(V(left_payload, right_payload));
                    },
                    | (
                        &Computation::Handle {
                            signature: ref left,
                            subject: left_subject,
                            on_return: left_return,
                            clauses: ref left_clauses,
                        },
                        &Computation::Handle {
                            signature: ref right,
                            subject: right_subject,
                            on_return: right_return,
                            clauses: ref right_clauses,
                        },
                    ) if left_clauses.len() == right_clauses.len() => {
                        if signature_children(&mut pending, left, right)
                            == CertificateEquality::Different
                        {
                            return CertificateEquality::Different;
                        }
                        pending
                            .extend([C(left_subject, right_subject), C(left_return, right_return)]);
                        for (left, right) in left_clauses.iter().zip(right_clauses.iter()) {
                            if left.operation != right.operation {
                                return CertificateEquality::Different;
                            }
                            pending.push(C(left.body, right.body));
                        }
                    },
                    | (&Computation::Resume(a, b), &Computation::Resume(c, d)) => {
                        pending.extend([V(a, c), C(b, d)]);
                    },
                    | (
                        &Computation::Split {
                            scrutinee: a,
                            arity: left_arity,
                            body: b,
                        },
                        &Computation::Split {
                            scrutinee: c,
                            arity: right_arity,
                            body: d,
                        },
                    ) if left_arity == right_arity => pending.extend([V(a, c), C(b, d)]),
                    | (&Computation::Reset(a), &Computation::Reset(b))
                    | (&Computation::Shift(a), &Computation::Shift(b))
                    | (&Computation::Lambda(a), &Computation::Lambda(b)) => pending.push(C(a, b)),
                    | (&Computation::With(a, b), &Computation::With(c, d))
                    | (&Computation::Bind(a, b), &Computation::Bind(c, d)) => {
                        pending.extend([C(a, c), C(b, d)]);
                    },
                    | (&Computation::Project(a, b), &Computation::Project(c, d)) if a == c => {
                        pending.push(C(b, d));
                    },
                    | (
                        &Computation::ListFold {
                            element: left_element,
                            result: left_result,
                            list: left_list,
                            on_nil: left_nil,
                            on_cons: left_cons,
                        },
                        &Computation::ListFold {
                            element: right_element,
                            result: right_result,
                            list: right_list,
                            on_nil: right_nil,
                            on_cons: right_cons,
                        },
                    ) => pending.extend([
                        VT(left_element, right_element),
                        VT(left_result, right_result),
                        V(left_list, right_list),
                        C(left_nil, right_nil),
                        C(left_cons, right_cons),
                    ]),
                    | (
                        &Computation::PathTransport {
                            motive: left_motive,
                            path: left_path,
                            value: left_value,
                        },
                        &Computation::PathTransport {
                            motive: right_motive,
                            path: right_path,
                            value: right_value,
                        },
                    ) => pending.extend([
                        VT(left_motive, right_motive),
                        V(left_path, right_path),
                        V(left_value, right_value),
                    ]),
                    | (
                        &Computation::TelescopeTransport {
                            motive: left_motive,
                            path: left_path,
                            start: left_start,
                            over: left_over,
                            value: left_value,
                        },
                        &Computation::TelescopeTransport {
                            motive: right_motive,
                            path: right_path,
                            start: right_start,
                            over: right_over,
                            value: right_value,
                        },
                    ) => pending.extend([
                        CT(left_motive, right_motive),
                        V(left_path, right_path),
                        V(left_start, right_start),
                        V(left_over, right_over),
                        V(left_value, right_value),
                    ]),
                    | (
                        &Computation::Primitive {
                            primitive: a,
                            arguments: ref aa,
                        },
                        &Computation::Primitive {
                            primitive: b,
                            arguments: ref right_arguments,
                        },
                    ) if a == b && aa.len() == right_arguments.len() => pending.extend(
                        aa.iter()
                            .zip(right_arguments.iter())
                            .map(|(a, b)| V(*a, *b)),
                    ),
                    | (
                        &Computation::Fixpoint {
                            body: a,
                            evidence: left_evidence,
                        },
                        &Computation::Fixpoint {
                            body: b,
                            evidence: right_evidence,
                        },
                    ) if left_evidence == right_evidence => pending.push(C(a, b)),
                    | (&Computation::Return(a), &Computation::Return(b))
                    | (&Computation::Force(a), &Computation::Force(b)) => pending.push(V(a, b)),
                    | (&Computation::Application(a, b), &Computation::Application(c, d)) => {
                        pending.extend([C(a, c), V(b, d)]);
                    },
                    | (&Computation::Transport(a, b), &Computation::Transport(c, d)) => {
                        pending.extend([V(a, c), V(b, d)]);
                    },
                    | (
                        &Computation::Case {
                            scrutinee: left_scrutinee,
                            branches: ref left_branches,
                        },
                        &Computation::Case {
                            scrutinee: right_scrutinee,
                            branches: ref right_branches,
                        },
                    ) if left_branches.len() == right_branches.len() => {
                        pending.push(V(left_scrutinee, right_scrutinee));
                        pending.extend(
                            left_branches
                                .iter()
                                .zip(right_branches.iter())
                                .map(|(a, b)| C(*a, *b)),
                        );
                    },
                    | (&Computation::Hole(left), &Computation::Hole(right)) if left == right => {},
                    | (
                        &Computation::Mark {
                            mark: left_mark,
                            body: left_body,
                        },
                        &Computation::Mark {
                            mark: right_mark,
                            body: right_body,
                        },
                    ) if left_mark == right_mark => pending.push(C(left_body, right_body)),
                    | _ => return CertificateEquality::Different,
                }
            },
            | VT(a, b) => {
                let (Some(a), Some(b)) = (arena.value_type(a), arena.value_type(b))
                else {
                    return CertificateEquality::Different;
                };
                {
                    let (matched_left_value, matched_right_value) = (a, b);
                    if let ValueType::Data {
                        declaration: a,
                        arguments: ref aa,
                    } = *matched_left_value
                        && let ValueType::Data {
                            declaration: b,
                            arguments: ref right_arguments,
                        } = *matched_right_value
                        && (a == b && aa.len() == right_arguments.len())
                    {
                        {
                            pending.extend(aa.iter().zip(right_arguments).map(|(a, b)| V(*a, *b)));
                        }
                    }
                    else if let ValueType::Record(ref a) = *matched_left_value
                        && let ValueType::Record(ref b) = *matched_right_value
                        && (a.len() == b.len() && a.keys().eq(b.keys()))
                    {
                        {
                            pending.extend(a.values().zip(b.values()).map(|(a, b)| VT(*a, *b)));
                        }
                    }
                    else if let (
                        &ValueType::Stack {
                            input: a,
                            output: b,
                        },
                        &ValueType::Stack {
                            input: c,
                            output: d,
                        },
                    ) = (matched_left_value, matched_right_value)
                    {
                        pending.extend([CT(a, c), CT(b, d)]);
                    }
                    else if let (
                        &ValueType::Path {
                            carrier: a,
                            left: b,
                            right: c,
                        },
                        &ValueType::Path {
                            carrier: d,
                            left: e,
                            right: f,
                        },
                    ) = (matched_left_value, matched_right_value)
                    {
                        pending.extend([VT(a, d), V(b, e), V(c, f)]);
                    }
                    else if let (&ValueType::List(a), &ValueType::List(b)) =
                        (matched_left_value, matched_right_value)
                    {
                        pending.push(VT(a, b));
                    }
                    else if let ValueType::PathUniverse(a, b) = *matched_left_value
                        && let ValueType::PathUniverse(c, d) = *matched_right_value
                    {
                        {
                            pending.extend([V(a, c), V(b, d)]);
                        }
                    }
                    else if let ValueType::Product(ref a) = *matched_left_value
                        && let ValueType::Product(ref b) = *matched_right_value
                        && a.len() == b.len()
                    {
                        pending.extend(a.iter().zip(b.iter()).map(|(a, b)| VT(*a, *b)));
                    }
                    else if let ValueType::Sum(ref a) = *matched_left_value
                        && let ValueType::Sum(ref b) = *matched_right_value
                        && a.len() == b.len()
                    {
                        pending.extend(a.iter().zip(b.iter()).map(|(a, b)| VT(*a, *b)));
                    }
                    else if let ValueType::StaticPi {
                        domain: a,
                        codomain: b,
                    } = *matched_left_value
                        && let ValueType::StaticPi {
                            domain: c,
                            codomain: d,
                        } = *matched_right_value
                    {
                        pending.extend([VT(a, c), VT(b, d)]);
                    }
                    else if let ValueType::Thunk(a) = *matched_left_value
                        && let ValueType::Thunk(b) = *matched_right_value
                    {
                        pending.push(CT(a, b));
                    }
                    else if let ValueType::Lift {
                        inner: a,
                        ref target,
                    } = *matched_left_value
                        && let ValueType::Lift {
                            inner: b,
                            target: ref other,
                        } = *matched_right_value
                        && (target == other)
                    {
                        pending.push(VT(a, b));
                    }
                    else if let ValueType::Element {
                        code: a,
                        ref target,
                    } = *matched_left_value
                        && let ValueType::Element {
                            code: b,
                            target: ref other,
                        } = *matched_right_value
                        && (target == other)
                    {
                        pending.push(V(a, b));
                    }
                    else if (matches!(
                        *matched_left_value,
                        ValueType::Base(_)
                            | ValueType::Universe { .. }
                            | ValueType::Abstract(_)
                            | ValueType::Unknown
                    ) && (a == b))
                    {
                        {}
                    }
                    else {
                        return CertificateEquality::Different;
                    }
                }
            },
            | CT(a, b) => {
                let (Some(a), Some(b)) = (arena.comp_type(a), arena.comp_type(b))
                else {
                    return CertificateEquality::Different;
                };
                match (a, b) {
                    | (&CompType::With(a, b), &CompType::With(c, d)) => {
                        pending.extend([CT(a, c), CT(b, d)]);
                    },
                    | (
                        &CompType::Returner {
                            result: a,
                            effects: ref first,
                        },
                        &CompType::Returner {
                            result: b,
                            effects: ref second,
                        },
                    ) => {
                        if first.signatures().len() != second.signatures().len() {
                            return CertificateEquality::Different;
                        }
                        for (left, right) in first.signatures().zip(second.signatures()) {
                            if signature_children(&mut pending, left, right)
                                == CertificateEquality::Different
                            {
                                return CertificateEquality::Different;
                            }
                        }
                        pending.push(VT(a, b));
                    },
                    | (
                        &CompType::Arrow {
                            domain: a,
                            codomain: b,
                        },
                        &CompType::Arrow {
                            domain: c,
                            codomain: d,
                        },
                    )
                    | (
                        &CompType::Pi {
                            domain: a,
                            codomain: b,
                        },
                        &CompType::Pi {
                            domain: c,
                            codomain: d,
                        },
                    ) => pending.extend([VT(a, c), CT(b, d)]),
                    | (
                        &CompType::Element {
                            code: a,
                            ref target,
                        },
                        &CompType::Element {
                            code: b,
                            target: ref other,
                        },
                    ) if target == other => pending.push(V(a, b)),
                    | (&CompType::Unknown, &CompType::Unknown) => {},
                    | _ => return CertificateEquality::Different,
                }
            },
        }
    }
    CertificateEquality::Equal
}

#[cfg(test)]
mod tests
{
    use super::*;

    #[test]
    fn the_unit_is_the_empty_product()
    {
        let mut arena = crate::CoreArena::new();
        let unit = arena.value_type_unit();
        let first = arena.value_type_unit();
        let pair = arena.value_type_product(&[unit, first]);
        assert_eq!(
            arena.value_type(unit),
            Some(&ValueType::unit()),
            "the minted unit is the empty product"
        );
        assert_ne!(
            arena.value_type(pair),
            Some(&ValueType::unit()),
            "a product of two components is not the unit"
        );
        assert_eq!(
            equal_type_syntax(&arena, unit, first),
            CertificateEquality::Equal,
            "two units are one type"
        );
        assert_eq!(
            equal_type_syntax(&arena, unit, pair),
            CertificateEquality::Different,
            "and no arity but zero is the unit"
        );
    }

    #[test]
    fn the_unit_is_the_empty_tuple()
    {
        let mut arena = crate::CoreArena::new();
        let unit = arena.value_unit();
        let other = arena.value_tuple(&[]);
        let pair = arena.value_tuple(&[unit, other]);
        let injected = arena.value_injection(Summand::from(0_usize), unit);
        assert_eq!(
            arena.value(unit),
            Some(&Value::unit()),
            "the minted unit is the empty tuple"
        );
        assert_eq!(
            arena.value(pair).and_then(Value::components),
            Some([unit, other].as_slice()),
            "a tuple reads back its components in order"
        );
        assert_eq!(
            arena.value(unit).and_then(Value::components),
            Some([].as_slice())
        );
        assert_eq!(
            arena.value(injected).and_then(Value::components),
            None,
            "an injection has no components"
        );
        assert_eq!(
            equal_certificate_syntax(&arena, unit, other),
            CertificateEquality::Equal,
            "two units are one value"
        );
        assert_eq!(
            equal_certificate_syntax(&arena, unit, pair),
            CertificateEquality::Different,
            "and no arity but zero is the unit"
        );
    }

    #[test]
    fn certificate_syntax_erases_only_evidence()
    {
        let mut arena = crate::CoreArena::new();
        let unit = arena.value_type_unit();
        let code = arena.value_quote(unit);
        let classifier = arena.value_type_path_universe(code, code);
        let variable = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let returned = arena.computation_return(variable);
        let lambda = arena.computation_lambda(returned);
        let identity = arena.value_thunk(lambda);
        let first =
            arena.value_path_equiv(classifier, identity, identity, alloc::sync::Arc::default());
        let mut evidence = gandr_kernel_term::PathEvidence::default();
        evidence.source.push(alloc::vec::Vec::new());
        let evidence = alloc::sync::Arc::new(evidence);
        let same = arena.value_path_equiv(
            classifier,
            identity,
            identity,
            alloc::sync::Arc::clone(&evidence),
        );
        assert_eq!(
            CertificateEquality::Equal,
            equal_certificate_syntax(&arena, first, same)
        );
        let extra = arena.computation_bind(returned, returned);
        let extra = arena.computation_lambda(extra);
        let extra = arena.value_thunk(extra);
        let different = arena.value_path_equiv(classifier, extra, identity, evidence);
        assert_eq!(
            CertificateEquality::Different,
            equal_certificate_syntax(&arena, first, different)
        );
        let fresh = arena.value_type_unit();
        let fresh = arena.value_quote(fresh);
        let one = arena.value_path_refl(code);
        let two = arena.value_path_refl(fresh);
        assert_eq!(
            CertificateEquality::Equal,
            equal_certificate_syntax(&arena, one, two)
        );
    }
}

/// A nominal declaration's parameter telescope, constructor table and universe.
///
/// Parameter classifiers are scoped under their predecessors. Constructor
/// fields are scoped under all parameters and do not bind one another.
/// Admission, not this container, verifies those scopes and the universe bound.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct DataSignature
{
    /// Parameter classifiers in telescope order.
    parameters: Vec<ValueTypeId>,
    /// Constructor fields in tag order.
    constructors: Vec<Vec<ValueTypeId>>,
    /// The positive universe bounding every constructor field.
    kind: ValueTypeId,
}

impl DataSignature
{
    /// Construct a signature whose formation remains the checker's obligation.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub const fn new(
        parameters: Vec<ValueTypeId>,
        constructors: Vec<Vec<ValueTypeId>>,
        kind: ValueTypeId,
    ) -> Self
    {
        Self {
            parameters,
            constructors,
            kind,
        }
    }

    /// Parameter classifiers in telescope order.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub fn parameters(&self) -> &[ValueTypeId]
    {
        &self.parameters
    }

    /// Constructor field classifiers in tag order.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub fn constructors(&self) -> &[Vec<ValueTypeId>]
    {
        &self.constructors
    }

    /// The positive universe bounding constructor fields.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub const fn kind(&self) -> ValueTypeId
    {
        self.kind
    }
}
