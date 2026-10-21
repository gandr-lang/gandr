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
//! Project frames select a component of a lazy product. `With([C₀, …, Cₙ₋₁])`
//! classifies a lazy computation tuple, distinct from an eager value product;
//! the empty one is the terminal computation type.
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
//! `control::tests::lazy_tuples_keep_their_components_and_projection_position`,
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
//! `gandr-core-checker`.
//!
//! A field may name its own declaration's family: the syntax is an ordinary
//! `ValueType::Data` at the declaration's own position, and whether that
//! occurrence is admissible is the checker's question, not the arena's.
//! `Computation::Fixpoint { body, evidence }` is `fix x. M`: its body stands
//! under one intuitionistic binder, the self thunk, so binder rewrites, shifts
//! and substitutions treat it as they treat a lambda. `FixpointEvidence` is the
//! kernel's own — `Partial`, `StructuralDescent` (its first parameter staged)
//! or `Staged { position }` — and the arena records the claim and grants
//! nothing; syntax equality distinguishes the claims. `ValueType::Staged` is
//! the type a checker's recursion core gives a staged parameter or field; two
//! such types are syntactically equal at one stage over equal bases.
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
//! `Computation::Split { scrutinee, arity, motive, body }` eliminates a product
//! or a dependent pair by binding every component at once: the body stands
//! under one intuitionistic binder per component, component zero outermost and
//! the last innermost, so a split of `n` components reads its last at index
//! zero. The arity is stated rather than read off the scrutinee's type, so that
//! a split of no components is well scoped on its own and types its scrutinee
//! as the unit: it discards a unit value without a projection to name. Syntax
//! equality compares the arity and the motive before the children, and
//! `Binders::deeper_by` moves a walk under the body's binders.
//!
//! The [`SplitMotive`] says what the body is checked against.
//! `SplitMotive::Ambient` is the type the split is checked against, shifted
//! past the components, so the split only checks and eliminates a product.
//! `SplitMotive::Scrutinee(C)` is a computation type under one binder of the
//! scrutinee, as a nominal case's motive is: the split synthesises `C` at the
//! scrutinee, and the body checks against `C` at the tuple of the components it
//! binds, so the body's type may read them.
//!
//! **Choice.** A split with an explicit arity and a motive that is either the
//! ambient type or one under the scrutinee binder, beside the positional
//! projection. **Alternatives.** Projection alone, which cannot type the
//! discard of a unit, there being no component to project; a split reading its
//! arity from the scrutinee's type, which leaves the empty split's scope
//! undetermined before checking; a second former for the dependent split,
//! whose body has the same scope as the ambient split's and whose motive is a
//! child the ambient split lacks, not a child read differently. **Reversal.**
//! A split whose motive binds more than the scrutinee — an index of the
//! scrutinee's type — gains a former of its own.
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
//! # The dependent pair
//!
//! `ValueType::Sigma { first, second }` is `Σ (x : A). B`, the second factor
//! under one intuitionistic binder of the first. It is a positive value type at
//! the join of its factors' levels. Its pair is the [`Value::Tuple`] of two
//! components, checked against it: the first against `A`, the second against
//! `B` at the first. A tuple that synthesises has its eager product, so a
//! dependent pair is reached only by checking. It is eliminated by a split
//! with a scrutinee motive and observed by the positional projection: `p.0`
//! returns `A`, and `p.1` returns `B` at the value `p.0` returns, which
//! [`Value::Returned`] spells in the type.
//!
//! **Choice.** `Product` stays its own n-ary former, and `Sigma` is binary and
//! written only where the second factor reads its binder, as a dependent arrow
//! is written only where its codomain reads its binder; a dependent record of
//! more entries nests to the right. The two do not convert with each other,
//! and neither has an η law: the eager product has none, and the dependent pair
//! follows it. **Alternatives.** The product read as a dependent pair with a
//! vacuous binder, which puts a binder into every walk over every first-order
//! code and loses the n-ary reading; a native dependent record former keyed by
//! labels, which the core would have to compare up to label order with
//! dependencies between fields; a package-style existential, which hides the
//! first component and so cannot state a law about it. **Reversal.** A
//! conversion that identifies a dependent pair ignoring its binder with the
//! binary product makes the two spellings one; a labelled consumer the
//! positional pair cannot serve gains the labelled former.
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
//! fragment and the kernel replays candidates. Element-identity, higher-field
//! and bridge-mode programs remain separate kernel APIs; the directed family's
//! statements are core values the checker decides and the bridge erases.
//! **Reversal.**
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
use gandr_kernel_term::Summand;
use quenchant_shape::shape::Maybe;

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
    /// Univalence `ua(e)`, written `Univalence(e, f)`: an element of
    /// `Path(U, a, b)` for a bi-invertible map `e : A ≃ B`, `a` and `b` the
    /// codes of `A` and `B`, at any two codes of the level-zero value universe.
    /// The record's laws are its evidence; the kernel checks them as the
    /// record's fields and decides nothing. `f` is the record's forward map
    /// `thunk (λx. e.0 x)`, derived by the lowering from `e` so that transport
    /// along the path applies it; the bridge drops it and the kernel derives
    /// the same map from the record.
    Univalence(ValueId, ValueId),
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
    /// A session identity statement between two session codes: `bisim(a, b)`,
    /// an element of `Path(Type, a, b)` when the protocols are bisimilar, or
    /// `sim(a, b)`, an element of `Flow(Type, a, b)` when `a` is a Gay–Hole
    /// subtype of `b`. The checker decides it with the session engine and
    /// records the relation, and the kernel replays that relation as a native
    /// session path or session flow; it is inert, as a native certificate is.
    SessionRelated
    {
        /// The identity claimed.
        relation: crate::session::SessionRelation,
        /// The source code.
        source: ValueId,
        /// The target code.
        target: ValueId,
    },
    /// Directed reflexivity `stay(a)`: the canonical element of `Flow(A, a,
    /// a)`.
    Stay(ValueId),
    /// Directed composition `then(f, g)`: given `f : Flow(A, a, b)` and `g :
    /// Flow(A, b, c)`, an element of `Flow(A, a, c)`.
    Then(ValueId, ValueId),
    /// The componentwise product `flowProduct(p, q)` of two universe flows:
    /// from `p : Flow(Type, a, a')` and `q : Flow(Type, b, b')` an element of
    /// `Flow(Type, #{a, b}, #{a', b'})`, the directed twin of
    /// [`Self::PathProduct`].
    FlowProduct(ValueId, ValueId),
    /// A forward flow `forward(f)`: an element of `Flow(Type, a, b)` for a
    /// closed translator `f : U (A → F B)` between first-order codes, `a` and
    /// `b` the quotes of `A` and `B`, whose output at every pattern of `A`'s
    /// coverage is leaf-natural. No inverse is asked. The checker decides it by
    /// computation and the kernel replays it as its forward certificate; it is
    /// inert, as a native certificate is.
    Forward(ValueId),
    /// The arrow's action on two boundary flows, `arrow(d, c)`: an element of
    /// `Flow(Type, ⌜U (A → F B)⌝, ⌜U (A' → F B')⌝)` from a domain flow `d :
    /// Flow(Type, A', A)`, which runs against the arrow, and a codomain flow
    /// `c : Flow(Type, B, B')`, which runs with it. The kernel replays it as
    /// its function certificate; it is inert, as a native certificate is.
    FunctionFlow(ValueId, ValueId),
    /// A recorded run `recorded(m₁, …, mₙ)`: one endpoint's complete trace,
    /// each payload a value. It checks against `Run(s)` by replay of its
    /// moves through the session monitor and of its payloads at the types
    /// the protocol assigns them.
    Recorded(alloc::sync::Arc<[crate::session::RecordedMove]>),
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
    #[spec(ensures: |ret| match *self { Self::Tuple(ref components) => ret == Some(&**components), Self::Primitive { .. } | Self::PathRefl(_) | Self::PathProduct(..) | Self::PathEquiv { .. } | Self::Here(_) | Self::Univalence(..) | Self::Funext(..) | Self::Equiv(..) | Self::Ua { .. } | Self::SessionRelated { .. } | Self::Stay(_) | Self::Then(..) | Self::FlowProduct(..) | Self::Forward(_) | Self::FunctionFlow(..) | Self::Recorded(_) | Self::Returned(_) | Self::Nested(_) | Self::Run(_) | Self::Variable { .. } | Self::Constant(_) | Self::Literal(_) | Self::Injection(..) | Self::ListNil | Self::ListCons(..) | Self::Thunk(_) | Self::Lift { .. } | Self::Quote(_) | Self::QuoteComputation(_) | Self::StaticLambda(_) | Self::StaticApplication(..) | Self::Constructor { .. } | Self::Record(_) | Self::Hole(_) | Self::Mark { .. } | Self::Reify(_) => ret.is_none() })]
    #[inline]
    #[must_use]
    pub fn components(&self) -> Option<&[ValueId]>
    {
        match *self {
            Self::Tuple(ref components) => Some(components),
            Self::Primitive { .. }
            | Self::PathRefl(_)
            | Self::PathProduct(..)
            | Self::PathEquiv { .. }
            | Self::Here(_)
            | Self::Univalence(..)
            | Self::Funext(..)
            | Self::Equiv(..)
            | Self::Ua { .. }
            | Self::SessionRelated { .. }
            | Self::Stay(_)
            | Self::Then(..)
            | Self::FlowProduct(..)
            | Self::Forward(_)
            | Self::FunctionFlow(..)
            | Self::Recorded(_)
            | Self::Returned(_)
            | Self::Nested(_)
            | Self::Run(_)
            | Self::Variable { .. }
            | Self::Constant(_)
            | Self::Literal(_)
            | Self::Injection(..)
            | Self::ListNil
            | Self::ListCons(..)
            | Self::Thunk(_)
            | Self::Lift { .. }
            | Self::Quote(_)
            | Self::QuoteComputation(_)
            | Self::StaticLambda(_)
            | Self::StaticApplication(..)
            | Self::Constructor { .. }
            | Self::Record(_)
            | Self::Hole(_)
            | Self::Mark { .. }
            | Self::Reify(_) => None,
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

/// What a split's body is checked against.
///
/// The motive is a payload beside the split's children rather than a second
/// former: the body stands under one binder per component either way, so no
/// child changes its scope with the motive.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum SplitMotive
{
    /// The type the split is checked against, shifted past the components:
    /// the body's type reads no component, and the split only checks.
    Ambient,
    /// A computation type under one intuitionistic binder of the scrutinee:
    /// the split synthesises it at the scrutinee, and the body checks against
    /// it at the tuple of the components the body binds.
    Scrutinee(CompTypeId),
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
    /// Directed transport `ride(P, f, x)` along a flow: given `f : Flow(A, a,
    /// b)` and `x : P[a]`, it returns `P[b]`. The motive `P` is a value type
    /// under one intuitionistic binder of the carrier `A`, in which the
    /// binder occurs only covariantly.
    Ride
    {
        /// The motive, under one intuitionistic binder: the moving endpoint.
        motive: ValueTypeId,
        /// The flow ridden along.
        flow: ValueId,
        /// The value moved, an inhabitant of the motive at the flow's source.
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
    /// An ascription `(M : C)`: the computation `M` checked against the
    /// stated type `C`, which the ascription synthesises. It is the
    /// bidirectional switch, standing a checking form where a type is
    /// synthesised; it runs as `M` runs, and the kernel replays it at a
    /// typed position of its own rather than trusting it.
    ///
    /// The surface writes one as the typed bind `run x : A <- c ;`, which
    /// ascribes `c` the pure `-F A`: the annotation writes no row, so an
    /// effectful `c` is refused there. Alternatives: ascribing the returned
    /// value instead, `x ← c ; (return x : F A)`, which keeps `c`'s row but
    /// leaves a `c` that only checks, a return or a case, unsynthesisable;
    /// and a value-type ascription at the row the bind's continuation
    /// allows, which synthesis does not carry. Reversal: once synthesis
    /// carries the row a continuation allows, the typed bind ascribes that
    /// row and an effectful `c` checks.
    Ascribe
    {
        /// The computation ascribed.
        body: ComputationId,
        /// The type it is checked against, in the ambient context.
        ty: CompTypeId,
    },
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
    /// A product or dependent-pair elimination, binding every component of
    /// the scrutinee into the body: component zero outermost, the last
    /// innermost. The arity is the scrutinee's own, stated so that a split of
    /// no components types its scrutinee as the unit.
    Split
    {
        /// The scrutinee value, of a product or a dependent-pair type.
        scrutinee: ValueId,
        /// How many components the scrutinee has, each bound in the body.
        arity: ComponentCount,
        /// What the body is checked against.
        motive: SplitMotive,
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
    /// A case on a native list: the cell branch binds the head then the tail.
    /// Each branch is an ordinary computation, so a walk through a list may
    /// stop at any cell. The list's type is read off the list itself, as a
    /// sum case reads its scrutinee's.
    ListCase
    {
        /// Native list to inspect.
        list: ValueId,
        /// Empty branch in the ambient context.
        on_nil: ComputationId,
        /// Cell branch beneath two intuitionistic binders: the head at index
        /// one, the tail at index zero.
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
    /// Exercise an operation through a capability, `c.op v`: the operation's
    /// interface rides inline, as a request's does, and the capability names
    /// the authority the request is made under.
    Exercise
    {
        /// The capability the operation is exercised through.
        capability: ValueId,
        /// The full interface the operation belongs to.
        signature: crate::effect::EffectSig,
        /// The selected operation.
        operation: crate::effect::OperationName,
        /// Its value payload.
        payload: ValueId,
    },
    /// Handle one interface deeply over a body that receives the capability
    /// the handler introduces, `handle (c. t) with h`: the subject stands
    /// under one intuitionistic binder, the capability, and the clauses run
    /// outside it.
    Scope
    {
        /// The interface whose operations are handled, and the authority of
        /// the capability the subject receives.
        signature: crate::effect::EffectSig,
        /// The computation being handled, beneath the capability's binder.
        subject: ComputationId,
        /// Return clause beneath one intuitionistic result binder.
        on_return: ComputationId,
        /// Operation clauses beneath payload then resumption binders.
        clauses: alloc::sync::Arc<[crate::control::EffectClause]>,
    },
    /// Feed a computation to a first-class stack.
    Resume(ValueId, ComputationId),
    /// End a first-class stack without resuming it, `abandon(k)`: the rest of
    /// the computation the stack captured never runs, and the form returns
    /// unit.
    Abandon(ValueId),
    /// Delimit a continuation capture.
    Reset(ComputationId),
    /// Capture to the nearest reset, binding one intuitionistic stack value.
    Shift(ComputationId),
    /// A lazy negative tuple; only the observed component executes.
    With(alloc::boxed::Box<[ComputationId]>),
    /// Observe the component of a negative product at a position.
    Project(Component, ComputationId),
    /// A session action: send, receive, select, offer or close on a linear
    /// endpoint, or fork a new pair of endpoints.
    Session(crate::session::SessionAction),
    /// A memory form: hold a value exclusively, access it through a view,
    /// or end a view by resuming or aborting it.
    Memory(crate::memory::MemoryForm),
    /// A world form: hold a value at the current world, open a handle at its
    /// world, or migrate to another world.
    World(crate::world::WorldForm),
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
    /// Directed identity `Flow(A, a, b)`: the type of forward-only flows from
    /// `a` to `b` in the value type `A`. It has no inverse: a flow transports
    /// along itself in one direction only.
    Flow
    {
        /// The carrier the two endpoints inhabit.
        carrier: ValueTypeId,
        /// The source endpoint.
        source: ValueId,
        /// The target endpoint.
        target: ValueId,
    },
    /// `Run(s)`: the complete recorded runs of the session code `s`, each a
    /// finite trace the protocol's monitor accepts.
    Run(ValueId),
    /// A rigid base-type atom.
    Base(BaseType),
    /// The product of its components, in order: `Product([])` is the unit
    /// type, inhabited by the empty [`Value::Tuple`] alone, and
    /// `Product([A, B])` the pair type `A × B`.
    Product(alloc::boxed::Box<[ValueTypeId]>),
    /// The dependent pair `Σ (x : A). B`: a pair whose second component's
    /// type reads the first. Its introduction is the [`Value::Tuple`] of two
    /// components, checked only; its elimination a [`Computation::Split`]
    /// with a [`SplitMotive::Scrutinee`] motive, or a
    /// [`Computation::TupleProjection`].
    ///
    /// The scoping is the whole difference from a product of two components,
    /// which is why the two are distinct nodes: the same two children, the
    /// second under a binder here and in the ambient context there.
    Sigma
    {
        /// The first factor `A`, in the ambient context.
        first: ValueTypeId,
        /// The second factor `B`, under one intuitionistic binder of `A`.
        second: ValueTypeId,
    },
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
    /// `A^s`: the values of `base` at the stage `s` of a recursion, which only
    /// the checker mints — at a fixpoint's staged parameter, its
    /// self-reference's domain and the recursive fields of a case on a staged
    /// value. A stage refines the type's values and never its identity: `A^s`
    /// is used where `A` is wanted, and every other comparison takes it for
    /// itself. The base is never itself staged.
    Staged
    {
        /// The type the stage refines.
        base: ValueTypeId,
        /// The stage.
        stage: gandr_kernel_term::Stage,
    },
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
    /// The type of a linear endpoint: a protocol, its payload types and the
    /// state the endpoint stands at.
    Session(crate::session::SessionType),
    /// The capability `Cap E`: the type of a context hypothesis carrying the
    /// authority `E`. No term introduces it; a hypothesis the host holds or a
    /// capability scope's binder is the only inhabitant.
    Capability
    {
        /// The grant atoms: each interface restricted to the operations it
        /// grants.
        authority: crate::effect::EffectRow,
        /// How often the capability may be exercised.
        grade: crate::effect::capability::CapabilityGrade,
        /// How long it lives.
        region: crate::effect::capability::Region,
    },
    /// The buffer token `Buf`: an id into a registered area that a completion
    /// delivers and the program must return, exactly once. No term
    /// introduces it: a receive's binder holds one, and so does the reply of
    /// an operation the scope handling it mints the buffer for, each placed
    /// live in the linear zone; it leaves that zone only by being handed on
    /// whole, through a send, an operation's payload or a resumption.
    Buffer,
    /// A value kept in a region: `A at c`, a value of `A` that may capture a
    /// shared view lent while the capability scope at `region` lives, and so
    /// lives as long as that scope rather than the access.
    Kept
    {
        /// The kept value's type.
        value: ValueTypeId,
        /// The capability scope it lives in.
        region: crate::effect::capability::RegionDepth,
    },
    /// A type that names a world: `A at w`, a handle to a value meaningful
    /// at `w`, or `cap_w`, the one-shot authority to migrate to `w`.
    World(crate::world::WorldType),
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
    /// A lazy negative product; an observation selects one component. The
    /// empty one is the terminal computation type.
    With(alloc::boxed::Box<[CompTypeId]>),
    /// A nominal codata type `νX. &{dᵢ : Bᵢ}` applied to its declaration's
    /// parameter telescope.
    ///
    /// It is read as the lazy product of its observations, each instantiated
    /// at `arguments`, only where a computation is introduced against it or
    /// one of its observations is taken; two codata types are equal exactly
    /// when they name one declaration at equal arguments, and none is equal
    /// to the product of its observations.
    Codata
    {
        /// Admission position of the codata signature.
        declaration: ConstantIndex,
        /// Quoted type or ordinary value arguments, in telescope order.
        arguments: Vec<ValueId>,
    },
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

/// Which identifications [`equal_syntax`] makes beside the syntax.
#[derive(Clone, Copy)]
enum Reading<'signatures>
{
    /// As the certificate holds it: two types agree only where their syntax
    /// does, and a stage is part of its type.
    Syntax,
    /// As a printed type reads back: the words of the signatures' presented
    /// types as the path at their point, two session types by their protocols'
    /// behaviour, a decoded static redex as its reduct, as every checker reads
    /// them, a staged type as its base, which is all of it the surface
    /// writes, a call kept unelaborated as the value it returns, which is
    /// all a printed `f(x)` says, a call of a function literal as the
    /// value its body returns, which no surface call spells, and a forced
    /// returned value as the computation returning it, which a printed call
    /// on a selection writes alike.
    Printed(&'signatures BTreeMap<ConstantIndex, alloc::sync::Arc<DataSignature>>),
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
    equal_syntax(arena, Reading::Syntax, StructuralGoal::Value(left, right))
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
    equal_syntax(
        arena,
        Reading::Syntax,
        StructuralGoal::ValueType(left, right),
    )
}

/// Compare computation type syntax as [`equal_type_syntax`] compares value
/// types.
///
/// # Specification
/// - ensures: equal roots have the same former and structurally equal children.
/// - fails: unreadable roots or children compare different.
///
/// # Adequacy
/// - hypothesis: L3 — two separately allocated codata types over one argument
///   compare equal; a different argument compares different.
/// - witness: `syntax::tests::computation_type_syntax_ignores_allocation_identity`
#[spec(ensures: |ret| ret != CertificateEquality::Equal || match (arena.comp_type(left), arena.comp_type(right)) {
    (Some(left), Some(right)) => core::mem::discriminant(left) == core::mem::discriminant(right),
    _ => false,
})]
#[inline]
#[must_use]
pub fn equal_comp_type_syntax(
    arena: &crate::CoreArena,
    left: CompTypeId,
    right: CompTypeId,
) -> CertificateEquality
{
    equal_syntax(
        arena,
        Reading::Syntax,
        StructuralGoal::CompType(left, right),
    )
}

/// Compare type syntax as [`equal_type_syntax`] does, as a printed type reads.
///
/// Those read as one are the types every checker reads alike — a
/// parameterless type of words and the path type at its cells' point,
/// reflexivity at that point and the words' empty word, two session types
/// whose protocols behave alike from their states, a type decoding a static
/// redex and the type its reduct decodes — and a staged type and its base, as
/// the printer writes it, since the surface spells no stage, and a dependent
/// arrow whose codomain names no binder and the plain arrow, since the surface
/// reads `(x : A) -> C` as the arrow where `C` does not name `x` (#577).
///
/// # Specification
/// - requires: `signatures` holds the data declarations the types name.
/// - ensures: [`CertificateEquality::Equal`] exactly when every reached pair,
///   each value type read at its base when it is staged, agrees in syntax after
///   path evidence is erased, is `Data(words, [])` against `Path(S, a, b)` with
///   [`identified_words`] reading the path as `words`, in either order, is
///   `here(p)` against the empty word of such words at a point `p` spells
///   ([`empty_word`]), in either order, or is two session types whose
///   protocols, each unfolded at its recursion, take the same action at every
///   pair of states reached from the two types' states — sends and receives
///   with payload types that agree in turn, selections and offers over the same
///   labels, `end` — whatever their nodes' positions; a decode whose code is a
///   static abstraction applied to no more arguments than its chain has binders
///   is read as the decode of the abstraction's body instantiated at the
///   arguments, at most [`StaticSteps::ALLOWED`] times along one comparison; a
///   call of a function literal on no more arguments than the literal has
///   abstractions, whose body returns, is read as the value it returns, on the
///   same steps, and a decode of such a call as the decode of what it returns
///   (#736), the runs its code binds calls by read as the calls first (#768); a
///   call kept unelaborated is read as the value it returns; a dependent arrow
///   is read as the plain arrow where its codomain reads as the arrow's
///   codomain under the binder, which then names no binder; and a dependent
///   pair as the product of two where its second factor reads as the product's
///   second component under the binder (#771).
/// - provides: the comparison a printed type's reading back is held to: a type
///   of words has no name the surface writes, and is spelled as the path type
///   it reads as; a session type at a state is spelled as the protocol from
///   that state, which reads back to a protocol at its root; a static redex the
///   surface cannot apply is spelled as its reduct, and so is a call of a
///   function literal; a stage has no spelling, and a staged type is spelled as
///   its base; a dependent arrow ignoring its binder has no spelling, and is
///   spelled as the arrow; a dependent pair ignoring its binder is spelled as
///   the product.
/// - fails: returns `Different` on a dangling node.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the circle's words against the path at its point, alone
///   and under a path type, compare equal where the syntax alone compares
///   different; at an endpoint off the point they stay different; reflexivity
///   at the point against the empty word compares equal, off it different. A
///   session type past its first send against the rest of its protocol at its
///   root, and a recursive protocol against its unfolding, compare equal; a
///   differing payload or label stays different. A decoded redex against its
///   reduct compares equal; against another type it stays different. A called
///   function literal reads as the value its body returns, and a called name
///   stays a call. A staged type, alone and as an arrow's domain, reads as its
///   base where the syntax alone tells them apart, and stays different from
///   another type. A path between a call returned reads as one between the call
///   kept, and not as one between another call. A dependent arrow ignoring its
///   binder reads as the arrow, in either order; one naming its binder stays
///   different. A decoded literal call reads as what it returns, and a
///   dependent arrow whose binder only that call names as the arrow; so does a
///   literal decoded at a run-bound call, forty side by side in one comparison,
///   while a run calling a name stays a decode. A dependent pair ignoring its
///   binder reads as the product, in either order; one naming it stays
///   different.
/// - witness: `syntax::tests::a_type_of_words_reads_as_the_path_at_its_point_399`
/// - witness: `syntax::tests::a_session_type_reads_as_its_protocol_from_its_state_400`
/// - witness: `syntax::tests::a_decoded_redex_reads_as_its_reduct`
/// - witness: `syntax::tests::a_staged_type_reads_as_its_base_465`
/// - witness: `syntax::tests::a_called_function_literal_reads_as_what_it_returns_675`
/// - witness: `syntax::tests::a_kept_call_reads_as_the_value_it_returns`
/// - witness: `syntax::tests::a_dependent_arrow_ignoring_its_binder_reads_as_the_arrow`
/// - witness: `syntax::tests::a_decoded_literal_call_reads_as_what_it_returns_736`
/// - witness: `syntax::tests::a_literal_decoded_at_a_run_bound_call_reads_as_what_it_returns_768`
/// - witness: `syntax::tests::a_dependent_pair_ignoring_its_binder_reads_as_the_product_771`
#[spec(ensures: |ret| ret == CertificateEquality::Different || (arena.value_type(left).is_some() && arena.value_type(right).is_some()))]
#[inline]
#[must_use]
pub fn equal_type_reading(
    arena: &crate::CoreArena,
    signatures: &BTreeMap<ConstantIndex, alloc::sync::Arc<DataSignature>>,
    left: ValueTypeId,
    right: ValueTypeId,
) -> CertificateEquality
{
    equal_syntax(
        arena,
        Reading::Printed(signatures),
        StructuralGoal::ValueType(left, right),
    )
}

/// The type `id` refines when it is staged, `id` itself otherwise.
///
/// # Specification
/// - requires: nothing; an unreadable id is returned as it is.
/// - ensures: the base of a staged type, which is never itself staged; `id` for
///   any other.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`equal_type_reading`].
/// - witness: `syntax::tests::a_staged_type_reads_as_its_base_465`
#[spec(ensures: |ret| ret == id || matches!(arena.value_type(id), Some(&ValueType::Staged { base, .. }) if base == ret))]
fn unstaged(
    arena: &crate::CoreArena,
    id: ValueTypeId,
) -> ValueTypeId
{
    match arena.value_type(id) {
        Some(&ValueType::Staged { base, .. }) => base,
        Some(_) | None => id,
    }
}

/// The computation `id` forces when it forces the value a computation
/// returns, `id` itself otherwise: `force (returned c)` is the head the
/// checker writes where a type applies a component of a dependent pair, and
/// `c` the one a call on the selection lowers to; both print as the selection
/// called.
///
/// # Specification
/// - requires: nothing; an unreadable id is returned as it is.
/// - ensures: `c` for `force (returned c)`; `id` for any other.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`equal_type_reading`].
/// - witness: `syntax::tests::a_forced_returned_head_reads_as_its_computation_935`
#[spec(ensures: |ret| ret == id || matches!(arena.computation(id), Some(&Computation::Force(forced)) if matches!(arena.value(forced), Some(&Value::Returned(c)) if c == ret)))]
fn forced_returned(
    arena: &crate::CoreArena,
    id: ComputationId,
) -> ComputationId
{
    if let Some(&Computation::Force(forced)) = arena.computation(id)
        && let Some(&Value::Returned(returned)) = arena.value(forced)
    {
        return returned;
    }
    id
}

/// The static steps one [`equal_type_reading`] has left: a code the steps do
/// not settle is compared as it stands.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct StaticSteps(u32);

/// Whether [`StaticSteps::spend`] took a step.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Spend
{
    /// A step was left and is spent.
    Taken,
    /// No step was left.
    Exhausted,
}

impl StaticSteps
{
    /// The steps one comparison starts with: the record of the λ-calculus's
    /// models, seventeen components each read at the syntax model, spends
    /// seventy-one along its widest comparison (#768).
    const ALLOWED: Self = Self(256);

    /// Spend one step, if one is left.
    ///
    /// # Specification
    /// - ensures: [`Spend::Taken`] and one step fewer when a step was left;
    ///   [`Spend::Exhausted`] and no change when none was.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`equal_type_reading`].
    /// - witness: `syntax::tests::a_decoded_redex_reads_as_its_reduct`
    #[spec(captures: before = self.0, ensures: |ret| (ret == Spend::Taken && self.0.checked_add(1) == Some(before)) || (ret == Spend::Exhausted && before == 0 && self.0 == 0))]
    fn spend(&mut self) -> Spend
    {
        match self.0.checked_sub(1_u32) {
            Some(left) => {
                self.0 = left;
                Spend::Taken
            },
            None => Spend::Exhausted,
        }
    }
}

/// The code a static redex `code` reduces to in one step, or `code` itself.
///
/// # Specification
/// - requires: nothing.
/// - ensures: for a spine of static applications whose head is a static
///   abstraction with at least as many binders as the spine has arguments, the
///   abstraction's body instantiated at the arguments, the first applied
///   outermost, and the binders left over still bound; `code` itself for every
///   other code. The arena is copied the first time it is written.
/// - provides: static β, as the checker's own step takes it, for the comparison
///   a printed type's reading back is held to.
/// - fails: never.
/// - panics: none.
///
/// # Termination
/// - reason: `while` loops over the spine and over the arguments.
/// - measure: the arguments left.
///
/// # Adequacy
/// - hypothesis: L3 — as [`equal_type_reading`].
/// - witness: `syntax::tests::a_decoded_redex_reads_as_its_reduct`
#[spec(ensures: |ret| ret == code || arena.value(ret).is_some())]
fn static_reduct(
    arena: &mut alloc::borrow::Cow<'_, crate::CoreArena>,
    code: ValueId,
) -> ValueId
{
    let mut arguments = Vec::new();
    let mut head = code;
    while let Some(&Value::StaticApplication(applied, argument)) = arena.value(head) {
        arguments.push(argument);
        head = applied;
    }
    let mut reduct = head;
    while let Some(argument) = arguments.pop() {
        let Some(&Value::StaticLambda(body)) = arena.value(reduct)
        else {
            return code;
        };
        reduct = crate::rewrite::instantiate_value(arena.to_mut(), body, argument);
    }
    if reduct == head { code } else { reduct }
}

/// The value type `ty` reads as once a static redex its decode holds is
/// reduced, while `steps` lasts.
///
/// # Specification
/// - requires: nothing.
/// - ensures: for a decode of a code [`static_reduct`] reduces, or else of a
///   call of a function literal [`called_reduct`] reduces (#736) once each run
///   the code binds a call by is read as the call ([`inlined_runs`], #768), the
///   decode of the reduct — the quoted type itself when the reduct is a quote —
///   taken again while it reduces and `steps` lasts, one step spent per
///   reduction and per run read; `ty` itself for every other type, its runs
///   kept and no step spent.
/// - provides: the value-type half of the static β [`equal_type_reading`] reads
///   through.
/// - fails: never.
/// - panics: none.
///
/// # Termination
/// - reason: every turn spends one of `steps`.
/// - measure: `steps`.
///
/// # Adequacy
/// - hypothesis: L3 — as [`equal_type_reading`].
/// - witness: `syntax::tests::a_decoded_redex_reads_as_its_reduct`
/// - witness: `syntax::tests::a_decoded_literal_call_reads_as_what_it_returns_736`
/// - witness: `syntax::tests::a_literal_decoded_at_a_run_bound_call_reads_as_what_it_returns_768`
#[spec(ensures: |ret| ret == ty || arena.value_type(ret).is_some())]
fn decoded_value_type(
    arena: &mut alloc::borrow::Cow<'_, crate::CoreArena>,
    steps: &mut StaticSteps,
    ty: ValueTypeId,
) -> ValueTypeId
{
    let mut ty = ty;
    while let Some(&ValueType::Element { code, ref target }) = arena.value_type(ty) {
        let target = target.clone();
        let reduct = static_reduct(arena, code);
        let reduct = if reduct == code {
            literal_reduct(arena, steps, code)
        }
        else {
            reduct
        };
        if reduct == code {
            break;
        }
        if steps.spend() == Spend::Exhausted {
            break;
        }
        ty = arena.to_mut().value_type_element(reduct, target);
    }
    ty
}

/// The computation type `ty` reads as once a static redex its decode holds is
/// reduced, while `steps` lasts.
///
/// # Specification
/// - requires: nothing.
/// - ensures: as [`decoded_value_type`], for a computation type's decode.
/// - provides: the computation-type half of the static β [`equal_type_reading`]
///   reads through.
/// - fails: never.
/// - panics: none.
///
/// # Termination
/// - reason: every turn spends one of `steps`.
/// - measure: `steps`.
///
/// # Adequacy
/// - hypothesis: L3 — as [`equal_type_reading`].
/// - witness: `syntax::tests::a_decoded_redex_reads_as_its_reduct`
#[spec(ensures: |ret| ret == ty || arena.comp_type(ret).is_some())]
fn decoded_comp_type(
    arena: &mut alloc::borrow::Cow<'_, crate::CoreArena>,
    steps: &mut StaticSteps,
    ty: CompTypeId,
) -> CompTypeId
{
    let mut ty = ty;
    while let Some(&CompType::Element { code, ref target }) = arena.comp_type(ty) {
        let target = target.clone();
        let reduct = static_reduct(arena, code);
        let reduct = if reduct == code {
            literal_reduct(arena, steps, code)
        }
        else {
            reduct
        };
        if reduct == code {
            break;
        }
        if steps.spend() == Spend::Exhausted {
            break;
        }
        ty = arena.to_mut().comp_type_element(reduct, target);
    }
    ty
}

/// The code a decode of `code` reads as once a call of a function literal it
/// stands for is reduced, its runs over calls read as the calls first.
///
/// # Specification
/// - requires: nothing.
/// - ensures: [`called_reduct`] of the code [`inlined_runs`] reads `code` as,
///   with the steps both spend taken from `steps`, when that reduces; `code`
///   itself, and `steps` as they were, when it does not. Nodes the attempt
///   makes stay in `arena` unread.
/// - provides: a family filled by a function literal and applied at a nested
///   call — `tm(e(g))`, which the lowering binds as `x ← e(g); tm(x)` — reads
///   as what the literal returns, as the printer spells it (#768).
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`equal_type_reading`].
/// - witness: `syntax::tests::a_literal_decoded_at_a_run_bound_call_reads_as_what_it_returns_768`
#[spec(ensures: |ret| ret == code || arena.value(ret).is_some())]
fn literal_reduct(
    arena: &mut alloc::borrow::Cow<'_, crate::CoreArena>,
    steps: &mut StaticSteps,
    code: ValueId,
) -> ValueId
{
    let mut trial = *steps;
    let inlined = inlined_runs(arena, &mut trial, code);
    let called = called_reduct(arena, &mut trial, inlined);
    if called == inlined {
        return code;
    }
    *steps = trial;
    called
}

/// The computation type `ty` stands for once its decode is read.
///
/// The code is reduced as [`equal_type_reading`] reduces it, and a reduct
/// that quotes a computation type decodes to that type
/// ([`CoreArena::comp_type_element`]).
///
/// # Specification
/// - requires: nothing; an unreadable id is returned as it is.
/// - ensures: as `decoded_comp_type` within [`StaticSteps::ALLOWED`] steps: for
///   a decode whose code reduces, the decode of the reduct — the quoted type
///   itself when the reduct is a quote — taken again while it reduces; `ty`
///   itself for every other type. Nodes a reduction makes are minted in
///   `arena`.
/// - provides: what a computation the run judged at a decode returns, which a
///   `run` binder answers at (#298): `T(A)` at `T` a static abstraction reads
///   as the returner its body is at `A`.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a decode of a static abstraction applied to a type reads
///   as the returner the abstraction's body is at that type; a returner reads
///   as itself.
/// - witness: `syntax::tests::a_decoded_redex_reads_as_the_type_it_quotes_298`
///
/// [`CoreArena::comp_type_element`]: crate::CoreArena::comp_type_element
#[spec(ensures: |ret| ret == ty || arena.comp_type(ret).is_some())]
#[inline]
pub fn decoded_comp_reading(
    arena: &mut crate::CoreArena,
    ty: CompTypeId,
) -> CompTypeId
{
    let mut steps = StaticSteps::ALLOWED;
    // The arena is moved in and back rather than borrowed: a reduction writes
    // it, and a borrowed reading would copy it whole on the first write.
    let mut read = alloc::borrow::Cow::Owned(core::mem::take(arena));
    let read_type = decoded_comp_type(&mut read, &mut steps, ty);
    *arena = read.into_owned();
    read_type
}

/// The value `value` reads as once a call of a function literal it stands
/// for is reduced, while `steps` lasts.
///
/// # Specification
/// - requires: nothing.
/// - ensures: for a call standing as a value, nested or returned, whose head
///   forces a thunk literal of at least as many abstractions as the call has
///   arguments, the value the instantiated body returns, the first argument
///   instantiating the outermost abstraction, taken again while it reduces and
///   `steps` lasts, one step spent per reduction; `value` itself for every
///   other value, and for a body that does more than return. The arena is
///   copied the first time it is written.
/// - provides: the dynamic β [`equal_type_reading`] reads through: a type
///   instantiated at a function literal holds its call, which the surface
///   cannot spell, and is printed as the value the call returns (#675).
/// - fails: never.
/// - panics: none.
///
/// # Termination
/// - reason: every turn of the outer loop spends one of `steps`; the inner
///   loops run over the call's spine and its arguments.
/// - measure: `steps`.
///
/// # Adequacy
/// - hypothesis: L3 — a call of a literal identity and one of a literal
///   projection on two arguments read as the argument they return; a call of a
///   named function and a literal whose body does more than return stay as
///   written.
/// - witness: `syntax::tests::a_called_function_literal_reads_as_what_it_returns_675`
#[spec(ensures: |ret| ret == value || arena.value(ret).is_some())]
fn called_reduct(
    arena: &mut alloc::borrow::Cow<'_, crate::CoreArena>,
    steps: &mut StaticSteps,
    value: ValueId,
) -> ValueId
{
    let mut value = value;
    let mut arguments = Vec::new();
    let mut carried = Vec::new();
    'reduce: while let Some(&(Value::Nested(call) | Value::Returned(call))) = arena.value(value) {
        arguments.clear();
        let mut head = call;
        while let Some(&Computation::Application(function, argument)) = arena.computation(head) {
            arguments.push(argument);
            head = function;
        }
        let Some(&Computation::Force(thunk)) = arena.computation(head)
        else {
            break;
        };
        let Some(&Value::Thunk(mut body)) = arena.value(thunk)
        else {
            break;
        };
        if arguments.is_empty() {
            break;
        }
        while let Some(argument) = arguments.pop() {
            let Some(&Computation::Lambda(inner)) = arena.computation(body)
            else {
                break 'reduce;
            };
            carried.clear();
            body = crate::rewrite::instantiate_computation_traced(
                arena.to_mut(),
                inner,
                argument,
                &mut carried,
            );
        }
        let Some(&Computation::Return(result)) = arena.computation(body)
        else {
            break;
        };
        if steps.spend() == Spend::Exhausted {
            break;
        }
        value = result;
    }
    value
}

/// The value `value` reads as once every run its computation binds a call by
/// stands for the call, while `steps` lasts.
///
/// # Specification
/// - requires: nothing.
/// - ensures: for a value, nested or returned, whose computation is a bind
///   whose bound is a call — an application whose spine ends at a force — the
///   nested value of the rest with the binder instantiated at the call kept
///   nested, taken again while it binds a call and `steps` lasts, one step
///   spent per run; `value` itself for every other value. The arena is copied
///   the first time it is written.
/// - provides: the reading of a nested call the lowering commutes into a run —
///   `same(same(x))` lowers to `a ← same(x); same(a)` — as the call it was
///   written as, which a type instantiated at a function holds and the printer
///   spells (#676).
/// - fails: never.
/// - panics: none.
///
/// # Termination
/// - reason: every turn spends one of `steps`; the inner loop runs over the
///   bound call's spine.
/// - measure: `steps`.
///
/// # Adequacy
/// - hypothesis: L3 — one run and two runs over calls read as the nested calls;
///   a run binding a value forced alone stays a run.
/// - witness: `syntax::tests::a_run_bound_call_reads_as_the_nested_call_676`
#[spec(ensures: |ret| ret == value || arena.value(ret).is_some())]
fn inlined_runs(
    arena: &mut alloc::borrow::Cow<'_, crate::CoreArena>,
    steps: &mut StaticSteps,
    value: ValueId,
) -> ValueId
{
    let mut value = value;
    let mut carried = Vec::new();
    while let Some(&(Value::Nested(computation) | Value::Returned(computation))) =
        arena.value(value)
        && let Some(&Computation::Bind(bound, rest)) = arena.computation(computation)
        && let Some(&Computation::Application(mut head, _)) = arena.computation(bound)
    {
        while let Some(&Computation::Application(inner, _)) = arena.computation(head) {
            head = inner;
        }
        if !matches!(arena.computation(head), Some(&Computation::Force(_))) {
            break;
        }
        if steps.spend() == Spend::Exhausted {
            break;
        }
        let call = arena.to_mut().value_nested(bound);
        carried.clear();
        let rest = crate::rewrite::instantiate_computation_traced(
            arena.to_mut(),
            rest,
            call,
            &mut carried,
        );
        value = arena.to_mut().value_nested(rest);
    }
    value
}

quenchant_shape::reason_enum! {
    /// Why a path type reads as no type of words.
    pub mod unworded {
        /// The reason [`super::identified_words`] answered no declaration.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No declaration's free cells loop over the carrier, as written,
            /// at a point both endpoints spell.
            Unlooped,
        }
    }
}

/// The type of words the path type `Path(carrier, left, right)` reads as.
///
/// The declaration among `signatures` whose free cells loop at a point both
/// endpoints spell, over the parameterless data type `carrier` is as written.
///
/// # Specification
/// - requires: nothing; unreadable ids read as no words.
/// - ensures: `Present(words)` exactly when `carrier` is `Data(sort, [])` and
///   `words`, the first such in key order, carries cells over `sort` whose
///   point both `left` and `right` spell as constructor terms of `sort`.
/// - provides: the identification a checker reads a path type by
///   (`CheckingContext::words`), the one the kernel's `Presentations::words`
///   makes over the admitted cells, and the one a printed type's reading back
///   is held to ([`equal_type_reading`]).
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the circle's path at its point reads as its words; with
///   an endpoint off the point it reads as none.
/// - witness: `syntax::tests::a_type_of_words_reads_as_the_path_at_its_point_399`
#[spec(ensures: |ret| match ret {
    Maybe::Present(words) => signatures.get(&words).is_some_and(|signature| signature.presentation().cells().is_some()),
    Maybe::Absent(_) => true,
})]
#[inline]
pub fn identified_words(
    arena: &crate::CoreArena,
    signatures: &BTreeMap<ConstantIndex, alloc::sync::Arc<DataSignature>>,
    carrier: ValueTypeId,
    (left, right): (ValueId, ValueId),
) -> Maybe<ConstantIndex, unworded::Absent>
{
    let Some(&ValueType::Data {
        declaration: sort,
        ref arguments,
    }) = arena.value_type(carrier)
    else {
        return Maybe::Absent(unworded::Absent::Unlooped);
    };
    if !arguments.is_empty() {
        return Maybe::Absent(unworded::Absent::Unlooped);
    }
    signatures
        .iter()
        .find_map(|(&words, signature)| {
            let cells = signature.presentation().cells()?;
            (cells.sort() == sort
                && spells(arena, sort, left, cells.point()) == Spelling::Spelled
                && spells(arena, sort, right, cells.point()) == Spelling::Spelled)
                .then_some(words)
        })
        .map_or(Maybe::Absent(unworded::Absent::Unlooped), Maybe::Present)
}

/// Whether `words` is `Data(w, [])` and `path` a path type
/// [`identified_words`] reads as `w`.
///
/// # Specification
/// - requires: nothing; unreadable ids identify nothing.
/// - ensures: `Present(w)` exactly in that case.
/// - provides: the rule [`equal_type_reading`] adds to the syntax for a type of
///   words.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`equal_type_reading`].
/// - witness: `syntax::tests::a_type_of_words_reads_as_the_path_at_its_point_399`
#[spec(ensures: |ret| match ret {
    Maybe::Present(found) => matches!(arena.value_type(words), Some(&ValueType::Data { declaration, .. }) if declaration == found),
    Maybe::Absent(_) => true,
})]
fn read_as_words(
    arena: &crate::CoreArena,
    signatures: &BTreeMap<ConstantIndex, alloc::sync::Arc<DataSignature>>,
    (words, path): (ValueTypeId, ValueTypeId),
) -> Maybe<ConstantIndex, unworded::Absent>
{
    let (
        Some(&ValueType::Data {
            declaration,
            ref arguments,
        }),
        Some(&ValueType::Path {
            carrier,
            left,
            right,
        }),
    ) = (arena.value_type(words), arena.value_type(path))
    else {
        return Maybe::Absent(unworded::Absent::Unlooped);
    };
    if !arguments.is_empty() {
        return Maybe::Absent(unworded::Absent::Unlooped);
    }
    if let Maybe::Present(found) = identified_words(arena, signatures, carrier, (left, right))
        && found == declaration
    {
        return Maybe::Present(found);
    }
    Maybe::Absent(unworded::Absent::Unlooped)
}

/// Whether `here` is reflexivity at a point and `word` the empty word of a
/// type of words over that point, which a checker reads as one path.
///
/// # Specification
/// - requires: nothing; unreadable ids identify nothing.
/// - ensures: [`CertificateEquality::Equal`] exactly when `here` is `here(p)`
///   and `word` the constructor of tag zero with no fields of `Data(w, [])`,
///   `w` among `signatures` with cells whose point `p` spells over their sort;
///   [`CertificateEquality::Different`] otherwise.
/// - provides: the value half of the identification [`read_as_words`] makes for
///   types: `here(a)` at the point of a family's loops is its empty word, as
///   the lowering reads it.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the circle's reflexivity at its point against its empty
///   word, alone and under a transport, compares equal; off the point it stays
///   different.
/// - witness: `syntax::tests::a_type_of_words_reads_as_the_path_at_its_point_399`
#[spec(ensures: |ret| ret == CertificateEquality::Different || matches!(arena.value(here), Some(&Value::Here(_))))]
fn empty_word(
    arena: &crate::CoreArena,
    signatures: &BTreeMap<ConstantIndex, alloc::sync::Arc<DataSignature>>,
    (here, word): (ValueId, ValueId),
) -> CertificateEquality
{
    let (
        Some(&Value::Here(point)),
        Some(&Value::Constructor {
            datatype,
            tag,
            ref fields,
        }),
    ) = (arena.value(here), arena.value(word))
    else {
        return CertificateEquality::Different;
    };
    let Some(&ValueType::Data {
        declaration,
        ref arguments,
    }) = arena.value_type(datatype)
    else {
        return CertificateEquality::Different;
    };
    let empty = tag == ConstructorTag::from(0_usize)
        && fields.is_empty()
        && arguments.is_empty()
        && signatures
            .get(&declaration)
            .and_then(|signature| signature.presentation().cells())
            .is_some_and(|cells| {
                spells(arena, cells.sort(), point, cells.point()) == Spelling::Spelled
            });
    if empty {
        CertificateEquality::Equal
    }
    else {
        CertificateEquality::Different
    }
}

/// Whether a value is the closed term a rule side spells.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Spelling
{
    /// The value is the term the side spells.
    Spelled,
    /// It is another term, or no term the arena can read.
    Apart,
}

/// Whether `value` is the constructor term of `sort` that the closed rule side
/// `side` spells.
///
/// # Specification
/// - requires: nothing — unreadable ids spell nothing.
/// - ensures: [`Spelling::Spelled`] exactly when reading `value` in pre-order
///   meets one constructor of `sort` per node of `side`, each with the node's
///   tag, and no node is left over on either side; a variable node spells
///   nothing.
/// - provides: the endpoint comparison of [`identified_words`], as the
///   kernel's, bounded by the side's length whatever the value's depth.
/// - fails: never.
/// - panics: none.
///
/// # Termination
/// - reason: one `for` loop over `side`'s nodes, not recursion.
/// - measure: the nodes of `side` not yet read.
///
/// # Adequacy
/// - hypothesis: L3 — as [`identified_words`].
/// - witness: `syntax::tests::a_type_of_words_reads_as_the_path_at_its_point_399`
#[spec(ensures: |ret| ret == Spelling::Apart || !side.is_empty())]
fn spells(
    arena: &crate::CoreArena,
    sort: ConstantIndex,
    value: ValueId,
    side: &[gandr_kernel_term::RuleNode],
) -> Spelling
{
    let mut pending = Vec::with_capacity(side.len());
    pending.push(value);
    for &node in side {
        let (Some(at), gandr_kernel_term::RuleNode::Constructor(tag)) = (pending.pop(), node)
        else {
            return Spelling::Apart;
        };
        let Some(&Value::Constructor {
            datatype,
            tag: written,
            ref fields,
        }) = arena.value(at)
        else {
            return Spelling::Apart;
        };
        if written != tag
            || !matches!(
                arena.value_type(datatype),
                Some(&ValueType::Data { declaration, .. }) if declaration == sort
            )
        {
            return Spelling::Apart;
        }
        pending.extend(fields.iter().rev());
    }
    if pending.is_empty() {
        Spelling::Spelled
    }
    else {
        Spelling::Apart
    }
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
/// - witness: `effect::tests::a_signature_includes_another_only_at_one_name_and_one_operation_table`
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

/// Queue the payload type pairs of two session types whose protocols behave
/// alike from their states.
///
/// # Specification
/// - ensures: [`CertificateEquality::Equal`] when every pair of states reached
///   from the two types' states, each unfolded through its `mu` and its
///   recursion variables, takes the same action: a send against a send and a
///   receive against a receive, their continuations paired and their payload
///   types queued; a selection against a selection and an offer against an
///   offer over the same labels, the arms paired label by label; `end` against
///   `end`. [`CertificateEquality::Different`] at the first pair that does not,
///   at a node or payload slot past either protocol, and at a state that
///   unfolds to no action within the protocol's length.
/// - executable: none — this is the structural comparison's work-list rule for
///   sessions; its witness drives it through [`equal_type_reading`].
///
/// # Adequacy
/// - hypothesis: L3 — as [`equal_type_reading`].
/// - witness: `syntax::tests::a_session_type_reads_as_its_protocol_from_its_state_400`
fn session_children(
    pending: &mut alloc::vec::Vec<StructuralGoal>,
    left: &crate::session::SessionType,
    right: &crate::session::SessionType,
) -> CertificateEquality
{
    use crate::session::Protocol;
    use crate::session::ProtocolNode;
    use crate::session::ProtocolState;
    /// The action `at` stands at: past every `mu` and recursion variable.
    ///
    /// # Specification
    /// - ensures: the first node of the unfolding from `at` that is an action
    ///   or `end`, with its state; none past the protocol or after more steps
    ///   than it has nodes.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a state under a `mu` and one at a recursion variable
    ///   each reach the action the protocol takes there.
    /// - witness: `syntax::tests::a_session_type_reads_as_its_protocol_from_its_state_400`
    #[spec(ensures: |ret| ret.is_none_or(|(_, node)| !matches!(*node, ProtocolNode::Mu(_) | ProtocolNode::Recur(_))))]
    fn acting(
        protocol: &Protocol,
        at: ProtocolState,
    ) -> Option<(ProtocolState, &ProtocolNode)>
    {
        let mut at = at;
        for _step in 0 ..= protocol.nodes().len() {
            match *protocol.node(at).ok()? {
                ProtocolNode::Mu(next) | ProtocolNode::Recur(next) => at = next,
                ref node @ (ProtocolNode::Send { .. }
                | ProtocolNode::Receive { .. }
                | ProtocolNode::Select(_)
                | ProtocolNode::Offer(_)
                | ProtocolNode::End) => return Some((at, node)),
            }
        }
        None
    }
    let payload = |session: &crate::session::SessionType, slot: crate::session::PayloadSlot| {
        session.payloads().get(usize::from(slot)).copied()
    };
    let mut seen = alloc::collections::BTreeSet::new();
    let mut states = alloc::vec![(left.state(), right.state())];
    while let Some((at_left, at_right)) = states.pop() {
        let (Some((at_left, acts_left)), Some((at_right, acts_right))) = (
            acting(left.protocol(), at_left),
            acting(right.protocol(), at_right),
        )
        else {
            return CertificateEquality::Different;
        };
        if !seen.insert((at_left, at_right)) {
            continue;
        }
        match (acts_left, acts_right) {
            (
                &ProtocolNode::Send {
                    payload: sent,
                    next,
                },
                &ProtocolNode::Send {
                    payload: other,
                    next: then,
                },
            )
            | (
                &ProtocolNode::Receive {
                    payload: sent,
                    next,
                },
                &ProtocolNode::Receive {
                    payload: other,
                    next: then,
                },
            ) => {
                let (Some(sent), Some(other)) = (payload(left, sent), payload(right, other))
                else {
                    return CertificateEquality::Different;
                };
                pending.push(StructuralGoal::ValueType(sent, other));
                states.push((next, then));
            },
            (&ProtocolNode::Select(ref arms), &ProtocolNode::Select(ref others))
            | (&ProtocolNode::Offer(ref arms), &ProtocolNode::Offer(ref others)) => {
                if !arms.keys().eq(others.keys()) {
                    return CertificateEquality::Different;
                }
                states.extend(arms.values().copied().zip(others.values().copied()));
            },
            (&ProtocolNode::End, &ProtocolNode::End) => {},
            (
                &(ProtocolNode::Send { .. }
                | ProtocolNode::Receive { .. }
                | ProtocolNode::Select(_)
                | ProtocolNode::Offer(_)
                | ProtocolNode::End
                | ProtocolNode::Mu(_)
                | ProtocolNode::Recur(_)),
                _,
            ) => return CertificateEquality::Different,
        }
    }
    CertificateEquality::Equal
}

/// Run the shared, evidence-erasing structural comparison.
///
/// # Specification
/// - ensures: returns equal exactly when every reached pair agrees in syntax
///   after path evidence is erased or, under [`Reading::Printed`], is a pair a
///   printed type reads back as one type: each value type at its base when it
///   is staged, a value-type pair the signatures read as one type of words
///   ([`read_as_words`]) agreeing outright, two session types whose protocols
///   behave alike from their states ([`session_children`]), a decoded static
///   redex read as its reduct ([`decoded_value_type`], [`decoded_comp_type`]),
///   a call of a function literal read as the value its body returns
///   ([`called_reduct`]), a call kept unelaborated read as the value it
///   returns, as the lowering keeps it where a type after it reads it, a
///   dependent arrow read as the plain arrow where its codomain reads as the
///   arrow's codomain weakened past its binder, and a dependent pair as the
///   product of two where its second factor reads as the product's second
///   component weakened past its binder (#771); under [`Reading::Syntax`] no
///   reduction is performed.
/// - executable: none — the contract is the inductive graph comparison, not a
///   second traversal pretending to be an independent postcondition.
///
/// # Adequacy
/// - hypothesis: L3 — both certificate and type roots must reach the same child
///   comparison rules without depending on allocation order.
/// - witness: `syntax::tests::certificate_syntax_erases_only_evidence`
/// - witness: `effect::tests::signature_inclusion_ignores_allocation_identity`
/// - witness: `syntax::tests::a_type_of_words_reads_as_the_path_at_its_point_399`
/// - witness: `syntax::tests::a_session_type_reads_as_its_protocol_from_its_state_400`
/// - witness: `syntax::tests::a_dependent_arrow_ignoring_its_binder_reads_as_the_arrow`
/// - witness: `syntax::tests::each_value_former_equals_its_twin_and_differs_where_its_guard_does`
/// - witness: `syntax::tests::each_computation_former_equals_its_twin_and_differs_where_its_guard_does`
/// - witness: `syntax::tests::each_type_former_equals_its_twin_and_differs_where_its_guard_does`
fn equal_syntax(
    arena: &crate::CoreArena,
    reading: Reading<'_>,
    root: StructuralGoal,
) -> CertificateEquality
{
    use StructuralGoal::CompType as CT;
    use StructuralGoal::Computation as C;
    use StructuralGoal::Value as V;
    use StructuralGoal::ValueType as VT;
    let unread = BTreeMap::new();
    let signatures = match reading {
        Reading::Syntax => &unread,
        Reading::Printed(signatures) => signatures,
    };
    let mut arena = alloc::borrow::Cow::Borrowed(arena);
    let mut steps = StaticSteps::ALLOWED;
    let mut pending = alloc::vec![root];
    let mut visited = alloc::collections::BTreeSet::new();
    while let Some(goal) = pending.pop() {
        let goal = match (reading, goal) {
            (Reading::Printed(_), VT(a, b)) => {
                let (a, b) = (unstaged(&arena, a), unstaged(&arena, b));
                VT(
                    decoded_value_type(&mut arena, &mut steps, a),
                    decoded_value_type(&mut arena, &mut steps, b),
                )
            },
            (Reading::Printed(_), CT(a, b)) => CT(
                decoded_comp_type(&mut arena, &mut steps, a),
                decoded_comp_type(&mut arena, &mut steps, b),
            ),
            (Reading::Printed(_), V(a, b)) => {
                let a = inlined_runs(&mut arena, &mut steps, a);
                let b = inlined_runs(&mut arena, &mut steps, b);
                V(
                    called_reduct(&mut arena, &mut steps, a),
                    called_reduct(&mut arena, &mut steps, b),
                )
            },
            (Reading::Printed(_), C(a, b)) => {
                C(forced_returned(&arena, a), forced_returned(&arena, b))
            },
            (Reading::Syntax, _) => goal,
        };
        if !visited.insert(goal) {
            continue;
        }
        match goal {
            V(a, b) => {
                if empty_word(&arena, signatures, (a, b)) == CertificateEquality::Equal
                    || empty_word(&arena, signatures, (b, a)) == CertificateEquality::Equal
                {
                    continue;
                }
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
                                (
                                    crate::control::StackFrame::Apply(left),
                                    crate::control::StackFrame::Apply(right),
                                ) => pending.push(V(left, right)),
                                (
                                    crate::control::StackFrame::Bind(left),
                                    crate::control::StackFrame::Bind(right),
                                ) => pending.push(C(left, right)),
                                (
                                    crate::control::StackFrame::Project(left),
                                    crate::control::StackFrame::Project(right),
                                ) if left == right => {},
                                _ => return CertificateEquality::Different,
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
                    else if let (&Value::Here(a), &Value::Here(b))
                    | (&Value::Stay(a), &Value::Stay(b))
                    | (&Value::Forward(a), &Value::Forward(b)) =
                        (matched_left_value, matched_right_value)
                    {
                        pending.push(V(a, b));
                    }
                    else if let Value::Returned(a) = *matched_left_value
                        && let Value::Returned(b) = *matched_right_value
                    {
                        pending.push(C(a, b));
                    }
                    // A call printed in a type, `f(x)`, is one spelling the
                    // lowering keeps unelaborated where the checker decides
                    // it and as the value it returns where a type after it
                    // reads it; read back, either is the value it returns.
                    else if matches!(reading, Reading::Printed(_))
                        && let (&Value::Returned(a), &Value::Nested(b))
                        | (&Value::Nested(a), &Value::Returned(b)) =
                            (matched_left_value, matched_right_value)
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
                    | (&Value::Equiv(a, b), &Value::Equiv(c, d))
                    | (&Value::Univalence(a, b), &Value::Univalence(c, d))
                    | (&Value::Then(a, b), &Value::Then(c, d))
                    | (&Value::FlowProduct(a, b), &Value::FlowProduct(c, d))
                    | (&Value::FunctionFlow(a, b), &Value::FunctionFlow(c, d)) =
                        (matched_left_value, matched_right_value)
                    {
                        pending.extend([V(a, c), V(b, d)]);
                    }
                    else if let Value::SessionRelated {
                        relation: left_relation,
                        source: a,
                        target: b,
                    } = *matched_left_value
                        && let Value::SessionRelated {
                            relation: right_relation,
                            source: c,
                            target: d,
                        } = *matched_right_value
                        && left_relation == right_relation
                    {
                        pending.extend([V(a, c), V(b, d)]);
                    }
                    else if let Value::Recorded(ref left) = *matched_left_value
                        && let Value::Recorded(ref right) = *matched_right_value
                        && left.len() == right.len()
                    {
                        for (left, right) in left.iter().zip(right.iter()) {
                            match (left, right) {
                                (
                                    &crate::session::RecordedMove::Sent(a),
                                    &crate::session::RecordedMove::Sent(b),
                                )
                                | (
                                    &crate::session::RecordedMove::Received(a),
                                    &crate::session::RecordedMove::Received(b),
                                ) => pending.push(V(a, b)),
                                (
                                    &crate::session::RecordedMove::Selected(ref a),
                                    &crate::session::RecordedMove::Selected(ref b),
                                )
                                | (
                                    &crate::session::RecordedMove::Offered(ref a),
                                    &crate::session::RecordedMove::Offered(ref b),
                                ) if a == b => {},
                                (
                                    &crate::session::RecordedMove::Closed,
                                    &crate::session::RecordedMove::Closed,
                                ) => {},
                                _ => return CertificateEquality::Different,
                            }
                        }
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
            C(a, b) => {
                let (Some(a), Some(b)) = (arena.computation(a), arena.computation(b))
                else {
                    return CertificateEquality::Different;
                };
                match (a, b) {
                    (
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
                    (
                        &Computation::RecordProjection(a, ref al),
                        &Computation::RecordProjection(b, ref bl),
                    ) if al == bl => pending.push(V(a, b)),
                    (
                        &Computation::TupleProjection(a, ac),
                        &Computation::TupleProjection(b, bc),
                    ) if ac == bc => pending.push(V(a, b)),
                    (
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
                    (
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
                    (
                        &Computation::Scope {
                            signature: ref left,
                            subject: left_subject,
                            on_return: left_return,
                            clauses: ref left_clauses,
                        },
                        &Computation::Scope {
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
                    (
                        &Computation::Exercise {
                            capability: left_capability,
                            signature: ref left,
                            operation: ref left_op,
                            payload: left_payload,
                        },
                        &Computation::Exercise {
                            capability: right_capability,
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
                        pending.extend([
                            V(left_capability, right_capability),
                            V(left_payload, right_payload),
                        ]);
                    },
                    (&Computation::Resume(a, b), &Computation::Resume(c, d)) => {
                        pending.extend([V(a, c), C(b, d)]);
                    },
                    (&Computation::Abandon(a), &Computation::Abandon(b)) => {
                        pending.push(V(a, b));
                    },
                    (
                        &Computation::Split {
                            scrutinee: a,
                            arity: left_arity,
                            motive: left_motive,
                            body: b,
                        },
                        &Computation::Split {
                            scrutinee: c,
                            arity: right_arity,
                            motive: right_motive,
                            body: d,
                        },
                    ) if left_arity == right_arity => match (left_motive, right_motive) {
                        (SplitMotive::Ambient, SplitMotive::Ambient) => {
                            pending.extend([V(a, c), C(b, d)]);
                        },
                        (SplitMotive::Scrutinee(left), SplitMotive::Scrutinee(right)) => {
                            pending.extend([V(a, c), CT(left, right), C(b, d)]);
                        },
                        (SplitMotive::Ambient | SplitMotive::Scrutinee(_), _) => {
                            return CertificateEquality::Different;
                        },
                    },
                    (&Computation::Reset(a), &Computation::Reset(b))
                    | (&Computation::Shift(a), &Computation::Shift(b))
                    | (&Computation::Lambda(a), &Computation::Lambda(b)) => pending.push(C(a, b)),
                    (&Computation::Bind(a, b), &Computation::Bind(c, d)) => {
                        pending.extend([C(a, c), C(b, d)]);
                    },
                    (&Computation::With(ref left), &Computation::With(ref right))
                        if left.len() == right.len() =>
                    {
                        pending.extend(left.iter().zip(right.iter()).map(|(a, b)| C(*a, *b)));
                    },
                    (
                        &Computation::Ascribe { body: a, ty: b },
                        &Computation::Ascribe { body: c, ty: d },
                    ) => pending.extend([C(a, c), CT(b, d)]),
                    (&Computation::Project(a, b), &Computation::Project(c, d)) if a == c => {
                        pending.push(C(b, d));
                    },
                    (
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
                    (
                        &Computation::ListCase {
                            list: left_list,
                            on_nil: left_nil,
                            on_cons: left_cons,
                        },
                        &Computation::ListCase {
                            list: right_list,
                            on_nil: right_nil,
                            on_cons: right_cons,
                        },
                    ) => pending.extend([
                        V(left_list, right_list),
                        C(left_nil, right_nil),
                        C(left_cons, right_cons),
                    ]),
                    (
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
                    )
                    | (
                        &Computation::Ride {
                            motive: left_motive,
                            flow: left_path,
                            value: left_value,
                        },
                        &Computation::Ride {
                            motive: right_motive,
                            flow: right_path,
                            value: right_value,
                        },
                    ) => pending.extend([
                        VT(left_motive, right_motive),
                        V(left_path, right_path),
                        V(left_value, right_value),
                    ]),
                    (
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
                    (
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
                    (
                        &Computation::Fixpoint {
                            body: a,
                            evidence: left_evidence,
                        },
                        &Computation::Fixpoint {
                            body: b,
                            evidence: right_evidence,
                        },
                    ) if left_evidence == right_evidence => pending.push(C(a, b)),
                    (&Computation::Return(a), &Computation::Return(b))
                    | (&Computation::Force(a), &Computation::Force(b)) => pending.push(V(a, b)),
                    (&Computation::Application(a, b), &Computation::Application(c, d)) => {
                        pending.extend([C(a, c), V(b, d)]);
                    },
                    (&Computation::Transport(a, b), &Computation::Transport(c, d)) => {
                        pending.extend([V(a, c), V(b, d)]);
                    },
                    (
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
                    (&Computation::Hole(left), &Computation::Hole(right)) if left == right => {},
                    (
                        &Computation::Mark {
                            mark: left_mark,
                            body: left_body,
                        },
                        &Computation::Mark {
                            mark: right_mark,
                            body: right_body,
                        },
                    ) if left_mark == right_mark => pending.push(C(left_body, right_body)),
                    (&Computation::Session(ref left), &Computation::Session(ref right)) => {
                        if left.shape() != right.shape() {
                            return CertificateEquality::Different;
                        }
                        pending.extend(
                            left.value_types()
                                .zip(right.value_types())
                                .map(|(a, b)| VT(a, b)),
                        );
                        pending.extend(left.values().zip(right.values()).map(|(a, b)| V(a, b)));
                        pending.extend(
                            left.computations()
                                .zip(right.computations())
                                .map(|(a, b)| C(a, b)),
                        );
                    },
                    (&Computation::Memory(ref left), &Computation::Memory(ref right)) => {
                        if left.shape() != right.shape() {
                            return CertificateEquality::Different;
                        }
                        pending.extend(left.values().zip(right.values()).map(|(a, b)| V(a, b)));
                        pending.extend(
                            left.computations()
                                .zip(right.computations())
                                .map(|(a, b)| C(a, b)),
                        );
                    },
                    (&Computation::World(ref left), &Computation::World(ref right)) => {
                        if left.shape() != right.shape() {
                            return CertificateEquality::Different;
                        }
                        pending.extend(left.values().zip(right.values()).map(|(a, b)| V(a, b)));
                        pending.extend(
                            left.computations()
                                .zip(right.computations())
                                .map(|(a, b)| C(a, b)),
                        );
                    },
                    _ => return CertificateEquality::Different,
                }
            },
            VT(a, b) => {
                if matches!(read_as_words(&arena, signatures, (a, b)), Maybe::Present(_))
                    || matches!(read_as_words(&arena, signatures, (b, a)), Maybe::Present(_))
                {
                    continue;
                }
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
                    )
                    | (
                        &ValueType::Flow {
                            carrier: a,
                            source: b,
                            target: c,
                        },
                        &ValueType::Flow {
                            carrier: d,
                            source: e,
                            target: f,
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
                    else if let (&ValueType::Run(a), &ValueType::Run(b)) =
                        (matched_left_value, matched_right_value)
                    {
                        pending.push(V(a, b));
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
                    else if let ValueType::Sigma {
                        first: a,
                        second: b,
                    } = *matched_left_value
                        && let ValueType::Sigma {
                            first: c,
                            second: d,
                        } = *matched_right_value
                    {
                        pending.extend([VT(a, c), VT(b, d)]);
                    }
                    // The surface reads a record whose later field names no
                    // earlier one as the product, and the printer spells a
                    // dependent pair whose second factor, as printed, names
                    // no binder as that record: read back, it is the product.
                    // The second factor is compared with the product's second
                    // component weakened past the binder, so a binder only a
                    // reduced call names (#771) reads as the product too.
                    else if matches!(reading, Reading::Printed(_))
                        && let Some((first, second, component, rest)) =
                            match (matched_left_value, matched_right_value) {
                                (
                                    &ValueType::Sigma { first, second },
                                    &ValueType::Product(ref parts),
                                )
                                | (
                                    &ValueType::Product(ref parts),
                                    &ValueType::Sigma { first, second },
                                ) => match **parts {
                                    [component, rest] => Some((first, second, component, rest)),
                                    _ => None,
                                },
                                _ => None,
                            }
                    {
                        let rest = crate::rewrite::shift_value_type(
                            arena.to_mut(),
                            rest,
                            crate::rewrite::Binders::ONE,
                        )
                        .settle(arena.to_mut());
                        pending.extend([VT(first, component), VT(second, rest)]);
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
                    else if let ValueType::Staged {
                        base: a,
                        stage: ref first,
                    } = *matched_left_value
                        && let ValueType::Staged {
                            base: b,
                            stage: ref second,
                        } = *matched_right_value
                        && (first == second)
                    {
                        pending.push(VT(a, b));
                    }
                    else if let ValueType::Kept {
                        value: a,
                        region: first,
                    } = *matched_left_value
                        && let ValueType::Kept {
                            value: b,
                            region: second,
                        } = *matched_right_value
                        && first == second
                    {
                        pending.push(VT(a, b));
                    }
                    else if let ValueType::Session(ref a) = *matched_left_value
                        && let ValueType::Session(ref b) = *matched_right_value
                        && a.protocol() == b.protocol()
                        && a.state() == b.state()
                    {
                        pending.extend(
                            a.payloads()
                                .iter()
                                .zip(b.payloads())
                                .map(|(a, b)| VT(*a, *b)),
                        );
                    }
                    else if let ValueType::Session(ref a) = *matched_left_value
                        && let ValueType::Session(ref b) = *matched_right_value
                        && matches!(reading, Reading::Printed(_))
                    {
                        if session_children(&mut pending, a, b) == CertificateEquality::Different {
                            return CertificateEquality::Different;
                        }
                    }
                    else if let ValueType::Capability {
                        authority: ref first,
                        grade: left_grade,
                        region: left_region,
                    } = *matched_left_value
                        && let ValueType::Capability {
                            authority: ref second,
                            grade: right_grade,
                            region: right_region,
                        } = *matched_right_value
                        && left_grade == right_grade
                        && left_region == right_region
                        && first.signatures().len() == second.signatures().len()
                    {
                        for (left, right) in first.signatures().zip(second.signatures()) {
                            if signature_children(&mut pending, left, right)
                                == CertificateEquality::Different
                            {
                                return CertificateEquality::Different;
                            }
                        }
                    }
                    else if let ValueType::World(ref first) = *matched_left_value
                        && let ValueType::World(ref second) = *matched_right_value
                        && first.shape() == second.shape()
                    {
                        pending.extend(first.types().zip(second.types()).map(|(a, b)| VT(a, b)));
                    }
                    else if (matches!(
                        *matched_left_value,
                        ValueType::Base(_)
                            | ValueType::Universe { .. }
                            | ValueType::Abstract(_)
                            | ValueType::Unknown
                            | ValueType::Buffer
                    ) && (a == b))
                    {
                        {}
                    }
                    else {
                        return CertificateEquality::Different;
                    }
                }
            },
            CT(a, b) => {
                let (Some(a), Some(b)) = (arena.comp_type(a), arena.comp_type(b))
                else {
                    return CertificateEquality::Different;
                };
                match (a, b) {
                    (&CompType::With(ref left), &CompType::With(ref right))
                        if left.len() == right.len() =>
                    {
                        pending.extend(left.iter().zip(right.iter()).map(|(a, b)| CT(*a, *b)));
                    },
                    (
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
                    (
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
                    // The surface reads `(x : A) -> C` as the plain arrow
                    // where `C` does not name `x`, and the printer spells a
                    // dependent arrow whose codomain, as printed, names no
                    // binder as that arrow: read back, it is the arrow. The
                    // codomain is compared with the arrow's weakened past the
                    // binder, so a binder only a reduced call names (#736)
                    // reads as the arrow too.
                    (
                        &CompType::Pi {
                            domain: a,
                            codomain: b,
                        },
                        &CompType::Arrow {
                            domain: c,
                            codomain: d,
                        },
                    )
                    | (
                        &CompType::Arrow {
                            domain: c,
                            codomain: d,
                        },
                        &CompType::Pi {
                            domain: a,
                            codomain: b,
                        },
                    ) if matches!(reading, Reading::Printed(_)) => {
                        let d = crate::rewrite::shift_comp_type(
                            arena.to_mut(),
                            d,
                            crate::rewrite::Binders::ONE,
                        )
                        .settle(arena.to_mut());
                        pending.extend([VT(a, c), CT(b, d)]);
                    },
                    (
                        &CompType::Element {
                            code: a,
                            ref target,
                        },
                        &CompType::Element {
                            code: b,
                            target: ref other,
                        },
                    ) if target == other => pending.push(V(a, b)),
                    (&CompType::Unknown, &CompType::Unknown) => {},
                    (
                        &CompType::Codata {
                            declaration: a,
                            arguments: ref left,
                        },
                        &CompType::Codata {
                            declaration: b,
                            arguments: ref right,
                        },
                    ) if a == b && left.len() == right.len() => {
                        pending.extend(left.iter().zip(right).map(|(a, b)| V(*a, *b)));
                    },
                    _ => return CertificateEquality::Different,
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
    fn computation_type_syntax_ignores_allocation_identity()
    {
        let mut arena = crate::CoreArena::new();
        let stream = gandr_kernel_term::ConstantIndex::from(0_usize);
        let over = |arena: &mut crate::CoreArena, index: u32| {
            let argument = arena.value_variable(
                crate::Zone::Intuitionistic,
                gandr_kernel_term::DeBruijnIndex::from(index),
            );
            arena.comp_type_codata(stream, alloc::vec![argument])
        };
        let first = over(&mut arena, 0);
        let twin = over(&mut arena, 0);
        let other = over(&mut arena, 1);
        assert_eq!(
            equal_comp_type_syntax(&arena, first, twin),
            CertificateEquality::Equal,
            "two allocations of one codata type are one type"
        );
        assert_eq!(
            equal_comp_type_syntax(&arena, first, other),
            CertificateEquality::Different,
            "a different argument is a different type"
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

    #[test]
    fn a_type_of_words_reads_as_the_path_at_its_point_399()
    {
        use gandr_kernel_term::FreeCell;
        use gandr_kernel_term::FreeCells;
        use gandr_kernel_term::Presentation;
        use gandr_kernel_term::RuleNode;

        let mut arena = crate::CoreArena::new();
        let kind = arena.value_type_universe(
            Sort::Ground(gandr_kernel_term::GroundSort::Value),
            Level::zero(),
        );
        let (sort, words) = (ConstantIndex::from(0_usize), ConstantIndex::from(1_usize));
        let carrier = arena.value_type_data(sort, alloc::vec![]);
        let own = arena.value_type_data(words, alloc::vec![]);
        let point = arena.value_constructor(carrier, ConstructorTag::from(0_usize), alloc::vec![]);
        let base = || -> alloc::boxed::Box<[RuleNode]> {
            [RuleNode::Constructor(ConstructorTag::from(0_usize))].into()
        };
        let cells = FreeCells::new(sort, alloc::vec![FreeCell::new(base(), base())]);
        let mut signatures = BTreeMap::new();
        let _sort = signatures.insert(
            sort,
            alloc::sync::Arc::new(DataSignature::new(
                alloc::vec![],
                alloc::vec![alloc::vec![]],
                kind,
            )),
        );
        let _words = signatures.insert(
            words,
            alloc::sync::Arc::new(
                DataSignature::new(
                    alloc::vec![],
                    alloc::vec![alloc::vec![], alloc::vec![own], alloc::vec![own]],
                    kind,
                )
                .presented(Presentation::words(cells)),
            ),
        );
        let at_point = arena.value_type_path(carrier, point, point);
        let off = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let off_point = arena.value_type_path(carrier, point, off);
        assert_eq!(
            identified_words(&arena, &signatures, carrier, (point, point)),
            Maybe::Present(words),
            "the path at the point reads as its words"
        );
        assert_eq!(
            identified_words(&arena, &signatures, carrier, (point, off)),
            Maybe::Absent(unworded::Absent::Unlooped),
            "an endpoint off the point reads as none"
        );
        // The point is spelled by its constructor of its own sort: another
        // constructor, or the same tag of another datatype, is off it.
        let other_tag =
            arena.value_constructor(carrier, ConstructorTag::from(1_usize), alloc::vec![]);
        let foreign = arena.value_constructor(own, ConstructorTag::from(0_usize), alloc::vec![]);
        for endpoint in [other_tag, foreign] {
            assert_eq!(
                identified_words(&arena, &signatures, carrier, (point, endpoint)),
                Maybe::Absent(unworded::Absent::Unlooped),
                "an endpoint spelled otherwise reads as none"
            );
        }
        // A word's own type, alone and as the carrier of a path between words.
        let empty = arena.value_constructor(own, ConstructorTag::from(0_usize), alloc::vec![]);
        let over_words = arena.value_type_path(own, empty, empty);
        let over_path = arena.value_type_path(at_point, empty, empty);
        for (left, right, what) in [
            (own, at_point, "the words against the path at their point"),
            (at_point, own, "in either order"),
            (over_words, over_path, "under a path type"),
        ] {
            assert_eq!(
                equal_type_reading(&arena, &signatures, left, right),
                CertificateEquality::Equal,
                "{what} read as one type"
            );
            assert_eq!(
                equal_type_syntax(&arena, left, right),
                CertificateEquality::Different,
                "{what} differ in syntax"
            );
        }
        assert_eq!(
            equal_type_reading(&arena, &signatures, own, off_point),
            CertificateEquality::Different,
            "the words are not a path off their point"
        );
        // Reflexivity at the point, against the empty word, as a path's
        // endpoint: the value half of the same identification.
        let reflexive = arena.value_here(point);
        let off_reflexive = arena.value_here(off);
        let doubled = arena.value_type_path(at_point, reflexive, reflexive);
        let off_doubled = arena.value_type_path(at_point, off_reflexive, off_reflexive);
        assert_eq!(
            (
                equal_type_reading(&arena, &signatures, doubled, over_path),
                equal_type_reading(&arena, &signatures, over_path, doubled),
                equal_type_syntax(&arena, doubled, over_path),
            ),
            (
                CertificateEquality::Equal,
                CertificateEquality::Equal,
                CertificateEquality::Different
            ),
            "reflexivity at the point reads as the empty word, in either order"
        );
        assert_eq!(
            equal_type_reading(&arena, &signatures, off_doubled, over_path),
            CertificateEquality::Different,
            "reflexivity off the point is no word"
        );
    }

    #[test]
    fn a_session_type_reads_as_its_protocol_from_its_state_400()
    {
        use alloc::sync::Arc;

        use crate::session::PayloadCount;
        use crate::session::PayloadSlot;
        use crate::session::Protocol;
        use crate::session::ProtocolState;
        use crate::session::ProtocolSyntax;
        use crate::session::RecursionIndex;
        use crate::session::SessionType;

        let slot = PayloadSlot::from;
        let state = ProtocolState::from;
        let mut arena = crate::CoreArena::new();
        let integer = arena.value_type_base(gandr_kernel_term::BaseType::Integer);
        let string = arena.value_type_base(gandr_kernel_term::BaseType::String);
        let protocol = |syntax: alloc::vec::Vec<ProtocolSyntax>, payloads: usize| {
            Arc::new(
                Protocol::new(syntax, state(0_usize), PayloadCount::from(payloads))
                    .expect("the protocol is well formed"),
            )
        };
        // !Integer. mu t. ?String. t, past its send.
        let whole = protocol(
            alloc::vec![
                ProtocolSyntax::Send {
                    payload: slot(0_usize),
                    next: state(1_usize),
                },
                ProtocolSyntax::Mu(state(2_usize)),
                ProtocolSyntax::Receive {
                    payload: slot(1_usize),
                    next: state(3_usize),
                },
                ProtocolSyntax::Recur(RecursionIndex::from(0_usize)),
            ],
            2_usize,
        );
        let past = SessionType::new(whole, Arc::from([integer, string]))
            .and_then(|session| session.at(state(1_usize)))
            .expect("the state is a node of the protocol");
        let past = arena.value_type_session(past);
        // mu t. ?A. t, and its unfolding ?A. mu t. ?A. t, each at its root.
        let rest = protocol(
            alloc::vec![
                ProtocolSyntax::Mu(state(1_usize)),
                ProtocolSyntax::Receive {
                    payload: slot(0_usize),
                    next: state(2_usize),
                },
                ProtocolSyntax::Recur(RecursionIndex::from(0_usize)),
            ],
            1_usize,
        );
        let unfolded = protocol(
            alloc::vec![
                ProtocolSyntax::Receive {
                    payload: slot(0_usize),
                    next: state(1_usize),
                },
                ProtocolSyntax::Mu(state(2_usize)),
                ProtocolSyntax::Receive {
                    payload: slot(0_usize),
                    next: state(3_usize),
                },
                ProtocolSyntax::Recur(RecursionIndex::from(0_usize)),
            ],
            1_usize,
        );
        let mut rooted = |protocol: &Arc<Protocol>, payload| {
            let session = SessionType::new(Arc::clone(protocol), Arc::from([payload]))
                .expect("one payload for one slot");
            arena.value_type_session(session)
        };
        let rest_of_strings = rooted(&rest, string);
        let unfolded_strings = rooted(&unfolded, string);
        let rest_of_integers = rooted(&rest, integer);
        let signatures = BTreeMap::new();
        for (other, what) in [
            (rest_of_strings, "the rest of the protocol at its root"),
            (unfolded_strings, "its unfolding"),
        ] {
            assert_eq!(
                equal_type_reading(&arena, &signatures, past, other),
                CertificateEquality::Equal,
                "the state reads as {what}"
            );
            assert_eq!(
                equal_type_syntax(&arena, past, other),
                CertificateEquality::Different,
                "the state and {what} differ in syntax"
            );
        }
        assert_eq!(
            equal_type_reading(&arena, &signatures, past, rest_of_integers),
            CertificateEquality::Different,
            "a differing payload type stays different"
        );
    }

    #[test]
    fn a_decoded_redex_reads_as_its_reduct()
    {
        let mut arena = crate::CoreArena::new();
        let level = Level::constant(gandr_kernel_strata::LevelConstant::ZERO);
        let integer = arena.value_type_base(BaseType::Integer);
        let string = arena.value_type_base(BaseType::String);
        let quoted_integer = arena.value_quote(integer);
        let quoted_string = arena.value_quote(string);
        let decoded = |arena: &mut crate::CoreArena, index: u32| {
            let variable = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(index));
            arena.value_type_element(variable, level.clone())
        };
        // `(\a. -F (a * a))(Integer)`, a computation type's decode.
        let a = decoded(&mut arena, 0_u32);
        let square = arena.value_type_product(&[a, a]);
        let returner = arena.comp_type_returner(square);
        let body = arena.value_quote_computation(returner);
        let operator = arena.value_static_lambda(body);
        let redex = arena.value_static_application(operator, quoted_integer);
        let redex = arena.comp_type_element(redex, level.clone());
        let redex = arena.value_type_thunk(redex);
        let squared = arena.value_type_product(&[integer, integer]);
        let squared = arena.comp_type_returner(squared);
        let squared = arena.value_type_thunk(squared);
        let mixed = arena.value_type_product(&[integer, string]);
        let mixed = arena.comp_type_returner(mixed);
        let mixed = arena.value_type_thunk(mixed);
        // `(\a. \b. a * b)(Integer)(String)`, a value type's decode.
        let outer = decoded(&mut arena, 1_u32);
        let inner = decoded(&mut arena, 0_u32);
        let pair = arena.value_type_product(&[outer, inner]);
        let pair = arena.value_quote(pair);
        let pair = arena.value_static_lambda(pair);
        let pair = arena.value_static_lambda(pair);
        let pair = arena.value_static_application(pair, quoted_integer);
        let pair = arena.value_static_application(pair, quoted_string);
        let pair = arena.value_type_element(pair, level.clone());
        let in_order = arena.value_type_product(&[integer, string]);
        let swapped = arena.value_type_product(&[string, integer]);
        let signatures = BTreeMap::new();

        assert_eq!(
            (
                equal_type_reading(&arena, &signatures, redex, squared),
                equal_type_syntax(&arena, redex, squared),
            ),
            (CertificateEquality::Equal, CertificateEquality::Different),
            "the decoded redex reads as its reduct, which its syntax is not"
        );
        assert_eq!(
            equal_type_reading(&arena, &signatures, redex, mixed),
            CertificateEquality::Different,
            "the reduct is not another type"
        );
        assert_eq!(
            (
                equal_type_reading(&arena, &signatures, pair, in_order),
                equal_type_reading(&arena, &signatures, pair, swapped),
            ),
            (CertificateEquality::Equal, CertificateEquality::Different),
            "the first argument instantiates the outer binder"
        );
    }

    /// #298: a decode of a static abstraction applied to a type reads as the
    /// returner the abstraction's body is at that type, which a `run` binder
    /// answers at; a returner reads as itself.
    #[test]
    fn a_decoded_redex_reads_as_the_type_it_quotes_298()
    {
        let mut arena = crate::CoreArena::new();
        let level = Level::constant(gandr_kernel_strata::LevelConstant::ZERO);
        let integer = arena.value_type_base(BaseType::Integer);
        let quoted_integer = arena.value_quote(integer);
        // `(\a. -F (a * a))(Integer)`, a computation type's decode.
        let variable = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let a = arena.value_type_element(variable, level.clone());
        let square = arena.value_type_product(&[a, a]);
        let body = arena.comp_type_returner(square);
        let body = arena.value_quote_computation(body);
        let operator = arena.value_static_lambda(body);
        let redex = arena.value_static_application(operator, quoted_integer);
        let redex = arena.comp_type_element(redex, level);
        let squared = arena.value_type_product(&[integer, integer]);

        let read = decoded_comp_reading(&mut arena, redex);
        let Some(&CompType::Returner { result, .. }) = arena.comp_type(read)
        else {
            panic!(
                "the decode reads as a returner: {:?}",
                arena.comp_type(read)
            );
        };
        assert_eq!(
            equal_type_syntax(&arena, result, squared),
            CertificateEquality::Equal,
            "the returner returns the body's type at the argument"
        );
        let returner = arena.comp_type_returner(squared);
        assert_eq!(
            decoded_comp_reading(&mut arena, returner),
            returner,
            "a returner reads as itself"
        );
    }

    /// #935: a type calling a dependent pair's first component, as the
    /// checker writes it (`force (returned p.0)` called), reads as the call
    /// on the selection the surface lowers it to; a call on another head
    /// stays different.
    #[test]
    fn a_forced_returned_head_reads_as_its_computation_935()
    {
        let mut arena = crate::CoreArena::new();
        let signatures = BTreeMap::new();
        let nat = arena.value_type_data(ConstantIndex::from(0_usize), alloc::vec![]);
        let pair = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let point = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
        let selected = |arena: &mut crate::CoreArena| {
            arena.computation_tuple_projection(pair, gandr_kernel_term::Component::from(0_usize))
        };
        // `Path(Nat, head(x), x)`.
        let called = |arena: &mut crate::CoreArena, head: ComputationId| {
            let call = arena.computation_application(head, point);
            let value = arena.value_returned(call);
            arena.value_type_path(nat, value, point)
        };
        let projected = selected(&mut arena);
        let returned = arena.value_returned(projected);
        let forced = arena.computation_force(returned);
        let checked = called(&mut arena, forced);
        let selection = selected(&mut arena);
        let lowered = called(&mut arena, selection);
        let other = arena.computation_force(point);
        let elsewhere = called(&mut arena, other);
        assert_eq!(
            equal_type_reading(&arena, &signatures, checked, lowered),
            CertificateEquality::Equal,
            "the checker's head reads as the lowered selection"
        );
        assert_eq!(
            equal_type_reading(&arena, &signatures, lowered, checked),
            CertificateEquality::Equal,
            "in either order"
        );
        assert_eq!(
            equal_type_syntax(&arena, checked, lowered),
            CertificateEquality::Different,
            "the two heads differ in syntax"
        );
        assert_eq!(
            equal_type_reading(&arena, &signatures, checked, elsewhere),
            CertificateEquality::Different,
            "a call on another head does not read as the selection's"
        );
    }

    #[test]
    fn a_staged_type_reads_as_its_base_465()
    {
        use gandr_kernel_term::Stage;
        use gandr_kernel_term::StageId;

        let mut arena = crate::CoreArena::new();
        let signatures = BTreeMap::new();
        let nat = arena.value_type_data(ConstantIndex::from(0_usize), alloc::vec![]);
        let other = arena.value_type_data(ConstantIndex::from(1_usize), alloc::vec![]);
        let staged = arena.value_type_staged(nat, Stage::At(StageId::from(1_usize)));
        // A recursion's self reference: the parameter it descends on, staged,
        // as the domain of a thunked arrow.
        let returner = arena.comp_type_returner(nat);
        let at_stage = arena.comp_type_arrow(staged, returner);
        let at_stage = arena.value_type_thunk(at_stage);
        let plain = arena.comp_type_arrow(nat, returner);
        let plain = arena.value_type_thunk(plain);
        for (left, right, what) in [
            (staged, nat, "the staged type against its base"),
            (nat, staged, "in either order"),
            (at_stage, plain, "as an arrow's domain"),
        ] {
            assert_eq!(
                equal_type_reading(&arena, &signatures, left, right),
                CertificateEquality::Equal,
                "{what} read as one type"
            );
            assert_eq!(
                equal_type_syntax(&arena, left, right),
                CertificateEquality::Different,
                "{what} differ in syntax"
            );
        }
        assert_eq!(
            equal_type_reading(&arena, &signatures, staged, other),
            CertificateEquality::Different,
            "a staged type does not read as another type"
        );
    }

    /// #736: a decode of a called function literal reads as the decode of
    /// what the call returns, and a dependent arrow whose binder only that
    /// call names reads as the plain arrow; one whose codomain still names
    /// its binder once read stays different.
    #[test]
    fn a_decoded_literal_call_reads_as_what_it_returns_736()
    {
        let mut arena = crate::CoreArena::new();
        let signatures = BTreeMap::new();
        let unit = arena.value_type_product(&[]);
        let unit_code = arena.value_quote(unit);
        let x = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        // `(thunk { fn (g) { return Unit } })(x)`, decoded.
        let returns = arena.computation_return(unit_code);
        let constant = arena.computation_lambda(returns);
        let constant = arena.value_thunk(constant);
        let forced = arena.computation_force(constant);
        let called = arena.computation_application(forced, x);
        let called = arena.value_returned(called);
        let decoded = arena.value_type_element(called, Level::zero());
        let held = arena.comp_type_returner(decoded);
        let read = arena.comp_type_returner(unit);
        let dependent = arena.comp_type_pi(unit, held);
        let plain = arena.comp_type_arrow(unit, read);
        // `(x : Unit) -> -F (x = x)`, whose codomain names its binder.
        let path = arena.value_type_path(unit, x, x);
        let path = arena.comp_type_returner(path);
        let naming = arena.comp_type_pi(unit, path);
        let (held, read, dependent, plain, naming) = (
            arena.value_type_thunk(held),
            arena.value_type_thunk(read),
            arena.value_type_thunk(dependent),
            arena.value_type_thunk(plain),
            arena.value_type_thunk(naming),
        );
        for (left, right, what) in [
            (
                decoded,
                unit,
                "a decoded literal call against what it returns",
            ),
            (held, read, "the same under a returner"),
            (
                dependent,
                plain,
                "a dependent arrow whose binder only the call names against the arrow",
            ),
            (plain, dependent, "in either order"),
        ] {
            assert_eq!(
                (
                    equal_type_reading(&arena, &signatures, left, right),
                    equal_type_syntax(&arena, left, right),
                ),
                (CertificateEquality::Equal, CertificateEquality::Different),
                "{what} read as one type and differ in syntax"
            );
        }
        assert_eq!(
            equal_type_reading(&arena, &signatures, naming, plain),
            CertificateEquality::Different,
            "a dependent arrow naming its binder does not read as the arrow"
        );
    }

    /// A decode substituting a constant family leaves a dependent arrow
    /// whose codomain names no binder (#577); printed as the arrow, it reads
    /// back as one.
    #[test]
    fn a_dependent_arrow_ignoring_its_binder_reads_as_the_arrow()
    {
        let mut arena = crate::CoreArena::new();
        let signatures = BTreeMap::new();
        let nat = arena.value_type_data(ConstantIndex::from(0_usize), alloc::vec![]);
        // A path between the binder `index` binders out, the codomain's
        // result.
        let path = |arena: &mut crate::CoreArena, index: u32| {
            let end = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(index));
            let path = arena.value_type_path(nat, end, end);
            arena.comp_type_returner(path)
        };
        let thunked = |arena: &mut crate::CoreArena, ty: CompTypeId| arena.value_type_thunk(ty);
        // Under one binder around the type: the dependent arrow's codomain
        // names that binder at index one, the arrow's at index zero.
        let (outer_under, outer, own) = (
            path(&mut arena, 1),
            path(&mut arena, 0),
            path(&mut arena, 0),
        );
        let vacuous = arena.comp_type_pi(nat, outer_under);
        let vacuous = thunked(&mut arena, vacuous);
        let plain = arena.comp_type_arrow(nat, outer);
        let plain = thunked(&mut arena, plain);
        let dependent = arena.comp_type_pi(nat, own);
        let dependent = thunked(&mut arena, dependent);
        for (left, right, what) in [
            (
                vacuous,
                plain,
                "a dependent arrow ignoring its binder against the arrow",
            ),
            (plain, vacuous, "in either order"),
        ] {
            assert_eq!(
                equal_type_reading(&arena, &signatures, left, right),
                CertificateEquality::Equal,
                "{what} read as one type"
            );
            assert_eq!(
                equal_type_syntax(&arena, left, right),
                CertificateEquality::Different,
                "{what} differ in syntax"
            );
        }
        assert_eq!(
            equal_type_reading(&arena, &signatures, dependent, plain),
            CertificateEquality::Different,
            "a dependent arrow naming its binder does not read as the arrow"
        );
    }

    /// #771: a dependent pair whose second factor names no binder prints as
    /// the product, and reads back as one, in either order; one whose second
    /// factor names its binder stays different.
    #[test]
    fn a_dependent_pair_ignoring_its_binder_reads_as_the_product_771()
    {
        let mut arena = crate::CoreArena::new();
        let signatures = BTreeMap::new();
        let nat = arena.value_type_data(ConstantIndex::from(0_usize), alloc::vec![]);
        let path = |arena: &mut crate::CoreArena, index: u32| {
            let end = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(index));
            arena.value_type_path(nat, end, end)
        };
        // Under one binder around the type: the pair's second factor names
        // that binder at index one, the product's component at index zero.
        let (outer_under, outer, own) = (
            path(&mut arena, 1),
            path(&mut arena, 0),
            path(&mut arena, 0),
        );
        let vacuous = arena.value_type_sigma(nat, outer_under);
        let product = arena.value_type_product(&[nat, outer]);
        let dependent = arena.value_type_sigma(nat, own);
        for (left, right, what) in [
            (
                vacuous,
                product,
                "a dependent pair ignoring its binder against the product",
            ),
            (product, vacuous, "in either order"),
        ] {
            assert_eq!(
                equal_type_reading(&arena, &signatures, left, right),
                CertificateEquality::Equal,
                "{what} read as one type"
            );
            assert_eq!(
                equal_type_syntax(&arena, left, right),
                CertificateEquality::Different,
                "{what} differ in syntax"
            );
        }
        assert_eq!(
            equal_type_reading(&arena, &signatures, dependent, product),
            CertificateEquality::Different,
            "a dependent pair naming its binder does not read as the product"
        );
    }

    #[test]
    fn a_kept_call_reads_as_the_value_it_returns()
    {
        let mut arena = crate::CoreArena::new();
        let signatures = BTreeMap::new();
        let int = arena.value_type_data(ConstantIndex::from(0_usize), alloc::vec![]);
        // `f(x)` with `f` and `x` the two binders around the type.
        let function = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
        let argument = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let forced = arena.computation_force(function);
        let call = arena.computation_application(forced, argument);
        let other = arena.computation_force(argument);
        let returned = arena.value_returned(call);
        let nested = arena.value_nested(call);
        let elsewhere = arena.value_nested(other);
        let at = |arena: &mut crate::CoreArena, end: ValueId| arena.value_type_path(int, end, end);
        let (returned, nested, elsewhere) = (
            at(&mut arena, returned),
            at(&mut arena, nested),
            at(&mut arena, elsewhere),
        );
        for (left, right, what) in [
            (returned, nested, "a call returned against the call kept"),
            (nested, returned, "in either order"),
        ] {
            assert_eq!(
                equal_type_reading(&arena, &signatures, left, right),
                CertificateEquality::Equal,
                "{what} read as one type"
            );
            assert_eq!(
                equal_type_syntax(&arena, left, right),
                CertificateEquality::Different,
                "{what} differ in syntax"
            );
        }
        assert_eq!(
            equal_type_reading(&arena, &signatures, returned, elsewhere),
            CertificateEquality::Different,
            "a call does not read as another call kept"
        );
    }

    /// #675: a type instantiated at a function literal holds its call, which
    /// the surface prints as the value the call returns.
    #[test]
    fn a_called_function_literal_reads_as_what_it_returns_675()
    {
        let mut arena = crate::CoreArena::new();
        let signatures = BTreeMap::new();
        let int = arena.value_type_data(ConstantIndex::from(0_usize), alloc::vec![]);
        let x = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let y = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
        // `(thunk { fn (b) { return b } })(x)`.
        let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let returns = arena.computation_return(bound);
        let identity = arena.computation_lambda(returns);
        let identity = arena.value_thunk(identity);
        let forced = arena.computation_force(identity);
        let called = arena.computation_application(forced, x);
        let called = arena.value_nested(called);
        // `(thunk { fn (a) { fn (b) { return a } } })(y)((… )(x))`: the first
        // argument instantiates the outer abstraction, and the second is
        // itself a call that reduces.
        let outer = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
        let first = arena.computation_return(outer);
        let first = arena.computation_lambda(first);
        let first = arena.computation_lambda(first);
        let first = arena.value_thunk(first);
        let forced_first = arena.computation_force(first);
        let partly = arena.computation_application(forced_first, y);
        let projected = arena.computation_application(partly, called);
        let projected = arena.value_returned(projected);
        // A call of a name, and a literal whose body does more than return.
        let named = arena.computation_force(y);
        let named = arena.computation_application(named, x);
        let named = arena.value_nested(named);
        let forced_body = arena.computation_force(bound);
        let forcing = arena.computation_lambda(forced_body);
        let forcing = arena.value_thunk(forcing);
        let forcing = arena.computation_force(forcing);
        let forcing = arena.computation_application(forcing, x);
        let forcing = arena.value_nested(forcing);
        let at = |arena: &mut crate::CoreArena, end: ValueId| arena.value_type_path(int, end, x);
        let (called, projected, named, forcing, plain, other) = (
            at(&mut arena, called),
            at(&mut arena, projected),
            at(&mut arena, named),
            at(&mut arena, forcing),
            at(&mut arena, x),
            at(&mut arena, y),
        );
        for (left, right, what) in [
            (
                called,
                plain,
                "a called identity literal against its argument",
            ),
            (plain, called, "in either order"),
            (
                projected,
                other,
                "the first argument instantiates the outer abstraction",
            ),
        ] {
            assert_eq!(
                (
                    equal_type_reading(&arena, &signatures, left, right),
                    equal_type_syntax(&arena, left, right),
                ),
                (CertificateEquality::Equal, CertificateEquality::Different),
                "{what} reads as one type, which its syntax is not"
            );
        }
        for (left, right, what) in [
            (projected, plain, "the outer binder is not the inner one"),
            (named, plain, "a call of a name stays a call"),
            (
                forcing,
                plain,
                "a body that does more than return stays a call",
            ),
        ] {
            assert_eq!(
                equal_type_reading(&arena, &signatures, left, right),
                CertificateEquality::Different,
                "{what}"
            );
        }
    }

    /// #676: the lowering commutes a nested call in a type into a run,
    /// `same(same(x))` into `a ← same(x); same(a)`; read back, the run is
    /// the nested call it was written as.
    #[test]
    fn a_run_bound_call_reads_as_the_nested_call_676()
    {
        let mut arena = crate::CoreArena::new();
        let signatures = BTreeMap::new();
        let int = arena.value_type_data(ConstantIndex::from(0_usize), alloc::vec![]);
        let at = |arena: &mut crate::CoreArena, index: u32| {
            arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(index))
        };
        let call = |arena: &mut crate::CoreArena, function: ValueId, argument: ValueId| {
            let forced = arena.computation_force(function);
            arena.computation_application(forced, argument)
        };
        // `f` and `x` the two binders around the type.
        let (f, x) = (at(&mut arena, 1_u32), at(&mut arena, 0_u32));
        // `f(f(x))` and `f(f(f(x)))` as written: each inner call nested.
        let inner = call(&mut arena, f, x);
        let inner = arena.value_returned(inner);
        let twice = call(&mut arena, f, inner);
        let twice_value = arena.value_returned(twice);
        let thrice = call(&mut arena, f, twice_value);
        let twice = arena.value_nested(twice);
        let thrice = arena.value_nested(thrice);
        // `a ← f(x); f(a)`, and `a ← f(x); b ← f(a); f(b)`.
        let bound = call(&mut arena, f, x);
        let (f_under, a) = (at(&mut arena, 2_u32), at(&mut arena, 0_u32));
        let rest = call(&mut arena, f_under, a);
        let one_run = arena.computation_bind(bound, rest);
        let one_run = arena.value_nested(one_run);
        let second = call(&mut arena, f_under, a);
        let (f_twice_under, b) = (at(&mut arena, 3_u32), at(&mut arena, 0_u32));
        let last = call(&mut arena, f_twice_under, b);
        let two_runs = arena.computation_bind(second, last);
        let two_runs = arena.computation_bind(bound, two_runs);
        let two_runs = arena.value_nested(two_runs);
        // `a ← force(f); f(a)`: the bound is no call.
        let forced = arena.computation_force(f);
        let forced_run = arena.computation_bind(forced, rest);
        let forced_run = arena.value_nested(forced_run);
        let path = |arena: &mut crate::CoreArena, end: ValueId| arena.value_type_path(int, end, x);
        let (twice, thrice, one_run, two_runs, forced_run) = (
            path(&mut arena, twice),
            path(&mut arena, thrice),
            path(&mut arena, one_run),
            path(&mut arena, two_runs),
            path(&mut arena, forced_run),
        );
        for (left, right, what) in [
            (one_run, twice, "one run against the call nested once"),
            (twice, one_run, "in either order"),
            (two_runs, thrice, "two runs, the second naming the first"),
        ] {
            assert_eq!(
                (
                    equal_type_reading(&arena, &signatures, left, right),
                    equal_type_syntax(&arena, left, right),
                ),
                (CertificateEquality::Equal, CertificateEquality::Different),
                "{what} reads as one type, which its syntax is not"
            );
        }
        for (left, right, what) in [
            (one_run, thrice, "a run reads as its own call and no other"),
            (forced_run, twice, "a run binding no call stays a run"),
        ] {
            assert_eq!(
                equal_type_reading(&arena, &signatures, left, right),
                CertificateEquality::Different,
                "{what}"
            );
        }
    }

    /// #768: a family filled by a function literal and applied at a nested
    /// call decodes `x ← f(y); lit(x)`, the run the lowering binds the call
    /// by; read back, it is what the literal returns, as the printer spells
    /// it, while a run calling no literal stays a decode. A comparison whose
    /// reductions outnumber sixty-four, as the λ-calculus's model record's
    /// does, still reads through every one.
    #[test]
    fn a_literal_decoded_at_a_run_bound_call_reads_as_what_it_returns_768()
    {
        let mut arena = crate::CoreArena::new();
        let signatures = BTreeMap::new();
        let unit = arena.value_type_product(&[]);
        let unit_code = arena.value_quote(unit);
        let at = |arena: &mut crate::CoreArena, index: u32| {
            arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(index))
        };
        let call = |arena: &mut crate::CoreArena, function: ValueId, argument: ValueId| {
            let forced = arena.computation_force(function);
            arena.computation_application(forced, argument)
        };
        // `f` and `y` the two binders around the type; `x` the run's.
        let (f, y) = (at(&mut arena, 1_u32), at(&mut arena, 0_u32));
        let bound = call(&mut arena, f, y);
        let x = at(&mut arena, 0_u32);
        // `x ← f(y); (thunk { fn (g) { return Unit } })(x)`, decoded.
        let returns = arena.computation_return(unit_code);
        let literal = arena.computation_lambda(returns);
        let literal = arena.value_thunk(literal);
        let rest = call(&mut arena, literal, x);
        let run = arena.computation_bind(bound, rest);
        let run = arena.value_returned(run);
        let decoded = arena.value_type_element(run, Level::zero());
        // `x ← f(y); f(x)`, decoded: the run calls no literal.
        let f_under = at(&mut arena, 2_u32);
        let named = call(&mut arena, f_under, x);
        let named = arena.computation_bind(bound, named);
        let named = arena.value_returned(named);
        let named = arena.value_type_element(named, Level::zero());
        // Forty of each side by side: eighty reductions in one comparison.
        let wide = arena.value_type_product(&alloc::vec![decoded; 40]);
        let units = arena.value_type_product(&alloc::vec![unit; 40]);
        for (left, right, what) in [
            (
                decoded,
                unit,
                "a literal decoded at a run-bound call against what it returns",
            ),
            (unit, decoded, "in either order"),
            (wide, units, "forty of them against forty units"),
        ] {
            assert_eq!(
                (
                    equal_type_reading(&arena, &signatures, left, right),
                    equal_type_syntax(&arena, left, right),
                ),
                (CertificateEquality::Equal, CertificateEquality::Different),
                "{what} reads as one type, which its syntax is not"
            );
        }
        assert_eq!(
            equal_type_reading(&arena, &signatures, named, unit),
            CertificateEquality::Different,
            "a run calling no literal does not read as the unit"
        );
    }

    #[test]
    fn each_value_former_equals_its_twin_and_differs_where_its_guard_does()
    {
        use alloc::sync::Arc;

        use crate::control::StackFrame;
        use crate::session::RecordedMove;
        use crate::session::SessionRelation;
        use crate::ua::Description;
        use crate::ua::Sides;
        use crate::ua::Stratum;

        let mut arena = crate::CoreArena::new();
        let unit = arena.value_unit();
        let unit_type = arena.value_type_unit();
        let returned = arena.computation_return(unit);
        let label = |name| FieldLabel::from(alloc::string::String::from(name));
        let one = Level::zero().succ().expect("one is a level");
        let mut cases = Vec::new();

        let [twin, same, other_tag, wider] =
            [(0, 1), (0, 1), (1, 1), (0, 2)].map(|(tag, width)| {
                arena.value_constructor(
                    unit_type,
                    ConstructorTag::from(tag),
                    alloc::vec![unit; width],
                )
            });
        cases.push((twin, same, alloc::vec![other_tag, wider], "a constructor"));
        let [twin, same, other_label, wider] = [
            alloc::vec!["a"],
            alloc::vec!["a"],
            alloc::vec!["b"],
            alloc::vec!["a", "b"],
        ]
        .map(|labels| {
            arena.value_record(labels.into_iter().map(|name| (label(name), unit)).collect())
        });
        cases.push((twin, same, alloc::vec![other_label, wider], "a record"));
        let frames = [
            StackFrame::Apply(unit),
            StackFrame::Bind(returned),
            StackFrame::Project(Component::from(0_usize)),
        ];
        let [twin, same] = [(); 2].map(|()| arena.value_reify(Arc::from(frames)));
        let shorter = arena.value_reify(Arc::from([StackFrame::Apply(unit)]));
        let other_side = arena.value_reify(Arc::from([
            StackFrame::Apply(unit),
            StackFrame::Bind(returned),
            StackFrame::Project(Component::from(1_usize)),
        ]));
        cases.push((twin, same, alloc::vec![shorter, other_side], "a stack"));
        let [twin, same, other] = [
            SessionRelation::Equivalence,
            SessionRelation::Equivalence,
            SessionRelation::Subtyping,
        ]
        .map(|relation| arena.value_session_related(relation, unit, unit));
        cases.push((twin, same, alloc::vec![other], "a session identity"));
        let moves = |chosen| {
            Arc::from([
                RecordedMove::Sent(unit),
                RecordedMove::Selected(label(chosen)),
                RecordedMove::Closed,
            ])
        };
        let [twin, same, other_choice] =
            ["a", "a", "b"].map(|chosen| arena.value_recorded(moves(chosen)));
        let shorter = arena.value_recorded(Arc::from([RecordedMove::Sent(unit)]));
        cases.push((
            twin,
            same,
            alloc::vec![shorter, other_choice],
            "a recorded run",
        ));
        let description = |name| Description {
            name: gandr_theory_levitation::Name::from(name),
            generators: alloc::boxed::Box::from([]),
        };
        let sides = |name| {
            Arc::new(Sides {
                source: description(name),
                target: description(name),
            })
        };
        let stratum = |degree| Stratum {
            degree: gandr_theory_sites::Degree::from(degree),
            bound: gandr_theory_sites::ShapeSize::from(4_usize),
        };
        let [twin, same, other_degree, other_sides] =
            [(1_usize, "M"), (1, "M"), (2, "M"), (1, "N")]
                .map(|(degree, name)| arena.value_ua(stratum(degree), sides(name), unit, unit));
        cases.push((
            twin,
            same,
            alloc::vec![other_degree, other_sides],
            "a univalence",
        ));
        let [twin, same, other] =
            [0_usize, 0, 1].map(|summand| arena.value_injection(Summand::from(summand), unit));
        cases.push((twin, same, alloc::vec![other], "an injection"));
        let primitives = crate::primitive::PRELUDE;
        let [twin, same, other] = [0_usize, 0, 1].map(|row| {
            arena.alloc_value(Value::Primitive {
                primitive: primitives
                    .get(row)
                    .copied()
                    .expect("the prelude has two rows"),
                body: returned,
            })
        });
        cases.push((twin, same, alloc::vec![other], "a native function"));
        let [twin, same, other] =
            [Level::zero(), Level::zero(), one].map(|target| arena.value_lift(target, unit));
        cases.push((twin, same, alloc::vec![other], "a lift"));
        let [twin, same, other] =
            [0_u32, 0, 1].map(|mark| arena.value_mark(MarkIndex::from(mark), unit));
        cases.push((twin, same, alloc::vec![other], "a marked value"));

        for (twin, same, others, what) in cases {
            assert_eq!(
                CertificateEquality::Equal,
                equal_certificate_syntax(&arena, twin, same),
                "{what} equals its twin"
            );
            for other in others {
                assert_eq!(
                    CertificateEquality::Different,
                    equal_certificate_syntax(&arena, twin, other),
                    "{what} differs from one that changes a guarded part"
                );
            }
        }
    }

    #[test]
    fn each_computation_former_equals_its_twin_and_differs_where_its_guard_does()
    {
        use alloc::sync::Arc;

        use crate::control::EffectClause;
        use crate::effect::EffectName;
        use crate::effect::EffectOp;
        use crate::effect::EffectSig;
        use crate::effect::OperationName;
        use crate::memory::MemoryForm;
        use crate::primitive::Arguments;
        use crate::session::SessionAction;

        let mut arena = crate::CoreArena::new();
        let unit = arena.value_unit();
        let unit_type = arena.value_type_unit();
        let returned = arena.computation_return(unit);
        let motive = arena.comp_type_returner(unit_type);
        let label = |name| FieldLabel::from(alloc::string::String::from(name));
        let signature = |name| {
            EffectSig::new(EffectName::from(name), [
                EffectOp {
                    name: OperationName::from("ask"),
                    payload: unit_type,
                    reply: unit_type,
                },
                EffectOp {
                    name: OperationName::from("tell"),
                    payload: unit_type,
                    reply: unit_type,
                },
            ])
            .expect("two distinct operations")
        };
        let clause = |operation: &'static str| EffectClause {
            operation: OperationName::from(operation),
            body: returned,
        };
        let mut cases = Vec::new();

        let [twin, same, wider] = [1_usize, 1, 2]
            .map(|count| arena.computation_data_case(unit, motive, alloc::vec![returned; count]));
        cases.push((twin, same, alloc::vec![wider], "a nominal case"));
        let [twin, same, other] =
            ["a", "a", "b"].map(|name| arena.computation_record_projection(unit, label(name)));
        cases.push((twin, same, alloc::vec![other], "a record projection"));
        let [twin, same, other] = [0_usize, 0, 1]
            .map(|component| arena.computation_tuple_projection(unit, Component::from(component)));
        cases.push((twin, same, alloc::vec![other], "a tuple projection"));
        let [twin, same, other_operation, other_signature] =
            [("P", "ask"), ("P", "ask"), ("P", "tell"), ("Q", "ask")].map(|(name, operation)| {
                arena.computation_perform(signature(name), OperationName::from(operation), unit)
            });
        cases.push((
            twin,
            same,
            alloc::vec![other_operation, other_signature],
            "a perform",
        ));
        let [twin, same, other_operation, other_signature] =
            [("P", "ask"), ("P", "ask"), ("P", "tell"), ("Q", "ask")].map(|(name, operation)| {
                arena.computation_exercise(
                    unit,
                    signature(name),
                    OperationName::from(operation),
                    unit,
                )
            });
        cases.push((
            twin,
            same,
            alloc::vec![other_operation, other_signature],
            "an exercise",
        ));
        for scoped in [false, true] {
            let mut handler = |name, operations: &[&'static str]| {
                let clauses: Arc<[EffectClause]> = operations
                    .iter()
                    .map(|&operation| clause(operation))
                    .collect();
                if scoped {
                    arena.computation_scope(signature(name), returned, returned, clauses)
                }
                else {
                    arena.computation_handle(signature(name), returned, returned, clauses)
                }
            };
            let twin = handler("P", &["ask"]);
            let same = handler("P", &["ask"]);
            let others = alloc::vec![
                handler("P", &["ask", "tell"]),
                handler("Q", &["ask"]),
                handler("P", &["tell"]),
            ];
            cases.push((
                twin,
                same,
                others,
                if scoped { "a scope" } else { "a handler" },
            ));
        }
        let [twin, same, other] = [1_usize, 1, 2]
            .map(|arity| arena.computation_split(unit, ComponentCount::from(arity), returned));
        cases.push((twin, same, alloc::vec![other], "a split"));
        let [twin, same] = [(); 2]
            .map(|()| arena.computation_list_fold(unit_type, unit_type, unit, returned, returned));
        cases.push((twin, same, alloc::vec![], "a list fold"));
        let [twin, same] =
            [(); 2].map(|()| arena.computation_telescope_transport(motive, unit, unit, unit, unit));
        cases.push((twin, same, alloc::vec![], "a telescope transport"));
        let primitives = crate::primitive::PRELUDE;
        let row = |index: usize| {
            primitives
                .get(index)
                .copied()
                .expect("the prelude has two rows")
        };
        let [twin, same, other_row, other_count] = [
            (0_usize, Arguments::Unary(unit)),
            (0, Arguments::Unary(unit)),
            (1, Arguments::Unary(unit)),
            (0, Arguments::Binary([unit, unit])),
        ]
        .map(|(index, arguments)| arena.computation_primitive(row(index), arguments));
        cases.push((
            twin,
            same,
            alloc::vec![other_row, other_count],
            "a native operation",
        ));
        let [twin, same, other] = [
            FixpointEvidence::Partial,
            FixpointEvidence::Partial,
            FixpointEvidence::StructuralDescent,
        ]
        .map(|evidence| arena.computation_fixpoint(returned, evidence));
        cases.push((twin, same, alloc::vec![other], "a fixpoint"));
        let [twin, same] = [(); 2].map(|()| arena.computation_transport(unit, unit));
        cases.push((twin, same, alloc::vec![], "a transport"));
        let [twin, same, wider] = [1_usize, 1, 2]
            .map(|count| arena.computation_case(unit, &alloc::vec![returned; count]));
        cases.push((twin, same, alloc::vec![wider], "a sum case"));
        let [twin, same, other] =
            [0_u32, 0, 1].map(|hole| arena.computation_hole(HoleId::from(hole)));
        cases.push((twin, same, alloc::vec![other], "a hole"));
        let [twin, same, other] =
            [0_u32, 0, 1].map(|mark| arena.computation_mark(MarkIndex::from(mark), returned));
        cases.push((twin, same, alloc::vec![other], "a marked computation"));
        let send = |endpoint| SessionAction::Send {
            endpoint: DeBruijnIndex::from(endpoint),
            payload: unit,
        };
        let [twin, same, other] =
            [0_u32, 0, 1].map(|endpoint| arena.computation_session(send(endpoint)));
        cases.push((twin, same, alloc::vec![other], "a session action"));
        let hold = |grade| MemoryForm::Hold {
            value: unit,
            body: returned,
            grade,
        };
        let [twin, same] =
            [(); 2].map(|()| arena.computation_memory(hold(crate::memory::HoldGrade::Many)));
        let other = arena.computation_memory(MemoryForm::Abort {
            view: DeBruijnIndex::from(0_u32),
        });
        let graded = arena.computation_memory(hold(crate::memory::HoldGrade::One));
        cases.push((twin, same, alloc::vec![other, graded], "a memory form"));
        let migrate = |world: usize| crate::world::WorldForm::Migrate {
            world: crate::world::World::Declared(ConstantIndex::from(world)),
            body: returned,
        };
        let [twin, same, other] =
            [0_usize, 0, 1].map(|world| arena.computation_world(migrate(world)));
        cases.push((twin, same, alloc::vec![other], "a world form"));
        let unit_list = arena.value_type_list(unit_type);
        let unit_motive = arena.comp_type_returner(unit_list);
        let [twin, same] = [(); 2].map(|()| arena.computation_ascribe(returned, motive));
        let other = arena.computation_ascribe(returned, unit_motive);
        cases.push((twin, same, alloc::vec![other], "an ascription"));

        for (twin, same, others, what) in cases {
            let twin = arena.value_thunk(twin);
            let same = arena.value_thunk(same);
            assert_eq!(
                CertificateEquality::Equal,
                equal_certificate_syntax(&arena, twin, same),
                "{what} equals its twin"
            );
            for other in others {
                let other = arena.value_thunk(other);
                assert_eq!(
                    CertificateEquality::Different,
                    equal_certificate_syntax(&arena, twin, other),
                    "{what} differs from one that changes a guarded part"
                );
            }
        }
    }

    #[test]
    fn each_type_former_equals_its_twin_and_differs_where_its_guard_does()
    {
        let mut arena = crate::CoreArena::new();
        let unit = arena.value_unit();
        let unit_type = arena.value_type_unit();
        let label = |name| FieldLabel::from(alloc::string::String::from(name));
        let one = Level::zero().succ().expect("one is a level");
        let mut cases = Vec::new();

        let [twin, same, other_declaration, wider] = [(0_usize, 1_usize), (0, 1), (1, 1), (0, 2)]
            .map(|(declaration, count)| {
                arena.value_type_data(ConstantIndex::from(declaration), alloc::vec![unit; count])
            });
        cases.push((
            twin,
            same,
            alloc::vec![other_declaration, wider],
            "a nominal type",
        ));
        let [twin, same, other_label, wider] = [
            alloc::vec!["a"],
            alloc::vec!["a"],
            alloc::vec!["b"],
            alloc::vec!["a", "b"],
        ]
        .map(|labels| {
            arena.value_type_record(
                labels
                    .into_iter()
                    .map(|name| (label(name), unit_type))
                    .collect(),
            )
        });
        cases.push((twin, same, alloc::vec![other_label, wider], "a record type"));
        let [twin, same, wider] =
            [1_usize, 1, 2].map(|count| arena.value_type_product(&alloc::vec![unit_type; count]));
        cases.push((twin, same, alloc::vec![wider], "a product type"));
        let [twin, same, wider] =
            [1_usize, 1, 2].map(|count| arena.value_type_sum(&alloc::vec![unit_type; count]));
        cases.push((twin, same, alloc::vec![wider], "a sum type"));
        let [twin, same, other] = [Level::zero(), Level::zero(), one.clone()]
            .map(|target| arena.value_type_lift(unit_type, target));
        cases.push((twin, same, alloc::vec![other], "a lifted type"));
        let [twin, same, other] = [Level::zero(), Level::zero(), one.clone()]
            .map(|target| arena.value_type_element(unit, target));
        cases.push((twin, same, alloc::vec![other], "an element type"));
        let base = arena.value_type_data(ConstantIndex::from(0_usize), alloc::vec![]);
        let [twin, same, other] = [0_usize, 0, 1].map(|stage| {
            arena.value_type_staged(
                base,
                gandr_kernel_term::Stage::At(gandr_kernel_term::StageId::from(stage)),
            )
        });
        cases.push((twin, same, alloc::vec![other], "a staged type"));
        let session = {
            use crate::session::PayloadCount;
            use crate::session::PayloadSlot;
            use crate::session::Protocol;
            use crate::session::ProtocolState;
            use crate::session::ProtocolSyntax;
            let send = Protocol::new(
                alloc::vec![
                    ProtocolSyntax::Send {
                        payload: PayloadSlot::from(0_usize),
                        next: ProtocolState::from(1_usize),
                    },
                    ProtocolSyntax::End,
                ],
                ProtocolState::from(0_usize),
                PayloadCount::from(1_usize),
            )
            .expect("a send, then the end");
            crate::session::SessionType::new(
                alloc::sync::Arc::new(send),
                alloc::sync::Arc::from([unit_type]),
            )
            .expect("one payload for one slot")
        };
        let [twin, same] = [(); 2].map(|()| arena.value_type_session(session.clone()));
        let received = arena.value_type_session(session.dual());
        let ended = arena.value_type_session(
            session
                .at(crate::session::ProtocolState::from(1_usize))
                .expect("the end is a state"),
        );
        cases.push((twin, same, alloc::vec![received, ended], "a session type"));
        let returner = arena.comp_type_returner(unit_type);
        let arrows = [
            arena.comp_type_arrow(unit_type, returner),
            arena.comp_type_arrow(unit_type, returner),
            arena.comp_type_pi(unit_type, returner),
            arena.comp_type_pi(unit_type, returner),
        ];
        let mut thunked = |comp_type| arena.value_type_thunk(comp_type);
        let [arrow, same_arrow, pi, same_pi] = arrows.map(&mut thunked);
        cases.push((arrow, same_arrow, alloc::vec![], "an arrow"));
        cases.push((pi, same_pi, alloc::vec![], "a dependent arrow"));
        let elements =
            [Level::zero(), Level::zero(), one].map(|target| arena.comp_type_element(unit, target));
        let [twin, same, other] = elements.map(|element| arena.value_type_thunk(element));
        cases.push((twin, same, alloc::vec![other], "a computation element type"));
        let unknowns = [(); 2].map(|()| arena.comp_type_unknown());
        let [twin, same] = unknowns.map(|unknown| arena.value_type_thunk(unknown));
        cases.push((twin, same, alloc::vec![], "an unknown computation type"));

        for (twin, same, others, what) in cases {
            assert_eq!(
                CertificateEquality::Equal,
                equal_type_syntax(&arena, twin, same),
                "{what} equals its twin"
            );
            for other in others {
                assert_eq!(
                    CertificateEquality::Different,
                    equal_type_syntax(&arena, twin, other),
                    "{what} differs from one that changes a guarded part"
                );
            }
        }
    }
}

/// A nominal declaration's parameter telescope, index telescope, constructor
/// table with the index each constructor stands at, universe and the rules
/// presenting its terms.
///
/// Parameter classifiers are scoped under their predecessors, and index
/// classifiers under the parameters and the indices before them. Constructor
/// fields are scoped under all parameters and then the fields before them in
/// their constructor, which a later field may name; a constructor's result
/// indices under the parameters and all its fields.
/// Admission, not this container, verifies those scopes, the universe bound
/// and that every rule is constructor-headed over the table.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct DataSignature
{
    /// Parameter classifiers in telescope order.
    parameters: Vec<ValueTypeId>,
    /// Index classifiers in telescope order; none for a parameterised type.
    indices: Vec<ValueTypeId>,
    /// Constructor fields in tag order.
    constructors: Vec<Vec<ValueTypeId>>,
    /// Each constructor's result indices in tag order; none for a
    /// parameterised type.
    results: Vec<Vec<ValueId>>,
    /// The positive universe bounding every constructor field.
    kind: ValueTypeId,
    /// The rules rewriting the type's constructor terms; none for a free type.
    presentation: gandr_kernel_term::Presentation,
}

impl DataSignature
{
    /// Construct a free signature whose formation remains the checker's
    /// obligation; [`Self::presented`] attaches rules and [`Self::indexed`]
    /// indices.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub fn new(
        parameters: Vec<ValueTypeId>,
        constructors: Vec<Vec<ValueTypeId>>,
        kind: ValueTypeId,
    ) -> Self
    {
        Self {
            parameters,
            indices: Vec::new(),
            constructors,
            results: Vec::new(),
            kind,
            presentation: gandr_kernel_term::Presentation::default(),
        }
    }

    /// This signature indexed by `indices`, each constructor standing at its
    /// row of `results`; its parameters, constructors and universe unchanged.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub fn indexed(
        self,
        indices: Vec<ValueTypeId>,
        results: Vec<Vec<ValueId>>,
    ) -> Self
    {
        Self {
            indices,
            results,
            ..self
        }
    }

    /// Index classifiers in telescope order.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub fn indices(&self) -> &[ValueTypeId]
    {
        &self.indices
    }

    /// Each constructor's result indices in tag order.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub fn results(&self) -> &[Vec<ValueId>]
    {
        &self.results
    }

    /// The arguments an application of the family carries: its parameters,
    /// then its indices.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub fn arity(&self) -> crate::description::TypeArity
    {
        crate::description::TypeArity(self.parameters.len().saturating_add(self.indices.len()))
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

    /// The rules rewriting the type's constructor terms, in written order:
    /// none for a free type.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub const fn presentation(&self) -> &gandr_kernel_term::Presentation
    {
        &self.presentation
    }

    /// This signature presenting its terms by `presentation`, its parameters,
    /// constructors and universe unchanged.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub fn presented(
        self,
        presentation: gandr_kernel_term::Presentation,
    ) -> Self
    {
        Self {
            presentation,
            ..self
        }
    }
}

/// A nominal codata declaration's parameter telescope, its observations and
/// the computation universe bounding them.
///
/// Parameter classifiers are scoped under their predecessors; each
/// observation is a computation type scoped under all parameters, which may
/// name the declaration itself at its result. Admission, not this container,
/// verifies those scopes, the universe bound and that every self reference
/// stands at an observation's result.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct CodataSignature
{
    /// Parameter classifiers in telescope order.
    parameters: Vec<ValueTypeId>,
    /// The observations, in written order.
    observations: Vec<CompTypeId>,
    /// The computation universe bounding every observation.
    kind: ValueTypeId,
}

impl CodataSignature
{
    /// Construct a signature whose formation remains the checker's
    /// obligation.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub const fn new(
        parameters: Vec<ValueTypeId>,
        observations: Vec<CompTypeId>,
        kind: ValueTypeId,
    ) -> Self
    {
        Self {
            parameters,
            observations,
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

    /// The observations, in written order.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub fn observations(&self) -> &[CompTypeId]
    {
        &self.observations
    }

    /// The computation universe bounding the observations.
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
