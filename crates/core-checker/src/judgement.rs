//! The judgement: four directed faces over one machine, which also runs type
//! formation.
//!
//! # The former decides the mode
//!
//! Every term former but the bind and the pair has one mode. Leaves and
//! eliminations synthesise — their type is read out of the context, the
//! signature table, an atom, the type they quote, or the type of the term
//! they eliminate — and introductions check against a type handed in,
//! because nothing in an introduction alone fixes its type:
//!
//! |Former|Mode|Rule|
//! |---|---|---|
//! |variable|synthesise|the type its binder declared, relocated past the binders opened since: a root update the value bridge reads through, settled where any other rule reads it|
//! |constant|synthesise|the type its declaration supplied|
//! |unit, integer, string and character literal|synthesise|the atom|
//! |quote `⌜A⌝`, `⌜C⌝`|synthesise|the quoted type is formed; the quote has the universe of its family's sort at the type's level|
//! |thunk|check against `U C`|its body checks against `C`|
//! |force|synthesise|the forced value synthesises `U C`; the force has `C`|
//! |application|synthesise|the head synthesises `A → C` or `(x : A) → C`, the argument checks against `A`; the application has `C`, instantiated at the argument for the dependent arrow; an argument at a static Pi must not normalize away|
//! |bind|either|the bound computation synthesises `F A`; opens a binder of `A`; the body is judged in the bind's own mode, and the bind has what the body has, lowered out of the binder|
//! |pair|either|synthesising, each component synthesises and the pair has their eager product; checking against `A × B`, each component checks against its factor; checking against `Σ (x : A). B`, the first checks against `A` and the second against `B` at the first; checking against a path between dependent pairs or between tuples, it checks against that path's fibre (§ Element identity)|
//! |lambda|check against `A → C` or `(x : A) → C`|opens a binder of `A`; the body checks against `C`|
//! |static lambda|check against a static Pi `K ⇒ J`|opens a binder of `K`; the body checks against `J`|
//! |static application|synthesise|the head synthesises one static Pi per argument; each argument checks against its Pi's domain; the application has the last codomain|
//! |dependent split|synthesise|the scrutinee synthesises `Σ (x : A). B`; the motive `C` forms under a binder of the Σ; the body checks against `C` at the pair of its two binders, `x : A` outermost; the split has `C` at the scrutinee|
//! |tuple projection|synthesise|the tuple synthesises a product or a Σ; at a Σ the first projection has `A` and the second `B` at the first projection|
//! |record update `#{b \| l = a, …}`|synthesise|the base synthesises a record, a computation written there running first and read at what it returns; the overlay's fields synthesise; the update has the base's record with each written label at its written type — a label the base lacks extends it, one at another type retypes it — and the base's other labels kept|
//! |return|check against `F A`, or synthesise|checked, the value checks against `A`; synthesised, the value synthesises `A` and the return the pure returner of `A`|
//!
//! A bind and a pair are the formers of either mode, and so is a return. A
//! bind eliminates the returner its bound computation synthesises, so that half
//! synthesises, and it hands its type through from its body, so the body is
//! judged in whichever mode the bind was asked for. A return synthesises when
//! its value does: the value's type is the one it synthesised, and a return
//! performs nothing, so its row is the empty one, which every row it meets
//! subsumes. A return whose value only checks, a thunk or a lambda, is refused
//! at that value rather than given a guessed type. A body type that mentions
//! the bound name is refused as a dependent bind: the binder is opaque to
//! types, so that type has no reading outside it. A pair synthesises when every
//! component does and checks component-wise otherwise, so a thunk stands in a
//! pair checked against a product.
//!
//! A synthesising term in checking position synthesises, then its type crosses
//! the conversion boundary to the expected type; that is the only place a
//! type meets a type. A checking form in synthesis position is refused, naming
//! the form: the judgement never guesses a type an introduction did not
//! carry.
//!
//! Constructors, nominal cases, and record and tuple projections synthesise; a
//! record is answered in both directions, as `judgement::native` states. The
//! direction is a crate-local type declared as the judgement's direction, and
//! the `mode_dispatch_wildcard` lint from the workspace's policy library
//! refuses any match on it, or on a parameter declared to carry the expected
//! type, that answers a case through a fallback arm, so a rule added in one
//! direction and forgotten in the other does not compile. The alternatives were
//! a mode register with a type-directed default; the same constraint as a
//! review convention; and a workflow gate matching source text, which cannot
//! tell a match on a direction from any other match. The choice reverses when
//! the judgement is restated so that a term's syntactic class is itself a type,
//! at which point the arm the lint looks for cannot be written.
//!
//! The bind is answered in both directions because its type is its body's: a
//! bind fixed to synthesis would refuse every block that ends in a return of a
//! value that only checks, and a bind fixed to checking would refuse a block
//! standing where a type is wanted from it, as the head of an application.
//!
//! The pair is answered in both directions for the same reason at its
//! components: a pair fixed to checking would refuse every unsigned definition
//! of a pair, and one fixed to synthesis would refuse a pair holding a thunk,
//! which only checks. Against a dependent pair it only checks: its second
//! factor reads the first component, which no synthesis of the components
//! fixes, so a pair in synthesis position is the product of its components
//! and never a Σ. The alternative was the checking-only pair of a
//! bidirectional system, which refuses every unsigned definition of a
//! product; it reverses with a metavariable for the second factor, which
//! would let a pair synthesise the Σ its use solves.
//!
//! # Static operators
//!
//! A static lambda checks against a static Pi, its body against the codomain
//! beneath a binder of the domain. A static application is judged as a spine:
//! its root head synthesises, and each argument, first to last, checks against
//! the domain of the next static Pi the head's type opens, so the application
//! has the last codomain. A spine longer than the head's static Pis is
//! [`CheckRefusal::FamilyArity`], naming the Pis opened and the arguments
//! given; an argument whose classifier does not cross to its domain is
//! [`CheckRefusal::FamilyArgumentClassifier`], naming its position and both
//! classifiers, so a universe of the wrong sort or level reads as a mistake in
//! the family's use, not an anonymous mismatch. A saturated instance of a
//! static definition unfolds as a code constant does, one certified δβ-step at
//! a time, and two rigid instances convert when their heads and arguments do.
//! The alternatives were the plain `TypeMismatch` at the argument, which loses
//! which argument of which family failed, and a classifier check at formation
//! only, which misses an application whose head is a variable.
//!
//! A static lambda is not a value the kernel types: the kernel's terms have no
//! static lambda, and every static application reduces before the kernel sees
//! it. So a static lambda, a static definition, or an instance of one short of
//! saturation, handed to a static parameter, normalizes away with the
//! application that receives it; handed to a dynamic application — a
//! computation applied at a value whose type is a static Pi — it would survive
//! into the kernel's terms, and it is refused as
//! [`CheckRefusal::StaticLambdaArgument`] at the argument. An opaque operator,
//! the one a hole owes, is rigid and crosses as a kernel constant, so it
//! passes. `a_static_lambda_at_a_static_parameter_normalizes_away` and
//! `a_static_lambda_at_a_dynamic_parameter_is_refused_by_name` assert the two
//! sides. The alternatives were defunctionalising each static lambda into a
//! kernel constant at its use, which hands the kernel an operator it can only
//! treat as opaque and certifies nothing about it, and a static lambda in the
//! kernel, which widens the trusted base by a binder and its β-rule for terms
//! that normalize away anyway. The refusal reverses if the kernel gains static
//! abstraction, at which point a static lambda crosses at a dynamic parameter
//! as itself.
//!
//! # Types are read at their weak head
//!
//! Every rule that reads the former of a type — a thunk checked against it, a
//! head applied at it, a returner bound — reads it at its weak head first, so
//! `El Num` for `def Num : Type = U (F Integer)` is a thunk type to a thunk.
//! The unfolding is the context's: the normaliser's conversion certifies each
//! step and the constant is logged as consulted.
//!
//! # Formation is goals of the same machine
//!
//! A type is formed by goals beside the term goals: a decode `El c` asks for
//! the synthesis of `c`, which may itself form a quoted type, and a dependent
//! arrow forms its codomain under a binder of its domain. Running both in one
//! machine keeps the judgement free of recursion between the two and charges
//! both to one allowance.
//!
//! # One machine, no recursion
//!
//! The four faces and formation all run [`Machine`]: an explicit goal and a
//! stack of frames, one step per transition, charged against the context's
//! allowance. A term as deep as memory holds is judged without a native
//! stack, and the allowance bounds the run whatever sharing the term has.
//!
//! # A shared subterm is judged per occurrence
//!
//! The machine keeps no memo: a subterm reached twice is judged twice. The
//! fragment's terms are what a lowering produced from source text, whose
//! sharing is the author's repetition, and the allowance bounds the rest. The
//! alternative is a check memo keyed by node and context, the seam
//! `gandr-kernel-check-memo` provides; it becomes worth its bookkeeping when a
//! producer starts sharing aggressively, which an elaborator's output will.
//!
//! # A hole and a mark are judged without their contents
//!
//! A term hole checks against any type and synthesises the unknown type, as
//! Hazelnut's empty hole does (Omar et al., POPL 2017,
//! doi:10.1145/3009837.3009900). A mark is Hazelnut's non-empty hole: it
//! records a refusal its body already met, so its body is not judged again,
//! and it checks and synthesises as a hole does. A rule that demands a
//! former of an expected or a synthesised type reads it through the matched
//! operations of `gandr_core_term::hole`: the unknown type matches every
//! former with unknown components, so an introduction checked against it and
//! an elimination of a term that synthesised it both go on, and conversion
//! treats the unknown as consistent with every type. A path's endpoints and a
//! nominal type's constructors are read off the type itself, so a transport
//! or a native case over the unknown type is refused, and a total elaboration
//! marks it.
//!
//! Consistency is not transitive, and nothing here composes it: each crossing
//! compares one synthesised type with one expected type. The alternatives were
//! a fresh metavariable per hole, which needs a solver the fragment does not
//! have, and consistency with runtime casts, which the kernel would have to
//! trust; the unknown type never reaches the kernel, whose bridge refuses it.
//! The choice reverses when an inference feature needs a hole's type to drive a
//! solution: the hole then gets a metavariable with provenance, and the unknown
//! type becomes its unsolved state.
//!
//! The unknown type forms at the lowest level: a judgement that asks its
//! universe gets the value universe at level zero. Each limit on what the
//! unknown type can do — a transport, a native data case or a record projection
//! over it, a hole beneath an index's root — reverses with the consumer that
//! needs it: a typed transport, data case or projection over an unfinished
//! scrutinee. Witnesses:
//! `judgement::tests::a_hole_synthesises_the_unknown_type_and_checks_against_any`,
//! `judgement::tests::an_introduction_against_the_unknown_type_checks_its_parts`,
//! `conversion::tests::the_unknown_type_is_consistent_beside_a_differing_former`
//! and `view::tests::the_unknown_type_and_the_decode_of_a_hole_view_alike`.
//!
//! # A refusal leaves the context as it found it
//!
//! A refused run closes every binder it opened before it returns, so the
//! next judgement in the same context starts where this one did.
//!
//! # The dependent arrow, and the bind that is not
//!
//! A lambda checked against a dependent arrow opens the binder and checks its
//! body against the codomain as written; one checked against a plain arrow
//! shifts the codomain past the new binder. An application of a dependent arrow
//! synthesises the codomain instantiated at the argument — at the argument as
//! the recorded lift wrote it when the argument crossed a value bridge one
//! universe up — so the type the caller sees names the type the caller passed.
//!
//! A bind is not dependent. Its continuation is judged under a binder of the
//! returned value, and when the bind synthesises, the continuation's type is
//! strengthened out from under that binder; a type that mentions the bound
//! value is `DependentBind`. A returned value is a computation's result, and a
//! type that names it would depend on an effect having run, which is the
//! substitution the fire triangle forbids alongside dependent elimination
//! (Pédrot and Tabareau, POPL 2020, doi:10.1145/3371126). The alternatives were
//! a dependent bind, sound only for a thunkable continuation, and dependency on
//! computations, which needs the linearity discipline the core does not have.
//! Either reverses only with that discipline.
//!
//! # A split takes its body's type, and a split under a motive its motive's
//!
//! A split's scrutinee synthesises a product of exactly the split's arity, the
//! unit for a split of none, and its body is judged under one binder per
//! component, component zero outermost, each typed by its component shifted
//! past the binders before it. Checked, the body checks against the expected
//! type shifted past all of them. Synthesised, the body's type is strengthened
//! out from under them, as a bind's is, and a type that reads a component is
//! the bind's refusal, `DependentBind`, at the split. A split of another arity
//! or of anything but a product is a `ShapeMismatch` wanting a product, at the
//! scrutinee. A statement `e;` is a split of its unit result, so it synthesises
//! wherever what follows it does.
//! `judgement::tests::a_split_binds_every_component_of_its_product` and
//! `judgement::tests::a_split_synthesises_its_body_type_outside_its_binders`
//! assert each arm.
//!
//! A split under a motive is the dependent pair's eliminator. Its scrutinee
//! synthesises `Σ (x : A). B` and its arity is two; the motive `C`, written
//! under a binder of the Σ, forms; the body checks against `C` at the pair of
//! its two binders, `x : A` and then `y : B`; and the split synthesises `C`
//! at the scrutinee, so its answer may read what it eliminates. Any other
//! scrutinee, or another arity, is a `ShapeMismatch` wanting a dependent
//! pair; a split without a motive at a Σ is the shape mismatch wanting a
//! product, since its answer could not read the pair.
//! `judgement::tests::a_dependent_split_synthesises_its_motive_at_the_scrutinee`
//! asserts each arm.
//!
//! - Alternatives: projections alone, which eliminate a Σ but leave a match
//!   whose answer reads the scrutinee unwritable; a split that infers its
//!   motive from the expected type, which is higher-order unification.
//! - Reversal: a motive inferred where the expected type abstracts the
//!   scrutinee syntactically, as the lowering does, would let the motive go
//!   unwritten here too.
//!
//! # Effects and control
//!
//! A perform checks its payload and synthesises its reply under its singleton
//! interface row. A handler covers that interface exactly once and checks every
//! branch against its answer, retaining residual effects. Shared interface
//! names require invariant operation types. Effectful bind needs a returner
//! continuation; pure bind may continue with a lambda.
//!
//! Stack Apply instantiates a dependent codomain; Bind unions rows and
//! strengthens its result, refusing escaping type codes as `DependentStack`;
//! Project selects a lazy-product component. Reset supplies Shift's answer,
//! weakened through intervening binders. Stack literals, handlers, resets,
//! shifts and lazy products check rather than synthesise. A handler's subject
//! and a Bind frame's body synthesise, so a `return` there synthesises its
//! value. Returner rows and stacks subsume by the variance `conversion`
//! states.
//!
//! Against the unknown type, a stack literal runs its frames over unknown
//! endpoints, a lazy product checks its components against unknowns, and a List
//! reads an unknown element. A handler checked against the unknown answer reads
//! it through the matched returner: the residual is absorbed and each
//! resumption consumes the reply under the empty row. A resumption of a hole
//! infers the unknown type, so a hole in stack position stays local.
//!
//! **Choice.** Bidirectional rules and named refusals, not answer-type
//! inference or a row solver. **Reversal.** An explicit answer-polymorphic
//! contract. Control formers and nonempty rows never become assumed
//! declarations at pure readmission:
//! `bridge::tests::effectful_declarations_are_refused_by_name_at_the_pure_boundary`.
//!
//! Witnesses in `judgement::tests`: `pure_bind_into_lambda_is_unchanged`,
//! `effectful_bind_into_lambda_is_shape_mismatch`, `bind_unions_effect_rows`,
//! `check_mode_bind_subsumes_the_accumulated_row`,
//! `check_mode_bind_accepts_a_contained_row`,
//! `host_operations_check_payloads_and_retain_effects`,
//! `handlers_discharge_only_their_own_interface`,
//! `handle_against_a_non_returner_is_stuck`,
//! `handle_of_a_non_returner_scrutinee_is_a_shape_mismatch`,
//! `empty_signature_handler_finishes_after_the_return_clause`,
//! `handle_against_unknown_answer`,
//! `control_rules_preserve_rows_scopes_and_shapes`,
//! `reset_answers_are_weakened_through_intervening_binders`,
//! `a_stack_bind_cannot_export_its_local_type_code`,
//! `stack_bind_accumulates_input_and_body_rows`,
//! `reify_empty_stack_is_identity`, `reify_delivered_answer_subsumes_up`,
//! `reify_delivered_answer_cannot_drop_a_row`,
//! `reify_against_non_stack_type_is_stuck`,
//! `reify_interior_bind_frame_threads_the_accumulated_row`,
//! `resume_of_a_non_stack_is_a_shape_mismatch`,
//! `resume_delivering_a_row_cannot_drop_it`,
//! `resume_delivered_answer_subsumes_up`, `resume_of_a_hole_infers_unknown`,
//! `reset_is_transparent_on_the_type`,
//! `shift_binds_the_continuation_at_the_captured_type` and
//! `an_introduction_against_the_unknown_type_checks_its_parts`.
//!
//! # Native universe paths
//!
//! `PathUniverse`, `PathRefl`, `PathEquiv`, `PathProduct` and `Transport` are
//! programmatic core forms. `Path_U` is a type of certified equivalences, not
//! equality decided by running its maps. Endpoint codes must be closed
//! first-order quotes; map types are opposite CBPV arrows. `PathCode`
//! classifies a malformed endpoint as malformed source. The judgement checks
//! shape and typing but does not certify round-trip evidence: export remaps
//! every native child and carries candidate dialogues unchanged to ordinary
//! kernel admission.
//!
//! `bridge::tests::native_path_module_round_trips` exports all five forms,
//! persists and imports four declarations, then replays imported product
//! transport. Of these forms the surface writes only the product,
//! `pathProduct(p, q)`, whose rule in [`crate::product`] also reads a
//! component at the universe's element identity and elaborates such a product
//! to the native one. Beside it, the surface writes a universe equivalence
//! `equiv(f, g)`, which the rule in [`crate::equiv`] decides by computation
//! and the bridge erases to `PathEquiv` with the dialogues it recorded, and
//! univalence at a stratum `ua[n, k](a, b, f, g)`, which [`crate::ua`]
//! derives and the bridge erases to the path product of one `PathEquiv` per
//! corolla. The directed family's statements — `sim`, `forward`, `arrow` and
//! `flowProduct` at `Flow(Type, A, B)` — are the rules of [`crate::flow`],
//! [`crate::forward`] and [`crate::product`]. A bridge `Bridge(A, a, b)` is
//! read by the bridge fold of [`crate::relatedness`]; higher fields and
//! guarded List inhabitants stay at their kernel rule-language boundaries;
//! function extensionality is the element-identity rule below.
//!
//! **Choice.** Preserve untrusted native evidence across the export boundary
//! instead of treating successful frontend checking as certification.
//! `CheckBudget` bounds the frontend machine; the kernel's formation and
//! replay allowances stay separate, and their exhaustion is not a negative
//! equality verdict. **Reversal.** Broader endpoint codes or a source notation
//! must acquire their own typing and kernel replay rules before this boundary
//! widens.
//!
//! # Element identity
//!
//! `Path(A, a, b)` forms when its carrier forms and both endpoints check
//! against it; it stands at the carrier's level. Reflexivity `here(a)`
//! synthesises `Path(A, a, a)` from the type its point synthesises, and
//! checks against `Path(A, l, r)` when its point checks against `A` and is
//! both `l` and `r`: the same syntax with evidence erased, or convertible
//! with every definition unfolded and the free binders read as rigid
//! variables. Anything else is [`CheckRefusal::EndpointMismatch`], naming the
//! point and both endpoints. A conversion the machine cannot decide — a
//! native operation over a variable, `0 + x` against `x` — is a mismatch too:
//! the rule admits what it shows and refutes nothing it cannot. The refusal
//! carries whether the machine spent its step budget before deciding
//! ([`crate::EndpointMiss`]), so a computation too long for the budget is not
//! reported as endpoints apart.
//!
//! The conversion runs with a compound endpoint held at the definition it
//! calls, so the machine unfolds it as a recorded decision rather than inside
//! evaluation, and the trace from the point to each endpoint is kept at the
//! `here` ([`crate::code::Reflexivity`]). The bridge carries both dialogues on
//! the kernel's `here`, and the kernel replays them: every δ-step an endpoint
//! needs, under a binder or not, is one the dialogue names.
//!
//! A compound endpoint is a computation standing where an endpoint is read,
//! taken as the value it returns. It synthesises the result of the pure
//! returner its computation synthesises, and is
//! [`CheckRefusal::CompoundEndpoint`] when that is no returner or performs an
//! effect: an effect has no value to compare.
//!
//! Transport `tr(P, p, x)` synthesises. The path synthesises `Path(A, a, b)`,
//! the motive forms under a binder of `A`, the operand checks against `P[a]`,
//! and the transport has `F P[b]`. The motive is first order: one value type
//! under one binder. A motive over a dependent arrow, `y. U((x : B[y]) →
//! C[x, y])`, transports the argument back along the path and the result
//! forward over both binders; that is the dependent-arrow extension, and this
//! rule does not take it.
//!
//! **A path between dependent pairs is a pair of paths.** A pair checked at
//! `Path(Σ (x : A). B, l, r)` checks at the fibre `Σ (p : Path(A, l₀, r₀)).
//! Path(B[r₀], ⟨tr(x. B, p, l₁)⟩, r₁)`: a path between the first components
//! and, over it, a path from the left second component transported along it
//! to the right one. `l₀` and `l₁` are the components of a written pair and
//! `⟨l.0⟩`, `⟨l.1⟩` of any other endpoint, and so for `r`. The kernel computes
//! the same fibre, so a judged path readmits. Transport along such a path is
//! the rule above: it reduces on reflexivity and in a motive that ignores its
//! binder, and stays neutral otherwise.
//! `judgement::tests::a_pair_of_paths_checks_at_the_identity_of_a_dependent_pair`
//! and
//! `judgement::tests::a_transport_along_a_path_at_a_dependent_pair_reads_its_motive_at_the_target`
//! witness both.
//!
//! - Alternatives: the identity at a Σ as its own neutral fibre, which leaves a
//!   path between pairs unwritable but by reflexivity; a fibre over the product
//!   of the two components' paths, which is wrong once the second factor reads
//!   the first.
//! - Reversal: a fold clause for the Σ in the identity recursion would compute
//!   this fibre where the rule states it, and reduce transport along a path
//!   that is not reflexivity componentwise.
//!
//! **A path between tuples is a tuple of paths.** A tuple checked at
//! `Path(A₀ × … × Aₙ, l, r)` checks at `Path(A₀, l₀, r₀) × … × Path(Aₙ, lₙ,
//! rₙ)`, its components read as the Σ rule reads them; a tuple transported at
//! a product motive, `⟨tr(x. A₀ × … × Aₙ, p, v)⟩`, is read as its components'
//! transports `⟨tr(x. Aᵢ, p, vᵢ)⟩`. An endpoint unfolds only through declared
//! constants, as the kernel reads it, so the fibre is the kernel's and the
//! dialogues recorded at its endpoints replay there.
//! `judgement::tests::a_tuple_of_paths_checks_at_the_identity_of_a_product`
//! witnesses it. At the empty product the fibre is the empty tuple of paths:
//! `()` checks at `Path(Unit, l, r)` between any two points; the law of the
//! lawful atom below is one.
//!
//! **Identity at an open type is a neutral fibre.** A carrier that mentions a
//! variable bound outside it — the decode of a type variable, a data type at a
//! variable index — or exposes no structure — the decode of a code no quote
//! reaches, the unknown type — has no fibre the identity recursion can read,
//! so the path type is its own fibre there, as a higher observational type
//! theory leaves the identity of a neutral type. It forms, reflexivity
//! synthesises and checks at it by the endpoint rule above, transport along it
//! is stuck except on reflexivity, where it reduces, and two such path types
//! convert structurally. The kernel reads the same neutral fibre, so a judged
//! identity readmits. A sealed atom past its seal is the fragment's other open
//! type and its identity is the same neutral fibre, unless its interface
//! states a law: then an introduction at `Path(atom, l, r)` checks at the
//! relation between its endpoints, `El(⟨relation l r⟩)`, the atom's identity
//! system, and the kernel reads the same fibre
//! (`bridge::tests::a_lawful_atom_reads_its_relation_as_its_identity_in_both_checkers`).
//! Inside its seal the weak head reads its representation, whose fibre the
//! recursion computes. The alternatives were refusing the path type and
//! reflexivity at such a carrier, which left every law over an abstract
//! carrier unstatable, and refusing it at readmission alone, which let a
//! reflexivity inside a body reach the kernel. Reversal: a recursion clause
//! for type variables computes the fibre this leaves neutral.
//!
//! **Function extensionality is decided by computation.** `funext(f, g)`
//! synthesises `Path(U (A → F B), f, g)` for closed functions over a
//! first-order domain and result when, at every input of the domain's
//! coverage, both return one value with every admitted definition unfolded
//! ([`crate::funext`] states the rule, its fragment and its refusals). The
//! decision is recorded per input with the machine's traces, and the bridge
//! hands them to the kernel as a higher evaluation, which replays them.
//!
//! K is not derivable: no rule matches a path against reflexivity, and the
//! lowering refuses a `here` pattern before a term reaches the judgement, as
//! it refuses an endpoint whose head names nothing.
//!
//! **Choice.** One eliminator, typed in its written motive, with `back`,
//! `then` and `cong` arriving as transports. The alternatives were a
//! primitive `J`, whose motive ranges over the path as well as its endpoint,
//! and a typing rule per derived operation, three places for their laws to
//! drift. **Reversal.** The dependent-arrow extension and identity between
//! identities each add a rule beside this one rather than widening it.

use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::BinderDepth;
use gandr_core_term::Binders;
use gandr_core_term::CompType;
use gandr_core_term::CompTypeId;
use gandr_core_term::ComponentCount;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::ContextError;
use gandr_core_term::Relocated;
use gandr_core_term::Sort;
use gandr_core_term::SplitMotive;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::effect::capability::CapabilityGrade;
use gandr_core_term::effect::capability::Region;
use gandr_core_term::effect::capability::RegionDepth;
use gandr_core_term::hole::CodomainScope;
use gandr_core_term::hole::Components;
use gandr_core_term::hole::HoleId;
use gandr_core_term::hole::HoleOrigin;
use gandr_core_term::hole::matched_function;
use gandr_core_term::hole::matched_list;
use gandr_core_term::hole::matched_product;
use gandr_core_term::hole::matched_returner;
use gandr_core_term::hole::matched_stack;
use gandr_core_term::hole::matched_static_pi;
use gandr_core_term::hole::matched_sum;
use gandr_core_term::hole::matched_thunk;
use gandr_core_term::hole::matched_with;
use gandr_core_term::hole::matching;
use gandr_core_term::instantiate_comp_type;
use gandr_core_term::instantiate_comp_type_at_call;
use gandr_core_term::instantiate_value_type;
use gandr_core_term::instantiate_value_type_under;
use gandr_core_term::session::SessionAction;
use gandr_core_term::shift_comp_type;
use gandr_core_term::shift_value;
use gandr_core_term::shift_value_type;
use gandr_core_term::shift_value_type_under;
use gandr_core_term::strengthen_comp_type;
use gandr_kernel_core::stage_order::Fit;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FieldCount;
use gandr_kernel_term::FixpointEvidence;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::StagedPosition;
use quenchant_shape::shape::Maybe;

use crate::context::Atom;
use crate::context::CheckingContext;
use crate::conversion::ConversionCount;
use crate::conversion::comp_bridge;
use crate::conversion::decode_bridge;
use crate::conversion::value_bridge;
use crate::failure::Failure;
use crate::failure::FoldPremise;
use crate::failure::FrameRole;
use crate::failure::Obligation;
use crate::failure::Pursuit;
use crate::failure::Stage;
use crate::failure::judged;
use crate::formation::FormedCompType;
use crate::formation::FormedValueType;
use crate::formation::level_of;
use crate::nested::Nesting;
use crate::refusal::ArgumentPosition;
use crate::refusal::CheckRefusal;
use crate::refusal::CheckingForm;
use crate::refusal::CoreNode;
use crate::refusal::ExpectedShape;
use crate::refusal::Mismatch;
use crate::refusal::StaticArity;
use crate::refusal::TacticFault;
use crate::refusal::TermNode;
use crate::refusal::TypeNode;
use crate::refusal::UnadmittedFormer;
use crate::view::CompTypeView;
use crate::view::ValueTypeView;
use crate::view::comp_type_view;
use crate::view::value_type_view;

mod access;

mod elaboration;

mod native;

mod session;

mod worlds;

use self::elaboration::Anchor;
pub use self::elaboration::Elaboration;
pub use self::elaboration::Formed;
pub use self::elaboration::Kept;
pub use self::elaboration::MarkEntry;
use self::elaboration::Marking;
pub use self::elaboration::Typing;
pub use self::elaboration::Typings;
pub use self::elaboration::elaborate_comp;
pub use self::elaboration::elaborate_value;
pub use self::elaboration::type_value;
use self::session::Sessions;

/// The direction a judgement runs in.
///
/// # Judgement
/// - direction: synthesis hands the term's type out; checking takes the
///   expected type in. A dispatch on it names both, so a rule added in one mode
///   is a compile error in every dispatch that forgot the other.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Direction<Expected>
{
    /// The term's type is read off the term.
    Synthesise,
    /// The term is checked against the type held.
    Check(Expected),
}

/// A type a judgement synthesised, beside the evidence of how it got there.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Synthesised<Type>
{
    /// The type.
    produced: Type,
    /// The conversions the run made.
    conversions: ConversionCount,
}

impl<Type: Copy> Synthesised<Type>
{
    /// The type synthesised.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn produced(&self) -> Type
    {
        self.produced
    }

    /// How many times the run crossed the conversion boundary.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn conversions(&self) -> ConversionCount
    {
        self.conversions
    }
}

/// The evidence a check succeeded with.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Checked
{
    /// The conversions the run made.
    conversions: ConversionCount,
}

impl Checked
{
    /// How many times the run crossed the conversion boundary.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn conversions(&self) -> ConversionCount
    {
        self.conversions
    }
}

/// Synthesise the type of `value`.
///
/// # Specification
/// - requires: `value` is closed over the context's binders, which are empty
///   between judgements.
/// - ensures: the formed type `value` has by the synthesis rule of its former,
///   the checks of its subterms done by their rules.
/// - provides: the conversions the run made, as [`Synthesised::conversions`].
/// - fails: [`CheckRefusal::NotSynthesisable`] for a thunk; otherwise any
///   refusal a reached rule gives — see the vocabulary.
/// - panics: none.
/// - intension: the conversion count is the declared projection of the run's
///   crossings of the boundary.
///
/// # Errors
/// - [`CheckRefusal`] — the term has no type in the fragment, or the run hit
///   the allowance or a dangling id.
///
/// # Adequacy
/// - hypothesis: L3 — the decision surface is the per-former rule table in
///   synthesis mode, separated by one term of every value former, each asserted
///   to synthesise its exact type or refuse with its exact refusal; the free
///   generator pins the faces against each other by property.
/// - witness: `judgement::tests::every_value_former_is_answered_in_both_modes`
/// - witness: `judgement::tests::the_faces_agree_on_free_terms`
/// - witness: `judgement::tests::well_typed_terms_synthesise_and_check_their_type`
#[spec(
    captures: depth = context.depth(Zone::Intuitionistic),
    ensures: |ret| context.depth(Zone::Intuitionistic) == depth && match ret {
        | Ok(synthesised) => context.arena().value_type(synthesised.produced().id()).is_some()
            && usize::from(synthesised.conversions()) <= usize::from(context.budget()),
        | Err(_) => true,
    },
)]
#[inline]
pub fn synthesise_value(
    context: &mut CheckingContext<'_>,
    value: ValueId,
) -> Result<Synthesised<FormedValueType>, CheckRefusal>
{
    synthesise_value_with_failure(context, value).map_err(|failure| failure.refusal())
}

/// Synthesise the type of `value`, keeping the failure of a refused run.
///
/// # Specification
/// - requires: as for [`synthesise_value`].
/// - ensures: as for [`synthesise_value`].
/// - fails: the failure whose refusal [`synthesise_value`] gives, with the
///   rules pending when it came.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a refused body in a module keeps the failure the strict
///   face projects.
/// - witness: `module::tests::a_refused_body_keeps_the_rules_it_was_refused_inside`
#[spec(
    captures: depth = context.depth(Zone::Intuitionistic),
    ensures: |ret| context.depth(Zone::Intuitionistic) == depth,
)]
pub fn synthesise_value_with_failure(
    context: &mut CheckingContext<'_>,
    value: ValueId,
) -> Result<Synthesised<FormedValueType>, Failure>
{
    let goal = Goal::Value {
        term: value,
        direction: Direction::Synthesise,
    };
    let (produced, conversions) = Machine::run(context, goal)?;
    match produced {
        Produced::ValueType(produced) => Ok(Synthesised {
            produced: FormedValueType::derived(produced.settle(context.arena_mut())),
            conversions,
        }),
        Produced::CompType(_) | Produced::Checked => {
            Err(Failure::bare(CheckRefusal::MachineInvariant, pursued(goal)))
        },
    }
}

/// Check `value` against `expected`.
///
/// # Specification
/// - requires: `value` is closed over the context's binders, which are empty
///   between judgements.
/// - ensures: success exactly when the check rule of `value`'s former accepts
///   `expected`; for a synthesising former, exactly when its synthesised type
///   converts to `expected`.
/// - provides: the conversions the run made, as [`Checked::conversions`].
/// - fails: [`CheckRefusal::ShapeMismatch`] for a thunk checked against a type
///   that is no thunk type; [`CheckRefusal::TypeMismatch`] for a synthesising
///   value whose type does not convert; otherwise any refusal a reached rule
///   gives.
/// - panics: none.
/// - intension: the conversion count is the declared projection of the run's
///   crossings of the boundary.
///
/// # Errors
/// - [`CheckRefusal`] — the term does not have `expected`, or the run hit the
///   allowance or a dangling id.
///
/// # Judgement
/// - expected: `expected`
///
/// # Adequacy
/// - hypothesis: L3 — the per-former rule table in checking mode, separated as
///   for [`synthesise_value`], plus a mismatching literal and a thunk against
///   the wrong former.
/// - witness: `judgement::tests::every_value_former_is_answered_in_both_modes`
/// - witness: `judgement::tests::a_mismatched_literal_is_refused_with_both_types`
/// - witness: `judgement::tests::an_introduction_against_the_wrong_former_is_a_shape_mismatch`
/// - witness: `judgement::tests::the_faces_agree_on_free_terms`
/// - witness: `judgement::tests::well_typed_terms_synthesise_and_check_their_type`
#[spec(
    captures: depth = context.depth(Zone::Intuitionistic),
    ensures: |ret| context.depth(Zone::Intuitionistic) == depth
        && ret.as_ref().is_ok_and(|checked| usize::from(checked.conversions()) <= usize::from(context.budget())) == ret.is_ok(),
)]
#[inline]
pub fn check_value(
    context: &mut CheckingContext<'_>,
    value: ValueId,
    expected: FormedValueType,
) -> Result<Checked, CheckRefusal>
{
    check_value_with_failure(context, value, expected).map_err(|failure| failure.refusal())
}

/// Check `value` against `expected`, keeping the failure of a refused run.
///
/// # Specification
/// - requires: as for [`check_value`].
/// - ensures: as for [`check_value`].
/// - fails: the failure whose refusal [`check_value`] gives, with the rules
///   pending when it came.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a refusal under a thunk keeps the thunk's rule and the
///   force's, outermost first.
/// - witness: `judgement::tests::a_refusal_keeps_the_rules_it_stood_inside`
#[spec(
    captures: depth = context.depth(Zone::Intuitionistic),
    ensures: |ret| context.depth(Zone::Intuitionistic) == depth,
)]
pub fn check_value_with_failure(
    context: &mut CheckingContext<'_>,
    value: ValueId,
    expected: FormedValueType,
) -> Result<Checked, Failure>
{
    let goal = Goal::Value {
        term: value,
        direction: Direction::Check(expected.id()),
    };
    let (produced, conversions) = Machine::run(context, goal)?;
    checked(produced, conversions).map_err(|refusal| Failure::bare(refusal, pursued(goal)))
}

/// The pursuit of `goal` as it starts.
///
/// # Specification
/// trivial.
const fn pursued(goal: Goal) -> Pursuit
{
    let (at, expected) = judged(goal);
    Pursuit::new(at, expected, Stage::Starting)
}

/// Synthesise the type of `computation`.
///
/// # Specification
/// - requires: `computation` is closed over the context's binders, which are
///   empty between judgements.
/// - ensures: the formed type `computation` has by the synthesis rule of its
///   former.
/// - provides: the conversions the run made, as [`Synthesised::conversions`].
/// - fails: [`CheckRefusal::NotSynthesisable`] for a lambda, a return or an
///   offer; [`CheckRefusal::ShapeMismatch`] for a force of a value of no thunk
///   type, an application whose head has no arrow type, or a bind whose bound
///   computation has no returner type; [`CheckRefusal::SessionMismatch`] and
///   [`CheckRefusal::Linearity`] as for [`check_comp`]; otherwise any refusal a
///   reached rule gives.
/// - panics: none.
/// - intension: the conversion count is the declared projection of the run's
///   crossings of the boundary.
///
/// # Errors
/// - [`CheckRefusal`] — the term has no type in the fragment, or the run hit
///   the allowance or a dangling id.
///
/// # Adequacy
/// - hypothesis: L3 — the per-former rule table over computations in synthesis
///   mode, separated by one term of every computation former and the two
///   elimination shape refusals.
/// - witness: `judgement::tests::every_comp_former_is_answered_in_both_modes`
/// - witness: `judgement::tests::an_elimination_of_the_wrong_former_is_a_shape_mismatch`
/// - witness: `judgement::tests::a_bind_synthesises_its_continuations_type`
/// - witness: `judgement::tests::a_bind_of_a_non_returner_is_a_shape_mismatch`
/// - witness: `judgement::tests::the_faces_agree_on_free_terms`
/// - witness: `judgement::tests::well_typed_terms_synthesise_and_check_their_type`
/// - witness: `judgement::session::tests::the_seat_exchange_checks_at_both_ends`
#[spec(
    captures: depth = context.depth(Zone::Intuitionistic),
    ensures: |ret| context.depth(Zone::Intuitionistic) == depth && match ret {
        | Ok(synthesised) => context.arena().comp_type(synthesised.produced().id()).is_some()
            && usize::from(synthesised.conversions()) <= usize::from(context.budget()),
        | Err(_) => true,
    },
)]
#[inline]
pub fn synthesise_comp(
    context: &mut CheckingContext<'_>,
    computation: ComputationId,
) -> Result<Synthesised<FormedCompType>, CheckRefusal>
{
    let (produced, conversions) = Machine::run(context, Goal::Computation {
        term: computation,
        direction: Direction::Synthesise,
    })
    .map_err(|failure| failure.refusal())?;
    match produced {
        Produced::CompType(produced) => Ok(Synthesised {
            produced: FormedCompType::derived(produced),
            conversions,
        }),
        Produced::ValueType(_) | Produced::Checked => Err(CheckRefusal::MachineInvariant),
    }
}

/// Check `computation` against `expected`.
///
/// # Specification
/// - requires: `computation` is closed over the context's binders, which are
///   empty between judgements.
/// - ensures: success exactly when the check rule of the former accepts
///   `expected`; for a synthesising former, exactly when its synthesised type
///   converts to `expected`.
/// - provides: the conversions the run made, as [`Checked::conversions`].
/// - fails: [`CheckRefusal::ShapeMismatch`] for a lambda against no arrow, a
///   return against no returner, or a bind whose bound computation has no
///   returner type; [`CheckRefusal::TypeMismatch`] for a synthesising
///   computation whose type does not convert; [`CheckRefusal::SessionMismatch`]
///   for a session action its endpoint's state does not admit, and
///   [`CheckRefusal::Linearity`] for an endpoint left, reused, captured or sent
///   (see [`crate::session`]); otherwise any refusal a reached rule gives.
/// - panics: none.
/// - intension: the conversion count is the declared projection of the run's
///   crossings of the boundary.
///
/// # Errors
/// - [`CheckRefusal`] — the term does not have `expected`, or the run hit the
///   allowance or a dangling id.
///
/// # Judgement
/// - expected: `expected`
///
/// # Adequacy
/// - hypothesis: L3 — the per-former rule table over computations in checking
///   mode, separated by one term of every computation former, the two
///   introduction shape refusals and a mismatching application.
/// - witness: `judgement::tests::every_comp_former_is_answered_in_both_modes`
/// - witness: `judgement::tests::a_mismatched_application_is_refused_at_the_computation_bridge`
/// - witness: `judgement::tests::a_bind_checks_against_the_expected_computation`
/// - witness: `judgement::tests::a_bind_of_a_non_returner_is_a_shape_mismatch`
/// - witness: `judgement::tests::an_introduction_against_the_wrong_former_is_a_shape_mismatch`
/// - witness: `judgement::tests::well_typed_terms_synthesise_and_check_their_type`
/// - witness: `judgement::session::tests::the_seat_exchange_checks_at_both_ends`
/// - witness: `judgement::session::tests::a_leftover_endpoint_is_reported_by_name`
/// - witness: `judgement::tests::the_faces_agree_on_free_terms`
#[spec(
    captures: depth = context.depth(Zone::Intuitionistic),
    ensures: |ret| context.depth(Zone::Intuitionistic) == depth
        && ret.as_ref().is_ok_and(|checked| usize::from(checked.conversions()) <= usize::from(context.budget())) == ret.is_ok(),
)]
#[inline]
pub fn check_comp(
    context: &mut CheckingContext<'_>,
    computation: ComputationId,
    expected: FormedCompType,
) -> Result<Checked, CheckRefusal>
{
    let (produced, conversions) = Machine::run(context, Goal::Computation {
        term: computation,
        direction: Direction::Check(expected.id()),
    })
    .map_err(|failure| failure.refusal())?;
    checked(produced, conversions)
}

/// The evidence of a check run that produced `produced`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: [`Checked`] carrying `conversions` when the run ended on a check.
/// - fails: [`CheckRefusal::MachineInvariant`] when a check run produced a
///   type.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a check result and both type-result families expose check
///   evidence or the exact machine fault; public checking also observes the
///   retained conversion count.
/// - witness: `judgement::tests::a_result_of_the_wrong_kind_is_a_machine_fault`
/// - witness: `judgement::tests::a_two_bridge_check_crosses_the_boundary_twice`
#[spec(ensures: |ret| match produced {
    | Produced::Checked => ret.is_ok(),
    | Produced::ValueType(_) | Produced::CompType(_) => matches!(ret, Err(CheckRefusal::MachineInvariant)),
})]
const fn checked(
    produced: Produced,
    conversions: ConversionCount,
) -> Result<Checked, CheckRefusal>
{
    match produced {
        Produced::Checked => Ok(Checked { conversions }),
        Produced::ValueType(_) | Produced::CompType(_) => Err(CheckRefusal::MachineInvariant),
    }
}

/// Form `node` in the context's binders: the goal [`crate::formation`]'s faces
/// run.
///
/// # Specification
/// - requires: nothing.
/// - ensures: success exactly when every node `node` reaches has a formation
///   rule that accepts it, as [`crate::formation::form_value_type`] states.
/// - fails: the first refusal a formation rule or a code's judgement gives.
/// - panics: none.
///
/// # Errors
/// - [`CheckRefusal`] — the type is not formed.
///
/// # Adequacy
/// - hypothesis: L1 over bounded generated type programs compares the exact
///   classifier, with L3 every admitted or refused former and a dangling node;
///   wrong formation decisions and scope leakage change those observations.
/// - witness: `formation::tests::every_type_has_exactly_one_classifier`
/// - witness: `formation::tests::every_value_type_constructor_has_a_formation_rule`
/// - witness: `formation::tests::every_comp_type_constructor_has_a_formation_rule`
#[spec(
    captures: depth = context.depth(Zone::Intuitionistic),
    ensures: context.depth(Zone::Intuitionistic) == depth,
)]
pub fn form(
    context: &mut CheckingContext<'_>,
    node: TypeNode,
) -> Result<(), CheckRefusal>
{
    let (produced, conversions) =
        Machine::run(context, Goal::Form(node)).map_err(|failure| failure.refusal())?;
    checked(produced, conversions).map(|_| ())
}

/// The fixed endpoints of a forward stack-typing judgment.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct StackJudgement
{
    /// The source stack literal.
    at: ValueId,
    /// The caller's expected stack classifier.
    expected: ValueTypeId,
    /// The original consumed computation type.
    consumed: CompTypeId,
}

/// A position in a stack literal's frames or a handler's clauses, counted
/// from zero.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct Ordinal(usize);

impl Ordinal
{
    /// The first frame or clause.
    const FIRST: Self = Self(0);

    /// The position after this one.
    ///
    /// # Specification
    /// - ensures: the successor position.
    /// - fails: [`CheckRefusal::MachineInvariant`] past the largest position,
    ///   which no arena-held list reaches.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a multi-frame stack and a multi-clause handler visit
    ///   each element once and in order; a skipped or repeated position changes
    ///   the observed rows and binders.
    /// - witness: `judgement::tests::control_rules_preserve_rows_scopes_and_shapes`
    /// - witness: `judgement::tests::handlers_discharge_only_their_own_interface`
    #[spec(ensures: |ret| ret.is_err() || ret.as_ref().is_ok_and(|next| next.0 == self.0.wrapping_add(1)))]
    fn next(self) -> Result<Self, CheckRefusal>
    {
        self.0
            .checked_add(1)
            .map(Self)
            .ok_or(CheckRefusal::MachineInvariant)
    }
}

/// A judgement the machine is to run.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Goal
{
    /// Advance one frame of a first-class stack.
    Stack
    {
        /// The source and fixed endpoint of the judgment.
        judgement: StackJudgement,
        /// The next source frame.
        position: Ordinal,
        /// The type delivered by the preceding frames.
        input: CompTypeId,
    },
    /// Judge a value.
    Value
    {
        /// The value.
        term: ValueId,
        /// The direction, holding the expected value type when checking.
        direction: Direction<ValueTypeId>,
    },
    /// Judge a computation.
    Computation
    {
        /// The computation.
        term: ComputationId,
        /// The direction, holding the expected computation type when checking.
        direction: Direction<CompTypeId>,
    },
    /// Form a type; a formed type ends in [`Produced::Checked`].
    Form(TypeNode),
}

/// What a finished judgement hands to the frame awaiting it.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Produced
{
    /// A synthesised value type, read through the relocation it carries: a
    /// variable's slot type moved to the depth it is read at. The value
    /// bridge reads it through; every other rule settles it where it reads
    /// it.
    ValueType(Relocated<ValueTypeId>),
    /// A synthesised computation type.
    CompType(CompTypeId),
    /// A check that succeeded, or a type formed.
    Checked,
}

/// The codomain an application has once its argument checks.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Codomain
{
    /// An arrow's: the application has it as it stands.
    Ambient(CompTypeId),
    /// A dependent arrow's, scoped under the argument's binder: the application
    /// has it instantiated at the argument.
    Dependent(CompTypeId),
}

/// The path type a term is judged against or synthesised, read at its weak
/// head.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum PathReading
{
    /// A path type with its carrier and endpoints.
    Known
    {
        /// The carrier.
        carrier: ValueTypeId,
        /// The left endpoint.
        left: ValueId,
        /// The right endpoint.
        right: ValueId,
    },
    /// The unknown type, which stands for a path type of unknown parts.
    Unknown(ValueTypeId),
}

/// A telescope transport's motive `Π (y : A). Π (z : B). F C`, read as its
/// three layers.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct TelescopeParts
{
    /// The path's carrier `A`, in the transport's context.
    carrier: ValueTypeId,
    /// The family `B`, under the point's binder.
    family: ValueTypeId,
    /// The body `C`, under the point's binder and then the family element's.
    body: ValueTypeId,
}

/// A telescope body instantiated at a point and an element of the family's
/// fibre over it: `C[point, element]`.
///
/// # Specification
/// - requires: `body` stands under two binders more than `point` and `element`,
///   which share one context.
/// - ensures: the point substituted at the outer binder, past the kept inner
///   one, then the element at the inner binder.
/// - provides: the telescope's substitution law as iterated single
///   substitution, the kernel's reading of the same rule.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a body reading both entries instantiates each at its own
///   endpoint.
/// - witness: `judgement::tests::a_telescope_transport_replays_its_substitution_law`
#[spec(ensures: |ret| ret == body || arena.value_type(ret).is_some())]
fn telescope_instance(
    arena: &mut gandr_core_term::CoreArena,
    body: ValueTypeId,
    (point, element): (ValueId, ValueId),
) -> ValueTypeId
{
    let fibre = instantiate_value_type_under(arena, body, point, Binders::from(1_u32));
    instantiate_value_type(arena, fibre, element)
}

/// The two components of a dependent pair's inhabitant: those of the written
/// pair it is or a declared constant's body is, and otherwise its two
/// projections, each read as the value it returns.
///
/// # Specification
/// - requires: `pair` inhabits a dependent pair.
/// - ensures: [`tuple_components`] of `pair` at two components.
/// - fails: the unfolding's refusal.
/// - panics: none.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Adequacy
/// - hypothesis: L3 — the identity of a written pair reads its components, the
///   identity of a declared pair those of the pair it unfolds to, and the
///   identity of a pair without a body its projections.
/// - witness: `judgement::tests::a_pair_of_paths_checks_at_the_identity_of_a_dependent_pair`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |components| components.iter().all(|&component| context.arena().value(component).is_some())))]
fn pair_components(
    context: &mut CheckingContext<'_>,
    pair: ValueId,
) -> Result<[ValueId; 2], CheckRefusal>
{
    match *tuple_components(context, pair, ComponentCount::from(2_usize))?.as_slice() {
        [first, second] => Ok([first, second]),
        _ => Err(CheckRefusal::MachineInvariant),
    }
}

/// The `width` components of a tuple's inhabitant, read as the kernel reads
/// an identity's endpoint: those of the written tuple it is or a declared
/// constant's body is, its components' transports when that is a written
/// tuple transported at a product, and otherwise its projections, each read
/// as the value it returns.
///
/// # Specification
/// - requires: `tuple` inhabits a product or a dependent pair of `width`
///   factors.
/// - ensures: the components of the written tuple of `width` that `tuple` is,
///   or that the chain of declared constants it names unfolds to; when that
///   head is `⟨tr(x. A₀ × … × Aₙ, p, v)⟩` and `v` is or names such a tuple, its
///   components each transported along `p` in their own factor, `⟨tr(x. Aᵢ, p,
///   vᵢ)⟩`; `⟨tuple.0⟩` … `⟨tuple.n⟩` otherwise. No other reduction runs, so
///   the endpoints are the ones the kernel computes and the dialogues recorded
///   at them replay there.
/// - fails: the unfolding's refusal.
/// - panics: none.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Adequacy
/// - hypothesis: L3 — as [`pair_components`], the identity of a written tuple
///   of three reads its three components, and a tuple transported along a
///   univalence path at a product reads its components' transports.
/// - witness: `judgement::tests::a_transported_tuple_reads_its_components_transports`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |components| components.len() == usize::from(width) && components.iter().all(|&component| context.arena().value(component).is_some())))]
fn tuple_components(
    context: &mut CheckingContext<'_>,
    tuple: ValueId,
    width: ComponentCount,
) -> Result<Vec<ValueId>, CheckRefusal>
{
    let count = usize::from(width);
    let head = declared_head(context, tuple)?;
    if let Some(components) = context.arena().value(head).and_then(Value::components)
        && components.len() == count
    {
        return Ok(components.to_vec());
    }
    if let Some(&Value::Returned(formed)) = context.arena().value(head)
        && let Some(&Computation::PathTransport {
            motive,
            path,
            value,
        }) = context.arena().computation(formed)
        && let Some(&gandr_core_term::ValueType::Product(ref factors)) =
            context.arena().value_type(motive)
        && factors.len() == count
    {
        let factors = factors.to_vec();
        let moved = declared_head(context, value)?;
        let arena = context.arena_mut();
        if let Some(components) = arena.value(moved).and_then(Value::components)
            && components.len() == count
        {
            let components = components.to_vec();
            return Ok(factors
                .into_iter()
                .zip(components)
                .map(|(factor, component)| {
                    let transported = arena.computation_path_transport(factor, path, component);
                    arena.value_returned(transported)
                })
                .collect());
        }
    }
    let arena = context.arena_mut();
    Ok((0_usize .. count)
        .map(|index| {
            let projected = arena
                .computation_tuple_projection(tuple, gandr_kernel_term::Component::from(index));
            arena.value_returned(projected)
        })
        .collect())
}

/// The value `value` is read as at an identity's endpoint: the body of the
/// declared constant it names, through a chain of definitions whose bodies
/// name a constant, or itself.
///
/// # Specification
/// - requires: as [`CheckingContext::unfold`].
/// - ensures: `value` when it names no constant or its constant has no body the
///   checker unfolds; otherwise the first value of the chain of unfoldings that
///   names no constant, or the last one that unfolds no further.
/// - fails: as [`CheckingContext::unfold`].
/// - panics: none.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Termination
/// - reason: the `loop` takes one certified unfolding per turn.
/// - measure: the chain of definitions: each step unfolds one constant to its
///   accepted body, and the judgement's step allowance bounds the chain.
///
/// # Adequacy
/// - hypothesis: L3 — as [`tuple_components`].
/// - witness: `judgement::tests::a_pair_of_paths_checks_at_the_identity_of_a_dependent_pair`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |&head| context.arena().value(head).is_some()))]
fn declared_head(
    context: &mut CheckingContext<'_>,
    value: ValueId,
) -> Result<ValueId, CheckRefusal>
{
    let mut head = value;
    while matches!(context.arena().value(head), Some(&Value::Constant(..))) {
        match context.unfold(head)? {
            Maybe::Present(reduct) => head = reduct,
            Maybe::Absent(_) => break,
        }
    }
    Ok(head)
}

/// How a run checking `goal` reaches a region its definition abstracts, `A at
/// r` under `@[r : Region]`, with no region open: through the type it checks
/// against.
///
/// # Specification
/// - ensures: for a goal checked against a type, what
///   [`crate::capability::abstracts`] answers for it, and
///   [`crate::capability::Reach::Keeps`] where that refuses, so a type the walk
///   cannot read runs the fence; [`crate::capability::Reach::Clear`] for a goal
///   that synthesises, a form and a stack.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a definition over `@[r : Region]` that stashes a value
///   kept at `r` in a thunk kept in no region is refused, and one that forces
///   it or hands it back at `r` checks.
/// - witness: `judgement::access::tests::a_thunk_naming_a_value_kept_at_a_region_binder_is_kept_there_1221`
#[spec(ensures: |ret| ret == crate::capability::Reach::Clear || matches!(goal, Goal::Value { direction: Direction::Check(_), .. } | Goal::Computation { direction: Direction::Check(_), .. }))]
fn abstracted_by(
    arena: &gandr_core_term::CoreArena,
    goal: Goal,
) -> crate::capability::Reach
{
    let checked = match goal {
        Goal::Value {
            direction: Direction::Check(expected),
            ..
        } => TypeNode::Value(expected),
        Goal::Computation {
            direction: Direction::Check(expected),
            ..
        } => TypeNode::Computation(expected),
        Goal::Value { .. } | Goal::Computation { .. } | Goal::Form(_) | Goal::Stack { .. } => {
            return crate::capability::Reach::Clear;
        },
    };
    crate::capability::abstracts(arena, checked).unwrap_or(crate::capability::Reach::Keeps)
}

/// The completed premise of a native List fold rule.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum ListPhase
{
    /// The element annotation is formed.
    Element,
    /// The result annotation is formed.
    Result,
    /// The list checks at its annotated element type.
    Input,
    /// The nil branch checks in the ambient context.
    Nil,
    /// The cell branch checks under its two binders.
    Cons,
}

/// How a run's value was reached: as the goal of a judgement of its own, or
/// read without one.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Read
{
    /// A written run, or a nested computation checked against a value type:
    /// the value's own goal keeps its typing when it ascends.
    Goal,
    /// A nested computation read where no thunk stands
    /// ([`Machine::unsuspended`]): the run keeps the value's typing.
    Unsuspended,
}

/// How a computation written where a thunk is read is judged.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum NestedRead
{
    /// Checked against the thunk's body, and suspended.
    Body,
    /// A call synthesised first: it runs when its type is a returner.
    Call,
}

/// A rule waiting on the judgement of one of its subterms.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Frame
{
    /// Continue a native premise after the previous premise succeeded.
    NativeNext(Goal),
    /// Publish the native judgment after all its premises succeeded.
    NativeYield(Produced),
    /// Retain a synthesized field type in the flat native result stack.
    NativeCollect,
    /// An extra record field was typed but does not contribute to the expected
    /// type.
    NativeDiscard,
    /// Assemble a synthesised tuple's eager product from its components'
    /// types, the result-stack suffix from `base`.
    NativeTuple
    {
        /// The result-stack suffix owned by this tuple.
        base: usize,
    },
    /// Assemble a record's exact inferred field types.
    NativeRecord
    {
        /// The source record supplies labels.
        term: ValueId,
        /// The result-stack suffix owned by this record.
        base: usize,
    },
    /// Await the case scrutinee's nominal classifier.
    NativeCase(ComputationId),
    /// Await formation under the case's one motive binder.
    NativeMotive
    {
        /// The case.
        term: ComputationId,
        /// Its scrutinee classifier.
        datatype: ValueTypeId,
        /// How the case is read against its type's rules, when the type has
        /// any.
        respect: Maybe<crate::respect::Reading, crate::respect::obligation::Absent>,
        /// The stage the case opened for its recursive fields, when its
        /// scrutinee stood at one.
        opened: Maybe<gandr_kernel_term::StageId, crate::recursion::Unstaged>,
    },
    /// Show a case over a presented type respects the type's rules, once its
    /// branches have checked.
    NativeRespect
    {
        /// The case.
        term: ComputationId,
        /// Its scrutinee classifier.
        datatype: ValueTypeId,
        /// How the case is read against the rules.
        reading: crate::respect::Reading,
    },
    /// Show a case over a sort its words loop at respects each loop, once
    /// its branches have checked.
    NativeLoops
    {
        /// The case.
        term: ComputationId,
        /// Its scrutinee classifier.
        datatype: ValueTypeId,
    },
    /// Form a branch's identified telescope with the open mutual block's
    /// definitions foreseen, before the branch checks at it.
    NativeForesee(CompTypeId),
    /// Close the foresight a branch's telescope formed in.
    NativeForget(crate::context::Foresight),
    /// Await a dependent split scrutinee's classifier, which must be a
    /// dependent pair.
    SigmaSplitScrutinee(ComputationId),
    /// Await formation of a dependent split's motive under the scrutinee's
    /// binder.
    SigmaSplitMotive
    {
        /// The split.
        term: ComputationId,
        /// The dependent pair the scrutinee synthesised, at its weak head.
        sigma: ValueTypeId,
    },
    /// Await a projection operand's record or product classifier.
    NativeProjection(ComputationId),
    /// Check an ascription's body against its stated type, once the type
    /// has formed.
    Ascription
    {
        /// The computation ascribed.
        body: ComputationId,
        /// The type it is ascribed.
        ty: CompTypeId,
    },
    /// Check an operation payload after forming its interface.
    PerformPayload
    {
        /// The perform or the exercise.
        at: ComputationId,
        /// The supplied payload.
        payload: ValueId,
        /// Its interface classifier.
        expected: ValueTypeId,
        /// The singleton-row result.
        result: CompTypeId,
    },
    /// Continue with another checking premise.
    Next(Goal),
    /// Read a resumption's stack classifier.
    Resume
    {
        /// The first-class stack.
        stack: ValueId,
        /// The computation fed to it.
        body: ComputationId,
    },
    /// Read an abandoned stack's classifier.
    Abandon
    {
        /// The first-class stack.
        stack: ValueId,
    },
    /// Select one component of a synthesized lazy product.
    Project
    {
        /// The projection.
        at: ComputationId,
        /// The selected component.
        component: gandr_kernel_term::Component,
    },
    /// The nearest answer delimiter, retained while checking its body.
    Reset
    {
        /// Its answer in the delimiter's scope.
        answer: CompTypeId,
        /// The scope in which the answer was formed.
        depth: BinderDepth,
    },
    /// Infer a handler's subject after forming the carried interface.
    HandlerForm
    {
        /// The handler.
        at: ComputationId,
        /// Its answer type.
        answer: CompTypeId,
        /// The formed interface carrier.
        interface: CompTypeId,
    },
    /// Read the subject's result and residual effects.
    HandlerSubject
    {
        /// The handler.
        at: ComputationId,
        /// Its answer type.
        answer: CompTypeId,
        /// The formed interface carrier.
        interface: CompTypeId,
    },
    /// Close the return-clause binder and check the operation clauses.
    HandlerReturn
    {
        /// The handler.
        at: ComputationId,
        /// Its ambient answer type.
        answer: CompTypeId,
    },
    /// Close one operation clause's payload and resumption binders.
    HandlerClause
    {
        /// The handler.
        at: ComputationId,
        /// Its ambient answer type.
        answer: CompTypeId,
        /// The next clause.
        position: Ordinal,
    },
    /// Await the synthesised type of the capability an operation is exercised
    /// through.
    ExerciseCapability
    {
        /// The exercise.
        at: ComputationId,
    },
    /// Check a capability scope's subject after forming the type it is
    /// checked at.
    ScopeForm
    {
        /// The scope.
        at: ComputationId,
        /// Its answer type.
        answer: CompTypeId,
        /// The subject's type, in the scope's own context.
        subject: CompTypeId,
    },
    /// Close the capability binder once the subject checks, then open the
    /// return clause. While it waits, the region of the scope at its depth
    /// is live.
    ScopeSubject
    {
        /// The scope.
        at: ComputationId,
        /// Its answer type.
        answer: CompTypeId,
    },
    /// Continue a stack after its current frame synthesizes an output.
    StackNext
    {
        /// The source and fixed endpoints.
        judgement: StackJudgement,
        /// The next source frame.
        position: Ordinal,
    },
    /// Strengthen a stack bind's body and accumulate its consumed row.
    StackBind
    {
        /// The source stack literal.
        at: ValueId,
        /// The body, for row diagnostics.
        body: ComputationId,
        /// The consumed returner in the ambient scope.
        bound: CompTypeId,
    },
    /// Await a pure native List fold premise.
    ListFold
    {
        /// The source fold.
        at: ComputationId,
        /// Its ambient pure returner classifier.
        result: CompTypeId,
        /// The premise just checked.
        phase: ListPhase,
    },
    /// Await the first component path.
    PathProductFirst
    {
        /// The product.
        product: ValueId,
        /// The first path.
        at: ValueId,
        /// The second path.
        second: ValueId,
    },
    /// Await the second component path.
    PathProductSecond
    {
        /// The product.
        product: ValueId,
        /// The second path.
        at: ValueId,
        /// The first path's classifier.
        classifier: ValueTypeId,
        /// The first path, read.
        first: crate::product::Component,
    },
    /// Check the inverse after the forward map.
    PathBackward
    {
        /// The inverse map.
        backward: ValueId,
        /// The source type.
        source: ValueTypeId,
        /// The target type.
        target: ValueTypeId,
        /// The certificate classifier.
        path_type: ValueTypeId,
    },
    /// Finish a native certificate after both maps check.
    PathChecked
    {
        /// The certificate classifier.
        path_type: ValueTypeId,
    },
    /// Check the second argument of a saturated native operation.
    PrimitiveSecond
    {
        /// The second argument.
        argument: ValueId,
        /// Its table-declared classifier.
        expected: ValueTypeId,
        /// The operation's returner type.
        result: CompTypeId,
    },
    /// Complete a native operation after its arguments checked.
    PrimitiveResult
    {
        /// The operation's returner type.
        result: CompTypeId,
    },
    /// Await the path classifier.
    TransportPath
    {
        /// The path.
        path: ValueId,
        /// The transported operand.
        value: ValueId,
    },
    /// Await the source operand check.
    TransportOperand
    {
        /// The target returner.
        result: CompTypeId,
    },
    /// Await the type reflexivity's point synthesises; reflexivity has the
    /// path type from the point to itself in it.
    HereSynthesised
    {
        /// The point.
        point: ValueId,
    },
    /// Await the check of reflexivity's point against the carrier, then meet
    /// the point with both endpoints of the path type it is checked against.
    HereEndpoints
    {
        /// The reflexivity.
        at: ValueId,
        /// Its point.
        point: ValueId,
        /// The path type's left endpoint.
        left: ValueId,
        /// The path type's right endpoint.
        right: ValueId,
    },
    /// Await the type `funext`'s first function synthesises: the classifier
    /// its second function checks against.
    FunextLeft
    {
        /// The `funext`.
        at: ValueId,
        /// Its first function.
        left: ValueId,
        /// Its second function.
        right: ValueId,
    },
    /// Await the check of `funext`'s second function against the classifier,
    /// then decide the two functions pointwise.
    FunextRight
    {
        /// The `funext`.
        at: ValueId,
        /// Its first function.
        left: ValueId,
        /// Its second function.
        right: ValueId,
        /// The type the first function synthesised.
        classifier: ValueTypeId,
    },
    /// Await the type `equiv`'s forward translator synthesises, which names
    /// the two codes and so the type its backward translator checks against.
    EquivForward
    {
        /// The `equiv`.
        at: ValueId,
        /// Its forward translator.
        forward: ValueId,
        /// Its backward translator.
        backward: ValueId,
    },
    /// Await the check of `equiv`'s backward translator, then decide both
    /// round trips.
    EquivBackward
    {
        /// The `equiv`.
        at: ValueId,
        /// Its forward translator.
        forward: ValueId,
        /// Its backward translator.
        backward: ValueId,
        /// The source code's type and the target code's.
        codes: (ValueTypeId, ValueTypeId),
    },
    /// Await the type a univalence's record synthesises, which names the two
    /// types its forward map relates.
    UnivalenceRecord
    {
        /// The `ua`.
        at: ValueId,
        /// Its record.
        record: ValueId,
        /// The forward map it carries.
        forward: ValueId,
    },
    /// Await the checks of a univalence's record and codes, then produce its
    /// path type.
    UnivalenceChecked
    {
        /// The path type it synthesises.
        path: ValueTypeId,
    },
    /// Await the checks of a `ua`'s translators, then derive its path at its
    /// stratum.
    UaTranslators
    {
        /// The `ua`.
        at: ValueId,
    },
    /// Await the type a compound endpoint's computation synthesises, which
    /// must be a pure returner.
    ReturnedEndpoint
    {
        /// The compound endpoint.
        at: ValueId,
    },
    /// Await the type a run computation synthesises, which must be a returner:
    /// the run stands for the value it returns.
    Ran
    {
        /// The nested computation or written run.
        at: ValueId,
        /// Whether `at` is the goal of a judgement of its own.
        read: Read,
    },
    /// Await the type a call written where a thunk is read synthesises, when
    /// the thunk's body is no returner: a call that returns runs, and the
    /// value it returns crosses the value bridge; any other is suspended, and
    /// its type crosses the computation bridge to the body.
    NestedCall
    {
        /// The nested computation's value.
        at: ValueId,
        /// The call.
        call: ComputationId,
        /// The thunk type `at` is checked against.
        expected: ValueTypeId,
        /// The body that thunk type matches.
        body: CompTypeId,
    },
    /// Await the element path's classifier; the motive is then formed under a
    /// binder of its carrier.
    ElementTransportPath
    {
        /// The transport.
        at: ComputationId,
        /// The motive, under one binder.
        motive: ValueTypeId,
        /// The transported operand.
        value: ValueId,
    },
    /// Await the motive's formation under its binder, closed again; the operand
    /// then checks against the motive at the left endpoint.
    ElementTransportMotive
    {
        /// The transport.
        at: ComputationId,
        /// The motive, under one binder.
        motive: ValueTypeId,
        /// The transported operand.
        value: ValueId,
        /// The path's carrier, which a stage crosses only as a set.
        carrier: ValueTypeId,
        /// The path's left endpoint.
        left: ValueId,
        /// The path's right endpoint.
        right: ValueId,
    },
    /// Await both operands of the session statement `at`, checked against the
    /// value universe; the engine then decides it.
    SessionStatement
    {
        /// The statement.
        at: ValueId,
    },
    /// Await a bisimilarity's payload paths, checked against the paths it
    /// owes; they are then elaborated to native certificates.
    SessionPayloads
    {
        /// The statement.
        at: ValueId,
        /// The identity it inhabits.
        identity: ValueTypeId,
    },
    /// Await the type a stay's point synthesised.
    StaySynthesised
    {
        /// The stay.
        at: ValueId,
        /// Its point.
        point: ValueId,
    },
    /// Await the first flow of a composite.
    ThenFirst
    {
        /// The composite.
        at: ValueId,
        /// Its second flow.
        second: ValueId,
    },
    /// Await the second flow of a composite, which must start where the first
    /// ends.
    ThenSecond
    {
        /// The composite.
        at: ValueId,
        /// The first flow's type.
        first: ValueTypeId,
    },
    /// Await the first component flow of a flow product.
    FlowProductFirst
    {
        /// The product.
        product: ValueId,
        /// The first flow.
        at: ValueId,
        /// The second flow.
        second: ValueId,
    },
    /// Await the second component flow of a flow product.
    FlowProductSecond
    {
        /// The second flow.
        at: ValueId,
        /// The first flow's source and target codes.
        first: (ValueTypeId, ValueTypeId),
    },
    /// Await a record update's base; its shape is read, and its overlay is
    /// synthesised next.
    UpdateBase
    {
        /// The update.
        at: ValueId,
    },
    /// Await a record update's overlay, its base's type in hand.
    UpdateOverlay
    {
        /// The update.
        at: ValueId,
        /// The base's type.
        base: ValueTypeId,
    },
    /// Await the flow a ride moves along; its motive then forms under a binder
    /// of the flow's carrier.
    RideFlow
    {
        /// The ride.
        at: ComputationId,
        /// The motive, under one binder.
        motive: ValueTypeId,
        /// The ridden value.
        value: ValueId,
    },
    /// Await the motive's formation under its binder, closed again; the ride
    /// is then classified and the value checks at the motive's source fibre.
    RideMotive
    {
        /// The ride.
        at: ComputationId,
        /// The flow's type.
        flow: ValueTypeId,
    },
    /// Await the ridden value's check; a run moving between distinct sessions
    /// is then admitted by the recorded-run consumer.
    RideValue
    {
        /// The ride.
        at: ComputationId,
        /// The ridden value.
        value: ValueId,
        /// The flow's type.
        flow: ValueTypeId,
        /// The returner of the motive's target fibre.
        result: CompTypeId,
        /// Whether the value is a run or a prefix moving between distinct
        /// sessions.
        moving: crate::flow::Moving,
    },
    /// Await the type a `forward`'s translator synthesised: the two codes the
    /// statement relates.
    ForwardTranslator
    {
        /// The `forward`.
        at: ValueId,
        /// Its translator.
        translator: ValueId,
    },
    /// Await the type a function flow's domain boundary synthesised.
    ArrowDomain
    {
        /// The function flow.
        at: ValueId,
        /// Its codomain boundary.
        codomain: ValueId,
    },
    /// Await the type a function flow's codomain boundary synthesised.
    ArrowCodomain
    {
        /// The function flow.
        at: ValueId,
        /// The domain boundary's type.
        domain_type: ValueTypeId,
    },
    /// Await the type a function flow synthesised, then compare it with the
    /// flow type it is checked against, naming a misdirected boundary.
    ArrowAgainst
    {
        /// The function flow.
        at: ValueId,
        /// The flow type it is checked against.
        expected: ValueTypeId,
    },
    /// Await the check of a stay's point against the carrier, then meet the
    /// point with both endpoints of the flow type it is checked against.
    StayEndpoints
    {
        /// The stay.
        at: ValueId,
        /// Its point.
        point: ValueId,
        /// The flow type's carrier.
        carrier: ValueTypeId,
        /// The flow type's source.
        left: ValueId,
        /// The flow type's target.
        right: ValueId,
    },
    /// Await the path classifier of the telescope transport `at`; its motive
    /// then forms.
    TelescopePath
    {
        /// The transport.
        at: ComputationId,
    },
    /// Await the formation of the telescope transport's motive; the path's
    /// carrier then meets the motive's first entry and the start checks in
    /// the family's fibre over the source.
    TelescopeMotive
    {
        /// The transport.
        at: ComputationId,
        /// The path's carrier.
        carrier: ValueTypeId,
        /// The path's source and target.
        ends: (ValueId, ValueId),
    },
    /// Await the start's check; the identity over the path then synthesises.
    TelescopeStart
    {
        /// The transport.
        at: ComputationId,
        /// The path's source and target.
        ends: (ValueId, ValueId),
    },
    /// Await the classifier of the identity over the path, which must lie
    /// over it; the operand then checks at the body's source instance.
    TelescopeOver
    {
        /// The transport.
        at: ComputationId,
        /// The path's source and target.
        ends: (ValueId, ValueId),
    },
    /// Await the sum scrutinee classifier of the case `at`.
    CaseScrutinee
    {
        /// The case.
        at: ComputationId,
        /// The scrutinee.
        scrutinee: ValueId,
        /// The common result type.
        expected: CompTypeId,
    },
    /// Await the product scrutinee classifier of the split `at`.
    SplitScrutinee
    {
        /// The split.
        at: ComputationId,
        /// The scrutinee.
        scrutinee: ValueId,
        /// The direction the body is judged in: synthesised, or checked
        /// against a type outside the split's binders.
        direction: Direction<CompTypeId>,
    },
    /// Await the split body's judgement, then close one binder per component;
    /// a synthesised type is strengthened past them first.
    SplitBody
    {
        /// The split.
        at: ComputationId,
        /// Its component count: the binders the body is judged under.
        arity: gandr_core_term::ComponentCount,
    },
    /// Once the previous branch has checked, check `branch` under a binder of
    /// its summand.
    CaseBranch
    {
        /// The branch.
        branch: ComputationId,
        /// Its summand, which the branch binds.
        summand: ValueTypeId,
        /// The common result type under one binder.
        expected: CompTypeId,
    },
    /// Await the List classifier of the list case `at`'s scrutinee.
    ListCaseScrutinee
    {
        /// The list case.
        at: ComputationId,
        /// The list it reads.
        scrutinee: ValueId,
        /// The common result type.
        expected: CompTypeId,
    },
    /// Once the list case `at`'s empty branch has checked, check its cell
    /// branch under a binder of the element and one of the tail.
    ListCaseNil
    {
        /// The list case.
        at: ComputationId,
        /// The list's element type.
        element: ValueTypeId,
        /// The tail's type, at the stage the case opened when the list
        /// stood at one.
        tail: ValueTypeId,
        /// The common result type.
        expected: CompTypeId,
    },
    /// Await the cell branch's check, then close its two binders.
    ListCaseCons,
    /// The arm `arm` of a case whose arms join a held value or a live buffer
    /// has checked, with another to come: give the next arm the held slots
    /// and live buffers as the case found them.
    ArmEnded
    {
        /// Where the case's zones are kept.
        zones: session::ZoneMark,
        /// The arm that checked.
        arm: ComputationId,
    },
    /// The last arm `arm` of a case whose arms join a held value or a live
    /// buffer has checked: leave each held slot consumed when any arm consumed
    /// it.
    ArmsJoined
    {
        /// Where the case's zones are kept.
        zones: session::ZoneMark,
        /// The arm that checked.
        arm: ComputationId,
    },
    /// A force waits on the type its value synthesises, which must be a thunk
    /// type; the force has the thunk's body.
    Force
    {
        /// The forced value.
        value: ValueId,
    },
    /// A decomposition waits on the type its dialogue synthesises, which must
    /// be a dialogue type; the decomposition returns a web.
    Decompose
    {
        /// The dialogue decomposed.
        dialogue: ValueId,
    },
    /// An application waits on the type its head synthesises, which must be an
    /// arrow or a dependent arrow; the argument then checks against the
    /// domain.
    ApplicationHead
    {
        /// The head.
        head: ComputationId,
        /// The argument still to check.
        argument: ValueId,
    },
    /// An application waits on its argument's check; an argument at a static
    /// Pi must then be rigid, and the application has the codomain.
    ApplicationArgument
    {
        /// The head the argument is applied to, when the application is a
        /// term rather than a stack frame.
        head: Option<ComputationId>,
        /// The argument, which a dependent codomain is instantiated at.
        argument: ValueId,
        /// The domain the argument checked against.
        domain: ValueTypeId,
        /// The codomain.
        codomain: Codomain,
    },
    /// An applied fixpoint waits on the type its argument synthesises; the
    /// fixpoint then checks against the arrow from that type to the
    /// application's.
    FixpointArgument
    {
        /// The fixpoint.
        head: ComputationId,
        /// The application's type.
        expected: CompTypeId,
    },
    /// A lambda waits on its body's check, then closes the binder it opened.
    LambdaBody,
    /// A bind waits on the type its bound computation synthesises, which must
    /// be a returner; it then opens a binder of the returned type and judges
    /// its body in the bind's own direction.
    BindBound
    {
        /// The bind.
        at: ComputationId,
        /// The bound computation.
        bound: ComputationId,
        /// The body still to judge.
        body: ComputationId,
        /// The bind's own direction, which the body takes.
        direction: Direction<CompTypeId>,
    },
    /// A bind waits on its body's judgement, then closes the binder it opened
    /// and hands the body's result on, a synthesised type lowered out of the
    /// binder.
    BindBody
    {
        /// The bind.
        at: ComputationId,
        /// The bound returner's type, in the ambient context.
        bound: CompTypeId,
    },
    /// A synthesising value in checking position waits on its synthesised type,
    /// which then crosses the value bridge.
    ValueBridge
    {
        /// The value.
        at: ValueId,
        /// The type it is checked against.
        expected: ValueTypeId,
    },
    /// A synthesising computation in checking position waits on its
    /// synthesised type, which then crosses the computation bridge.
    CompBridge
    {
        /// The computation.
        at: ComputationId,
        /// The type it is checked against.
        expected: CompTypeId,
    },
    /// A quote waits on the formation of the type it quotes; it then has the
    /// universe at that type's level.
    Quote(TypeNode),
    /// A former waits on the formation of one child; the next is formed then.
    FormNext(TypeNode),
    /// A dependent arrow or a dependent pair waits on its domain's formation;
    /// it then forms its codomain or second factor under a binder of the
    /// domain.
    FormUnder
    {
        /// The domain, or the first factor.
        domain: ValueTypeId,
        /// The codomain or the second factor, scoped under the domain's
        /// binder.
        under: TypeNode,
    },
    /// A dependent arrow or a dependent pair waits on the formation under its
    /// binder, then closes the binder it opened.
    FormBinder,
    /// A lift waits on its type's formation; its target must then lie above
    /// the type's level.
    FormLift(ValueTypeId),
    /// A decode waits on the type its code synthesises, which then crosses the
    /// decode bridge.
    FormElement(TypeNode),
    /// A static Pi waits on the formation of both its classifiers; each must
    /// then be a static classifier — a universe or a static Pi — at its weak
    /// head.
    FormStaticPi(ValueTypeId),
    /// A run or prefix type waits on its protocol's check. Both stay on the
    /// checker's side, so a session type formed beneath this frame may read a
    /// binder outside it, as no session type elsewhere may.
    RunProtocol,
    /// A list cell, or a pair checked against a dependent pair, waits on its
    /// first component's check; the second then checks against the second
    /// factor, read at the first component for a dependent pair.
    PairSecond
    {
        /// The second component.
        second: ValueId,
        /// The second factor, at the first component.
        expected: ValueTypeId,
    },
    /// A static application waits on the type its head so far synthesises,
    /// which must be a static Pi; the argument at `position` then meets its
    /// domain.
    StaticSpine
    {
        /// The whole application.
        at: ValueId,
        /// How many arguments stand before this one.
        position: ArgumentPosition,
        /// The argument.
        argument: ValueId,
        /// How many arguments the application spine applies.
        spine: StaticArity,
    },
    /// A static application's argument waits on its synthesised type, which
    /// then crosses the value bridge to the domain; the application so far
    /// has the codomain.
    StaticArgument
    {
        /// The argument.
        argument: ValueId,
        /// How many arguments stand before this one.
        position: ArgumentPosition,
        /// The static Pi's domain.
        domain: ValueTypeId,
        /// The static Pi's codomain.
        codomain: ValueTypeId,
    },
    /// A static application's static-lambda argument waits on its check
    /// against the domain; the application so far has the codomain.
    StaticOperand
    {
        /// The static Pi's codomain.
        codomain: ValueTypeId,
    },
    /// A total run checked a term that could not synthesise against the
    /// unknown type; the term synthesises the unknown type of its family.
    Unknowing(TermNode),
    /// A thunk waits on its body's check against the computation type it
    /// suspends.
    ThunkBody,
    /// A return waits on its value: checked against the result of the returner
    /// it is checked against, or synthesised for the pure returner the return
    /// then synthesises.
    ReturnValue,
    /// An injection waits on its payload's check against its summand.
    InjectionPayload,
    /// A splice's tactic's answer is checked against the splice's goal; the
    /// answer then fills the splice's hole.
    Spliced
    {
        /// The splice's hole, where it stands.
        at: ValueId,
        /// The hole, whose name carries the tactic.
        hole: HoleId,
        /// The tactic's answer.
        answer: ValueId,
    },
    /// A send waits on its payload's check; its endpoint then advances.
    SessionSend
    {
        /// The send.
        at: ComputationId,
        /// The endpoint.
        endpoint: DeBruijnIndex,
        /// The session type the endpoint advances to.
        next: ValueTypeId,
    },
    /// An offer's arm is being checked from the zone the offer found; the
    /// zone it leaves must agree with the first arm's.
    OfferArm
    {
        /// The offer.
        at: ComputationId,
        /// The arm's position among the arms, in label order.
        arm: Ordinal,
        /// The type every arm is checked against.
        expected: CompTypeId,
        /// Where the offer's kept zones begin.
        zones: session::ZoneMark,
    },
    /// A receive's body is being judged with its payload bound.
    ReceiveBody
    {
        /// The receive.
        at: ComputationId,
        /// The receive's own direction, which its body takes.
        direction: Direction<CompTypeId>,
    },
    /// A fork waits on its protocol annotation's formation.
    ForkProtocol
    {
        /// The fork.
        at: ComputationId,
        /// The fork's own direction, which its parent takes.
        direction: Direction<CompTypeId>,
    },
    /// A fork's child is being checked with its end bound.
    ForkChild
    {
        /// The fork.
        at: ComputationId,
        /// The fork's own direction, which its parent takes.
        direction: Direction<CompTypeId>,
        /// The child's session type, whose dual the parent's end takes.
        session: ValueTypeId,
    },
    /// A fork's parent is being judged with its end bound.
    ForkParent
    {
        /// The fork.
        at: ComputationId,
        /// The fork's own direction.
        direction: Direction<CompTypeId>,
    },
    /// A hold waits on its value's synthesis; the held slot then opens.
    HoldValue
    {
        /// The hold.
        at: ComputationId,
        /// The hold's own direction, which its scope takes.
        direction: Direction<CompTypeId>,
    },
    /// A hold's scope is being judged with the held slot bound.
    HoldBody
    {
        /// The hold.
        at: ComputationId,
        /// The hold's own direction.
        direction: Direction<CompTypeId>,
    },
    /// An access at a place waits on its index's check against the integer
    /// type; the place is then lent and the view opens at its element type.
    AccessIndex
    {
        /// The access.
        at: ComputationId,
        /// The access's own direction, which its body takes.
        direction: Direction<CompTypeId>,
    },
    /// An access's body is being judged with its view bound and its held
    /// slot lent.
    AccessBody
    {
        /// The access.
        at: ComputationId,
        /// The access's own direction.
        direction: Direction<CompTypeId>,
    },
    /// An access's unwind is being checked against the pure returner of the
    /// unit; the body's result then ascends.
    AccessUnwind
    {
        /// The access.
        at: ComputationId,
        /// What the body produced.
        produced: Produced,
    },
    /// A resume waits on its value's check; its view is then spent.
    ResumeValue
    {
        /// The resume.
        at: ComputationId,
        /// The view it ends.
        view: DeBruijnIndex,
    },
    /// A hold of a value at the current world waits on the value's synthesis.
    WorldHold
    {
        /// The hold.
        at: ComputationId,
    },
    /// A `leta` waits on its handle's synthesis; its binder then opens at the
    /// handle's world.
    LetaValue
    {
        /// The `leta`.
        at: ComputationId,
        /// The `leta`'s own direction, which its body takes.
        direction: Direction<CompTypeId>,
    },
    /// A `leta`'s body is being judged with its binder located.
    LetaBody
    {
        /// The `leta`.
        at: ComputationId,
    },
    /// A migration's body is being judged at the world it migrated to.
    MigrateBody
    {
        /// The migration.
        at: ComputationId,
        /// The world it left, which its result crosses back to.
        from: gandr_core_term::world::World,
        /// The migration's own direction.
        direction: Direction<CompTypeId>,
    },
}

/// A frame beside the goal under way when its rule pushed it: the node the
/// rule stands on.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct Waiting
{
    /// The frame.
    frame: Frame,
    /// The goal whose rule pushed it.
    owner: Goal,
}

/// What the machine was doing when a step refused.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Control
{
    /// Starting a goal.
    Starting(Goal),
    /// A popped frame's rule consuming its subterm's result.
    Resuming(Waiting),
    /// Handing a result to the frame on top of the stack, still unpopped.
    Handing,
}

/// A refused step: the refusal, and what the machine was doing.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct Halt
{
    /// The refusal.
    refusal: CheckRefusal,
    /// What the machine was doing.
    control: Control,
}

impl Frame
{
    /// The rule this frame stands for.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the role named after the frame's own variant, the fold's
    ///   premise carried across for a List fold.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a refusal under a thunk's force names each pending
    ///   rule by its own frame.
    /// - witness: `judgement::tests::a_refusal_keeps_the_rules_it_stood_inside`
    /// - witness: `judgement::tests::each_rule_a_refusal_stood_inside_is_named_by_its_own_role`
    #[spec(ensures: |ret| matches!(self, Self::ListFold { .. }) == matches!(ret, FrameRole::ListFold(_)))]
    const fn role(self) -> FrameRole
    {
        match self {
            // A foresight's open and close continue the case's premises.
            Self::NativeNext(_) | Self::NativeForesee(_) | Self::NativeForget(_) => {
                FrameRole::NativeNext
            },
            Self::NativeYield(_) => FrameRole::NativeYield,
            Self::NativeCollect => FrameRole::NativeCollect,
            Self::NativeDiscard => FrameRole::NativeDiscard,
            Self::NativeTuple { .. } => FrameRole::NativeTuple,
            Self::NativeRecord { .. } => FrameRole::NativeRecord,
            Self::NativeCase(_) => FrameRole::NativeCase,
            Self::NativeMotive { .. } => FrameRole::NativeMotive,
            Self::NativeRespect { .. } => FrameRole::NativeRespect,
            Self::NativeLoops { .. } => FrameRole::NativeLoops,
            Self::SigmaSplitScrutinee(_) => FrameRole::SigmaSplitScrutinee,
            Self::SigmaSplitMotive { .. } => FrameRole::SigmaSplitMotive,
            Self::NativeProjection(_) => FrameRole::NativeProjection,
            Self::Ascription { .. } => FrameRole::Ascription,
            Self::PerformPayload { .. } => FrameRole::PerformPayload,
            Self::Next(_) => FrameRole::Next,
            Self::Resume { .. } => FrameRole::Resume,
            Self::Abandon { .. } => FrameRole::Abandon,
            Self::Project { .. } => FrameRole::Project,
            Self::Reset { .. } => FrameRole::Reset,
            Self::HandlerForm { .. } => FrameRole::HandlerForm,
            Self::HandlerSubject { .. } => FrameRole::HandlerSubject,
            Self::HandlerReturn { .. } => FrameRole::HandlerReturn,
            Self::HandlerClause { .. } => FrameRole::HandlerClause,
            Self::ExerciseCapability { .. } => FrameRole::ExerciseCapability,
            Self::ScopeForm { .. } => FrameRole::ScopeForm,
            Self::ScopeSubject { .. } => FrameRole::ScopeSubject,
            Self::StackNext { .. } => FrameRole::StackNext,
            Self::StackBind { .. } => FrameRole::StackBind,
            Self::ListFold { phase, .. } => FrameRole::ListFold(match phase {
                ListPhase::Element => FoldPremise::Element,
                ListPhase::Result => FoldPremise::Result,
                ListPhase::Input => FoldPremise::Input,
                ListPhase::Nil => FoldPremise::Nil,
                ListPhase::Cons => FoldPremise::Cons,
            }),
            Self::PathProductFirst { .. } => FrameRole::PathProductFirst,
            Self::PathProductSecond { .. } => FrameRole::PathProductSecond,
            Self::PathBackward { .. } => FrameRole::PathBackward,
            Self::PathChecked { .. } => FrameRole::PathChecked,
            Self::PrimitiveSecond { .. } => FrameRole::PrimitiveSecond,
            Self::PrimitiveResult { .. } => FrameRole::PrimitiveResult,
            Self::TransportPath { .. } => FrameRole::TransportPath,
            Self::TransportOperand { .. } => FrameRole::TransportOperand,
            Self::HereSynthesised { .. } => FrameRole::HereSynthesised,
            Self::HereEndpoints { .. } => FrameRole::HereEndpoints,
            Self::FunextLeft { .. } => FrameRole::FunextLeft,
            Self::FunextRight { .. } => FrameRole::FunextRight,
            Self::EquivForward { .. } => FrameRole::EquivForward,
            Self::EquivBackward { .. } => FrameRole::EquivBackward,
            Self::UaTranslators { .. } => FrameRole::UaTranslators,
            Self::UnivalenceRecord { .. } => FrameRole::UnivalenceRecord,
            Self::UnivalenceChecked { .. } => FrameRole::UnivalenceChecked,
            Self::ReturnedEndpoint { .. } => FrameRole::ReturnedEndpoint,
            Self::Ran { .. } => FrameRole::Ran,
            Self::NestedCall { .. } => FrameRole::NestedCall,
            Self::ElementTransportPath { .. } => FrameRole::ElementTransportPath,
            Self::ElementTransportMotive { .. } => FrameRole::ElementTransportMotive,
            Self::TelescopePath { .. } => FrameRole::TelescopePath,
            Self::TelescopeMotive { .. } => FrameRole::TelescopeMotive,
            Self::TelescopeStart { .. } => FrameRole::TelescopeStart,
            Self::TelescopeOver { .. } => FrameRole::TelescopeOver,
            Self::CaseScrutinee { .. } => FrameRole::CaseScrutinee,
            Self::SplitScrutinee { .. } => FrameRole::SplitScrutinee,
            Self::SplitBody { .. } => FrameRole::SplitBody,
            Self::CaseBranch { .. } | Self::ArmEnded { .. } | Self::ArmsJoined { .. } => {
                FrameRole::CaseBranch
            },
            Self::ListCaseScrutinee { .. } => FrameRole::ListCaseScrutinee,
            Self::ListCaseNil { .. } => FrameRole::ListCaseNil,
            Self::ListCaseCons => FrameRole::ListCaseCons,
            Self::Force { .. } => FrameRole::Force,
            Self::Decompose { .. } => FrameRole::Decompose,
            Self::ApplicationHead { .. } => FrameRole::ApplicationHead,
            Self::ApplicationArgument { .. } => FrameRole::ApplicationArgument,
            Self::FixpointArgument { .. } => FrameRole::FixpointArgument,
            Self::LambdaBody => FrameRole::LambdaBody,
            Self::BindBound { .. } => FrameRole::BindBound,
            Self::BindBody { .. } => FrameRole::BindBody,
            Self::ValueBridge { .. } => FrameRole::ValueBridge,
            Self::CompBridge { .. } => FrameRole::CompBridge,
            Self::Quote(_) => FrameRole::Quote,
            Self::FormNext(_) => FrameRole::FormNext,
            Self::FormUnder {
                under: TypeNode::Computation(_),
                ..
            } => FrameRole::FormPi,
            Self::FormUnder {
                under: TypeNode::Value(_),
                ..
            } => FrameRole::FormSigma,
            Self::FormBinder => FrameRole::FormBinder,
            Self::FormLift(_) => FrameRole::FormLift,
            Self::FormElement(_) => FrameRole::FormElement,
            Self::FormStaticPi(_) => FrameRole::FormStaticPi,
            Self::RunProtocol => FrameRole::RunProtocol,
            Self::PairSecond { .. } => FrameRole::PairSecond,
            Self::StaticSpine { .. } => FrameRole::StaticSpine,
            Self::StaticArgument { .. } => FrameRole::StaticArgument,
            Self::StaticOperand { .. } => FrameRole::StaticOperand,
            Self::Unknowing(_) => FrameRole::Unknowing,
            Self::ThunkBody => FrameRole::ThunkBody,
            Self::ReturnValue => FrameRole::ReturnValue,
            Self::InjectionPayload => FrameRole::InjectionPayload,
            Self::Spliced { .. } => FrameRole::Spliced,
            Self::SessionSend { .. } => FrameRole::SessionSend,
            Self::OfferArm { .. } => FrameRole::OfferArm,
            Self::ForkProtocol { .. } => FrameRole::ForkProtocol,
            Self::ReceiveBody { .. } => FrameRole::ReceiveBody,
            Self::ForkChild { .. } => FrameRole::ForkChild,
            Self::ForkParent { .. } => FrameRole::ForkParent,
            Self::SessionStatement { .. } => FrameRole::SessionStatement,
            Self::SessionPayloads { .. } => FrameRole::SessionPayloads,
            Self::StaySynthesised { .. } => FrameRole::StaySynthesised,
            Self::ThenFirst { .. } => FrameRole::ThenFirst,
            Self::ThenSecond { .. } => FrameRole::ThenSecond,
            Self::FlowProductFirst { .. } => FrameRole::FlowProductFirst,
            Self::FlowProductSecond { .. } => FrameRole::FlowProductSecond,
            Self::UpdateBase { .. } => FrameRole::UpdateBase,
            Self::UpdateOverlay { .. } => FrameRole::UpdateOverlay,
            Self::RideFlow { .. } => FrameRole::RideFlow,
            Self::RideMotive { .. } => FrameRole::RideMotive,
            Self::RideValue { .. } => FrameRole::RideValue,
            Self::ForwardTranslator { .. } => FrameRole::ForwardTranslator,
            Self::ArrowDomain { .. } => FrameRole::ArrowDomain,
            Self::ArrowCodomain { .. } => FrameRole::ArrowCodomain,
            Self::ArrowAgainst { .. } => FrameRole::ArrowAgainst,
            Self::StayEndpoints { .. } => FrameRole::StayEndpoints,
            Self::HoldValue { .. } => FrameRole::HoldValue,
            Self::HoldBody { .. } => FrameRole::HoldBody,
            Self::AccessIndex { .. } => FrameRole::AccessIndex,
            Self::AccessBody { .. } => FrameRole::AccessBody,
            Self::AccessUnwind { .. } => FrameRole::AccessUnwind,
            Self::ResumeValue { .. } => FrameRole::ResumeValue,
            Self::WorldHold { .. } => FrameRole::WorldHold,
            Self::LetaValue { .. } => FrameRole::LetaValue,
            Self::LetaBody { .. } => FrameRole::LetaBody,
            Self::MigrateBody { .. } => FrameRole::MigrateBody,
        }
    }

    /// How many intuitionistic binders this frame holds open while it waits.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one for an abstraction body, a bind body, a `leta` body, a
    ///   formation under a binder, a return clause, a capability scope's
    ///   subject, a stack bind and a case motive; two for an operation clause
    ///   and a list case's cell branch; the component count for a split body;
    ///   zero otherwise.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a refusal under a bind attributes its one hypothesis
    ///   to the bind body; a miscount drops or misplaces it.
    /// - witness: `judgement::tests::a_refusal_under_a_bind_keeps_its_hypothesis`
    #[spec(ensures: |ret| usize::from(ret) <= 2 || matches!(self, Self::SplitBody { .. }))]
    fn opens(self) -> BinderDepth
    {
        BinderDepth::from(match self {
            Self::LambdaBody
            | Self::BindBody { .. }
            | Self::FormBinder
            | Self::HandlerReturn { .. }
            | Self::StackBind { .. }
            | Self::NativeMotive { .. }
            | Self::SigmaSplitMotive { .. }
            | Self::ScopeSubject { .. }
            | Self::LetaBody { .. } => 1_usize,
            Self::HandlerClause { .. } | Self::ListCaseCons => 2_usize,
            Self::SplitBody { arity, .. } => usize::from(arity),
            Self::NativeNext(_)
            | Self::NativeYield(_)
            | Self::NativeCollect
            | Self::NativeDiscard
            | Self::NativeTuple { .. }
            | Self::NativeRecord { .. }
            | Self::NativeCase(_)
            | Self::NativeRespect { .. }
            | Self::NativeLoops { .. }
            | Self::NativeForesee(_)
            | Self::NativeForget(_)
            | Self::SigmaSplitScrutinee(_)
            | Self::NativeProjection(_)
            | Self::Ascription { .. }
            | Self::PerformPayload { .. }
            | Self::Next(_)
            | Self::Resume { .. }
            | Self::Abandon { .. }
            | Self::Project { .. }
            | Self::Reset { .. }
            | Self::HandlerForm { .. }
            | Self::HandlerSubject { .. }
            | Self::ExerciseCapability { .. }
            | Self::ScopeForm { .. }
            | Self::StackNext { .. }
            | Self::ListFold { .. }
            | Self::PathProductFirst { .. }
            | Self::PathProductSecond { .. }
            | Self::PathBackward { .. }
            | Self::PathChecked { .. }
            | Self::PrimitiveSecond { .. }
            | Self::PrimitiveResult { .. }
            | Self::TransportPath { .. }
            | Self::TransportOperand { .. }
            | Self::HereSynthesised { .. }
            | Self::HereEndpoints { .. }
            | Self::FunextLeft { .. }
            | Self::FunextRight { .. }
            | Self::EquivForward { .. }
            | Self::EquivBackward { .. }
            | Self::UaTranslators { .. }
            | Self::UnivalenceRecord { .. }
            | Self::UnivalenceChecked { .. }
            | Self::ReturnedEndpoint { .. }
            | Self::Ran { .. }
            | Self::NestedCall { .. }
            | Self::ElementTransportPath { .. }
            | Self::ElementTransportMotive { .. }
            | Self::TelescopePath { .. }
            | Self::TelescopeMotive { .. }
            | Self::TelescopeStart { .. }
            | Self::TelescopeOver { .. }
            | Self::CaseScrutinee { .. }
            | Self::SplitScrutinee { .. }
            | Self::CaseBranch { .. }
            | Self::ArmEnded { .. }
            | Self::ArmsJoined { .. }
            | Self::ListCaseScrutinee { .. }
            | Self::ListCaseNil { .. }
            | Self::Force { .. }
            | Self::Decompose { .. }
            | Self::ApplicationHead { .. }
            | Self::ApplicationArgument { .. }
            | Self::FixpointArgument { .. }
            | Self::BindBound { .. }
            | Self::ValueBridge { .. }
            | Self::CompBridge { .. }
            | Self::Quote(_)
            | Self::FormNext(_)
            | Self::FormUnder { .. }
            | Self::FormLift(_)
            | Self::FormElement(_)
            | Self::FormStaticPi(_)
            | Self::RunProtocol
            | Self::PairSecond { .. }
            | Self::StaticSpine { .. }
            | Self::StaticArgument { .. }
            | Self::StaticOperand { .. }
            | Self::Unknowing(_)
            | Self::ThunkBody
            | Self::ReturnValue
            | Self::InjectionPayload
            | Self::Spliced { .. }
            | Self::SessionSend { .. }
            | Self::OfferArm { .. }
            | Self::ForkProtocol { .. }
            | Self::ForkChild { .. }
            | Self::ReceiveBody { .. }
            | Self::ForkParent { .. }
            | Self::SessionStatement { .. }
            | Self::SessionPayloads { .. }
            | Self::StaySynthesised { .. }
            | Self::ThenFirst { .. }
            | Self::ThenSecond { .. }
            | Self::FlowProductFirst { .. }
            | Self::FlowProductSecond { .. }
            | Self::UpdateBase { .. }
            | Self::UpdateOverlay { .. }
            | Self::RideFlow { .. }
            | Self::RideMotive { .. }
            | Self::RideValue { .. }
            | Self::ForwardTranslator { .. }
            | Self::ArrowDomain { .. }
            | Self::ArrowCodomain { .. }
            | Self::ArrowAgainst { .. }
            | Self::StayEndpoints { .. }
            | Self::HoldValue { .. }
            | Self::HoldBody { .. }
            | Self::AccessIndex { .. }
            | Self::AccessBody { .. }
            | Self::AccessUnwind { .. }
            | Self::ResumeValue { .. }
            | Self::WorldHold { .. }
            | Self::LetaValue { .. }
            | Self::MigrateBody { .. } => 0_usize,
        })
    }
}

/// The node `goal` judges or forms and the type it is checked against.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a value or computation goal's term with its expected type when
///   checking and [`judged::Absent::Synthesised`] when synthesising; a stack
///   goal's literal with the stack type it is checked against; a formation
///   goal's type with [`judged::Absent::Formed`].
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a refusal under a thunk names each enclosing node with
///   the type it was checked against.
/// - witness: `judgement::tests::a_refusal_keeps_the_rules_it_stood_inside`
#[spec(ensures: |ret| matches!(goal, Goal::Form(_)) == matches!(ret.0, CoreNode::Type(_)))]
const fn judged(goal: Goal) -> (CoreNode, Maybe<TypeNode, judged::Absent>)
{
    match goal {
        Goal::Stack { judgement, .. } => (
            CoreNode::Term(TermNode::Value(judgement.at)),
            Maybe::Present(TypeNode::Value(judgement.expected)),
        ),
        Goal::Value { term, direction } => {
            (CoreNode::Term(TermNode::Value(term)), match direction {
                Direction::Check(expected) => Maybe::Present(TypeNode::Value(expected)),
                Direction::Synthesise => Maybe::Absent(judged::Absent::Synthesised),
            })
        },
        Goal::Computation { term, direction } => (
            CoreNode::Term(TermNode::Computation(term)),
            match direction {
                Direction::Check(expected) => Maybe::Present(TypeNode::Computation(expected)),
                Direction::Synthesise => Maybe::Absent(judged::Absent::Synthesised),
            },
        ),
        Goal::Form(node) => (CoreNode::Type(node), Maybe::Absent(judged::Absent::Formed)),
    }
}

/// The machine's next move.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Step
{
    /// Start a judgement.
    Descend(Goal),
    /// Hand a finished judgement's result to the innermost frame.
    Ascend(Produced),
}

/// One run of the judgement: the context, the frames, the conversions made
/// and the allowance left; in a total run, the terms it would recover at and
/// the refusals it marked.
struct Machine<'context, 'arena>
{
    /// The context the run reads and goes under binders in.
    context: &'context mut CheckingContext<'arena>,
    /// The rules waiting on subterms, innermost last, each beside the goal
    /// whose rule pushed it.
    frames: Vec<Waiting>,
    /// The goal whose rule is running: the one started last, or the owner of
    /// the frame resumed last.
    owner: Goal,
    /// Inferred record field types; nested records own separate suffixes.
    native_types: Vec<ValueTypeId>,
    /// The crossings of the conversion boundary so far.
    conversions: ConversionCount,
    /// The steps left before the run refuses.
    remaining: usize,
    /// Whether a refusal ends the run or marks the term it stands at.
    marking: Marking,
    /// The term judgements under way, innermost last; empty in a strict run
    /// unless the context records typings.
    anchors: Vec<Anchor>,
    /// The refusals a total run marked, in the order met.
    marks: Vec<MarkEntry>,
    /// The endpoints the run bound and the zones its offers keep.
    sessions: Sessions,
    /// The case a structural fixpoint checked last opens with, beside how it
    /// reads against its type's rules: taken by the next case the run meets,
    /// which is that one, since the fixpoint's body is `λy. case y`.
    root: Maybe<(ComputationId, crate::respect::Reading), crate::respect::root::Absent>,
    /// The cases checked at a staged result, each beside the motive its
    /// branches read ([`crate::recursion::motive_at`]): set where the case is
    /// checked, taken where its branches are.
    staged_motives: Vec<(ComputationId, CompTypeId)>,
    /// The images of the thunks a migration's body forms.
    images: worlds::Images,
}

impl<'context, 'arena> Machine<'context, 'arena>
{
    /// Read the two endpoints of a first-class stack classifier.
    ///
    /// # Specification
    /// - ensures: success returns the weak-head stack's input and output, or
    ///   two unknown computation types when the classifier is unknown.
    /// - fails: a shape mismatch names the original value and classifier.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — differing endpoints and a non-stack separate the
    ///   rule; the unknown type reads as a stack of unknowns.
    /// - witness: `judgement::tests::control_rules_preserve_rows_scopes_and_shapes`
    /// - witness: `judgement::tests::an_introduction_against_the_unknown_type_checks_its_parts`
    #[spec(ensures: |ret| match ret { Err(CheckRefusal::ShapeMismatch { at: site, wanted, found }) => site == TermNode::Value(at) && wanted == ExpectedShape::Stack && found == TypeNode::Value(classifier), Ok((input, output)) => self.context.arena().comp_type(input).is_some() && self.context.arena().comp_type(output).is_some(), Err(_) => true })]
    fn stack_expected(
        &mut self,
        at: ValueId,
        classifier: ValueTypeId,
    ) -> Result<(CompTypeId, CompTypeId), CheckRefusal>
    {
        let head = self.context.whnf_value_type(classifier)?;
        match matched_stack(self.context.arena_mut(), head) {
            Maybe::Present(endpoints) => Ok(endpoints),
            Maybe::Absent(absent) => Err(unmatched(
                absent,
                TypeNode::Value(head),
                CheckRefusal::ShapeMismatch {
                    at: TermNode::Value(at),
                    wanted: ExpectedShape::Stack,
                    found: TypeNode::Value(classifier),
                },
            )),
        }
    }

    /// Read a lazy product without evaluating any component.
    ///
    /// # Specification
    /// - ensures: the components retain their order; an unknown classifier
    ///   reads as one unknown type every component stands at.
    /// - fails: a non-With classifier is a named shape mismatch.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — distinct component types expose selecting the wrong
    ///   component.
    /// - witness: `judgement::tests::control_rules_preserve_rows_scopes_and_shapes`
    /// - witness: `judgement::tests::an_introduction_against_the_unknown_type_checks_its_parts`
    #[spec(ensures: |ret| match ret {
        | Err(CheckRefusal::ShapeMismatch { at: site, wanted, found }) => site == at && wanted == ExpectedShape::With && found == TypeNode::Computation(classifier),
        | Ok(Components::Known(ref parts)) => parts.iter().all(|&part| self.context.arena().comp_type(part).is_some()),
        | Ok(Components::Unknown(unknown)) => self.context.arena().comp_type(unknown).is_some(),
        | Err(_) => true,
    })]
    fn with_parts(
        &mut self,
        at: TermNode,
        classifier: CompTypeId,
    ) -> Result<Components<CompTypeId>, CheckRefusal>
    {
        let head = crate::codata::read(self.context, classifier)?;
        match matched_with(self.context.arena_mut(), head) {
            Maybe::Present(components) => Ok(components),
            Maybe::Absent(absent) => Err(unmatched(
                absent,
                TypeNode::Computation(head),
                CheckRefusal::ShapeMismatch {
                    at,
                    wanted: ExpectedShape::With,
                    found: TypeNode::Computation(classifier),
                },
            )),
        }
    }

    /// Read an application domain and distinguish ambient from dependent
    /// output.
    ///
    /// # Specification
    /// - ensures: a Pi's codomain remains under its argument binder.
    /// - fails: a non-function is a shape mismatch at the calling term.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — dependent stack application must substitute its
    ///   argument.
    /// - witness: `judgement::tests::control_rules_preserve_rows_scopes_and_shapes`
    #[spec(ensures: |ret| match ret { Err(CheckRefusal::ShapeMismatch { at: site, wanted, found }) => site == at && wanted == ExpectedShape::Arrow && found == TypeNode::Computation(classifier), Ok((domain, _)) => self.context.arena().value_type(domain).is_some(), Err(_) => true })]
    fn application_type(
        &mut self,
        at: TermNode,
        classifier: CompTypeId,
    ) -> Result<(ValueTypeId, Codomain), CheckRefusal>
    {
        let head = crate::codata::read(self.context, classifier)?;
        match matched_function(self.context.arena_mut(), head) {
            Maybe::Present(function) => Ok((function.domain(), match function.scope() {
                CodomainScope::Ambient => Codomain::Ambient(function.codomain()),
                CodomainScope::UnderBinder => Codomain::Dependent(function.codomain()),
            })),
            Maybe::Absent(absent) => Err(unmatched(
                absent,
                TypeNode::Computation(head),
                CheckRefusal::ShapeMismatch {
                    at,
                    wanted: ExpectedShape::Arrow,
                    found: TypeNode::Computation(classifier),
                },
            )),
        }
    }

    /// Advance a flat stack from its consumed type, one frame per machine step.
    ///
    /// # Specification
    /// - ensures: only Bind opens a value binder; later stack frames are
    ///   ambient.
    /// - fails: mismatched frame shapes, operands, or delivered endpoint.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an interior bind and a dependent application expose
    ///   row loss and accidental capture by a preceding frame's binder.
    /// - witness: `judgement::tests::control_rules_preserve_rows_scopes_and_shapes`
    #[spec(captures: depth = usize::from(self.context.depth(Zone::Intuitionistic)),
        ensures: |ret| ret.is_err() || usize::from(self.context.depth(Zone::Intuitionistic)) == if matches!(self.context.arena().value(judgement.at), Some(Value::Reify(frames)) if matches!(frames.get(position.0), Some(gandr_core_term::control::StackFrame::Bind(_)))) { depth.saturating_add(1) } else { depth })]
    fn stack_step(
        &mut self,
        judgement: StackJudgement,
        position: Ordinal,
        input: CompTypeId,
    ) -> Result<Step, CheckRefusal>
    {
        let Value::Reify(ref frames) = *self.value(judgement.at)?
        else {
            return Err(CheckRefusal::MachineInvariant);
        };
        let Some(frame) = frames.get(position.0).copied()
        else {
            let actual = self
                .context
                .arena_mut()
                .value_type_stack(judgement.consumed, input);
            value_bridge(
                self.context,
                judgement.at,
                actual,
                judgement.expected,
                &mut self.conversions,
            )?;
            return Ok(Step::Ascend(Produced::Checked));
        };
        let position = position.next()?;
        match frame {
            gandr_core_term::control::StackFrame::Apply(argument) => {
                let (domain, codomain) =
                    self.application_type(TermNode::Value(judgement.at), input)?;
                self.wait(Frame::StackNext {
                    judgement,
                    position,
                });
                self.wait(Frame::ApplicationArgument {
                    head: None,
                    argument,
                    domain,
                    codomain,
                });
                Ok(Step::Descend(Goal::Value {
                    term: argument,
                    direction: Direction::Check(domain),
                }))
            },
            gandr_core_term::control::StackFrame::Bind(body) => {
                let head = self.context.whnf_comp_type(input)?;
                let CompTypeView::Returner { result, .. } =
                    comp_type_view(self.context.arena(), head)?
                else {
                    return Err(CheckRefusal::ShapeMismatch {
                        at: TermNode::Value(judgement.at),
                        wanted: ExpectedShape::Returner,
                        found: TypeNode::Computation(input),
                    });
                };
                self.context.binders().open(Zone::Intuitionistic, result);
                self.wait(Frame::StackNext {
                    judgement,
                    position,
                });
                self.wait(Frame::StackBind {
                    at: judgement.at,
                    body,
                    bound: head,
                });
                Ok(Step::Descend(Goal::Computation {
                    term: body,
                    direction: Direction::Synthesise,
                }))
            },
            gandr_core_term::control::StackFrame::Project(component) => {
                let input =
                    match self.with_parts(TermNode::Value(judgement.at), input)? {
                        Components::Known(parts) => *parts.get(usize::from(component)).ok_or(
                            CheckRefusal::ShapeMismatch {
                                at: TermNode::Value(judgement.at),
                                wanted: ExpectedShape::With,
                                found: TypeNode::Computation(input),
                            },
                        )?,
                        Components::Unknown(unknown) => unknown,
                    };
                Ok(Step::Descend(Goal::Stack {
                    judgement,
                    position,
                    input,
                }))
            },
        }
    }

    /// Check a shift under the nearest reset's answer, weakened to this scope.
    ///
    /// # Specification
    /// - ensures: success opens exactly the captured stack's binder.
    /// - fails: a shift without an answer delimiter is named at its source.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — nested resets and an intervening binder distinguish
    ///   scope.
    /// - witness: `judgement::tests::control_rules_preserve_rows_scopes_and_shapes`
    #[spec(captures: depth = usize::from(self.context.depth(Zone::Intuitionistic)), ensures: |ret| ret.is_err() || usize::from(self.context.depth(Zone::Intuitionistic)) == depth.saturating_add(1))]
    fn shift(
        &mut self,
        at: ComputationId,
        body: ComputationId,
        captured: CompTypeId,
    ) -> Result<Step, CheckRefusal>
    {
        // A migration delimits control: a shift in its body captures no
        // continuation past it, which would run at the world it left.
        let Some((answer, depth)) = self
            .frames
            .iter()
            .rev()
            .take_while(|waiting| !matches!(waiting.frame, Frame::MigrateBody { .. }))
            .find_map(|waiting| match waiting.frame {
                Frame::Reset { answer, depth } => Some((answer, depth)),
                Frame::NativeNext(_)
                | Frame::NativeYield(_)
                | Frame::NativeCollect
                | Frame::NativeDiscard
                | Frame::NativeTuple { .. }
                | Frame::NativeRecord { .. }
                | Frame::NativeCase(_)
                | Frame::NativeMotive { .. }
                | Frame::NativeRespect { .. }
                | Frame::NativeLoops { .. }
                | Frame::NativeForesee(_)
                | Frame::NativeForget(_)
                | Frame::SigmaSplitScrutinee(_)
                | Frame::SigmaSplitMotive { .. }
                | Frame::NativeProjection(_)
                | Frame::Ascription { .. }
                | Frame::PerformPayload { .. }
                | Frame::Next(_)
                | Frame::Resume { .. }
                | Frame::Abandon { .. }
                | Frame::Project { .. }
                | Frame::HandlerForm { .. }
                | Frame::HandlerSubject { .. }
                | Frame::HandlerReturn { .. }
                | Frame::HandlerClause { .. }
                | Frame::ExerciseCapability { .. }
                | Frame::ScopeForm { .. }
                | Frame::ScopeSubject { .. }
                | Frame::StackNext { .. }
                | Frame::StackBind { .. }
                | Frame::ListFold { .. }
                | Frame::PathProductFirst { .. }
                | Frame::PathProductSecond { .. }
                | Frame::PathBackward { .. }
                | Frame::PathChecked { .. }
                | Frame::PrimitiveSecond { .. }
                | Frame::PrimitiveResult { .. }
                | Frame::TransportPath { .. }
                | Frame::TransportOperand { .. }
                | Frame::HereSynthesised { .. }
                | Frame::HereEndpoints { .. }
                | Frame::FunextLeft { .. }
                | Frame::FunextRight { .. }
                | Frame::EquivForward { .. }
                | Frame::EquivBackward { .. }
                | Frame::UaTranslators { .. }
                | Frame::UnivalenceRecord { .. }
                | Frame::UnivalenceChecked { .. }
                | Frame::ReturnedEndpoint { .. }
                | Frame::Ran { .. }
                | Frame::NestedCall { .. }
                | Frame::ElementTransportPath { .. }
                | Frame::ElementTransportMotive { .. }
                | Frame::SessionStatement { .. }
                | Frame::SessionPayloads { .. }
                | Frame::StaySynthesised { .. }
                | Frame::ThenFirst { .. }
                | Frame::ThenSecond { .. }
                | Frame::FlowProductFirst { .. }
                | Frame::FlowProductSecond { .. }
                | Frame::UpdateBase { .. }
                | Frame::UpdateOverlay { .. }
                | Frame::RideFlow { .. }
                | Frame::RideMotive { .. }
                | Frame::RideValue { .. }
                | Frame::ForwardTranslator { .. }
                | Frame::ArrowDomain { .. }
                | Frame::ArrowCodomain { .. }
                | Frame::ArrowAgainst { .. }
                | Frame::StayEndpoints { .. }
                | Frame::TelescopePath { .. }
                | Frame::TelescopeMotive { .. }
                | Frame::TelescopeStart { .. }
                | Frame::TelescopeOver { .. }
                | Frame::CaseScrutinee { .. }
                | Frame::SplitScrutinee { .. }
                | Frame::SplitBody { .. }
                | Frame::CaseBranch { .. }
                | Frame::ArmEnded { .. }
                | Frame::ArmsJoined { .. }
                | Frame::ListCaseScrutinee { .. }
                | Frame::ListCaseNil { .. }
                | Frame::ListCaseCons
                | Frame::Force { .. }
                | Frame::Decompose { .. }
                | Frame::ApplicationHead { .. }
                | Frame::ApplicationArgument { .. }
                | Frame::FixpointArgument { .. }
                | Frame::LambdaBody
                | Frame::BindBound { .. }
                | Frame::BindBody { .. }
                | Frame::ValueBridge { .. }
                | Frame::CompBridge { .. }
                | Frame::Quote(_)
                | Frame::FormNext(_)
                | Frame::FormUnder { .. }
                | Frame::FormBinder
                | Frame::FormLift(_)
                | Frame::FormElement(_)
                | Frame::FormStaticPi(_)
                | Frame::RunProtocol
                | Frame::PairSecond { .. }
                | Frame::StaticSpine { .. }
                | Frame::StaticArgument { .. }
                | Frame::StaticOperand { .. }
                | Frame::Unknowing(_)
                | Frame::ThunkBody
                | Frame::ReturnValue
                | Frame::InjectionPayload
                | Frame::Spliced { .. }
                | Frame::SessionSend { .. }
                | Frame::OfferArm { .. }
                | Frame::ForkProtocol { .. }
                | Frame::ForkChild { .. }
                | Frame::ReceiveBody { .. }
                | Frame::ForkParent { .. }
                | Frame::HoldValue { .. }
                | Frame::HoldBody { .. }
                | Frame::AccessIndex { .. }
                | Frame::AccessBody { .. }
                | Frame::AccessUnwind { .. }
                | Frame::ResumeValue { .. }
                | Frame::WorldHold { .. }
                | Frame::LetaValue { .. }
                | Frame::LetaBody { .. }
                | Frame::MigrateBody { .. } => None,
            })
        else {
            return Err(CheckRefusal::ShiftWithoutReset { at });
        };
        let added = usize::from(self.context.depth(Zone::Intuitionistic))
            .checked_sub(usize::from(depth))
            .ok_or(CheckRefusal::MachineInvariant)?;
        let added = u32::try_from(added).map_err(|_overflow| CheckRefusal::MachineInvariant)?;
        let answer = shift_comp_type(self.context.arena_mut(), answer, Binders::from(added))
            .settle(self.context.arena_mut());
        let stack = self.context.arena_mut().value_type_stack(captured, answer);
        let expected = shift_comp_type(self.context.arena_mut(), answer, Binders::from(1_u32))
            .settle(self.context.arena_mut());
        self.context.binders().open(Zone::Intuitionistic, stack);
        self.wait(Frame::LambdaBody);
        Ok(Step::Descend(Goal::Computation {
            term: body,
            direction: Direction::Check(expected),
        }))
    }

    /// Form a handler's interface after checking exact clause coverage.
    ///
    /// # Specification
    /// - ensures: a complete clause set and one pending subject judgment.
    /// - fails: missing, repeated and unknown clauses are malformed source.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — distinct operation names separate exact coverage from
    ///   count.
    /// - witness: `judgement::tests::handlers_discharge_only_their_own_interface`
    #[spec(captures: depth = self.frames.len(), ensures: |ret| ret.is_err() || (self.frames.len() == depth.saturating_add(1) && matches!(self.frames.last(), Some(Waiting { frame: Frame::HandlerForm { at: site, .. }, .. }) if *site == at)))]
    fn handle(
        &mut self,
        at: ComputationId,
        answer: CompTypeId,
    ) -> Result<Step, CheckRefusal>
    {
        let result = self.returner_expected(at, answer)?;
        let Computation::Handle {
            ref signature,
            ref clauses,
            ..
        } = *self.computation(at)?
        else {
            return Err(CheckRefusal::MachineInvariant);
        };
        if signature.operations().len() != clauses.len() {
            return Err(CheckRefusal::HandlerCoverage { at });
        }
        let mut names: Vec<_> = clauses.iter().map(|clause| &clause.operation).collect();
        names.sort_unstable();
        if !names
            .into_iter()
            .zip(signature.operations())
            .all(|(name, operation)| name == &operation.name)
        {
            return Err(CheckRefusal::HandlerCoverage { at });
        }
        let effects = gandr_core_term::effect::EffectRow::singleton(signature.clone());
        let interface = self
            .context
            .arena_mut()
            .comp_type_returner_with_effects(result, effects);
        self.wait(Frame::HandlerForm {
            at,
            answer,
            interface,
        });
        Ok(Step::Descend(Goal::Form(TypeNode::Computation(interface))))
    }

    /// Check a handler's residual row and open its return clause.
    ///
    /// # Specification
    /// - ensures: only this handler's interface is discharged, and never
    ///   [`gandr_core_term::effect::host::DIV`], which no handler eliminates: a
    ///   handler of it leaves it in the residual row; success binds the
    ///   subject's returned payload, not the handler's answer payload.
    /// - fails: conflicting signatures, a non-returner or leaked effects.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an unrelated effect and distinct payload types expose
    ///   loss; a handler of `Div` over a diverging call leaks it.
    /// - witness: `judgement::tests::handlers_discharge_only_their_own_interface`
    /// - witness: `divergence::tests::no_handler_discharges_div`
    #[spec(captures: depth = usize::from(self.context.depth(Zone::Intuitionistic)), ensures: |ret| ret.is_err() || usize::from(self.context.depth(Zone::Intuitionistic)) == depth.saturating_add(1))]
    fn handle_subject(
        &mut self,
        at: ComputationId,
        answer: CompTypeId,
        interface: CompTypeId,
        subject: CompTypeId,
    ) -> Result<Step, CheckRefusal>
    {
        let answer_result = self.returner_expected(at, answer)?;
        let head = self.context.whnf_comp_type(subject)?;
        let CompTypeView::Returner { result, effects } =
            comp_type_view(self.context.arena(), head)?
        else {
            return Err(CheckRefusal::ShapeMismatch {
                at: TermNode::Computation(at),
                wanted: ExpectedShape::Returner,
                found: TypeNode::Computation(subject),
            });
        };
        let Computation::Handle {
            ref signature,
            ref on_return,
            ..
        } = *self.computation(at)?
        else {
            return Err(CheckRefusal::MachineInvariant);
        };
        if effects.signatures().any(|held| {
            held.name() == signature.name()
                && held.inclusion(signature, self.context.arena())
                    == gandr_core_term::row::RowInclusion::Excluded
        }) {
            return Err(CheckRefusal::EffectSignatureConflict {
                at,
                first: subject,
                second: interface,
            });
        }
        // Divergence has no operation to answer: a handler of it runs its
        // subject, which may still run forever.
        let residual = if signature.name().as_ref() == gandr_core_term::effect::host::DIV {
            effects.clone()
        }
        else {
            effects.without(&gandr_core_term::effect::EffectLabel::Interface(
                gandr_core_term::row::Label::from(signature.name()),
            ))
        };
        let on_return = *on_return;
        let level = level_of(self.context, TypeNode::Value(result))?;
        self.context.record_handled(at, crate::handler::Handled {
            subject: result,
            answer,
            level,
        });
        let natural = self
            .context
            .arena_mut()
            .comp_type_returner_with_effects(answer_result, residual);
        comp_bridge(self.context, at, natural, answer, &mut self.conversions)?;
        let expected = shift_comp_type(self.context.arena_mut(), answer, Binders::from(1_u32))
            .settle(self.context.arena_mut());
        self.context.binders().open(Zone::Intuitionistic, result);
        self.wait(Frame::HandlerReturn { at, answer });
        Ok(Step::Descend(Goal::Computation {
            term: on_return,
            direction: Direction::Check(expected),
        }))
    }

    /// Open one deep operation clause of a handler or a capability scope:
    /// payload first, resumption second. A scope's clause whose operation's
    /// continuation captured a live resident owes that continuation exactly
    /// one end, which a linear slot opened beside the stack tracks.
    ///
    /// # Specification
    /// - ensures: the resumption consumes the operation reply with the answer's
    ///   row and delivers the answer; an unknown answer, which `handle` read
    ///   through the matched returner, contributes the empty row. Completing
    ///   the clause list opens no binder and drops the scope's capture records.
    /// - fails: inconsistent private continuation state or existing type
    ///   faults.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — unlike payload/reply/answer types expose swapped
    ///   binders; a handler with clauses checked against the unknown answer
    ///   exposes a reader that demands a known returner; a clause whose
    ///   operation captured an endpoint owes its continuation.
    /// - witness: `judgement::tests::handlers_discharge_only_their_own_interface`
    /// - witness: `judgement::tests::handle_against_unknown_answer`
    /// - witness: `judgement::session::tests::a_clause_ends_a_continuation_holding_an_obligation_once_1334`
    #[spec(captures: depth = usize::from(self.context.depth(Zone::Intuitionistic)), ensures: |ret| ret.is_err() || usize::from(self.context.depth(Zone::Intuitionistic)) == if matches!(ret, Ok(Step::Ascend(Produced::Checked))) { depth } else { depth.saturating_add(2) })]
    fn handle_clause(
        &mut self,
        at: ComputationId,
        answer: CompTypeId,
        position: Ordinal,
    ) -> Result<Step, CheckRefusal>
    {
        let (Computation::Handle {
            ref signature,
            ref clauses,
            ..
        }
        | Computation::Scope {
            ref signature,
            ref clauses,
            ..
        }) = *self.computation(at)?
        else {
            return Err(CheckRefusal::MachineInvariant);
        };
        let Some(clause) = clauses.get(position.0)
        else {
            self.sessions.owing.retain(|&(scope, _)| scope != at);
            return Ok(Step::Ascend(Produced::Checked));
        };
        let Maybe::Present(operation) = signature.operation(&clause.operation)
        else {
            return Err(CheckRefusal::MachineInvariant);
        };
        let (payload, reply, body) = (operation.payload, operation.reply, clause.body);
        let owes = self
            .sessions
            .owing
            .iter()
            .any(|&(scope, ref name)| scope == at && *name == clause.operation);
        // An operation replying a buffer has the scope mint it: the clause
        // receives the payload paired with the buffer, and resumes with it.
        let minted = self.context.whnf_value_type(reply)?;
        let payload = if matches!(
            value_type_view(self.context.arena(), minted)?,
            ValueTypeView::Buffer
        ) {
            self.context
                .arena_mut()
                .value_type_product(&[payload, reply])
        }
        else {
            payload
        };
        let head = self.context.whnf_comp_type(answer)?;
        let effects = match comp_type_view(self.context.arena(), head)? {
            CompTypeView::Returner { effects, .. } => effects.clone(),
            CompTypeView::Unknown => gandr_core_term::effect::EffectRow::EMPTY,
            CompTypeView::Element { .. }
            | CompTypeView::Arrow { .. }
            | CompTypeView::Pi { .. }
            | CompTypeView::With(..)
            | CompTypeView::Codata { .. } => return Err(CheckRefusal::MachineInvariant),
        };
        let input = self
            .context
            .arena_mut()
            .comp_type_returner_with_effects(reply, effects);
        let stack = self.context.arena_mut().value_type_stack(input, answer);
        let stack = shift_value_type(self.context.arena_mut(), stack, Binders::from(1_u32))
            .settle(self.context.arena_mut());
        let expected = shift_comp_type(self.context.arena_mut(), answer, Binders::from(2_u32))
            .settle(self.context.arena_mut());
        let position = position.next()?;
        self.context.binders().open(Zone::Intuitionistic, payload);
        if owes {
            self.owe(body, stack)?;
        }
        self.context.binders().open(Zone::Intuitionistic, stack);
        self.wait(Frame::HandlerClause {
            at,
            answer,
            position,
        });
        Ok(Step::Descend(Goal::Computation {
            term: body,
            direction: Direction::Check(expected),
        }))
    }

    /// The depth of the regions enclosing the next capability scope, each
    /// counted by the frame waiting on its body — a scope's subject or a
    /// hold's scope.
    ///
    /// # Specification
    /// - ensures: the number of waiting [`Frame::ScopeSubject`] and
    ///   [`Frame::HoldBody`] frames.
    /// - fails: [`CheckRefusal::MachineInvariant`] past the depth a region
    ///   counts.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::next_region`].
    /// - witness: `capability::tests::a_scoped_capability_never_leaves_its_scope`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body counts the waiting region frames once; the check counts them once more"
        )
    )]
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |&open| usize::try_from(u32::from(open)).ok() == Some(self.frames.iter().filter(|waiting| matches!(waiting.frame, Frame::ScopeSubject { .. } | Frame::HoldBody { .. })).count())))]
    fn regions_open(&self) -> Result<RegionDepth, CheckRefusal>
    {
        u32::try_from(
            self.frames
                .iter()
                .filter(|waiting| {
                    matches!(
                        waiting.frame,
                        Frame::ScopeSubject { .. } | Frame::HoldBody { .. }
                    )
                })
                .count(),
        )
        .map(RegionDepth::from)
        .map_err(|_overflow| CheckRefusal::MachineInvariant)
    }

    /// The region the next capability scope introduces: one deeper than every
    /// region enclosing it.
    ///
    /// # Specification
    /// - ensures: [`Region::Scoped`] at one past [`Self::regions_open`].
    /// - fails: [`CheckRefusal::MachineInvariant`] past the depth a region
    ///   counts.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a scope nested in another's subject introduces its
    ///   capability at depth two, and its escape is refused at that depth.
    /// - witness: `capability::tests::a_scoped_capability_never_leaves_its_scope`
    #[spec(ensures: |ret| ret.is_err() || matches!(ret, Ok(Region::Scoped(_))))]
    fn next_region(&self) -> Result<Region, CheckRefusal>
    {
        let depth = u32::from(self.regions_open()?)
            .checked_add(1)
            .ok_or(CheckRefusal::MachineInvariant)?;
        Ok(Region::Scoped(RegionDepth::from(depth)))
    }

    /// The region the next capability scope's answer lands in: the innermost
    /// region enclosing the scope, or at depth zero the definition's own body.
    ///
    /// # Specification
    /// - ensures: [`Region::Scoped`] at [`Self::regions_open`].
    /// - fails: [`CheckRefusal::MachineInvariant`] past the depth a region
    ///   counts.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a scope answering its own capability is refused at
    ///   the region around it, and one answering a value kept at a region its
    ///   definition abstracts checks.
    /// - witness: `capability::tests::a_scoped_capability_never_leaves_its_scope`
    /// - witness: `capability::tests::a_bound_region_outlives_every_scope_and_no_held_one_1221`
    #[spec(ensures: |ret| ret.is_err() || matches!(ret, Ok(Region::Scoped(_))))]
    fn enclosing_region(&self) -> Result<Region, CheckRefusal>
    {
        Ok(Region::Scoped(self.regions_open()?))
    }

    /// Type an operation exercised through a capability, once the capability
    /// synthesised `classifier`: the Exercise rule. The host answers an
    /// operation through a capability it holds exactly once; a scope's clause
    /// answers one through the scope's capability with the rest of the scope
    /// as a continuation, which the clause then owes exactly one end when it
    /// holds a live resident.
    ///
    /// # Specification
    /// - requires: `at` is an exercise whose capability synthesised
    ///   `classifier`.
    /// - ensures: the payload is checked against the operation's payload type
    ///   next, and the exercise synthesises the returner of the operation's
    ///   reply whose row is the operation's interface alone, labelled by the
    ///   capability's region — the interface's default for a held capability or
    ///   one of the unknown type, an instance at its region otherwise; a
    ///   capability of the unknown type grants every operation; an operation a
    ///   scope's clause answers while a resident opened in the scope's region
    ///   is live is recorded for the clause, as [`Self::region_captured`] says.
    /// - fails: [`CheckRefusal::UnknownOperation`] for an operation outside the
    ///   carried interface; [`CheckRefusal::ShapeMismatch`] wanting
    ///   [`ExpectedShape::Capability`] for a capability of another former;
    ///   [`CheckRefusal::CapabilityOutsideAuthority`] for an operation the
    ///   capability's authority does not grant with the interface's own payload
    ///   and reply types; as [`Self::region_captured`] for a capability of the
    ///   unknown type while any resident the run opened still owes something.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a granted operation synthesising its interface's row,
    ///   an operation of the interface the authority withholds, a value of
    ///   another type in capability position and an operation outside the
    ///   interface, each asserted as the exact type or refusal; an endpoint
    ///   held across an operation the host answers checks, and one held across
    ///   an operation its scope's clause answers is owed by the clause.
    /// - witness: `capability::tests::an_operation_is_exercised_only_within_the_authority`
    /// - witness: `judgement::session::tests::an_operation_a_scope_answers_captures_what_the_scope_opened_1334`
    /// - witness: `judgement::session::tests::a_clause_ends_a_continuation_holding_an_obligation_once_1334`
    #[spec(captures: depth = self.frames.len(), ensures: |ret| ret.is_err() || (self.frames.len() == depth.saturating_add(1) && matches!(ret, Ok(Step::Descend(Goal::Form(_))))))]
    fn exercise(
        &mut self,
        at: ComputationId,
        classifier: ValueTypeId,
    ) -> Result<Step, CheckRefusal>
    {
        let Computation::Exercise {
            capability,
            ref signature,
            ref operation,
            payload,
        } = *self.computation(at)?
        else {
            return Err(CheckRefusal::MachineInvariant);
        };
        let Maybe::Present(requested) = signature.operation(operation)
        else {
            return Err(CheckRefusal::UnknownOperation { at });
        };
        let (expected, reply) = (requested.payload, requested.reply);
        let (signature, operation) = (signature.clone(), operation.clone());
        let head = self.context.whnf_value_type(classifier)?;
        crate::capability::authorise(
            self.context.arena(),
            at,
            capability,
            classifier,
            head,
            &signature,
            &operation,
        )?;
        // A capability of the unknown type may be any scope's, so any handler
        // may receive the operation's continuation; so may one at a region the
        // definition abstracts, whose scope stands outside the run.
        let (answerer, placed) = if let ValueTypeView::Capability { region, .. } =
            value_type_view(self.context.arena(), head)?
        {
            let answerer = match region {
                Region::Held => session::Answerer::Host,
                Region::Scoped(depth) => session::Answerer::Scope {
                    depth,
                    operation: &operation,
                },
                Region::Bound(_) => session::Answerer::Anyone,
            };
            (answerer, region)
        }
        else {
            (session::Answerer::Anyone, Region::Held)
        };
        self.region_captured(at, answerer, payload)?;
        let effects = gandr_core_term::effect::EffectRow::instance(signature, placed);
        let result = self
            .context
            .arena_mut()
            .comp_type_returner_with_effects(reply, effects);
        self.wait(Frame::PerformPayload {
            at,
            payload,
            expected,
            result,
        });
        Ok(Step::Descend(Goal::Form(TypeNode::Computation(result))))
    }

    /// Start a capability scope checked against `answer`: the Scope rule's
    /// coverage, its region side condition and the type its subject is checked
    /// at.
    ///
    /// # Specification
    /// - ensures: the subject's type `F^⟨I, I@ρ | ε⟩ A` is formed next, where
    ///   `I` is the handled interface, `ρ` the region the scope's capability
    ///   lives in and `F^ε A` the answer, with the scope waiting on it: the
    ///   subject may perform the interface by name and through the capability;
    ///   a scope of [`gandr_core_term::effect::host::DIV`], which no handler
    ///   eliminates, checks its subject at `F^ε A` itself.
    /// - fails: [`CheckRefusal::ShapeMismatch`] for an answer that is no
    ///   returner; [`CheckRefusal::HandlerCoverage`] for clauses that do not
    ///   cover the interface exactly once; [`CheckRefusal::CapabilityEscaped`]
    ///   for an answer whose capability lives in the scope's own region or a
    ///   deeper one, and [`CheckRefusal::Access`] naming
    ///   [`crate::access::AccessDefect::KeptEscaped`] for one whose value is
    ///   kept there; [`CheckRefusal::EffectSignatureConflict`] for an answer
    ///   row giving the interface's name other operations.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a scope whose subject exercises its own capability
    ///   checks; an answer mentioning the scope's region, a missing clause and
    ///   a conflicting answer row are each refused by name; a scope of `Div`
    ///   over a diverging call leaves the call's row to the answer.
    /// - witness: `capability::tests::a_scope_handles_the_capability_it_introduces`
    /// - witness: `divergence::tests::no_handler_discharges_div`
    /// - witness: `capability::tests::a_scoped_capability_never_leaves_its_scope`
    /// - witness: `judgement::access::tests::a_view_kept_in_a_region_lives_as_long_as_its_scope`
    #[spec(captures: depth = self.frames.len(), ensures: |ret| ret.is_err() || (self.frames.len() == depth.saturating_add(1) && matches!(self.frames.last(), Some(Waiting { frame: Frame::ScopeForm { at: site, .. }, .. }) if *site == at)))]
    fn scope(
        &mut self,
        at: ComputationId,
        answer: CompTypeId,
    ) -> Result<Step, CheckRefusal>
    {
        let result = self.returner_expected(at, answer)?;
        let Computation::Scope {
            ref signature,
            ref clauses,
            ..
        } = *self.computation(at)?
        else {
            return Err(CheckRefusal::MachineInvariant);
        };
        if signature.operations().len() != clauses.len() {
            return Err(CheckRefusal::HandlerCoverage { at });
        }
        let mut names: Vec<_> = clauses.iter().map(|clause| &clause.operation).collect();
        names.sort_unstable();
        if !names
            .into_iter()
            .zip(signature.operations())
            .all(|(name, operation)| name == &operation.name)
        {
            return Err(CheckRefusal::HandlerCoverage { at });
        }
        let signature = signature.clone();
        let around = self.enclosing_region()?;
        match crate::capability::reaches(
            self.context.arena(),
            TypeNode::Computation(answer),
            around,
        )? {
            crate::capability::Reach::Clear => {},
            crate::capability::Reach::Mentions => {
                return Err(CheckRefusal::CapabilityEscaped {
                    at: TermNode::Computation(at),
                    found: TypeNode::Computation(answer),
                });
            },
            crate::capability::Reach::Keeps => {
                return Err(CheckRefusal::Access {
                    at: CoreNode::Term(TermNode::Computation(at)),
                    defect: crate::access::AccessDefect::KeptEscaped,
                });
            },
        }
        let head = self.context.whnf_comp_type(answer)?;
        let ambient = match comp_type_view(self.context.arena(), head)? {
            CompTypeView::Returner { effects, .. } => effects.clone(),
            CompTypeView::Unknown => gandr_core_term::effect::EffectRow::EMPTY,
            CompTypeView::Element { .. }
            | CompTypeView::Arrow { .. }
            | CompTypeView::Pi { .. }
            | CompTypeView::With(..)
            | CompTypeView::Codata { .. } => return Err(CheckRefusal::MachineInvariant),
        };
        // Divergence has no operation to answer: its scope runs the subject
        // in the answer's own row.
        let divergence = signature.name().as_ref() == gandr_core_term::effect::host::DIV;
        let own = self.next_region()?;
        let handled = gandr_core_term::effect::EffectRow::from_placed([
            (signature.clone(), Region::Held),
            (signature, own),
        ])
        .map_err(|_twice| CheckRefusal::MachineInvariant)?;
        let widened = if divergence {
            Ok(ambient)
        }
        else {
            ambient.union(&handled, self.context.arena())
        };
        let Ok(row) = widened
        else {
            let interface = self
                .context
                .arena_mut()
                .comp_type_returner_with_effects(result, handled);
            return Err(CheckRefusal::EffectSignatureConflict {
                at,
                first: answer,
                second: interface,
            });
        };
        let level = level_of(self.context, TypeNode::Value(result))?;
        self.context.record_handled(at, crate::handler::Handled {
            subject: result,
            answer,
            level,
        });
        let subject = self
            .context
            .arena_mut()
            .comp_type_returner_with_effects(result, row);
        self.wait(Frame::ScopeForm {
            at,
            answer,
            subject,
        });
        Ok(Step::Descend(Goal::Form(TypeNode::Computation(subject))))
    }

    /// Open a capability scope's binder and check its subject beneath it.
    ///
    /// # Specification
    /// - requires: `subject` is the formed type the subject is checked at, in
    ///   the scope's own context.
    /// - ensures: one intuitionistic binder of the capability `Cap_ρ ⟨I⟩`,
    ///   durable, at the region one deeper than every enclosing scope; the
    ///   region marked with the linear slots opened before it, whose shared
    ///   views a value kept there may name; the subject is checked against
    ///   `subject` shifted past it.
    /// - fails: [`CheckRefusal::MachineInvariant`] for a node that is no scope.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the subject exercising the binder checks, and the
    ///   binder returned through the subject is refused as escaping; a shared
    ///   view of a hold outside the scope is kept in its region, one of a hold
    ///   inside it is refused.
    /// - witness: `capability::tests::a_scope_handles_the_capability_it_introduces`
    /// - witness: `capability::tests::a_scoped_capability_never_leaves_its_scope`
    /// - witness: `judgement::access::tests::a_view_kept_in_a_region_lives_as_long_as_its_scope`
    #[spec(captures: depth = usize::from(self.context.depth(Zone::Intuitionistic)), ensures: |ret| ret.is_err() || usize::from(self.context.depth(Zone::Intuitionistic)) == depth.saturating_add(1))]
    fn scope_subject(
        &mut self,
        at: ComputationId,
        answer: CompTypeId,
        subject: CompTypeId,
    ) -> Result<Step, CheckRefusal>
    {
        let Computation::Scope {
            ref signature,
            subject: body,
            ..
        } = *self.computation(at)?
        else {
            return Err(CheckRefusal::MachineInvariant);
        };
        let authority = gandr_core_term::effect::EffectRow::singleton(signature.clone());
        let region = self.next_region()?;
        let arena = self.context.arena_mut();
        let capability = arena.value_type_capability(authority, CapabilityGrade::Durable, region);
        let expected = shift_comp_type(arena, subject, Binders::from(1_u32)).settle(arena);
        self.context
            .binders()
            .open(Zone::Intuitionistic, capability);
        self.sessions.regions.push(self.sessions.opened.len());
        self.wait(Frame::ScopeSubject { at, answer });
        Ok(Step::Descend(Goal::Computation {
            term: body,
            direction: Direction::Check(expected),
        }))
    }

    /// Close a capability scope's binder and open its return clause.
    ///
    /// # Specification
    /// - ensures: the capability's binder is closed; one binder of the answer's
    ///   result is open, and the return clause is checked against the answer
    ///   shifted past it.
    /// - fails: [`CheckRefusal::MachineInvariant`] when the binder stack is not
    ///   where the scope left it.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a return clause typed at the answer checks; one
    ///   returning another type is refused.
    /// - witness: `capability::tests::a_scope_handles_the_capability_it_introduces`
    #[spec(captures: depth = usize::from(self.context.depth(Zone::Intuitionistic)), ensures: |ret| ret.is_err() || usize::from(self.context.depth(Zone::Intuitionistic)) == depth)]
    fn scope_return(
        &mut self,
        at: ComputationId,
        answer: CompTypeId,
    ) -> Result<Step, CheckRefusal>
    {
        self.close()?;
        let result = self.returner_expected(at, answer)?;
        let Computation::Scope { on_return, .. } = *self.computation(at)?
        else {
            return Err(CheckRefusal::MachineInvariant);
        };
        let expected = shift_comp_type(self.context.arena_mut(), answer, Binders::from(1_u32))
            .settle(self.context.arena_mut());
        self.context.binders().open(Zone::Intuitionistic, result);
        self.wait(Frame::HandlerReturn { at, answer });
        Ok(Step::Descend(Goal::Computation {
            term: on_return,
            direction: Direction::Check(expected),
        }))
    }

    /// Run `goal` to its result in `context`, strictly.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the result the goal's rule produced and the
    ///   crossings made; on success and on refusal alike, the binders stand
    ///   where they stood at entry.
    /// - fails: the failure of the first refusal a rule gives, or of
    ///   [`CheckRefusal::BudgetExceeded`] when the allowance runs out.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the decision surfaces are the step loop, the
    ///   allowance and the unwinding, separated by a run that finishes, one cut
    ///   short by the allowance, and a refusal under binders followed by a
    ///   judgement in the same context.
    /// - witness: `judgement::tests::an_exhausted_allowance_is_refused_with_the_budget`
    /// - witness: `judgement::tests::a_refusal_under_binders_leaves_the_context_as_found`
    /// - witness: `judgement::tests::the_faces_agree_on_free_terms`
    #[spec(
        captures: depth = context.depth(Zone::Intuitionistic),
        ensures: |ret| context.depth(Zone::Intuitionistic) == depth && match ret {
            | Ok((produced, conversions)) => usize::from(conversions) <= usize::from(context.budget())
                && matches!((goal, produced),
                    (Goal::Value { direction: Direction::Synthesise, .. }, Produced::ValueType(_))
                        | (Goal::Computation { direction: Direction::Synthesise, .. }, Produced::CompType(_))
                        | (Goal::Value { direction: Direction::Check(_), .. }
                            | Goal::Computation { direction: Direction::Check(_), .. }
                            | Goal::Form(_) | Goal::Stack { .. }, Produced::Checked)),
            | Err(_) => true,
        },
    )]
    fn run(
        context: &'context mut CheckingContext<'arena>,
        goal: Goal,
    ) -> Result<(Produced, ConversionCount), Failure>
    {
        Machine::execute(context, goal, Marking::Strict)
            .map(|(produced, conversions, _marks)| (produced, conversions))
    }

    /// Run `goal` to its result in `context`, strictly or totally.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the result the goal's rule produced, the crossings
    ///   made and the refusals marked, none in a strict run; on success and on
    ///   refusal alike, the binders stand where they stood at entry, and the
    ///   foresights a mutual block's branches opened are closed.
    /// - fails: in a strict run, the first refusal a rule gives; in a total
    ///   run, the first engine fault; in both, [`CheckRefusal::BudgetExceeded`]
    ///   when the allowance runs out. The failure holds the frames pending,
    ///   outermost first, the goal under way and the binders the run opened,
    ///   read before they are closed.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a strict run and a total run over the same ill-typed
    ///   term separate the refusal from the mark; a run cut short by the
    ///   allowance and a refusal under binders keep the context as found; a
    ///   refusal under a thunk and under a bind hands back the rules it stood
    ///   in and the binder it was under.
    /// - witness: `judgement::tests::an_exhausted_allowance_is_refused_with_the_budget`
    /// - witness: `judgement::tests::a_refusal_under_binders_leaves_the_context_as_found`
    /// - witness: `judgement::elaboration::tests::a_total_run_marks_where_a_strict_run_refuses`
    /// - witness: `judgement::tests::a_refusal_keeps_the_rules_it_stood_inside`
    /// - witness: `judgement::tests::a_refusal_under_a_bind_keeps_its_hypothesis`
    #[spec(
        captures: depth = context.depth(Zone::Intuitionistic),
        ensures: |ret| context.depth(Zone::Intuitionistic) == depth && match ret.as_ref() {
            | Ok(&(produced, conversions, ref marks)) => usize::from(conversions) <= usize::from(context.budget())
                && (marking == Marking::Total || marks.is_empty())
                && matches!((goal, produced),
                    (Goal::Value { direction: Direction::Synthesise, .. }, Produced::ValueType(_))
                        | (Goal::Computation { direction: Direction::Synthesise, .. }, Produced::CompType(_))
                        | (Goal::Value { direction: Direction::Check(_), .. }
                            | Goal::Computation { direction: Direction::Check(_), .. }
                            | Goal::Form(_), Produced::Checked)),
            | Err(_) => true,
        },
    )]
    fn execute(
        context: &'context mut CheckingContext<'arena>,
        goal: Goal,
        marking: Marking,
    ) -> Result<(Produced, ConversionCount, Vec<MarkEntry>), Failure>
    {
        let entry = context.binders().depth(Zone::Intuitionistic);
        let foresight = context.foresight();
        let remaining = usize::from(context.budget());
        let base = context.depth(Zone::Linear);
        let abstracted = abstracted_by(context.arena(), goal);
        let mut machine = Machine {
            context,
            frames: Vec::new(),
            owner: goal,
            native_types: Vec::new(),
            conversions: ConversionCount::default(),
            remaining,
            marking,
            anchors: Vec::new(),
            marks: Vec::new(),
            sessions: Sessions::new(base, abstracted),
            root: Maybe::Absent(crate::respect::root::Absent::Unmarked),
            staged_motives: Vec::new(),
            images: worlds::Images::default(),
        };
        let register = machine.context.binders().world();
        let scope = machine.session_scope();
        let entered = machine.open_entry();
        match machine.drive(goal) {
            Ok(produced) => {
                // An entry's capabilities are tokens: spent or not, they end
                // with the run that held them.
                if entered == worlds::Entered::Holding {
                    machine.close_sessions(scope);
                }
                Ok((produced, machine.conversions, machine.marks))
            },
            Err(halt) => {
                let failure = machine.failure(halt, entry);
                machine.unwind(entry);
                machine.context.forget_foresight(foresight);
                machine.close_sessions(scope);
                let _moved = machine.context.binders().relocate(register);
                Err(failure)
            },
        }
    }

    /// The failure a halted run leaves: its pending frames and the binders it
    /// opened above `entry`.
    ///
    /// # Specification
    /// - requires: the binders stand at or above `entry`.
    /// - ensures: the halt's refusal; one obligation per pending frame,
    ///   outermost first, the resumed frame innermost when the halt came while
    ///   resuming; the pursuit of the goal started or the resumed frame's
    ///   owner; the types of the binders opened above `entry`, outermost first,
    ///   each attributed to the frame that opened it when the frames' binder
    ///   counts add up to them, and to none otherwise. A node of a refined term
    ///   reads as the written node it rewrites, in the pursuit, in each frame
    ///   and as a type mismatch's term; a frame on a refinement's copy of a
    ///   binder stands on the node of the frame that opened that binder; a
    ///   frame on a node the refinement minted that opens no binder is left out
    ///   (#3694). The frame stack is left empty and the binders are left open.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a refusal inside a thunk's force, under a bind and at
    ///   an application head separate the frame order, the attribution of a
    ///   binder and the resumed frame; a refusal inside a refined arm separates
    ///   the written term, the copied binder and the minted frames.
    /// - witness: `judgement::tests::a_refusal_keeps_the_rules_it_stood_inside`
    /// - witness: `judgement::tests::a_refusal_under_a_bind_keeps_its_hypothesis`
    /// - witness: `tests::native_formers::a_refusal_inside_a_refined_arm_names_the_written_term_3694`
    #[spec(
        requires: self.context.depth(Zone::Intuitionistic) >= entry,
        ensures: |ret| self.frames.is_empty() && core::mem::discriminant(&ret.refusal()) == core::mem::discriminant(&halt.refusal),
    )]
    fn failure(
        &mut self,
        halt: Halt,
        entry: BinderDepth,
    ) -> Failure
    {
        let mut frames = core::mem::take(&mut self.frames);
        let stage = match halt.control {
            Control::Starting(goal) => (goal, Stage::Starting),
            Control::Resuming(waiting) => {
                frames.push(waiting);
                (waiting.owner, Stage::Resuming)
            },
            Control::Handing => (self.owner, Stage::Handing),
        };
        let (at, expected) = judged(stage.0);
        // A node of a refined term reads as the written node it rewrites, so
        // the refusal stands where the source wrote it (#3694).
        let context = &*self.context;
        let written = |term: TermNode| match context.standing(term) {
            crate::solution::Standing::Written(written) => written,
            crate::solution::Standing::Copy(_) | crate::solution::Standing::Minted => term,
        };
        let at = match at {
            CoreNode::Term(term) => CoreNode::Term(written(term)),
            CoreNode::Type(_) => at,
        };
        let refusal = if let CheckRefusal::TypeMismatch(mismatch) = halt.refusal {
            match mismatch {
                Mismatch::Value {
                    at: value,
                    synthesised,
                    expected,
                } => match written(TermNode::Value(value)) {
                    TermNode::Value(value) => CheckRefusal::TypeMismatch(Mismatch::Value {
                        at: value,
                        synthesised,
                        expected,
                    }),
                    TermNode::Computation(_) => halt.refusal,
                },
                Mismatch::Computation {
                    at: computation,
                    synthesised,
                    expected,
                } => match written(TermNode::Computation(computation)) {
                    TermNode::Computation(computation) => {
                        CheckRefusal::TypeMismatch(Mismatch::Computation {
                            at: computation,
                            synthesised,
                            expected,
                        })
                    },
                    TermNode::Value(_) => halt.refusal,
                },
            }
        }
        else {
            halt.refusal
        };
        let pursuit = Pursuit::new(at, expected, stage.1);
        let opened = usize::from(self.context.binders().depth(Zone::Intuitionistic))
            .saturating_sub(usize::from(entry));
        let mut hypotheses = Vec::with_capacity(opened);
        for index in (0 .. opened).rev() {
            let Ok(index) = u32::try_from(index)
            else {
                break;
            };
            let Ok(declared) = self
                .context
                .binders()
                .occurrence(Zone::Intuitionistic, DeBruijnIndex::from(index))
            else {
                break;
            };
            hypotheses.push(declared);
        }
        let counted = frames
            .iter()
            .map(|waiting| usize::from(waiting.frame.opens()))
            .fold(0_usize, usize::saturating_add);
        let attributed = counted == hypotheses.len();
        let mut next = 0_usize;
        // The node each hypothesis's frame stands on, outermost first, so a
        // frame of a refinement's copy of a binder reads at the frame that
        // opened the binder it copies (#3694).
        let mut openers: Vec<CoreNode> = Vec::with_capacity(hypotheses.len());
        let mut obligations = Vec::with_capacity(frames.len());
        for waiting in frames {
            let binders = if attributed {
                let end = next.saturating_add(usize::from(waiting.frame.opens()));
                let binders = hypotheses
                    .get(next .. end)
                    .map_or_else(Vec::new, <[_]>::to_vec);
                next = end;
                binders
            }
            else {
                Vec::new()
            };
            let (at, expected) = judged(waiting.owner);
            // A frame on a node a refinement minted adds nothing the source
            // wrote. It is kept only when it opens a binder, so every
            // hypothesis keeps a frame that names it.
            let at = match at {
                CoreNode::Term(term) => match self.context.standing(term) {
                    crate::solution::Standing::Written(written) => CoreNode::Term(written),
                    crate::solution::Standing::Copy(place) => usize::from(place)
                        .checked_sub(usize::from(entry))
                        .and_then(|position| openers.get(position))
                        .copied()
                        .unwrap_or(at),
                    crate::solution::Standing::Minted
                        if usize::from(waiting.frame.opens()) == 0 =>
                    {
                        continue;
                    },
                    crate::solution::Standing::Minted => at,
                },
                CoreNode::Type(_) => at,
            };
            openers.extend(core::iter::repeat_n(at, binders.len()));
            obligations.push(Obligation::new(waiting.frame.role(), at, expected, binders));
        }
        let endpoints = self.live_endpoints();
        Failure::new(refusal, obligations, pursuit, hypotheses, endpoints)
    }

    /// Step from `goal` until no frame waits.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the result handed out when the frame stack empties.
    /// - fails: as for [`Self::run`], with what the machine was doing at the
    ///   refused step: the goal it was starting, the frame it had popped to
    ///   resume, or the hand-off of a result to the frame still on top.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — completing and budget-exhausted runs expose final
    ///   results and retained scope; L1 bounded free terms compare the two
    ///   faces. Premature completion or uncharged transitions changes these
    ///   observations, not a claim about arbitrary malformed frame stacks.
    /// - witness: `judgement::tests::an_exhausted_allowance_is_refused_with_the_budget`
    /// - witness: `judgement::tests::the_faces_agree_on_free_terms`
    /// - witness: `judgement::tests::a_refusal_keeps_the_rules_it_stood_inside`
    #[spec(
        captures: before = self.remaining,
        ensures: |ret| self.remaining <= before && (ret.is_err() || self.frames.is_empty()),
    )]
    fn drive(
        &mut self,
        goal: Goal,
    ) -> Result<Produced, Halt>
    {
        let mut step = Step::Descend(goal);
        loop {
            if let Err(refusal) = self.charge() {
                let control = match step {
                    Step::Descend(goal) => Control::Starting(goal),
                    Step::Ascend(_) => Control::Handing,
                };
                return Err(Halt { refusal, control });
            }
            let (control, next) = match step {
                Step::Descend(goal) => {
                    self.owner = goal;
                    self.anchor(goal);
                    (Control::Starting(goal), self.descend(goal))
                },
                Step::Ascend(produced) => {
                    self.settle(produced);
                    match self.frames.pop() {
                        Some(waiting) => {
                            self.owner = waiting.owner;
                            (
                                Control::Resuming(waiting),
                                self.resume(waiting.frame, produced),
                            )
                        },
                        None => return Ok(produced),
                    }
                },
            };
            step = match next {
                Ok(next) => next,
                Err(refusal) => {
                    let refusal = self.unwinding(refusal, control);
                    let refusal = self.spliced_refusal(refusal);
                    match self.recover(refusal) {
                        Ok(next) => next,
                        Err(refusal) => return Err(Halt { refusal, control }),
                    }
                },
            };
        }
    }

    /// Push `frame`, owned by the goal whose rule is running.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the frame stack grows by `frame` beside the running goal.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a refusal under a thunk observes each frame beside
    ///   the node whose rule pushed it.
    /// - witness: `judgement::tests::a_refusal_keeps_the_rules_it_stood_inside`
    #[spec(
        captures: before = self.frames.len(),
        ensures: self.frames.len().checked_sub(before) == Some(1)
            && self.frames.last() == Some(&Waiting { frame, owner: self.owner }),
    )]
    fn wait(
        &mut self,
        frame: Frame,
    )
    {
        self.frames.push(Waiting {
            frame,
            owner: self.owner,
        });
    }

    /// The refusal a step gives while a splice's answer is under judgement:
    /// the splice's tactic refused as forged, since the tactic answered a term
    /// its goal refuses.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`CheckRefusal::TacticRefused`] with [`TacticFault::Forged`]
    ///   at the innermost pending splice, naming its tactic; `refusal`
    ///   unchanged when no splice is pending.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an answer of another type and one past the goal's
    ///   binders are refused naming the tactic; the answer of the goal's type
    ///   fills the hole.
    /// - witness: `judgement::tests::a_forged_answer_is_refused_naming_its_tactic_2762`
    #[spec(ensures: |ret| ret == refusal
        || matches!(ret, CheckRefusal::TacticRefused { fault: TacticFault::Forged, .. }))]
    fn spliced_refusal(
        &self,
        refusal: CheckRefusal,
    ) -> CheckRefusal
    {
        self.frames
            .iter()
            .rev()
            .find_map(|waiting| {
                let Frame::Spliced { at, hole, .. } = waiting.frame
                else {
                    return None;
                };
                hole.tactic().map(|tactic| CheckRefusal::TacticRefused {
                    at,
                    tactic,
                    fault: TacticFault::Forged,
                })
            })
            .unwrap_or(refusal)
    }

    /// Spend one step of the allowance.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success one fewer step remains; refusal leaves zero.
    /// - fails: [`CheckRefusal::BudgetExceeded`] when none remains.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — zero and one remaining step expose exact exhaustion
    ///   and the original allowance; complete judgements distinguish charging
    ///   too early, too late or not at all.
    /// - witness: `judgement::tests::machine_bookkeeping_preserves_zero_and_one_boundaries`
    /// - witness: `judgement::tests::an_exhausted_allowance_is_refused_with_the_budget`
    #[spec(
        captures: before = self.remaining,
        ensures: |ret| match before.checked_sub(1) {
            | Some(remaining) => ret == Ok(()) && self.remaining == remaining,
            | None => self.remaining == 0 && ret == Err(CheckRefusal::BudgetExceeded { budget: self.context.budget() }),
        },
    )]
    fn charge(&mut self) -> Result<(), CheckRefusal>
    {
        let Some(remaining) = self.remaining.checked_sub(1_usize)
        else {
            return Err(CheckRefusal::BudgetExceeded {
                budget: self.context.budget(),
            });
        };
        self.remaining = remaining;
        Ok(())
    }

    /// Close every binder opened since the binders stood at `entry`.
    ///
    /// # Specification
    /// - requires: the binders stand at or above `entry`.
    /// - ensures: the binders stand at `entry`.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — refusal inside binders and explicit zero/one-scope
    ///   transitions observe the original depth before the next judgement;
    ///   incomplete unwinding or closing an outer binder changes the result.
    /// - witness: `judgement::tests::a_refusal_under_binders_leaves_the_context_as_found`
    /// - witness: `judgement::tests::machine_bookkeeping_preserves_zero_and_one_boundaries`
    #[spec(
        requires: self.context.depth(Zone::Intuitionistic) >= entry,
        ensures: self.context.depth(Zone::Intuitionistic) == entry,
    )]
    fn unwind(
        &mut self,
        entry: BinderDepth,
    )
    {
        while self.context.binders().depth(Zone::Intuitionistic) > entry {
            if self.context.binders().close(Zone::Intuitionistic).is_err() {
                break;
            }
        }
        self.context.closed_binder();
    }

    /// Close the innermost binder this run opened.
    ///
    /// # Specification
    /// - requires: a rule of this run opened a binder it has not closed.
    /// - ensures: that binder is closed.
    /// - fails: [`CheckRefusal::MachineInvariant`] when no binder is open.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty and one-binder scopes expose an exact machine
    ///   fault or one removed binder; checked lambdas and binds observe that
    ///   closing restores the surrounding context rather than an outer scope.
    /// - witness: `judgement::tests::machine_bookkeeping_preserves_zero_and_one_boundaries`
    /// - witness: `judgement::tests::a_bind_checks_against_the_expected_computation`
    #[spec(
        captures: before = usize::from(self.context.depth(Zone::Intuitionistic)),
        ensures: |ret| match before.checked_sub(1) {
            | Some(depth) => ret == Ok(()) && usize::from(self.context.depth(Zone::Intuitionistic)) == depth,
            | None => ret == Err(CheckRefusal::MachineInvariant)
                && self.context.depth(Zone::Intuitionistic) == BinderDepth::default(),
        },
    )]
    fn close(&mut self) -> Result<(), CheckRefusal>
    {
        let closed = self.context.binders().close(Zone::Intuitionistic);
        self.context.closed_binder();
        match closed {
            Ok(_) => Ok(()),
            Err(_) => Err(CheckRefusal::MachineInvariant),
        }
    }

    /// Start the judgement `goal`, by its direction.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the rule of the goal's direction for its term's former runs,
    ///   or the formation rule of the type's former.
    /// - fails: as that rule; as [`Self::fence`] for a former that may run an
    ///   endpoint's use other than once.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each former through each public direction exposes its
    ///   result family or named refusal, with L1 bounded free terms comparing
    ///   the faces; wrong dispatch or an unrelated ascent differs.
    /// - witness: `judgement::tests::every_value_former_is_answered_in_both_modes`
    /// - witness: `judgement::tests::every_comp_former_is_answered_in_both_modes`
    /// - witness: `judgement::tests::the_faces_agree_on_free_terms`
    /// - witness: `tests::native_formers::record_width_depth_and_projection`
    #[spec(ensures: |ret| match ret {
        | Ok(Step::Ascend(produced)) => matches!((goal, produced),
            (Goal::Value { direction: Direction::Synthesise, .. }, Produced::ValueType(_))
                | (Goal::Computation { direction: Direction::Synthesise, .. }, Produced::CompType(_))
                | (Goal::Value { direction: Direction::Check(_), .. }
                    | Goal::Computation { direction: Direction::Check(_), .. } | Goal::Form(_) | Goal::Stack { .. }, Produced::Checked)),
        | Ok(Step::Descend(_)) | Err(_) => true,
    })]
    fn descend(
        &mut self,
        goal: Goal,
    ) -> Result<Step, CheckRefusal>
    {
        self.fence(goal)?;
        match goal {
            Goal::Stack {
                judgement,
                position,
                input,
            } => self.stack_step(judgement, position, input),
            Goal::Value { term, direction } => match direction {
                Direction::Synthesise => self.synthesise_value(term),
                Direction::Check(expected) => self
                    .check_value(term, expected)
                    .or_else(|refusal| self.forged(term, expected, refusal)),
            },
            Goal::Computation { term, direction } => {
                // A case on a variable whose arms read a later binder at it is
                // checked at the motive generalised over that binder.
                let term = match crate::solution::refined_case(self.context, term)? {
                    Maybe::Present(refined) => {
                        self.context.record_refinement(term, &refined);
                        refined.term
                    },
                    Maybe::Absent(_) => term,
                };
                match direction {
                    Direction::Synthesise => self.synthesise_comp(term),
                    Direction::Check(expected) => self.check_comp(term, expected),
                }
            },
            Goal::Form(TypeNode::Value(at)) => self.form_value_type(at),
            Goal::Form(TypeNode::Computation(at)) => self.form_comp_type(at),
        }
    }

    /// The node of `term`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the node `term` names.
    /// - fails: [`CheckRefusal::DanglingNode`] when the arena holds none.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — present value formers and a missing value id expose
    ///   the exact node rule or exact dangling fault; these distinguish a wrong
    ///   family, substituted node and omitted failure.
    /// - witness: `judgement::tests::every_value_former_is_answered_in_both_modes`
    /// - witness: `judgement::tests::machine_bookkeeping_preserves_zero_and_one_boundaries`
    #[spec(ensures: |ret| match (self.context.arena().value(term), ret) {
        | (Some(expected), Ok(held)) => core::ptr::eq(core::ptr::from_ref(expected), core::ptr::from_ref(held)),
        | (None, Err(refusal)) => refusal == CheckRefusal::DanglingNode { node: CoreNode::Term(TermNode::Value(term)) },
        | _ => false,
    })]
    fn value(
        &self,
        term: ValueId,
    ) -> Result<&Value, CheckRefusal>
    {
        self.context
            .arena()
            .value(term)
            .ok_or(CheckRefusal::DanglingNode {
                node: CoreNode::Term(TermNode::Value(term)),
            })
    }

    /// The node of `term`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the node `term` names.
    /// - fails: [`CheckRefusal::DanglingNode`] when the arena holds none.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — present computation formers and a missing computation
    ///   id expose the selected rule or exact dangling fault; these separate a
    ///   substituted node and a value-family diagnostic.
    /// - witness: `judgement::tests::every_comp_former_is_answered_in_both_modes`
    /// - witness: `judgement::tests::machine_bookkeeping_preserves_zero_and_one_boundaries`
    #[spec(ensures: |ret| match (self.context.arena().computation(term), ret) {
        | (Some(expected), Ok(held)) => core::ptr::eq(core::ptr::from_ref(expected), core::ptr::from_ref(held)),
        | (None, Err(refusal)) => refusal == CheckRefusal::DanglingNode { node: CoreNode::Term(TermNode::Computation(term)) },
        | _ => false,
    })]
    fn computation(
        &self,
        term: ComputationId,
    ) -> Result<&Computation, CheckRefusal>
    {
        self.context
            .arena()
            .computation(term)
            .ok_or(CheckRefusal::DanglingNode {
                node: CoreNode::Term(TermNode::Computation(term)),
            })
    }

    /// The synthesis rules over values.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a variable has the type its binder declared, shifted past the
    ///   binders opened since; a constant the type its declaration supplied;
    ///   the unit value and an integer, string or character literal their atom;
    ///   a hole and a mark the unknown type, minted; a quote awaits its type's
    ///   formation; a pair awaits its components' types and has their eager
    ///   product; a static application awaits its head's type and meets each
    ///   argument in turn; reflexivity awaits its point's type `A` and has
    ///   `Path(A, a, a)` at its point `a`; a compound endpoint awaits its
    ///   computation's type, which must be a pure returner `F A`, and has `A`;
    ///   a written run awaits its computation's type, which must be a returner
    ///   `F^e A`, records the run and has `A`; an ascription `(v : A)` awaits
    ///   `A`'s formation, checks `v` against it and has `A`; a row literal
    ///   awaits each of its types' formation and has the row kind. A leaf
    ///   ascends with the frames as found; every other rule descends above a
    ///   new frame.
    /// - fails: [`CheckRefusal::NotSynthesisable`] for a thunk, a static lambda
    ///   and a computation written where a value is read, which the expected
    ///   type decides; [`CheckRefusal::UnboundIndex`] for a variable past its
    ///   zone's binders; [`CheckRefusal::UnknownConstant`] for a constant with
    ///   no type; [`CheckRefusal::OutOfFragment`] for a numeric literal, an
    ///   injection and a value lift.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one value of every former synthesised, each to its
    ///   exact type or refusal.
    /// - witness: `judgement::tests::every_value_former_is_answered_in_both_modes`
    /// - witness: `judgement::tests::a_pair_synthesises_its_eager_product_and_checks_against_one`
    /// - witness: `judgement::tests::a_static_lambda_checks_only_against_a_static_pi`
    /// - witness: `bridge::tests::family_applied_at_wrong_arity_raises_the_exact_variant`
    /// - witness: `judgement::tests::a_hole_synthesises_the_unknown_type_and_checks_against_any`
    #[spec(
        captures: depth = self.frames.len(),
        ensures: |ret| match ret {
            | Ok(Step::Ascend(_)) => self.frames.len() == depth || (matches!(self.context.arena().value(term), Some(Value::Record(_))) && self.frames.len() > depth),
            | Ok(Step::Descend(_)) => self.frames.len() > depth,
            | Err(_) => true,
        },
    )]
    fn synthesise_value(
        &mut self,
        term: ValueId,
    ) -> Result<Step, CheckRefusal>
    {
        let produced = |found: FormedValueType| {
            Ok(Step::Ascend(Produced::ValueType(Relocated::from(
                found.id(),
            ))))
        };
        match *self.value(term)? {
            Value::Constructor { .. } => self.native_constructor(term),
            Value::Record(_) => self.native_record(term),
            Value::Reify(_) => Err(CheckRefusal::NotSynthesisable {
                form: CheckingForm::Reify(term),
            }),
            Value::ListNil | Value::ListCons(..) => Err(CheckRefusal::NotSynthesisable {
                form: CheckingForm::List(term),
            }),
            Value::Ascribe { value, ty } => {
                self.wait(Frame::NativeYield(Produced::ValueType(Relocated::from(ty))));
                self.wait(Frame::NativeNext(Goal::Value {
                    term: value,
                    direction: Direction::Check(ty),
                }));
                Ok(Step::Descend(Goal::Form(TypeNode::Value(ty))))
            },
            Value::Primitive { primitive, .. } => {
                let computation = primitive.declared_type(self.context.arena_mut());
                let classifier = self.context.arena_mut().value_type_thunk(computation);
                Ok(Step::Ascend(Produced::ValueType(Relocated::from(
                    classifier,
                ))))
            },
            Value::PathRefl(code) => {
                let _endpoint = crate::formation::path_code(self.context.arena(), code)?;
                let classifier = self
                    .context
                    .arena_mut()
                    .value_type_path_universe(code, code);
                Ok(Step::Ascend(Produced::ValueType(Relocated::from(
                    classifier,
                ))))
            },
            Value::PathProduct(first, second) => {
                self.wait(Frame::PathProductFirst {
                    product: term,
                    at: first,
                    second,
                });
                Ok(Step::Descend(Goal::Value {
                    term: first,
                    direction: Direction::Synthesise,
                }))
            },
            Value::PathEquiv {
                path_type,
                forward,
                backward,
                ..
            } => {
                let (source, target) = self.path_endpoints(term, path_type)?;
                let expected = self.map_type(source, target);
                self.wait(Frame::PathBackward {
                    backward,
                    source,
                    target,
                    path_type,
                });
                Ok(Step::Descend(Goal::Value {
                    term: forward,
                    direction: Direction::Check(expected),
                }))
            },
            Value::Variable {
                zone: Zone::Linear,
                index,
            } => self.linear_read(term, index),
            Value::Variable {
                zone: Zone::Intuitionistic,
                index,
            } => match self
                .context
                .binders()
                .occurrence(Zone::Intuitionistic, index)
            {
                Ok(declared) => {
                    self.located_here(term, index)?;
                    // The slot's type moved to this depth as a root update:
                    // the value bridge reads it through the relocation, and
                    // every other rule settles it where it reads it.
                    let read =
                        shift_value_type(self.context.arena_mut(), declared, Binders::past(index));
                    self.captured(term, index, read)?;
                    self.mention(term, index)?;
                    self.footprint_mentioned(declared)?;
                    Ok(Step::Ascend(Produced::ValueType(read)))
                },
                Err(ContextError::UnboundIndex { zone, index, depth }) => {
                    Err(CheckRefusal::UnboundIndex {
                        at: term,
                        zone,
                        index,
                        depth,
                    })
                },
                Err(
                    ContextError::LinearSlotConsumed { .. }
                    | ContextError::LinearSlotUnconsumed { .. }
                    | ContextError::NoBinderToClose { .. },
                ) => Err(CheckRefusal::MachineInvariant),
            },
            Value::Constant(constant) => match self.context.consult(constant) {
                Maybe::Present(declared) => {
                    self.located_constant(term, constant, declared.id())?;
                    self.footprint_mentioned(declared.id())?;
                    let read = match self.quantified_at(constant, declared.id())? {
                        Maybe::Present(staged) => staged,
                        Maybe::Absent(crate::quantified::Unread::Plain) => declared.id(),
                    };
                    match self.regioned_at(read)? {
                        Maybe::Present(placed) => {
                            Ok(Step::Ascend(Produced::ValueType(Relocated::from(placed))))
                        },
                        Maybe::Absent(_) if read != declared.id() => {
                            Ok(Step::Ascend(Produced::ValueType(Relocated::from(read))))
                        },
                        Maybe::Absent(_) => produced(declared),
                    }
                },
                Maybe::Absent(_) => Err(CheckRefusal::UnknownConstant { at: term, constant }),
            },
            Value::Literal(ref literal) => match literal.base_type() {
                BaseType::Integer => produced(self.context.atom(Atom::Integer)),
                BaseType::String => produced(self.context.atom(Atom::String)),
                BaseType::Character => produced(self.context.atom(Atom::Character)),
                BaseType::Float64 => produced(self.context.atom(Atom::Float64)),
                BaseType::Fixed(width) => produced(self.context.atom(Atom::Fixed(width))),
                BaseType::Numeric => Err(unadmitted_value(term, UnadmittedFormer::NumericLiteral)),
            },
            Value::Quote(quoted) => Ok(self.quote(TypeNode::Value(quoted))),
            Value::QuoteComputation(quoted) => Ok(self.quote(TypeNode::Computation(quoted))),
            Value::Thunk(_) => Err(CheckRefusal::NotSynthesisable {
                form: CheckingForm::Thunk(term),
            }),
            Value::Tuple(ref components) if components.is_empty() => {
                produced(self.context.atom(Atom::Unit))
            },
            Value::Tuple(_) => {
                let Some(components) = self.context.arena().value(term).and_then(Value::components)
                else {
                    return Err(CheckRefusal::MachineInvariant);
                };
                let owner = self.owner;
                self.frames.push(Waiting {
                    frame: Frame::NativeTuple {
                        base: self.native_types.len(),
                    },
                    owner,
                });
                for &component in components.iter().rev() {
                    self.frames.push(Waiting {
                        frame: Frame::NativeCollect,
                        owner,
                    });
                    self.frames.push(Waiting {
                        frame: Frame::NativeNext(Goal::Value {
                            term: component,
                            direction: Direction::Synthesise,
                        }),
                        owner,
                    });
                }
                let first = self.frames.pop().ok_or(CheckRefusal::MachineInvariant)?;
                self.resume(first.frame, Produced::Checked)
            },
            Value::Injection(..) => Err(CheckRefusal::NotSynthesisable {
                form: CheckingForm::Injection(term),
            }),
            Value::Lift { .. } => Err(unadmitted_value(term, UnadmittedFormer::ValueLift)),
            Value::StaticLambda(_) => Err(CheckRefusal::NotSynthesisable {
                form: CheckingForm::StaticLambda(term),
            }),
            Value::StaticApplication(..) => self.static_application(term),
            Value::Here(point) => {
                self.wait(Frame::HereSynthesised { point });
                Ok(Step::Descend(Goal::Value {
                    term: point,
                    direction: Direction::Synthesise,
                }))
            },
            Value::Funext(left, right) => {
                self.wait(Frame::FunextLeft {
                    at: term,
                    left,
                    right,
                });
                Ok(Step::Descend(Goal::Value {
                    term: left,
                    direction: Direction::Synthesise,
                }))
            },
            Value::Equiv(forward, backward) => {
                self.wait(Frame::EquivForward {
                    at: term,
                    forward,
                    backward,
                });
                Ok(Step::Descend(Goal::Value {
                    term: forward,
                    direction: Direction::Synthesise,
                }))
            },
            Value::Univalence(record, forward) => {
                self.wait(Frame::UnivalenceRecord {
                    at: term,
                    record,
                    forward,
                });
                Ok(Step::Descend(Goal::Value {
                    term: record,
                    direction: Direction::Synthesise,
                }))
            },
            Value::Ua { .. } => {
                let premises = crate::ua::premises(self.context, term)?;
                let owner = self.owner;
                self.frames.push(Waiting {
                    frame: Frame::UaTranslators { at: term },
                    owner,
                });
                for &(record, expected) in premises.iter().rev() {
                    self.frames.push(Waiting {
                        frame: Frame::NativeNext(Goal::Value {
                            term: record,
                            direction: Direction::Check(expected),
                        }),
                        owner,
                    });
                }
                let first = self.frames.pop().ok_or(CheckRefusal::MachineInvariant)?;
                self.resume(first.frame, Produced::Checked)
            },
            Value::Returned(computation) => {
                self.wait(Frame::ReturnedEndpoint { at: term });
                Ok(Step::Descend(Goal::Computation {
                    term: computation,
                    direction: Direction::Synthesise,
                }))
            },
            Value::Nested(_) => Err(CheckRefusal::NotSynthesisable {
                form: CheckingForm::Nested(term),
            }),
            Value::Run(computation) => {
                self.wait(Frame::Ran {
                    at: term,
                    read: Read::Goal,
                });
                Ok(Step::Descend(Goal::Computation {
                    term: computation,
                    direction: Direction::Synthesise,
                }))
            },
            // A computation written as the base runs, and the update reads
            // the record it returns.
            Value::RecordUpdate { base, .. } => {
                self.wait(Frame::UpdateBase { at: term });
                self.unsuspended(base)
            },
            Value::SessionRelated { source, target, .. } => {
                let universe = crate::flow::universe(self.context.arena_mut());
                let owner = self.owner;
                self.frames.push(Waiting {
                    frame: Frame::SessionStatement { at: term },
                    owner,
                });
                for code in [target, source] {
                    self.frames.push(Waiting {
                        frame: Frame::NativeNext(Goal::Value {
                            term: code,
                            direction: Direction::Check(universe),
                        }),
                        owner,
                    });
                }
                let first = self.frames.pop().ok_or(CheckRefusal::MachineInvariant)?;
                self.resume(first.frame, Produced::Checked)
            },
            Value::Stay(point) => {
                self.wait(Frame::StaySynthesised { at: term, point });
                Ok(Step::Descend(Goal::Value {
                    term: point,
                    direction: Direction::Synthesise,
                }))
            },
            Value::Then(first, second) => {
                self.wait(Frame::ThenFirst { at: term, second });
                Ok(Step::Descend(Goal::Value {
                    term: first,
                    direction: Direction::Synthesise,
                }))
            },
            Value::FlowProduct(first, second) => {
                self.wait(Frame::FlowProductFirst {
                    product: term,
                    at: first,
                    second,
                });
                Ok(Step::Descend(Goal::Value {
                    term: first,
                    direction: Direction::Synthesise,
                }))
            },
            Value::Forward(translator) => {
                self.wait(Frame::ForwardTranslator {
                    at: term,
                    translator,
                });
                Ok(Step::Descend(Goal::Value {
                    term: translator,
                    direction: Direction::Synthesise,
                }))
            },
            Value::FunctionFlow(domain, codomain) => {
                self.wait(Frame::ArrowDomain { at: term, codomain });
                Ok(Step::Descend(Goal::Value {
                    term: domain,
                    direction: Direction::Synthesise,
                }))
            },
            Value::Recorded(_) | Value::Dialogue(_) => Err(CheckRefusal::NotSynthesisable {
                form: CheckingForm::Run(term),
            }),
            Value::Web(_) => {
                let web = self.context.arena_mut().value_type_web();
                Ok(Step::Ascend(Produced::ValueType(Relocated::from(web))))
            },
            // Each type a row carries is formed, its tail at the row kind,
            // and the row has the row kind. The row is shared, not copied, so
            // its types are read while the arena mints the kind.
            Value::Row(ref row) => {
                let row = row.clone();
                let kind = self.context.arena_mut().value_type_row();
                let produced = Produced::ValueType(Relocated::from(kind));
                let mut types = row.types();
                let Some(first) = types.next()
                else {
                    return Ok(Step::Ascend(produced));
                };
                self.wait(Frame::NativeYield(produced));
                for ty in types.rev() {
                    self.wait(Frame::NativeNext(Goal::Form(TypeNode::Value(ty))));
                }
                Ok(Step::Descend(Goal::Form(TypeNode::Value(first))))
            },
            Value::Hole(hole) => {
                match hole.origin() {
                    HoleOrigin::Nominated | HoleOrigin::Wildcard => {
                        self.context.nominate(term, hole)?;
                    },
                    // A splice's goal is the type it is checked against, and
                    // here none is.
                    HoleOrigin::Spliced => {
                        return Err(CheckRefusal::TacticRefused {
                            at: term,
                            tactic: hole.tactic().ok_or(CheckRefusal::MachineInvariant)?,
                            fault: crate::refusal::TacticFault::Unplaced,
                        });
                    },
                    HoleOrigin::Written => {},
                }
                let unknown = self.context.arena_mut().value_type_unknown();
                Ok(Step::Ascend(Produced::ValueType(Relocated::from(unknown))))
            },
            Value::Mark { .. } => {
                let unknown = self.context.arena_mut().value_type_unknown();
                Ok(Step::Ascend(Produced::ValueType(Relocated::from(unknown))))
            },
        }
    }

    /// Start a quote of `quoted`: the quoted type's formation is the next
    /// goal, with the quote's frame awaiting it.
    ///
    /// # Specification
    /// - requires: nothing; formation answers a missing or unadmitted type.
    /// - ensures: one quote frame awaits formation of exactly `quoted`.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — quotes of value and computation types expose their
    ///   exact universe families and levels; a missing frame or wrong quoted
    ///   node changes synthesis, within those admitted quote forms.
    /// - witness: `judgement::tests::a_universe_classifies_one_level_up_in_the_positive_sort`
    #[spec(
        captures: before = self.frames.len(),
        ensures: |ret| self.frames.len().checked_sub(before) == Some(1)
            && self.frames.last().map(|waiting| waiting.frame) == Some(Frame::Quote(quoted))
            && ret == Step::Descend(Goal::Form(quoted)),
    )]
    fn quote(
        &mut self,
        quoted: TypeNode,
    ) -> Step
    {
        self.wait(Frame::Quote(quoted));
        Step::Descend(Goal::Form(quoted))
    }

    /// Name a checking rule's refusal of `term` at a capability type as the
    /// forgery it is: no value former introduces a capability, so a checking
    /// form met at one is a term standing where only a capability hypothesis
    /// may.
    ///
    /// # Specification
    /// - ensures: `refusal` unchanged, but for a shape mismatch at `term` whose
    ///   found type is a capability at its weak head, which becomes
    ///   [`CheckRefusal::CapabilityForged`] at `term` against `expected`.
    /// - fails: always; the weak head's refusal when it does not unfold.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a thunk and a pair checked at a capability type are
    ///   refused as forged, and a thunk checked at the integers keeps its shape
    ///   mismatch.
    /// - witness: `capability::tests::no_term_forges_a_capability`
    #[spec(ensures: |ret| ret.is_err())]
    fn forged(
        &mut self,
        term: ValueId,
        expected: ValueTypeId,
        refusal: CheckRefusal,
    ) -> Result<Step, CheckRefusal>
    {
        if let CheckRefusal::ShapeMismatch {
            at: TermNode::Value(at),
            found: TypeNode::Value(found),
            ..
        } = refusal
            && at == term
        {
            let head = self.context.whnf_value_type(found)?;
            if matches!(
                value_type_view(self.context.arena(), head)?,
                ValueTypeView::Capability { .. }
            ) {
                return Err(CheckRefusal::CapabilityForged { at, expected });
            }
        }
        Err(refusal)
    }

    /// The checking rules over values.
    ///
    /// # Specification
    /// - requires: `expected` is formed.
    /// - ensures: an introduction form checked at a type kept in a region
    ///   checks at the type kept, the region's entry, and a synthesising value
    ///   crosses the bridge to the kept type itself; a thunk's body checks
    ///   against the body `expected` matches as a thunk type at its weak head;
    ///   a pair's components check against the factors it matches as an eager
    ///   product, and against a dependent pair its first component checks
    ///   against the first factor and its second against the second factor at
    ///   the first component; a static lambda opens a binder of the domain it
    ///   matches as a static Pi and its body checks against the codomain
    ///   shifted past the binder; a hole and a mark check against any type at
    ///   once; a computation written where a value is read is decided by
    ///   `expected` — against a thunk type, or the unknown type, its
    ///   computation checks against the thunk's body and it is recorded
    ///   suspended, except a call against a thunk whose body is no returner
    ///   ([`Self::nested_read`]), which synthesises first and runs when it
    ///   returns, and except the decode of an implicit the solver has not bound
    ///   yet, where it runs so that what it returns binds the implicit; against
    ///   any other it runs: its computation synthesises a returner whose result
    ///   crosses the value bridge to `expected`, and it is recorded run; a
    ///   constructor checked at a staged type checks as
    ///   [`Self::staged_constructor`] does; a synthesising value synthesises,
    ///   then crosses the value bridge to `expected`. Every other rule
    ///   descends.
    /// - fails: [`CheckRefusal::ShapeMismatch`] for a thunk against no thunk
    ///   type, a pair against no eager product or dependent pair, a pair of
    ///   other than two components against a dependent pair, a static lambda
    ///   against no static Pi; [`CheckRefusal::OutOfFragment`] for an injection
    ///   and a value lift.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one value of every former checked, against its own
    ///   former and another; a thunk checked at a type kept in a region, and a
    ///   variable already kept there bound again at that type.
    /// - witness: `judgement::tests::every_value_former_is_answered_in_both_modes`
    /// - witness: `judgement::tests::a_pair_synthesises_its_eager_product_and_checks_against_one`
    /// - witness: `judgement::tests::a_pair_checks_against_a_dependent_pair_at_its_first_components_fibre`
    /// - witness: `judgement::tests::a_static_lambda_checks_only_against_a_static_pi`
    /// - witness: `judgement::tests::a_hole_synthesises_the_unknown_type_and_checks_against_any`
    /// - witness: `module::tests::a_nested_computation_is_decided_by_its_expected_type`
    /// - witness: `module::tests::a_call_returning_a_function_runs_where_one_is_read_2327`
    /// - witness: `module::tests::a_nested_argument_binds_the_implicit_it_is_read_at`
    /// - witness: `judgement::access::tests::a_view_kept_in_a_region_lives_as_long_as_its_scope`
    ///
    /// # Judgement
    /// - expected: `expected`
    #[spec(
        captures: depth = self.frames.len(),
        ensures: |ret| ret.is_err()
            || (self.frames.len() >= depth && matches!(ret, Ok(Step::Descend(_) | Step::Ascend(Produced::Checked)))),
    )]
    fn check_value(
        &mut self,
        term: ValueId,
        expected: ValueTypeId,
    ) -> Result<Step, CheckRefusal>
    {
        // An introduction form enters a region at the type it keeps; a value
        // that synthesises crosses the bridge to the kept type itself, so a
        // value already kept there stays kept.
        let mut entered = expected;
        let mut expected = expected;
        while let ValueTypeView::Kept { value, .. } =
            value_type_view(self.context.arena(), expected)?
        {
            expected = value;
        }
        let introduction = matches!(
            *self.value(term)?,
            Value::Tuple(_)
                | Value::Literal(_)
                | Value::Constructor { .. }
                | Value::Thunk(_)
                | Value::Record(_)
                | Value::Quote(_)
                | Value::ListNil
                | Value::ListCons(..)
        );
        // An introduction checked at an identity of the unit type checks at
        // the unit type, and one at an identity of a lawful atom at the
        // relation between its endpoints, the atom's identity system,
        // whether its own rule or its synthesis reads it; at a lawless one
        // it is refused, the relation being no identity without its law.
        if introduction && let Some(fibre) = self.identity_fibre(term, expected)? {
            expected = fibre;
            entered = fibre;
        }
        // One checked at a bridge checks at the bridge fold's fibre between
        // its endpoints. `funext` at a bridge between two functions checks at
        // their identity: on the first-order codes it decides, a bridge between
        // two inputs is their identity, so the two folds relate the same
        // functions, and the kernel replays it at the bridge as written.
        else if let funext = matches!(*self.value(term)?, Value::Funext(..))
            && (introduction || funext)
            && let head = self.context.whnf_value_type(expected)?
            && let ValueTypeView::Bridge {
                carrier,
                left,
                right,
            } = value_type_view(self.context.arena(), head)?
        {
            let read = if funext {
                let function = self.context.whnf_value_type(carrier)?;
                if let ValueTypeView::Thunk(_) = value_type_view(self.context.arena(), function)? {
                    crate::relatedness::Fibre::Read(
                        self.context
                            .arena_mut()
                            .value_type_path(carrier, left, right),
                    )
                }
                else {
                    crate::relatedness::Fibre::Written
                }
            }
            else {
                crate::relatedness::fibre(self.context, term, (head, carrier, left, right))?
            };
            if let crate::relatedness::Fibre::Read(fibre) = read {
                expected = fibre;
                entered = fibre;
            }
        }
        // A constructor checked at a stage stands above its recursive fields.
        if matches!(*self.value(term)?, Value::Constructor { .. })
            && let Maybe::Present(owed) =
                crate::recursion::constructor_owes(self.context, expected)?
        {
            return self.staged_constructor(term, expected, owed);
        }
        match *self.value(term)? {
            Value::Record(_) => self.check_native_record(term, expected),
            Value::Reify(_) => {
                let (input, _) = self.stack_expected(term, expected)?;
                Ok(Step::Descend(Goal::Stack {
                    judgement: StackJudgement {
                        at: term,
                        expected,
                        consumed: input,
                    },
                    position: Ordinal::FIRST,
                    input,
                }))
            },
            Value::ListNil => {
                self.list_expected(term, expected)?;
                Ok(Step::Ascend(Produced::Checked))
            },
            Value::ListCons(first, second) => {
                let element = self.list_expected(term, expected)?;
                self.wait(Frame::PairSecond { second, expected });
                Ok(Step::Descend(Goal::Value {
                    term: first,
                    direction: Direction::Check(element),
                }))
            },
            Value::Thunk(body) => {
                let body_type = self.thunk_expected(term, expected)?;
                self.wait(Frame::ThunkBody);
                self.forming(term);
                Ok(Step::Descend(Goal::Computation {
                    term: body,
                    direction: Direction::Check(body_type),
                }))
            },
            Value::Nested(computation) => {
                let head = self.context.whnf_value_type(expected)?;
                // The decode of an implicit no argument has bound yet is no
                // thunk the author wrote: the computation runs, and the type
                // it returns binds the implicit across the bridge.
                let matched = if self
                    .context
                    .deferrals()
                    .unbound(self.context.arena(), head)
                    .is_some()
                {
                    Maybe::Absent(matching::Absent::Mismatched)
                }
                else {
                    matched_thunk(self.context.arena_mut(), head)
                };
                match matched {
                    Maybe::Present(body_type) => {
                        // Against a thunk whose body no returner converts
                        // with, a call is read by what it synthesises.
                        if self.nested_read(computation, body_type)? == NestedRead::Call {
                            self.wait(Frame::NestedCall {
                                at: term,
                                call: computation,
                                expected: entered,
                                body: body_type,
                            });
                            return Ok(Step::Descend(Goal::Computation {
                                term: computation,
                                direction: Direction::Synthesise,
                            }));
                        }
                        self.context.record_nesting(term, Nesting::Suspended);
                        self.wait(Frame::ThunkBody);
                        Ok(Step::Descend(Goal::Computation {
                            term: computation,
                            direction: Direction::Check(body_type),
                        }))
                    },
                    Maybe::Absent(matching::Absent::Mismatched) => {
                        self.wait(Frame::ValueBridge {
                            at: term,
                            expected: entered,
                        });
                        self.wait(Frame::Ran {
                            at: term,
                            read: Read::Goal,
                        });
                        Ok(Step::Descend(Goal::Computation {
                            term: computation,
                            direction: Direction::Synthesise,
                        }))
                    },
                    Maybe::Absent(matching::Absent::Dangling) => Err(CheckRefusal::DanglingNode {
                        node: CoreNode::Type(TypeNode::Value(head)),
                    }),
                }
            },
            Value::Tuple(ref components) if !components.is_empty() => {
                let count = components.len();
                let head = self.context.whnf_value_type(expected)?;
                let view = value_type_view(self.context.arena(), head)?;
                if let ValueTypeView::Sigma { first, second } = view {
                    return self.dependent_pair(term, expected, first, second);
                }
                let mut expected = expected;
                if let ValueTypeView::Path {
                    carrier,
                    left,
                    right,
                } = view
                {
                    let base = self.context.whnf_value_type(carrier)?;
                    let fibre = value_type_view(self.context.arena(), base)?;
                    let factors = if let ValueTypeView::Product(parts) = fibre
                        && parts.len() == count
                    {
                        Some(parts.to_vec())
                    }
                    else {
                        None
                    };
                    if let ValueTypeView::Sigma { first, second } = fibre
                        && count == 2
                    {
                        let (paths, over) = self.sigma_identity(first, second, left, right)?;
                        return self.dependent_pair(term, expected, paths, over);
                    }
                    if let Some(parts) = factors {
                        expected = self.product_identity(&parts, left, right)?;
                    }
                }
                let factors = self.product_expected(term, expected)?;
                if matches!(factors, Components::Known(ref parts) if parts.len() != count) {
                    return Err(CheckRefusal::ShapeMismatch {
                        at: TermNode::Value(term),
                        wanted: ExpectedShape::Product,
                        found: TypeNode::Value(expected),
                    });
                }
                let Some(components) = self.context.arena().value(term).and_then(Value::components)
                else {
                    return Err(CheckRefusal::MachineInvariant);
                };
                let owner = self.owner;
                for (index, &component) in components.iter().enumerate().rev() {
                    let factor = match factors {
                        Components::Known(ref parts) => {
                            *parts.get(index).ok_or(CheckRefusal::MachineInvariant)?
                        },
                        Components::Unknown(unknown) => unknown,
                    };
                    self.frames.push(Waiting {
                        frame: Frame::NativeNext(Goal::Value {
                            term: component,
                            direction: Direction::Check(factor),
                        }),
                        owner,
                    });
                }
                Ok(Step::Ascend(Produced::Checked))
            },
            Value::StaticLambda(body) => {
                let (domain, codomain) = self.static_pi_expected(term, expected)?;
                self.context.binders().open(Zone::Intuitionistic, domain);
                self.wait(Frame::LambdaBody);
                Ok(Step::Descend(Goal::Value {
                    term: body,
                    direction: Direction::Check(codomain),
                }))
            },
            Value::Here(point) => match self.reflexive_expected(TermNode::Value(term), expected)? {
                PathReading::Known {
                    carrier,
                    left,
                    right,
                } => {
                    self.wait(Frame::HereEndpoints {
                        at: term,
                        point,
                        left,
                        right,
                    });
                    Ok(Step::Descend(Goal::Value {
                        term: point,
                        direction: Direction::Check(carrier),
                    }))
                },
                PathReading::Unknown(unknown) => Ok(Step::Descend(Goal::Value {
                    term: point,
                    direction: Direction::Check(unknown),
                })),
            },
            Value::Recorded(_) => self.check_recorded(term, expected),
            Value::Dialogue(_) => self.check_dialogue(term, expected),
            // Against an identity at `Type`, a univalence checks its record
            // against the record type the two codes name, so a record literal
            // checks; the path it then synthesises meets `expected` at the
            // bridge. Against any other type it is synthesised.
            Value::Univalence(record, forward) => {
                match crate::univalence::checked(self.context, (record, forward), expected)? {
                    crate::univalence::Reading::Record {
                        record: record_type,
                        path,
                    } => {
                        self.wait(Frame::ValueBridge {
                            at: term,
                            expected: entered,
                        });
                        self.wait(Frame::UnivalenceChecked { path });
                        Ok(Step::Descend(Goal::Value {
                            term: record,
                            direction: Direction::Check(record_type),
                        }))
                    },
                    crate::univalence::Reading::Synthesised => {
                        self.wait(Frame::ValueBridge {
                            at: term,
                            expected: entered,
                        });
                        Ok(Step::Descend(Goal::Value {
                            term,
                            direction: Direction::Synthesise,
                        }))
                    },
                }
            },
            Value::Stay(point) => {
                let head = self.context.whnf_value_type(expected)?;
                if let ValueTypeView::Flow {
                    carrier,
                    source: left,
                    target: right,
                } = value_type_view(self.context.arena(), head)?
                {
                    self.wait(Frame::StayEndpoints {
                        at: term,
                        point,
                        carrier,
                        left,
                        right,
                    });
                    return Ok(Step::Descend(Goal::Value {
                        term: point,
                        direction: Direction::Check(carrier),
                    }));
                }
                self.wait(Frame::ValueBridge {
                    at: term,
                    expected: entered,
                });
                Ok(Step::Descend(Goal::Value {
                    term,
                    direction: Direction::Synthesise,
                }))
            },
            Value::FunctionFlow(..) => {
                self.wait(Frame::ArrowAgainst { at: term, expected });
                Ok(Step::Descend(Goal::Value {
                    term,
                    direction: Direction::Synthesise,
                }))
            },
            Value::PathRefl(_)
            | Value::Returned(_)
            | Value::Run(_)
            | Value::RecordUpdate { .. }
            | Value::Funext(..)
            | Value::Equiv(..)
            | Value::Ua { .. }
            | Value::Constructor { .. }
            | Value::PathProduct(..)
            | Value::PathEquiv { .. }
            | Value::Primitive { .. }
            | Value::Variable { .. }
            | Value::Constant(_)
            | Value::Tuple(_)
            | Value::Literal(_)
            | Value::Quote(_)
            | Value::QuoteComputation(_)
            | Value::StaticApplication(..)
            | Value::SessionRelated { .. }
            | Value::Then(..)
            | Value::FlowProduct(..)
            | Value::Forward(_)
            | Value::Web(_)
            | Value::Row(_)
            | Value::Ascribe { .. } => {
                self.wait(Frame::ValueBridge {
                    at: term,
                    expected: entered,
                });
                Ok(Step::Descend(Goal::Value {
                    term,
                    direction: Direction::Synthesise,
                }))
            },
            Value::Injection(summand, value) => {
                let summand = match self.sum_expected(term, expected)? {
                    Components::Known(parts) => {
                        *parts
                            .get(usize::from(summand))
                            .ok_or(CheckRefusal::ShapeMismatch {
                                at: TermNode::Value(term),
                                // The sum is met, so what it lacks is the
                                // summand the injection names: any, when it
                                // is the empty sum (#2340).
                                wanted: if parts.is_empty() {
                                    ExpectedShape::EmptySum
                                }
                                else {
                                    ExpectedShape::Summand
                                },
                                found: TypeNode::Value(expected),
                            })?
                    },
                    Components::Unknown(unknown) => unknown,
                };
                self.wait(Frame::InjectionPayload);
                Ok(Step::Descend(Goal::Value {
                    term: value,
                    direction: Direction::Check(summand),
                }))
            },
            Value::Lift { .. } => Err(unadmitted_value(term, UnadmittedFormer::ValueLift)),
            Value::Hole(hole) => match hole.origin() {
                HoleOrigin::Nominated | HoleOrigin::Wildcard => {
                    self.context.nominate(term, hole)?;
                    Ok(Step::Ascend(Produced::Checked))
                },
                // The tactic answers at the goal, and its answer is judged
                // against it as the next goal; a refusal there names the
                // tactic ([`Self::spliced_refusal`]).
                HoleOrigin::Spliced => {
                    let answer = crate::tactic::answer(self.context, term, hole, expected)?;
                    self.wait(Frame::Spliced {
                        at: term,
                        hole,
                        answer,
                    });
                    Ok(Step::Descend(Goal::Value {
                        term: answer,
                        direction: Direction::Check(expected),
                    }))
                },
                HoleOrigin::Written => Ok(Step::Ascend(Produced::Checked)),
            },
            Value::Mark { .. } => Ok(Step::Ascend(Produced::Checked)),
        }
    }

    /// Start the static application `at`: the root head's synthesis is the
    /// next goal, with one frame per argument awaiting the type the spine so
    /// far has, the first argument's innermost.
    ///
    /// # Specification
    /// - requires: `at` is a static application.
    /// - ensures: the frames, outermost last, name each argument with its
    ///   position and the spine's length; the head's synthesis is the step,
    ///   above at least one new frame.
    /// - fails: [`CheckRefusal::DanglingNode`] for a node the arena does not
    ///   hold; [`CheckRefusal::MachineInvariant`] for a spine past the `u32`
    ///   ceiling.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`CheckRefusal`] — as above.
    ///
    /// # Termination
    /// - reason: the `while let` loop descends the spine's heads, and the `for`
    ///   loop walks the arguments it collected, not recursion.
    /// - measure: the arena position of the head, which a static application
    ///   holds below its own; then the arguments left.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — separated by a saturated instance, one past its
    ///   arity, one of a code that is no operator, and one whose argument
    ///   misses its classifier at either position.
    /// - witness: `bridge::tests::family_applied_at_wrong_arity_raises_the_exact_variant`
    /// - witness: `bridge::tests::family_argument_at_wrong_classifier_raises_the_exact_variant`
    #[spec(
        captures: depth = self.frames.len(),
        ensures: |ret| ret.is_err()
            || (matches!(ret, Ok(Step::Descend(_))) && self.frames.len() > depth),
    )]
    fn static_application(
        &mut self,
        at: ValueId,
    ) -> Result<Step, CheckRefusal>
    {
        let mut arguments = Vec::new();
        let mut head = at;
        while let Value::StaticApplication(function, argument) = *self.value(head)? {
            arguments.push(argument);
            head = function;
        }
        let length =
            u32::try_from(arguments.len()).map_err(|_overflow| CheckRefusal::MachineInvariant)?;
        let spine = StaticArity::from(length);
        let mut position = length;
        for argument in arguments {
            position = position
                .checked_sub(1)
                .ok_or(CheckRefusal::MachineInvariant)?;
            self.wait(Frame::StaticSpine {
                at,
                position: ArgumentPosition::from(position),
                argument,
                spine,
            });
        }
        Ok(Step::Descend(Goal::Value {
            term: head,
            direction: Direction::Synthesise,
        }))
    }

    /// Check the recorded run `term` against `expected`: the monitor replays
    /// its skeleton, then each payload checks against the type its move names.
    ///
    /// # Specification
    /// - requires: `term` is a recorded run.
    /// - ensures: one queued check per payload, in move order, once the
    ///   protocol of the run or prefix type `expected` accepts the run's
    ///   skeleton.
    /// - fails: as [`crate::flow::run_premises`].
    /// - panics: none.
    ///
    /// # Errors
    /// - [`CheckRefusal`] — as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a complete seat run checks, a run with a payload of
    ///   the wrong type is refused by that payload's mismatch, a paused run is
    ///   refused at its pause.
    /// - witness: `flow::tests::a_run_rides_forward_and_refuses_by_move`
    #[spec(
        captures: depth = self.frames.len(),
        ensures: |ret| ret.is_err() || (ret == Ok(Step::Ascend(Produced::Checked)) && self.frames.len() >= depth),
    )]
    fn check_recorded(
        &mut self,
        term: ValueId,
        expected: ValueTypeId,
    ) -> Result<Step, CheckRefusal>
    {
        let premises = crate::flow::run_premises(self.context, term, expected)?;
        let owner = self.owner;
        self.frames.extend(
            premises
                .iter()
                .rev()
                .map(|&(payload, payload_type)| Waiting {
                    frame: Frame::NativeNext(Goal::Value {
                        term: payload,
                        direction: Direction::Check(payload_type),
                    }),
                    owner,
                }),
        );
        Ok(Step::Ascend(Produced::Checked))
    }

    /// Check the dialogue `term` against `expected`: each endpoint's moves
    /// replay against its protocol, every message is received as sent and
    /// the log is one linearization of the dialogue's causal web, then each
    /// payload checks against the type its endpoint's move names.
    ///
    /// # Specification
    /// - requires: `term` is a dialogue.
    /// - ensures: one queued check per payload, the left endpoint's in move
    ///   order and then the right's, once the dialogue type `expected` admits
    ///   the dialogue.
    /// - fails: as [`crate::flow::dialogue_premises`].
    /// - panics: none.
    ///
    /// # Errors
    /// - [`CheckRefusal`] — as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a dialogue of one message checks, two logs of one
    ///   dialogue check alike, a receipt of another payload is unmatched, a
    ///   receipt logged before its send is inverted, and a move off its
    ///   endpoint's protocol is refused at that move.
    /// - witness: `flow::tests::a_dialogue_checks_by_its_web_and_refuses_by_move`
    #[spec(
        captures: depth = self.frames.len(),
        ensures: |ret| ret.is_err() || (ret == Ok(Step::Ascend(Produced::Checked)) && self.frames.len() >= depth),
    )]
    fn check_dialogue(
        &mut self,
        term: ValueId,
        expected: ValueTypeId,
    ) -> Result<Step, CheckRefusal>
    {
        let premises = crate::flow::dialogue_premises(self.context, term, expected)?;
        let owner = self.owner;
        self.frames.extend(
            premises
                .iter()
                .rev()
                .map(|&(payload, payload_type)| Waiting {
                    frame: Frame::NativeNext(Goal::Value {
                        term: payload,
                        direction: Direction::Check(payload_type),
                    }),
                    owner,
                }),
        );
        Ok(Step::Ascend(Produced::Checked))
    }

    /// Whether the argument `argument` a computation applies at a static Pi is
    /// rigid: a static lambda, a static definition and an unsaturated
    /// instance of one normalize away, and the kernel has no static lambda.
    ///
    /// # Specification
    /// - requires: `argument` checked against a static Pi.
    /// - ensures: success when `argument`, reduced at its head, is a spine
    ///   whose root is neither a static lambda nor a code constant with a body.
    /// - fails: [`CheckRefusal::StaticLambdaArgument`] at `argument` otherwise;
    ///   the unfolding's refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`CheckRefusal`] — as above.
    ///
    /// # Termination
    /// - reason: the `while let` loop descends the spine's heads, not
    ///   recursion.
    /// - measure: the arena position of the head, which a static application
    ///   holds below its own.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — separated by a static lambda, a static definition and
    ///   an opaque operator, each at a dynamic parameter.
    /// - witness: `bridge::tests::a_static_lambda_at_a_dynamic_parameter_is_refused_by_name`
    #[spec(ensures: |ret| match ret {
        | Err(CheckRefusal::StaticLambdaArgument { at }) => at == argument,
        | Ok(()) | Err(_) => true,
    })]
    fn rigid_operator(
        &mut self,
        argument: ValueId,
    ) -> Result<(), CheckRefusal>
    {
        let mut root = self.context.whnf_code(argument)?;
        while let Value::StaticApplication(function, _) = *self.value(root)? {
            root = function;
        }
        let normalizes_away = match *self.value(root)? {
            Value::StaticLambda(_) => true,
            Value::Constant(constant) => {
                matches!(self.context.definitions().body(constant), Maybe::Present(_))
            },
            Value::PathRefl(_)
            | Value::Here(_)
            | Value::Funext(..)
            | Value::Equiv(..)
            | Value::Univalence(..)
            | Value::Ua { .. }
            | Value::Returned(_)
            | Value::Nested(_)
            | Value::Run(_)
            | Value::RecordUpdate { .. }
            | Value::Constructor { .. }
            | Value::Record(_)
            | Value::Reify(_)
            | Value::Primitive { .. }
            | Value::PathProduct(..)
            | Value::PathEquiv { .. }
            | Value::Variable { .. }
            | Value::Tuple(_)
            | Value::ListNil
            | Value::ListCons(..)
            | Value::Literal(_)
            | Value::Injection(..)
            | Value::Thunk(_)
            | Value::Ascribe { .. }
            | Value::Lift { .. }
            | Value::Quote(_)
            | Value::QuoteComputation(_)
            | Value::StaticApplication(..)
            | Value::Hole(_)
            | Value::Mark { .. }
            | Value::SessionRelated { .. }
            | Value::Stay(_)
            | Value::Then(..)
            | Value::FlowProduct(..)
            | Value::Forward(_)
            | Value::FunctionFlow(..)
            | Value::Recorded(_)
            | Value::Dialogue(_)
            | Value::Web(_)
            | Value::Row(_) => false,
        };
        if normalizes_away {
            Err(CheckRefusal::StaticLambdaArgument { at: argument })
        }
        else {
            Ok(())
        }
    }

    /// Read `value` where no thunk stands: a case's, a split's or a list
    /// case's scrutinee, the record or tuple a projection reads, the path an
    /// element transport follows, or a record update's base. A computation
    /// written there runs, and its type is the one it returns; any other value
    /// synthesises.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: for a nested computation, [`Frame::Ran`] waits on `value`,
    ///   read as [`Read::Unsuspended`] so the run keeps `value`'s typing at
    ///   what it returns, and the step descends to synthesise the computation;
    ///   for any other value, the step descends to synthesise it.
    /// - fails: [`CheckRefusal::DanglingNode`] for a value the arena does not
    ///   hold.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a comparison written as a case's scrutinee runs and
    ///   the case reads its answer, as a path written as a call does; the
    ///   scrutinee's typing is kept once, at what it returns; a field of a
    ///   field runs the inner projection and reads the record it returns.
    /// - witness: `module::tests::a_computation_written_as_a_scrutinee_runs_1141`
    /// - witness: `module::tests::a_computation_written_as_a_projected_record_runs_1106`
    #[spec(
        captures: [
            before = self.frames.len(),
            nested = matches!(self.context.arena().value(value), Some(&Value::Nested(_))),
        ],
        ensures: |ret| ret.is_err() || (matches!(ret, Ok(Step::Descend(_))) && before.checked_add(usize::from(nested)) == Some(self.frames.len())),
    )]
    fn unsuspended(
        &mut self,
        value: ValueId,
    ) -> Result<Step, CheckRefusal>
    {
        if let Value::Nested(computation) = *self.value(value)? {
            self.wait(Frame::Ran {
                at: value,
                read: Read::Unsuspended,
            });
            return Ok(Step::Descend(Goal::Computation {
                term: computation,
                direction: Direction::Synthesise,
            }));
        }
        Ok(Step::Descend(Goal::Value {
            term: value,
            direction: Direction::Synthesise,
        }))
    }

    /// The synthesis rules over computations.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a force awaits its value's synthesised type; a return awaits
    ///   its value's; an application awaits its head's; a bind awaits its bound
    ///   computation's; a transport awaits its path's, a data case or a split
    ///   its scrutinee's and a projection its record's, each read by
    ///   [`Self::unsuspended`], so a computation nested there waits a second
    ///   frame, the run's; an ascription forms its stated type, checks its body
    ///   against it and synthesises it; a hole and a mark have the unknown
    ///   computation type, minted, and ascend.
    /// - fails: [`CheckRefusal::NotSynthesisable`] for a lambda or a fixpoint;
    ///   [`CheckRefusal::OutOfFragment`] for a case.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — force, application and bind expose their synthesised
    ///   types while introductions and case expose exact refusals; L1 free
    ///   pools compare the faces, separating wrong child goals and frames.
    /// - witness: `judgement::tests::every_comp_former_is_answered_in_both_modes`
    /// - witness: `judgement::tests::the_faces_agree_on_free_terms`
    /// - witness: `judgement::tests::a_hole_synthesises_the_unknown_type_and_checks_against_any`
    /// - witness: `tests::native_formers::a_composite_along_a_returned_path_cancels_in_both_checkers`
    /// - witness: `judgement::tests::an_ascription_checks_its_body_and_synthesises_its_type`
    #[spec(
        captures: before = self.frames.len(),
        ensures: |ret| ret.is_err() || (matches!(ret, Ok(Step::Descend(_)))
            && (self.frames.len().checked_sub(before) == Some(1)
                || (self.frames.len().checked_sub(before) == Some(2)
                    && matches!(self.frames.last().map(|waiting| waiting.frame), Some(Frame::Ran { .. })))))
            || (matches!(ret, Ok(Step::Ascend(Produced::CompType(_)))) && self.frames.len() == before),
    )]
    fn synthesise_comp(
        &mut self,
        term: ComputationId,
    ) -> Result<Step, CheckRefusal>
    {
        match *self.computation(term)? {
            Computation::DataCase { scrutinee, .. } => {
                self.wait(Frame::NativeCase(term));
                self.unsuspended(scrutinee)
            },
            Computation::RecordProjection(record, _) | Computation::TupleProjection(record, _) => {
                self.wait(Frame::NativeProjection(term));
                self.unsuspended(record)
            },
            Computation::Ascribe { body, ty } => {
                self.wait(Frame::Ascription { body, ty });
                Ok(Step::Descend(Goal::Form(TypeNode::Computation(ty))))
            },
            Computation::Perform {
                ref signature,
                ref operation,
                payload,
            } => {
                let Maybe::Present(operation) = signature.operation(operation)
                else {
                    return Err(CheckRefusal::UnknownOperation { at: term });
                };
                let expected = operation.payload;
                let reply = operation.reply;
                let effects = gandr_core_term::effect::EffectRow::singleton(signature.clone());
                // An operation performed by name goes to whichever handler
                // stands nearest when it runs, so any of them may receive the
                // rest of the run as a continuation.
                self.region_captured(term, session::Answerer::Anyone, payload)?;
                self.footprint_performed(term);
                let result = self
                    .context
                    .arena_mut()
                    .comp_type_returner_with_effects(reply, effects);
                self.wait(Frame::PerformPayload {
                    at: term,
                    payload,
                    expected,
                    result,
                });
                Ok(Step::Descend(Goal::Form(TypeNode::Computation(result))))
            },
            Computation::Exercise { capability, .. } => {
                self.wait(Frame::ExerciseCapability { at: term });
                Ok(Step::Descend(Goal::Value {
                    term: capability,
                    direction: Direction::Synthesise,
                }))
            },
            Computation::Scope { .. } => Err(CheckRefusal::NotSynthesisable {
                form: CheckingForm::Scope(term),
            }),
            Computation::Resume(stack, body) => {
                self.ending(term, stack)?;
                self.wait(Frame::Resume { stack, body });
                Ok(Step::Descend(Goal::Value {
                    term: stack,
                    direction: Direction::Synthesise,
                }))
            },
            Computation::Abandon(stack) => {
                // An unwind runs to completion under the empty row, which
                // carries no abandonment.
                if self
                    .frames
                    .iter()
                    .any(|waiting| matches!(waiting.frame, Frame::AccessUnwind { .. }))
                {
                    return Err(CheckRefusal::Access {
                        at: CoreNode::Term(TermNode::Computation(term)),
                        defect: crate::access::AccessDefect::UnwindEffect,
                    });
                }
                self.ending(term, stack)?;
                self.wait(Frame::Abandon { stack });
                Ok(Step::Descend(Goal::Value {
                    term: stack,
                    direction: Direction::Synthesise,
                }))
            },
            Computation::Project(component, subject) => {
                self.wait(Frame::Project {
                    at: term,
                    component,
                });
                Ok(Step::Descend(Goal::Computation {
                    term: subject,
                    direction: Direction::Synthesise,
                }))
            },
            Computation::Handle { .. } => Err(CheckRefusal::NotSynthesisable {
                form: CheckingForm::Handle(term),
            }),
            Computation::Reset(_) => Err(CheckRefusal::NotSynthesisable {
                form: CheckingForm::Reset(term),
            }),
            Computation::Shift(_) => Err(CheckRefusal::NotSynthesisable {
                form: CheckingForm::Shift(term),
            }),
            Computation::With(..) => Err(CheckRefusal::NotSynthesisable {
                form: CheckingForm::With(term),
            }),
            Computation::ListFold {
                element, result, ..
            } => {
                let result = self.context.arena_mut().comp_type_returner(result);
                self.wait(Frame::ListFold {
                    at: term,
                    result,
                    phase: ListPhase::Element,
                });
                Ok(Step::Descend(Goal::Form(TypeNode::Value(element))))
            },
            Computation::Primitive {
                primitive,
                arguments,
            } => {
                let domains = primitive.arguments();
                if domains.len() != arguments.len() {
                    return Err(CheckRefusal::MachineInvariant);
                }
                let arena = self.context.arena_mut();
                let result = primitive.result().mint(arena);
                let result = arena.comp_type_returner(result);
                let first_domain = domains
                    .first()
                    .ok_or(CheckRefusal::MachineInvariant)?
                    .mint(arena);
                let first = match arguments {
                    gandr_core_term::primitive::Arguments::Unary(argument) => {
                        self.wait(Frame::PrimitiveResult { result });
                        argument
                    },
                    gandr_core_term::primitive::Arguments::Binary([first, second]) => {
                        let expected = domains
                            .get(1)
                            .ok_or(CheckRefusal::MachineInvariant)?
                            .mint(arena);
                        self.wait(Frame::PrimitiveSecond {
                            argument: second,
                            expected,
                            result,
                        });
                        first
                    },
                };
                Ok(Step::Descend(Goal::Value {
                    term: first,
                    direction: Direction::Check(first_domain),
                }))
            },
            Computation::PathTransport {
                motive,
                path,
                value,
            } => {
                self.wait(Frame::ElementTransportPath {
                    at: term,
                    motive,
                    value,
                });
                self.unsuspended(path)
            },
            Computation::Ride {
                motive,
                flow,
                value,
            } => {
                self.wait(Frame::RideFlow {
                    at: term,
                    motive,
                    value,
                });
                Ok(Step::Descend(Goal::Value {
                    term: flow,
                    direction: Direction::Synthesise,
                }))
            },
            Computation::TelescopeTransport { path, .. } => {
                self.wait(Frame::TelescopePath { at: term });
                Ok(Step::Descend(Goal::Value {
                    term: path,
                    direction: Direction::Synthesise,
                }))
            },
            Computation::Transport(path, value) => {
                self.wait(Frame::TransportPath { path, value });
                Ok(Step::Descend(Goal::Value {
                    term: path,
                    direction: Direction::Synthesise,
                }))
            },
            Computation::Force(value) => {
                self.wait(Frame::Force { value });
                Ok(Step::Descend(Goal::Value {
                    term: value,
                    direction: Direction::Synthesise,
                }))
            },
            Computation::Decompose(dialogue) => {
                self.wait(Frame::Decompose { dialogue });
                Ok(Step::Descend(Goal::Value {
                    term: dialogue,
                    direction: Direction::Synthesise,
                }))
            },
            Computation::Application(head, argument) => {
                self.wait(Frame::ApplicationHead { head, argument });
                Ok(Step::Descend(Goal::Computation {
                    term: head,
                    direction: Direction::Synthesise,
                }))
            },
            Computation::Lambda(_) => Err(CheckRefusal::NotSynthesisable {
                form: CheckingForm::Lambda(term),
            }),
            Computation::Return(value) => {
                self.wait(Frame::ReturnValue);
                Ok(Step::Descend(Goal::Value {
                    term: value,
                    direction: Direction::Synthesise,
                }))
            },
            Computation::Fixpoint { .. } => Err(CheckRefusal::NotSynthesisable {
                form: CheckingForm::Fixpoint(term),
            }),
            Computation::Bind(bound, body) => {
                Ok(self.bind(term, bound, body, Direction::Synthesise))
            },
            Computation::Case { .. } | Computation::ListCase { .. } => {
                Err(CheckRefusal::NotSynthesisable {
                    form: CheckingForm::Case(term),
                })
            },
            Computation::Split {
                scrutinee,
                motive: SplitMotive::Scrutinee(_),
                ..
            } => {
                self.wait(Frame::SigmaSplitScrutinee(term));
                self.unsuspended(scrutinee)
            },
            Computation::Split {
                scrutinee,
                motive: SplitMotive::Ambient,
                ..
            } => {
                self.wait(Frame::SplitScrutinee {
                    at: term,
                    scrutinee,
                    direction: Direction::Synthesise,
                });
                self.unsuspended(scrutinee)
            },
            Computation::Session(_) => self.session(term, Direction::Synthesise),
            Computation::Memory(_) => self.memory(term, Direction::Synthesise),
            Computation::World(_) => self.world(term, Direction::Synthesise),
            Computation::Hole(hole)
                if matches!(self.context.pattern_hole(hole), Maybe::Present(_)) =>
            {
                Err(CheckRefusal::UndecidedCoverage(term))
            },
            Computation::Hole(_) | Computation::Mark { .. } => {
                let unknown = self.context.arena_mut().comp_type_unknown();
                Ok(Step::Ascend(Produced::CompType(unknown)))
            },
        }
    }

    /// The checking rules over computations.
    ///
    /// # Specification
    /// - requires: `expected` is formed.
    /// - ensures: a lambda opens a binder of the domain `expected` matches as a
    ///   function type at its weak head, and its body checks against the
    ///   codomain — an arrow's shifted past the binder, a dependent arrow's as
    ///   it stands; a return's value checks against the result it matches as a
    ///   returner; a bind awaits its bound computation's synthesised type, then
    ///   checks its body against `expected` shifted past its binder; a lazy
    ///   product of `n` components matches `expected` as a lazy product of `n`
    ///   and leaves one goal per component, each checked against its own; a
    ///   hole and a mark check against any type at once; a fixpoint opens a
    ///   binder of `U expected` and checks its body against `expected` shifted
    ///   past it, a partial one only at a type stating that it may diverge
    ///   ([`crate::divergence::require`]), except that a structural one opens
    ///   its stage ([`crate::recursion::open_fixpoint`]): the self binder takes
    ///   the recursed-on parameter below the stage and the body takes it at the
    ///   stage; a list case synthesises its list's type, opens one stage below
    ///   it ([`crate::recursion::open_case`]), checks its empty branch against
    ///   `expected` and its cell branch, under a binder of the element and one
    ///   of the tail at that stage, against `expected` shifted past both; an
    ///   applied fixpoint synthesises its argument's type and checks the
    ///   fixpoint against the arrow from it to `expected`; a data case at its
    ///   written motive with the result read at a stage
    ///   ([`crate::recursion::motive_at`]) synthesises its branches at that
    ///   reading; a synthesising computation synthesises, then crosses the
    ///   computation bridge to `expected`.
    /// - fails: [`CheckRefusal::ShapeMismatch`] for a lambda against no arrow,
    ///   a return against no returner, or a structural fixpoint against a type
    ///   with no arrow to recurse on; [`CheckRefusal::OutOfFragment`] for a
    ///   case; as [`crate::divergence::require`] for a partial fixpoint.
    ///
    /// # Judgement
    /// - expected: `expected`
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each computation former checks against its own shape
    ///   or another, including dependent binders; exact acceptance or refusal
    ///   separates wrong child directions and expected-type dispatch.
    /// - witness: `judgement::tests::every_comp_former_is_answered_in_both_modes`
    /// - witness: `judgement::tests::an_introduction_against_the_wrong_former_is_a_shape_mismatch`
    /// - witness: `judgement::tests::a_bind_checks_against_the_expected_computation`
    /// - witness: `judgement::tests::a_hole_synthesises_the_unknown_type_and_checks_against_any`
    /// - witness: `judgement::tests::a_pattern_hole_at_a_leaf_leaves_the_match_undecided`
    /// - witness: `tests::recursive_data::a_fixpoint_checks_at_every_computation_type`
    /// - witness: `recursion::tests::a_recursion_descends_on_its_first_parameter`
    /// - witness: `recursion::tests::a_result_follows_the_parameter_it_recurses_on`
    #[spec(
        captures: before = self.frames.len(),
        ensures: |ret| ret.is_err() || (matches!(ret, Ok(Step::Descend(_))) && self.frames.len() >= before)
            || (matches!(ret, Ok(Step::Ascend(Produced::Checked))) && self.frames.len() == before
                && matches!(self.context.arena().computation(term), Some(Computation::Hole(_) | Computation::Mark { .. })))
            || (matches!(ret, Ok(Step::Ascend(Produced::Checked)))
                && matches!(self.context.arena().computation(term), Some(Computation::With(components)) if before.checked_add(components.len()) == Some(self.frames.len()))),
    )]
    fn check_comp(
        &mut self,
        term: ComputationId,
        expected: CompTypeId,
    ) -> Result<Step, CheckRefusal>
    {
        // A case checked at its written motive with the result read at a stage
        // reads its branches there.
        if let &Computation::DataCase {
            scrutinee, motive, ..
        } = self.computation(term)?
            && let Maybe::Present(read) =
                crate::recursion::motive_at(self.context, motive, expected)?
        {
            self.wait(Frame::CompBridge { at: term, expected });
            self.staged_motives.push((term, read));
            self.wait(Frame::NativeCase(term));
            return self.unsuspended(scrutinee);
        }
        match *self.computation(term)? {
            Computation::Handle { .. } => self.handle(term, expected),
            Computation::Scope { .. } => self.scope(term, expected),
            Computation::Reset(body) => {
                self.wait(Frame::Reset {
                    answer: expected,
                    depth: self.context.depth(Zone::Intuitionistic),
                });
                Ok(Step::Descend(Goal::Computation {
                    term: body,
                    direction: Direction::Check(expected),
                }))
            },
            Computation::Shift(body) => self.shift(term, body, expected),
            Computation::With(ref components) => {
                let count = components.len();
                let parts = self.with_parts(TermNode::Computation(term), expected)?;
                if matches!(parts, Components::Known(ref types) if types.len() != count) {
                    return Err(CheckRefusal::ShapeMismatch {
                        at: TermNode::Computation(term),
                        wanted: ExpectedShape::With,
                        found: TypeNode::Computation(expected),
                    });
                }
                let Some(&Computation::With(ref components)) =
                    self.context.arena().computation(term)
                else {
                    return Err(CheckRefusal::MachineInvariant);
                };
                let owner = self.owner;
                for (index, &component) in components.iter().enumerate().rev() {
                    let component_type = match parts {
                        Components::Known(ref types) => {
                            *types.get(index).ok_or(CheckRefusal::MachineInvariant)?
                        },
                        Components::Unknown(unknown) => unknown,
                    };
                    self.frames.push(Waiting {
                        frame: Frame::Next(Goal::Computation {
                            term: component,
                            direction: Direction::Check(component_type),
                        }),
                        owner,
                    });
                }
                Ok(Step::Ascend(Produced::Checked))
            },
            Computation::Lambda(body) => {
                let (domain, codomain) = self.arrow_expected(term, expected)?;
                self.context.binders().open(Zone::Intuitionistic, domain);
                self.context.open_copy(term);
                self.wait(Frame::LambdaBody);
                Ok(Step::Descend(Goal::Computation {
                    term: body,
                    direction: Direction::Check(codomain),
                }))
            },
            Computation::Return(value) => {
                let result = self.returner_expected(term, expected)?;
                self.wait(Frame::ReturnValue);
                Ok(Step::Descend(Goal::Value {
                    term: value,
                    direction: Direction::Check(result),
                }))
            },
            Computation::Fixpoint { body, evidence } => {
                let position = match evidence {
                    FixpointEvidence::Partial => None,
                    FixpointEvidence::StructuralDescent => Some(StagedPosition::default()),
                    FixpointEvidence::Staged { position } => Some(position),
                };
                let (own, inside) = match position {
                    None => {
                        crate::divergence::require(self.context, term, body, expected)?;
                        (expected, expected)
                    },
                    Some(position) => {
                        self.root = self.fold_root(term, (expected, position), body)?;
                        match crate::recursion::open_fixpoint(
                            self.context,
                            term,
                            expected,
                            position,
                        )? {
                            Maybe::Present(opened) => (opened.own, opened.inside),
                            Maybe::Absent(_unknown) => (expected, expected),
                        }
                    },
                };
                let arena = self.context.arena_mut();
                let recursive = arena.value_type_thunk(own);
                let scoped = shift_comp_type(arena, inside, Binders::from(1_u32)).settle(arena);
                // A structural fixpoint is the definition's own when its body
                // thunks it: inside it, a case reads the definition's
                // constant in its family's fields as this binder.
                if position.is_some() {
                    self.context.open_own(term, recursive);
                }
                self.context.binders().open(Zone::Intuitionistic, recursive);
                self.wait(Frame::LambdaBody);
                Ok(Step::Descend(Goal::Computation {
                    term: body,
                    direction: Direction::Check(scoped),
                }))
            },
            Computation::Application(head, argument)
                if matches!(
                    self.context.arena().computation(head),
                    Some(&Computation::Fixpoint { .. })
                ) =>
            {
                self.wait(Frame::FixpointArgument { head, expected });
                Ok(Step::Descend(Goal::Value {
                    term: argument,
                    direction: Direction::Synthesise,
                }))
            },
            Computation::Primitive { .. }
            | Computation::DataCase { .. }
            | Computation::RecordProjection(..)
            | Computation::TupleProjection(..)
            | Computation::Perform { .. }
            | Computation::Exercise { .. }
            | Computation::Resume(..)
            | Computation::Abandon(_)
            | Computation::Project(..)
            | Computation::ListFold { .. }
            | Computation::Transport(..)
            | Computation::PathTransport { .. }
            | Computation::Ride { .. }
            | Computation::TelescopeTransport { .. }
            | Computation::Force(_)
            | Computation::Decompose(_)
            | Computation::Application(..)
            | Computation::Ascribe { .. }
            | Computation::Split {
                motive: SplitMotive::Scrutinee(_),
                ..
            }
            | Computation::Session(
                SessionAction::Send { .. }
                | SessionAction::Select { .. }
                | SessionAction::Close { .. },
            )
            | Computation::Memory(
                gandr_core_term::memory::MemoryForm::Resume { .. }
                | gandr_core_term::memory::MemoryForm::Abort { .. }
                | gandr_core_term::memory::MemoryForm::Consume { .. },
            ) => {
                self.wait(Frame::CompBridge { at: term, expected });
                Ok(Step::Descend(Goal::Computation {
                    term,
                    direction: Direction::Synthesise,
                }))
            },
            Computation::Bind(bound, body) => {
                Ok(self.bind(term, bound, body, Direction::Check(expected)))
            },
            Computation::Split { scrutinee, .. } => {
                self.wait(Frame::SplitScrutinee {
                    at: term,
                    scrutinee,
                    direction: Direction::Check(expected),
                });
                self.unsuspended(scrutinee)
            },
            Computation::Case { scrutinee, .. } => {
                self.wait(Frame::CaseScrutinee {
                    at: term,
                    scrutinee,
                    expected,
                });
                self.unsuspended(scrutinee)
            },
            Computation::ListCase { list, .. } => {
                self.wait(Frame::ListCaseScrutinee {
                    at: term,
                    scrutinee: list,
                    expected,
                });
                self.unsuspended(list)
            },
            Computation::Session(
                SessionAction::Receive { .. }
                | SessionAction::Offer { .. }
                | SessionAction::Fork { .. }
                | SessionAction::Place { .. },
            ) => self.session(term, Direction::Check(expected)),
            Computation::Memory(
                gandr_core_term::memory::MemoryForm::Hold { .. }
                | gandr_core_term::memory::MemoryForm::Access { .. },
            ) => self.memory(term, Direction::Check(expected)),
            Computation::World(_) => self.world(term, Direction::Check(expected)),
            Computation::Hole(hole)
                if matches!(self.context.pattern_hole(hole), Maybe::Present(_)) =>
            {
                Err(CheckRefusal::UndecidedCoverage(term))
            },
            Computation::Hole(_) | Computation::Mark { .. } => Ok(Step::Ascend(Produced::Checked)),
        }
    }

    /// Start the bind `at` of `bound` into `body`, judged in `direction`.
    ///
    /// # Specification
    /// - requires: `bound` and `body` are the two halves of the bind `at`.
    /// - ensures: the bound computation's synthesis is the next goal, with the
    ///   bind's frame awaiting its type and holding the direction the body is
    ///   judged in.
    /// - provides: the one rule both computation faces share.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the rule's surfaces are the two directions, the
    ///   returner test and the lowering out of the binder, separated by a bind
    ///   synthesising its body's type, a bind checked against its body's type,
    ///   a bind of an arrow-typed computation, and a bind whose body's type
    ///   mentions the bound name, each asserted as the exact type, check or
    ///   refusal.
    /// - witness: `judgement::tests::a_bind_synthesises_its_continuations_type`
    /// - witness: `judgement::tests::a_bind_checks_against_the_expected_computation`
    /// - witness: `judgement::tests::a_bind_of_a_non_returner_is_a_shape_mismatch`
    /// - witness: `judgement::tests::a_bind_whose_type_mentions_its_binder_is_refused`
    #[spec(
        captures: before = self.frames.len(),
        ensures: |ret| self.frames.len().checked_sub(before) == Some(1)
            && self.frames.last().map(|waiting| waiting.frame) == Some(Frame::BindBound { at, bound, body, direction })
            && ret == Step::Descend(Goal::Computation { term: bound, direction: Direction::Synthesise }),
    )]
    fn bind(
        &mut self,
        at: ComputationId,
        bound: ComputationId,
        body: ComputationId,
        direction: Direction<CompTypeId>,
    ) -> Step
    {
        self.wait(Frame::BindBound {
            at,
            bound,
            body,
            direction,
        });

        Step::Descend(Goal::Computation {
            term: bound,
            direction: Direction::Synthesise,
        })
    }

    /// The body a thunk checks against: the one the expected type matches as a
    /// thunk type at its weak head.
    ///
    /// # Specification
    /// - requires: `expected` is formed.
    /// - ensures: the body of `expected` when it is `U C` at its weak head; an
    ///   unknown computation type, minted, when it is the unknown type.
    /// - fails: [`CheckRefusal::ShapeMismatch`] at `at`, wanting a thunk type,
    ///   for any other former; the unfolding's refusal.
    /// - panics: none.
    ///
    /// # Judgement
    /// - expected: `expected`
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a thunk checked against a thunk type, the unknown
    ///   type and an atom exposes the selected body or exact shape refusal;
    ///   defined-code conversion covers a head reached through unfolding.
    /// - witness: `judgement::tests::every_value_former_is_answered_in_both_modes`
    /// - witness: `judgement::tests::an_introduction_against_the_wrong_former_is_a_shape_mismatch`
    /// - witness: `judgement::tests::an_introduction_against_the_unknown_type_checks_its_parts`
    #[spec(ensures: |ret| match ret {
        | Ok(body) => self.context.arena().comp_type(body).is_some()
            && match value_type_view(self.context.arena(), expected) {
                | Ok(ValueTypeView::Thunk(held)) => body == held,
                | Ok(ValueTypeView::Unknown) => matches!(comp_type_view(self.context.arena(), body), Ok(CompTypeView::Unknown)),
                | Ok(_) | Err(_) => true,
            },
        | Err(CheckRefusal::ShapeMismatch { at: named, wanted, found }) => named == TermNode::Value(at)
            && wanted == ExpectedShape::Thunk && found == TypeNode::Value(expected),
        | Err(_) => true,
    })]
    fn thunk_expected(
        &mut self,
        at: ValueId,
        expected: ValueTypeId,
    ) -> Result<CompTypeId, CheckRefusal>
    {
        let head = self.context.whnf_value_type(expected)?;
        match matched_thunk(self.context.arena_mut(), head) {
            Maybe::Present(body) => Ok(body),
            Maybe::Absent(absent) => Err(unmatched(
                absent,
                TypeNode::Value(head),
                CheckRefusal::ShapeMismatch {
                    at: TermNode::Value(at),
                    wanted: ExpectedShape::Thunk,
                    found: TypeNode::Value(expected),
                },
            )),
        }
    }

    /// How a computation written where a thunk is read is judged: a call, read
    /// against a body no returner converts with, may return the function the
    /// thunk holds, so the type it synthesises decides it.
    ///
    /// # Specification
    /// - requires: `body` is formed.
    /// - ensures: [`NestedRead::Call`] exactly when `computation` is an
    ///   application whose head is no fixpoint, or a force — the calls, which
    ///   check by synthesis — and `body` at its weak head is neither a returner
    ///   nor the unknown type; [`NestedRead::Body`] otherwise.
    /// - fails: [`CheckRefusal::DanglingNode`] for a computation the arena does
    ///   not hold; the unfolding's refusal.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a call returning a function, read where that
    ///   function's thunk is read, runs; a call returning a value, read where a
    ///   thunk of its returner is read, stays suspended.
    /// - witness: `module::tests::a_call_returning_a_function_runs_where_one_is_read_2327`
    /// - witness: `module::tests::a_nested_computation_is_decided_by_its_expected_type`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |&read| read == NestedRead::Body
        || matches!(
            self.context.arena().computation(computation),
            Some(&(Computation::Application(..) | Computation::Force(_)))
        )))]
    fn nested_read(
        &mut self,
        computation: ComputationId,
        body: CompTypeId,
    ) -> Result<NestedRead, CheckRefusal>
    {
        let node = self.computation(computation)?;
        let call = if let &Computation::Application(head, _) = node {
            !matches!(
                self.context.arena().computation(head),
                Some(&Computation::Fixpoint { .. })
            )
        }
        else {
            matches!(*node, Computation::Force(_))
        };
        if !call {
            return Ok(NestedRead::Body);
        }
        let head = self.context.whnf_comp_type(body)?;
        if matches!(
            comp_type_view(self.context.arena(), head)?,
            CompTypeView::Returner { .. } | CompTypeView::Unknown
        ) {
            return Ok(NestedRead::Body);
        }
        Ok(NestedRead::Call)
    }

    /// The factors a pair's components check against: the ones the expected
    /// type matches as an eager product at its weak head.
    ///
    /// # Specification
    /// - requires: `expected` is formed.
    /// - ensures: both factors of `expected` when it is `A × B` at its weak
    ///   head, or two unknown types when it is the unknown type, each resolving
    ///   in the arena.
    /// - fails: [`CheckRefusal::ShapeMismatch`] at `at`, wanting an eager
    ///   product, for any other former; the unfolding's refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`CheckRefusal`] — as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — separated by a pair against a product, against the
    ///   unknown type and against an atom.
    /// - witness: `judgement::tests::a_pair_synthesises_its_eager_product_and_checks_against_one`
    /// - witness: `judgement::tests::an_introduction_against_the_unknown_type_checks_its_parts`
    ///
    /// # Judgement
    /// - expected: `expected`
    #[spec(ensures: |ret| match ret {
        | Ok(Components::Known(ref parts)) => {
            parts.iter().all(|&part| self.context.arena().value_type(part).is_some())
        },
        | Ok(Components::Unknown(unknown)) => self.context.arena().value_type(unknown).is_some(),
        | Err(CheckRefusal::ShapeMismatch { at: shaped, wanted, found }) => {
            shaped == TermNode::Value(at)
                && wanted == ExpectedShape::Product
                && found == TypeNode::Value(expected)
        },
        | Err(_) => true,
    })]
    fn product_expected(
        &mut self,
        at: ValueId,
        expected: ValueTypeId,
    ) -> Result<Components, CheckRefusal>
    {
        let head = self.context.whnf_value_type(expected)?;
        match matched_product(self.context.arena_mut(), head) {
            Maybe::Present(factors) => Ok(factors),
            Maybe::Absent(absent) => Err(unmatched(
                absent,
                TypeNode::Value(head),
                CheckRefusal::ShapeMismatch {
                    at: TermNode::Value(at),
                    wanted: ExpectedShape::Product,
                    found: TypeNode::Value(expected),
                },
            )),
        }
    }

    /// Check the pair `term` against the dependent pair `Σ (x : first).
    /// second` that `expected` reads as at its weak head.
    ///
    /// # Specification
    /// - requires: `first` and `second` are the factors of `expected`'s weak
    ///   head, `second` scoped under one binder of `first`.
    /// - ensures: the first component checks against `first` next, and the
    ///   second waits to check against `second` with the first component for
    ///   its binder.
    /// - fails: [`CheckRefusal::ShapeMismatch`] at `term`, wanting a dependent
    ///   pair, for a tuple of other than two components;
    ///   [`CheckRefusal::DanglingNode`] when `term` does not resolve.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`CheckRefusal`] — as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a pair whose second component lies in the fibre over
    ///   its first checks, one at another fibre is refused, and a triple is a
    ///   shape mismatch.
    /// - witness: `judgement::tests::a_pair_checks_against_a_dependent_pair_at_its_first_components_fibre`
    ///
    /// # Judgement
    /// - expected: `expected`
    #[spec(
        captures: depth = self.frames.len(),
        ensures: |ret| match ret {
            | Ok(step) => matches!(step, Step::Descend(_)) && self.frames.len() == depth.saturating_add(1),
            | Err(CheckRefusal::ShapeMismatch { at, wanted, found }) => at == TermNode::Value(term) && wanted == ExpectedShape::Sigma && found == TypeNode::Value(expected),
            | Err(_) => true,
        },
    )]
    fn dependent_pair(
        &mut self,
        term: ValueId,
        expected: ValueTypeId,
        first: ValueTypeId,
        second: ValueTypeId,
    ) -> Result<Step, CheckRefusal>
    {
        let Some(&[left, right]) = self.value(term)?.components()
        else {
            return Err(CheckRefusal::ShapeMismatch {
                at: TermNode::Value(term),
                wanted: ExpectedShape::Sigma,
                found: TypeNode::Value(expected),
            });
        };
        self.read_by_a_type(left);
        let fibre = instantiate_value_type(self.context.arena_mut(), second, left);
        self.wait(Frame::PairSecond {
            second: right,
            expected: fibre,
        });
        Ok(Step::Descend(Goal::Value {
            term: left,
            direction: Direction::Check(first),
        }))
    }

    /// The fibre of the identity at the dependent pair `Σ (x : first).
    /// second` between `left` and `right`, as its two factors: a path between
    /// the first components, and over it a path from the left second
    /// component transported along that path to the right one.
    ///
    /// # Specification
    /// - requires: `first` and `second` are a dependent pair's factors,
    ///   `second` under one binder of `first`; `left` and `right` inhabit it.
    /// - ensures: `Path(first, l₀, r₀)` and, under one binder `p` of it,
    ///   `Path(second[r₀], ⟨tr(x. second, p, l₁)⟩, r₁)`, each endpoint's
    ///   components read by [`pair_components`].
    /// - fails: as [`pair_components`].
    /// - panics: none.
    ///
    /// # Errors
    /// - [`CheckRefusal`] — as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a pair of reflexivities at the identity of a written
    ///   pair with itself checks, one whose second path ends elsewhere is
    ///   refused, and the identity of a declared pair with itself checks with
    ///   the reflexivities of its body's components.
    /// - witness: `judgement::tests::a_pair_of_paths_checks_at_the_identity_of_a_dependent_pair`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |&(paths, over)| self.context.arena().value_type(paths).is_some() && self.context.arena().value_type(over).is_some()))]
    fn sigma_identity(
        &mut self,
        first: ValueTypeId,
        second: ValueTypeId,
        left: ValueId,
        right: ValueId,
    ) -> Result<(ValueTypeId, ValueTypeId), CheckRefusal>
    {
        let [left_first, left_second] = pair_components(self.context, left)?;
        let [right_first, right_second] = pair_components(self.context, right)?;
        let arena = self.context.arena_mut();
        let paths = arena.value_type_path(first, left_first, right_first);
        let at_right = instantiate_value_type(arena, second, right_first);
        let at_right = shift_value_type(arena, at_right, Binders::ONE).settle(arena);
        let motive =
            shift_value_type_under(arena, second, Binders::ONE, Binders::ONE).settle(arena);
        let path = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let moved = shift_value(arena, left_second, Binders::ONE).settle(arena);
        let transport = arena.computation_path_transport(motive, path, moved);
        let transported = arena.value_returned(transport);
        let target = shift_value(arena, right_second, Binders::ONE).settle(arena);
        let over = arena.value_type_path(at_right, transported, target);

        Ok((paths, over))
    }

    /// The fibre of the identity at the product of `parts` between `left`
    /// and `right`: the product of the identities at each factor, between the
    /// two endpoints' components there.
    ///
    /// # Specification
    /// - requires: `parts` are a product's factors; `left` and `right` inhabit
    ///   it.
    /// - ensures: `Path(A₀, l₀, r₀) × … × Path(Aₙ, lₙ, rₙ)`, each endpoint's
    ///   components read by [`tuple_components`].
    /// - fails: as [`tuple_components`].
    /// - panics: none.
    ///
    /// # Errors
    /// - [`CheckRefusal`] — as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a tuple of reflexivities at the identity of a written
    ///   tuple with itself checks, and one whose path ends elsewhere is refused
    ///   at that component.
    /// - witness: `judgement::tests::a_tuple_of_paths_checks_at_the_identity_of_a_product`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |&fibre| self.context.arena().value_type(fibre).is_some()))]
    fn product_identity(
        &mut self,
        parts: &[ValueTypeId],
        left: ValueId,
        right: ValueId,
    ) -> Result<ValueTypeId, CheckRefusal>
    {
        let width = ComponentCount::from(parts.len());
        let lefts = tuple_components(self.context, left, width)?;
        let rights = tuple_components(self.context, right, width)?;
        let arena = self.context.arena_mut();
        let paths: Vec<ValueTypeId> = parts
            .iter()
            .zip(lefts.into_iter().zip(rights))
            .map(|(&part, (from, to))| arena.value_type_path(part, from, to))
            .collect();
        Ok(arena.value_type_product(&paths))
    }

    /// The fibre the introduction `term` checked at an identity reads: at the
    /// unit type, the unit type, the empty tuple of paths as a tuple at a
    /// product is a tuple of paths; at a lawful atom past its seal, the
    /// relation its interface states, between the two endpoints; at an
    /// identity whose identities read as the unit type, the unit type.
    ///
    /// # Specification
    /// - requires: `expected` is formed.
    /// - ensures: when `expected`'s weak head is `Path(A, left, right)`: `A`
    ///   itself when `A`'s weak head is the unit type, and `El(⟨relation left
    ///   right⟩)` at the atom's kind's level when it is an atom whose interface
    ///   states a law, the fibre of that identity instead when its weak head is
    ///   itself an identity whose fibre this reading reaches; when `A` is
    ///   itself an identity, its own fibre read the same way, innermost out,
    ///   and the unit type when that fibre's weak head is the unit type, an
    ///   identity of the unit type being the unit type; nothing otherwise, an
    ///   atom inside its seal reading as its representation.
    /// - fails: [`CheckRefusal::AtomTransport`] at `term` when an atom on the
    ///   way is one whose interface states no law; the unfolding's refusal;
    ///   [`CheckRefusal::MachineInvariant`] for an atom whose kind is no
    ///   universe.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`CheckRefusal`] — as above.
    ///
    /// # Termination
    /// - reason: one `loop` over the carriers under `expected`, not recursion.
    /// - measure: the identity nesting under the current carrier, which each
    ///   identity step lowers, and the admission position of the atom read,
    ///   whose relation is admitted before it and so names no later atom.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the relation's evidence between two points of a
    ///   lawful atom checks at their identity and is refused by name at a
    ///   lawless one, `()` checks at an identity of the unit type between two
    ///   variables and at an identity of the paths of a lawful atom relating by
    ///   the unit type, and the kernel admits each identity checked.
    /// - witness: `bridge::tests::a_lawful_atom_reads_its_relation_as_its_identity_in_both_checkers`
    /// - witness: `bridge::tests::an_atom_stating_no_law_refuses_the_relation_s_evidence_by_name`
    /// - witness: `bridge::tests::j_along_an_atom_relating_by_the_paths_of_the_unit_type_checks_and_replays_1960`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |fibre| fibre.is_none_or(|fibre| self.context.arena().value_type(fibre).is_some())))]
    fn identity_fibre(
        &mut self,
        term: ValueId,
        expected: ValueTypeId,
    ) -> Result<Option<ValueTypeId>, CheckRefusal>
    {
        let head = self.context.whnf_value_type(expected)?;
        let ValueTypeView::Path {
            carrier,
            mut left,
            mut right,
        } = value_type_view(self.context.arena(), head)?
        else {
            return Ok(None);
        };
        let mut carrier = self.context.whnf_value_type(carrier)?;
        let mut nested = false;
        // What an atom's relation reads as at the outermost identity, kept
        // when the identity it reads as has no fibre this reading reaches.
        let mut related_fibre = None;
        loop {
            let view = value_type_view(self.context.arena(), carrier)?;
            if view == ValueTypeView::Unit {
                return Ok(Some(carrier));
            }
            if let ValueTypeView::Path {
                carrier: inner,
                left: from,
                right: to,
            } = view
            {
                nested = true;
                (left, right) = (from, to);
                carrier = self.context.whnf_value_type(inner)?;
                continue;
            }
            let ValueTypeView::Abstract(atom) = view
            else {
                return Ok(related_fibre);
            };
            let Some((interface, kind)) = self.context.interface_of(atom)
            else {
                return Ok(related_fibre);
            };
            if let Maybe::Absent(_) = interface.law() {
                return Err(CheckRefusal::AtomTransport { at: term, atom });
            }
            let Some(&gandr_core_term::ValueType::Universe { ref level, .. }) =
                self.context.arena().value_type(kind)
            else {
                return Err(CheckRefusal::MachineInvariant);
            };
            let level = level.clone();
            let related = crate::former::related_by(
                self.context.arena_mut(),
                interface.relation(),
                (left, right),
                level,
            );
            let read = self.context.whnf_value_type(related)?;
            // The relation returns an identity's code: the introduction reads
            // that identity's fibre in turn.
            if let ValueTypeView::Path {
                carrier: inner,
                left: from,
                right: to,
            } = value_type_view(self.context.arena(), read)?
            {
                if !nested {
                    related_fibre = Some(related);
                }
                (left, right) = (from, to);
                carrier = self.context.whnf_value_type(inner)?;
            }
            else if nested {
                carrier = read;
            }
            else {
                return Ok(Some(related));
            }
        }
    }

    /// The domain and codomain a static lambda's body checks against: the
    /// ones the expected type matches as a static Pi at its weak head.
    ///
    /// # Specification
    /// - requires: `expected` is formed.
    /// - ensures: the domain of `expected`, and its codomain shifted past the
    ///   lambda's binder: a static Pi's codomain stands in the ambient context;
    ///   two unknown types when it is the unknown type. Both resolve in the
    ///   arena.
    /// - fails: [`CheckRefusal::ShapeMismatch`] at `at`, wanting a static Pi,
    ///   for any other former; the unfolding's refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`CheckRefusal`] — as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — separated by a static lambda against a static Pi, the
    ///   unknown type and an atom.
    /// - witness: `judgement::tests::a_static_lambda_checks_only_against_a_static_pi`
    /// - witness: `judgement::tests::an_introduction_against_the_unknown_type_checks_its_parts`
    ///
    /// # Judgement
    /// - expected: `expected`
    #[spec(ensures: |ret| match ret {
        | Ok((domain, codomain)) => {
            self.context.arena().value_type(domain).is_some()
                && self.context.arena().value_type(codomain).is_some()
        },
        | Err(CheckRefusal::ShapeMismatch { at: shaped, wanted, found }) => {
            shaped == TermNode::Value(at)
                && wanted == ExpectedShape::StaticPi
                && found == TypeNode::Value(expected)
        },
        | Err(_) => true,
    })]
    fn static_pi_expected(
        &mut self,
        at: ValueId,
        expected: ValueTypeId,
    ) -> Result<(ValueTypeId, ValueTypeId), CheckRefusal>
    {
        let head = self.context.whnf_value_type(expected)?;
        match matched_static_pi(self.context.arena_mut(), head) {
            Maybe::Present((domain, codomain)) => {
                let scoped =
                    shift_value_type(self.context.arena_mut(), codomain, Binders::from(1_u32))
                        .settle(self.context.arena_mut());
                Ok((domain, scoped))
            },
            Maybe::Absent(absent) => Err(unmatched(
                absent,
                TypeNode::Value(head),
                CheckRefusal::ShapeMismatch {
                    at: TermNode::Value(at),
                    wanted: ExpectedShape::StaticPi,
                    found: TypeNode::Value(expected),
                },
            )),
        }
    }

    /// The domain and codomain a lambda's body checks against: the ones the
    /// expected type matches as a function type at its weak head.
    ///
    /// # Specification
    /// - requires: `expected` is formed.
    /// - ensures: the domain of `expected`, and its codomain read under the
    ///   lambda's binder — an arrow's shifted past it, a dependent arrow's as
    ///   it stands, the unknown type's unknown codomain shifted as an arrow's.
    /// - fails: [`CheckRefusal::ShapeMismatch`] at `at`, wanting an arrow, for
    ///   any other former; the unfolding's refusal.
    /// - panics: none.
    ///
    /// # Judgement
    /// - expected: `expected`
    ///
    /// # Adequacy
    /// - hypothesis: L3 — ordinary and dependent lambdas expose checked bodies
    ///   and exact shape failures; the dependent application case separates
    ///   using the ambient codomain where substitution is required; a lambda
    ///   against the unknown type checks its body against the unknown.
    /// - witness: `judgement::tests::every_comp_former_is_answered_in_both_modes`
    /// - witness: `judgement::tests::a_dependent_application_instantiates_its_codomain_at_the_argument`
    /// - witness: `judgement::tests::an_introduction_against_the_unknown_type_checks_its_parts`
    #[spec(ensures: |ret| match ret {
        | Ok((domain, codomain)) => self.context.arena().value_type(domain).is_some()
            && self.context.arena().comp_type(codomain).is_some()
            && match comp_type_view(self.context.arena(), expected) {
                | Ok(CompTypeView::Pi { domain: held_domain, codomain: held_codomain }) => domain == held_domain && codomain == held_codomain,
                | Ok(CompTypeView::Arrow { domain: held, .. }) => domain == held,
                | Ok(CompTypeView::Element { .. } | CompTypeView::Unknown | CompTypeView::Codata { .. }) => true,
                | Ok(CompTypeView::Returner { .. } | CompTypeView::With(..)) | Err(_) => false,
            },
        | Err(CheckRefusal::ShapeMismatch { at: named, wanted, found }) => named == TermNode::Computation(at)
            && wanted == ExpectedShape::Arrow && found == TypeNode::Computation(expected),
        | Err(_) => true,
    })]
    fn arrow_expected(
        &mut self,
        at: ComputationId,
        expected: CompTypeId,
    ) -> Result<(ValueTypeId, CompTypeId), CheckRefusal>
    {
        let head = crate::codata::read(self.context, expected)?;
        match matched_function(self.context.arena_mut(), head) {
            Maybe::Present(function) => match function.scope() {
                CodomainScope::Ambient => {
                    let scoped = shift_comp_type(
                        self.context.arena_mut(),
                        function.codomain(),
                        Binders::from(1_u32),
                    )
                    .settle(self.context.arena_mut());
                    Ok((function.domain(), scoped))
                },
                CodomainScope::UnderBinder => Ok((function.domain(), function.codomain())),
            },
            Maybe::Absent(absent) => Err(unmatched(
                absent,
                TypeNode::Computation(head),
                CheckRefusal::ShapeMismatch {
                    at: TermNode::Computation(at),
                    wanted: ExpectedShape::Arrow,
                    found: TypeNode::Computation(expected),
                },
            )),
        }
    }

    /// The result type a return checks its value against: the one the
    /// expected type matches as a returner at its weak head.
    ///
    /// # Specification
    /// - requires: `expected` is formed.
    /// - ensures: the result of `expected` when it is `F A` at its weak head;
    ///   an unknown value type, minted, when it is the unknown type.
    /// - fails: [`CheckRefusal::ShapeMismatch`] at `at`, wanting a returner,
    ///   for any other former; the unfolding's refusal.
    /// - panics: none.
    ///
    /// # Judgement
    /// - expected: `expected`
    ///
    /// # Adequacy
    /// - hypothesis: L3 — returns against a returner, the unknown type and an
    ///   arrow expose checking at the selected value type or the exact shape
    ///   failure; a substituted result type or wrong node family changes these
    ///   answers.
    /// - witness: `judgement::tests::every_comp_former_is_answered_in_both_modes`
    /// - witness: `judgement::tests::an_introduction_against_the_wrong_former_is_a_shape_mismatch`
    /// - witness: `judgement::tests::an_introduction_against_the_unknown_type_checks_its_parts`
    #[spec(ensures: |ret| match ret {
        | Ok(result) => self.context.arena().value_type(result).is_some()
            && match comp_type_view(self.context.arena(), expected) {
                | Ok(CompTypeView::Returner { result: held, .. }) => result == held,
                | Ok(CompTypeView::Element { .. } | CompTypeView::Unknown | CompTypeView::Codata { .. }) => true,
                | Ok(CompTypeView::Arrow { .. } | CompTypeView::Pi { .. } | CompTypeView::With(..)) | Err(_) => false,
            },
        | Err(CheckRefusal::ShapeMismatch { at: named, wanted, found }) => named == TermNode::Computation(at)
            && wanted == ExpectedShape::Returner && found == TypeNode::Computation(expected),
        | Err(_) => true,
    })]
    fn returner_expected(
        &mut self,
        at: ComputationId,
        expected: CompTypeId,
    ) -> Result<ValueTypeId, CheckRefusal>
    {
        let head = crate::codata::read(self.context, expected)?;
        match matched_returner(self.context.arena_mut(), head) {
            Maybe::Present(result) => Ok(result),
            Maybe::Absent(absent) => Err(unmatched(
                absent,
                TypeNode::Computation(head),
                CheckRefusal::ShapeMismatch {
                    at: TermNode::Computation(at),
                    wanted: ExpectedShape::Returner,
                    found: TypeNode::Computation(expected),
                },
            )),
        }
    }

    /// The formation rules over value types.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: an atom, the unit type and the row kind are formed; a row's
    ///   tail checks its term against the row kind; a sealed atom is formed
    ///   when its abstract type was admitted; a thunk type forms its body; a
    ///   universe is formed below the greatest level; a lift forms its type,
    ///   then awaits the raise; a decode awaits its code's synthesised type; an
    ///   eager product and a sum form each component, an empty sum at once; a
    ///   dependent pair forms its first factor, then its second under a binder
    ///   of the first; a static Pi forms both classifiers, then awaits their
    ///   check as static classifiers; a path type and a flow type form their
    ///   carrier, open or closed, then check each endpoint against it, source
    ///   first; a run or prefix type checks its protocol against the value
    ///   universe beneath a run frame; a session type forms each payload, then
    ///   awaits their check as no session types — its payloads read no binder
    ///   outside it unless a run frame waits beneath it, a run or prefix
    ///   staying on the checker's side; a capability forms the payload and
    ///   reply of every operation its authority grants, and is refused when
    ///   consumable. A former formed at once leaves the frames as found, but
    ///   for a data type, a record, a product, a sum, a session type and a
    ///   capability, which queue their components; one that descends leaves
    ///   them no shorter.
    /// - fails: the view's refusal for a former outside the fragment or a
    ///   dangling id; [`CheckRefusal::OutOfFragment`] naming
    ///   [`UnadmittedFormer::TopUniverse`]; [`CheckRefusal::NotAnAbstractType`]
    ///   for a sealed atom no admitted abstract type declares;
    ///   [`CheckRefusal::CapabilityConsumable`] for a consumable capability,
    ///   whose linear zone no former binds into;
    ///   [`CheckRefusal::OutOfFragment`] naming [`UnadmittedFormer::Stage`] for
    ///   a staged type whose stage this judgement did not mint;
    ///   [`CheckRefusal::OpenSessionPayload`] for a session type whose payload
    ///   reads a binder outside it, no run frame waiting.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one type of every former, formed or refused, through
    ///   the public faces.
    /// - witness: `formation::tests::every_value_type_constructor_has_a_formation_rule`
    /// - witness: `bridge::tests::a_static_pi_over_a_type_that_classifies_no_codes_is_refused_by_name`
    /// - witness: `judgement::tests::a_session_payload_reads_a_binder_only_in_a_run_protocol_1728`
    #[spec(
        captures: depth = self.frames.len(),
        ensures: |ret| match ret {
            | Ok(Step::Ascend(_)) => self.frames.len() == depth || (matches!(self.context.arena().value_type(at), Some(gandr_core_term::ValueType::Data { .. } | gandr_core_term::ValueType::Record(_) | gandr_core_term::ValueType::Product(_) | gandr_core_term::ValueType::Sum(_) | gandr_core_term::ValueType::Session(_) | gandr_core_term::ValueType::Capability { .. })) && self.frames.len() >= depth),
            | Ok(Step::Descend(_)) => self.frames.len() >= depth,
            | Err(_) => true,
        },
    )]
    fn form_value_type(
        &mut self,
        at: ValueTypeId,
    ) -> Result<Step, CheckRefusal>
    {
        // A bridge forms as an identity does, unless its carrier reaches a
        // sealed atom stating no interface: the relation there is the
        // abstraction's to choose.
        if let ValueTypeView::Bridge { carrier, .. } = value_type_view(self.context.arena(), at)? {
            crate::relatedness::require_unsealed(self.context, at, carrier)?;
        }
        match value_type_view(self.context.arena(), at)? {
            ValueTypeView::Data { .. } => self.native_data(at),
            ValueTypeView::Record(fields) => {
                let owner = self.owner;
                self.frames
                    .extend(fields.values().rev().map(|&field| Waiting {
                        frame: Frame::NativeNext(Goal::Form(TypeNode::Value(field))),
                        owner,
                    }));
                Ok(Step::Ascend(Produced::Checked))
            },
            ValueTypeView::Stack { input, output } => {
                self.wait(Frame::FormNext(TypeNode::Computation(output)));
                Ok(Step::Descend(Goal::Form(TypeNode::Computation(input))))
            },
            ValueTypeView::Path {
                carrier,
                left,
                right,
            }
            | ValueTypeView::Bridge {
                carrier,
                left,
                right,
            } => {
                self.wait(Frame::Next(Goal::Value {
                    term: right,
                    direction: Direction::Check(carrier),
                }));
                self.wait(Frame::Next(Goal::Value {
                    term: left,
                    direction: Direction::Check(carrier),
                }));
                Ok(Step::Descend(Goal::Form(TypeNode::Value(carrier))))
            },
            ValueTypeView::Flow {
                carrier,
                source,
                target,
            } => {
                self.wait(Frame::Next(Goal::Value {
                    term: target,
                    direction: Direction::Check(carrier),
                }));
                self.wait(Frame::Next(Goal::Value {
                    term: source,
                    direction: Direction::Check(carrier),
                }));
                Ok(Step::Descend(Goal::Form(TypeNode::Value(carrier))))
            },
            ValueTypeView::Run(protocol)
            | ValueTypeView::Prefix(protocol)
            | ValueTypeView::Dialogue(protocol) => {
                let universe = crate::flow::universe(self.context.arena_mut());
                self.wait(Frame::RunProtocol);
                Ok(Step::Descend(Goal::Value {
                    term: protocol,
                    direction: Direction::Check(universe),
                }))
            },
            ValueTypeView::PathUniverse(source, target) => {
                let _source = crate::formation::path_code(self.context.arena(), source)?;
                let _target = crate::formation::path_code(self.context.arena(), target)?;
                Ok(Step::Ascend(Produced::Checked))
            },
            // A row's tail is a term of the row kind.
            ValueTypeView::RowTail(tail) => {
                let kind = self.context.arena_mut().value_type_row();
                Ok(Step::Descend(Goal::Value {
                    term: tail,
                    direction: Direction::Check(kind),
                }))
            },
            ValueTypeView::Integer
            | ValueTypeView::String
            | ValueTypeView::Character
            | ValueTypeView::Float64
            | ValueTypeView::Fixed(_)
            | ValueTypeView::Unit
            | ValueTypeView::Buffer
            | ValueTypeView::Row
            | ValueTypeView::Web
            | ValueTypeView::Unknown => Ok(Step::Ascend(Produced::Checked)),
            ValueTypeView::Abstract(atom) => {
                let _level = self.context.abstract_level(atom)?;
                Ok(Step::Ascend(Produced::Checked))
            },
            ValueTypeView::List(element) | ValueTypeView::Kept { value: element, .. } => {
                Ok(Step::Descend(Goal::Form(TypeNode::Value(element))))
            },
            ValueTypeView::Staged { base, stage } => {
                // A stage is in scope where this judgement minted it: an order
                // fits a stage within itself exactly when it minted it.
                if self.context.stages().fit(stage, stage) == Fit::NotBelow {
                    return Err(CheckRefusal::OutOfFragment {
                        at: CoreNode::Type(TypeNode::Value(at)),
                        former: UnadmittedFormer::Stage,
                    });
                }
                Ok(Step::Descend(Goal::Form(TypeNode::Value(base))))
            },
            ValueTypeView::Thunk(body) => {
                Ok(Step::Descend(Goal::Form(TypeNode::Computation(body))))
            },
            ValueTypeView::Universe { level, .. } => {
                if level.succ().is_err() {
                    return Err(CheckRefusal::OutOfFragment {
                        at: CoreNode::Type(TypeNode::Value(at)),
                        former: UnadmittedFormer::TopUniverse,
                    });
                }
                Ok(Step::Ascend(Produced::Checked))
            },
            ValueTypeView::Lift { inner, .. } => {
                self.wait(Frame::FormLift(at));
                Ok(Step::Descend(Goal::Form(TypeNode::Value(inner))))
            },
            ValueTypeView::Element { code, .. } => {
                self.wait(Frame::FormElement(TypeNode::Value(at)));
                Ok(Step::Descend(Goal::Value {
                    term: code,
                    direction: Direction::Synthesise,
                }))
            },
            ValueTypeView::Sum(components) | ValueTypeView::Product(components) => {
                let owner = self.owner;
                self.frames
                    .extend(components.iter().rev().map(|&component| Waiting {
                        frame: Frame::FormNext(TypeNode::Value(component)),
                        owner,
                    }));
                Ok(Step::Ascend(Produced::Checked))
            },
            ValueTypeView::Session(session) => {
                let reach = crate::code::loose_reach(
                    self.context.arena(),
                    crate::refusal::CoreNode::Type(TypeNode::Value(at)),
                )?;
                if usize::from(reach) != 0
                    && !self
                        .frames
                        .iter()
                        .any(|waiting| matches!(waiting.frame, Frame::RunProtocol))
                {
                    return Err(CheckRefusal::OpenSessionPayload { at });
                }
                let owner = self.owner;
                self.frames
                    .extend(session.payloads().iter().rev().map(|&payload| Waiting {
                        frame: Frame::FormNext(TypeNode::Value(payload)),
                        owner,
                    }));
                Ok(Step::Ascend(Produced::Checked))
            },
            ValueTypeView::StaticPi { domain, codomain } => {
                self.wait(Frame::FormStaticPi(at));
                self.wait(Frame::FormNext(TypeNode::Value(codomain)));
                Ok(Step::Descend(Goal::Form(TypeNode::Value(domain))))
            },
            ValueTypeView::Sigma { first, second } => {
                self.wait(Frame::FormUnder {
                    domain: first,
                    under: TypeNode::Value(second),
                });
                Ok(Step::Descend(Goal::Form(TypeNode::Value(first))))
            },
            ValueTypeView::Capability {
                authority, grade, ..
            } => {
                if grade == gandr_core_term::effect::capability::CapabilityGrade::Consumable {
                    return Err(CheckRefusal::CapabilityConsumable(at));
                }
                let owner = self.owner;
                self.frames
                    .extend(authority.types().rev().map(|ty| Waiting {
                        frame: Frame::FormNext(TypeNode::Value(ty)),
                        owner,
                    }));
                Ok(Step::Ascend(Produced::Checked))
            },
            // A handle names a declared world and forms what it holds; a
            // capability lives only in the linear zone an entry opens, which
            // no written type reaches.
            ValueTypeView::World(gandr_core_term::world::WorldType::At { inner, world }) => {
                self.context
                    .worlds()
                    .named(world)
                    .map_err(|defect| CheckRefusal::Located {
                        at: CoreNode::Type(TypeNode::Value(at)),
                        defect,
                    })?;
                Ok(Step::Descend(Goal::Form(TypeNode::Value(inner))))
            },
            ValueTypeView::World(gandr_core_term::world::WorldType::Capability(_)) => {
                Err(CheckRefusal::CapabilityConsumable(at))
            },
        }
    }

    /// The formation rules over computation types.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a returner forms its result; an arrow forms its domain, then
    ///   its codomain; a dependent arrow forms its domain, then its codomain
    ///   under a binder of the domain; a decode awaits its code's synthesised
    ///   type; a codata application checks each argument against its
    ///   instantiated parameter; the unknown type is formed at once.
    /// - fails: the view's refusal for a dangling id; [`CheckRefusal::Codata`]
    ///   for a codata application naming the declaration being formed, no
    ///   admitted declaration, or another number of arguments.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the four computation-type formers expose exact
    ///   classifiers, including a dependent codomain; wrong children, skipped
    ///   domain formation or missing binder frames change those observations.
    /// - witness: `formation::tests::every_comp_type_constructor_has_a_formation_rule`
    /// - witness: `formation::tests::the_dependent_arrow_forms_at_the_join_of_its_levels`
    #[spec(
        captures: before = self.frames.len(),
        ensures: |ret| ret.is_err()
            || (matches!(ret, Ok(Step::Descend(_) | Step::Ascend(Produced::Checked))) && self.frames.len() >= before),
    )]
    fn form_comp_type(
        &mut self,
        at: CompTypeId,
    ) -> Result<Step, CheckRefusal>
    {
        match comp_type_view(self.context.arena(), at)? {
            CompTypeView::With(components) => {
                let owner = self.owner;
                self.frames
                    .extend(components.iter().rev().map(|&component| Waiting {
                        frame: Frame::FormNext(TypeNode::Computation(component)),
                        owner,
                    }));
                Ok(Step::Ascend(Produced::Checked))
            },
            CompTypeView::Returner { result, effects } => {
                let owner = self.owner;
                self.frames.extend(effects.types().rev().map(|ty| Waiting {
                    frame: Frame::FormNext(TypeNode::Value(ty)),
                    owner,
                }));
                Ok(Step::Descend(Goal::Form(TypeNode::Value(result))))
            },
            CompTypeView::Arrow { domain, codomain } => {
                self.wait(Frame::FormNext(TypeNode::Computation(codomain)));
                Ok(Step::Descend(Goal::Form(TypeNode::Value(domain))))
            },
            CompTypeView::Pi { domain, codomain } => {
                self.wait(Frame::FormUnder {
                    domain,
                    under: TypeNode::Computation(codomain),
                });
                Ok(Step::Descend(Goal::Form(TypeNode::Value(domain))))
            },
            CompTypeView::Element { code, .. } => {
                self.wait(Frame::FormElement(TypeNode::Computation(at)));
                Ok(Step::Descend(Goal::Value {
                    term: code,
                    direction: Direction::Synthesise,
                }))
            },
            CompTypeView::Codata { .. } => self.native_codata(at),
            CompTypeView::Unknown => Ok(Step::Ascend(Produced::Checked)),
        }
    }

    /// Add the bound computation's demand to the continuation's ambient type.
    ///
    /// # Specification
    /// - ensures: a pure bound, and one whose type is unknown because a total
    ///   run marked it, leave the continuation unchanged; otherwise both
    ///   demands remain in the returner, with one definition per name.
    /// - fails: a non-returner cannot carry a nonempty row; conflicting
    ///   definitions are refused rather than overwritten.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — distinct rows and conflicting shared names
    ///   distinguish accumulation, row laundering, and silent signature
    ///   replacement.
    /// - witness: `judgement::tests::bind_unions_effect_rows`
    /// - witness: `judgement::tests::check_mode_bind_subsumes_the_accumulated_row`
    /// - witness: `judgement::elaboration::tests::a_marked_bound_leaves_its_continuation_judged`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body unions the two rows, comparing every shared interface; the check compares each demanded interface with the union once"
        )
    )]
    #[spec(ensures: |ret| ret.is_err() || match comp_type_view(self.context.arena(), bound) {
        Ok(CompTypeView::Returner { effects, .. }) if effects.purity() == gandr_core_term::effect::Purity::Pure => ret == Ok(continued),
        Ok(CompTypeView::Unknown) => ret == Ok(continued),
        Ok(CompTypeView::Returner { effects, .. }) => ret.is_ok_and(|actual| matches!(comp_type_view(self.context.arena(), actual), Ok(CompTypeView::Returner { effects: actual, .. }) if effects.is_subset(actual, self.context.arena()) == gandr_core_term::row::RowInclusion::Included)),
        _ => false,
    })]
    fn accumulate_effects(
        &mut self,
        at: ComputationId,
        bound: CompTypeId,
        continued: CompTypeId,
    ) -> Result<CompTypeId, CheckRefusal>
    {
        let view = comp_type_view(self.context.arena(), bound)?;
        if matches!(view, CompTypeView::Unknown) {
            return Ok(continued);
        }
        let CompTypeView::Returner { effects, .. } = view
        else {
            return Err(CheckRefusal::MachineInvariant);
        };
        if effects.purity() == gandr_core_term::effect::Purity::Pure {
            return Ok(continued);
        }
        let demanded = effects.clone();
        let head = self.context.whnf_comp_type(continued)?;
        let CompTypeView::Returner { result, effects } =
            comp_type_view(self.context.arena(), head)?
        else {
            return Err(CheckRefusal::ShapeMismatch {
                at: TermNode::Computation(at),
                wanted: ExpectedShape::Returner,
                found: TypeNode::Computation(continued),
            });
        };
        let combined = demanded
            .union(effects, self.context.arena())
            .map_err(|_conflict| CheckRefusal::EffectSignatureConflict {
                at,
                first: bound,
                second: continued,
            })?;
        Ok(self
            .context
            .arena_mut()
            .comp_type_returner_with_effects(result, combined))
    }

    /// The universe a quote of the formed type `quoted` has: its family's sort
    /// at the type's level.
    ///
    /// # Specification
    /// - requires: `quoted` is formed.
    /// - ensures: the value universe for a value type, the computation universe
    ///   for a computation type, at [`level_of`] the type, minted.
    /// - fails: as [`level_of`].
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — quotes of atoms, returners and universes expose exact
    ///   sorts and natural levels; swapped quote families or a missing universe
    ///   successor differs on these finite forms.
    /// - witness: `judgement::tests::a_universe_classifies_one_level_up_in_the_positive_sort`
    #[spec(ensures: |ret| ret.is_err() || ret.is_ok_and(|universe|
        matches!(value_type_view(self.context.arena(), universe), Ok(ValueTypeView::Universe { sort, .. })
            if matches!((quoted, sort), (TypeNode::Value(_), GroundSort::Value) | (TypeNode::Computation(_), GroundSort::Computation)))))]
    fn quoted(
        &mut self,
        quoted: TypeNode,
    ) -> Result<ValueTypeId, CheckRefusal>
    {
        let level = level_of(self.context, quoted)?;
        let sort = match quoted {
            TypeNode::Value(_) => GroundSort::Value,
            TypeNode::Computation(_) => GroundSort::Computation,
        };
        Ok(self
            .context
            .arena_mut()
            .value_type_universe(Sort::Ground(sort), level))
    }

    /// Whether the lift `at`, its type formed, raises it.
    ///
    /// # Specification
    /// - requires: `at` is a lift whose type is formed.
    /// - ensures: success exactly when the lift's target lies strictly above
    ///   [`level_of`] its type.
    /// - fails: [`CheckRefusal::OutOfFragment`] naming
    ///   [`UnadmittedFormer::TypeLift`] otherwise;
    ///   [`CheckRefusal::MachineInvariant`] when `at` is no lift.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — targets below, equal to and above a nonzero natural
    ///   level expose exact lift refusal or formation, separating non-strict
    ///   comparison and wrong diagnostic identity; non-lifts fault explicitly.
    /// - witness: `judgement::tests::lift_formation_distinguishes_below_equal_and_above`
    /// - witness: `judgement::tests::machine_bookkeeping_preserves_zero_and_one_boundaries`
    #[spec(ensures: |ret| match ret {
        | Ok(()) => matches!(value_type_view(self.context.arena(), at), Ok(ValueTypeView::Lift { .. })),
        | Err(CheckRefusal::OutOfFragment { at: named, former: UnadmittedFormer::TypeLift }) => named == CoreNode::Type(TypeNode::Value(at)),
        | Err(_) => true,
    })]
    fn raises(
        &self,
        at: ValueTypeId,
    ) -> Result<(), CheckRefusal>
    {
        let arena = self.context.arena();
        let ValueTypeView::Lift { inner, target } = value_type_view(arena, at)?
        else {
            return Err(CheckRefusal::MachineInvariant);
        };
        if bool::from(level_of(self.context, TypeNode::Value(inner))?.lt(target)) {
            Ok(())
        }
        else {
            Err(CheckRefusal::OutOfFragment {
                at: CoreNode::Type(TypeNode::Value(at)),
                former: UnadmittedFormer::TypeLift,
            })
        }
    }

    /// Whether the static Pi `at`, both classifiers formed, ranges over static
    /// classifiers only.
    ///
    /// # Specification
    /// - requires: `at` is a static Pi whose classifiers are formed.
    /// - ensures: success exactly when its domain and its codomain are each, at
    ///   the weak head, a universe, the row kind or a static Pi.
    /// - fails: [`CheckRefusal::StaticClassifierExpected`] naming `at` and the
    ///   first classifier that is neither; [`CheckRefusal::MachineInvariant`]
    ///   when `at` is no static Pi; the unfolding's refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`CheckRefusal`] — as above.
    ///
    /// # Termination
    /// - reason: the `for` loop visits the two classifiers, not recursion.
    /// - measure: the classifiers left, at most two.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — separated by classifiers that are universes and
    ///   static Pis, a domain that is neither, and a codomain that is neither.
    /// - witness: `bridge::tests::a_static_pi_over_a_type_that_classifies_no_codes_is_refused_by_name`
    /// - witness: `bridge::tests::every_checked_static_declaration_is_readmitted`
    #[spec(ensures: |ret| match ret {
        | Err(CheckRefusal::StaticClassifierExpected { at: named, .. }) => named == at,
        | Ok(()) | Err(_) => true,
    })]
    fn static_classifiers(
        &mut self,
        at: ValueTypeId,
    ) -> Result<(), CheckRefusal>
    {
        let ValueTypeView::StaticPi { domain, codomain } =
            value_type_view(self.context.arena(), at)?
        else {
            return Err(CheckRefusal::MachineInvariant);
        };
        for classifier in [domain, codomain] {
            let head = self.context.whnf_value_type(classifier)?;
            match value_type_view(self.context.arena(), head)? {
                ValueTypeView::Universe { .. }
                | ValueTypeView::StaticPi { .. }
                | ValueTypeView::Row
                | ValueTypeView::Unknown => {},
                ValueTypeView::PathUniverse(..)
                | ValueTypeView::Path { .. }
                | ValueTypeView::Bridge { .. }
                | ValueTypeView::Flow { .. }
                | ValueTypeView::Run(_)
                | ValueTypeView::Prefix(_)
                | ValueTypeView::Dialogue(_)
                | ValueTypeView::Web
                | ValueTypeView::Data { .. }
                | ValueTypeView::Record(_)
                | ValueTypeView::Sum(..)
                | ValueTypeView::List(_)
                | ValueTypeView::Stack { .. }
                | ValueTypeView::Capability { .. }
                | ValueTypeView::Buffer
                | ValueTypeView::RowTail(_)
                | ValueTypeView::Integer
                | ValueTypeView::String
                | ValueTypeView::Character
                | ValueTypeView::Float64
                | ValueTypeView::Fixed(_)
                | ValueTypeView::Unit
                | ValueTypeView::Thunk(_)
                | ValueTypeView::Lift { .. }
                | ValueTypeView::Element { .. }
                | ValueTypeView::Product(..)
                | ValueTypeView::Sigma { .. }
                | ValueTypeView::Abstract(_)
                | ValueTypeView::Staged { .. }
                | ValueTypeView::Kept { .. }
                | ValueTypeView::Session(_)
                | ValueTypeView::World(_) => {
                    return Err(CheckRefusal::StaticClassifierExpected {
                        at,
                        found: classifier,
                    });
                },
            }
        }
        Ok(())
    }

    /// Cross the decode bridge for the decode `node`, whose code synthesised
    /// `synthesised`.
    ///
    /// # Specification
    /// - requires: `node` is a decode.
    /// - ensures: as [`decode_bridge`] at the decode's code, its family's sort
    ///   and its level.
    /// - fails: as [`decode_bridge`]; [`CheckRefusal::MachineInvariant`] when
    ///   `node` is no decode.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — value and computation decodes expose their exact
    ///   classifier or sort/type refusal; these separate a wrong family, target
    ///   level or missing conversion crossing within the fragment.
    /// - witness: `formation::tests::every_value_type_constructor_has_a_formation_rule`
    /// - witness: `formation::tests::every_comp_type_constructor_has_a_formation_rule`
    /// - witness: `judgement::tests::a_value_type_in_a_computation_universe_is_a_sort_mismatch`
    #[spec(
        captures: before = usize::from(self.conversions),
        ensures: usize::from(self.conversions) == if match node {
            | TypeNode::Value(at) => matches!(value_type_view(self.context.arena(), at), Ok(ValueTypeView::Element { .. })),
            | TypeNode::Computation(at) => matches!(comp_type_view(self.context.arena(), at), Ok(CompTypeView::Element { .. })),
        } { before.saturating_add(1) } else { before },
    )]
    fn decodes(
        &mut self,
        node: TypeNode,
        synthesised: ValueTypeId,
    ) -> Result<(), CheckRefusal>
    {
        let arena = self.context.arena();
        let (code, target, sort) = match node {
            TypeNode::Value(at) => match value_type_view(arena, at)? {
                ValueTypeView::Element { code, target } => {
                    (code, target.clone(), GroundSort::Value)
                },
                ValueTypeView::PathUniverse(..)
                | ValueTypeView::Path { .. }
                | ValueTypeView::Bridge { .. }
                | ValueTypeView::Flow { .. }
                | ValueTypeView::Run(_)
                | ValueTypeView::Prefix(_)
                | ValueTypeView::Dialogue(_)
                | ValueTypeView::Web
                | ValueTypeView::Data { .. }
                | ValueTypeView::Record(_)
                | ValueTypeView::Sum(..)
                | ValueTypeView::List(_)
                | ValueTypeView::Stack { .. }
                | ValueTypeView::Capability { .. }
                | ValueTypeView::Buffer
                | ValueTypeView::Row
                | ValueTypeView::RowTail(_)
                | ValueTypeView::Integer
                | ValueTypeView::String
                | ValueTypeView::Character
                | ValueTypeView::Float64
                | ValueTypeView::Fixed(_)
                | ValueTypeView::Unit
                | ValueTypeView::Thunk(_)
                | ValueTypeView::Universe { .. }
                | ValueTypeView::Lift { .. }
                | ValueTypeView::Product(..)
                | ValueTypeView::Sigma { .. }
                | ValueTypeView::StaticPi { .. }
                | ValueTypeView::Abstract(_)
                | ValueTypeView::Staged { .. }
                | ValueTypeView::Kept { .. }
                | ValueTypeView::Session(_)
                | ValueTypeView::World(_)
                | ValueTypeView::Unknown => return Err(CheckRefusal::MachineInvariant),
            },
            TypeNode::Computation(at) => match comp_type_view(arena, at)? {
                CompTypeView::Element { code, target } => {
                    (code, target.clone(), GroundSort::Computation)
                },
                CompTypeView::Returner { .. }
                | CompTypeView::With(..)
                | CompTypeView::Arrow { .. }
                | CompTypeView::Pi { .. }
                | CompTypeView::Codata { .. }
                | CompTypeView::Unknown => {
                    return Err(CheckRefusal::MachineInvariant);
                },
            },
        };
        decode_bridge(
            self.context,
            code,
            synthesised,
            sort,
            &target,
            &mut self.conversions,
        )
    }

    /// The type an application whose argument checked has.
    ///
    /// The canonical type-position form of a call argument is the bind-ahead
    /// form the lowering writes for `f(g(x))` in a type, `⟨c ← g(x); f(c)⟩`,
    /// so a codomain read at the call and a type written with it are one
    /// syntax, which conversion compares as such (#720). The argument itself
    /// keeps #444's reading — a pure nested call a type reads stands as
    /// [`Nesting::Returned`] — and stands as that value wherever no returned
    /// code encloses the binder. Alternatives: reading `⟨c ← M; N⟩` as
    /// `N[⟨M⟩]` in conversion, a kernel conversion extension with its own
    /// soundness argument; and lowering a type-read call in place, which loses
    /// the bound variable standing below the stage. Reversal: a memo cost from
    /// repeated binds of one call, measured as sharing lost, would hold the
    /// call once outside the codes that read it.
    ///
    /// # Specification
    /// - requires: `argument` checked against the domain `codomain` belongs to,
    ///   and the application frames waiting on the stack are the arguments the
    ///   spine applies after it, innermost first.
    /// - ensures: an arrow's codomain as it stands; a dependent arrow's
    ///   instantiated at the argument — at the staged code a later argument of
    ///   the spine holds for a plain code
    ///   ([`crate::recursion::instantiation`]), and at the lifted code when the
    ///   argument crossed the value bridge with a lift, so the codomain reads
    ///   the code at the universe the domain names. An argument written as a
    ///   call, nested or returned, is instantiated with the call bound ahead of
    ///   each decode whose returned code reads it
    ///   ([`gandr_core_term::instantiate_comp_type_at_call`]).
    /// - fails: the staged instantiation's refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — ordinary and dependent applications expose exact
    ///   result types, with a dependent argument substituted into its codomain;
    ///   retaining a bound variable or changing an ambient codomain differs; a
    ///   type argument a later argument holds at a stage is substituted staged.
    /// - witness: `judgement::tests::every_comp_former_is_answered_in_both_modes`
    /// - witness: `judgement::tests::a_dependent_application_instantiates_its_codomain_at_the_argument`
    /// - witness: `judgement::tests::a_family_at_a_call_argument_converts_with_the_type_written_with_it_720`
    /// - witness: `recursion::tests::a_type_parameter_instantiates_at_a_staged_code`
    #[spec(ensures: |ret| match codomain {
        | Codomain::Ambient(held) => ret == Ok(held),
        | Codomain::Dependent(_) => ret.as_ref().map_or(true, |&instantiated| self.context.arena().comp_type(instantiated).is_some()),
    })]
    fn applied(
        &mut self,
        argument: ValueId,
        codomain: Codomain,
    ) -> Result<CompTypeId, CheckRefusal>
    {
        match codomain {
            Codomain::Ambient(codomain) => Ok(codomain),
            Codomain::Dependent(codomain) => {
                self.read_by_a_type(argument);
                let spine = self.frames.iter().rev().map_while(|waiting| {
                    if let Frame::ApplicationHead { argument, .. } = waiting.frame {
                        Some(argument)
                    }
                    else {
                        None
                    }
                });
                let instance = match crate::recursion::instantiation(
                    self.context,
                    (argument, codomain),
                    spine,
                )? {
                    Maybe::Present(staged) => staged,
                    Maybe::Absent(
                        crate::recursion::Unstaged::Plain | crate::recursion::Unstaged::Unknown,
                    ) => argument,
                };
                let lift = self.context.lifts().get(&argument).cloned();
                let arena = self.context.arena_mut();
                if lift.is_none()
                    && instance == argument
                    && let Some(&(Value::Nested(call) | Value::Returned(call))) =
                        arena.value(argument)
                {
                    return Ok(instantiate_comp_type_at_call(
                        arena, codomain, argument, call,
                    ));
                }
                let code = lift.map_or(instance, |lift| lift.mint(arena, instance));
                Ok(instantiate_comp_type(arena, codomain, code))
            },
        }
    }

    /// The type the constant at `constant`, declared `declared`, has where a
    /// call forces it: for a definition quantified over stages, `declared`
    /// with each binder at the stage the call's arguments show it at, which a
    /// stage the call supplies, `f[i = j]`, must be.
    ///
    /// # Specification
    /// - requires: the constant is the term the machine has just synthesised.
    /// - ensures: present for a definition quantified over stages that a force
    ///   waits on, re-staged by `crate::quantified::restaged` at the arguments
    ///   the applications waiting on that force apply, first applied first;
    ///   absent for a definition quantified over none and for one read outside
    ///   a call, which reads its plain type.
    /// - fails: the instantiation's or the re-staging's refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a recursion's claim handed to a helper typed at a
    ///   stage is admitted, and a call on a value at no stage reads the
    ///   helper's type plain.
    /// - witness: `quantified::tests::a_helper_at_a_stage_takes_a_recursion_s_claim`
    /// - witness: `quantified::tests::a_call_at_no_stage_reads_its_result_plain`
    /// - witness: `quantified::tests::a_supplied_stage_is_held_to_the_arguments_1227`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |read| match *read {
        Maybe::Present(staged) => self.context.arena().value_type(staged).is_some(),
        Maybe::Absent(_) => true,
    }))]
    fn quantified_at(
        &mut self,
        constant: gandr_kernel_term::ConstantIndex,
        declared: ValueTypeId,
    ) -> Result<Maybe<ValueTypeId, crate::quantified::Unread>, CheckRefusal>
    {
        let Some(signature) = self.context.stage_signatures().get(&constant).cloned()
        else {
            return Ok(Maybe::Absent(crate::quantified::Unread::Plain));
        };
        let Some((head, spine)) = self.forced_call()
        else {
            return Ok(Maybe::Absent(crate::quantified::Unread::Plain));
        };
        let context = &*self.context;
        let supplied: Vec<(gandr_kernel_term::StageBinder, gandr_kernel_term::Stage)> = context
            .supplies()
            .iter()
            .filter(|supply| supply.head == head)
            .map(|supply| (supply.binder, supply.stage))
            .collect();
        let at = crate::quantified::instantiation(
            (context.arena(), context.stages()),
            (declared, &signature),
            &spine,
            (head, &supplied),
            |index| context.hypothesis(index),
        )?;
        crate::quantified::restaged(self.context.arena_mut(), declared, &signature, &at)
            .map(Maybe::Present)
    }

    /// The value the force the machine has just reached forces, and the
    /// arguments the applications waiting on that force apply, first applied
    /// first: the call a constant just synthesised heads.
    ///
    /// # Specification
    /// - ensures: present exactly when the innermost waiting frame is a
    ///   [`Frame::Force`], with every [`Frame::ApplicationHead`] directly
    ///   beneath it, innermost first.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::quantified_at`] and [`Self::regioned_at`].
    /// - witness: `quantified::tests::a_helper_at_a_stage_takes_a_recursion_s_claim`
    #[spec(ensures: |ret| ret.is_some() == matches!(self.frames.last(), Some(Waiting { frame: Frame::Force { .. }, .. })))]
    fn forced_call(&self) -> Option<(ValueId, Vec<ValueId>)>
    {
        let mut waiting = self.frames.iter().rev();
        let Some(&Frame::Force { value: head }) = waiting.next().map(|top| &top.frame)
        else {
            return None;
        };
        let spine = waiting
            .map_while(|waiting| {
                if let Frame::ApplicationHead { argument, .. } = waiting.frame {
                    Some(argument)
                }
                else {
                    None
                }
            })
            .collect();
        Some((head, spine))
    }

    /// The type `read`, a constant's declared type as its call reads its
    /// stages, has where the call forces it: each region binder it names
    /// placed at the region the call's arguments show it at, or at the
    /// call's innermost region.
    ///
    /// # Specification
    /// - requires: the constant is the term the machine has just synthesised.
    /// - ensures: present for a type naming a region binder that a force waits
    ///   on, renamed by `crate::regioned::placement` at the arguments the
    ///   applications waiting on that force apply, first applied first, and at
    ///   the region [`Self::enclosing_region`] names; absent for a type naming
    ///   none and for one read outside a call, which keeps its binders.
    /// - fails: the placement's refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a call lending a thunk kept in a capability scope's
    ///   region to a definition over `@[r : Region]` reads its parameter at
    ///   that region.
    /// - witness: `regioned::tests::a_call_places_each_binder_at_the_shortest_region_shown_1221`
    /// - witness: `regioned::tests::a_call_of_a_definition_over_a_region_checks_where_it_stands`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |placed| match *placed {
        Maybe::Present(placed) => self.context.arena().value_type(placed).is_some(),
        Maybe::Absent(_) => true,
    }))]
    fn regioned_at(
        &mut self,
        read: ValueTypeId,
    ) -> Result<Maybe<ValueTypeId, crate::regioned::Unread>, CheckRefusal>
    {
        if crate::capability::binder_precedence(self.context.arena(), TypeNode::Value(read))
            == gandr_core_term::BinderPrecedence::Before
        {
            return Ok(Maybe::Absent(crate::regioned::Unread::Unabstracted));
        }
        let Some((_head, spine)) = self.forced_call()
        else {
            return Ok(Maybe::Absent(crate::regioned::Unread::Unabstracted));
        };
        let innermost = self.enclosing_region()?;
        let context = &*self.context;
        let renaming =
            match crate::regioned::placement(context.arena(), read, (&spine, innermost), |index| {
                context.hypothesis(index)
            })? {
                Maybe::Present(renaming) => renaming,
                Maybe::Absent(unread) => return Ok(Maybe::Absent(unread)),
            };
        Ok(Maybe::Present(crate::regioned::instantiated(
            self.context.arena_mut(),
            read,
            &renaming,
        )))
    }

    /// Note that a type after `value` reads it, so a pure run there stands
    /// as what it returns, and so does each run written beneath it: an
    /// argument of a call it returns or runs, a field of a constructor, a
    /// component of a tuple, record or injection. A run beneath decided to run
    /// would bind its value ahead of the call, and the type would read the
    /// bound variable rather than the call the source wrote (#762).
    ///
    /// # Specification
    /// - requires: a dependent type is instantiated at `value`.
    /// - ensures: each nested computation at `value` or beneath it, through
    ///   call arguments, fields and components, decided to run purely or not
    ///   decided yet, is decided [`Nesting::Returned`], which the run's own
    ///   decision keeps when it runs purely; any other value, or a decision to
    ///   suspend or to run effectfully, is left as it is.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a call as a dependent pair's first component and a
    ///   projection as a dependent function's argument each stand in the type
    ///   after them as what they return, and the second run accepts them; a
    ///   call written two deep, or under a constructor, as a dependent argument
    ///   converts with the type written with it.
    /// - witness: `module::tests::a_pure_run_a_type_reads_stands_as_what_it_returns_444`
    /// - witness: `module::tests::a_call_beneath_a_type_read_argument_stands_as_written_762`
    #[spec(
        captures: [
            before = self.context.nesting().get(&self.context.written(value)).copied(),
            nested = matches!(self.context.arena().value(value), Some(&Value::Nested(_))),
        ],
        ensures: self.context.nesting().get(&self.context.written(value)).copied() == match before {
            None | Some(Nesting::Ran(gandr_core_term::effect::Purity::Pure)) if nested => Some(Nesting::Returned),
            held => held,
        },
    )]
    fn read_by_a_type(
        &mut self,
        value: ValueId,
    )
    {
        let mut seen = alloc::collections::BTreeSet::new();
        let mut pending = Vec::from([value]);
        while let Some(at) = pending.pop() {
            if !seen.insert(at) {
                continue;
            }
            let call = match self.context.arena().value(at) {
                Some(&Value::Nested(call)) => {
                    match self.context.nesting().get(&self.context.written(at)) {
                        None | Some(&Nesting::Ran(gandr_core_term::effect::Purity::Pure)) => {
                            self.context.record_nesting(at, Nesting::Returned);
                        },
                        Some(
                            &(Nesting::Suspended
                            | Nesting::Ran(gandr_core_term::effect::Purity::Effectful)),
                        ) => continue,
                        Some(&Nesting::Returned) => {},
                    }
                    call
                },
                Some(&Value::Returned(call)) => call,
                Some(&Value::Constructor { ref fields, .. }) => {
                    pending.extend(fields.iter().copied());
                    continue;
                },
                Some(&Value::Tuple(ref components)) => {
                    pending.extend(components.iter().copied());
                    continue;
                },
                Some(&Value::Record(ref fields)) => {
                    pending.extend(fields.values().copied());
                    continue;
                },
                Some(&Value::Injection(_, component)) => {
                    pending.push(component);
                    continue;
                },
                _ => continue,
            };
            let mut head = call;
            while let Some(&Computation::Application(function, argument)) =
                self.context.arena().computation(head)
            {
                pending.push(argument);
                head = function;
            }
        }
    }

    /// Hand `produced` to the rule `frame` holds.
    ///
    /// # Specification
    /// - requires: `frame` was pushed by a rule of this run.
    /// - ensures: a force has the body of its value's thunk type; an
    ///   application checks its argument against its head's domain, refuses an
    ///   argument at a static Pi that normalizes away, then has the codomain,
    ///   instantiated for a dependent arrow; a bind opens a binder of its bound
    ///   computation's returned type and judges its body, then closes the
    ///   binder and has what the body had, lowered out of the binder; a lambda
    ///   closes its binder; a bridge frame crosses its bridge and the check
    ///   succeeds; a call read where a thunk of no returner is read runs when
    ///   it synthesises a returner, its result crossing the value bridge, and
    ///   is suspended otherwise, its type crossing the computation bridge to
    ///   the thunk's body; a quote has its universe; a formation frame forms
    ///   the next child, closes its binder, checks a lift's raise, crosses the
    ///   decode bridge or checks a static Pi's classifiers; a pair checks or
    ///   synthesises its second component after its first; a static application
    ///   meets each argument at the domain of the static Pi its head so far
    ///   has, and has the codomain. Every type read for its former is read at
    ///   its weak head.
    /// - fails: [`CheckRefusal::ShapeMismatch`] for a forced value of no thunk
    ///   type, a head of no arrow type, or a bound computation of no returner
    ///   type; [`CheckRefusal::DependentBind`] for a bind whose body's type
    ///   mentions the bound name; [`CheckRefusal::FamilyArity`] for a static
    ///   application whose head opens fewer static Pis than it has arguments;
    ///   [`CheckRefusal::FamilyArgumentClassifier`] for an argument whose type
    ///   does not cross to its domain; [`CheckRefusal::StaticLambdaArgument`]
    ///   for an argument at a dynamic application that normalizes away;
    ///   [`CheckRefusal::StageNotCarried`] for a transport of a staged variable
    ///   along a path whose carrier is not a set; the bridges' refusals;
    ///   [`CheckRefusal::MachineInvariant`] when `produced` is not the kind the
    ///   frame awaits.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every frame resumed by a term of its former through
    ///   the public faces, each to its exact answer or refusal, beside a result
    ///   of the wrong kind; an arity refusal names more arguments than the head
    ///   opened; the arms of a case on a sum, under a hold, each consume it.
    /// - witness: `judgement::tests::every_value_former_is_answered_in_both_modes`
    /// - witness: `judgement::tests::every_comp_former_is_answered_in_both_modes`
    /// - witness: `judgement::tests::a_result_of_the_wrong_kind_is_a_machine_fault`
    /// - witness: `judgement::tests::a_pair_synthesises_its_eager_product_and_checks_against_one`
    /// - witness: `bridge::tests::family_applied_at_wrong_arity_raises_the_exact_variant`
    /// - witness: `bridge::tests::family_argument_at_wrong_classifier_raises_the_exact_variant`
    /// - witness: `bridge::tests::a_static_lambda_at_a_dynamic_parameter_is_refused_by_name`
    /// - witness: `product::tests::a_product_with_a_native_and_a_written_component_reads_as_an_element`
    /// - witness: `judgement::access::tests::a_case_s_arms_each_take_a_hold_from_where_the_case_found_it_1488`
    /// - witness: `judgement::tests::a_transport_along_an_unknown_path_and_a_run_of_a_function_are_refused_by_shape`
    #[spec(ensures: |ret| match ret {
        | Err(CheckRefusal::FamilyArity { expected, actual, .. }) => {
            u32::from(expected) < u32::from(actual)
        },
        | Ok(_) | Err(_) => true,
    })]
    fn resume(
        &mut self,
        frame: Frame,
        produced: Produced,
    ) -> Result<Step, CheckRefusal>
    {
        match (frame, produced) {
            (Frame::NativeNext(goal) | Frame::Next(goal), Produced::Checked) => {
                Ok(Step::Descend(goal))
            },
            (Frame::NativeYield(result), Produced::Checked) => Ok(Step::Ascend(result)),
            // The ascribed type has formed: the body checks against it, and
            // the ascription synthesises it.
            (Frame::Ascription { body, ty }, Produced::Checked) => {
                self.wait(Frame::NativeYield(Produced::CompType(ty)));
                Ok(Step::Descend(Goal::Computation {
                    term: body,
                    direction: Direction::Check(ty),
                }))
            },
            (Frame::NativeCollect, Produced::ValueType(field)) => {
                let field = field.settle(self.context.arena_mut());
                self.native_types.push(field);
                Ok(Step::Ascend(Produced::Checked))
            },
            (Frame::ThunkBody, Produced::Checked) => {
                self.formed();
                Ok(Step::Ascend(Produced::Checked))
            },
            (Frame::NativeDiscard, Produced::ValueType(_))
            | (
                Frame::Reset { .. }
                | Frame::ReturnValue
                | Frame::InjectionPayload
                | Frame::RunProtocol,
                Produced::Checked,
            ) => Ok(Step::Ascend(Produced::Checked)),
            // The answer checked against the goal: it fills the hole as a
            // metavariable's solution does, under the binders open here.
            (Frame::Spliced { hole, answer, .. }, Produced::Checked) => {
                let scope = self.context.intuitionistic_scope()?;
                self.context.deferrals_mut().splice(hole, answer, scope);
                Ok(Step::Ascend(Produced::Checked))
            },
            (Frame::ReturnValue, Produced::ValueType(result)) => {
                let arena = self.context.arena_mut();
                let result = result.settle(arena);
                Ok(Step::Ascend(Produced::CompType(
                    arena.comp_type_returner(result),
                )))
            },
            (Frame::NativeRecord { term, base }, Produced::Checked) => {
                let Some(matched_native_node) = self.context.arena().value(term)
                else {
                    return Err(CheckRefusal::MachineInvariant);
                };
                let Value::Record(ref fields) = *matched_native_node
                else {
                    return Err(CheckRefusal::MachineInvariant);
                };
                if self.native_types.len().checked_sub(base) != Some(fields.len()) {
                    return Err(CheckRefusal::MachineInvariant);
                }
                let fields = fields
                    .keys()
                    .cloned()
                    .zip(self.native_types.drain(base ..))
                    .collect();
                let record = self.context.arena_mut().value_type_record(fields);
                Ok(Step::Ascend(Produced::ValueType(record.into())))
            },
            (Frame::NativeTuple { base }, Produced::Checked) => {
                let product = self.context.arena_mut().value_type_product(
                    self.native_types
                        .get(base ..)
                        .ok_or(CheckRefusal::MachineInvariant)?,
                );
                self.native_types.truncate(base);
                Ok(Step::Ascend(Produced::ValueType(product.into())))
            },
            (Frame::NativeCase(term), Produced::ValueType(datatype)) => {
                let datatype = datatype.settle(self.context.arena_mut());
                self.native_case(term, datatype)
            },
            (
                Frame::NativeMotive {
                    term,
                    datatype,
                    respect,
                    opened,
                },
                Produced::Checked,
            ) => self.native_branches(term, datatype, respect, opened),
            (
                Frame::NativeRespect {
                    term,
                    datatype,
                    reading,
                },
                Produced::Checked,
            ) => {
                // A first run reads each nested call in place, where no
                // conversion unfolds it; the second run judges the rule on the
                // elaborated body, each call bound ahead of its arm.
                if self.context.nesting().is_empty() {
                    let signature = crate::former::signature(self.context, datatype)?;
                    crate::respect::respected(self.context, term, &signature, reading)?;
                }
                Ok(Step::Ascend(Produced::Checked))
            },
            (Frame::NativeLoops { term, datatype }, Produced::Checked) => {
                // As the rules are, a loop is judged on the elaborated body.
                if self.context.nesting().is_empty() {
                    let signature = crate::former::signature(self.context, datatype)?;
                    crate::loops::respected(self.context, term, (datatype, &signature))?;
                }
                Ok(Step::Ascend(Produced::Checked))
            },
            // The identified telescope forms in the block's foresight, which
            // closes before the branch checks at it.
            (Frame::NativeForesee(telescope), Produced::Checked) => {
                let foresight = self.context.foresee_hindsight();
                self.wait(Frame::NativeForget(foresight));
                Ok(Step::Descend(Goal::Form(TypeNode::Computation(telescope))))
            },
            (Frame::NativeForget(foresight), Produced::Checked) => {
                self.context.forget_foresight(foresight);
                Ok(Step::Ascend(Produced::Checked))
            },
            (Frame::SigmaSplitScrutinee(term), Produced::ValueType(classifier)) => {
                let classifier = classifier.settle(self.context.arena_mut());
                self.sigma_split(term, classifier)
            },
            (Frame::SigmaSplitMotive { term, sigma }, Produced::Checked) => {
                self.sigma_split_body(term, sigma)
            },
            (Frame::NativeProjection(term), Produced::ValueType(record)) => {
                let record = record.settle(self.context.arena_mut());
                self.native_projection(term, record)
            },
            (Frame::Resume { stack, body }, Produced::ValueType(classifier)) => {
                let classifier = classifier.settle(self.context.arena_mut());
                let (input, output) = self.stack_expected(stack, classifier)?;
                // A resumption hands a buffer on whole, as a send does: its
                // slot is spent, never read.
                if let Computation::Return(returned) = *self.computation(body)? {
                    let head = self.context.whnf_comp_type(input)?;
                    if let CompTypeView::Returner { result, .. } =
                        comp_type_view(self.context.arena(), head)?
                        && self.returned_buffer(body, returned, result)?
                            == session::HandedOn::Buffer
                    {
                        return Ok(Step::Ascend(Produced::CompType(output)));
                    }
                }
                self.wait(Frame::PrimitiveResult { result: output });
                Ok(Step::Descend(Goal::Computation {
                    term: body,
                    direction: Direction::Check(input),
                }))
            },
            // An abandonment returns the unit and performs no operation: the
            // unwinds it runs answer under the empty row.
            (Frame::Abandon { stack }, Produced::ValueType(classifier)) => {
                let classifier = classifier.settle(self.context.arena_mut());
                let _fed = self.stack_expected(stack, classifier)?;
                Ok(Step::Ascend(Produced::CompType(self.unit_returner())))
            },
            (Frame::Project { at, component }, Produced::CompType(classifier)) => {
                Ok(Step::Ascend(Produced::CompType(
                    match self.with_parts(TermNode::Computation(at), classifier)? {
                        Components::Known(parts) => *parts
                            .get(usize::from(component))
                            .ok_or(CheckRefusal::AbsentTupleComponent(at))?,
                        Components::Unknown(unknown) => unknown,
                    },
                )))
            },
            (
                Frame::HandlerForm {
                    at,
                    answer,
                    interface,
                },
                Produced::Checked,
            ) => {
                let Computation::Handle { subject, .. } = *self.computation(at)?
                else {
                    return Err(CheckRefusal::MachineInvariant);
                };
                self.wait(Frame::HandlerSubject {
                    at,
                    answer,
                    interface,
                });
                Ok(Step::Descend(Goal::Computation {
                    term: subject,
                    direction: Direction::Synthesise,
                }))
            },
            (
                Frame::HandlerSubject {
                    at,
                    answer,
                    interface,
                },
                Produced::CompType(subject),
            ) => self.handle_subject(at, answer, interface, subject),
            (Frame::ExerciseCapability { at }, Produced::ValueType(classifier)) => {
                let classifier = classifier.settle(self.context.arena_mut());
                self.exercise(at, classifier)
            },
            (
                Frame::ScopeForm {
                    at,
                    answer,
                    subject,
                },
                Produced::Checked,
            ) => self.scope_subject(at, answer, subject),
            (Frame::ScopeSubject { at, answer }, Produced::Checked) => {
                self.close_region()?;
                self.scope_return(at, answer)
            },
            (Frame::HandlerReturn { at, answer }, Produced::Checked) => {
                self.close()?;
                self.handle_clause(at, answer, Ordinal::FIRST)
            },
            (
                Frame::HandlerClause {
                    at,
                    answer,
                    position,
                },
                Produced::Checked,
            ) => {
                self.owed_ended()?;
                self.close()?;
                self.close()?;
                self.handle_clause(at, answer, position)
            },
            (
                Frame::StackNext {
                    judgement,
                    position,
                },
                Produced::CompType(input),
            ) => Ok(Step::Descend(Goal::Stack {
                judgement,
                position,
                input,
            })),
            (Frame::StackBind { at, body, bound }, Produced::CompType(synthesised)) => {
                let Maybe::Present(lowered) =
                    strengthen_comp_type(self.context.arena_mut(), synthesised)
                else {
                    return Err(CheckRefusal::DependentStack { at, synthesised });
                };
                let lowered = lowered.settle(self.context.arena_mut());
                self.close()?;
                let result = self.accumulate_effects(body, bound, lowered)?;
                Ok(Step::Ascend(Produced::CompType(result)))
            },
            (Frame::ListFold { at, result, phase }, Produced::Checked) => {
                self.list_fold(at, result, phase)
            },
            (
                Frame::PrimitiveSecond {
                    argument,
                    expected,
                    result,
                },
                Produced::Checked,
            ) => {
                self.wait(Frame::PrimitiveResult { result });
                Ok(Step::Descend(Goal::Value {
                    term: argument,
                    direction: Direction::Check(expected),
                }))
            },
            (
                Frame::PerformPayload {
                    at,
                    payload,
                    expected,
                    result,
                },
                Produced::Checked,
            ) => {
                // An operation's buffer payload is returned to the handler
                // whole, as a send's is.
                if self.returned_buffer(at, payload, expected)? == session::HandedOn::Buffer {
                    return Ok(Step::Ascend(Produced::CompType(result)));
                }
                self.wait(Frame::PrimitiveResult { result });
                Ok(Step::Descend(Goal::Value {
                    term: payload,
                    direction: Direction::Check(expected),
                }))
            },
            (
                Frame::PrimitiveResult { result } | Frame::TransportOperand { result },
                Produced::Checked,
            ) => Ok(Step::Ascend(Produced::CompType(result))),
            (
                Frame::PathProductFirst {
                    product,
                    at,
                    second,
                },
                Produced::ValueType(classifier),
            ) => {
                let classifier = classifier.settle(self.context.arena_mut());
                let first = crate::product::component(self.context, at, classifier)?;
                self.wait(Frame::PathProductSecond {
                    product,
                    at: second,
                    classifier,
                    first,
                });
                Ok(Step::Descend(Goal::Value {
                    term: second,
                    direction: Direction::Synthesise,
                }))
            },
            (
                Frame::PathProductSecond {
                    product,
                    at,
                    classifier: first_classifier,
                    first,
                },
                Produced::ValueType(classifier),
            ) => {
                let classifier = classifier.settle(self.context.arena_mut());
                let second = crate::product::component(self.context, at, classifier)?;
                if first.reading == crate::product::Reading::Element
                    || second.reading == crate::product::Reading::Element
                {
                    let native = crate::product::native(
                        self.context,
                        product,
                        (first_classifier, classifier),
                    )?;
                    self.context.record_native(product, native);
                }
                let classifier =
                    crate::product::classifier(self.context.arena_mut(), first, second);
                Ok(Step::Ascend(Produced::ValueType(classifier.into())))
            },
            (
                Frame::PathBackward {
                    backward,
                    source,
                    target,
                    path_type,
                },
                Produced::Checked,
            ) => {
                let expected = self.map_type(target, source);
                self.wait(Frame::PathChecked { path_type });
                Ok(Step::Descend(Goal::Value {
                    term: backward,
                    direction: Direction::Check(expected),
                }))
            },
            (Frame::PathChecked { path_type }, Produced::Checked) => {
                Ok(Step::Ascend(Produced::ValueType(path_type.into())))
            },
            (Frame::TransportPath { path, value }, Produced::ValueType(classifier)) => {
                let classifier = classifier.settle(self.context.arena_mut());
                let (source, target) = self.path_endpoints(path, classifier)?;
                let result = self.context.arena_mut().comp_type_returner(target);
                self.wait(Frame::TransportOperand { result });
                Ok(Step::Descend(Goal::Value {
                    term: value,
                    direction: Direction::Check(source),
                }))
            },
            (Frame::HereSynthesised { point }, Produced::ValueType(carrier)) => {
                let carrier = carrier.settle(self.context.arena_mut());
                let path = self
                    .context
                    .arena_mut()
                    .value_type_path(carrier, point, point);
                Ok(Step::Ascend(Produced::ValueType(path.into())))
            },
            (
                Frame::HereEndpoints {
                    at,
                    point,
                    left,
                    right,
                },
                Produced::Checked,
            ) => {
                self.reaches(at, point, left, right)?;
                Ok(Step::Ascend(Produced::Checked))
            },
            (Frame::FunextLeft { at, left, right }, Produced::ValueType(classifier)) => {
                let classifier = classifier.settle(self.context.arena_mut());
                self.wait(Frame::FunextRight {
                    at,
                    left,
                    right,
                    classifier,
                });
                Ok(Step::Descend(Goal::Value {
                    term: right,
                    direction: Direction::Check(classifier),
                }))
            },
            (
                Frame::FunextRight {
                    at,
                    left,
                    right,
                    classifier,
                },
                Produced::Checked,
            ) => {
                let funext = crate::funext::decide(self.context, at, (left, right), classifier)?;
                self.context.record_funext(at, funext);
                let path = self
                    .context
                    .arena_mut()
                    .value_type_path(classifier, left, right);
                Ok(Step::Ascend(Produced::ValueType(path.into())))
            },
            (
                Frame::EquivForward {
                    at,
                    forward,
                    backward,
                },
                Produced::ValueType(classifier),
            ) => {
                let classifier = classifier.settle(self.context.arena_mut());
                let codes = crate::equiv::codes(self.context, at, classifier)?;
                let inverse = crate::equiv::translator(self.context, (codes.1, codes.0));
                self.wait(Frame::EquivBackward {
                    at,
                    forward,
                    backward,
                    codes,
                });
                Ok(Step::Descend(Goal::Value {
                    term: backward,
                    direction: Direction::Check(inverse),
                }))
            },
            (
                Frame::EquivBackward {
                    at,
                    forward,
                    backward,
                    codes,
                },
                Produced::Checked,
            ) => {
                let decided = crate::equiv::decide(self.context, at, (forward, backward), codes)?;
                let path = decided.identity(self.context.arena_mut());
                self.context.record_equivalence(at, decided);
                Ok(Step::Ascend(Produced::ValueType(path.into())))
            },
            (
                Frame::UnivalenceRecord {
                    at,
                    record,
                    forward,
                },
                Produced::ValueType(classifier),
            ) => {
                let classifier = classifier.settle(self.context.arena_mut());
                let premises =
                    crate::univalence::premises(self.context, at, (record, forward), classifier)?;
                let owner = self.owner;
                self.frames.push(Waiting {
                    frame: Frame::UnivalenceChecked {
                        path: premises.path,
                    },
                    owner,
                });
                let [(first, first_type), rest @ ..] = premises.checks;
                for &(term, expected) in rest.iter().rev() {
                    self.frames.push(Waiting {
                        frame: Frame::NativeNext(Goal::Value {
                            term,
                            direction: Direction::Check(expected),
                        }),
                        owner,
                    });
                }
                Ok(Step::Descend(Goal::Value {
                    term: first,
                    direction: Direction::Check(first_type),
                }))
            },
            (Frame::UnivalenceChecked { path }, Produced::Checked) => {
                Ok(Step::Ascend(Produced::ValueType(path.into())))
            },
            (Frame::UaTranslators { at }, Produced::Checked) => {
                let universal = crate::ua::decide(self.context, at)?;
                self.context.record_native(at, universal.path());
                let identity = universal.identity(self.context.arena_mut());
                Ok(Step::Ascend(Produced::ValueType(identity.into())))
            },
            (Frame::Ran { at, read }, Produced::CompType(synthesised)) => {
                let head = self.context.whnf_comp_type(synthesised)?;
                let (result, purity) = match comp_type_view(self.context.arena(), head)? {
                    CompTypeView::Returner { result, effects } => (result, effects.purity()),
                    CompTypeView::Unknown => (
                        self.context.arena_mut().value_type_unknown(),
                        gandr_core_term::effect::Purity::Pure,
                    ),
                    CompTypeView::With(..)
                    | CompTypeView::Arrow { .. }
                    | CompTypeView::Pi { .. }
                    | CompTypeView::Element { .. }
                    | CompTypeView::Codata { .. } => {
                        let Some(&(Value::Nested(nested) | Value::Run(nested))) =
                            self.context.arena().value(at)
                        else {
                            return Err(CheckRefusal::MachineInvariant);
                        };
                        return Err(CheckRefusal::ShapeMismatch {
                            at: TermNode::Computation(nested),
                            wanted: ExpectedShape::Returner,
                            found: TypeNode::Computation(synthesised),
                        });
                    },
                };
                // A pure run a type after it reads stands as what it returns.
                let decided = match (
                    purity,
                    self.context.nesting().get(&self.context.written(at)),
                ) {
                    (gandr_core_term::effect::Purity::Pure, Some(&Nesting::Returned)) => {
                        Nesting::Returned
                    },
                    (
                        gandr_core_term::effect::Purity::Pure
                        | gandr_core_term::effect::Purity::Effectful,
                        _,
                    ) => Nesting::Ran(purity),
                };
                self.context.record_nesting(at, decided);
                // A value read without a goal of its own keeps its typing here,
                // at what it returns: the patterns of a case on it are read at
                // that type.
                if read == Read::Unsuspended
                    && self.context.recording() == crate::context::Recording::On
                {
                    self.context.keep_typing(Typing {
                        term: TermNode::Value(at),
                        ty: TypeNode::Value(result),
                        depth: self.context.depth(Zone::Intuitionistic),
                    });
                }
                Ok(Step::Ascend(Produced::ValueType(result.into())))
            },
            // A call read where a thunk of no returner is read: one that
            // returns runs, its value crossing to the thunk type, and any other
            // is suspended, its type crossing to the thunk's body.
            (
                Frame::NestedCall {
                    at,
                    call,
                    expected,
                    body,
                },
                Produced::CompType(synthesised),
            ) => {
                let head = self.context.whnf_comp_type(synthesised)?;
                if matches!(
                    comp_type_view(self.context.arena(), head)?,
                    CompTypeView::Returner { .. }
                ) {
                    self.wait(Frame::ValueBridge { at, expected });
                    self.wait(Frame::Ran {
                        at,
                        read: Read::Goal,
                    });
                    return Ok(Step::Ascend(Produced::CompType(synthesised)));
                }
                self.context.record_nesting(at, Nesting::Suspended);
                comp_bridge(self.context, call, synthesised, body, &mut self.conversions)?;
                Ok(Step::Ascend(Produced::Checked))
            },
            (Frame::ReturnedEndpoint { at }, Produced::CompType(synthesised)) => {
                let head = self.context.whnf_comp_type(synthesised)?;
                match comp_type_view(self.context.arena(), head)? {
                    CompTypeView::Returner { result, effects }
                        if effects.purity() == gandr_core_term::effect::Purity::Pure =>
                    {
                        Ok(Step::Ascend(Produced::ValueType(result.into())))
                    },
                    CompTypeView::Unknown => {
                        let unknown = self.context.arena_mut().value_type_unknown();
                        Ok(Step::Ascend(Produced::ValueType(unknown.into())))
                    },
                    CompTypeView::Returner { .. }
                    | CompTypeView::With(..)
                    | CompTypeView::Arrow { .. }
                    | CompTypeView::Pi { .. }
                    | CompTypeView::Element { .. }
                    | CompTypeView::Codata { .. } => {
                        Err(CheckRefusal::CompoundEndpoint { at, synthesised })
                    },
                }
            },
            (
                Frame::ElementTransportPath { at, motive, value },
                Produced::ValueType(classifier),
            ) => {
                let classifier = classifier.settle(self.context.arena_mut());
                let PathReading::Known {
                    carrier,
                    left,
                    right,
                } = self.transported_path(TermNode::Computation(at), classifier)?
                else {
                    return Err(CheckRefusal::ShapeMismatch {
                        at: TermNode::Computation(at),
                        wanted: ExpectedShape::Path,
                        found: TypeNode::Value(classifier),
                    });
                };
                let motive = crate::flow::levelled(self.context, at, motive, carrier)?;
                self.context.binders().open(Zone::Intuitionistic, carrier);
                self.wait(Frame::ElementTransportMotive {
                    at,
                    motive,
                    value,
                    carrier,
                    left,
                    right,
                });
                self.wait(Frame::FormBinder);
                Ok(Step::Descend(Goal::Form(TypeNode::Value(motive))))
            },
            (
                Frame::ElementTransportMotive {
                    at,
                    motive,
                    value,
                    carrier,
                    left,
                    right,
                },
                Produced::Checked,
            ) => {
                let arena = self.context.arena_mut();
                let source = instantiate_value_type(arena, motive, left);
                let target = instantiate_value_type(arena, motive, right);
                let target =
                    crate::recursion::carried_stage(self.context, at, value, (carrier, target))?;
                let result = self.context.arena_mut().comp_type_returner(target);
                self.wait(Frame::TransportOperand { result });
                Ok(Step::Descend(Goal::Value {
                    term: value,
                    direction: Direction::Check(source),
                }))
            },
            (Frame::SessionStatement { at }, Produced::Checked) => {
                let Value::SessionRelated {
                    relation,
                    source,
                    target,
                    payloads,
                } = *self.value(at)?
                else {
                    return Err(CheckRefusal::MachineInvariant);
                };
                let statement = crate::flow::decide(self.context, at, relation, (source, target))?;
                let identity =
                    crate::flow::identity(self.context.arena_mut(), relation, (source, target));
                let unwritten = matches!(
                    self.context.arena().value(payloads),
                    Some(Value::Tuple(components)) if components.is_empty()
                );
                if unwritten && !statement.owed().is_empty() {
                    return Err(CheckRefusal::SessionNotEquivalent { at });
                }
                let expected = (!unwritten).then(|| {
                    crate::flow::payload_paths(self.context.arena_mut(), statement.owed())
                });
                self.context.record_flow(at, statement);
                let Some(expected) = expected
                else {
                    return Ok(Step::Ascend(Produced::ValueType(identity.into())));
                };
                self.wait(Frame::SessionPayloads { at, identity });
                Ok(Step::Descend(Goal::Value {
                    term: payloads,
                    direction: Direction::Check(expected),
                }))
            },
            (Frame::SessionPayloads { at, identity }, Produced::Checked) => {
                crate::flow::elaborate(self.context, at)?;
                Ok(Step::Ascend(Produced::ValueType(identity.into())))
            },
            (Frame::StaySynthesised { at, point }, Produced::ValueType(carrier)) => {
                let carrier = carrier.settle(self.context.arena_mut());
                crate::flow::record_simulation(self.context, at, carrier, (point, point))?;
                let flow = self
                    .context
                    .arena_mut()
                    .value_type_flow(carrier, point, point);
                Ok(Step::Ascend(Produced::ValueType(flow.into())))
            },
            (Frame::ThenFirst { at, second }, Produced::ValueType(first)) => {
                let first = first.settle(self.context.arena_mut());
                self.wait(Frame::ThenSecond { at, first });
                Ok(Step::Descend(Goal::Value {
                    term: second,
                    direction: Direction::Synthesise,
                }))
            },
            (Frame::ThenSecond { at, first }, Produced::ValueType(synthesised)) => {
                let synthesised = synthesised.settle(self.context.arena_mut());
                let Value::Then(_, second) = *self.value(at)?
                else {
                    return Err(CheckRefusal::MachineInvariant);
                };
                let (carrier, source, middle) =
                    crate::flow::endpoints(self.context, TermNode::Value(at), first)?;
                let (_, _, end) =
                    crate::flow::endpoints(self.context, TermNode::Value(second), synthesised)?;
                let expected = self
                    .context
                    .arena_mut()
                    .value_type_flow(carrier, middle, end);
                value_bridge(
                    self.context,
                    second,
                    synthesised,
                    expected,
                    &mut self.conversions,
                )?;
                crate::flow::record_simulation(self.context, at, carrier, (source, end))?;
                let composite = self
                    .context
                    .arena_mut()
                    .value_type_flow(carrier, source, end);
                Ok(Step::Ascend(Produced::ValueType(composite.into())))
            },
            (
                Frame::FlowProductFirst {
                    product: _,
                    at,
                    second,
                },
                Produced::ValueType(classifier),
            ) => {
                let classifier = classifier.settle(self.context.arena_mut());
                let first = crate::product::flow_component(self.context, at, classifier)?;
                self.wait(Frame::FlowProductSecond { at: second, first });
                Ok(Step::Descend(Goal::Value {
                    term: second,
                    direction: Direction::Synthesise,
                }))
            },
            (Frame::FlowProductSecond { at, first }, Produced::ValueType(classifier)) => {
                let classifier = classifier.settle(self.context.arena_mut());
                let second = crate::product::flow_component(self.context, at, classifier)?;
                let product =
                    crate::product::flow_classifier(self.context.arena_mut(), first, second);
                Ok(Step::Ascend(Produced::ValueType(product.into())))
            },
            (Frame::UpdateBase { at }, Produced::ValueType(base)) => {
                let base = base.settle(self.context.arena_mut());
                self.update_base(at, base)
            },
            (Frame::UpdateOverlay { at, base }, Produced::ValueType(overlay)) => {
                let overlay = overlay.settle(self.context.arena_mut());
                self.native_update(at, base, overlay)
            },
            (Frame::RideFlow { at, motive, .. }, Produced::ValueType(flow)) => {
                let flow = flow.settle(self.context.arena_mut());
                let (carrier, ..) =
                    crate::flow::endpoints(self.context, TermNode::Computation(at), flow)?;
                let motive = crate::flow::levelled(self.context, at, motive, carrier)?;
                self.context.binders().open(Zone::Intuitionistic, carrier);
                self.wait(Frame::RideMotive { at, flow });
                self.wait(Frame::FormBinder);
                Ok(Step::Descend(Goal::Form(TypeNode::Value(motive))))
            },
            (Frame::RideMotive { at, flow }, Produced::Checked) => {
                let ride = crate::flow::ride(self.context, at, flow)?;
                self.wait(Frame::RideValue {
                    at,
                    value: ride.value,
                    flow,
                    result: ride.result,
                    moving: ride.moving,
                });
                Ok(Step::Descend(Goal::Value {
                    term: ride.value,
                    direction: Direction::Check(ride.source),
                }))
            },
            (
                Frame::RideValue {
                    at,
                    value,
                    flow,
                    result,
                    moving,
                },
                Produced::Checked,
            ) => {
                crate::flow::admit(self.context, at, value, flow, moving)?;
                Ok(Step::Ascend(Produced::CompType(result)))
            },
            (Frame::ForwardTranslator { at, translator }, Produced::ValueType(classifier)) => {
                let classifier = classifier.settle(self.context.arena_mut());
                let codes = crate::forward::codes(self.context, at, classifier)?;
                let decided = crate::forward::decide(self.context, at, translator, codes)?;
                let flow = decided.classifier();
                self.context
                    .record_directed(at, crate::forward::Directed::Forward(decided));
                Ok(Step::Ascend(Produced::ValueType(flow.into())))
            },
            (Frame::ArrowDomain { at, codomain }, Produced::ValueType(domain_type)) => {
                let domain_type = domain_type.settle(self.context.arena_mut());
                self.wait(Frame::ArrowCodomain { at, domain_type });
                Ok(Step::Descend(Goal::Value {
                    term: codomain,
                    direction: Direction::Synthesise,
                }))
            },
            (Frame::ArrowCodomain { at, domain_type }, Produced::ValueType(codomain_type)) => {
                let codomain_type = codomain_type.settle(self.context.arena_mut());
                let Value::FunctionFlow(domain, codomain) = *self.value(at)?
                else {
                    return Err(CheckRefusal::MachineInvariant);
                };
                let flow = crate::forward::arrow(
                    self.context,
                    at,
                    (domain, domain_type),
                    (codomain, codomain_type),
                )?;
                self.context
                    .record_directed(at, crate::forward::Directed::Function(flow));
                Ok(Step::Ascend(Produced::ValueType(flow.into())))
            },
            (Frame::ArrowAgainst { at, expected }, Produced::ValueType(synthesised)) => {
                let synthesised = synthesised.settle(self.context.arena_mut());
                let Value::FunctionFlow(domain, codomain) = *self.value(at)?
                else {
                    return Err(CheckRefusal::MachineInvariant);
                };
                crate::forward::against(
                    self.context,
                    at,
                    (domain, codomain),
                    (synthesised, expected),
                    &mut self.conversions,
                )?;
                Ok(Step::Ascend(Produced::Checked))
            },
            (
                Frame::StayEndpoints {
                    at,
                    point,
                    carrier,
                    left,
                    right,
                },
                Produced::Checked,
            ) => {
                self.reaches(at, point, left, right)?;
                crate::flow::record_simulation(self.context, at, carrier, (left, right))?;
                Ok(Step::Ascend(Produced::Checked))
            },
            (Frame::TelescopePath { at }, Produced::ValueType(classifier)) => {
                let classifier = classifier.settle(self.context.arena_mut());
                let PathReading::Known {
                    carrier,
                    left,
                    right,
                } = self.transported_path(TermNode::Computation(at), classifier)?
                else {
                    return Err(CheckRefusal::ShapeMismatch {
                        at: TermNode::Computation(at),
                        wanted: ExpectedShape::Path,
                        found: TypeNode::Value(classifier),
                    });
                };
                let (motive, _) = self.telescope(at)?;
                self.wait(Frame::TelescopeMotive {
                    at,
                    carrier,
                    ends: (left, right),
                });
                Ok(Step::Descend(Goal::Form(TypeNode::Computation(motive))))
            },
            (
                Frame::TelescopeMotive {
                    at,
                    carrier,
                    ends: (left, right),
                },
                Produced::Checked,
            ) => {
                let Computation::TelescopeTransport { path, start, .. } = *self.computation(at)?
                else {
                    return Err(CheckRefusal::MachineInvariant);
                };
                let (_, parts) = self.telescope(at)?;
                value_bridge(
                    self.context,
                    path,
                    carrier,
                    parts.carrier,
                    &mut self.conversions,
                )?;
                let source = instantiate_value_type(self.context.arena_mut(), parts.family, left);
                self.wait(Frame::TelescopeStart {
                    at,
                    ends: (left, right),
                });
                Ok(Step::Descend(Goal::Value {
                    term: start,
                    direction: Direction::Check(source),
                }))
            },
            (Frame::TelescopeStart { at, ends }, Produced::Checked) => {
                let Computation::TelescopeTransport { over, .. } = *self.computation(at)?
                else {
                    return Err(CheckRefusal::MachineInvariant);
                };
                self.wait(Frame::TelescopeOver { at, ends });
                Ok(Step::Descend(Goal::Value {
                    term: over,
                    direction: Direction::Synthesise,
                }))
            },
            (
                Frame::TelescopeOver {
                    at,
                    ends: (left, right),
                },
                Produced::ValueType(classifier),
            ) => {
                let classifier = classifier.settle(self.context.arena_mut());
                let Computation::TelescopeTransport {
                    path,
                    start,
                    over,
                    value,
                    ..
                } = *self.computation(at)?
                else {
                    return Err(CheckRefusal::MachineInvariant);
                };
                let (_, parts) = self.telescope(at)?;
                let PathReading::Known { right: finish, .. } =
                    self.path_expected(TermNode::Value(over), classifier)?
                else {
                    return Err(CheckRefusal::ShapeMismatch {
                        at: TermNode::Value(over),
                        wanted: ExpectedShape::Path,
                        found: TypeNode::Value(classifier),
                    });
                };
                let arena = self.context.arena_mut();
                let fibre = instantiate_value_type(arena, parts.family, right);
                let carried = arena.computation_path_transport(parts.family, path, start);
                let carried = arena.value_returned(carried);
                let lies_over = arena.value_type_path(fibre, carried, finish);
                match value_bridge(
                    self.context,
                    over,
                    classifier,
                    lies_over,
                    &mut self.conversions,
                ) {
                    Ok(()) => {},
                    Err(CheckRefusal::TypeMismatch(Mismatch::Value { .. })) => {
                        return Err(CheckRefusal::NotOver {
                            at: over,
                            synthesised: classifier,
                            expected: lies_over,
                        });
                    },
                    Err(refusal) => return Err(refusal),
                }
                let arena = self.context.arena_mut();
                let source = telescope_instance(arena, parts.body, (left, start));
                let target = telescope_instance(arena, parts.body, (right, finish));
                let result = arena.comp_type_returner(target);
                self.wait(Frame::TransportOperand { result });
                Ok(Step::Descend(Goal::Value {
                    term: value,
                    direction: Direction::Check(source),
                }))
            },
            (
                Frame::CaseScrutinee {
                    at,
                    scrutinee,
                    expected,
                },
                Produced::ValueType(classifier),
            ) => {
                let classifier = classifier.settle(self.context.arena_mut());
                let summands = self.sum_expected(scrutinee, classifier)?;
                let expected =
                    shift_comp_type(self.context.arena_mut(), expected, Binders::from(1_u32))
                        .settle(self.context.arena_mut());
                let joining = self.arms_opened();
                let Some(case) = self.context.arena().computation(at)
                else {
                    return Err(CheckRefusal::MachineInvariant);
                };
                let Computation::Case { ref branches, .. } = *case
                else {
                    return Err(CheckRefusal::MachineInvariant);
                };
                if matches!(summands, Components::Known(ref parts) if parts.len() != branches.len())
                {
                    return Err(CheckRefusal::ShapeMismatch {
                        at: TermNode::Value(scrutinee),
                        wanted: ExpectedShape::Sum,
                        found: TypeNode::Value(classifier),
                    });
                }
                let owner = self.owner;
                if let session::Joining::Joined(zones) = joining {
                    // An empty case checks no arm, so no arm can disagree: the
                    // join names the case itself.
                    let arm = branches.last().copied().unwrap_or(at);
                    self.frames.push(Waiting {
                        frame: Frame::ArmsJoined { zones, arm },
                        owner,
                    });
                }
                for (index, &branch) in branches.iter().enumerate().rev() {
                    let summand = match summands {
                        Components::Known(ref parts) => {
                            *parts.get(index).ok_or(CheckRefusal::MachineInvariant)?
                        },
                        Components::Unknown(unknown) => unknown,
                    };
                    self.frames.push(Waiting {
                        frame: Frame::CaseBranch {
                            branch,
                            summand,
                            expected,
                        },
                        owner,
                    });
                    if let session::Joining::Joined(zones) = joining
                        && let Some(&arm) =
                            index.checked_sub(1).and_then(|before| branches.get(before))
                    {
                        self.frames.push(Waiting {
                            frame: Frame::ArmEnded { zones, arm },
                            owner,
                        });
                    }
                }
                Ok(Step::Ascend(Produced::Checked))
            },
            (
                Frame::SplitScrutinee {
                    at,
                    scrutinee,
                    direction,
                },
                Produced::ValueType(classifier),
            ) => {
                let classifier = classifier.settle(self.context.arena_mut());
                self.split(at, scrutinee, classifier, direction)
            },
            (Frame::SplitBody { arity, .. }, Produced::Checked) => {
                for _ in 0_usize .. usize::from(arity) {
                    self.close()?;
                }
                Ok(Step::Ascend(Produced::Checked))
            },
            (Frame::SplitBody { at, arity }, Produced::CompType(synthesised)) => {
                // Every binder stays open until the type has left them all, so a
                // refusal attributes each to this frame.
                let mut lowered = synthesised;
                for _ in 0_usize .. usize::from(arity) {
                    let Maybe::Present(outer) =
                        strengthen_comp_type(self.context.arena_mut(), lowered)
                    else {
                        return Err(CheckRefusal::DependentBind { at, synthesised });
                    };
                    lowered = outer.settle(self.context.arena_mut());
                }
                for _ in 0_usize .. usize::from(arity) {
                    self.close()?;
                }
                Ok(Step::Ascend(Produced::CompType(lowered)))
            },
            (
                Frame::CaseBranch {
                    branch,
                    summand,
                    expected,
                },
                Produced::Checked,
            ) => {
                self.context.binders().open(Zone::Intuitionistic, summand);
                self.wait(Frame::LambdaBody);
                Ok(Step::Descend(Goal::Computation {
                    term: branch,
                    direction: Direction::Check(expected),
                }))
            },
            (
                Frame::ListCaseScrutinee {
                    at,
                    scrutinee,
                    expected,
                },
                Produced::ValueType(classifier),
            ) => {
                let classifier = classifier.settle(self.context.arena_mut());
                let (list, opened) = crate::recursion::open_case(self.context, classifier)?;
                let element = self.list_expected(scrutinee, list)?;
                let tail = self.context.arena_mut().value_type_list(element);
                let tail = match opened {
                    Maybe::Present(child) => self
                        .context
                        .arena_mut()
                        .value_type_staged(tail, gandr_kernel_term::Stage::At(child)),
                    Maybe::Absent(_) => tail,
                };
                let Computation::ListCase {
                    on_nil, on_cons, ..
                } = *self.computation(at)?
                else {
                    return Err(CheckRefusal::MachineInvariant);
                };
                let joining = self.arms_opened();
                if let session::Joining::Joined(zones) = joining {
                    self.wait(Frame::ArmsJoined {
                        zones,
                        arm: on_cons,
                    });
                }
                self.wait(Frame::ListCaseNil {
                    at,
                    element,
                    tail,
                    expected,
                });
                if let session::Joining::Joined(zones) = joining {
                    self.wait(Frame::ArmEnded { zones, arm: on_nil });
                }
                Ok(Step::Descend(Goal::Computation {
                    term: on_nil,
                    direction: Direction::Check(expected),
                }))
            },
            (
                Frame::ListCaseNil {
                    at,
                    element,
                    tail,
                    expected,
                },
                Produced::Checked,
            ) => {
                let Computation::ListCase { on_cons, .. } = *self.computation(at)?
                else {
                    return Err(CheckRefusal::MachineInvariant);
                };
                let tail = shift_value_type(self.context.arena_mut(), tail, Binders::from(1_u32))
                    .settle(self.context.arena_mut());
                let expected =
                    shift_comp_type(self.context.arena_mut(), expected, Binders::from(2_u32))
                        .settle(self.context.arena_mut());
                self.context.binders().open(Zone::Intuitionistic, element);
                self.context.binders().open(Zone::Intuitionistic, tail);
                self.wait(Frame::ListCaseCons);
                Ok(Step::Descend(Goal::Computation {
                    term: on_cons,
                    direction: Direction::Check(expected),
                }))
            },
            (Frame::ListCaseCons, Produced::Checked) => {
                self.close()?;
                self.close()?;
                Ok(Step::Ascend(Produced::Checked))
            },
            (Frame::ArmEnded { zones, arm }, Produced::Checked) => {
                self.arm_ended(zones, arm)?;
                Ok(Step::Ascend(Produced::Checked))
            },
            (Frame::ArmsJoined { zones, arm }, Produced::Checked) => {
                self.arms_joined(zones, arm)?;
                Ok(Step::Ascend(Produced::Checked))
            },
            (Frame::Force { value }, Produced::ValueType(synthesised)) => {
                let synthesised = synthesised.settle(self.context.arena_mut());
                let mut head = self.context.whnf_value_type(synthesised)?;
                // A thunk kept in a region forces as the thunk it keeps.
                if let ValueTypeView::Kept { value: kept, .. } =
                    value_type_view(self.context.arena(), head)?
                {
                    head = self.context.whnf_value_type(kept)?;
                }
                match matched_thunk(self.context.arena_mut(), head) {
                    Maybe::Present(body) => Ok(Step::Ascend(Produced::CompType(body))),
                    Maybe::Absent(absent) => Err(unmatched(
                        absent,
                        TypeNode::Value(head),
                        CheckRefusal::ShapeMismatch {
                            at: TermNode::Value(value),
                            wanted: ExpectedShape::Thunk,
                            found: TypeNode::Value(synthesised),
                        },
                    )),
                }
            },
            (Frame::Decompose { dialogue }, Produced::ValueType(synthesised)) => {
                let synthesised = synthesised.settle(self.context.arena_mut());
                let head = self.context.whnf_value_type(synthesised)?;
                match value_type_view(self.context.arena(), head)? {
                    ValueTypeView::Dialogue(_) | ValueTypeView::Unknown => {
                        let web = self.context.arena_mut().value_type_web();
                        let returner = self.context.arena_mut().comp_type_returner(web);
                        Ok(Step::Ascend(Produced::CompType(returner)))
                    },
                    ValueTypeView::Data { .. }
                    | ValueTypeView::Record(_)
                    | ValueTypeView::Stack { .. }
                    | ValueTypeView::PathUniverse(..)
                    | ValueTypeView::Path { .. }
                    | ValueTypeView::Bridge { .. }
                    | ValueTypeView::Flow { .. }
                    | ValueTypeView::Run(_)
                    | ValueTypeView::Prefix(_)
                    | ValueTypeView::Web
                    | ValueTypeView::Sum(_)
                    | ValueTypeView::List(_)
                    | ValueTypeView::Integer
                    | ValueTypeView::String
                    | ValueTypeView::Character
                    | ValueTypeView::Float64
                    | ValueTypeView::Fixed(_)
                    | ValueTypeView::Unit
                    | ValueTypeView::Thunk(_)
                    | ValueTypeView::Universe { .. }
                    | ValueTypeView::Lift { .. }
                    | ValueTypeView::Element { .. }
                    | ValueTypeView::Product(_)
                    | ValueTypeView::StaticPi { .. }
                    | ValueTypeView::Sigma { .. }
                    | ValueTypeView::Abstract(_)
                    | ValueTypeView::Staged { .. }
                    | ValueTypeView::Kept { .. }
                    | ValueTypeView::Capability { .. }
                    | ValueTypeView::Buffer
                    | ValueTypeView::Row
                    | ValueTypeView::RowTail(_)
                    | ValueTypeView::Session(_)
                    | ValueTypeView::World(_) => Err(CheckRefusal::ShapeMismatch {
                        at: TermNode::Value(dialogue),
                        wanted: ExpectedShape::Dialogue,
                        found: TypeNode::Value(synthesised),
                    }),
                }
            },
            (Frame::FixpointArgument { head, expected }, Produced::ValueType(domain)) => {
                let domain = domain.settle(self.context.arena_mut());
                let arrow = self.context.arena_mut().comp_type_arrow(domain, expected);
                Ok(Step::Descend(Goal::Computation {
                    term: head,
                    direction: Direction::Check(arrow),
                }))
            },
            (Frame::ApplicationHead { head, argument }, Produced::CompType(synthesised)) => {
                let (domain, codomain) =
                    self.application_type(TermNode::Computation(head), synthesised)?;
                self.wait(Frame::ApplicationArgument {
                    head: Some(head),
                    argument,
                    domain,
                    codomain,
                });
                Ok(Step::Descend(Goal::Value {
                    term: argument,
                    direction: Direction::Check(domain),
                }))
            },
            (
                Frame::ApplicationArgument {
                    head,
                    argument,
                    domain,
                    codomain,
                },
                Produced::Checked,
            ) => {
                let read = self.context.whnf_value_type(domain)?;
                if let ValueTypeView::StaticPi { .. } = value_type_view(self.context.arena(), read)?
                {
                    self.rigid_operator(argument)?;
                }
                let applied = self.applied(argument, codomain)?;
                let applied = match head {
                    Some(head) => {
                        crate::recursion::followed(self.context, (head, argument), applied)?
                    },
                    None => applied,
                };
                Ok(Step::Ascend(Produced::CompType(applied)))
            },
            (Frame::LambdaBody | Frame::FormBinder | Frame::BindBody { .. }, Produced::Checked) => {
                self.close()?;
                Ok(Step::Ascend(Produced::Checked))
            },
            (
                Frame::BindBound {
                    at,
                    bound,
                    body,
                    direction,
                },
                Produced::CompType(synthesised),
            ) => {
                let read = crate::codata::read(self.context, synthesised)?;
                let result = match matched_returner(self.context.arena_mut(), read) {
                    Maybe::Present(result) => result,
                    Maybe::Absent(absent) => {
                        return Err(unmatched(
                            absent,
                            TypeNode::Computation(read),
                            CheckRefusal::ShapeMismatch {
                                at: TermNode::Computation(bound),
                                wanted: ExpectedShape::Returner,
                                found: TypeNode::Computation(synthesised),
                            },
                        ));
                    },
                };
                let direction = match direction {
                    Direction::Synthesise => Direction::Synthesise,
                    Direction::Check(expected) => {
                        let accumulated = self.accumulate_effects(at, read, expected)?;
                        if accumulated != expected {
                            comp_bridge(
                                self.context,
                                at,
                                accumulated,
                                expected,
                                &mut self.conversions,
                            )?;
                        }
                        let arena = self.context.arena_mut();
                        Direction::Check(
                            shift_comp_type(arena, expected, Binders::from(1_u32)).settle(arena),
                        )
                    },
                };
                self.context.binders().open(Zone::Intuitionistic, result);
                self.context.open_copy(at);
                self.wait(Frame::BindBody { at, bound: read });
                Ok(Step::Descend(Goal::Computation {
                    term: body,
                    direction,
                }))
            },
            (Frame::BindBody { at, bound }, Produced::CompType(synthesised)) => {
                let Maybe::Present(lowered) =
                    strengthen_comp_type(self.context.arena_mut(), synthesised)
                else {
                    return Err(CheckRefusal::DependentBind { at, synthesised });
                };
                let lowered = lowered.settle(self.context.arena_mut());
                self.close()?;
                let lowered = self.accumulate_effects(at, bound, lowered)?;
                Ok(Step::Ascend(Produced::CompType(lowered)))
            },
            (Frame::ValueBridge { at, expected }, Produced::ValueType(synthesised)) => {
                value_bridge(
                    self.context,
                    at,
                    synthesised,
                    expected,
                    &mut self.conversions,
                )?;
                Ok(Step::Ascend(Produced::Checked))
            },
            (Frame::CompBridge { at, expected }, Produced::CompType(synthesised)) => {
                comp_bridge(
                    self.context,
                    at,
                    synthesised,
                    expected,
                    &mut self.conversions,
                )?;
                Ok(Step::Ascend(Produced::Checked))
            },
            (Frame::Quote(quoted), Produced::Checked) => {
                let quoted = self.quoted(quoted)?;
                Ok(Step::Ascend(Produced::ValueType(quoted.into())))
            },
            (Frame::FormNext(next), Produced::Checked) => Ok(Step::Descend(Goal::Form(next))),
            (Frame::FormUnder { domain, under }, Produced::Checked) => {
                self.context.binders().open(Zone::Intuitionistic, domain);
                self.wait(Frame::FormBinder);
                Ok(Step::Descend(Goal::Form(under)))
            },
            (Frame::FormLift(at), Produced::Checked) => {
                self.raises(at)?;
                Ok(Step::Ascend(Produced::Checked))
            },
            (Frame::FormElement(node), Produced::ValueType(synthesised)) => {
                let synthesised = synthesised.settle(self.context.arena_mut());
                self.decodes(node, synthesised)?;
                Ok(Step::Ascend(Produced::Checked))
            },
            (Frame::FormStaticPi(at), Produced::Checked) => {
                self.static_classifiers(at)?;
                Ok(Step::Ascend(Produced::Checked))
            },
            (Frame::PairSecond { second, expected }, Produced::Checked) => {
                Ok(Step::Descend(Goal::Value {
                    term: second,
                    direction: Direction::Check(expected),
                }))
            },
            (
                Frame::StaticSpine {
                    at,
                    position,
                    argument,
                    spine,
                },
                Produced::ValueType(synthesised),
            ) => {
                let synthesised = synthesised.settle(self.context.arena_mut());
                let head = self.context.whnf_value_type(synthesised)?;
                let (domain, codomain) = match matched_static_pi(self.context.arena_mut(), head) {
                    Maybe::Present(classifiers) => classifiers,
                    Maybe::Absent(absent) => {
                        return Err(unmatched(
                            absent,
                            TypeNode::Value(head),
                            CheckRefusal::FamilyArity {
                                at,
                                expected: StaticArity::from(u32::from(position)),
                                actual: spine,
                            },
                        ));
                    },
                };
                if let Value::StaticLambda(_) = *self.value(argument)? {
                    self.wait(Frame::StaticOperand { codomain });
                    return Ok(Step::Descend(Goal::Value {
                        term: argument,
                        direction: Direction::Check(domain),
                    }));
                }
                self.wait(Frame::StaticArgument {
                    argument,
                    position,
                    domain,
                    codomain,
                });
                Ok(Step::Descend(Goal::Value {
                    term: argument,
                    direction: Direction::Synthesise,
                }))
            },
            (
                Frame::StaticArgument {
                    argument,
                    position,
                    domain,
                    codomain,
                },
                Produced::ValueType(synthesised),
            ) => {
                let synthesised = synthesised.settle(self.context.arena_mut());
                value_bridge(
                    self.context,
                    argument,
                    synthesised,
                    domain,
                    &mut self.conversions,
                )
                .map_err(|refusal| match refusal {
                    CheckRefusal::TypeMismatch(_)
                    | CheckRefusal::SortMismatch { .. }
                    | CheckRefusal::LevelMismatch { .. } => {
                        CheckRefusal::FamilyArgumentClassifier {
                            at: argument,
                            position,
                            synthesised,
                            expected: domain,
                        }
                    },
                    other @ (CheckRefusal::NotADataType(_)
                    | CheckRefusal::DataKindNotUniverse(_)
                    | CheckRefusal::DataFieldLevel { .. }
                    | CheckRefusal::RuleNotPresentable { .. }
                    | CheckRefusal::RuleNotRespected { .. }
                    | CheckRefusal::NotApart { .. }
                    | CheckRefusal::LoopNotRespected { .. }
                    | CheckRefusal::LoopUndecided { .. }
                    | CheckRefusal::AbstractKindNotUniverse(_)
                    | CheckRefusal::RepresentationAboveKind { .. }
                    | CheckRefusal::NotAnAbstractType(_)
                    | CheckRefusal::AtomTransport { .. }
                    | CheckRefusal::BridgeAtSealedType { .. }
                    | CheckRefusal::OutsideFold { .. }
                    | CheckRefusal::SealSiteRepeated(_)
                    | CheckRefusal::DataArgumentArity(_)
                    | CheckRefusal::UnknownConstructor { .. }
                    | CheckRefusal::ConstructorArity(_)
                    | CheckRefusal::NonExhaustiveDataCase(_)
                    | CheckRefusal::UndecidedCoverage(_)
                    | CheckRefusal::AbsentRecordField(_)
                    | CheckRefusal::AbsentTupleComponent(_)
                    | CheckRefusal::MissingRecordField { .. }
                    | CheckRefusal::UnknownOperation { .. }
                    | CheckRefusal::HandlerCoverage { .. }
                    | CheckRefusal::HandlerUnlawful { .. }
                    | CheckRefusal::ShiftWithoutReset { .. }
                    | CheckRefusal::DependentStack { .. }
                    | CheckRefusal::PathCode(_)
                    | CheckRefusal::EndpointMismatch { .. }
                    | CheckRefusal::CompoundEndpoint { .. }
                    | CheckRefusal::FunextUnsupported { .. }
                    | CheckRefusal::PointwiseDistinct { .. }
                    | CheckRefusal::EquivUnsupported { .. }
                    | CheckRefusal::UncertifiedStratum { .. }
                    | CheckRefusal::RoundTripDistinct { .. }
                    | CheckRefusal::NotOver { .. }
                    | CheckRefusal::UaUncertified { .. }
                    | CheckRefusal::UaInequivalent { .. }
                    | CheckRefusal::EffectSignatureConflict { .. }
                    | CheckRefusal::ShapeMismatch { .. }
                    | CheckRefusal::NotSynthesisable { .. }
                    | CheckRefusal::UnknownConstant { .. }
                    | CheckRefusal::OutOfFragment { .. }
                    | CheckRefusal::UnboundIndex { .. }
                    | CheckRefusal::BudgetExceeded { .. }
                    | CheckRefusal::DanglingNode { .. }
                    | CheckRefusal::AdmissionOrder { .. }
                    | CheckRefusal::MachineInvariant
                    | CheckRefusal::DependentBind { .. }
                    | CheckRefusal::Undecided { .. }
                    | CheckRefusal::FamilyArity { .. }
                    | CheckRefusal::FamilyArgumentClassifier { .. }
                    | CheckRefusal::StaticLambdaArgument { .. }
                    | CheckRefusal::StaticClassifierExpected { .. }
                    | CheckRefusal::NegativeOccurrence(_)
                    | CheckRefusal::NestedOccurrence(_)
                    | CheckRefusal::IndexOccurrence(_)
                    | CheckRefusal::NonUniformOccurrence(_)
                    | CheckRefusal::CrossBlockReference { .. }
                    | CheckRefusal::StageNotBelow { .. }
                    | CheckRefusal::StagesDisagree { .. }
                    | CheckRefusal::StageNotCarried { .. }
                    | CheckRefusal::SessionMismatch { .. }
                    | CheckRefusal::Linearity { .. }
                    | CheckRefusal::UnenclosedRun { .. }
                    | CheckRefusal::ImplicitUnsolved { .. }
                    | CheckRefusal::ModelUnanswered { .. }
                    | CheckRefusal::ModelAmbiguous { .. }
                    | CheckRefusal::TacticRefused { .. }
                    | CheckRefusal::CapabilityForged { .. }
                    | CheckRefusal::CapabilityAmplified(_)
                    | CheckRefusal::CapabilityOutsideAuthority { .. }
                    | CheckRefusal::CapabilityEscaped { .. }
                    | CheckRefusal::CapabilityConsumable(_)
                    | CheckRefusal::CapabilityUngranted { .. }
                    | CheckRefusal::FootprintsOverlap { .. }
                    | CheckRefusal::SessionNotEquivalent { .. }
                    | CheckRefusal::SessionNotSubtype { .. }
                    | CheckRefusal::SessionCodeExpected { .. }
                    | CheckRefusal::OpenSessionPayload { .. }
                    | CheckRefusal::UnassertedLaw { .. }
                    | CheckRefusal::NonCovariantMotive { .. }
                    | CheckRefusal::RideUnsupported { .. }
                    | CheckRefusal::RunNotAdmitted { .. }
                    | CheckRefusal::DialogueUnmatched { .. }
                    | CheckRefusal::DialogueInverted { .. }
                    | CheckRefusal::ForwardUnsupported { .. }
                    | CheckRefusal::Boundary { .. }
                    | CheckRefusal::Access { .. }
                    | CheckRefusal::Codata { .. }
                    | CheckRefusal::Located { .. }) => other,
                })?;
                Ok(Step::Ascend(Produced::ValueType(codomain.into())))
            },
            (Frame::StaticOperand { codomain }, Produced::Checked) => {
                Ok(Step::Ascend(Produced::ValueType(codomain.into())))
            },
            (Frame::Unknowing(TermNode::Value(_)), Produced::Checked) => {
                let unknown = self.context.arena_mut().value_type_unknown();
                Ok(Step::Ascend(Produced::ValueType(unknown.into())))
            },
            (Frame::Unknowing(TermNode::Computation(_)), Produced::Checked) => {
                let unknown = self.context.arena_mut().comp_type_unknown();
                Ok(Step::Ascend(Produced::CompType(unknown)))
            },
            (Frame::SessionSend { endpoint, next, .. }, Produced::Checked) => {
                self.sent(endpoint, next)
            },
            (
                Frame::OfferArm {
                    at,
                    arm,
                    expected,
                    zones,
                },
                Produced::Checked,
            ) => self.armed(at, arm, expected, zones),
            (Frame::ForkProtocol { at, direction }, Produced::Checked) => {
                self.fork_formed(at, direction)
            },
            (
                Frame::ForkChild {
                    at,
                    direction,
                    session,
                },
                Produced::Checked,
            ) => self.forked(at, direction, session),
            (Frame::ReceiveBody { at, direction }, produced) => {
                self.received(at, direction, produced)
            },
            (Frame::ForkParent { at, direction }, produced) => self.joined(at, direction, produced),
            (Frame::HoldValue { at, direction }, Produced::ValueType(held)) => {
                let held = held.settle(self.context.arena_mut());
                self.held(at, direction, held)
            },
            (Frame::HoldBody { at, direction }, produced) => self.dropped(at, direction, produced),
            (Frame::AccessIndex { at, direction }, Produced::Checked) => self.placed(at, direction),
            (Frame::AccessBody { at, .. }, produced) => self.accessed(at, produced),
            (Frame::AccessUnwind { produced, .. }, Produced::Checked) => Ok(Step::Ascend(produced)),
            (Frame::ResumeValue { at, view }, Produced::Checked) => self.resumed(at, view),
            (Frame::WorldHold { .. }, Produced::ValueType(held)) => {
                let held = held.settle(self.context.arena_mut());
                self.held_here(held)
            },
            (Frame::LetaValue { at, direction }, Produced::ValueType(handle)) => {
                let handle = handle.settle(self.context.arena_mut());
                self.opened_at(at, direction, handle)
            },
            (Frame::LetaBody { at }, produced) => self.leta_closed(at, produced),
            (
                Frame::MigrateBody {
                    at,
                    from,
                    direction,
                },
                produced,
            ) => self.returned(at, from, direction, produced),
            (
                Frame::PathProductFirst { .. }
                | Frame::Resume { .. }
                | Frame::Abandon { .. }
                | Frame::PathProductSecond { .. }
                | Frame::TransportPath { .. }
                | Frame::HereSynthesised { .. }
                | Frame::FunextLeft { .. }
                | Frame::EquivForward { .. }
                | Frame::UnivalenceRecord { .. }
                | Frame::ElementTransportPath { .. }
                | Frame::TelescopePath { .. }
                | Frame::TelescopeOver { .. }
                | Frame::CaseScrutinee { .. }
                | Frame::ListCaseScrutinee { .. }
                | Frame::FixpointArgument { .. }
                | Frame::SplitScrutinee { .. }
                | Frame::Force { .. }
                | Frame::Decompose { .. }
                | Frame::ValueBridge { .. }
                | Frame::FormElement(_)
                | Frame::StaticSpine { .. }
                | Frame::StaticArgument { .. }
                | Frame::ExerciseCapability { .. }
                | Frame::StaySynthesised { .. }
                | Frame::ThenFirst { .. }
                | Frame::ThenSecond { .. }
                | Frame::FlowProductFirst { .. }
                | Frame::FlowProductSecond { .. }
                | Frame::UpdateBase { .. }
                | Frame::UpdateOverlay { .. }
                | Frame::RideFlow { .. }
                | Frame::ForwardTranslator { .. }
                | Frame::ArrowDomain { .. }
                | Frame::ArrowCodomain { .. }
                | Frame::ArrowAgainst { .. }
                | Frame::HoldValue { .. }
                | Frame::WorldHold { .. }
                | Frame::LetaValue { .. },
                Produced::CompType(_) | Produced::Checked,
            )
            | (
                Frame::ApplicationHead { .. }
                | Frame::CompBridge { .. }
                | Frame::ReturnedEndpoint { .. }
                | Frame::Ran { .. }
                | Frame::NestedCall { .. }
                | Frame::BindBound { .. }
                | Frame::Project { .. }
                | Frame::HandlerSubject { .. }
                | Frame::StackNext { .. }
                | Frame::StackBind { .. },
                Produced::ValueType(_) | Produced::Checked,
            )
            | (
                Frame::PathBackward { .. }
                | Frame::Ascription { .. }
                | Frame::PerformPayload { .. }
                | Frame::Next(_)
                | Frame::Reset { .. }
                | Frame::HandlerForm { .. }
                | Frame::HandlerReturn { .. }
                | Frame::HandlerClause { .. }
                | Frame::ScopeForm { .. }
                | Frame::ScopeSubject { .. }
                | Frame::PathChecked { .. }
                | Frame::PrimitiveSecond { .. }
                | Frame::PrimitiveResult { .. }
                | Frame::ListFold { .. }
                | Frame::TransportOperand { .. }
                | Frame::HereEndpoints { .. }
                | Frame::FunextRight { .. }
                | Frame::EquivBackward { .. }
                | Frame::UaTranslators { .. }
                | Frame::UnivalenceChecked { .. }
                | Frame::ElementTransportMotive { .. }
                | Frame::TelescopeMotive { .. }
                | Frame::TelescopeStart { .. }
                | Frame::CaseBranch { .. }
                | Frame::ArmEnded { .. }
                | Frame::ArmsJoined { .. }
                | Frame::ListCaseNil { .. }
                | Frame::ListCaseCons
                | Frame::ApplicationArgument { .. }
                | Frame::LambdaBody
                | Frame::FormBinder
                | Frame::Quote(_)
                | Frame::FormNext(_)
                | Frame::FormUnder { .. }
                | Frame::FormLift(_)
                | Frame::FormStaticPi(_)
                | Frame::RunProtocol
                | Frame::PairSecond { .. }
                | Frame::StaticOperand { .. }
                | Frame::Unknowing(_)
                | Frame::ThunkBody
                | Frame::InjectionPayload
                | Frame::Spliced { .. }
                | Frame::SessionSend { .. }
                | Frame::OfferArm { .. }
                | Frame::ForkProtocol { .. }
                | Frame::ForkChild { .. }
                | Frame::SessionStatement { .. }
                | Frame::SessionPayloads { .. }
                | Frame::RideMotive { .. }
                | Frame::RideValue { .. }
                | Frame::StayEndpoints { .. }
                | Frame::AccessUnwind { .. }
                | Frame::AccessIndex { .. }
                | Frame::ResumeValue { .. },
                Produced::ValueType(_) | Produced::CompType(_),
            )
            | (
                Frame::NativeNext(_)
                | Frame::NativeYield(_)
                | Frame::NativeCollect
                | Frame::NativeDiscard
                | Frame::NativeTuple { .. }
                | Frame::NativeRecord { .. }
                | Frame::NativeCase(_)
                | Frame::NativeMotive { .. }
                | Frame::NativeRespect { .. }
                | Frame::NativeLoops { .. }
                | Frame::NativeForesee(_)
                | Frame::NativeForget(_)
                | Frame::SigmaSplitScrutinee(_)
                | Frame::SigmaSplitMotive { .. }
                | Frame::NativeProjection(_),
                _,
            )
            | (Frame::BindBody { .. } | Frame::SplitBody { .. }, Produced::ValueType(_))
            | (Frame::ReturnValue, Produced::CompType(_)) => Err(CheckRefusal::MachineInvariant),
        }
    }
    /// Open one binder per component of the split `at`'s scrutinee, whose
    /// classifier is `classifier`, and judge its body in `direction`.
    ///
    /// # Specification
    /// - requires: `at` is a split of `scrutinee`, and `classifier` its
    ///   synthesised type.
    /// - ensures: one binder per component is open, component zero outermost,
    ///   each typed by its component shifted past the binders before it, and
    ///   the body is the next goal, synthesised, or checked against the
    ///   expected type shifted past all of them; a split of no components
    ///   checks its body against the expected type itself.
    /// - fails: [`CheckRefusal::ShapeMismatch`] at the scrutinee, wanting a
    ///   product, for a classifier that is no product or a product of another
    ///   arity; the unfolding's refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`CheckRefusal`] — as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a split reading each of three components, a split of
    ///   the unit, a split of another arity and a split of a non-product
    ///   separate the binder order, the shift and both refusals; a split
    ///   synthesising its body's type, and one whose body's type mentions a
    ///   component, separate the strengthening past the binders from its
    ///   refusal.
    /// - witness: `judgement::tests::a_split_binds_every_component_of_its_product`
    /// - witness: `judgement::tests::a_split_synthesises_its_body_type_outside_its_binders`
    #[spec(
        captures: before = usize::from(self.context.depth(Zone::Intuitionistic)),
        ensures: |ret| ret.is_err() || (matches!(ret, Ok(Step::Descend(Goal::Computation { direction: judged, .. }))
                if matches!((direction, judged), (Direction::Synthesise, Direction::Synthesise) | (Direction::Check(_), Direction::Check(_))))
            && self.context.arena().computation(at).is_some_and(|node| matches!(*node,
                Computation::Split { arity, .. } if usize::from(self.context.depth(Zone::Intuitionistic)) == before.saturating_add(usize::from(arity))))),
    )]
    fn split(
        &mut self,
        at: ComputationId,
        scrutinee: ValueId,
        classifier: ValueTypeId,
        direction: Direction<CompTypeId>,
    ) -> Result<Step, CheckRefusal>
    {
        let Some(&Computation::Split { arity, body, .. }) = self.context.arena().computation(at)
        else {
            return Err(CheckRefusal::MachineInvariant);
        };
        let components = self.product_expected(scrutinee, classifier)?;
        let count = usize::from(arity);
        if matches!(components, Components::Known(ref parts) if parts.len() != count) {
            return Err(CheckRefusal::ShapeMismatch {
                at: TermNode::Value(scrutinee),
                wanted: ExpectedShape::Product,
                found: TypeNode::Value(classifier),
            });
        }
        let binders = u32::try_from(count).map_err(|_overflow| CheckRefusal::MachineInvariant)?;
        let judged = match direction {
            Direction::Synthesise => Direction::Synthesise,
            Direction::Check(expected) => {
                let arena = self.context.arena_mut();
                Direction::Check(
                    shift_comp_type(arena, expected, Binders::from(binders)).settle(arena),
                )
            },
        };
        for (index, shift) in (0_u32 .. binders).enumerate() {
            let component = match components {
                Components::Known(ref parts) => {
                    *parts.get(index).ok_or(CheckRefusal::MachineInvariant)?
                },
                Components::Unknown(unknown) => unknown,
            };
            let component =
                shift_value_type(self.context.arena_mut(), component, Binders::from(shift))
                    .settle(self.context.arena_mut());
            self.context.binders().open(Zone::Intuitionistic, component);
        }
        self.wait(Frame::SplitBody { at, arity });
        Ok(Step::Descend(Goal::Computation {
            term: body,
            direction: judged,
        }))
    }

    /// Read the two decoded endpoints of a native path classifier.
    ///
    /// # Specification
    /// - requires: nothing; a non-path classifier is refused.
    /// - ensures: both endpoints are closed first-order value types.
    /// - provides: source and target types in classifier order.
    /// - fails: a shape mismatch or an unsupported path code.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — native endpoint codes remain ordered and in the
    ///   first-order fragment; mismatched classifiers report their original
    ///   site.
    /// - witness: `bridge::tests::native_path_module_round_trips`
    /// - witness: `judgement::tests::each_former_refuses_a_classifier_of_another_shape_by_name`
    #[spec(ensures: |ret| match ret {
        Ok(pair) => <[ValueTypeId; 2]>::from(pair).iter().all(|&id| matches!(self.context.arena().value_type(id), Some(&(gandr_core_term::ValueType::Base(_) | gandr_core_term::ValueType::Product(_) | gandr_core_term::ValueType::Sum(_))))),
        Err(CheckRefusal::ShapeMismatch { at: found_at, wanted, found }) => found_at == TermNode::Value(at) && wanted == ExpectedShape::PathUniverse && found == TypeNode::Value(classifier),
        Err(_) => true,
    })]
    fn path_endpoints(
        &mut self,
        at: ValueId,
        classifier: ValueTypeId,
    ) -> Result<(ValueTypeId, ValueTypeId), CheckRefusal>
    {
        let head = self.context.whnf_value_type(classifier)?;
        let ValueTypeView::PathUniverse(source, target) =
            value_type_view(self.context.arena(), head)?
        else {
            return Err(CheckRefusal::ShapeMismatch {
                at: TermNode::Value(at),
                wanted: ExpectedShape::PathUniverse,
                found: TypeNode::Value(classifier),
            });
        };
        Ok((
            crate::formation::path_code(self.context.arena(), source)?,
            crate::formation::path_code(self.context.arena(), target)?,
        ))
    }

    /// Read the type a reflexivity `here(a)` is checked at: a bridge at an
    /// atom stating an interface as the bridge it is, any other as
    /// [`Self::path_expected`] reads it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the carrier and both endpoints of a bridge whose carrier's
    ///   weak head is an atom stating an interface: the interface's
    ///   reflexivity, checked where the atom was admitted, is the evidence a
    ///   bridge at the atom from a point to itself has; otherwise
    ///   [`Self::path_expected`] of `classifier`.
    /// - provides: what reflexivity is checked against.
    /// - fails: as [`Self::path_expected`].
    /// - panics: none.
    ///
    /// # Errors
    /// - [`CheckRefusal`] — as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `here` checks at a bridge at an interfaced atom from
    ///   a point to itself and is refused at a bridge at the universe by shape,
    ///   in both checkers.
    /// - witness: `bridge::tests::bridges::an_interfaced_atom_bears_its_relation_as_its_bridge_in_both_checkers`
    /// - witness: `bridge::tests::bridges::a_bridge_at_the_universe_is_a_relation_in_both_checkers`
    #[spec(ensures: |ret| match ret {
        | Err(CheckRefusal::ShapeMismatch { at: site, wanted, found }) => site == at && wanted == ExpectedShape::Path && found == TypeNode::Value(classifier),
        | Ok(PathReading::Known { .. } | PathReading::Unknown(_)) | Err(_) => true,
    })]
    fn reflexive_expected(
        &mut self,
        at: TermNode,
        classifier: ValueTypeId,
    ) -> Result<PathReading, CheckRefusal>
    {
        let head = self.context.whnf_value_type(classifier)?;
        if let ValueTypeView::Bridge {
            carrier,
            left,
            right,
        } = value_type_view(self.context.arena(), head)?
            && let domain = self.context.whnf_value_type(carrier)?
            && let ValueTypeView::Abstract(atom) = value_type_view(self.context.arena(), domain)?
            && self.context.interface_of(atom).is_some()
        {
            return Ok(PathReading::Known {
                carrier,
                left,
                right,
            });
        }
        self.path_expected(at, classifier)
    }

    /// Read the element path type `classifier` names at its weak head.
    ///
    /// # Specification
    /// - requires: nothing; a classifier of another former is refused.
    /// - ensures: the carrier and both endpoints of a path type; the unknown
    ///   type, standing for a path type of unknown parts, as itself.
    /// - provides: what reflexivity is checked against and what a transported
    ///   path's type is read as.
    /// - fails: [`CheckRefusal::ShapeMismatch`] at `at`, wanting a path type,
    ///   for any other former; the unfolding's refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`CheckRefusal`] — as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — reflexivity against a path type, the unknown type and
    ///   an atom separates the three readings.
    /// - witness: `judgement::tests::reflexivity_checks_by_endpoint_conversion`
    /// - witness: `judgement::tests::each_former_refuses_a_classifier_of_another_shape_by_name`
    #[spec(ensures: |ret| match ret {
        | Err(CheckRefusal::ShapeMismatch { at: site, wanted, found }) => site == at && wanted == ExpectedShape::Path && found == TypeNode::Value(classifier),
        | Ok(PathReading::Known { .. } | PathReading::Unknown(_)) | Err(_) => true,
    })]
    fn path_expected(
        &mut self,
        at: TermNode,
        classifier: ValueTypeId,
    ) -> Result<PathReading, CheckRefusal>
    {
        let head = self.context.whnf_value_type(classifier)?;
        match value_type_view(self.context.arena(), head)? {
            ValueTypeView::Path {
                carrier,
                left,
                right,
            } => Ok(PathReading::Known {
                carrier,
                left,
                right,
            }),
            ValueTypeView::Unknown => Ok(PathReading::Unknown(head)),
            ValueTypeView::Data { .. }
            | ValueTypeView::Record(_)
            | ValueTypeView::Stack { .. }
            | ValueTypeView::PathUniverse(..)
            | ValueTypeView::Bridge { .. }
            | ValueTypeView::Flow { .. }
            | ValueTypeView::Run(_)
            | ValueTypeView::Prefix(_)
            | ValueTypeView::Dialogue(_)
            | ValueTypeView::Web
            | ValueTypeView::Sum(_)
            | ValueTypeView::List(_)
            | ValueTypeView::Integer
            | ValueTypeView::String
            | ValueTypeView::Character
            | ValueTypeView::Float64
            | ValueTypeView::Fixed(_)
            | ValueTypeView::Unit
            | ValueTypeView::Thunk(_)
            | ValueTypeView::Universe { .. }
            | ValueTypeView::Lift { .. }
            | ValueTypeView::Element { .. }
            | ValueTypeView::Product(_)
            | ValueTypeView::StaticPi { .. }
            | ValueTypeView::Sigma { .. }
            | ValueTypeView::Abstract(_)
            | ValueTypeView::Staged { .. }
            | ValueTypeView::Kept { .. }
            | ValueTypeView::Capability { .. }
            | ValueTypeView::Buffer
            | ValueTypeView::Row
            | ValueTypeView::RowTail(_)
            | ValueTypeView::Session(_)
            | ValueTypeView::World(_) => Err(CheckRefusal::ShapeMismatch {
                at,
                wanted: ExpectedShape::Path,
                found: TypeNode::Value(classifier),
            }),
        }
    }

    /// Read the type of the path a transport follows: a parameterless type of
    /// words as the path at its cells' point it is, any other type as
    /// [`Self::path_expected`] reads it.
    ///
    /// # Specification
    /// - requires: nothing; a classifier of another former is refused.
    /// - ensures: for a weak head `Data(words, [])` whose signature carries
    ///   free cells, `Path(S, pt, pt)`, `S` the cells' sort and `pt` their
    ///   point ([`crate::loops::point`]), the path type conversion identifies
    ///   the words with ([`CheckingContext::words`]); as
    ///   [`Self::path_expected`] otherwise.
    /// - provides: the reading a transport and a telescope transport give the
    ///   path they follow, so a word written where the path stands is followed
    ///   as the path it is.
    /// - fails: as [`Self::path_expected`]; as [`crate::loops::point`] for
    ///   cells whose point does not build.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`CheckRefusal`] — as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a composite along the empty word and an inverse along
    ///   the inverse letter's word, each written as a constructor of the words,
    ///   read the path at the circle's point and replay in the kernel; the
    ///   composite set against reflexivity is refused at its endpoints, where
    ///   reading the words as their own type would refuse by shape.
    /// - witness: `tests::native_formers::a_word_written_as_a_transport_path_is_that_path_in_both_checkers_397`
    #[spec(ensures: |ret| match ret {
        | Ok(PathReading::Known { carrier, left, right }) => self.context.arena().value_type(carrier).is_some()
            && self.context.arena().value(left).is_some()
            && self.context.arena().value(right).is_some(),
        | Ok(PathReading::Unknown(_)) | Err(_) => true,
    })]
    fn transported_path(
        &mut self,
        at: TermNode,
        classifier: ValueTypeId,
    ) -> Result<PathReading, CheckRefusal>
    {
        let head = self.context.whnf_value_type(classifier)?;
        let ValueTypeView::Data {
            declaration: words,
            arguments: &[],
        } = value_type_view(self.context.arena(), head)?
        else {
            return self.path_expected(at, classifier);
        };
        let signatures = self.context.data_signatures();
        let Some(sort) = signatures
            .get(&words)
            .and_then(|signature| signature.presentation().cells())
            .map(gandr_core_term::FreeCells::sort)
        else {
            return self.path_expected(at, classifier);
        };
        let arities: Vec<FieldCount> = signatures
            .get(&sort)
            .ok_or(CheckRefusal::MachineInvariant)?
            .constructors()
            .iter()
            .map(|fields| FieldCount::from(fields.len()))
            .collect();
        let carrier = self.context.arena_mut().value_type_data(sort, Vec::new());
        let point = crate::loops::point(self.context, (carrier, &arities), words)?;
        Ok(PathReading::Known {
            carrier,
            left: point,
            right: point,
        })
    }

    /// Read the motive of the telescope transport `at` as its three layers.
    ///
    /// # Specification
    /// - requires: nothing; a motive of another shape is refused.
    /// - ensures: the motive and its carrier `A`, family `B` and body `C`
    ///   exactly when it is `Π (y : A). Π (z : B). F C`.
    /// - provides: the one reading of a telescope motive the rule's frames
    ///   share.
    /// - fails: [`CheckRefusal::ShapeMismatch`] at `at`, wanting a telescope,
    ///   for any other motive; [`CheckRefusal::MachineInvariant`] when `at` is
    ///   no telescope transport; [`CheckRefusal::DanglingNode`] for an
    ///   unreadable node.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`CheckRefusal`] — as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a two-arrow motive reads as its layers and a
    ///   one-arrow motive is refused by its shape.
    /// - witness: `judgement::tests::a_telescope_transport_replays_its_substitution_law`
    /// - witness: `judgement::tests::a_one_entry_telescope_motive_is_a_shape_mismatch`
    #[spec(ensures: |ret| match ret {
        | Err(CheckRefusal::ShapeMismatch { at: site, wanted, .. }) => site == TermNode::Computation(at) && wanted == ExpectedShape::Telescope,
        | Ok(_) | Err(_) => true,
    })]
    fn telescope(
        &self,
        at: ComputationId,
    ) -> Result<(CompTypeId, TelescopeParts), CheckRefusal>
    {
        let Computation::TelescopeTransport { motive, .. } = *self.computation(at)?
        else {
            return Err(CheckRefusal::MachineInvariant);
        };
        let arena = self.context.arena();
        let shape = CheckRefusal::ShapeMismatch {
            at: TermNode::Computation(at),
            wanted: ExpectedShape::Telescope,
            found: TypeNode::Computation(motive),
        };
        let Some(&CompType::Pi {
            domain: carrier,
            codomain,
        }) = arena.comp_type(motive)
        else {
            return Err(shape);
        };
        let Some(&CompType::Pi {
            domain: family,
            codomain: innermost,
        }) = arena.comp_type(codomain)
        else {
            return Err(shape);
        };
        let Some(&CompType::Returner { result: body, .. }) = arena.comp_type(innermost)
        else {
            return Err(shape);
        };
        Ok((motive, TelescopeParts {
            carrier,
            family,
            body,
        }))
    }

    /// Meet reflexivity's point with both endpoints of the path type it is
    /// checked against, recording the dialogue relating it to each.
    ///
    /// # Specification
    /// - requires: `point` checked against the path type's carrier, and the
    ///   three values stand under the judgement's binders.
    /// - ensures: success exactly when the point converts to the left endpoint
    ///   and to the right one: the same node or the same syntax at once, a hole
    ///   or a mark consistently with anything, a metavariable among them posed
    ///   to the solver against the other side and refuted only when the solver
    ///   refutes it, each with the empty dialogue; a pair mentioning no
    ///   variable that the context's tier meets
    ///   ([`CheckingContext::decide_closed_on`]), with the one decision
    ///   `Evaluate`; and otherwise by the normaliser's conversion with every
    ///   definition admitted so far unfolding, returned endpoints held and an
    ///   unread call of a binder whose calls return
    ///   ([`crate::divergence::returning`]) discarded
    ///   ([`crate::code::CodeDefinitions::relation`]), with the trace it
    ///   recorded. A conversion that waits for a fill
    ///   ([`CheckingContext::awaits_fill`]) holds with the empty dialogue: the
    ///   run that judges the filled body meets the pair again. On success the
    ///   context records the two dialogues at `at`.
    /// - provides: the endpoint condition of reflexivity's rule, and the
    ///   dialogues the kernel replays for it.
    /// - fails: [`CheckRefusal::EndpointMismatch`] naming `at` and both
    ///   endpoints when either conversion is refuted, declined without waiting
    ///   for a fill, or undecided, at the first endpoint that fails: its miss
    ///   is [`crate::EndpointMiss::Budget`] when the machine spent its step
    ///   budget, and [`crate::EndpointMiss::Unshown`] otherwise; a dangling
    ///   node or a machine invariant as the conversion raises it.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`CheckRefusal`] — as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — reflexivity at equal literals, at a definition
    ///   applied to a variable against what it unfolds to, and at an arithmetic
    ///   redex over a variable against the variable separate the syntactic, the
    ///   normalising and the refuting outcomes; the recorded dialogues cross to
    ///   the kernel and replay there. Endpoints calling a definition over an
    ///   omitted model are met once the model is resolved, and refused when the
    ///   filled endpoints are apart.
    /// - witness: `judgement::tests::reflexivity_checks_by_endpoint_conversion`
    /// - witness: `judgement::tests::a_closed_pair_the_tier_meets_carries_its_evaluation_2282`
    /// - witness: `bridge::tests::a_reflexivity_crosses_with_the_dialogues_relating_its_endpoints`
    /// - witness: `judgement::tests::reflexivity_at_a_stuck_native_point_meets_it_by_syntax`
    /// - witness: `bridge::tests::an_endpoint_over_an_omitted_model_waits_for_its_resolution_2391`
    #[spec(ensures: |ret| match ret {
        | Err(CheckRefusal::EndpointMismatch { at: site, left: named_left, right: named_right, .. }) => site == at && named_left == left && named_right == right,
        | Ok(()) => self.context.reflexivities().contains_key(&at),
        | Err(_) => true,
    })]
    fn reaches(
        &mut self,
        at: ValueId,
        point: ValueId,
        left: ValueId,
        right: ValueId,
    ) -> Result<(), CheckRefusal>
    {
        let mut dialogues = [Vec::new(), Vec::new()];
        let mut returning = None;
        for (endpoint, dialogue) in [left, right].into_iter().zip(&mut dialogues) {
            let arena = self.context.arena();
            let syntactic = point == endpoint
                || gandr_core_term::equal_certificate_syntax(arena, point, endpoint)
                    == gandr_core_term::CertificateEquality::Equal;
            if syntactic {
                continue;
            }
            let open = [point, endpoint]
                .into_iter()
                .any(|side| matches!(arena.value(side), Some(Value::Hole(_) | Value::Mark { .. })));
            if open {
                if self.context.unify_values(point, endpoint)?
                    == crate::elaboration::Unified::Refuted
                {
                    return Err(CheckRefusal::EndpointMismatch {
                        at,
                        left,
                        right,
                        miss: crate::EndpointMiss::Unshown,
                    });
                }
                continue;
            }
            if self.context.meet_closed(point, endpoint) == crate::tier::Meeting::Met {
                *dialogue =
                    Vec::from([gandr_kernel_conversion_trace::ConversionDecision::Evaluate]);
                continue;
            }
            if returning.is_none() {
                returning = Some(crate::divergence::returning(self.context)?);
            }
            match self.context.definitions().relation(
                self.context.arena(),
                point,
                endpoint,
                returning.as_deref().unwrap_or_default(),
            ) {
                Ok((gandr_core_nbe::MachineVerdict::Convertible, decisions)) => {
                    *dialogue = decisions;
                },
                // A side standing on a hole a later solution fills is the
                // fill's to decide: the run that judges the filled body meets
                // the pair again.
                Ok((verdict, _))
                    if self.context.awaits_fill(verdict) == crate::elaboration::Deferred::Yes => {},
                Ok((gandr_core_nbe::MachineVerdict::Declined(reason), _)) => {
                    return Err(CheckRefusal::EndpointMismatch {
                        at,
                        left,
                        right,
                        miss: crate::EndpointMiss::from(reason),
                    });
                },
                Ok((gandr_core_nbe::MachineVerdict::NotConvertible, _))
                | Err(CheckRefusal::Undecided { .. }) => {
                    return Err(CheckRefusal::EndpointMismatch {
                        at,
                        left,
                        right,
                        miss: crate::EndpointMiss::Unshown,
                    });
                },
                Err(fault) => return Err(fault),
            }
        }
        let [left_dialogue, right_dialogue] = dialogues;
        self.context.record_reflexivity(
            at,
            crate::code::Reflexivity::new(left_dialogue, right_dialogue),
        );
        Ok(())
    }

    /// Form the thunked translator from a closed source to a closed target.
    ///
    /// # Specification
    /// trivial.
    fn map_type(
        &mut self,
        source: ValueTypeId,
        target: ValueTypeId,
    ) -> ValueTypeId
    {
        let arena = self.context.arena_mut();
        let result = arena.comp_type_returner(target);
        let arrow = arena.comp_type_arrow(source, result);
        arena.value_type_thunk(arrow)
    }

    /// Read the summands used by injection and case checking.
    ///
    /// # Specification
    /// - requires: nothing; a non-sum classifier is refused.
    /// - ensures: the summands the classifier's weak head matches as a sum, any
    ///   number of them; one unknown type for every summand of the unknown
    ///   type.
    /// - provides: the summands in order.
    /// - fails: a shape mismatch when the weak head is not a sum.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — sum operands retain their classifiers and mismatch
    ///   refusals retain the source site instead of reporting a native-path
    ///   shape; an injection against the unknown type checks its payload.
    /// - witness: `bridge::tests::native_path_module_round_trips`
    /// - witness: `judgement::tests::an_introduction_against_the_unknown_type_checks_its_parts`
    #[spec(ensures: |ret| match ret {
        Ok(Components::Known(ref parts)) => parts.iter().all(|&part| self.context.arena().value_type(part).is_some()) && self.context.arena().value_type(classifier).is_none_or(|held| !matches!(*held, gandr_core_term::ValueType::Sum(ref held) if held != parts)),
        Ok(Components::Unknown(unknown)) => self.context.arena().value_type(unknown).is_some(),
        Err(CheckRefusal::ShapeMismatch { at: found_at, wanted, found }) => found_at == TermNode::Value(at) && wanted == ExpectedShape::Sum && found == TypeNode::Value(classifier),
        Err(_) => true,
    })]
    fn sum_expected(
        &mut self,
        at: ValueId,
        classifier: ValueTypeId,
    ) -> Result<Components, CheckRefusal>
    {
        let head = self.context.whnf_value_type(classifier)?;
        match matched_sum(self.context.arena_mut(), head) {
            Maybe::Present(summands) => Ok(summands),
            Maybe::Absent(absent) => Err(unmatched(
                absent,
                TypeNode::Value(head),
                CheckRefusal::ShapeMismatch {
                    at: TermNode::Value(at),
                    wanted: ExpectedShape::Sum,
                    found: TypeNode::Value(classifier),
                },
            )),
        }
    }

    /// Read the element classifier of a native List expectation.
    ///
    /// # Specification
    /// - ensures: the element type at a List weak head, or an unknown element
    ///   when the classifier is unknown; no sum is unfolded.
    /// - fails: shape mismatch or the existing weak-head refusal.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — nil, cons, invalid head and invalid tail distinguish
    ///   the native rule.
    /// - witness: `bridge::tests::native_lists_check_and_round_trip`
    /// - witness: `judgement::tests::an_introduction_against_the_unknown_type_checks_its_parts`
    /// - witness: `judgement::tests::each_former_refuses_a_classifier_of_another_shape_by_name`
    #[spec(ensures: |ret| ret.is_err() || ret.as_ref().is_ok_and(|&element| self.context.arena().value_type(element).is_some()))]
    fn list_expected(
        &mut self,
        at: ValueId,
        classifier: ValueTypeId,
    ) -> Result<ValueTypeId, CheckRefusal>
    {
        let head = self.context.whnf_value_type(classifier)?;
        match matched_list(self.context.arena_mut(), head) {
            Maybe::Present(element) => Ok(element),
            Maybe::Absent(absent) => Err(unmatched(
                absent,
                TypeNode::Value(head),
                CheckRefusal::ShapeMismatch {
                    at: TermNode::Value(at),
                    wanted: ExpectedShape::List,
                    found: TypeNode::Value(classifier),
                },
            )),
        }
    }

    /// Advance the pure List fold's formation and typing premises.
    ///
    /// # Specification
    /// - requires: the preceding premise succeeded.
    /// - ensures: nil is checked in the ambient context; cons binds head then
    ///   folded result, and completing cons closes both binders.
    /// - fails: malformed source, type mismatch or existing formation refusal.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a fold with distinct head and result classifiers
    ///   separates binder order and closure; malformed annotations are refused
    ///   before use.
    /// - witness: `bridge::tests::native_lists_check_and_round_trip`
    #[spec(captures: depth = usize::from(self.context.depth(Zone::Intuitionistic)),
        ensures: |ret| ret.is_err() || usize::from(self.context.depth(Zone::Intuitionistic)) == match phase {
            ListPhase::Nil => depth.saturating_add(2), ListPhase::Cons => depth.saturating_sub(2), ListPhase::Element | ListPhase::Result | ListPhase::Input => depth,
        })]
    fn list_fold(
        &mut self,
        at: ComputationId,
        classifier: CompTypeId,
        phase: ListPhase,
    ) -> Result<Step, CheckRefusal>
    {
        let Computation::ListFold {
            element,
            result,
            list,
            on_nil,
            on_cons,
        } = *self.computation(at)?
        else {
            return Err(CheckRefusal::MachineInvariant);
        };
        let (next, goal) = match phase {
            ListPhase::Element => (ListPhase::Result, Goal::Form(TypeNode::Value(result))),
            ListPhase::Result => {
                let expected = self.context.arena_mut().value_type_list(element);
                (ListPhase::Input, Goal::Value {
                    term: list,
                    direction: Direction::Check(expected),
                })
            },
            ListPhase::Input => (ListPhase::Nil, Goal::Computation {
                term: on_nil,
                direction: Direction::Check(classifier),
            }),
            ListPhase::Nil => {
                let result =
                    shift_value_type(self.context.arena_mut(), result, Binders::from(1_u32))
                        .settle(self.context.arena_mut());
                let expected =
                    shift_comp_type(self.context.arena_mut(), classifier, Binders::from(2_u32))
                        .settle(self.context.arena_mut());
                self.context.binders().open(Zone::Intuitionistic, element);
                self.context.binders().open(Zone::Intuitionistic, result);
                (ListPhase::Cons, Goal::Computation {
                    term: on_cons,
                    direction: Direction::Check(expected),
                })
            },
            ListPhase::Cons => {
                self.close()?;
                self.close()?;
                return Ok(Step::Ascend(Produced::CompType(classifier)));
            },
        };
        self.wait(Frame::ListFold {
            at,
            result: classifier,
            phase: next,
        });
        Ok(Step::Descend(goal))
    }
}

/// The refusal a matched-type operation's absence answers: `mismatch` for a
/// known former other than the one asked for, a dangling node for an id the
/// arena does not hold.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `mismatch` for [`matching::Absent::Mismatched`];
///   [`CheckRefusal::DanglingNode`] naming `node` for
///   [`matching::Absent::Dangling`].
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the two arms, separated by an introduction against the
///   wrong former, which answers the mismatch.
/// - witness: `judgement::tests::an_introduction_against_the_wrong_former_is_a_shape_mismatch`
#[spec(ensures: |ret| match absent {
    | matching::Absent::Mismatched => ret == mismatch,
    | matching::Absent::Dangling => ret == CheckRefusal::DanglingNode { node: CoreNode::Type(node) },
})]
fn unmatched(
    absent: matching::Absent,
    node: TypeNode,
    mismatch: CheckRefusal,
) -> CheckRefusal
{
    match absent {
        matching::Absent::Mismatched => mismatch,
        matching::Absent::Dangling => CheckRefusal::DanglingNode {
            node: CoreNode::Type(node),
        },
    }
}

/// The refusal of a value former the fragment has no rule for.
///
/// # Specification
/// trivial.
const fn unadmitted_value(
    term: ValueId,
    former: UnadmittedFormer,
) -> CheckRefusal
{
    CheckRefusal::OutOfFragment {
        at: CoreNode::Term(TermNode::Value(term)),
        former,
    }
}

#[cfg(test)]
mod tests;
