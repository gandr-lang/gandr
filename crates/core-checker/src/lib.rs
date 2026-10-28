//! **The core checking judgement**: four directed faces over the slice's
//! fragment of the core language, the name-free declaration input with its
//! origin token, the checking context wrapped around the core context, type
//! formation, the conversion module boundary with its declared projection,
//! the absence-only obligation ledger, the refusal vocabulary with its
//! classifier, a total elaboration that marks a refusal and goes on,
//! three-valued match coverage over patterns with holes, and the kernel
//! bridge that has the kernel re-derive every declaration the judgement
//! accepted.
//!
//! The crate reads core nodes a producer minted and answers, per declaration,
//! whether its body has its type. There is no surface here: no names, no
//! spans, no syntax. A declaration arrives as an admission position, two
//! halves each present or absent for a stated reason, and an opaque origin
//! token the verdict echoes back.
//!
//! # The decisions that interlock
//!
//! **The former decides the mode.** Leaves and eliminations synthesise,
//! introductions check, and a dispatch on the direction names both cases, so a
//! rule added in one mode and forgotten in the other does not compile.
//!
//! **Types meet in three places.** A synthesising value or computation in
//! checking position crosses one of two bridges into the conversion module,
//! and a decode's code crosses a third when formation checks it; no rule
//! compares types itself, and each crossing is counted in the result a face
//! returns.
//!
//! **A computation where a value is read runs or is suspended by the type
//! expected there.** Beside the lowering's three sort-directed bridges, the
//! fourth is the checker's, by three rules: against a thunk type a nested
//! computation is suspended and against any other type it runs, as it does
//! where no thunk can stand, a scrutinee or a transport's path; runs bind in
//! written order around the innermost enclosing computation, never out of a
//! thunk or a case arm; and the checker elaborates the accepted body, each
//! run a bind at the nested call's span, and judges the result again. With no
//! type expected anywhere else it is refused by name,
//! [`CheckRefusal::NotSynthesisable`] with [`CheckingForm::Nested`], and a run
//! no computation encloses is [`CheckRefusal::UnenclosedRun`]. The recorded
//! decision was that the
//! lowering inserts every bridge, which held while the checker answered
//! verdicts rather than terms; whether a nested computation runs is the
//! expected type's, which only the checker holds, so a verdict now carries
//! the elaborated body and [`ModuleReport::nested_elaborations`] reports each
//! [`Nesting`]. The `nested` module states the alternatives and the reversal.
//!
//! **A type has one classifier.** Formation runs in the judgement's machine
//! and answers each formed type's universe — its family's sort at its natural
//! level — and never asks a smallness question.
//!
//! **Smallness is a lift at the value bridge.** A value code checks at a
//! value universe at or above its own, and the crossing records the lift the
//! kernel bridge writes; nothing else moves a type up a universe.
//!
//! **A model stands at a model of a theory it includes by its reduct.** Where
//! two value types are apart and a reduct the module mints
//! ([`CheckingContext::keep_reducts`]) carries the one to the other, the value
//! bridge crosses by it and records the crossing at the value; the elaboration
//! applies the reduct there as a run, bound before its region as a nested
//! run is, so the run and the kernel read the application. Conversion itself
//! never relates the two types.
//!
//! **Holes come in two grains.** A declaration with no body under a declared
//! type absorbs it and owes it, and one with nothing to absorb is refused. A
//! hole written inside a body synthesises the unknown type and checks against
//! any, the unknown type is consistent with every type, and the kernel bridge
//! refuses a hole where it stands. A total elaboration marks every refusal
//! where it stands and goes on, so every incomplete program gets a type.
//!
//! **Only an absence is owed.** The ledger is built from absences, which only
//! the hole rule makes; a refusal cannot be spelled as an obligation, and the
//! classifier leaves its absence class empty.
//!
//! **A law is admitted on the host's word only where the host gives it.** A
//! declaration whose body is [`body::Absent::Hosted`] — a model's `law x
//! admitted` — is owed as a hole is, and admitted only when its declared type
//! converts with a law the host asserts of one of its primitives
//! ([`gandr_core_term::primitive::Primitive::laws`]): integer and string
//! equality are equivalences, float equality symmetric and transitive alone,
//! NaN equal to nothing. Any other admission is refused
//! [`CheckRefusal::UnassertedLaw`]. The match is by conversion, so a model
//! stating its equality through its own component, `a == b`, is admitted as
//! the primitive it unfolds to; a syntactic match at the lowering would refuse
//! it. A primitive whose laws the host comes to assert takes a row of the
//! table, and nothing else changes.
//!
//! **A judgement waiting on a hole is suspended, not refused.** A comparison
//! between the decode of an owed code and a constructor-headed type waits on
//! that code: the declaration that made it is [`Verdict::Suspended`], typed
//! but not defined, and [`ModuleReport::suspensions`] names the holes it
//! waits on. A refusal wins over a wait, and a reader of a waiting
//! declaration waits with it. The [`elaboration`] module states the fragment,
//! the term-producing run that fills a hole and resumes what waited, and the
//! alternatives.
//!
//! **One machine, no recursion.** Every face and formation run one explicit
//! machine of goals and frames, charged one step per transition against an
//! allowance.
//!
//! **The kernel re-derives.** [`bridge::readmit`] erases every accepted
//! declaration and offers it to the kernel's one checked entry: a body as a
//! definition, an owed hole as an axiom, a refused or suspended declaration
//! as nothing. A decode of a code constant is unfolded at export and the
//! kernel replays the normaliser's certificate for every unfolding before it
//! admits the declaration. The artifact's audit is empty exactly when the
//! ledger is, and gates nothing.
//!
//! **Sealing mints an atom.** An abstract type is a nominal declaration: its
//! kind is a value universe, its representation forms within it, and its
//! site — the ascription and the component, never a name — mints one atom in
//! the run's seal table. The atom reads as its representation for the
//! declarations its seal reaches and as itself past them, where it relates to
//! nothing but itself; the kernel admits the same declaration and seals it at
//! the same place.
//!
//! # Recursion
//!
//! A structural fixpoint is typed by stages. The rule:
//!
//! - **A fixpoint opens a stage.** `fix f. λy₀ … λyₙ. M`, staged at position
//!   `k`, checks `M` with `yₖ : A^ι` for a fresh stage `ι`, and binds `f` at
//!   the same telescope with that parameter at `A^{<ι}`.
//! - **A case opens one stage below its scrutinee's.** A case on a value at
//!   `A^s` mints one child `s' < s`, and every arm binds its recursive fields
//!   at `A^{s'}`.
//! - **A constructor stands above its fields.** A constructor checked at `A^s`
//!   owes each recursive field at `A^{<s}`; one with no recursive field owes a
//!   value in scope at a stage within `s`, so a nullary constructor never
//!   stands below the first stage.
//! - **Subsumption is the order.** `A^r` stands where `A^s` is wanted when the
//!   stage forest places `r` within `s`, and `A^s` stands where `A` is wanted;
//!   a thunked arrow is contravariant in its domain and covariant in its
//!   result, and every other position compares a stage as itself. A call whose
//!   argument does not stand below the stage is refused as
//!   [`CheckRefusal::StageNotBelow`], naming where the argument stood and the
//!   bound.
//! - **A field places its family where a stage reaches it.** A data
//!   declaration's field may hold its family, at its own parameters, under any
//!   placeable former — a thunk, an arrow's domain or codomain, a returner's
//!   result, a record, product, sum, list or Σ component, a `&` branch, or a
//!   strictly positive parameter of an earlier family. Under no function's
//!   domain the family is strictly positive; under one, its block is
//!   stratified, and a case puts that occurrence at `A^{s'}` with the recursive
//!   fields, so a function field takes the case's fields and never its
//!   scrutinee. A case on a stratified value at no stage reads it at a fresh
//!   root its scrutinee does not fit. Curry's consumer, `λb. case b of { MkBad
//!   f ↦ (force f) b }`, is refused as `StageNotBelow` at its call; an
//!   occurrence no stage reaches is refused by name in the `occurrence` module.
//! - **A type parameter instantiates at a staged code.** A call whose callee
//!   quantifies a type parameter `a`, handed the plain code `⌜T⌝`, instantiates
//!   `a` at `⌜T^s⌝` when the first later argument that is a variable stands at
//!   `T^s` where its parameter's type holds `a` — as `El a` itself, or as an
//!   argument of a data type, `D(…, a, …)` met by `D(…, ⌜T^s⌝, …)` — and `T`
//!   converts with the written code's type. `map ⌜Rose⌝ ⌜Nat⌝ s kids`, with
//!   `kids : List ⌜Rose^{s'}⌝` bound by a case, takes `s` at `Rose^{s'} → F
//!   Nat`; a list built around the scrutinee itself stands at no stage and
//!   keeps `map` at the plain `Rose`, where `s` refuses it. Only a variable
//!   drives the rule, and the first one that holds the parameter decides it: a
//!   staged code inside another code needs a signature quantified over stages.
//! - **A result follows the parameter it recurses on.** A structural definition
//!   whose arrows past the recursed-on `A` end in `F A` is judged a second time
//!   with that result at `A^ι` in its body and `A^{<ι}` at its self binder, a
//!   case checked there reading its written motive's result at the stage; when
//!   that holds, a call handed a variable at `A^s` in that position returns `F
//!   A^s`. `minus(p, d)`, `p` a field one stage below a fixpoint's, returns a
//!   natural the fixpoint's self binder takes. A definition with no recursion
//!   opens no stage, and its result follows nothing.
//!
//! The kernel re-derives every stage from the case structure, the evidence's
//! staged position and the same instantiation and following rules, and no
//! stage is carried on a node or crosses to the kernel: a stage in a term would
//! change node identity, which stays free of sizes. A staged type is a
//! classifier the judgement holds and erases to its plain code on the wire; a
//! staged type the bridge meets in a term is refused by name.
//!
//! **This is the solver-free fragment of sized types** (Barthe et al.'s
//! stage-based termination): every stage is minted by a fixpoint or a case and
//! read off where it was minted, none is chosen, and the order is a forest read
//! off the term with no variables, no `∞` and no successor arithmetic to solve.
//! Stage polymorphism, the solver and measures extend this core without a
//! second format.
//!
//! **No global check, ever.** The guarantee is per definition: a definition's
//! typing is self-contained, so its termination holds in every extension of
//! the program and survives every consumer and every package added later —
//! Guo, Hagens, Kop and Vale's *universal computability*, a function
//! computable in every extension of its system on computable arguments. A
//! trace condition over a whole program's call graph lacks it: adding a
//! definition can break a guarantee already given. Every later rung of the
//! recursion lane keeps this invariant.
//!
//! **Accessibility is the declaration rule**: Guermond and Nadathur's ground
//! stratification read through the accessible argument positions of Guo,
//! Hagens, Kop and Vale — a positive occurrence at or below the constructor's
//! stage, a negative one strictly below it. Curry's paradox is refused where
//! it is built, at its consumer, so a well-founded consumer of the same
//! family stands. A function field's domain sits at the case's stage `s'`,
//! not below it: the field takes the values the case put below its
//! scrutinee, the recursive fields among them, and the scrutinee itself
//! never fits.
//!
//! Six alternatives were weighed:
//!
//! - **The descent claim**, a syntactic walk over case fields that the kernel
//!   replayed, gave the same verdicts over the corpus but recursed on the last
//!   parameter only, refused an argument rebuilt below the stage and could not
//!   recurse through a function such as `map`. Its walks are deleted; the
//!   evidence byte it wrote is still read, as the stage typing at position 0.
//!   Reversal: none — the stage rule admits every program the claim did.
//! - **Carried stages**, a stage written on each call's argument type for the
//!   kernel to compare, would make a stage part of a node's identity and of its
//!   content key. Reversal: an instantiation the kernel cannot re-derive from
//!   the arguments it reads — a stage a solver chooses — which then crosses as
//!   a stage binder of the signature, never on a node.
//! - **A stage as a decoration**, a size beside an unstaged type that
//!   instantiation passes over, keeps `map`'s parameter at the plain `Rose` and
//!   refuses a size computed through `map`. Reversal: none — the classifier
//!   admits every program the decoration does.
//! - **Sizes now**, full sized types with stage variables, `∞` and a constraint
//!   solver, decide more than the corpus asks for and add a consistency gate.
//!   Reversal: the sized rung, once a program needs a stage quantified over (a
//!   helper typed at a stage) or a measure.
//! - **Positivity by position**, every occurrence under a domain refused at the
//!   declaration and every nested one refused as `NestedOccurrence`, turned
//!   away function fields a consumer applies only below the stage and a rose
//!   tree over `List`. Reversal: a family the stratified reading admits that a
//!   model of the stage order rejects.
//! - **Mendler-style abstraction**, each field over an abstract recursive type,
//!   admits the same families but makes every consumer take its own recursion
//!   as an argument. Reversal: a consumer whose termination the stage order
//!   cannot state.
//!
//! The rules where they are applied are in the `recursion` module.
//!
//! # Dependent transport
//!
//! A transport whose motive depends on the path's endpoint is the telescope
//! transport `tr₂(Π (y : A). Π (z : B). F C, p, z₀, q, v)`: `z₀` is the family
//! element at the path's source and `q` an identity over the path. The rule
//! synthesises `p` at `Path(A', a, b)` and requires `A'` to convert to `A`,
//! checks `z₀` at `B[a]`, synthesises `q` and requires it at `Path(B[b],
//! ⟨tr(y. B, p, z₀)⟩, z₁)`, refusing it as [`CheckRefusal::NotOver`] when it
//! does not convert, then checks `v` at `C[a, z₀]` and returns `C[b, z₁]`,
//! each instance outer binder first. A motive of another shape is a
//! [`CheckRefusal::ShapeMismatch`] wanting a telescope. The normaliser computes
//! exactly the kernel's clauses — `here` along both identities, `here(c)`
//! along the path into a one-binder transport along `q` in the fibre `z. C[c,
//! z]` — and stacks every other transport on its path's spine, comparing the
//! motive as a closed code; it never computes a clause the kernel's replay
//! lacks, so every acceptance re-derives. `J` is this transport in the
//! singleton, `tr₂(Π y. Π q : Path(A, a, y). F C, p, here(a), here(p), d)`,
//! not a rule of its own. The alternatives were a motive under two binders of
//! the one-binder transport, which changes what an exported node means, and a
//! primitive `J`. Reversal: a Σ type in the core makes this the one-binder
//! transport over the Σ of the two entries.
//!
//! # Binary sessions
//!
//! A fork binds its two endpoints into the linear zone, at a session type and
//! its dual; `send`, `recv`, `select`, `offer` and `close` advance an endpoint
//! along its protocol as frames of the one machine, and every way an endpoint
//! escapes its one use is refused by name: [`CheckRefusal::SessionMismatch`]
//! for an action its state does not admit, [`CheckRefusal::Linearity`] for an
//! endpoint left, reused, captured, sent or declared. Session types relate
//! through `gandr-core-session`'s engine. Readmission erases the discipline:
//! a session type crosses as the kernel's own session code, rooted at the
//! state it stands at, and an action as what it computes. The rules, the
//! frames and the decisions are in [`session`].
//!
//! # Temporary access
//!
//! `hold x = v; t` binds a value held exclusively into the linear zone, and
//! `access x as w { t } unwind { u }` lends it to a view for the body's
//! extent: the view is a one-shot accessor whose two eliminators are
//! `resume(w, v)`, which writes `v` back when the access ends, and
//! `abort(w)`, which runs the unwind under the empty row and writes nothing.
//! Every way a view or a held value breaks the discipline is refused by name
//! as [`CheckRefusal::Access`]. The rules, the frames, the decisions and what
//! later work may assume are in [`access`].
//!
//! # Located judgements
//!
//! A world declaration names a place, and every judgement stands at one:
//! `hold v` makes the handle `A at w` at the world it runs at, `leta x = v; t`
//! opens one there with `x` usable at the handle's world alone, and
//! `migrate [w] { t }` runs `t` at `w`, spending the consumable capability
//! `cap_w` the declaration's entry holds in the linear zone. A migration's
//! result comes back only when it crosses: mobile and open, decided on every
//! value-type former, a sealed abstract type crossing exactly when its
//! signature marks it `mobile`, and a thunk by its image — a closure is
//! mobile when every hypothesis it captures is, and open when every one is
//! open, read where it is formed. Every way a located judgement breaks is
//! refused by name as [`CheckRefusal::Located`]; located declarations stay on
//! the checker's side of the kernel. The rules, the crossing table, the
//! image's three axes, the entry and the decisions are in [`worlds`].
//!
//! # Session identity
//!
//! `bisim(A, B)` states that two session codes are bisimilar, at `Path(Type,
//! A, B)`, and `sim(A, B)` that the first is a Gay–Hole subtype of the
//! second, at the directed `Flow(Type, A, B)`; the session engine decides each
//! and the kernel replays the engine's pairs at `Path_U` and `Flow_U`, trusting
//! nothing the engine searched. `bisim(A, B, p)` relates two protocols whose
//! payload types differ, `p` a path for each pair of payload types that do
//! not convert. `Run(S)` classifies the finite recorded traces
//! the protocol's monitor accepts, and `ride(\X. Run(X), f, r)` moves a run
//! along a flow by the recorded-run consumer, refusing by move a run the
//! target does not admit. A consumer may take a protocol's receipts as its
//! runs, compatibility of two protocols as a `Flow` the kernel replays, and
//! their equivalence as a `Path`. The rules, the decisions and their
//! alternatives are in the `flow` module.
//!
//! # Forward flows
//!
//! `forward(f)` states that the closed translator `f : U (A → F B)` migrates
//! the first-order code `A` into `B`, at `Flow(Type, A, B)`: the judgement
//! runs `f` at every pattern of `A`'s coverage, checks each image
//! leaf-natural, and records the images with the machine's dialogues; the
//! kernel regenerates the coverage, checks naturality and replays every
//! dialogue, trusting nothing the judgement decided. `arrow(d, c)` is the
//! arrow's action on a domain flow running against it and a codomain flow
//! running with it; `stay`, `then` and `ride` introduce, compose and
//! eliminate every flow, `ride` under the covariance condition and the
//! directed computation table. Nothing reverses a flow: `back` along one is
//! the symmetry ride, refused by its motive. The rules, the decisions and
//! what a consumer may assume are in the `forward` and `flow` modules.
//!
//! # Example
//!
//! ```
//! use gandr_core_checker::CheckBudget;
//! use gandr_core_checker::CheckingContext;
//! use gandr_core_checker::Declaration;
//! use gandr_core_checker::OriginToken;
//! use gandr_core_checker::Verdict;
//! use gandr_core_checker::body;
//! use gandr_core_checker::bridge;
//! use gandr_core_checker::check_module;
//! use gandr_core_checker::signature;
//! use gandr_core_term::CoreArena;
//! use gandr_kernel_term::BaseType;
//! use gandr_kernel_term::ConstantIndex;
//! use gandr_kernel_term::IntegerLiteral;
//! use gandr_kernel_term::Literal;
//! use gandr_kernel_term::Magnitude;
//! use gandr_kernel_term::Sign;
//! use quenchant_shape::shape::Maybe;
//!
//! // def answer : Integer = 0 ; def owed : Integer ; def copy = answer ;
//! let mut arena = CoreArena::new();
//! let integer = arena.value_type_base(BaseType::Integer);
//! let zero = arena.value_literal(Literal::Integer(IntegerLiteral::new(
//!     Sign::NonNegative,
//!     Magnitude::zero(),
//! )));
//! let answer = arena.value_constant(ConstantIndex::from(0_usize));
//! let declarations = [
//!     Declaration::new(
//!         ConstantIndex::from(0_usize),
//!         Maybe::Present(integer),
//!         Maybe::Present(zero),
//!         OriginToken::from(0_usize),
//!     ),
//!     Declaration::new(
//!         ConstantIndex::from(1_usize),
//!         Maybe::Present(integer),
//!         Maybe::Absent(body::Absent::Hole),
//!         OriginToken::from(1_usize),
//!     ),
//!     Declaration::new(
//!         ConstantIndex::from(2_usize),
//!         Maybe::Absent(signature::Absent::Unsigned),
//!         Maybe::Present(answer),
//!         OriginToken::from(2_usize),
//!     ),
//! ];
//!
//! let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
//! let report = check_module(&mut context, &declarations);
//!
//! let [checked, owed, copied] = report.judged()
//! else {
//!     unreachable!("one verdict per declaration");
//! };
//! assert!(
//!     matches!(checked.verdict(), Verdict::Checked { .. }),
//!     "zero has type Integer"
//! );
//! assert!(
//!     matches!(owed.verdict(), Verdict::Owed(_)),
//!     "the hole owes its declared type"
//! );
//! assert!(
//!     matches!(copied.verdict(), Verdict::Synthesised { .. }),
//!     "a constant synthesises"
//! );
//! assert_eq!(
//!     usize::from(report.ledger().count()),
//!     1_usize,
//!     "one hole is owed"
//! );
//!
//! // The kernel defines the two bodies and assumes the hole.
//! let readmission = bridge::readmit(&mut arena, &report);
//! assert_eq!(
//!     readmission.environment().entries().len(),
//!     3_usize,
//!     "every declaration crossed"
//! );
//! assert_eq!(
//!     readmission.audit().axioms(),
//!     [ConstantIndex::from(1_usize)],
//!     "the artifact rests on the owed hole alone"
//! );
//! ```
//!
//! # Executable contracts
//!
//! Nontrivial operations carry executable `#[spec]` predicates and bounded
//! `# Adequacy` witnesses beside their implementation. The contracts of
//! [`check_value`] and [`bridge::readmit`] cover scope, budget, remapping and
//! publication; exemptions state the missing observation locally. Run the
//! predicates with:
//!
//! ```sh
//! RUSTFLAGS="--cfg anodized_panic" cargo test -p gandr-core-checker
//! ```
//!
//! # References
//!
//! - Paul Blain Levy. "Call-by-Push-Value: A Subsuming Paradigm." _Typed Lambda
//!   Calculi and Applications (TLCA 1999)_, LNCS 1581, Springer (1999). <https://doi.org/10.1007/3-540-48959-2_17>
//!   — the value and computation sorts, the thunk and returner shifts `U` and
//!   `F`, and the arrow as a computation type, which fix every rule's premises.
//! - Jana Dunfield and Neel Krishnaswami. "Bidirectional Typing." _ACM
//!   Computing Surveys_ 54(5) (2021). <https://doi.org/10.1145/3450952> — the
//!   discipline the rules follow: introductions check, eliminations synthesise,
//!   and the subsumption rule is the one place a synthesised type meets an
//!   expected one.
//! - Zanzi Mihejevs and Jules Hedges. "Canonical bidirectional typechecking."
//!   arXiv:2512.07511 (2025). <https://arxiv.org/abs/2512.07511> — the
//!   checkable/synthesisable split read as a polarity duality whose seams are
//!   the shifts, the background for confining type comparison to the change of
//!   direction.
//! - Cyrus Omar, Ian Voysey, Michael Hilton, Jonathan Aldrich and Matthew A.
//!   Hammer. "Hazelnut: A Bidirectionally Typed Structure Editor Calculus."
//!   _POPL 2017_. <https://doi.org/10.1145/3009837.3009900> — holes with the
//!   unknown type, consistency in place of equality around it, the matched-type
//!   operations, and mark erasure.
//! - Cyrus Omar, Ian Voysey, Ravi Chugh and Matthew A. Hammer. "Live Functional
//!   Programming with Typed Holes." _Proceedings of the ACM on Programming Languages_
//!   3 (POPL), 2019. <https://doi.org/10.1145/3290327> — evaluation around
//!   holes to indeterminate results, which `gandr-core-nbe` performs on the
//!   terms this judgement types.
//! - Yongwei Yuan et al. "Live Pattern Matching with Typed Holes." _Proceedings
//!   of the ACM on Programming Languages_ 7 (OOPSLA1), 2023. <https://doi.org/10.1145/3586048>
//!   — exhaustiveness and irredundancy decided only when every filling of the
//!   pattern holes agrees.
//! - Eric Zhao et al. "Total Type Error Localization and Recovery with Holes."
//!   _Proceedings of the ACM on Programming Languages_ 8 (POPL), 2024.
//!   <https://doi.org/10.1145/3632910> — the marked lambda calculus: every term
//!   elaborates, each error a mark where it stands.
//! - Luc Maranget. "Warnings for pattern matching." _Journal of Functional
//!   Programming_ 17(3) (2007). <https://doi.org/10.1017/S0956796807006223> —
//!   the usefulness relation both coverage questions reduce to.
//! - Pierre-Marie Pédrot and Nicolas Tabareau. "The Fire Triangle: How to Mix
//!   Substitution, Dependent Elimination, and Effects." _Proceedings of the ACM
//!   on Programming Languages_ 4 (POPL), 2020. `doi:10.1145/3371126` — ∂CBPV: a
//!   universe of value types and a universe of computation types, both
//!   classified in the value sort, dependency on values only, and the bind
//!   whose type may not mention its binder.
//! - Josselin Poiret, Gaëtan Gilbert, Kenji Maillard, Pierre-Marie Pédrot,
//!   Matthieu Sozeau, Nicolas Tabareau and Éric Tanter. "All Your Base Are
//!   Belong to Us: Sort Polymorphism for Proof Assistants." _Proceedings of the
//!   ACM on Programming Languages_ 9 (POPL), 2025. `doi:10.1145/3704912` — the
//!   sort carried apart from the level, so a universe names both and a sort
//!   parameter is a separate question this crate refuses by name.
//! - Nathanaëlle Courant and Xavier Leroy. "A Lazy, Concurrent Convertibility
//!   Checker." _Proceedings of the ACM on Programming Languages_ 10 (POPL),
//!   Article 53, January 2026. `doi:10.1145/3776695` — §9's trace of the
//!   checker's decisions rechecked sequentially, which is how every unfolding
//!   the judgement takes reaches the kernel.
//! - N. G. de Bruijn. "Lambda calculus notation with nameless dummies."
//!   _Indagationes Mathematicae_ 75(5) (1972).
//!   <https://doi.org/10.1016/1385-7258(72)90034-0> — the binder indices a
//!   variable is resolved by.
//! - Henk Barendregt and Freek Wiedijk. "The challenge of computer
//!   mathematics." _Philosophical Transactions of the Royal Society A_
//!   363(1835) (2005). <https://doi.org/10.1098/rsta.2005.1650> — the de Bruijn
//!   criterion: a result is trusted when a small independent checker re-derives
//!   it, the posture of the kernel bridge.
//! - Iosif Petrakis. "Univalent Typoids." 2022. `arXiv:2205.06651` — a
//!   univalence map as a typoid function: the two-cell obligation [`ua`] names.
//! - Michael Shulman. "Univalence for Inverse Diagrams and Homotopy
//!   Canonicity." _Mathematical Structures in Computer Science_ 25, 5 (2015).
//!   `doi:10.1017/S0960129514000565` — diagrams built degree by degree, the
//!   telescope [`ua`] derives `ua_n` through.
//! - Gilles Barthe, Maria João Frade, Eduardo Giménez, Luís Pinto and Tarmo
//!   Uustalu. "Type-based termination of recursive definitions." _Mathematical
//!   Structures in Computer Science_ 14(1) (2004).
//!   `doi:10.1017/S0960129503004122` — stages on inductive types, a fixpoint's
//!   recursive calls typed at a smaller stage, and subtyping by the stage
//!   order: the fragment [§ Recursion](#recursion) types without a solver.
//! - Liye Guo, Kasper Hagens, Cynthia Kop and Deivid Vale. "Higher-Order
//!   Constrained Dependency Pairs for (Universal) Computability." _49th
//!   International Symposium on Mathematical Foundations of Computer Science
//!   (MFCS 2024)_. `doi:10.4230/LIPIcs.MFCS.2024.57` — universal computability,
//!   the per-definition guarantee the recursion core keeps.
//!
//! Each decision, with the alternative it was chosen over and what would
//! reverse it, is stated in the documentation of the module it governs.

// Module documentation that predates the shape lint: 159 headings outside the
// vocabulary, 87 decision records, 11 issue references and 48 budgets exceeded.
// Each allow leaves with the rewrite that clears its count.
#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    allow(
        module_doc_heading,
        doc_decision_record,
        doc_issue_reference,
        module_doc_budget,
        reason = "module documentation that predates the shape lint"
    )
)]
#![no_std]

extern crate alloc;
// The profiler's instrumentation names `std`; it links only into the
// benchmark build.
#[cfg(feature = "hotpath")]
extern crate std;

pub mod access;
pub mod bridge;
mod capability;
pub mod codata;
mod code;
mod context;
mod conversion;
mod coverage;
mod declaration;
mod divergence;
pub mod elaboration;
pub mod eliminator;
mod equiv;
mod failure;
#[cfg(test)]
mod fixture;
mod flow;
mod formation;
mod former;
mod forward;
mod funext;
mod handler;
mod judgement;
mod ledger;
mod loops;
mod module;
mod nested;
mod occurrence;
mod product;
mod quantified;
mod recursion;
mod refusal;
mod regioned;
mod relatedness;
mod respect;
mod retire;
mod seal;
pub mod session;
mod solution;
pub mod stage;
pub mod staging;
mod support;
mod tactic;
pub mod template;
pub mod tier;
pub mod ua;
mod univalence;
mod view;
pub mod worlds;

pub use crate::capability::Grants;
pub use crate::capability::HostGrant;
pub use crate::code::Certificate;
pub use crate::code::CodeDefinitions;
pub use crate::code::Derivation;
pub use crate::code::EndpointRelation;
pub use crate::code::Evaluation;
pub use crate::code::Lift;
pub use crate::code::Reading;
pub use crate::code::Reflexivity;
pub use crate::code::Stalled;
pub use crate::code::Unfolded;
pub use crate::code::converted;
pub use crate::code::evaluated;
pub use crate::code::unfolding;
pub use crate::context::CheckBudget;
pub use crate::context::CheckingContext;
pub use crate::context::Checkpoint;
pub use crate::context::Formations;
pub use crate::context::data_scope;
pub use crate::context::signature_table;
pub use crate::conversion::ConversionCount;
pub use crate::coverage::Coverage;
pub use crate::coverage::CoverageFault;
pub use crate::coverage::Exhaustiveness;
pub use crate::coverage::Redundancy;
pub use crate::coverage::cover;
pub use crate::declaration::AbstractType;
pub use crate::declaration::AtomInterface;
pub use crate::declaration::Declaration;
pub use crate::declaration::DeclarationContent;
pub use crate::declaration::OriginToken;
pub use crate::declaration::body;
pub use crate::declaration::entry;
pub use crate::declaration::interface;
pub use crate::declaration::law;
pub use crate::declaration::signature;
pub use crate::equiv::Equivalence;
pub use crate::failure::Failure;
pub use crate::failure::FoldPremise;
pub use crate::failure::FrameRole;
pub use crate::failure::Obligation;
pub use crate::failure::Pursuit;
pub use crate::failure::Stage;
pub use crate::failure::judged;
pub use crate::flow::Statement;
pub use crate::formation::FormedCompType;
pub use crate::formation::FormedValueType;
pub use crate::formation::classify_comp_type;
pub use crate::formation::classify_value_type;
pub use crate::formation::form_comp_type;
pub use crate::formation::form_value_type;
pub use crate::formation::level_of;
pub use crate::forward::Directed;
pub use crate::forward::Forward;
pub use crate::funext::Funext;
pub use crate::funext::Step as FunextStep;
pub use crate::handler::Handled;
pub use crate::judgement::Checked;
pub use crate::judgement::Direction;
pub use crate::judgement::Elaboration;
pub use crate::judgement::Formed;
pub use crate::judgement::MarkEntry;
pub use crate::judgement::Synthesised;
pub use crate::judgement::Typing;
pub use crate::judgement::Typings;
pub use crate::judgement::check_comp;
pub use crate::judgement::check_value;
pub use crate::judgement::elaborate_comp;
pub use crate::judgement::elaborate_value;
pub use crate::judgement::synthesise_comp;
pub use crate::judgement::synthesise_value;
pub use crate::judgement::type_value;
pub use crate::ledger::Absence;
pub use crate::ledger::ObligationCount;
pub use crate::ledger::ObligationEntry;
pub use crate::ledger::ObligationLedger;
pub use crate::module::Judged;
pub use crate::module::ModuleReport;
pub use crate::module::ModuleRun;
pub use crate::module::TypedModule;
pub use crate::module::Verdict;
pub use crate::module::check_declaration;
pub use crate::module::check_declaration_supported;
pub use crate::module::check_module;
pub use crate::module::elaborated_report;
pub use crate::module::type_module;
pub use crate::module::unmarked;
pub use crate::nested::NestedElaboration;
pub use crate::nested::Nesting;
pub use crate::refusal::ArgumentPosition;
pub use crate::refusal::CheckRefusal;
pub use crate::refusal::CheckingForm;
pub use crate::refusal::Compared;
pub use crate::refusal::CoreNode;
pub use crate::refusal::EndpointMiss;
pub use crate::refusal::ExpectedShape;
pub use crate::refusal::Forced;
pub use crate::refusal::LoopRespect;
pub use crate::refusal::Mismatch;
pub use crate::refusal::RunFault;
pub use crate::refusal::RunStep;
pub use crate::refusal::StaticArity;
pub use crate::refusal::TacticFault;
pub use crate::refusal::TermNode;
pub use crate::refusal::TypeNode;
pub use crate::refusal::UnadmittedFormer;
pub use crate::refusal::Unsolved;
pub use crate::refusal::compared;
pub use crate::retire::Demand;
pub use crate::retire::Polled;
pub use crate::retire::Retirement;
pub use crate::retire::Unretired;
pub use crate::seal::ComponentOrdinal;
pub use crate::seal::SealError;
pub use crate::seal::SealId;
pub use crate::seal::SealSerial;
pub use crate::seal::SealSite;
pub use crate::seal::SealTable;
pub use crate::seal::SealingSite;
pub use crate::seal::minted_site;
pub use crate::support::CodataConsulted;
pub use crate::support::Consulted;
pub use crate::support::DataConsulted;
pub use crate::support::Support;
pub use crate::support::Supported;
