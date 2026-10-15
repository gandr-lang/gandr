//! The kernel's **checking machine, conversion, and admission choke point**,
//! with the check memo wired as the default path on both machines.
//!
//! The crate holds judgements. The representation, the sharing format and the
//! decode budgets belong to the term crate below it; the level algebra to the
//! strata crate; the memo's storage to the check-memo seam crate. What lives
//! here is what re-derives an obligation.
//!
//! # Four decisions that interlock
//!
//! **The checker is a defunctionalized machine** over a goal register, a
//! produced register, a heap frame stack and an explicit typing-context stack,
//! never mutually recursive methods bounded by a depth budget — so it is total
//! on adversarial depth, which decode can build from bytes. Its correspondence
//! table, arm by arm, is in [`check`], and it is the trusted-base audit
//! artifact a reviewer walks to confirm the machine *is* the judgement.
//!
//! **Conversion is structural comparison with an id-equality fast path**, and
//! the fast path is **positive only**: equal ids discharge a pair, unequal ids
//! decide nothing. That asymmetry is what keeps it sound while taking no table
//! into the trusted base.
//!
//! **Admission truncates on both verdicts.** The choke point keeps this
//! declaration's content and drops the checker's intermediates on success, and
//! drops both on rejection — clamped at the admission floor so a rollback can
//! never delete content a prior admission committed.
//!
//! **The memo is the default path on both machines.** Admitting one declaration
//! runs two iterative machines over the shared graph, and both consult it. A
//! memo covering only the term half would ship a small constant against an
//! exponential capability.
//!
//! # The memo's six binding conditions, and where each lives
//!
//! The seam crate names no term type, so everything that makes a memo *sound*
//! is a consumer obligation, and this crate is the consumer.
//!
//! | condition                                              | where it is discharged                                                                             |
//! | ------------------------------------------------------ | -------------------------------------------------------------------------------------------------- |
//! | static dispatch on a null-object seam that compiles away | [`check::check_declaration_with_memo`] is generic; every memo interaction is behind a compile-time activity constant |
//! | the public admission entry cannot reach the opt-in entry | [`env::Environment::add_decl`] takes no memo and builds its own; the memo-taking entry admits nothing and returns no receipt |
//! | a lifetime of one check call                            | [`check::check_declaration`] builds a memo and drops it; nothing stores one                        |
//! | the content-only key                                    | [`encoding`] and [`support`]: `(direction, obligation content, expected content, telescope content)`, arena-free |
//! | storage and policy outside the kernel crate             | the seam crate owns the table and its ordering; this crate holds a type parameter                  |
//! | no authority and no persistence in a hit                | a hit claims only that this process already computed this answer for this support                   |
//!
//! The key carries no arena id, so dangling ids are not why the memo lives for
//! one call. The lifetime rests on the two-wall discipline directly: a hit
//! claims only its own history, and no kernel-checked support discipline
//! exists. An outcome also carries arena ids even though the key does not, so
//! an entry outliving its arena would hand back a type that no longer
//! resolves.
//!
//! The verdict differential excludes operational refusal: with sound per-call
//! histories, the typing answers agree when neither run reaches
//! `CodeObligationCeiling`. That ceiling counts processed code obligations,
//! not distinct supports. A memo can suppress duplicates, so it can accept a
//! well-typed declaration that a memoless check refuses operationally. The
//! boundary witness checks the exact allowed count, one excess occurrence
//! under the null memo, and acceptance of the same shared above-limit
//! declaration under a fresh live memo. The alternative is a support-based
//! budget independent of memo policy; the occurrence budget is retained
//! because it directly bounds the drain loop. Reconsider it if callers need
//! policy-independent resource refusals.
//!
//! # The memo's collapse law
//!
//! [`ExpansionCensus`] counts goal expansions and memo recalls per plane, and
//! every measurement here is asserted through it. The self-similar composite
//! is `t_0 = ()`, `t_{k+1} = (t_k, t_k)` against `T_0 = Unit`,
//! `T_{k+1} = T_k × T_k`. Memoless is `4 · 2^d - 2` in total: `2^(d+1) - 1`
//! body checks against `2^(d+1) - 1` type formations. Memoized is `2d + 2`:
//! `d + 1` term supports against `d + 1` type supports. The unit leaf is the
//! empty tuple, which checks against the empty product in one goal.
//!
//! | depth | memoless total | memoless term | memoless type | memoized total | memoized term | memoized type |
//! | ----- | -------------- | ------------- | ------------- | -------------- | ------------- | ------------- |
//! | 8 | 1,022 | 511 | 511 | 18 | 9 | 9 |
//! | 12 | 16,382 | 8,191 | 8,191 | 26 | 13 | 13 |
//! | 16 | 262,142 | 131,071 | 131,071 | 34 | 17 | 17 |
//! | 28 | 1,073,741,822 | — | — | 58 | 29 | 29 |
//!
//! The depth-28 row runs at the public choke point: a definition whose tree
//! expansion is 1,073,741,822 goals admits checked through
//! [`Environment::add_decl`], with no bypass. Its memoized columns are
//! asserted through the opt-in entry on the same shape; its memoless columns
//! are the closed form's value and are never run.
//!
//! **Anti-vacuity.** The memoless term-plane law pins the occurrence count, so
//! the workload cannot stop being shared unnoticed. The memo's entry count is
//! compared against the census from the other direction, per plane and in
//! total. A separate case pins that the shared composite and its fully
//! unshared spelling cost the memoless checker identically: sharing buys
//! checking nothing without the memo.
//!
//! **Edit locality: `d + 1` node checks per depth-`d` edit,** within one
//! check call. Both spellings are checked in one pass, because warming a memo
//! on the original and reusing it across calls would measure exactly what the
//! lifetime rule forbids. Extra term-plane expansions are 9 at depth 8, 13 at
//! depth 12 and 17 at depth 16; the type plane adds nothing, because the edit
//! changes no type. The count is `d + 1` rather than `d + 2` because of the
//! content key: the edited leaf's freshly minted payload collapses with the
//! original's.
//!
//! **Adversarial depth.** A 20,000-link `thunk`-over-`return` chain checks
//! totally inside a 256 KiB stack at both memo instantiations, costing 40,001
//! term-plane expansions. The count is asserted, so the case cannot
//! degenerate into a shallow term and keep passing.
//!
//! **Poisoned entries.** Each case is a permanent suite member, in both
//! directions and on both planes, and asserts its exercised-path count
//! through the census:
//!
//! - a poisoned term entry turns a refusal into an acceptance (served once);
//! - an entry differing only in its binder component is not served (served zero
//!   times), with a positive control under the matching telescope that does
//!   change the verdict, so the case measures the binder component rather than
//!   an inert poison;
//! - a poisoned type-formation entry turns an admission into a
//!   universe-violation refusal (served once, on the type plane);
//! - a term-shaped answer in a type-formation support is declined and
//!   recomputed at exactly the cost of having had no entry, and the mirror case
//!   holds on the term plane.
//!
//! # Sharing and persistence
//!
//! No interning table of decoded values, no content-keyed memo the
//! *conversion* path consults, and no persistence. What a decode hands over is
//! the sharing the checker sees, and id equality is conversion's only
//! sharing-aware step. The one place the kernel creates sharing is the rewrite
//! memo, among nodes it minted past the admission watermark, and nothing
//! decides on that sharing. The kernel's own type conversion performs no
//! search, so it records no conversion trace; [`replay()`] is where the kernel
//! reads one, rechecking an untrusted engine's term-conversion verdict decision
//! by decision.
//!
//! # Sealing
//!
//! An abstract type carries the representation it was sealed over, and the
//! kernel reads that representation only inside the admission that minted
//! the atom: a sealed module's members are checked at the representation and
//! exported at the atom, and every later declaration sees the atom alone. The
//! kernel draws the admission's boundary from its own count and carries it in
//! the atom's record, so an artifact replays to the same boundary through
//! [`Environment::replay`]. The rule, its alternatives and its reversal are in
//! [`seal`].
//!
//! # Universe identity boundaries
//!
//! The certified-equivalence type `Path_U` is native term syntax; conversion
//! compares its raw classifier and map syntax, never replay-equivalence or
//! certificate evidence. Transport is computation whose claims the kernel
//! replays. Identity on elements and the bridge mode share a code fold;
//! element identity, its guarded higher field and higher evaluation are
//! persisted syntax, as is the directed family: `Flow(A, x, y)`, `stay`,
//! sequential `then` and `ride` under a covariant motive, with forward,
//! function and session certificates at `Flow_U`. The bridge mode is a bounded
//! in-memory rule language. List has a finite native code and guarded,
//! borrowed inhabitants observed only to a supplied budget. Session codes and
//! their identity evidence are native; their directional flows relate
//! recorded runs, not kernel endpoint values, so a ride along one refuses.
//!
//! The decisions and exhaustion semantics are in [`path_universe`],
//! [`flow_universe`], [`identity_recursion`], [`element_identity`],
//! [`higher_field`] and [`session`]; every assigned and reserved wire byte is
//! in `gandr-kernel-term`'s tag table. Frontend checking, cached content,
//! presentation and the command IL each retain their own boundary: none turns
//! stored candidate evidence into authority or introduces source syntax by
//! representing it.
//!
//! # Element identity
//!
//! Element identity is persisted kernel syntax over the one identity fold.
//! [`element_identity`] forms `Path(A, a, b)` at any `A`, the identity at an
//! open type a neutral fibre; an introduction checks at the fold's native
//! fibre, `here` by the kernel's own conversion, a returned endpoint at the
//! returner its computation synthesizes, transport at its motive instantiated
//! by substitution, a higher field through its stated depth, a higher
//! evaluation by replaying every component over kernel-generated coverage, and
//! a quantified evaluation by replaying every step of a body that applies its
//! function argument, branching over the applied function's result. The
//! checking machine owes every nested check as a goal on its own stack, and
//! the replay computes transport and related application by the fold's
//! clauses. Each decision, with its alternatives and reversal, is stated in
//! that module; the fold's bridge reading has no persisted node.
//!
//! **A motive that depends on the path is a telescope, carried by its own
//! node.** The motive is the computation type `Π (y : A). Π (z : B). F C`,
//! `B` a family over the endpoint and `C` over both entries, and the
//! telescope transport `tr₂(M, p, z₀, q, v)` carries, besides the path and the
//! value, the family element `z₀` at the source and the identity `q` over
//! the path. The checker reads both entries off the motive, checks `z₀` at
//! `B[a]`, requires `q` to synthesize `Path(B[b], ⟨tr(y. B, p, z₀)⟩, z₁)`,
//! refusing it by name (`IdentityError::NotOver`) otherwise, checks `v` at
//! `C[a, z₀]` and returns `C[b, z₁]`, each instance by iterated single
//! substitution, outer binder first; a motive of any other shape is a
//! computation-shape mismatch naming the telescope. The replay computes it by
//! two clauses: `here` along both identities returns the value, and `here(c)`
//! along the path transports the value along `q` in the fibre `z. C[c, z]`;
//! everything else sticks. `J` is not a node: it is this transport in the
//! singleton, `tr₂(Π y. Π q : Path(A, a, y). F C, p, here(a), here(p), d)`,
//! whose identity over the path checks because the singleton clause carries
//! `here(a)` to `p`. The alternatives were widening the one-binder
//! transport's motive to a telescope, which would change what a persisted
//! node means, and a primitive `J`, which the identity fold does not need.
//! Reversal: once Σ is kernel syntax, the telescope transport is the
//! one-binder transport over the Σ of its two entries, and the node retires.
//!
//! # The trusted equality reflexivity reads
//!
//! Type conversion stays the structural comparison above. Term equality the
//! kernel decides with no engine's trace, `here(c)` against `Path(A, a, b)`
//! first of all, is `conv::convert_values`: α-equality, then
//! [`replay::convert`], the replay's own loop run with no trace. That loop
//! fires only the rules the shapes force — weak head reduction, forcing, the η
//! laws, the two commuting conversions of `F`, a returned endpoint taken as its
//! computation, and decomposition — unfolds no constant and certifies no
//! refutation, so `EndpointsDiffer` is reported only after it fails to relate
//! the endpoints and the endpoint's dialogue does not replay. A judgement that
//! needs another term equality enters at the same function.
//!
//! **Choice.** One conversion, the replay's, so the kernel admits every
//! reflexivity the engine's normalizer admits by those laws: the core admits
//! ⇒ the kernel admits. **Alternatives.** Structural equality alone, which
//! refuses `here(f)` at `Path(_, f to x. return x, f)` though the core admits
//! it; a normalizing equality of the kernel's own, a second trusted conversion
//! beside the replay's. **Reversal.** Endpoints related only through a
//! constant's body take an engine trace through [`replay()`] rather than a δ
//! rule in the forced loop, as reflexivity's do. The witness is
//! `element_identity::tests::reflexivity_converts_its_endpoints_by_the_laws_of_bind`.
//!
//! A reflexivity carries the engine's dialogue relating its point to each
//! endpoint, and an endpoint the forced conversion leaves apart is related by
//! replaying that dialogue with the admitted definitions unfoldable: the
//! kernel unfolds only the constant the dialogue names, at the side it names,
//! under a thunk as anywhere else. The forced loop stays δ-free and there is
//! no second equality ([`mod@element_identity`] § Reflexivity replays the
//! engine's conversion). The witness is
//! `element_identity::tests::an_endpoint_unfolding_under_a_thunk_replays_its_dialogue`.
//!
//! A returned endpoint at a mode switch is read, not compared. Where the
//! conversion leaves one apart, the kernel normalizes it by its own evaluator —
//! weak head reduction, and the δ-step a stuck head naming a definition admits
//! — and the normal forms enter `conv::convert_values` like any endpoint. One
//! computation's reduction to its value chooses nothing, so the δ-step is
//! evaluation, not a conversion rule. The witness is
//! `element_identity::tests::a_returned_endpoint_reads_at_a_mode_switch`.
//!
//! A definition whose declared type and body's type relate compound path
//! endpoints only through a constant's body carries the engine's dialogue for
//! each such pair, and a mode switch the forced reading leaves apart replays
//! the dialogue of the pair α-equal to the one it meets
//! ([`mod@element_identity`] § A definition's conversions replay the dialogues
//! it carries). Matching is content equality, never a search, and the forced
//! loop stays δ-free. The witness is
//! `element_identity::tests::a_definition_relating_compound_endpoints_admits`.
//!
//! # Presented types
//!
//! A data declaration may present its type by rules over its own
//! constructors, `Loop(Unloop(x)) ~> x` (kernel-term's `Presentation`, the
//! additive declaration kind `0x08`): two terms of the type are equal when
//! the rules rewrite them to one normal form. Admission validates the rules
//! against the constructor table ([`presented`]): each left side is headed by
//! a constructor, linear, and matches constructors only where a field has the
//! declaration's own type; each right side is built from the variables its
//! left side binds, each at most once and at the field type it was bound at,
//! and holds fewer constructors, so every rewrite shrinks the term and
//! normalization ends. A rule that fails is refused `RuleNotPresentable`,
//! naming the rule and its fault.
//!
//! The replay reads a presented value by its normal form as part of weak head
//! reduction, a forced step no decision records, and the mode switch sets a
//! pair of presented constructors aside for that reading. Normalization is
//! δ-free: it flattens the constructors of the presented type alone, and every
//! other field is a leaf it moves but never reads. A refutation of two
//! presented terms is not authoritative, because two normal forms headed
//! apart may still meet through a leaf.
//!
//! **Choice.** Rules live on the data declaration, read by one rewriting
//! strategy both checkers run (innermost, last in pre-order, first rule in
//! written order), so they reach one normal form even for rules that are not
//! confluent; conversion is then an equivalence the rules generate, and sound.
//! **Alternatives.** Quotient syntax with a node of its own, which would put
//! the rules' obligations in every term that names the type; a confluence
//! check at admission, which the producer's critical-pair joins already
//! certify for conversion (the apartness rule below runs its own, where a
//! refutation is the verdict). **Reversal.** A presentation whose rules
//! terminate only by a path order takes that order's check here in place of
//! the size bound; one whose redexes sit behind a definition unfolds its
//! leaves by recorded decisions.
//! The witnesses are
//! `presented::tests::the_forced_loop_converts_circle_words_by_their_normal_forms`
//! and `presented::tests::a_mode_switch_reads_circle_words_by_their_normal_forms`.
//!
//! A case reads its scrutinee's constructor as written, so over a presented
//! type its arms could tell apart two terms the rules identify — `Base` from
//! `Loop(Unloop(Base))` — and `cong` would carry the path between them to a
//! path between distinct results. Each rule `l ==> r` is therefore an
//! obligation on every case over the type, decided once its branches check:
//! `F(l)` converts with `F(r)`, `l` and `r` built over one fresh variable per
//! pattern variable, by the same forced replay. `F` is the structural fixpoint
//! itself when the case is its root, `fix f. λy. case y { … }`, so a recursive
//! call unfolds at a constructor field and meets its twin stuck at a variable;
//! any other case is `F` with each side in its scrutinee's place. A case that
//! fails is refused `RuleNotRespected`, naming the first such rule; the
//! checker decides the same obligation δ-free and refuses by the same name,
//! with both sides. The obligation is re-derived on readmission, so no trace
//! records it and the artifact format is unchanged.
//!
//! **Choice.** The fold form, the obligation a quotient puts on any map out
//! of it, decided by conversion. **Alternatives.** Refusing every case over a
//! presented type, which left it without an eliminator; a recorded dialogue
//! per rule, which the checker's decision makes redundant. **Reversal.** A
//! respect that holds only up to a path is the next paragraph's. The
//! witnesses are
//! `native_formers::native_formers::a_case_respects_its_type_s_rules_or_is_refused_by_the_rule`
//! and, on readmission,
//! `kernel_export::kernel_presented_readmission::a_fold_whose_arm_breaks_a_rule_is_refused_by_name`
//! in the surface corpus.
//!
//! **A fold whose sides meet only up to a path rests on laws.** The winding
//! number sends `Loop(Unloop(x))` to `turn(unturn(f(x)))`, which no
//! conversion reduces to `f(x)` on a variable. A definition may name one law
//! per rule (kernel-term's `Declaration::laws`, the additive declaration kind
//! `0x09`): a declaration whose type is `Path(C, a, b)` behind one parameter
//! per pattern variable. Where the δ-free test fails for rule `i`, law `i` is
//! instantiated at the rule's variables as the fold reads them — `F(x)`
//! returned where a variable stands at the folded type, the variable
//! elsewhere — and its endpoints must convert with `F(l)` and `F(r)`, each
//! read with its runs in place or bound ahead as elaboration binds them
//! ([`mod@check`]'s respect module). Nothing is searched and no trace is
//! recorded: the rule, the fold and the law's declared type re-derive the
//! claim, and the fold's audit names each law it rests on as it names an
//! operation it calls, so a law that is owed keeps the fold's verdict owed.
//!
//! **Choice.** Laws named by the definition, in rule order, each its own
//! declaration — owed, proved or assumed — so the obligation is a constant
//! the ledger already counts. **Alternatives.** A goal minted per rule beside
//! the fold, which would hide the model's laws behind anonymous holes and
//! repeat them for every fold out of the same model; laws found by searching
//! the environment, which makes admission depend on what else is declared.
//! **Reversal.** Arms generated from a model's signature, which would carry
//! the laws with the model rather than with each fold. The witnesses are
//! `native_formers::native_formers::a_fold_rests_on_the_law_of_each_rule_it_computes_apart`
//! and, on readmission,
//! `kernel_export::kernel_presented_readmission::a_fold_resting_on_a_forged_law_is_refused_by_name`
//! in the surface corpus.
//!
//! **Two terms of a data type are apart when their normal forms differ at a
//! constructor.** A case of no branch over a scrutinee of `Path(A, a, b)`, `A`
//! a data type, answers any motive when `a` and `b` are apart
//! ([`presented`] § Apartness): the kernel joins every critical pair of `A`'s
//! rules itself, reads each endpoint where `A` stands — a constructor of `A`
//! a node, a reference to a definition its body, anything else a leaf —
//! normalizes both, and requires the first difference to be two distinct
//! constructors, no leaf standing where `A` does. A free type is the case with
//! no rule: constructor disjointness. The case is the whole certificate: no
//! new node, no recorded verdict, the artifact format unchanged; a case whose
//! endpoints are not apart is refused `NotApart`, naming why — they agree,
//! differ only under a leaf of another type, are open, or the rules diverge —
//! and the checker decides the same rule over its own arena and refuses by the
//! same name. A data type with no constructor is eliminated by the same case
//! of no branch, with no decision to make. The witnesses are
//! `presented::tests::endpoints_are_apart_by_their_normal_forms`,
//! `native_formers::native_formers::an_absurd_case_rests_on_apart_endpoints_in_both_checkers`
//! and, on readmission,
//! `kernel_export::kernel_presented_readmission::an_absurd_case_readmits_by_apartness_and_forged_twins_are_refused_by_name`
//! in the surface corpus.
//!
//! # Contract boundaries
//!
//! The source `# Specification` is authoritative; `#[spec(...)]` checks
//! executable clauses. `# Adequacy` bounds finite witnesses, not unbounded
//! proofs.
//!
//! | Area | Contract source |
//! | ---- | --------------- |
//! | Admission, staging and audit | [Environment](crate::env): committed prefixes, rollback, registration ownership, provenance ordering, ordered dependency reasons and reachability boundaries. |
//! | Guarded local admission | [Admission](crate::admission): schema inheritance, rule-discrimination transparency, guarded substitution and exact instance-side agreement by same-arena identity. |
//! | Checking and conversion | [Checker](crate::check), [conversion](crate::conv) and `witness`: level precedence, refusal subjects, readable identities, mode transitions and witness projections. |
//! | Element identity | [Element identity](crate::element_identity): the neutral fibre at an open type, fibre redirection, reflexivity by conversion, the returned endpoint read by its reduction, a definition's related endpoints replayed by matching, guarded higher fields, coverage-replayed higher and quantified evaluation and transport by substitution. |
//! | Encoding and support | [Encoding](crate::encoding) and [support]: byte-exact frames and hashes, ordered children, content-id reuse, cache observations and binder reach. |
//! | Replay and rewrite | [Replay](mod@crate::replay) and [rewrite]: arena restoration, trace consumption, ordered premises, freezing, rule priority and unchanged-subject reuse. |
//! | Fixture observations | `acceptance`, `adversarial_depth`, `flow_universe::tests` and `path_universe::tests`: differential verdicts, closed-form counts, small-stack teardown and fixed syntax seams. |
//!
//! Scalar captures, byte views and fixed child arrays avoid repeated
//! conversion, normalization, hashing or graph walks. Captures allocate nothing
//! and add no ordinary-lane work. Const APIs stay const and compare fields or
//! variants; private runtime rewrite projections compare opaque ids.
//!
//! Saturated reach stays widest beneath binders and selects the whole
//! telescope: it is an unknown bound. Replay refuses exhausted budgets before
//! incrementing, including at the counter ceiling. Structural refusal may
//! consume an optional `Decompose` marker.
//!
//! Explicit `- executable: none` exemptions:
//!
//! | Boundary | Items | Unavailable observation |
//! | -------- | ----: | ----------------------- |
//! | Data declarations | 12 | Evidence validity, event history or comparison of executions; producers and consumers carry the callable obligations. |
//! | Evaluated tag assertion | 1 | No callable boundary; constant evaluation checks the sparse tag bound. |
//! | `KernelError::fmt` | 1 | No readable formatter output buffer. |
//! | `Unfoldings::new` | 1 | No arena provenance or closure observer; lookup and replay witness it. |
//!
//! The evaluated tag assertion is an anonymous `const` that checks every
//! assigned node tag against the private dangling sentinel `0xFF`; it checks
//! tag values rather than the length of the sparse table, and a named unused
//! constant would not establish that build-time guard.
//!
//! ## Where witnesses live
//!
//! A module's tests live in a child file, `src/<module>/tests.rs`, declared
//! `#[cfg(test)] mod tests;`. The library build never reads that file, so a
//! test-only edit rebuilds this crate's test target and nothing else. An
//! edit to the module's own file, a doc line included, rebuilds this crate
//! and every workspace crate above it. On a warm enforcing build, with every
//! core available, touching `stage/tests.rs` recompiled 1 unit in 16 s and
//! touching `stage.rs` recompiled 18 units in 43 s. On a four-core hosted
//! runner, a landing that dirtied this crate spent 348 s building.
//!
//! A mutation survivor's witness therefore lands in the child file alone.
//! The `- witness:` lines that register survivor witnesses under the items'
//! `# Adequacy` are added once per crate, in its last survivor change, so
//! each campaign rebuilds the cone once rather than once per batch. A defect
//! fix registers its own witness in the same change, because the fix edits
//! the library anyway. The alternative, an inline `mod tests { … }`, keeps a
//! module's tests beside it at the price of a cone rebuild for every added
//! test. Revisit this if the build tracks test-only items finely enough that
//! an inline test module no longer dirties the library.
//!
//! # Arithmetic and absence
//!
//! Arithmetic uses
//! [quenchant-arith](https://github.com/gandr-lang/quenchant/tree/8b8d0702d69409549e855606a85492c777e05fc9/crates/quenchant-arith):
//! strict operations for counts bounded by allocated data or a preceding
//! guard, wrapping multiplication only for FNV-1a modulo 2^128, and
//! saturation only for the stated census ceilings, binder-index ceilings and
//! conservative context reach. Defaults and unsafe `fast` mode remain off;
//! the build cfg selects specification instrumentation. The alternative was
//! primitive arithmetic with profile-dependent overflow behavior or a local
//! copy of these families; one maintained implementation gives each operation
//! an explicit, profile-independent meaning. Reconsider when the arithmetic
//! domain changes or a published release replaces the Git pin.
//!
//! Non-failure absence uses
//! [quenchant-shape](https://github.com/gandr-lang/quenchant/tree/8b8d0702d69409549e855606a85492c777e05fc9/crates/quenchant-shape),
//! with a sealed reason enum at each decision site rather than an
//! undifferentiated `Option`. A failure remains a typed error, never a
//! fabricated value. The six sites distinguish a formation answer from a term
//! answer, an out-of-scope slot, an unbound variable, an unadmitted constant,
//! a substitution needing no carrying shift, and a goal without an expected
//! type. Reconsider a reason only when its caller gains a distinct response to
//! it; container lookups and external traits retain their own boundary types.
//!
//! Content numbering is zero-based and infallible. Every fresh record first
//! appends a nonempty framed image, so the count is bounded by the allocated
//! byte stream. Supported targets bound that allocation by `isize::MAX`,
//! below `u64::MAX`. The latter ceiling is not an observable state; a test
//! that installs an impossible private count would test another state space.
//! The enforcing specification checks the count/stream bound, and the
//! content-collapse and sharing witnesses exercise both fresh and reused
//! records. A fallible mint was rejected: it adds an unreachable error, and
//! neither silent diagnostic failure nor a change to one-based numbering has a
//! semantic justification. Revisit the boundary if content numbering stops
//! being backed by this in-memory stream or target widths exceed 64 bits.
//!
//! [`Environment::add_decl`]: crate::env::Environment::add_decl

#![no_std]

extern crate alloc;

pub mod admission;
pub mod census;
pub mod check;
pub mod conv;
pub mod element_identity;
pub mod encoding;
pub mod env;
pub mod error;
pub mod flow_universe;
pub mod higher_field;
pub mod identity_recursion;
pub mod levels;
pub mod path_universe;
pub mod presented;
pub mod replay;
pub mod rewrite;
pub mod seal;
pub mod stage;
pub mod stage_order;
pub mod support;
mod witness;
mod words;

pub use crate::census::ExpansionCensus;
pub use crate::census::ExpansionCount;
pub use crate::census::ExpansionKind;
pub use crate::check::DefaultMemo;
pub use crate::check::Judgement;
pub use crate::check::check_declaration;
pub use crate::check::check_declaration_with_memo;
pub use crate::conv::Convertibility;
pub use crate::conv::convert_comp_type;
pub use crate::conv::convert_value_type;
pub use crate::conv::convertible_comp_types;
pub use crate::conv::convertible_value_types;
pub use crate::element_identity::EndpointSide;
pub use crate::element_identity::IdentityError;
pub use crate::encoding::ContentEncoding;
pub use crate::encoding::ContentId;
pub use crate::encoding::ContentTable;
pub use crate::encoding::EncodingLength;
pub use crate::encoding::RewriteGoal;
pub use crate::encoding::SupportGoal;
pub use crate::encoding::content_digest;
pub use crate::encoding::encode_rewrite;
pub use crate::encoding::encode_support;
pub use crate::env::Admission;
pub use crate::env::AdmittedDeclaration;
pub use crate::env::ArtifactRefusal;
pub use crate::env::AxiomReport;
pub use crate::env::CheckedId;
pub use crate::env::Environment;
pub use crate::env::OutstandingContent;
pub use crate::env::OutstandingCount;
pub use crate::env::StagedDeclaration;
pub use crate::env::Staging;
pub use crate::error::CompTypeHead;
pub use crate::error::CompTypeMismatch;
pub use crate::error::CompTypeWitness;
pub use crate::error::ExpectedComputationShape;
pub use crate::error::ExpectedValueShape;
pub use crate::error::KernelError;
pub use crate::error::LevelOrderRefutation;
pub use crate::error::NonInferableForm;
pub use crate::error::RegisterFault;
pub use crate::error::UniverseViolation;
pub use crate::error::ValueTypeHead;
pub use crate::error::ValueTypeMismatch;
pub use crate::error::ValueTypeWitness;
pub use crate::levels::LevelContext;
pub use crate::presented::Presentations;
pub use crate::replay::EngineClaim;
pub use crate::replay::KernelVerdict;
pub use crate::replay::ParameterCount;
pub use crate::replay::ReplayBudget;
pub mod session;
pub use crate::replay::ReplayDecline;
pub use crate::replay::ReplayNode;
pub use crate::replay::ReplayRefusal;
pub use crate::replay::ReplaySides;
pub use crate::replay::TracePosition;
pub use crate::replay::Unfoldable;
pub use crate::replay::Unfoldings;
pub use crate::replay::read_step;
pub use crate::replay::replay;
pub use crate::rewrite::BinderDepth;
pub use crate::rewrite::RewriteMemo;
pub use crate::rewrite::RewriteOutcome;
pub use crate::rewrite::RewritePlane;
pub use crate::rewrite::RewriteSupport;
pub use crate::rewrite::shift_value_type;
pub use crate::rewrite::substitute_comp_type;
pub use crate::support::LooseDepth;
pub use crate::support::LooseDepths;
pub use crate::support::NodeOutcome;
pub use crate::support::NodeSupport;
pub use crate::support::SupportContext;
pub use crate::support::SupportPlane;
