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
//! persisted syntax, while the bridge mode and forward-only `Flow_U` are
//! bounded in-memory rule languages. List has a finite native code and
//! guarded, borrowed inhabitants observed only to a supplied budget. Session
//! codes and their identity evidence are native; their directional flows
//! transport recorded runs, not kernel endpoint values.
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
//! by substitution, a higher field through its stated depth and a higher
//! evaluation by replaying every component over kernel-generated coverage. The
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
//! | Element identity | [Element identity](crate::element_identity): the neutral fibre at an open type, fibre redirection, reflexivity by conversion, the returned endpoint read by its reduction, guarded higher fields, coverage-replayed higher evaluation and transport by substitution. |
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
//! | Data declarations | 10 | Evidence validity, event history or comparison of executions; producers and consumers carry the callable obligations. |
//! | Evaluated tag assertion | 1 | No callable boundary; constant evaluation checks the sparse tag bound. |
//! | `KernelError::fmt` | 1 | No readable formatter output buffer. |
//! | `Unfoldings::new` | 1 | No arena provenance or closure observer; lookup and replay witness it. |
//!
//! The evaluated tag assertion is an anonymous `const` that checks every
//! assigned node tag against the private dangling sentinel `0xFF`; it checks
//! tag values rather than the length of the sparse table, and a named unused
//! constant would not establish that build-time guard.
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
pub mod replay;
pub mod rewrite;
pub mod seal;
pub mod stage;
pub mod support;
mod witness;

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
