# gandr-core-nbe

Normalization by evaluation for the core language: the glued value domain, the per-run arena that owns it, its two policy parameters, the evaluation and readback machines, the search-free steps of conversion, and the sharing overlay with its erasure.

<!-- toc -->
- [Synopsis](#synopsis)
- [References](#references)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Optional tracing](#optional-tracing)
- [Term face and unfolding face](#term-face-and-unfolding-face)
- [Neutrals and spines](#neutrals-and-spines)
- [Closure spaces](#closure-spaces)
- [Per-run arena](#per-run-arena)
- [Scheduling share](#scheduling-share)
- [Duplication stance](#duplication-stance)
- [Evaluation](#evaluation)
- [Lowered definition bodies](#lowered-definition-bodies)
- [Readback modes](#readback-modes)
- [Conversion steps 1 through 3](#conversion-steps-1-through-3)
- [The cached word](#the-cached-word)
- [What stays in kernel-core](#what-stays-in-kernel-core)
- [Sharing overlay](#sharing-overlay)
- [Erasure](#erasure)
- [Source sharing](#source-sharing)
- [Specification attributes](#specification-attributes)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** The semantic half of the core language. `eval_value` and `eval_computation` evaluate a `gandr-core-term` term to weak head in a `DomainArena`; `readback_value` and `readback_computation` read a domain node back into the core arena; `convert_values` and `convert_computations` run the three conversion steps that need no search. A domain node is glued: it carries what it denotes together with the core term it came from, and a neutral carries its unfolded form beside its neutral form. `SchedulingPolicy` and `DuplicationPolicy` are the two parameters the domain is written against; an `Overlay` holds the sharing syntax a duplication stance is asked over, and `erase_value` and its siblings erase it back to the unshared term. Types are not evaluated. The crate is `no_std` over `core` and `alloc`.

**Why.** A conversion checker compares neutral forms first and unfolds only when they disagree, and an elaborator wants a normal form that keeps the source term wherever nothing reduced. Both need a domain that holds both readings at once, and both run on terms whose depth is whatever an elaborator built, so neither machine may recurse on the host stack.

**How.** Evaluation and readback are machines over an explicit task stack and two result stacks split by polarity, so depth lives on the heap. Evaluation keeps a node's source term exactly when every child came back denoting the corresponding source child, and turns a manifest constant into a neutral carrying its body's content id unforced. Readback chooses a face by mode, goes under a binder by minting a fresh variable at a de Bruijn level and evaluating the closure's body against it, and converts each level back to an index. Both machines draw on one fuel budget, because β and `force` alone suffice to loop. Laziness is a scheduling restriction rather than a representation, so a definitional height is a share of attention, never a gate on which unfoldings are tried.

## References

- Nathanaëlle Courant and Xavier Leroy. "A Lazy, Concurrent Convertibility Checker." _Proceedings of the ACM on Programming Languages_ 10 (POPL), Article 53, January 2026. `doi:10.1145/3776695` — laziness recovered by scheduling rather than by representation, the non-uniform-share conjecture that motivates the scheduling parameter without fixing its default, and the early-success, `var-1`, `var-2`, `var-3` and `const` rules conversion's first three steps implement.
- Nathanaëlle Courant. _Towards an Efficient and Formally-Verified Convertibility Checker_. PhD thesis, Université Paris Cité, September 2024. `hal:tel-04884688`, chapter 12 — the complexity analysis whose exponent is the size of the smallest proof, the axis a duplication stance moves.
- Thibaut Balabonski. "Weak Optimality, and the Meaning of Sharing." _Proceedings of the 18th ACM SIGPLAN International Conference on Functional Programming (ICFP 2013)_, pages 263–274, September 2013. `doi:10.1145/2500365.2500606` — spinal and ordinary full laziness are both β-optimal for weak reduction, so the spinal stance pays only under strong reduction and stays a measured choice.
- Paul Blain Levy. _Call-By-Push-Value: A Functional/Imperative Synthesis_. Semantics Structures in Computation 2, Kluwer Academic Publishers, 2003. `isbn:978-1-4020-1730-8`, `doi:10.1007/978-94-007-0954-6` — the polarity split the domain's value and computation halves follow.

## Provided features

- `eval_value` and `eval_computation`: weak-head evaluation, refusing with `EvalFault`.
- `readback_value` and `readback_computation` under `ReadbackMode::ZeroUnfold` or `ReadbackMode::Unfolding`, refusing with `ReadbackFault`.
- `DomainArena` with `DomainValueId`, `DomainCompId`, `NeutralId`, `ValueClosureId` and `CompClosureId`: checked constructors and lookups, `force_neutral`, and `RunWatermark` with `DomainArena::truncate_to`.
- The glued vocabulary: `DomainValue`, `DomainComp`, `Neutral`, `NeutralHead`, `Elimination`, `TermFace`, `CompTermFace`, `Unfolding` and `Glued`.
- `ValueClosure`, `CompClosure` and the two-zone `Environment` they close over.
- `SchedulingPolicy` with its `Share`, and `DuplicationPolicy` with `DuplicationPolicy::copies`.
- `Definitions`: the lowered chain, the definitional environment and the scope a run reads unfoldings through, and `Fuel`, the run's budget.
- `LoweredChain`: a definition chain with every body lowered into the run's core arena in one pass, so `ReadbackMode::Unfolding` forces any body the chain holds — evaluating its lowering closed and recording it with `force_neutral` — and `ReadbackFault::UnloweredBody` is reachable only for a body no entry names. Witnesses: `readback::tests::a_lowered_definition_body_unfolds_through_readback`, `eval::tests::a_chain_lowers_each_body_once_in_admission_order`, `readback::tests::the_unfolding_mode_refuses_a_body_no_chain_entry_names`.
- `convert_values` and `convert_computations`: conversion steps 1 through 3, answering a `Settlement` — `Identical` from step 1, `GuardedApart` from step 2, `StructurallyEqual`, `StructurallyApart` or `Deferred` with its `Deferral` from step 3 — projected by `Settlement::verdict` to a three-valued `Convertibility`, refusing with `ConversionFault`. Each step answers a case the previous one does not, and a pair needing an unfolding or an opened binder is deferred, never separated. Witnesses: `conv::tests::identity_answers_one_node_and_one_source_term`, `conv::tests::the_guard_answers_a_rigid_pair_identity_does_not`, `conv::tests::structure_answers_what_the_guard_cannot`, `conv::tests::a_pair_needing_an_unfolding_or_a_binder_is_deferred`, `conv::tests::a_mismatch_separates_only_beneath_a_rigid_head`, `conv::tests::computations_settle_by_their_weak_heads`, `conv::tests::a_shared_graph_is_compared_once_per_pair`.
- `Guard`, the cached word minted with every value, computation and neutral and read through `DomainArena::value_guard`, `comp_guard` and `neutral_guard`; `Guard::settles` answers `GuardAnswer::Apart` only for two rigid words whose `ContentHash`es differ. Witnesses: `guard::tests::equal_content_folds_to_one_word`, `guard::tests::a_flexible_child_makes_its_parent_flexible`, `guard::tests::only_two_rigid_words_that_differ_are_apart`, `arena::tests::a_neutral_is_rigid_only_without_a_body_or_a_closure`.
- `Overlay`, the sharing overlay: one flat family per core family behind `OverlayValueId`, `OverlayCompId`, `OverlayValueTypeId` and `OverlayCompTypeId`, each node one of the closed set opaque, bound, shared and grafted (`ValueNode`, `CompNode`, `ValueTypeNode`, `CompTypeNode` over `Bound`, `Sharing` and the four graft formers); minted only over children it holds, refusing with `OverlayFault`; released by `OverlayWatermark` with `Overlay::truncate_to`. Witnesses: `overlay::tests::minting_refuses_a_child_the_overlay_does_not_hold`, `overlay::tests::truncating_to_a_watermark_drops_later_nodes`.
- `Overlay::validate`: a heap worklist over one root that refuses, by an `OverlayRefusal` naming the node, an open node set, an occurrence of another family than its leg, an occurrence out of preorder or past its share's arity, a share its body under-fills or that stands for nothing, a node reached twice and a root the overlay does not hold. Witnesses: `overlay::tests::validation_refuses_an_open_node_set_by_name`, `overlay::tests::validation_refuses_an_occurrence_of_another_family`, `overlay::tests::validation_holds_each_share_to_its_arity_in_preorder`, `overlay::tests::validation_refuses_a_node_reached_twice`, `overlay::tests::validation_refuses_a_root_the_overlay_does_not_hold`, `overlay::tests::a_leg_counts_from_outside_its_share`, `teardown::teardown::a_deep_overlay_validates_and_is_released_in_both_orders_inside_a_small_stack`.
- `erase_value`, `erase_computation`, `erase_value_type` and `erase_comp_type`: total, policy-free erasure from an overlay root back to the unshared core term, refusing with `EraseFault` and leaving the core arena as it found it. The erased arena equals node for node the one a hand-built unshared term mints, and the unshared pipeline evaluates and reads back both to equal domain arenas, core arenas and results on every deep case. Witnesses: `overlay::tests::erasure_mints_every_former_of_every_family_in_order`, `overlay::tests::a_refused_erasure_leaves_the_core_arena_unchanged`, `deep_evaluation::deep_evaluation::an_erased_value_chain_evaluates_byte_for_byte_as_the_unshared_one`, `deep_evaluation::deep_evaluation::an_erased_curried_application_evaluates_byte_for_byte_as_the_unshared_one`, `deep_evaluation::deep_evaluation::an_erased_bind_chain_evaluates_byte_for_byte_as_the_unshared_one`, `deep_readback::deep_readback::an_erased_value_chain_reads_back_byte_for_byte_as_the_unshared_one`, `deep_readback::deep_readback::an_erased_suspension_chain_reads_back_byte_for_byte_as_the_unshared_one`, `teardown::teardown::an_erased_deep_overlay_equals_the_unshared_chain_inside_a_small_stack`.

## Expected features

- **The core arena outlives the domain arena.** A domain node names core nodes it does not own: the source term its term face caches, a literal payload, the body a closure suspends. The domain arena cannot check those ids, so the caller runs one domain arena per evaluation over one core arena and never truncates the core arena below a node the domain holds; a violation yields a wrong readback, not a refusal.
- **Well-scoped input.** Readback splices a source id under open binders on the strength of its term face, which is sound only if that source term is closed. Evaluating a well-scoped term guarantees it. A loose index inside an unevaluated thunk body is never seen — `thunk (λ. return x₁)` keeps its face in the empty environment — and checking closedness at the splice is the traversal the face exists to avoid.
- **Lowering one body.** The definition chain names a body by its canonical subterm-table entry index, which is arena-independent; `LoweredChain::lower` runs the one pass in admission order and asks the caller, once per distinct index, for that body as a closed core value in the arena the run evaluates against. Reading a table entry as a core term is the caller's, because the caller holds the table. A lowering that is not closed surfaces as `EvalFault::UnboundVariable`, inside `ReadbackFault::Eval`, when the body is forced.
- **A fuel budget.** The caller sizes `Fuel` for the run; exhaustion is `EvalFault::OutOfFuel` or `ReadbackFault::OutOfFuel`, a decline rather than a verdict.
- **Shares placed where their legs are read.** Erasure copies a leg's indices to every occurrence unshifted, so a free index in a leg names the binder it reaches from the occurrence. A producer that means one binder at every occurrence places the share inside that binder.
- **The specification facade's `cfg`.** `#[spec(...)]` clauses are checked at runtime only when the whole build graph is compiled with `--cfg anodized_panic`.

## Examples

Evaluate a closed pair and read it back without minting a core node:

```rust
use gandr_core_nbe::Definitions;
use gandr_core_nbe::DomainArena;
use gandr_core_nbe::Fuel;
use gandr_core_nbe::LoweredChain;
use gandr_core_nbe::ReadbackMode;
use gandr_core_nbe::eval_value;
use gandr_core_nbe::readback_value;
use gandr_core_term::CoreArena;
use gandr_core_term::DefinitionalEnvironment;

fn round_trip() {
    let mut core = CoreArena::new();
    let unit = core.value_unit();
    let source = core.value_pair(unit, unit);

    let chain = LoweredChain::new();
    let environment = DefinitionalEnvironment::new();
    let definitions = Definitions::new(&chain, &environment, environment.root());
    let budget = Fuel::from(64_u32);

    let mut domain = DomainArena::new();
    let evaluated = eval_value(&core, &mut domain, definitions, budget, source)
        .expect("a closed pair evaluates");

    // Nothing reduced, so the zero-unfold mode answers with the source id.
    let mark = core.watermark();
    let read = readback_value(&mut core, &mut domain, definitions, ReadbackMode::ZeroUnfold, budget, evaluated)
        .expect("an unreduced pair reads back");
    assert_eq!(source, read);
    assert_eq!(mark, core.watermark());
}
```

Run the tests, then again with specifications enforced:

```sh
cargo nextest run -p gandr-core-nbe
RUSTFLAGS="--cfg anodized_panic" CARGO_TARGET_DIR=target/enforcing cargo nextest run -p gandr-core-nbe
```

The deep evaluation, deep readback and teardown suites run inside a thread with a deliberately small stack, so a machine or a destructor that recursed per node fails them rather than fitting on a large host stack. The pinned-term suite compares each readback against an expected term written out by hand.

## Optional tracing

Enable `tracing` to observe evaluation and readback boundaries. The feature preserves `no_std` and activates no subscriber or output backend. Fuel checks and semantic errors remain ordinary code, independent of instrumentation.

| Boundary | Level | Fields |
| -------- | ----- | ------ |
| `eval_value`, `eval_computation` | INFO | Initial `fuel` |
| `eval_comp_within` | DEBUG | Initial `fuel`, including evaluations driven by readback |
| `readback_value`, `readback_computation` | INFO | Initial `fuel` and `unfolding` mode |
| Evaluation or readback fuel exhaustion | WARN | A fixed message inside the active span |

The caller owns filtering, the subscriber and the output destination. [`tracing::instrument`](https://docs.rs/tracing-attributes/0.1.31/tracing_attributes/attr.instrument.html) uses `skip_all`: no arguments, terms, environments, arena contents or result payloads are recorded, and no argument gains a `Debug` bound. Existing `Debug` implementations remain unconditional. These are diagnostic spans, not the conversion decision vocabulary or a replay certificate.

The choice is `tracing` 0.1.44 with only `attributes`, optional and off by default. Its structured spans retain the relation between readback and nested evaluation without an async runtime. Flat `log` events lose that nesting; a custom observer would duplicate a standard diagnostics interface. Revisit for a security advisory affecting the selected version, loss of maintenance, or a consumer requiring a different diagnostic model. The feature does not change scheduling, duplication or reduction decisions.

## Term face and unfolding face

Readback chooses a face and conversion forces one, so both faces are part of one domain type. The **term face** caches the core term a node came from and keeps it while nothing inside reduced; once anything reduces the face is `TermFace::Reduced`, because a stale source id is a wrong readback rather than a slow one. The **unfolding face** keeps a neutral's neutral form beside its unfolded form: `Unfolding::Rigid` for a head with no body to unfold, `Unfolding::Unforced` carrying a manifest definition's body content id, and `Unfolding::Forced` once the evaluated body is recorded with `DomainArena::force_neutral`, by an unfolding readback or by the caller. Forcing adds the second reading and never replaces the first, so conversion can compare neutral forms and fall back to unfolding.

## Neutrals and spines

A stuck value and a stuck computation share a head and differ in what is stacked on it. The core vocabulary has no value eliminator, so a neutral in value position carries an empty spine and one in computation position carries the applications, binds and cases that could not fire. `Neutral` is one node kind; `DomainArena::value_neutral` refuses a spined neutral in value position, and `DomainArena::neutral_node` refuses an unfolding face on a head that has no definition behind it. A module reference is a rigid head like any opaque constant, with no eliminator of its own.

## Closure spaces

`ValueClosure` suspends a value body and `CompClosure` a computation body: a lambda, a thunk, a bind continuation and a case branch are computation closures. No former in the core vocabulary produces a value closure; it is the shape a code under a binder takes. Both spaces close over the same `Environment`, so entering either is one operation: extend the captured environment and evaluate the body. The environment has the typing context's two zones, because an occurrence names its zone and one stack could not answer a linear occurrence. Its entries are `Copy` ids, so capturing an environment clones two flat vectors.

## Per-run arena

A `DomainArena` belongs to one run: nothing is persisted or shared between runs. Six id families — values, computations, neutrals, both closure spaces and levels — are minted only by constructors over existing children, so a child id is below its parent's within its family and acyclicity across families rests on minting order. Values, computations and neutrals each carry their cached word in a vector beside the family, cut at the same mark. A level is a vector of atoms, so a lift names an entry in the run's level table and the domain node stays `Copy`. `DomainArena::truncate_to` discards a speculative evaluation past a `RunWatermark`; at the floor it is the run's whole teardown, nine flat vector drops in any order.

## Scheduling share

A definitional height is a prior about which side of a conversion is cheaper to unfold. As a gate on which reductions run it can foreclose the short proof; as a share it changes only how fast each process runs. `SchedulingPolicy::share` returns a strictly positive `Share` for every height under every stance, so no stance starves a process. `SchedulingStance::UniformFair` is the default; `SchedulingStance::HeightWeighted` weights shallow goals ahead of deep ones without stopping the deep ones.

## Duplication stance

`DuplicationPolicy::copies` answers, per part of a shared value, whether a duplication copies it. `DuplicationStance::EraseAndClone` copies everything and is the unshared reference output every other stance replays against. `DuplicationStance::Spinal` copies the binder-to-occurrence spine and shares the ribs; it is representable so the parameter can express it, and `DuplicationPolicy::new` refuses it with `PolicyRefusal::StanceGated`. The results that would certify it are stated over simply-typed systems that type no fragment of this language, so it installs only behind a conversion trace that checks it by replay, and this crate takes no such trace.

## Evaluation

A composite keeps its source face exactly when every child's face is `Source(c)` for the very `c` the source node names; a variable resolved out of the environment makes its parent `Reduced`. A closure keeps its source face only when it captured the empty environment. A stuck computation spine is marked `Reduced` even where nothing reduced. A constant becomes a neutral whose unfolding face reads the definition through the scope's transparency; nothing is expanded, because eager unfolding would defeat the face evaluation fills. Extending a neutral's spine carries the unfolding along, since forcing means unfolding the head and re-applying the spine.

## Lowered definition bodies

The chain carries a body as a canonical subterm-table entry index rather than as a core node, because a core id means something only in the arena that minted it and a chain is cloned into every run. A run therefore lowers the chain into its own arena in one pass, in admission order: `LoweredChain::lower` asks for each distinct index once, so definitions the canonical table gave one body share one lowering, and every body the chain holds has a lowering before any run reads it. Evaluation still unfolds nothing — a manifest constant stays a neutral carrying its index unforced. `ReadbackMode::Unfolding` forces a body when it meets one: it evaluates the lowering in the empty environment from the readback's own budget and records the result with `DomainArena::force_neutral`, so a neutral met twice evaluates its body once and its neutral form stays readable beside the unfolding.

Alternatives: lowering at evaluation time, which is eager unfolding under another name and defeats the term face; a table the caller fills one body at a time and attaches, which leaves `ReadbackFault::UnloweredBody` reachable for every definition the caller missed; and decoding the subterm table here, which needs a lookup by entry index that the decoded artifact does not expose and a kernel-to-core reading that no crate owns. Reversal: the decoded artifact gains a lookup by entry index and a crate owns reading a table entry as a core term; the per-entry lowering then moves behind that crate and the pass keeps its shape.

## Readback modes

`ReadbackMode::ZeroUnfold` prefers the term face: a node whose face is `TermFace::Source` hands back that core id and mints nothing, and no unfolding is forced, so an `Unfolding::Unforced` body is still unforced when readback returns. `ReadbackMode::Unfolding` ignores the term face, rebuilds every node in canonical binder form so two results compare by structure, and spends every unfolding, forcing an unforced one from the run's `LoweredChain` first. The mode is a nominal input rather than a flag, because the wrong mode yields a different term. At `depth` open binders in its zone a level `l` is the index `depth - l - 1`; both subtractions are checked, and a level outside the opened binders is refused by name. Readback reads no core node, so a domain miss surfaces as `ReadbackFault::Domain` and a core miss only through the evaluation it drives, as `ReadbackFault::Eval`.

## Conversion steps 1 through 3

Conversion's first three steps answer without searching, and each falls through to the next only when it does not answer. **Step 1, identity**: one id is one value, and so are two nodes whose term faces name one source term, which catches sharing the source had and evaluation expanded — the early-success rule `conv? β β′ → T if β = β′` read on the term face as well as on the id. **Step 2, the guard**: two rigid cached words with different hashes settle the pair distinct in constant time. **Step 3, structural comparison**, over a heap worklist with head-mismatch fast-fail: Courant–Leroy's `var-1`, `var-2`, `var-3` and `const` rules over neutrals, with steps 1 and 2 run again at every pair the walk reaches.

The answer has three values because the steps never unfold and never open a binder. A pair whose answer depends on either is `Settlement::Deferred`: `Deferral::Unfolding` when a neutral's head has a body that may unfold into the other side, `Deferral::Binder` when two closures suspend different bodies or a closure meets a neutral an η-equation may relate it to. A mismatch beneath an unfoldable head, or in a closure's environment, defers rather than separates, because the unfolded body or the opened closure may never read what differed; beneath a rigid head it separates. A distinct answer is therefore sound relative to β, δ and the η-equations a later step adds.

The walk keeps the pairs it has met, per call, and skips a repeat, so two graphs that share structure cost their distinct pairs rather than their expansion. The set holds pairs only and dies with the call; it decides nothing about which part of a value is copied, which is what keeps it clear of the duplication parameter. Nothing is evaluated and nothing recurses, so the walk is total on any depth and takes no fuel. Steps 4 to 6 — unfolding, case-progress gating and speculation — are the conversion machine's, with heights as scheduling shares.

## The cached word

Every value, computation and neutral is minted with a `Guard`: `Guard::Rigid` carrying an FNV-1a `ContentHash` of the node's kind, payload and children's words, or `Guard::Flexible`. A node is flexible when a closure or a head with a body to unfold sits inside it; a dangling child at mint makes its parent flexible, the direction that decides nothing. For two rigid nodes conversion is structural equality on the hashed content, so differing hashes separate them; equal hashes decide nothing, because a hash may collide. Literal payloads and lift levels enter the hash through their `Hash` implementations, whose equality is the conversion equality for both; a term face never enters it, because two faces over one content are one value.

The word carries the hash and the rigidity bit and nothing else. Alternatives: the hole and metavariable bits, a loose-variable range and an approximate depth that a Lean-style word packs. Each is uniformly trivial here — the domain has no hole former, levels make α-equivalence identity, and every node a binder could make loose is a closure, which is flexible and never hashed. Reversal: the hole surface adds the hole bit, and a guard asked to decide under a binder adds the range.

The fold is ten lines over `core::hash::Hasher` rather than a crate. Alternatives: `rustc-hash`, whose algorithm changed across major versions and which would hold conversion machinery outside the workspace; `fnv`, unreleased since 2020; `foldhash`, seeded per instance with no stable output; and the workspace's `blake3`, a 256-bit cryptographic digest where a collision costs only a fall-through to step 3. Reversal: a word that crosses a run boundary, or needs an output stable across builds, takes a maintained crate with that guarantee.

## What stays in kernel-core

`gandr-kernel-core` keeps its own conversion: identity and structural equality over kernel types and the codes they carry, in the kernel's own arena, two-valued, failing closed to distinct. It stays separate because it is trusted and this pipeline is not. The kernel compares kernel syntax with nothing to unfold and no closures, and it accepts nothing it cannot recheck. This pipeline compares glued domain values, holds neutrals with bodies and closures over environments, answers three ways, and carries a guard table the kernel admits into nothing; its answers reach the kernel only as a conversion trace the kernel replays. Sharing code would put the domain inside the trusted base or make the kernel depend on an untrusted engine, and the two walks share no node type. What is shared is what both must agree on: canonical level equality, the `Eq` of `gandr-kernel-strata`'s `Level`, and the per-call discipline of a set of met pairs.

## Sharing overlay

An `Overlay` is sharing syntax over the core language and holds no policy: which part of a shared leg a duplication copies is `DuplicationPolicy::copies`'s answer, asked by the walk that duplicates. It keeps one flat vector per core family — values, computations, value types, computation types — so an id's type names its family and its polarity, and teardown is four flat vector drops. A node is one of four kinds and nothing else: **opaque**, a core node held by id; **bound**, one occurrence of a shared leg, named by its distance — how many shares lie between it and its own — and its position among that share's occurrences; **shared**, `body[x₀ … xₙ₋₁ ← leg]`, a body holding exactly `arity` occurrences of one leg of any family, standing in its body's family; and **grafted**, one core former over overlay children, with one graft arm per core former. A node is minted only over children the overlay holds, so every child is older than its parent and the overlay is acyclic across families.

`Overlay::validate` walks one root in preorder on a heap task stack, with a frame per share whose body it is inside. A leg stands outside its own share's scope, so an occurrence in a leg counts from the shares around that share. An occurrence closes when its distance names an open frame whose leg is of the occurrence's family, at that frame's next position and below its arity; a share closes when its arity is non-zero and its body reaches it exactly. A position is therefore the occurrence's preorder rank among its share's, never a free choice.

Sharing is explicit or absent: a node reached twice from one root is refused. Every node then has one parent, so a walk enters each node once, and an overlay whose expansion doubles per link validates in its own size rather than its expansion. Alternatives: admitting implicit reuse and walking it as a tree, which costs the expansion the overlay exists to remove; a graft as a template term with seam placeholders, which adds a seam syntax with its own spelling, order and linearity rules to say what one former per graft says; and named occurrences, which need a fresh-name supply and a capture check. Reversal: a producer that cannot name its shares — one that hash-conses after the fact — needs reuse admitted, and the walks a visited table in place of the reached-once rule.

## Erasure

`erase_value`, `erase_computation`, `erase_value_type` and `erase_comp_type` take an overlay root and the core arena its opaque nodes name, validate, and mint the core term the root stands for: each graft one core node after its children, left to right; each opaque node its core id as it stands; each share's leg once, before its body, and every occurrence that one id. They take no policy, so the output is a fact about the overlay alone, and it is the unshared pipeline's input: no share survives, and evaluation walks each occurrence of the leg's id as a copy, which is `DuplicationStance::EraseAndClone` and the reference every finer stance replays against. A refusal is named — `EraseFault::Refused` with the validation refusal, or `EraseFault::UnresolvedOpaque` for a core id the arena does not hold — and the core arena is truncated back to its entry watermark, so erasure is total: an erased term or no change.

Because the minting order is fixed, "byte for byte" has a definite meaning: the erased arena equals, under the core arena's own equality, the arena a hand-built unshared term mints when built in the same order. The deep evaluation, readback and teardown cases are each built twice, by hand and as an overlay, and compared that way, then run through the unshared pipeline to equal domain arenas, core arenas and results.

Indices are copied, never shifted: a leg's free index names, at each occurrence, the binder it reaches from there, the reading a core DAG gives a node reached twice. Alternatives: cloning the leg at every occurrence, which makes the output exponential in a chain of shares; and shifting the leg's indices by the binders between its share and each occurrence, which mints a copy per occurrence under a binder and changes the reading from the core DAG's. Reversal: a producer that places shares outside the binders their legs read, and needs substitution's reading, makes erasure shift and stop being node for node.

## Source sharing

A core term is a DAG, and both machines walk it as a tree: evaluation evaluates a node reached twice twice, and readback mints a fresh core node per rebuilt domain node. A term with deep sharing costs its expansion, bounded by the fuel budget. Removing that cost is the duplication parameter's job, over the sharing overlay; a cache keyed on the source node inside a machine would make the sharing decision behind the parameter's back.

## Specification attributes

Each item's `# Specification` prose is the statement of record; a `#[spec(...)]` attribute states a clause verbatim where it is a cheap predicate over one call. `SchedulingPolicy::share` asserts its share is strictly positive, so a stance answering zero aborts at its first call under enforcement. The machines' `step` dispatchers stay prose: an assembly frame pops its operands in the same step that pushes its result, so no relation between entry and exit stack lengths states that the result reached the stack of its polarity. Where a clause covers part of a prose line, the block's `provides` names the residue and the witnesses that carry it.

## License

Apache-2.0 WITH LLVM-exception. The licence text is at the repository root.
