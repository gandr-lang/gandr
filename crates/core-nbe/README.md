# gandr-core-nbe

Normalization by evaluation for the core language: the glued value domain, the per-run arena that owns it, its two policy parameters, and the evaluation and readback machines.

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
- [Source sharing](#source-sharing)
- [Specification attributes](#specification-attributes)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** The semantic half of the core language. `eval_value` and `eval_computation` evaluate a `gandr-core-term` term to weak head in a `DomainArena`; `readback_value` and `readback_computation` read a domain node back into the core arena. A domain node is glued: it carries what it denotes together with the core term it came from, and a neutral carries its unfolded form beside its neutral form. `SchedulingPolicy` and `DuplicationPolicy` are the two parameters the domain is written against. Types are not evaluated. The crate is `no_std` over `core` and `alloc`.

**Why.** A conversion checker compares neutral forms first and unfolds only when they disagree, and an elaborator wants a normal form that keeps the source term wherever nothing reduced. Both need a domain that holds both readings at once, and both run on terms whose depth is whatever an elaborator built, so neither machine may recurse on the host stack.

**How.** Evaluation and readback are machines over an explicit task stack and two result stacks split by polarity, so depth lives on the heap. Evaluation keeps a node's source term exactly when every child came back denoting the corresponding source child, and turns a manifest constant into a neutral carrying its body's content id unforced. Readback chooses a face by mode, goes under a binder by minting a fresh variable at a de Bruijn level and evaluating the closure's body against it, and converts each level back to an index. Both machines draw on one fuel budget, because β and `force` alone suffice to loop. Laziness is a scheduling restriction rather than a representation, so a definitional height is a share of attention, never a gate on which unfoldings are tried.

## References

- Nathanaëlle Courant and Xavier Leroy. "A Lazy, Concurrent Convertibility Checker." _Proceedings of the ACM on Programming Languages_ 10 (POPL), Article 53, January 2026. `doi:10.1145/3776695` — laziness recovered by scheduling rather than by representation, and the non-uniform-share conjecture that motivates the scheduling parameter without fixing its default.
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

## Expected features

- **The core arena outlives the domain arena.** A domain node names core nodes it does not own: the source term its term face caches, a literal payload, the body a closure suspends. The domain arena cannot check those ids, so the caller runs one domain arena per evaluation over one core arena and never truncates the core arena below a node the domain holds; a violation yields a wrong readback, not a refusal.
- **Well-scoped input.** Readback splices a source id under open binders on the strength of its term face, which is sound only if that source term is closed. Evaluating a well-scoped term guarantees it. A loose index inside an unevaluated thunk body is never seen — `thunk (λ. return x₁)` keeps its face in the empty environment — and checking closedness at the splice is the traversal the face exists to avoid.
- **Lowering one body.** The definition chain names a body by its canonical subterm-table entry index, which is arena-independent; `LoweredChain::lower` runs the one pass in admission order and asks the caller, once per distinct index, for that body as a closed core value in the arena the run evaluates against. Reading a table entry as a core term is the caller's, because the caller holds the table. A lowering that is not closed surfaces as `EvalFault::UnboundVariable`, inside `ReadbackFault::Eval`, when the body is forced.
- **A fuel budget.** The caller sizes `Fuel` for the run; exhaustion is `EvalFault::OutOfFuel` or `ReadbackFault::OutOfFuel`, a decline rather than a verdict.
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

A `DomainArena` belongs to one run: nothing is persisted or shared between runs. Six id families — values, computations, neutrals, both closure spaces and levels — are minted only by constructors over existing children, so a child id is below its parent's within its family and acyclicity across families rests on minting order. A level is a vector of atoms, so a lift names an entry in the run's level table and the domain node stays `Copy`. `DomainArena::truncate_to` discards a speculative evaluation past a `RunWatermark`; at the floor it is the run's whole teardown, six flat vector drops in any order.

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

## Source sharing

A core term is a DAG, and both machines walk it as a tree: evaluation evaluates a node reached twice twice, and readback mints a fresh core node per rebuilt domain node. A term with deep sharing costs its expansion, bounded by the fuel budget. Removing that cost is the duplication parameter's job; a cache keyed on the source node inside a machine would make the sharing decision behind the parameter's back.

## Specification attributes

Each item's `# Specification` prose is the statement of record; a `#[spec(...)]` attribute states a clause verbatim where it is a cheap predicate over one call. `SchedulingPolicy::share` asserts its share is strictly positive, so a stance answering zero aborts at its first call under enforcement. The machines' `step` dispatchers stay prose: an assembly frame pops its operands in the same step that pushes its result, so no relation between entry and exit stack lengths states that the result reached the stack of its polarity. Where a clause covers part of a prose line, the block's `provides` names the residue and the witnesses that carry it.

## License

Apache-2.0 WITH LLVM-exception. The licence text is at the repository root.
