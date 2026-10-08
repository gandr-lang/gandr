# gandr-kernel-conversion-trace

The conversion-decision seam between the untrusted convertibility engine and the certified kernel: the decision vocabulary, and a statically dispatched sink.

Convertibility is proof search, and the proof is what gets certified. The engine searches and is trusted with nothing; what it emits is a trace of the decisions it made, and the kernel replays that trace with a sequential algorithm that performs no search. A wrong engine therefore costs completeness, never soundness.

The crate owns no term vocabulary, no storage format, no wire representation, and no replay policy. Its generic identifier parameter keeps those concerns in the consumer that owns the arena.

## Status

New in the reboot, derived from the `kernel-conversion-trace` crate of the pre-reboot prototype and revised against the ratified normalizer/elaborator plan, the milestones module's `seam-crates` and the architecture module's `trace-seam`. The plan governs where it and the prototype disagree.

Ref: 01a051fd-253b-7dbc-8cb8-d880c051ad15

Revisions against the prototype, each with its reason:

- **The decision vocabulary grows from four kinds to nine.** The prototype named `Unfold`, `Postpone`, `Force` and `ComparedShared`, which is the grain of a heuristic unfolding strategy. A proof search needs the side of every reduction and the branch taken at every choice point, so `ReduceLeft`, `ReduceRight`, `ConstShortcut`, `Freeze` and `EtaExpand` join them. The plan's table has eight rows; `Unfold` and `Postpone` share one, so the eight rows name nine variants.
- **`ConversionSide` is a type.** `Freeze` records which side froze and `EtaExpand` which side was applied to the fresh variable, per the plan's table; `ReduceLeft` and `ReduceRight` carry the side structurally. A trace whose side is implicit cannot be replayed without searching for it, which is the property the seam exists to deliver.
- **The sink carries a compile-time activity constant.** `SinkActivity` mirrors the check-memo seam's `MemoActivity`, so a conversion path builds no decision values when the sink is inactive. Sink-off conversion is the same function at a different type parameter rather than a second implementation.
- **A recording sink lands beside the null one.** `TraceLog` is what a conversion run emits replay evidence through, and what a differential counts its exercised path through — a suite that only ever instantiates `NullSink` can be green while reaching no recording code at all.
- **`non_exhaustive` is dropped.** The workspace is `publish = false` end to end, so the attribute protects no external consumer while costing a wildcard arm at every match — defeating exhaustiveness precisely where a new variant should break every consumer.

Preserved from the prototype without change: the consumer-owned identifier parameter, the statically dispatched null sink, `no_std` with no dependencies, and the statement that a trace is a session artifact rather than a serialization contract.

## What it provides

- `ConversionDecision<Id>`, the vocabulary: `ReduceLeft`, `ReduceRight`, `ConstShortcut`, `Unfold`, `Postpone`, `Freeze`, `EtaExpand`, `Force`, `ComparedShared`.
- `ConversionSide`, which leg of the comparison a one-sided decision acts on.
- `TraceSink<Id>`, the emit seam, with an associated `SinkActivity` constant.
- `NullSink`, zero-sized and constant, so a conversion path instantiated here has no recording state and no dynamic dispatch to pay for.
- `TraceLog<Id>`, the recording sink: a flat vector, read back in recording order, with `DecisionCount` for the exercised-path assertion.

## The contract attributes

The `# Specification` prose stays the statement of record; a `#[spec(...)]` attribute mirrors it wherever the clause is a runtime predicate over one call. Four items carry one, all on the two shipped implementations: `NullSink::record` asserts the count is still zero afterwards and `NullSink::recorded_count` asserts it answers zero, while `TraceLog::record` asserts the log grew by exactly one and `TraceLog::recorded_count` asserts it answers the number of decisions held. A later edit that gave the null sink storage, or gave the recording sink a dropping append, has to break one of them to stay green.

The rest of the blocks state what no attribute can check. `SinkActivity`, `ConversionSide`, `ConversionDecision`, `NullSink` and `TraceLog` are data items, where a `#[spec]` invariant is never checked at construction. `TraceSink` and its three declarations are declarations: a clause on one requires the trait itself to carry `#[spec]`, which turns each declaration into a wrapper over a generated required method and changes what an implementor implements. `TraceLog::decisions` returns `impl Iterator`, which a closure-form postcondition cannot name. Each of those blocks says so in its own `- provides:` line.

`anodized` supplies core-only specification helpers with default features disabled. The enforcing test lane selects `--cfg anodized_panic` for the whole dependency graph; no logic/BigInt dependency is enabled.

## What it does not provide

- **The strategy and the replay.** The concurrent convertibility machine that emits a trace and the kernel's sequential rechecker that consumes one are the plan's `conversion-machine` milestone. This crate's own tests carry a miniature strategy and a miniature replay as the differential's two sides, not as the real ones.
- **Any storage or wire format.** A trace is a session artifact whose lifetime is the consumer's. Nothing here persists.

## What a trace is not

A trace individuates strictly more finely than convertibility: two convertible terms can carry different traces. It is replay evidence and never an equality, so comparing two traces decides something finer than conversion and would disagree on convertible inputs while raising nothing.

A trace records that two occurrences met; it does not record that they agreed. A refutation and a proof carry the same closing decision, and the verdict is recomputed by the replay from the terms.

## Plan and obligations discharged

Milestone: `seam-crates`, the two seam crates in the milestones module. The vocabulary is fixed by the architecture module's `trace-seam`.

Ref: 01a051fd-253b-7dbc-8cb8-d880c051ad15

Obligations from the harvested measurements this crate carries:

- **`obligation-08-the-memoless-path-is-the-same-function`**, read here as the recorded path. Activity is a compile-time constant on a null-object seam, and the crate's differential instantiates one strategy twice and compares verdicts.
- **`obligation-02-differentials-assert-their-exercised-paths`.** The sink-off side's decision count is asserted to be zero and the sink-on side's exactly, rather than reported.
- **`obligation-03-teeth-are-permanent-suite-members`.** A trace whose recorded side is swapped, and a trace whose unfolding decision is dropped, are both refused by the replay rather than agreed with, and those cases ship as suite members.

Ref: 01a05203-4468-7931-8246-761a8f853a27

Design context consulted in the proto tracker: `gandr-yvi9.5` and `gandr-0bmd` for the kernel-side seam discipline the sink mirrors, and `gandr-9he0`, whose synthesized-context step records conversion's consulted unfoldings through this seam — with the asymmetry that a refusal's consulted set is the union over all branches while an acceptance's is the winning derivation's.

## Theoretical ideas relied on

Search in the engine and decision in the kernel: a checker whose answer is a proof, replayed rather than trusted. Search-free replay: with the recorded side choices in hand the rechecker has at most one applicable rule at every step, so it is a sequential worklist with no queue, no wait map, and no fairness.

## Primary references

- Nathanaëlle Courant and Xavier Leroy. "A Lazy, Concurrent Convertibility Checker." _Proceedings of the ACM on Programming Languages_ 10, POPL, Article 53, January 2026. `doi:10.1145/3776695` — figure 4's nine rules are what the vocabulary must cover, and §9 names trace instrumentation and sequential recheck as future work that this seam anticipates.
- Nathanaëlle Courant. "Towards an Efficient and Formally-Verified Convertibility Checker." PhD thesis, Université Paris Cité, 2024. HAL `tel-04884688` — chapter 12, the complexity analysis over the proof size the trace's decisions are counted in.

The ratified plan supplies the architecture module's `conv-proof-search` and `trace-seam`, the risks module's `finer-invariant`, and the milestones module's `seam-crates`.

Ref: 01a051fd-253b-7dbc-8cb8-d880c051ad15

## License

Apache-2.0 WITH LLVM-exception.
