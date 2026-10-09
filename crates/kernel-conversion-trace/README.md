# gandr-kernel-conversion-trace

The conversion-decision seam between an untrusted convertibility engine and the certified kernel: the decision vocabulary and a statically dispatched sink.

<!-- toc -->

- [Synopsis](#synopsis)
- [References](#references)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [The decision vocabulary](#the-decision-vocabulary)
- [Static dispatch](#static-dispatch)
- [Traces and equality](#traces-and-equality)
- [Exhaustive matching](#exhaustive-matching)
- [Contract attributes](#contract-attributes)
- [License](#license)

<!-- tocstop -->

## Synopsis

**What.** `ConversionDecision<Id>` names every decision a convertibility check makes: each reduction with its side, the branch taken at each choice point, and the premise a refuted decomposition rests on. `TraceSink<Id>` is the seam an engine emits decisions through; `NullSink` records nothing and `TraceLog<Id>` records every decision in order. The crate owns no term vocabulary, storage format, wire representation or replay policy: the identifier is a type parameter, so those stay with the consumer that owns the arena.

**Why.** Convertibility is proof search, and the proof is what gets certified. The engine searches and is trusted with nothing; it emits a trace of its decisions, and the kernel replays that trace with a sequential algorithm that performs no search. A wrong engine therefore costs completeness, never soundness.

**How.** The vocabulary records the side of every reduction and the branch at every choice point, so with the recorded choices in hand the rechecker has at most one applicable rule at every step: replay is a sequential worklist with no queue, no wait map and no fairness. `TraceSink` carries an associated `SinkActivity` constant, so a conversion path instantiated at `NullSink` builds no decision values, and sink-off conversion is the same function at a different type parameter.

## References

- Nathanaëlle Courant and Xavier Leroy. "A Lazy, Concurrent Convertibility Checker." _Proceedings of the ACM on Programming Languages_ 10, POPL, Article 53, January 2026. `doi:10.1145/3776695` — figure 4's nine rules, which the vocabulary covers, including the one negative premise of the rule refuting two applications of one rigid head; and §9's trace instrumentation with a sequential recheck, which this seam carries.
- Nathanaëlle Courant. "Towards an Efficient and Formally-Verified Convertibility Checker." PhD thesis, Université Paris Cité, 2024. HAL `tel-04884688` — chapter 12, the complexity analysis over proof size, the measure a trace's decisions count.

## Provided features

- `ConversionDecision<Id>`: the vocabulary — `ReduceLeft`, `ReduceRight`, `ConstShortcut`, `Unfold`, `Postpone`, `Freeze`, `EtaExpand`, `Force`, `ComparedShared`, `NegativeSubgoal`.
- `SubgoalPosition`: which premise of a decomposition a refutation names, counted in an order both consumers derive from the terms.
- `ConversionSide`: which leg of the comparison a one-sided decision acts on.
- `TraceSink<Id>`: the emit seam, with an associated `SinkActivity` constant.
- `NullSink`: zero-sized and constant, with no recording state and no dynamic dispatch.
- `TraceLog<Id>`: the recording sink, a flat vector read back in recording order, with `DecisionCount` for exercised-path assertions.

## Expected features

- **A strategy and a replay.** The consumer supplies the convertibility engine that records into a sink and the sequential rechecker that consumes a `TraceLog`. In this workspace the engine is `gandr-core-nbe`'s conversion machine, which emits its winning derivation through `TraceSink<TraceNode>` in preorder. The crate's tests carry a miniature of each as the two sides of their differential.
- **An identifier space.** Every `Id` is meaningful in the consumer's own arena or value space, and the consumer keeps a trace within the scope in which its identifiers resolve.
- **A lifetime.** A trace is a session artifact whose lifetime is the consumer's. Nothing persists, and a trace is no serialization contract.
- **`--cfg anodized_panic` for enforcement.** Built with this `cfg` across the whole dependency graph, the `#[spec]` attributes check their clauses at runtime and panic on a violation. The enforcing test lane sets it.

## Examples

`tests/differential.rs` runs a miniature convertibility strategy over two chains of definition layers, written once and generic in the sink. It asserts that recording does not move the verdict, that the sink-off side's decision count is zero and the sink-on side's exact, and that a search-free replay sharing no code with the strategy re-derives every verdict. A trace with a swapped side or a dropped unfolding decision is refused by the replay.

```sh
cargo nextest run -p gandr-kernel-conversion-trace
RUSTFLAGS="--cfg anodized_panic" cargo nextest run -p gandr-kernel-conversion-trace
```

## The decision vocabulary

The vocabulary is at the grain of a proof search. `Unfold`, `Postpone`, `Force` and `ComparedShared` suffice for a heuristic unfolding strategy; `ReduceLeft`, `ReduceRight`, `ConstShortcut`, `Freeze`, `EtaExpand` and `NegativeSubgoal` add the side of every reduction, the branch taken at every choice point and the premise every refutation of a decomposition rests on, which a search-free replay needs. `Unfold` and `Postpone` are the two outcomes of one unfolding choice.

`NegativeSubgoal` carries the one premise a refutation of a decomposition rests on. A decomposition — two applications of one rigid head, or two formers compared child by child — is refuted by any one premise, and the rule that refutes it has that one premise and no other. A replay that met the decomposition with no position would have to try every premise until one refuted, which is search; the position names the premise, so the replay checks one. The alternatives were to emit the refuted premise alone and let the replay find where it fits, which is the same search moved one step, or to emit every premise's derivation, which would make a refutation as long as the agreement it contradicts. The reversal condition is a replay that can locate the refuted premise from the terms without trying the others, which would make the position redundant.

`ConversionSide` is a type. `Freeze` records which side froze and `EtaExpand` which side was applied to the fresh variable; `ReduceLeft` and `ReduceRight` carry the side structurally. A trace whose side is implicit cannot be replayed without searching for it, and search-free replay is what the seam exists to deliver.

## Static dispatch

`SinkActivity` follows the same discipline as the check-memo seam's `MemoActivity`: a conversion path branches on it at compile time, so under `NullSink` it builds no decision values. `TraceLog` is what a conversion run emits replay evidence through and what a differential counts its exercised path through; a suite that instantiates only `NullSink` can be green while reaching no recording code at all.

## Traces and equality

A trace individuates strictly more finely than convertibility: two convertible terms can carry different traces. A trace is replay evidence and never an equality, so comparing two traces decides something finer than conversion and would disagree on convertible inputs while raising nothing.

A trace records that two occurrences met, not that they agreed. A refutation and a proof can carry the same closing decision, and the replay recomputes the verdict from the terms.

## Exhaustive matching

No enum here is `#[non_exhaustive]`. The workspace does not publish, so the attribute would protect no external consumer while forcing a wildcard arm at every match and defeating exhaustiveness exactly where a new variant should break every consumer.

## Contract attributes

The `# Specification` prose is the statement of record; a `#[spec(...)]` attribute mirrors it wherever the clause is a runtime predicate over one call. Both shipped sinks carry them: `NullSink::record` keeps the count at zero and `NullSink::recorded_count` answers zero, while `TraceLog::record` grows the log by exactly one and `TraceLog::recorded_count` answers the number of decisions held. A null sink given storage, or a recording sink given a dropping append, breaks one of them.

The other blocks state what no attribute can check, and each says so in its own `- provides:` line. `SinkActivity`, `ConversionSide`, `ConversionDecision`, `NullSink` and `TraceLog` are data items, where a `#[spec]` invariant is never checked at construction. `TraceSink` and its three methods are declarations: a clause on one would require the trait itself to carry `#[spec]` and change what an implementor implements. `TraceLog::decisions` returns `impl Iterator`, which a closure-form postcondition cannot name.

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
