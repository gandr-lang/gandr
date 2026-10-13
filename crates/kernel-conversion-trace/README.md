# gandr-kernel-conversion-trace

The conversion-decision seam between an untrusted convertibility engine and the certified kernel: the decision vocabulary and a statically dispatched sink.

<!-- toc -->

- [Synopsis](#synopsis)
- [References](#references)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Where the detail lives](#where-the-detail-lives)
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

- `ConversionDecision<Id>`: the vocabulary — `ReduceLeft`, `ReduceRight`, `ConstShortcut`, `Unfold`, `Postpone`, `Freeze`, `EtaExpand`, `ReturnEta`, `Reassociate`, `Force`, `ComparedShared`, `Decompose`, `NegativeSubgoal`.
- `ConversionDecision::map`: the same decision over another anchor, how a trace crosses from the engine's identifiers to a consumer's.
- `SubgoalPosition`: which premise of a decomposition a refutation names, counted in an order both consumers derive from the terms.
- `ConversionSide`: which leg of the comparison a one-sided decision acts on.
- `TraceSink<Id>`: the emit seam, with an associated `SinkActivity` constant.
- `NullSink`: zero-sized and constant, with no recording state and no dynamic dispatch.
- `TraceLog<Id>`: the recording sink, a flat vector read back in recording order, with `DecisionCount` for exercised-path assertions.

## Expected features

- **A strategy and a replay.** The consumer supplies the convertibility engine that records into a sink and the sequential rechecker that consumes a `TraceLog`. In this workspace the engine is `gandr-core-nbe`'s conversion machine, which emits its winning derivation through `TraceSink<TraceNode>` in preorder, and the rechecker is `gandr-kernel-core`'s `replay`, which reads the decisions with their identifiers mapped to the constants they name. The crate's tests carry a miniature of each as the two sides of their differential.
- **An identifier space.** Every `Id` is meaningful in the consumer's own arena or value space, and the consumer keeps a trace within the scope in which its identifiers resolve.
- **A lifetime.** Raw engine identifiers remain within the arena that gives them meaning. This crate defines no serialization contract; a consumer may persist remapped decisions only under its own framing and identifier policy.
- **`--cfg anodized_panic` for enforcement.** Built with this `cfg` across the whole dependency graph, the `#[spec]` attributes check their clauses at runtime and panic on a violation. The enforcing test lane sets it.

## Examples

`tests/differential.rs` runs a miniature convertibility strategy over two chains of definition layers, written once and generic in the sink. It asserts that recording does not move the verdict, that the sink-off side's decision count is zero and the sink-on side's exact, and that a search-free replay sharing no code with the strategy re-derives every verdict. A trace with a swapped side or a dropped unfolding decision is refused by the replay.

```sh
cargo nextest run -p gandr-kernel-conversion-trace
RUSTFLAGS="--cfg anodized_panic" cargo nextest run -p gandr-kernel-conversion-trace
```

## Where the detail lives

The vocabulary's grain, the refuted premise and the side discipline are in [`src/decision.rs`](src/decision.rs); static dispatch, traces and equality, portable path dialogues, exhaustive matching and the specification attributes are in [`src/lib.rs`](src/lib.rs); the sinks' obligations are on their items in [`src/sink.rs`](src/sink.rs).

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
