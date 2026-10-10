# gandr-core-session

Contractive binary session types, coinductive relations, and endpoint replay.

- [Synopsis](#synopsis)
- [References](#references)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Representation and relations](#representation-and-relations)
- [Replay and trust](#replay-and-trust)
- [Certified protocol identities](#certified-protocol-identities)
- [Integration boundary](#integration-boundary)
- [License](#license)

## Synopsis

**What.** Closed session types describe sends, receives, selections, offers, termination, and guarded recursion at one linear endpoint.

**Why.** Recursive protocols need equality up to unfolding, directional subtyping, and a deterministic check of recorded endpoint actions.

**How.** A flat syntax arena resolves recursion through binder identities. One greatest-fixpoint worklist decides equivalence and subtyping; duality compares against one structural dual transformation. Replay advances one state per recorded move without relation search.

## References

- The Univalent Foundations Program, _Homotopy Type Theory: Univalent Foundations of Mathematics_, 2013, [arXiv:1308.0729](https://arxiv.org/abs/1308.0729): equivalences as universe identity and transport, without adding a universal equality eliminator here.
- Simon Gay and Malcolm Hole, _Subtyping for Session Types in the Pi Calculus_, Acta Informatica 42, 2005, pp. 191–225, [doi:10.1007/s00236-005-0177-z](https://doi.org/10.1007/s00236-005-0177-z): contractive recursive types and visited-set coinductive subtyping.

## Provided features

- Send, receive, select, offer, end, recursion, and bound variables.
- Construction-time closure and contractivity validation.
- Equivalence, subtyping, and duality over opaque payload-type identities.
- Search-free replay with distinct direction, label, payload, incomplete-run, and resume-after-end refusals.
- Candidate finite relations exported by `relate`, checked independently as native `Path_U` or in-memory `Flow_U` evidence.
- Recorded-run transport through a freshly replayed session Flow and independently checked target monitor.

## Expected features

Consumers supply payload-type identities, payload digests, and endpoint-local moves. Identity assignment and payload-body validation belong to the consumer. Certified transport additionally requires native payload-code assignments. The crate uses `core` and `alloc` and depends on the existing `gandr-kernel-term` and `gandr-kernel-core` crates with default features disabled. It adds no external dependency or optional feature.

## Examples

Run the named generator, seat exchange, relation, and refusal witnesses:

```sh
cargo nextest run -p gandr-core-session
RUSTFLAGS="--cfg anodized_panic" cargo nextest run -p gandr-core-session
```

The generator protocol is `mu t. &{next: !Y.t, stop: end}`. Its consumer selects `next`, receives a yield, and eventually selects `stop` and closes.

The seat protocol is `?Dispatch. mu t. +{report: !Report.&{next: t, retire: end}, handoff: !Handoff.end}`. The operator holds its dual.

The finite oracle exhausts 177 generated protocols: send/receive words through length three over two payload identities, finite and repeating, plus recursive choices over two labels. All 31,329 ordered pairs are checked for equivalence, subtyping, and duality against independent greatest-fixpoint elimination. This bounded evidence supports the termination argument; it is not a proof over all arenas.

## Representation and relations

A session owns a finite syntax tree in an index-addressed arena. A variable references an enclosing `Mu` node. Structural cycles, shared syntax nodes, unbound variables, missing nodes, and unreachable nodes are rejected; recursion uses variable edges only. A `Mu` body must start with an action or `End`, not a variable or another `Mu`. This gives unfolding a bounded administrative path. Payload types are opaque identities, so payload subtyping is identity equality.

`S <= T` means an endpoint implementing `S` can replace one promising `T`. Selections in `S` form a subset of selections in `T`; offers in `S` form a superset of offers in `T`. Common continuations retain that direction. Equivalence requires equal label sets and matching actions and payload types. Duality swaps send/receive and select/offer once, then invokes equivalence.

The engine visits each reachable pair of unfolded states at most once. A pair revisited along recursion closes a coinductive obligation; every fresh pair still checks all required branches. Finite arenas bound the pair space by the product of their sizes. Recursive unfolding copies no syntax. A flat arena also makes clone and destruction independent of recursion depth.

The alternative, comparing syntax after a finite unfolding, distinguishes `mu t. !A.t` from `!A.mu t. !A.t` incorrectly. Independent relation engines would duplicate the recursion and branch rules. If codata gains a consumer, the common engine vocabulary can move to a shared layer.

## Replay and trust

Replay observes one endpoint's moves in order. Send and receive moves carry both a payload-type identity and a payload digest. Replay compares the type identity; it neither opens nor interprets the digest. Labels choose exactly one continuation. Closing requires an explicit `End` move at `End`; exhausting a run before that move is `IncompleteRun`. Any action after closure, or any non-close action at `End`, is `ResumeAfterEnd`.

A refusal identifies the move position, expected action, and observed move. Replay retains one endpoint state and traverses the recorded moves once. Label lookup selects a branch directly; no protocol search or backtracking occurs.

This monitor is a conformance check against a type the checker will have checked. Its result is not a certificate admitted by the kernel. Endpoint-local replay does not correlate asynchronous peers or check FIFO delivery, payload bodies, endpoint ownership, or global deadlock freedom.

## Certified protocol identities

`relate` exposes the same greatest-fixpoint engine's visited relation as untrusted data. `certified::encode` replaces opaque payload identities with slots into a native payload-code telescope; it preserves every graph position. Native `Value::SessionPath` and `Flow::Session` consume that data through the kernel's independent finite replay. The former requires equal labels; the latter checks directional selection/offer inclusions. A deleted continuation pair, wrong action, unguarded code, missing payload equality or wrong classifier family refuses. Neither an engine decision nor a stored Flow is an admission receipt.

`certified::transport` re-forms a direct session Flow, verifies both complete monitor/code bindings, replays the source run, maps moves through supplied pairs, and replays the result against the target monitor. Labels and digest bytes remain unchanged; payload identities are mapped to the target protocol. Bodies remain opaque: a native payload path certifies code identity, not that this monitor has transformed or validated a digest's body. The arena watermark is restored on either verdict.

The widened `SeatEnd'` adds `pause : !Report.turn` to the recursive selection. Both the two-report-retire run and the handoff run transport unchanged. A widened run using `pause` refuses against the original protocol in reverse order; the width simulation cannot serve as a `Path_U`. Offer width has the opposite inclusion, so a source-only offered label also refuses run transport. Subtyping is not permission to migrate every arbitrary local trace from a peer that violates the target promise.

**Choice.** Reuse the native code, admission and Flow rules rather than duplicate a trusted checker in this producer crate. The kernel does not depend on this engine. Raw relation search stays here; replay only checks supplied pairs and their local obligations. **Reversal.** A separate protocol universe can replace this shared-code representation if its cross-stratum rules require a different identity or ordering discipline; the finite witnesses do not establish that the shared universe is conservative.

`ValueType::Session` reflects a closed finite protocol graph in the value universe. Formation checks one rooted syntax tree, lexical recursive binders, observable guards, every payload slot, and the ordinary universe formation of a Unit-terminated payload telescope. Payloads may be native value codes, including higher-level codes and List; an ambient term binder cannot close an open session payload. Mu and variable edges stay inside the finite graph. There are no endpoint or channel value constructors.

`session::obligations` replays the supplied observable root pair and every supplied relation pair. It resolves at most Var → Mu → action; it does not construct a relation, search for a partner or unfold to a fixed point. Bisimulation requires identical action directions, equal label sets and related continuations. Simulation requires source selections ⊆ target selections and target offers ⊆ source offers. Payload codes must convert structurally or be named by a supplied native `Path_U` obligation; the ordinary checking machine checks the complete proof tuple in an empty context. A supplied payload path is subject to that path family's own formation rules, not accepted as an opaque assertion.

`Value::SessionPath` introduces native `Path_U` evidence and admits through `Environment::add_decl`. `Flow::Session` extends the existing in-memory directed rule language. Every Flow consumer rechecks its codes, simulation and payload proofs. Family tags never coerce, a reversed width relation refuses, and ordinary CBPV Flow lowering returns `RecordedRunRequired`. `gandr-core-session::certified::transport` supplies the separate recorded-run consumer and checks target-monitor acceptance. No runtime endpoint enters the kernel through that consumer.

The same-call memo witness checks a good session path followed by identical translator syntax with a missing relation. Conversion may erase relation pairs, but admission still refuses the second path: content keys bind the full evidence. The [six memo binding conditions](../kernel-core/README.md#memo-binding-conditions) remain unchanged. Session-specific trusted code is finite formation, local relation replay and the ordinary native traversal/encoding clauses; relation search and move mapping remain outside the kernel.

**Cross-stratum seam.** Session codes and first-order codes inhabit one value-code universe. The protocol's ordered interactions are retained in graph continuations, and the groupoidal Path and directed Flow families remain distinct. Finite replay establishes the stated relation over action skeletons; it does not establish conservativity when passing to components across an ordering/no-ordering boundary, a generic session-value transport law, or a combined-universe metatheorem.

**Choice.** A native finite graph plus supplied relation reuses universe formation, payload paths, admission and content support. Keeping protocols entirely outside the kernel cannot supply native protocol-code identity; granting the producer's Boolean decision authority would move relation search into the trusted base. **Reversal.** A separate protocol stratum is warranted if its ordering or coherence obligations do not admit conservative shared-universe rules. Endpoint ownership, asynchronous peer correlation, FIFO delivery and infinite-run productivity remain outside these finite judgements.

## Integration boundary

Live endpoint syntax, ownership and typing belong to `core-term` and `core-checker`. This crate reads no core terms. The kernel reflects finite session protocols as codes beside first-order codes in the value universe, solely to check type-identity evidence; it gains no endpoint or channel values. Recorded skeleton transport is a monitor-level operation, not a CBPV session-value eliminator. Ordinary Flow lowering refuses a session introduction as `RecordedRunRequired`. Native declaration persistence includes session codes and Path evidence; Flow certificates retain the existing in-memory representation.

## License

Apache-2.0 WITH LLVM-exception; license texts are at the repository root.
