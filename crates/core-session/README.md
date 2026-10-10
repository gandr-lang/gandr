# gandr-core-session

Contractive binary session types, coinductive relations, and endpoint replay.

- [Synopsis](#synopsis)
- [References](#references)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Representation and relations](#representation-and-relations)
- [Replay and trust](#replay-and-trust)
- [Integration boundary](#integration-boundary)
- [License](#license)

## Synopsis

**What.** Closed session types describe sends, receives, selections, offers, termination, and guarded recursion at one linear endpoint.

**Why.** Recursive protocols need equality up to unfolding, directional subtyping, and a deterministic check of recorded endpoint actions.

**How.** A flat syntax arena resolves recursion through binder identities. One greatest-fixpoint worklist decides equivalence and subtyping; duality compares against one structural dual transformation. Replay advances one state per recorded move without relation search.

## References

- Simon Gay and Malcolm Hole, _Subtyping for Session Types in the Pi Calculus_, Acta Informatica 42, 2005, pp. 191–225, [doi:10.1007/s00236-005-0177-z](https://doi.org/10.1007/s00236-005-0177-z): contractive recursive types and visited-set coinductive subtyping.

## Provided features

- Send, receive, select, offer, end, recursion, and bound variables.
- Construction-time closure and contractivity validation.
- Equivalence, subtyping, and duality over opaque payload-type identities.
- Search-free replay with distinct direction, label, payload, incomplete-run, and resume-after-end refusals.

## Expected features

Consumers supply payload-type identities, payload digests, and endpoint-local moves. Identity assignment and payload-body validation belong to the consumer. The crate uses `core` and `alloc`, with no dependencies or optional features.

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

## Integration boundary

The session former belongs in `core-term`; the checker will use the relation engine at endpoint positions. This experiment keeps its closed vocabulary in this crate and reads no core terms, so the planned `gandr-core-term` dependency stays absent until that integration. The kernel gains no session former.

## License

Apache-2.0 WITH LLVM-exception; license texts are at the repository root.
