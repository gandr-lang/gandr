# gandr-core-session

Contractive binary session types, coinductive relations, and endpoint replay.

- [Synopsis](#synopsis)
- [References](#references)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Leaf boundary](#leaf-boundary)
- [Flat recursive syntax](#flat-recursive-syntax)
- [One relation engine](#one-relation-engine)
- [Opaque replay](#opaque-replay)
- [Specification evidence](#specification-evidence)
- [Integration boundary](#integration-boundary)
- [License](#license)

## Synopsis

**What.** Closed session types describe sends, receives, selections, offers, termination, and guarded recursion at one endpoint.

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

Consumers supply payload-type identities, payload digests, and endpoint-local moves. Identity assignment and payload-body validation belong to the consumer. The library uses `core` and `alloc` without a runtime, store, or dependency on another gandr crate.

The workspace-pinned `anodized` facade supplies executable specifications with default features disabled. `--cfg anodized_panic` across the build graph enables runtime checks; ordinary builds retain construction validation and replay refusals without specification instrumentation. No optional crate feature is required.

## Examples

```rust
use gandr_core_session::{Completion, Move, Node, NodeId, Payload, PayloadDigest,
    Session, ValueTypeId, replay};

let identity = ValueTypeId([1; 32]);
let protocol = Session::new(
    vec![Node::Send(identity, NodeId(1)), Node::End],
    NodeId(0),
)?;
let body = Payload { identity, digest: PayloadDigest([9; 32]) };
assert_eq!(replay(&protocol, &[Move::Send(body), Move::End]), Ok(Completion));
# Ok::<(), gandr_core_session::TypeError>(())
```

Run the protocol, relation, and refusal witnesses in both modes:

```sh
cargo nextest run -p gandr-core-session
RUSTFLAGS="--cfg anodized_panic" cargo nextest run -p gandr-core-session
```

The generator protocol is `mu t. &{next: !Y.t, stop: end}`. Its consumer selects `next`, receives a yield, and eventually selects `stop` and closes. `SeatEnd` is `?Dispatch. mu t. +{report: !Report.&{next: t, retire: end}, handoff: !Handoff.end}`. Independently stated peers witness duality and accepted runs for both protocols.

## Leaf boundary

**Choice.** The engine and monitor form a leaf crate over `core` and `alloc`. Replay consumers need neither a checker machine nor term syntax. The sole dependency is the workspace's specification facade, with its optional logic and arithmetic features disabled.

**Alternatives.** Placing the monitor in the checker couples replay to the typing machine. Placing the engine in the term crate gives declarative syntax a decision procedure. Handwritten assertions instead of `anodized` lose the workspace's shared specification representation and instrumentation modes.

**Reversal.** If every monitor consumer also requires the checker, the monitor can fold into that crate. Reading integrated term syntax would justify a term dependency. The specification facade follows the workspace's policy choice.

## Flat recursive syntax

**Choice.** A session owns a finite syntax tree in an index-addressed arena. A variable references an enclosing `Mu` node. Structural cycles, shared syntax nodes, unbound variables, missing nodes, and unreachable nodes are rejected; recursion uses variable edges only. A `Mu` body starts with an action or `End`, never another `Mu` or a variable. Clone and destruction do not recurse through ownership.

**Alternatives.** Pointer-owned recursive syntax makes clone and destruction depth-dependent. Shared syntax nodes require context-sensitive variable interpretation. The tree restriction gives each syntax occurrence one lexical scope while preserving recursive behavior through named back edges.

**Reversal.** A consumer requiring shared syntax or mutually recursive definitions needs an explicit scope representation and corresponding validation. Ownership remains flat.

## One relation engine

**Choice.** One root-driven greatest-fixpoint worklist decides two relations. Equivalence requires matching actions, opaque payload identities, label sets, and continuations up to unfolding. For `S <= T`, selections in `S` form a subset of those in `T`, while offers form a superset. Common continuations retain the left-to-right direction. Payload subtyping is identity equality. Duality swaps send/receive and select/offer once, preserves binding, then invokes equivalence.

Each unfolded state pair is visited at most once. Revisiting a pair closes a coinductive hypothesis without skipping fresh branch obligations. The finite pair space is bounded by the product of arena sizes. Contractivity bounds administrative unfolding to `Var -> Mu -> action`, so every decision terminates on admitted finite input.

**Alternatives.** Finite unfolding followed by syntax comparison incorrectly separates `mu t. !A.t` and `!A.mu t. !A.t`. Independent engines duplicate recursion and branch rules. Full-product elimination materializes unrelated pairs; it serves as an independent test oracle rather than the production algorithm.

**Reversal.** A codata-equivalence consumer would move the shared engine vocabulary to a layer both consumers depend on.

## Opaque replay

**Choice.** Replay checks one endpoint's recorded actions in order. Send and receive moves carry a `ValueTypeId` and a separate `PayloadDigest`. The monitor compares the type identity, preserves the digest in a refusal, and never opens or interprets a body. Labels select exactly one continuation. Closing requires an explicit `End` move at `End`; a truncated run is `IncompleteRun`. A non-close move at `End`, or any move after closure, is `ResumeAfterEnd`.

A refusal retains the first failed position, expected action, and observed move. The accepted path allocates no replay worklist and performs no search or backtracking.

**Alternative.** Fetching every body and checking it against the payload type requires a store and a judgment connecting stored values to type identities.

**Reversal.** If that judgment exists and replay runs beside the store, a typed body check can extend the monitor boundary.

## Specification evidence

Executable predicates check construction guards, exact dual-node correspondence, bounded unfolding, local relation obligations, branch inclusion and continuation direction, and replay result boundaries. They borrow inputs and capture scalar state rather than cloning arenas. A returned-value predicate cannot establish termination; the finite-state argument above states that obligation.

The independent elimination oracle exhausts 177 protocols: all send/receive words through length three over two payload identities, with finite and repeating tails, plus eight recursive choices over two labels. Every ordered pair is checked for equivalence, subtyping, and duality. Directed witnesses cover nested binders, width direction, first-refusal positions, opaque digests, and end boundaries. This is bounded evidence, not a proof over all arenas or a mutation score.

## Integration boundary

Live endpoint syntax and linear ownership belong to term syntax and the checker. This crate neither enforces endpoint linearity nor introduces a kernel session former. The monitor establishes endpoint-local skeleton conformance, not a kernel certificate. It does not correlate asynchronous peers, check FIFO delivery, validate bodies, or establish global deadlock freedom.

## License

Apache-2.0 WITH LLVM-exception; license texts are at the repository root.
