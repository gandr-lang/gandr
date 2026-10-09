# gandr-core-sequent

The sequent tier of the core: the command IL a call-by-push-value program is focused into, and the two-region store its abstract machine works over.

<!-- toc -->

- [Synopsis](#synopsis)
- [References](#references)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Covariables are indices](#covariables-are-indices)
- [Children before parents](#children-before-parents)
- [The polarity is the cell substrate's](#the-polarity-is-the-cell-substrates)
- [Two regions](#two-regions)
- [The store owns the cell protocol](#the-store-owns-the-cell-protocol)
- [License](#license)

<!-- tocstop -->

## Synopsis

**What.** `CommandArena` holds the three node families of a polarized sequent calculus — producers, consumers and commands — over the core language's vocabulary: a command `⟨p |ε c⟩` cuts a producer against a consumer at a polarity, constructor and destructor heads (`ConstructorTag`, `DestructorTag`) declare their own arities, and variables and covariables are de Bruijn indices. `Store` is the two-region store an environment machine over that IL runs in: an append-only heap of values, memo cells and environment chains, and a walkable region of continuation frames addressed by marks.

**Why.** A call-by-push-value term has its evaluation order implicit in its syntax; a command makes it explicit, as a cut whose two sides say what is sent where. That is the form an abstract machine steps without a search for the next redex, the form a cell rule from the rewriting stack already speaks, and the form whose frames an effect handler will later need to walk. Fixing the IL and the store first fixes the contract every later piece — focusing, the machine, the bridge from cells — is written against.

**How.** Every node is minted only over children the arena already holds, so the arena is acyclic by construction, and a `SequentWatermark` with `CommandArena::truncate_to` drops exactly what a refused build minted. Binders count outward, producers and covariables in separate index spaces, so equal inputs build identical nodes and no translation keeps a name supply. The store's heap values are immutable and shared by address; a thunk's memo cell is the only mutable state, and the store itself enforces its three-state protocol. Frames carry fresh serials, so a continuation mark over a frame that has since been popped is refused as stale rather than resumed into another continuation.

## References

- Pierre-Louis Curien and Hugo Herbelin. "The Duality of Computation." In _Proceedings of the Fifth ACM SIGPLAN International Conference on Functional Programming (ICFP '00)_, pages 233–243, September 2000. `doi:10.1145/351240.351262` — the command `⟨p | c⟩`, the binders `μα` and `μ̃x`, and the critical pair a cut's polarity resolves.
- Paul Downen and Zena M. Ariola. "A Tutorial on Computational Classical Logic and the Sequent Calculus." _Journal of Functional Programming_ 28 (2018), e3. `doi:10.1017/S0956796818000023` — data and codata as constructor applications and copattern objects, pattern matches and destructor frames, and the polarized cut.
- Paul Blain Levy. "Call-by-Push-Value: A Subsuming Paradigm." In _Typed Lambda Calculi and Applications (TLCA '99)_, Lecture Notes in Computer Science 1581, pages 228–243, 1999. `doi:10.1007/3-540-48959-2_17` — the value/computation split the IL's two polarities carry, and the thunk as the positive suspension of a computation.
- John Launchbury. "A Natural Semantics for Lazy Evaluation." In _Proceedings of the 20th ACM SIGPLAN-SIGACT Symposium on Principles of Programming Languages (POPL '93)_, pages 144–154, 1993. `doi:10.1145/158511.158618` — call-by-need as a heap of updatable suspensions, and the black hole a re-entered suspension shows.
- Peter O'Hearn, John Reynolds and Hongseok Yang. "Local Reasoning about Programs that Alter Data Structures." In _Computer Science Logic (CSL 2001)_, Lecture Notes in Computer Science 2142, pages 1–19, 2001. `doi:10.1007/3-540-44802-0_1` — the heap as a partial commutative monoid under disjoint union, and the frame rule the memo-cell suite states its four conditions in.

## Provided features

- `CommandArena`, `ProducerNode`, `ConsumerNode`, `CommandNode`, `PatternArm`, `CopatternArm`: the IL's three families, minted only over resolving children, refusing with `MintRefusal`. Witnesses: `il::tests::arena_allocates_and_reads_back`, `il::tests::minting_refuses_a_dangling_child`.
- `SequentWatermark` with `CommandArena::watermark` and `CommandArena::truncate_to`: the rollback a refused build takes. Witness: `il::tests::truncation_drops_exactly_the_later_nodes`.
- `ConstructorTag` and `DestructorTag` with their declared `ProducerArity`, `ConsumerArity` and, for a destructor, the polarity it observes. Witnesses: `il::tests::tag_arities_are_stable`, `il::tests::tag_consumer_arities_are_declared`.
- `CovariableIndex`: a covariable is a de Bruijn index, in a space of its own.
- `Store` with `HeapValue`, `HeapValueId` and `CellId`: the heap region of immutable values and nominal memo cells, with `ForceEntry` and `MemoState` the cell protocol, `StoreFault` its refusals. Witnesses: `store::tests::cell_write_back_is_shared_and_nominal`, `tests::csl_fibration::frame_preservation_under_forcing`, `tests::csl_fibration::nominal_identity_freshness_and_alias_coherence`, `tests::csl_fibration::black_hole_discipline_under_reentry`, `tests::csl_fibration::write_back_purity_caches_the_exact_probe_allocation`.
- `Environment`, `ValueScope`, `CovalueScope`: persistent environment chains in the heap region, read innermost first. Witness: `store::tests::environments_bind_innermost_first`.
- `Frame`, `ContinuationMark` and `Store::shrink_to`: the walkable frame region, marks refused once stale, and the decline of every forcing a shrink abandons. Witness: `store::tests::frames_shrink_to_a_mark`.

## Expected features

- **Addresses from the same arena or store.** An address is a position in one arena or store; one from another resolves to an unrelated node or to nothing. Lookups fail closed on a dangling address, and nothing checks provenance beyond that.
- **Truncation by the minting party.** `CommandArena::truncate_to` drops nodes, not references to them; the caller that takes a mark is the one that may truncate to it, after dropping every address minted since.

## Examples

Mint the command `⟨() |+ ★⟩` and read it back.

```rust
use gandr_core_sequent::CommandArena;
use gandr_core_sequent::CommandNode;
use gandr_core_sequent::ConstructorTag;
use gandr_core_sequent::ConsumerNode;
use gandr_core_sequent::ProducerNode;
use gandr_theory_cell_complexes::Polarity;

let mut arena = CommandArena::new();
let unit = arena.mint_producer(ProducerNode::Constructor {
    tag: ConstructorTag::Unit,
    producers: Box::from([]),
    consumers: Box::from([]),
})?;
let top = arena.mint_consumer(ConsumerNode::Top)?;
let cut = arena.mint_cut(Polarity::Positive, unit, top)?;
assert!(matches!(arena.command(cut), Some(CommandNode::Cut { .. })));
# Ok::<(), gandr_core_sequent::MintRefusal>(())
```

Run the tests:

```sh
cargo nextest run -p gandr-core-sequent
```

## Covariables are indices

A covariable is a `CovariableIndex` counting covariable binders outward, in an index space separate from the producer variables' `(zone, DeBruijnIndex)`. A `μα`, a thunk's body and a copattern arm's consumer arguments bind covariables; a `μ̃x`, a pattern arm's fields and a copattern arm's producer arguments bind producer variables. Nothing mints a name: α-equivalent IL is identical IL, a translation needs no counter threaded through it, and two runs over equal input build identical arenas. The producer index space is the core's own, so a core variable crosses into the IL unchanged.

The alternatives were named covariables drawn from a fresh-name supply, which is what the earlier implementation of this design had — every translation threading a counter and every comparison working modulo renaming — and a counter newtype standing in for a name, which keeps the supply and only types it. The choice reverses if a consumer of the IL needs to address a covariable by identity across terms, which no reader of a command does today.

## Children before parents

Every `mint_*` call checks that each child it is given resolves in the arena before appending, so each node's children were minted strictly before it, across all three families, and the arena is acyclic by construction. A `SequentWatermark` records the three family lengths; truncating to it keeps exactly the nodes minted before it, and since those name only earlier nodes, truncation never leaves a dangling child inside the arena. A build that mints several nodes and then refuses truncates to the mark it took on entry, so a refusal leaves the arena as it found it. The earlier implementation of this design returned an error from a half-built translation with its partial nodes still in the arena.

The alternatives were unchecked minting, which admits a forward reference and with it a cycle every walk would then need a depth limit against, and a staging buffer committed at the end of a build, which copies every node twice. The choice reverses if a measured build shows the per-child check dominating minting.

## The polarity is the cell substrate's

A cut's `ε` is `gandr_theory_cell_complexes::Polarity`, the type a cell pattern's cut carries. A cell elaborated by the rewriting stack and a command focused from a core term then cut at one polarity vocabulary, and reading a cell into a command copies its polarity rather than translating it. The alternative was a polarity of this crate's own with a conversion at the bridge, which is two names for one distinction. The choice reverses only if the core tier is reordered below the theory tier.

## Two regions

The heap region holds what outlives the frame that created it: values, memo cells and environment bindings, all append-only and addressed, so sharing is address sharing and a closure captures its environment by one address. The frame region holds the continuation as frames, in pushing order, each under a fresh `FrameSerial`. A `ContinuationMark` is a height together with the serial of the frame directly below it: binding a covariable binds a mark, and returning through one shrinks the region to it. A mark whose height has since been popped and re-pushed names a different serial and is refused with `StoreFault::StaleMark`. An update frame dropped by a shrink is a forcing abandoned mid-way, and its cell is declined back to unforced, so no black hole outlives the forcing that opened it.

The alternatives were continuations as heap-allocated closures, which makes every frame an allocation and leaves nothing for an effect handler to walk, and a single stack holding values and frames together, which ties a value's lifetime to a frame's. The choice reverses if a measured run shows the serial check on every return to dominate, at which point marks of a well-bracketed fragment can skip it.

## The store owns the cell protocol

A memo cell's only transitions are `Unforced → InProgress` by `Store::begin_force`, `InProgress → Forced` by `Store::write_back` and `InProgress → Unforced` by `Store::decline`; the store refuses any other write with `StoreFault::CellNotInProgress` and leaves the cell as it was. The earlier implementation of this design left legality to the machine's force protocol over a permissive cell. Enforcing it here makes the four conditions of the memo-cell suite properties of the store under any trace rather than only under the traces one machine produces, and the suite generates arbitrary traces accordingly. The alternative was the permissive cell, which is one check cheaper per transition. The choice reverses if a measured run shows the check to matter, which a three-state comparison is unlikely to.

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
