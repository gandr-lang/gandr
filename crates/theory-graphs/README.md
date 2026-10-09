# gandr-theory-graphs

The graph theory gandr's grammar stands on: the operator-precedence DAG, the walk machine a grammar's tiles are closed under, and the graph algorithms both read.

<!-- toc -->

- [Synopsis](#synopsis)
- [References](#references)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Scope](#scope)
- [Graph library](#graph-library)
- [Precedence DAG](#precedence-dag)
- [Walk index](#walk-index)
- [Fingerprints](#fingerprints)
- [License](#license)

<!-- tocstop -->

## Synopsis

**What.** Two halves over one dense node vocabulary. The grammar half is the named precedence DAG (`PrecSpec`, `PrecDag`, `Prec`, `Assoc`, `Bound`) and the declarative walk index (`WalkSpec`, `WalkIndex`, `Walk`, `Swing`, `Dir`, `End`). The algorithm half is the part of a graph library the grammar reads, over one boundary, `EdgeSource`: `cycle_witness`, `reachability` and `condensation`. `Fnv64` is the fixed FNV-1a accumulator every stable fingerprint here and in the consumers is computed with. The crate is `no_std` and depends on `core`, `alloc` and petgraph.

**Why.** A tile-based parser asks two questions of a grammar on every token: how two precedence groups compare, and which walks connect two adjacent tiles. Both answers are fixed once the grammar is, so they are precomputed into lookup tables at build time, and the tables are fingerprinted so a cached parse is keyed by the grammar that produced it. The grammar's closing-class derivation reads the strongly-connected-component condensation, and the precedence DAG reads cycle evidence and reachability; those three algorithms are what the grammar needs from a graph library.

**How.** `PrecDag::build` refuses a cyclic tighter-than relation with a closed cycle as evidence and otherwise precomputes the transitive closure, so a comparison is a binary search in one sorted row. `WalkIndex::build` closes a walk machine's direct walks transitively through intermediate ends by iterative breadth-first search, keeps the valid and minimal walks of each row in the paper's canonical order, and projects them into the equal, less and greater queries and the molds-by-label table. Every algorithm validates its input once into sorted, deduplicated adjacency rows, so an out-of-bounds successor is a typed refusal and every result is independent of successor order and duplicate edges.

## References

- David Moon, Andrew Blinn, Thomas J. Porter, and Cyrus Omar. "Syntactic Completions with Material Obligations." _Proceedings of the ACM on Programming Languages_ 9, OOPSLA2 (October 2025). `doi:10.1145/3763182`; preprint `arXiv:2508.16848` — the walk, swing and stance vocabulary, the validity and minimality filters and canonical order of § 4.1, and the figure-33 fragments the walk suite pins.
- Nils Anders Danielsson and Ulf Norell. "Parsing Mixfix Operators." In _Implementation and Application of Functional Languages (IFL 2008)_, Lecture Notes in Computer Science 5836, pages 80–99, 2011. `doi:10.1007/978-3-642-24452-0_5` — the precedence-graph presentation the precedence DAG follows: groups related by a tighter-than order that need not be total.
- A. B. Kahn. "Topological Sorting of Large Networks." _Communications of the ACM_ 5, 11 (November 1962), pages 558–562. `doi:10.1145/368996.369025` — the ready-set topological sort the DAG's linear extension is, with its tie-break fixed to the smallest ready group.
- Micha Sharir. "A Strong-Connectivity Algorithm and Its Applications in Data Flow Analysis." _Computers & Mathematics with Applications_ 7, 1 (1981), pages 67–72. `doi:10.1016/0898-1221(81)90008-0` — the two-pass strongly-connected-component algorithm petgraph's condensation runs.
- Glenn Fowler, Landon Curt Noll, Kiem-Phong Vo, Donald Eastlake 3rd, and Tony Hansen. "The FNV Non-Cryptographic Hash Algorithm." RFC 9923, February 2026. `doi:10.17487/RFC9923` — the 64-bit FNV-1a parameters `Fnv64` fixes, pinned against the published test vectors.

## Provided features

- `PrecSpec`, `PrecDag`, `Prec`, `Assoc`, `Bound`: named groups with an associativity each, a tighter-than relation refused when cyclic, `lt`, `gt`, `eq` and `comparable` over groups, the same four over groups bounded by a virtual bottom and top, a deterministic linear extension, and a stable fingerprint. Witnesses: `tests::prec::prec_dag_contract`, `tests::prec::prec_cycle_witness_contract`, `tests::prec::virtual_bound_comparisons`, `tests::prec::prec_integer_chain_oracle`, `tests::prec::deterministic_linear_extension_uses_smallest_ready_id`, `tests::prec::fingerprint_stream_is_pinned`.
- `PrecDagError`, `PrecSpecError`, `PrecCycle`: every refusal as a typed value — a cycle with its closed witness, an invalid graph, an inconsistent internal state, a duplicate or unknown group, more groups than a 16-bit index names. Witnesses: `tests::prec::prec_spec_size_and_boundary_contract`, `tests::prec::duplicate_edge_canonicalization_and_invalid_edges`, `tests::prec::capacity_beyond_u16_is_typed`.
- `WalkSpec`, `WalkIndex`, `Walk`, `Swing`, `SwingArc`, `WalkSym`: a walk machine built from direct walks and generating swing arcs, closed into canonical rows, with the `walks`, `eq`, `lt`, `gt` and `molds` projections and a fingerprint independent of insertion order. Witnesses: `tests::walk::figure_33_fragments_are_literate_external_oracle`, `tests::walk::section_4_1_filters_and_canonical_order_are_observable`, `tests::walk::query_orientation_filters_direct_rows`, `tests::walk::molds_projection_is_reachable_canonical_and_label_indexed`, `tests::walk::insertion_permutation_duplicate_canonicalization_and_fingerprint_are_stable`, `tests::walk::small_chain_keyings_agree_under_permuted_insertion`.
- `WalkBuildError`: a refused walk, arc, machine or index — an empty swing, a non-alternating walk, a zero cap, an arc that neither emits nor continues, a walk past the cap, an overflowed count. Witnesses: `tests::walk::construction_guards_refuse_malformed_shapes`, `tests::walk::cyclic_outer_closure_terminates_and_cap_errors_are_typed`.
- `EdgeSource`, `cycle_witness`, `reachability`, `condensation`: the dense-graph boundary and the three algorithms over it, each total, each refusing an out-of-bounds successor by name, none recursive. Witnesses: `tests::algorithms::cycle_witness_names_the_back_edge`, `tests::algorithms::witness_exists_exactly_when_the_closure_has_a_loop`, `tests::algorithms::reachability_agrees_with_the_closure_matrix`, `tests::algorithms::condensation_agrees_with_mutual_reachability`, `tests::algorithms::out_of_bounds_edges_are_refused_by_name`, `tests::algorithms::deep_chain_runs_without_recursion`.
- `Fnv64`, `Fingerprint`: the fixed accumulator and its result. Witnesses: `fingerprint::tests::published_vectors_pin_the_parameters`, `fingerprint::tests::words_absorb_little_endian`.

## Expected features

- **A dense graph.** An algorithm reads a graph through `EdgeSource`: a node bound and, per node below it, its successors as `NodeId`s. A successor at or past the bound is refused, never read.
- **A symbol vocabulary with stable keys.** A walk machine is generic over `WalkSym`, which names the nonterminal, stance, sort, bounds, label and mold types and maps each nonterminal and stance to a `WalkSymbolKey`. The keys are what the fingerprint hashes, so they are stable across runs and processes: an interned id or a declared ordinal, never an address or a process-random hash.

## Examples

Declare two groups, relate them, and compare.

```rust
use gandr_theory_graphs::Assoc;
use gandr_theory_graphs::PrecDag;
use gandr_theory_graphs::PrecSpec;

fn example() -> Result<(), Box<dyn core::error::Error>> {
    let mut spec = PrecSpec::new();
    let additive = spec.insert("additive", Assoc::Left)?;
    let multiplicative = spec.insert("multiplicative", Assoc::Left)?;
    spec.add_edge(multiplicative, additive)?;
    let dag = PrecDag::build(&spec)?;
    assert!(bool::from(dag.lt(additive, multiplicative, Assoc::Non)));
    assert!(bool::from(dag.gt(additive, additive, Assoc::Left)));
    Ok(())
}
```

Run the tests:

```sh
cargo nextest run -p gandr-theory-graphs
```

## Scope

The algorithm half carries what the grammar reads and nothing else: cycle evidence and reachability for the precedence DAG, condensation for the closing-class derivation. The DAG's linear extension is its own Kahn order, so no general topological sort is exposed. Dominators, shortest paths, simple-path enumeration, transitive reduction, partition refinement and an adjacency fingerprint are absent because no consumer reads them; an algorithm with no reader is maintained surface with no contract a consumer depends on. The walk index needs no partition refinement: its rows are canonicalised by key, not by bisimulation.

The determinism probe — a binary that prints the byte-level projection of every public result while scratch allocation is perturbed — and the benchmarks are a lateral, outside this crate. Determinism is held here by construction and by test: every tie is broken by the smallest dense identifier, every collection the results are read from is ordered, no hasher is process-random, and the pinned fingerprints and permuted-insertion tests fail on any drift.

## Graph library

The condensation runs on petgraph, version `0.8.3`, every feature off; `condensation` and its `kosaraju_scc` build under `no_std` without `std`, `graphmap`, `stable_graph` or `matrix_graph`. petgraph is reached only through this crate and no public signature names one of its types: a graph enters as an `EdgeSource` and every result is in dense `NodeId`s and `ComponentIndex`es, so a consumer inherits no petgraph type and the library can change behind the boundary. The graph is built with `try_add_node` and `try_add_edge`, so an index-space overflow is `GraphValidationError::NodeCountTooLarge` or `EdgeCountTooLarge`, never petgraph's panic. The condensation is taken with `make_acyclic` off and its self-loops and parallel edges removed by one sort and deduplication afterwards, which avoids the per-edge neighbour scan `make_acyclic` performs; components are then renumbered in order of their smallest member, each member list ascending.

- Alternatives: a hand-written Kosaraju or Tarjan pass loses to a maintained, widely used implementation for an algorithm the crate has no reason to own; `pathfinding` loses because it has no `no_std` build and brings six required dependencies for one algorithm.
- Reversal: an advisory against petgraph, an unmaintained mark, or a `no_std` condensation that a smaller crate provides.

petgraph `0.8.3` resolves `hashbrown` `0.15` while its `indexmap` resolves `hashbrown` `0.17`; `clippy.toml` allows that one duplicate, with the release that unifies them as its removal condition.

Cycle evidence and reachability are this crate's own iterative depth-first searches over the validated rows: cycle evidence is the closed walk through the back edge that closes a cycle, where petgraph's cycle detection reports at most one node on it, and reachability runs one search per source, O(n·(n + e)) for the whole relation, where a pairwise path query would be O(n²·(n + e)).

## Precedence DAG

A group's associativity is one of three values, `Assoc::Left`, `Assoc::Right` and `Assoc::Non`. A lookup of an unknown group returns `Option<Assoc>`, so `Non` is a value of its own rather than an absent associativity, which would nest a lookup into `Option<Option<Assoc>>`. A group relates to itself only by the relation its associativity names, and only when the caller asserts the same associativity: a left-associative group is greater than itself under `Assoc::Left`, a right-associative one less than itself under `Assoc::Right`, a non-associative one equal to itself under `Assoc::Non`. `comparable` asks only whether two groups are ordered at all, so it holds for every known group with itself.

`PrecDag::build` returns `PrecDagError`, which keeps three refusals apart: `Cycle` with a closed witness naming every group on the cycle, `Graph` for a specification whose relation fails validation, and `Inconsistent` for an internal state that contradicts itself. A cycle is never reported with an empty witness.

The linear extension is Kahn's order with the smallest ready group taken first, so it is one fixed order for a given specification, and `linear_extension` borrows it. Comparisons read the precomputed closure: each group's row lists, ascending, the groups strictly looser than it, so `lt` and `gt` are one binary search.

## Walk index

A walk alternates swings — non-empty runs of nonterminals — with the stances between them, starting and ending on a swing. A machine supplies walks directly between two ends, and generates them from swing arcs: an arc extends a swing, crosses a stance into a new swing, or emits the walk so far at an end, from a seed per direction and source. The swing arcs are indexed by source once per build. Swing closure keys a visited state on its sort and bounds; `WalkIndex::compare_seen_keys` reports whether keying on the sort alone would change any row, the diagnostic that shows the bounds part of the key is needed.

The outer closure chains direct walks through intermediate stance ends by breadth-first search, never re-enters an end its path has passed, and drops a prefix that is already not minimal, since no extension makes it minimal again. Every row then keeps the walks that pass § 4.1's validity and minimality filters, one per canonical key, sorted by the canonical order; a cap on the alternating length makes an over-long walk `WalkBuildError::ChainLengthExceeded` rather than a silent truncation.

The `eq`, `lt` and `gt` projections are the direct rows filtered by query kind; `molds` lists, per label, the molded ends reachable from the root in canonical order.

## Fingerprints

`Fnv64` is 64-bit FNV-1a with the published offset basis and prime, and multi-byte words are absorbed little-endian, so a fingerprint is the same on every platform. A fingerprint keys a cache and is no proof of equality.

- `PrecDag::fingerprint` hashes the group count, then per group its name's length, its name and its associativity tag (`Non` 0, `Left` 1, `Right` 2), then the edge count and each edge as two 16-bit indices, in canonical edge order. Reordered or repeated edges agree; a renamed group, a changed associativity or a changed relation each move it.
- `WalkIndex::fingerprint` hashes the frame `gandr.walk.v1` and the cap, the direct rows under tag `D`, the transitive rows under tag `T`, then under tag `M` each label's molds by ordinal, with every symbol written as its stable key. Two machines with the same rows have the same fingerprint, whatever their insertion order.

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
