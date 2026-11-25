# gandr-theory-graphs

The graph theory gandr's grammar stands on: the operator-precedence DAG, the walk machine a grammar's tiles are closed under, and the graph algorithms both read.

<!-- toc -->
- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Where the detail lives](#where-the-detail-lives)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** Two halves over one dense node vocabulary. The grammar half is the named precedence DAG (`PrecSpec`, `PrecDag`, `Prec`, `Assoc`, `Bound`) and the declarative walk index (`WalkSpec`, `WalkIndex`, `Walk`, `Swing`, `Dir`, `End`). The algorithm half is the part of a graph library the grammar reads, over one boundary, `EdgeSource`: `cycle_witness`, `reachability` and `condensation`. `Fnv64` is the fixed FNV-1a accumulator every stable fingerprint here and in the consumers is computed with. The crate is `no_std` and depends on `core`, `alloc` and petgraph.

**Why.** A tile-based parser asks two questions of a grammar on every token: how two precedence groups compare, and which walks connect two adjacent tiles. Both answers are fixed once the grammar is, so they are precomputed into lookup tables at build time, and the tables are fingerprinted so a cached parse is keyed by the grammar that produced it. The grammar's closing-class derivation reads the strongly-connected-component condensation, and the precedence DAG reads cycle evidence and reachability; those three algorithms are what the grammar needs from a graph library.

**How.** `PrecDag::build` refuses a cyclic tighter-than relation with a closed cycle as evidence and otherwise precomputes the transitive closure, so a comparison is a binary search in one sorted row. `WalkIndex::build` closes a walk machine's direct walks transitively through intermediate ends by iterative breadth-first search, keeps the valid and minimal walks of each row in the paper's canonical order, and projects them into the equal, less and greater queries and the molds-by-label table. Every algorithm validates its input once into sorted, deduplicated adjacency rows, so an out-of-bounds successor is a typed refusal and every result is independent of successor order and duplicate edges.

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

## Where the detail lives

Mechanism, decisions with their alternatives and reversals, and witnesses live in the rustdoc beside the code:

| Topic | Module |
| ----- | ------ |
| Scope, determinism, specification evidence, references | [`src/lib.rs`](src/lib.rs) |
| The graph library and its algorithms | [`algorithms`](src/algorithms.rs) |
| The precedence DAG | [`prec`](src/prec.rs) |
| The walk index | [`walk`](src/walk.rs) |
| Fingerprints | [`fingerprint`](src/fingerprint.rs) |

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
