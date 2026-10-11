# gandr-theory-dynamic-graphs

Insertion-only topological orders and feasible valuations for standing graphs.

## Synopsis

**What.** `AcyclicityMaintenance` admits a directed edge exactly when it preserves acyclicity. `PotentialMaintenance` admits a weighted constraint `value(target) >= value(source) + offset` when the standing system remains feasible. Both retain their state across calls and return a closed cycle on semantic refusal.

**Why.** A consumer accumulating constraints can reuse a maintained order or valuation instead of traversing its entire admitted graph after every offer. A consumer rebuilding a graph for one query has no standing state to reuse.

**How.** The order structure uses a Pearce–Kelly bounded forward/backward search, sorting affected sets by their standing order and relocating them into the slots they already occupied. The valuation structure propagates strict raises along admitted constraints and journals each affected node's original value. A positive-cycle refusal or arithmetic failure restores that journal. Search and relocation buffers are retained across offers. The crate is `no_std` with `alloc`; searches use explicit work stacks rather than recursion.

## References

- David J. Pearce and Paul H. J. Kelly. “A Dynamic Topological Sort Algorithm for Directed Acyclic Graphs.” _ACM Journal of Experimental Algorithmics_ 11, article 1.7. [doi:10.1145/1187436.1210590](https://doi.org/10.1145/1187436.1210590). The bounded order-repair design; this API supports insertion only.
- [`gandr-theory-orders`](../theory-orders/README.md): stable order positions and label comparisons.
- [`gandr-theory-graphs`](../theory-graphs/README.md): graph identities, closed-cycle evidence, and the independent batch traversal used by the differential witnesses.

## Provided features

- `insert_edge`, `compare`, `nodes_in_order`, and `EdgeSource`: dense nodes are created on demand; duplicate edges are retained once; cycle-closing offers are refused without changing admitted edges or order. `compare` reports an unknown node as `MaintenanceError::NodeCapacity`, not an unordered comparison.
- `insert_constraint`, `value`, and `valuation_is_feasible`: signed offsets distinguish positive cycles from satisfiable zero/negative cycles. Distinct offsets on the same endpoints are distinct constraints. A missing node is `Maybe::Absent(PotentialAbsence::UnknownNode(node))`, distinct from a zero-valued node.
- `CycleWitness`: an offered edge plus an admitted path closing it. For the weighted structure, the caller retains its offset-labelled constraints; the graph witness contains node/edge identities, not offset labels.
- Saturating telemetry counts offers, refusals, repairs, visited/relocated nodes, raises, and examined constraints. These are declared operation projections, not timings or a complete cost model: they omit adjacency duplicate scans, sorting, allocation, and order-label maintenance.

## Expected features

Nodes have dense `u32` identities. Naming an unseen node creates all intervening nodes. `u32::MAX` cannot be a node identity because its required node count is unrepresentable. Offsets and potentials use checked `i64` arithmetic: a mathematically feasible system can still return `ValueOverflow`. On a propagation failure, previously held values and constraints are restored; nodes newly created by the offer remain present at zero. Allocation failure follows the allocator's behavior.

Neither structure deletes edges, rolls back admitted prefixes, or supports a changing node interpretation. Acyclicity alone is exact for strictly positive offsets. Allowing zero or negative offsets makes it conservative: a zero-sum cycle can be feasible with unequal potentials.

## Design decisions

Use bounded order repair for a standing insertion stream, rather than batch traversal after every offer. Reconsider the maintenance strategy when measured adjacency scans, sorting, or order-label work dominate its affected-region work. The single-shot and repeated-query witnesses compare explicit operation projections; they do not establish a universal runtime crossover.

Keep weighted propagation separate from topological-order maintenance. Refusing every cycle loses feasible systems as soon as offsets can be nonpositive. A node-only relaxation budget is unsound: arbitrarily many parallel offsets can successively raise one target on an acyclic graph. Propagation instead terminates over improving admitted paths; a nonpositive admitted cycle cannot improve a path, and reaching the new constraint's source detects a positive cycle. The journal records each node's original value once. Reconsider the work-list strategy if a consumer's measured path count requires a stronger complexity guarantee.

Directed composition remains a **batch** consumer. Its seam-flow graph is rebuilt for each certificate pair and restricted to the current left join; successive calls are not insertion-only extensions of one graph. [`the_gates_own_graph_streamed_incrementally_reproduces_its_verdict`](../theory-decomposition-spaces/tests/composition.rs) compares the same characterized graph in forward and reverse arrival order against the batch gate, without making maintenance a production dependency. Switch only when a consumer actually retains one graph or accumulates constraints monotonically across calls.

## Examples and evidence

[`a_standing_graph_preserves_prefixes_across_calls`](tests/standing.rs) holds a public graph through local repairs, a cycle refusal, and a later accepted edge, then checks the exact order, retained adjacency, and comparison errors. The same integration target exercises propagation-overflow rollback, parallel offsets exceeding a node-only budget, and refusal of an unrepresentable node count. It also exhausts 19,683 three-offer systems over three nodes and offsets −1, 0, and 1 against independent Bellman–Ford sweeps, checking positive-cycle evidence and unchanged values after refusal.

The graph differential rebuilds an independent batch oracle for every offer, validates refusal walks, and checks every retained prefix. Its property generator uses a fixed seed and persistent failure cases. Three deterministic stream families exercise hidden acyclic prefixes, adversarial back edges, and interleaving. The offset probe compares both structures only through their first disagreement, while they still share an admitted prefix; injected wrong verdicts check that the observers reject the intended fault class.

### Compatibility floor

All 26 named rows are present. The five public standing-state witnesses are additional. The composition comparison row belongs to `theory-decomposition-spaces` and is not counted twice.

| Test | Location |
| ---- | -------- |
| `an_edge_the_order_witnesses_is_admitted_without_moving_anything` | `maintenance::tests` |
| `a_violating_edge_is_repaired_locally` | `maintenance::tests` |
| `a_cycle_closing_edge_is_refused_with_its_walk` | `maintenance::tests` |
| `a_self_loop_is_refused` | `maintenance::tests` |
| `a_repeated_edge_is_admitted_once` | `maintenance::tests` |
| `the_maintained_order_is_topological` | `maintenance::tests` |
| `a_corrupted_order_is_caught_by_the_invariant` | `maintenance::tests` |
| `a_refusal_leaves_the_structure_usable` | `maintenance::tests` |
| `unaffected_nodes_between_the_endpoints_keep_their_slots` | `maintenance::tests` |
| `a_zero_weight_cycle_is_satisfiable` | `potential::tests` |
| `a_positive_weight_cycle_is_refuted` | `potential::tests` |
| `a_negative_offset_cycle_is_satisfiable` | `potential::tests` |
| `a_refuted_offer_restores_the_valuation` | `potential::tests` |
| `a_self_constraint_is_refuted_only_when_positive` | `potential::tests` |
| `the_valuation_stays_feasible` | `potential::tests` |
| `a_corrupted_valuation_is_caught_by_the_invariant` | `potential::tests` |
| `incremental_verdicts_equal_the_batch_answer` | `dynamic_graphs::differential::tests` |
| `every_stream_family_is_drift_free` | `dynamic_graphs::differential::tests` |
| `the_differential_catches_a_seeded_wrong_verdict` | `dynamic_graphs::differential::tests` |
| `a_single_shot_graph_costs_more_than_one_batch_check` | `dynamic_graphs::differential::tests` |
| `amortized_cost_is_below_batch_recheck` | `dynamic_graphs::differential::tests` |
| `strictly_positive_offsets_leave_the_order_structure_exact` | `dynamic_graphs::probe::tests` |
| `a_zero_offset_breaks_the_agreement` | `dynamic_graphs::probe::tests` |
| `acyclicity_refuses_a_superset_of_what_offsets_refute` | `dynamic_graphs::probe::tests` |
| `the_probe_catches_a_seeded_converse_divergence` | `dynamic_graphs::probe::tests` |
| `the_dichotomy_boundary_is_measured` | `dynamic_graphs::probe::tests` |

## Mutation backlog

A standalone campaign over `1793badece8881bb2d6b5ce06105dbdf9e4b781b..HEAD`, restricted to this crate and its composition comparison, should mutate bounded-search cutoffs, predecessor reconstruction, relocation ordering, constraint signs, rollback, and duplicate handling. Hypotheses: batch agreement rejects changed cycle verdicts; checked walks reject invalid evidence; unaffected-slot and exact-value boundaries reject overbroad repairs and lost rollback. No mutation score is claimed and this campaign is not a landing gate.

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
