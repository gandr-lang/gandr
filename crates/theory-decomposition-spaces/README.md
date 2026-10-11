# gandr-theory-decomposition-spaces

Sequential certificate composition in two modes and bounded backward pathway queries.

## Synopsis

**What.** Compose the derivation certificates of `gandr-theory-coherent-resolutions`, or ask which compressed derivations can end in a target cell.

**Why.** Certificate consumers need an explicit distinction between coherence composition and a directed gate, together with a static query whose refusals are not confused with normalizer failures.

**How.** Both modes concatenate the two recorded legs at a sequential boundary. The directed mode first builds a cell-and-hole flow graph at the left certificate's recorded join and refuses a cycle. The pathway query prepends transitions, certifies the recorded first leg through `gandr-theory-deep-inference`, checks the target's causal position, and retains one representative per normal form. The crate is `no_std` with `alloc`; it evaluates no program.

## References

- Imma Gálvez-Carrillo, Joachim Kock and Andrew Tonks. “Decomposition Spaces, Incidence Algebras and Möbius Inversion I: Basic Theory.” _Advances in Mathematics_ 331 (2018), 952–1015. [doi:10.1016/j.aim.2018.03.016](https://doi.org/10.1016/j.aim.2018.03.016) — decomposition spaces and incidence coalgebras, not a rewriting implementation.
- Imma Gálvez-Carrillo, Joachim Kock and Andrew Tonks. “Decomposition Spaces in Combinatorics.” [arXiv:1612.09225v3, §2.5.5](https://arxiv.org/html/1612.09225v3#S2.SS5.Thmlemma5), 2024 — the corrected planarity locator: ordered forests of planar trees give a decomposition space that is **monoidal but not symmetric monoidal**. This does not justify imposing planar order on a symmetric parallel-component interface. Ordering within a cell and permutation of independent components are separate choices here.
- Nicolas Behr and Joachim Kock. “Tracelet Hopf Algebras and Decomposition Spaces (Extended Abstract).” _EPTCS_ 372 (2022), 323–337. [doi:10.4204/EPTCS.372.23](https://doi.org/10.4204/EPTCS.372.23) — the tracelet composition and shift-quotient line. The implemented independence relation is the stricter guarded, trivial-overlap relation; this crate does not claim the paper's full quotient or a Hopf algebra.

## Provided features

- `compose_invertible`: unconditional sequential graft, retaining the left overlap and right join. Witnesses: `composition::tests::invertible_composition_of_a_ground_chain_replays` and `composition::tests::invertible_composition_is_well_defined_on_the_replay_quotient`.
- `compose_directed` and `CompositionObstruction`: the same graft behind the seam-flow cycle gate, with a semantic cell-and-hole cycle or a typed graph/capacity failure. Witnesses: `composition::tests::the_seam_edge_is_drawn_exactly_when_the_left_emits_and_the_right_absorbs` and `composition::tests::the_criterion_reads_the_seam_holes_of_the_left_certificates_recorded_join`.
- `target_occurs_only_last`: target absence, repetition, a non-predecessor, or acceptance relative to the guard. Every other event must precede the unique target. Witnesses: the four corresponding `pathway::tests` rows in the floor below.
- `synthesize_pathways`, `PathwayBudget`, `PathwayOutcome` and `PathwayObstruction`: breadth-first backward growth, duplicate compression, explicit length/candidate ceilings, and the stopped frontier. `certify_candidate` separates candidate-local refusals from failures that stop the query. Witnesses: `pathway::tests::a_backward_extension_is_returned_once_with_its_exact_frontier`, `pathway::tests::a_kill_signal_stops_the_query_rather_than_refusing_a_candidate`, and the pathway floor.

## Expected features

- **Sequential replay boundaries supplied by the caller.** Composition assumes the left join meets the right peak; it does not validate both input certificates. Replay is the semantic oracle.
- **A valid target seed.** The seed is a certified single-target pathway. Length counts transitions including that seed; candidate count charges each attempted prepend before composition. The seed is returned even when a ceiling permits no expansion. A decline retains admitted pathways and the current frontier; no resume protocol is provided.
- **Guard-relative positives.** The causal guard may retain excess dependence. A target-last refutation is sound; acceptance is an over-approximation relative to that guard, not a completeness theorem for the full shift quotient.

## Directed composition and identity

The graph uses distinct recorded cells, not application positions, multiplicities or substitutions. It restricts each cell's live metadata to the holes of the **left** recorded join. A forward endpoint emits, a backward endpoint absorbs, and a mixed endpoint does both. Edges cross between the two supports only from emitters to absorbers. Missing stored cells contribute no endpoint.

This gate is presentation-sensitive. Changing a certificate's representative can change its support and therefore the verdict, even when replay identifies the certificates. The admitted graft remains a certificate invariant. Reversing one unordered pair can also change the verdict because it changes the selected seam. Pairwise admission is therefore not a substitute for running the binary gate at each actual fold step.

The chosen emit-to-absorb criterion is strictly less conservative than a union-of-variances test: sequential producer-to-consumer seams are admitted without inventing a reverse edge. The alternative union criterion remains a test oracle. Reconsider the representation only when a consumer requires a presentation-invariant gate and supplies the extra data that can decide one; a normalized label alone is insufficient.

The graph is built afresh for each query. Keep its gate batch-based: successive certificate pairs can change both the support and the left-join hole filter, so they are not insertion-only updates. The dynamic comparison witness streams each characterized graph in both arrival orders and agrees with the batch gate; `gandr-theory-dynamic-graphs` is a development dependency only. Reconsider the gate only for a consumer retaining one standing graph or accumulating constraints monotonically across calls. No standing dynamic graph, durable step address, comultiplication or antipode is part of this crate. Build-local normal-form labels never acquire a transport type here.

## Certificate fields

`transport::step_fields` borrows a sequent cell and its application position. It yields structural fields in v1 order: left face, right face, orientation, provenance, metadata, then position. Faces use pre-order tags, names and arities. Names retain their spelling; metadata follows first occurrence. The immutable contractum-use classification is recoverable from the encoded faces and carries no redundant field.

The iterator walks flat producer tables and consumer spines without allocation or recursive calls. Storage owns checked widths, byte framing and BLAKE3 identities through [`gandr-storage-artifact::transport`](../storage-artifact/README.md#certificate-transport). This direction keeps theory independent of storage. A buffered byte image would allocate per hash; a sink trait would add an abstraction with one implementation. Reconsider the field boundary when a second alphabet supplies its canonical encoding.

## Examples

The deep-inference integration test [`composed_tracelets_replay_and_normalize_through_the_public_algebra`](../theory-deep-inference/tests/oracle.rs) constructs an `A → C → E` chain, composes in both modes, replays both legs, consumes the normalizer's receipt without copying its order, and checks the exact schedule and target-last verdict. It calls this crate's public API, not an internal fixture facade.

## Compatibility floor

The floor has 37 named rows: 27 are present here and 10 are exercised at the storage transport boundary; none are deferred. The reversed-pair seam witness and backward-growth/compression witness are additional; the composition consumer witness lives in deep-inference, and the transport consumer witness in storage-artifact. Integration targets are discovered directly by Cargo.

| Test | Disposition | Scope |
| ---- | ----------- | ----- |
| `a_derivation_without_the_target_is_not_a_pathway` | Present | Composition or pathway query |
| `a_target_firing_twice_is_refused` | Present | Composition or pathway query |
| `a_target_last_over_a_dependent_past_holds` | Present | Composition or pathway query |
| `a_non_predecessor_beside_the_target_refutes` | Present | Composition or pathway query |
| `a_length_ceiling_declines_with_its_frontier` | Present | Composition or pathway query |
| `every_obstruction_arm_is_classified_exactly` | Present | Composition or pathway query |
| `a_candidate_that_misses_its_join_is_refused` | Present | Composition or pathway query |
| `a_zero_candidate_ceiling_builds_nothing` | Present | Composition or pathway query |
| `a_candidate_ceiling_admits_exactly_its_count` | Present | Composition or pathway query |
| `synthesized_pathways_are_returned_in_normal_form` | Present | Composition or pathway query |
| `a_mixed_step_cell_is_classified_mixed` | Present | Composition or pathway query |
| `invertible_composition_of_a_ground_chain_replays` | Present | Composition or pathway query |
| `directed_composition_of_a_ground_chain_replays` | Present | Composition or pathway query |
| `directed_composition_declines_a_mixed_variance_cycle` | Present | Composition or pathway query |
| `the_acyclicity_verdict_reads_the_recorded_cell_support_and_nothing_finer` | Present | Composition or pathway query |
| `the_acyclicity_verdict_is_not_invariant_under_certificate_identity` | Present | Composition or pathway query |
| `a_single_polarity_partner_hides_the_divergence_from_every_probe` | Present | Composition or pathway query |
| `the_composite_is_a_certificate_invariant_even_where_the_verdict_is_not` | Present | Composition or pathway query |
| `invertible_composition_is_well_defined_on_the_replay_quotient` | Present | Composition or pathway query |
| `the_refined_seam_criterion_declines_strictly_less_than_the_union_reading` | Present | Composition or pathway query |
| `the_ordinary_sequential_seam_is_what_the_union_reading_declined` | Present | Composition or pathway query |
| `the_seam_edge_is_drawn_exactly_when_the_left_emits_and_the_right_absorbs` | Present | Composition or pathway query |
| `a_recorded_cell_the_store_does_not_hold_contributes_no_endpoint` | Present | Composition or pathway query |
| `fanout_family_is_a_multi_sum_not_a_single_rule` | Present | Composition or pathway query |
| `a_kill_signal_stops_the_query_rather_than_refusing_a_candidate` | Present | Composition or pathway query |
| `an_ordinary_non_replaying_candidate_is_refused_without_failing` | Present | Composition or pathway query |
| `the_v1_golden_step_identity_is_stable` | Present | [Storage certificate transport](../storage-artifact/README.md#certificate-transport) |
| `an_independently_rebuilt_cell_mints_the_same_identity` | Present | [Storage certificate transport](../storage-artifact/README.md#certificate-transport) |
| `the_identity_reads_the_position` | Present | [Storage certificate transport](../storage-artifact/README.md#certificate-transport) |
| `the_identity_reads_the_cell_content` | Present | [Storage certificate transport](../storage-artifact/README.md#certificate-transport) |
| `the_identity_is_stable_across_store_insertion_orders` | Present | [Storage certificate transport](../storage-artifact/README.md#certificate-transport) |
| `the_index_preserves_the_graded_factorization` | Present | [Storage certificate transport](../storage-artifact/README.md#certificate-transport) |
| `the_index_is_deterministic_across_repeated_normalization` | Present | [Storage certificate transport](../storage-artifact/README.md#certificate-transport) |
| `distinct_factorizations_index_distinctly` | Present | [Storage certificate transport](../storage-artifact/README.md#certificate-transport) |
| `a_shared_identity_with_distinct_content_is_refused` | Present | [Storage certificate transport](../storage-artifact/README.md#certificate-transport) |
| `a_shared_identity_with_equal_content_sums_the_grading` | Present | [Storage certificate transport](../storage-artifact/README.md#certificate-transport) |
| `the_gates_own_graph_streamed_incrementally_reproduces_its_verdict` | Present | Standing dynamic graph comparison |

The current metadata retains both faces of a fused rule. The presentation witnesses therefore use a replay-equivalent, alpha-renamed representative whose seam-named support differs, rather than assuming fusion erases mixed variance. Corpus checks compare semantic verdicts and replay, not an incidental count of pairs.

A candidate ceiling reached midway through a round retains that round’s already admitted normal forms as well as the stopped frontier. The backward-extension witness checks this against a one-candidate ceiling; dropping the partial round would lose an accepted pathway.

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
