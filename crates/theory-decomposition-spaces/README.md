# gandr-theory-decomposition-spaces

Sequential certificate composition in two modes and bounded backward pathway queries.

<!-- toc -->
- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Where the detail lives](#where-the-detail-lives)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** Compose the derivation certificates of `gandr-theory-coherent-resolutions`, or ask which compressed derivations can end in a target cell.

**Why.** Certificate consumers need an explicit distinction between coherence composition and a directed gate, together with a static query whose refusals are not confused with normalizer failures.

**How.** Both modes concatenate the two recorded legs at a sequential boundary. The directed mode first builds a cell-and-hole flow graph at the left certificate's recorded join and refuses a cycle. The pathway query prepends transitions, certifies the recorded first leg through `gandr-theory-deep-inference`, checks the target's causal position, and retains one representative per normal form. The crate is `no_std` with `alloc`; it evaluates no program.

## Provided features

- `compose_invertible`: unconditional sequential graft, retaining the left overlap and right join. Witnesses: `composition::tests::invertible_composition_of_a_ground_chain_replays` and `composition::tests::invertible_composition_is_well_defined_on_the_replay_quotient`.
- `compose_directed` and `CompositionObstruction`: the same graft behind the seam-flow cycle gate, with a semantic cell-and-hole cycle or a typed graph/capacity failure. Witnesses: `composition::tests::the_seam_edge_is_drawn_exactly_when_the_left_emits_and_the_right_absorbs` and `composition::tests::the_criterion_reads_the_seam_holes_of_the_left_certificates_recorded_join`.
- `target_occurs_only_last`: target absence, repetition, a non-predecessor, or acceptance relative to the guard. Every other event must precede the unique target. Witnesses: the four corresponding `pathway::tests` rows of the floor, [#202](https://github.com/gandr-lang/gandr/issues/202).
- `synthesize_pathways`, `PathwayBudget`, `PathwayOutcome` and `PathwayObstruction`: breadth-first backward growth, duplicate compression, explicit length/candidate ceilings, and the stopped frontier. `certify_candidate` separates candidate-local refusals from failures that stop the query. Witnesses: `pathway::tests::a_backward_extension_is_returned_once_with_its_exact_frontier`, `pathway::tests::a_kill_signal_stops_the_query_rather_than_refusing_a_candidate`, and the pathway rows of [#202](https://github.com/gandr-lang/gandr/issues/202).

## Expected features

- **Sequential replay boundaries supplied by the caller.** Composition assumes the left join meets the right peak; it does not validate both input certificates. Replay is the semantic oracle.
- **A valid target seed.** The seed is a certified single-target pathway. Length counts transitions including that seed; candidate count charges each attempted prepend before composition. The seed is returned even when a ceiling permits no expansion. A decline retains admitted pathways and the current frontier; no resume protocol is provided.
- **Guard-relative positives.** The causal guard may retain excess dependence. A target-last refutation is sound; acceptance is an over-approximation relative to that guard, not a completeness theorem for the full shift quotient.

## Examples

The deep-inference integration test [`composed_tracelets_replay_and_normalize_through_the_public_algebra`](../theory-deep-inference/tests/oracle.rs) constructs an `A → C → E` chain, composes in both modes, replays both legs, consumes the normalizer's receipt without copying its order, and checks the exact schedule and target-last verdict. It calls this crate's public API, not an internal fixture facade.

## Where the detail lives

Mechanism, decisions with their alternatives and reversals, and witnesses live in the rustdoc beside the code:

| Topic | Module |
| ----- | ------ |
| Directed composition, identity and the presentation witnesses | [`compose`](src/compose.rs) |
| Pathway queries and partial rounds | [`pathway`](src/pathway.rs) |
| Certificate fields | [`transport`](src/transport.rs) |
| References | [`src/lib.rs`](src/lib.rs) |

The behavioural floor — 37 named rows, none deferred — is recorded in [#202](https://github.com/gandr-lang/gandr/issues/202).

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
