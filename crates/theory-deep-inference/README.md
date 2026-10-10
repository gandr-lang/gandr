# gandr-theory-deep-inference

The identity relations on derivations: when two derivations that fire the same cells in different orders are one derivation, and the structure that decides it.

<!-- toc -->

- [Synopsis](#synopsis)
- [References](#references)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Shift equivalence](#shift-equivalence)
- [The causal order](#the-causal-order)
- [The certificate normal form](#the-certificate-normal-form)
- [Replay plans](#replay-plans)
- [Content addresses](#content-addresses)
- [The causal web and refinement](#the-causal-web-and-refinement)
- [The flow projection](#the-flow-projection)
- [The footprint relation](#the-footprint-relation)
- [Oracle tests over the engine](#oracle-tests-over-the-engine)
- [Specification evidence](#specification-evidence)
- [The guarded template](#the-guarded-template)
- [Boundary wrappers](#boundary-wrappers)
- [License](#license)

<!-- tocstop -->

## Synopsis

**What.** The identity layer over the rewriting engine's derivations, generic over `CellAlphabet`. `derive_shift_equivalence` earns the witness that two adjacent applications commute; `event_order` builds the finite partial order of one recorded derivation's events, with its canonical schedule, its layering and the exchange witness between two of its sequentializations; `normalize` and `normalize_certified` factor a derivation into content-addressed primitives with multiplicities, scheduled canonically, and compare the result by `nf_equal`, `nf_equal_across_stores`, `certified_nf_equal` and `tracelets_nf_equal`; `ReplayPlan` projects a certified derivation into antichain levels with its critical-path fuel; `causal_web` and `refines` read the order as a two-colour web and compare two webs over one event set; `project_flow` and `flows_equal` give a leg's atomic flow; `match_footprint` and `footprint_independence` give the polarized read and write footprint the shift guard is measured against; `anti_unify_tracelets` folds a family of certificates sharing one skeleton into a `GuardedTemplate` where that pays, each member admitted by instantiation and replay.

**Why.** Completion and fusion produce many certificates for one boundary, and a consumer that keys, deduplicates or schedules them needs to know when two are the same derivation without replaying both every time. Replay in `gandr-theory-coherent-resolutions` stays the semantic oracle; every relation here is a sound fast path below it, decidable from certificate data, whose positive answer implies replay equivalence and whose negative answer is never read as distinctness. The causal order also answers what a scheduler needs: which steps could fire together, and how much sequential fuel a complete replay consumes.

**How.** One independence relation, the shift guard, decides which adjacent applications commute: incomparable positions, no overlap between the two cells, and the alphabet's convexity discharge, confirmed by replaying both sequentializations from one peak with the engine's `replay_from_peak`. The causal order reads that relation as dependence, layers events by causal depth and orders each layer by a content-derived key that digests the event's causal past, refusing a tie rather than breaking it by arrival. The normal form, the replay plan, the web and the flow are read off that one order; none computes a second dependence relation. Every walk keeps its stack on the heap, so a derivation far longer than the thread's stack is ordered, normalized and projected. Absence and refusal are values: a lookup that finds nothing returns `Maybe` with its reason, and a refused operation returns `Result` with a typed obstruction.

## References

- Alessio Guglielmi and Tom Gundersen. "Normalisation Control in Deep Inference via Atomic Flows." _Logical Methods in Computer Science_ 4, 1 (2008), paper 9. `doi:10.2168/LMCS-4(1:9)2008` — atomic flows as graphs traced from atom occurrences with the logical structure forgotten (Definition 3.2), the object `project_flow` computes over a derivation's term positions.
- Nicolas Behr. "Tracelets and Tracelet Analysis of Compositional Rewriting Systems." In _Proceedings of Applied Category Theory 2019_, Electronic Proceedings in Theoretical Computer Science 323 (2020), pages 44–71. `doi:10.4204/EPTCS.323.4` — tracelets as derivations recorded for re-execution, the certificate data every relation here reads.
- Victoria Barrett, Alessio Guglielmi, Benjamin Ralph, and Lutz Straßburger. "Proof Compression via Subatomic Logic and Guarded Substitutions." In _Proceedings of the 40th Annual ACM/IEEE Symposium on Logic in Computer Science (LICS 2025)_, 2025. Preprint `arXiv:2505.20009` — guarded substitutions over a superposed proof and their two recorded prices, the quadratic range-inheritance check and the interpretation map; the guarded template is the first and never pays the second.
- Nicolas Behr and Joachim Kock. "Tracelet Hopf Algebras and Decomposition Spaces (Extended Abstract)." In _Proceedings of the Fourth International Conference on Applied Category Theory_, Electronic Proceedings in Theoretical Computer Science 372 (2022). `doi:10.4204/EPTCS.372.23` — the shift quotient of the tracelet algebra is free on its primitives, which the normal form reads as a unique factorization into content-addressed primitives with multiplicities.
- Filippo Bonchi, Fabio Gadducci, Aleks Kissinger, Paweł Sobociński, and Fabio Zanasi. "String Diagram Rewrite Theory II: Rewriting with Symmetric Monoidal Structure." _Mathematical Structures in Computer Science_ 32, 4 (2022), pages 511–541. `doi:10.1017/S0960129522000317`; preprint `arXiv:2104.14686` — convex matching and the example of two disjoint matches that interfere through each other's convexity, the reason the shift guard carries a convexity conjunct and the flow projection is sound only under its discharge.
- Matteo Acclavio, Ross Horne, Sjouke Mauw, and Lutz Straßburger. "A Graphical Proof Theory of Logical Time." In _7th International Conference on Formal Structures for Computation and Deduction (FSCD 2022)_, LIPIcs 228, 2022, pages 22:1–22:25. `doi:10.4230/LIPIcs.FSCD.2022.22` — causal webs with green precedence and white independence, and the slice-chain weakening `refines` decides on the identity-map fragment.
- Paul-André Melliès and Léo Stefanesco. "Concurrent Separation Logic Meets Template Games." Preprint, May 2020. `arXiv:2005.04453` — independence of transitions over read and write footprints, the reading the polarized footprint test takes and the shift guard is measured against.
- Paul-André Melliès. "Asynchronous Template Games and the Gray Tensor Product of 2-Categories." In _36th Annual ACM/IEEE Symposium on Logic in Computer Science (LICS 2021)_, June 2021. `doi:10.1109/LICS52264.2021.9470758` — asynchronous graphs and their symmetry, determinism and cube axioms, checked against the shift witness by the integration suite.

## Provided features

- `derive_shift_equivalence`, `ShiftEquivalence`, `ShiftObstruction`: the earned witness that two adjacent applications commute, its two sequentializations confirmed by replay from one peak, and the conjunct that refuses a pair. Witnesses: `shift::tests::two_applications_at_one_position_are_refused`, `shift::tests::a_nested_pair_is_refused_before_the_overlap_conjunct`, `shift::tests::a_genuinely_overlapping_pair_is_refused_the_witness`, `shift::tests::an_undischarged_convexity_conjunct_refuses_the_pair`, `shift::tests::a_step_that_does_not_fire_is_refused`, `tests::shift::the_cong2_pair_earns_its_shift_equivalence_witness`, `tests::shift::the_cong2_composite_replays_under_both_sequentializations`, `tests::shift::a_retargeted_composite_no_longer_replays`, `tests::shift::an_adjacent_transposition_schedule_asks_a_quadratic_number_of_questions`.
- The shift witness's tiles form an asynchronous graph: symmetric, deterministic, and satisfying the cube property over the fixture family, searched rather than assumed. Witnesses: `tests::asynchronous_axioms::every_permutation_tile_is_symmetric`, `tests::asynchronous_axioms::every_permutation_tile_is_deterministic`, `tests::asynchronous_axioms::the_cube_property_holds_for_every_pair_of_three_paths`, `tests::asynchronous_axioms::a_missing_pairwise_tile_removes_both_cube_routes`.
- `event_order`, `EventOrder`, `DerivationEvent`, `EventKey`, `ExchangeWitness`, `Transposition`, `ExchangeObstruction`, `KeyCollision`, `event_lookup`, `exchange_application`: the finite event partial order of one derivation, its canonical schedule and layering, and the exchange witness between two sequentializations. Witnesses: `causal::tests::precedence_is_the_transitive_closure_of_dependence`, `causal::tests::the_exchange_witness_carries_the_recorded_order_to_the_canonical_one`, `causal::tests::a_target_inverting_a_dependent_pair_is_refused`, `causal::tests::two_events_tying_on_depth_and_key_are_refused`, `tests::normal_form::causal_precedence_is_a_strict_partial_order`, `tests::normal_form::independence_is_symmetric_and_irreflexive`, `tests::normal_form::the_canonical_key_never_ties`, `tests::normal_form::the_canonical_order_is_always_reachable_by_licensed_transpositions`, `tests::normal_form::every_adjacent_independent_transposition_leaves_the_canonical_order_fixed`.
- `normalize`, `normalize_certified`, `TraceletNf`, `ReplayWitness`, `PrimCert`, `NormalFormObstruction`, `schedule_resolution`: the certificate normal form and its replay receipt. Witnesses: `normal_form::tests::a_recorded_derivation_normalizes_to_a_replay_receipt`, `normal_form::tests::a_unit_step_is_eliminated`, `normal_form::tests::a_path_that_misses_its_join_is_refused`, `tests::normal_form::a_repeated_primitive_is_graded_by_multiplicity`, `tests::normal_form::a_shuffled_independent_schedule_has_one_normal_form`, `tests::normal_form::two_primitives_sharing_a_content_address_are_refused_rather_than_merged`, `tests::normal_form::a_non_local_term_algebra_trips_the_kill_signal_at_the_join`, `tests::normal_form::an_alphabet_that_calls_nesting_incomparable_trips_the_kill_signal`.
- `nf_equal`, `nf_equal_across_stores`, `certified_nf_equal`, `tracelets_nf_equal`: the four normal-form relations, each a sound under-approximation of replay equivalence. Witnesses: `tests::normal_form::every_nf_equal_pair_is_replay_equivalent`, `normal_form::tests::nf_equal_certificates_are_replay_equivalent`, `normal_form::tests::replay_equal_derivations_may_be_nf_distinct`, `normal_form::tests::one_derivation_built_in_two_stores_compares_equal_across_them`, `normal_form::tests::two_stores_holding_different_cells_at_one_handle_compare_unequal`, `tests::normal_form::the_canonical_order_is_the_same_in_two_differently_ordered_stores`, `tests::normal_form::a_tracelet_pair_agreeing_only_on_its_first_leg_is_not_certified`.
- `ReplayPlan`, `replay_fuel`: antichain replay levels with critical-path fuel, replayed level by level or whole. Witnesses: `normal_form::tests::a_fused_fixture_replays_both_certificate_paths_through_its_critical_path_plan`, `tests::normal_form::a_two_member_replay_level_reaches_one_term_in_both_permitted_orders`, `tests::oracle::every_generated_certificate_matches_its_replay_plan`, `tests::oracle::a_relabelled_twin_schedules_and_replays_identically`, `tests::oracle::overlap_support_batches_replay_along_their_plans`.
- `prim_address`, `cell_address`, `causal_past_address`, `PrimId`, `CellAddress`, `CausalPast`: build-local content addresses that order and key within one process. Witnesses: `normal_form::tests::the_content_address_is_taken_over_content`, `normal_form::tests::the_two_address_domains_are_separated_by_type_and_by_digest`, `normal_form::tests::the_causal_past_digest_reads_the_multiset_and_not_the_order`, `tests::content_faithfulness::production_alphabets_satisfy_content_faithfulness`.
- `causal_web`, `CausalWeb`, `DependenceBits`, `WebRelation`, `refines`, `RefinementVerdict`, `RefinementCounterexample`, `SliceChain`, `SliceStep`, `HomomorphismFrontier`, `web_lookup`: the two-colour web of one event order, and refinement between two webs over one event set with a witness either way and named frontiers for everything else. Witnesses: `causal_web::tests::a_tracelet_fixture_builds_the_two_colour_web`, `causal_web::tests::an_independence_to_order_change_is_licensed`, `causal_web::tests::a_lost_precedence_is_a_negative_witness`, `causal_web::tests::a_label_mismatch_refuses_edge_strengthening_simulation`, `causal_web::tests::a_cardinality_mismatch_refuses_open_h_down`, `causal_web::tests::a_malformed_web_refuses_structural_comparison`, `tests::causal_web::a_precedence_reached_only_through_an_intermediate_event_is_green`, `tests::causal_web::refusal_frontiers_remain_named_in_public_api`.
- `project_flow`, `tracelet_flow`, `Flow`, `FlowThread`, `FlowEnd`, `TraceletFlow`, `FlowObstruction`, `flows_equal`, `legs_flow_equal`, `tracelets_flow_equal`, `flow_canonical`: the atomic-flow projection of a leg and of a certificate, and flow equality. Witnesses: `tests::flow::a_single_step_leg_threads_the_whole_term_through_one_vertex`, `tests::flow::disjoint_steps_share_no_thread`, `tests::flow::the_two_legs_of_a_permutation_tile_have_one_flow`, `tests::flow::flow_equality_implies_replay_equivalence`, `tests::flow::flow_equality_is_strictly_finer_than_replay_equivalence`, `tests::flow::replay_equivalent_certificates_can_carry_different_flows`, `tests::flow::flow_equality_sits_inside_the_games_quotient_on_the_discharge_class`, `flow::tests::indistinguishable_vertices_are_refused_a_canonical_order`.
- `match_footprint`, `MatchFootprint`, `footprint_independence`, `FootprintIndependence`, `FootprintObstruction`: the read and write footprint of one application and the polarized independence test. Witnesses: `tests::footprint::a_ground_redex_writes_its_whole_match_image`, `tests::footprint::a_preserved_root_is_read_and_its_hole_is_framed`, `tests::footprint::two_root_rules_sharing_only_a_read_node_are_independent`, `tests::footprint::a_rule_that_destroys_a_node_another_only_reads_is_refused`, `tests::footprint::the_guard_licenses_nothing_the_polarized_test_refuses`, `tests::footprint::every_row_of_the_differential_table_rules_as_recorded`.
- Every walk keeps its stack on the heap: a dependence chain far longer than a small thread's stack is ordered, normalized, projected to a flow and a web, and dropped inside that thread. Witness: `tests::deep_derivation::a_deep_derivation_is_ordered_normalized_and_dropped_on_a_small_stack`.
- `anti_unify_tracelets`, `GuardedTemplate`, `TemplateEntry`, `TemplateArm`, `TemplateRefusal`, `TemplateObstruction`, `InheritanceCache`, `InheritanceKey`, `InheritanceVerdict`, `TemplateLeg`, `TemplateAddress`, `ArmAddress`, `ProductionCounts`, `FamilyCostReport`, `inheritance_lookup`: the guarded template of a certificate family, emitted only below its expansion factor, its inheritance check memoized per content triple for one run, members admitted by instantiation and replay, and the family's cost with the template and without. Witnesses: `tests::template::a_template_is_emitted_only_below_its_expansion_factor`, `tests::template::every_member_admits_as_its_plain_replay`, `tests::template::a_skeleton_divergent_family_yields_no_template`, `tests::template::an_entry_a_cell_discriminates_on_yields_no_template`, `tests::template::a_family_with_no_shared_content_yields_no_template`, `tests::template::the_inheritance_check_runs_once_per_distinct_triple`, `tests::template::a_poisoned_inheritance_entry_is_caught_at_admission`, `tests::template::a_template_has_one_flow_for_its_family`, `tests::template::a_certificate_outside_the_template_is_refused_by_name`.
- The boundary wrappers (`CausalDepth`, `EventIndex`, `EventCount`, `EventDependence`, `EventPrecedence`, `EventConcurrency`, `SchedulePosition`, `TranspositionCount`, `ReplayLevel`, `NormalFormEquality`, `PrimMultiplicity`, `ShiftReplay`, `FlowEquality`, `FlowPortIndex`, `FlowVertexIndex`, `PeakOccurrenceIndex`, `WebVertex`, `WebVertexCount`, `WebPrecedence`, `WebIndependence`, `SliceStepCount`, `NodeCount`, `ExpansionFactor`, `MemberIndex`, `MemberCount`, `EntryIndex`, `GuardId`, `TripleCount`, `CacheHitCount`, `AdmissionCount`, `ReplayStepCount`, `LegStepIndex`): every count, index and verdict a public signature here crosses.

## Expected features

- **An alphabet keeping the inhabitant laws.** The relations spend the laws the substrate's `CellAlphabet` states and no type checks, and two more: a splice changes nothing outside its position, and a primitive's content address separates two cells that differ in content. The normal form replays its canonical schedule and refuses a schedule that does not land, so a broken locality law is caught as a kill signal; a content address that collides inside one normal form is refused rather than merged. The adversarial alphabets in `gandr-theory-cell-complexes-tools` exercise each law broken.
- **Derivations sized for certificates.** The causal order asks the guard once per pair of events, and a web is a dense square matrix over its events; both are quadratic in the derivation's length, sized for certificate legs rather than for whole program runs.
- **Addresses kept inside the process.** Content addresses are stable for one build of one target. A consumer orders and keys by them within one process and never persists or sends one.

## Examples

Fuse the frame-defining cell into the successor rule, certify one path of the certificate, and replay it along its plan.

```rust
use gandr_theory_cell_complexes::Cell;
use gandr_theory_cell_complexes::CellAlphabet as _;
use gandr_theory_cell_complexes::CellProvenance;
use gandr_theory_cell_complexes::CellStore;
use gandr_theory_cell_complexes::CmdPat;
use gandr_theory_cell_complexes::ConsPat;
use gandr_theory_cell_complexes::Orientation;
use gandr_theory_cell_complexes::Polarity;
use gandr_theory_cell_complexes::ProdPat;
use gandr_theory_cell_complexes::SequentAlphabet;
use gandr_theory_cell_complexes::Sym;
use gandr_theory_cell_complexes::frame_defining_cell;
use gandr_theory_coherent_resolutions::OverlapKind;
use gandr_theory_coherent_resolutions::derive_fused;
use gandr_theory_coherent_resolutions::enumerate_overlaps;
use gandr_theory_deep_inference::normalize_certified;
use quenchant_shape::shape::Maybe;

fn example() -> Result<(), &'static str> {
    let mut store = CellStore::new();
    let frame = store.insert(frame_defining_cell(&Sym::new("Succ")));
    // ⟨Succ(m) | add(n; α)⟩ ~> ⟨m | add(n; Succ⁻(α))⟩
    let add = store.insert(Cell::new(
        CmdPat::cut(
            Polarity::Positive,
            ProdPat::ctor("Succ", [ProdPat::meta("m")]),
            ConsPat::op("add", [ProdPat::meta("n")], ConsPat::meta("alpha")),
        ),
        CmdPat::cut(
            Polarity::Positive,
            ProdPat::meta("m"),
            ConsPat::op("add", [ProdPat::meta("n")], ConsPat::frame("Succ", ConsPat::meta("alpha"))),
        ),
        Orientation::PolarityDerived,
        CellProvenance::SurfaceRule,
    ));
    let composition = enumerate_overlaps(&store)
        .into_iter()
        .find(|o| o.kind == OverlapKind::Composition && o.left == frame && o.right == add)
        .ok_or("the two cells compose")?;
    let (_fused, certificate) =
        derive_fused(&composition, &mut store).map_err(|_| "the composition fuses")?;
    let witness = normalize_certified(
        &store,
        &certificate.overlap.peak,
        &certificate.joins_at,
        &certificate.path_a,
    )
    .map_err(|_| "the two-step path replays to the join")?;
    let plan = witness.replay_plan();
    match plan.replay_with_fuel(&store, plan.critical_path()) {
        Ok(Maybe::Present(reached)) => {
            assert_eq!(SequentAlphabet::skolemize(witness.joins_at()), reached);
            Ok(())
        },
        Ok(Maybe::Absent(_)) | Err(_) => Err("critical-path fuel completes the plan"),
    }
}
```

Ask whether two adjacent applications commute, and read the refusal when they do not.

```rust
use gandr_theory_cell_complexes::CellAlphabet;
use gandr_theory_cell_complexes::CellStore;
use gandr_theory_coherent_resolutions::CellApp;
use gandr_theory_deep_inference::ShiftObstruction;
use gandr_theory_deep_inference::derive_shift_equivalence;

fn explain<A: CellAlphabet>(
    store: &CellStore<A>,
    peak: &A::Cmd,
    first: &CellApp<A>,
    second: &CellApp<A>,
) -> &'static str {
    match derive_shift_equivalence(store, peak, first, second) {
        Ok(_witness) => "the two applications commute",
        Err(ShiftObstruction::UnknownCell { .. }) => "an application names no stored cell",
        Err(ShiftObstruction::ComparablePositions { .. }) => "one position encloses the other",
        Err(ShiftObstruction::GenuineOverlap { .. }) => "the two cells overlap at a seam",
        Err(ShiftObstruction::ConvexityNotDischarged) => "the alphabet withholds the convexity warrant",
        Err(ShiftObstruction::StepDoesNotFire { .. }) => "a sequentialization does not fire",
        Err(ShiftObstruction::SequentializationsDiffer { .. }) => "the two orders reach different terms",
    }
}
```

Run the tests:

```sh
cargo nextest run -p gandr-theory-deep-inference
RUSTFLAGS="--cfg anodized_panic" CARGO_TARGET_DIR=target/enforcing cargo nextest run -p gandr-theory-deep-inference
```

## Shift equivalence

Two adjacent applications commute when three conjuncts hold, asked in this order: their positions are incomparable, the two cells have no overlap at a seam, and the alphabet discharges the convexity conjunct for the store. The first refusal is the one returned, so a nested pair is refused on its positions before its cells are read. A pair that passes is then confirmed rather than trusted: both sequentializations are fired from the one peak and must reach one join, through the engine's `replay_from_peak`. A shift boundary is a peak, a join and two paths, not a critical pair, so it has no overlap, and the engine's peak-rooted replay is the one replay both crates use; a replay written here would be a second semantics beside the oracle. The guard is the crate's single independence relation, and two cells firing at one position are refused before any tile exists, which is why the cells branching as a rewrite system never reaches the tile set.

## The causal order

An event depends directly on every earlier event the guard refuses to commute with it, and precedence is the transitive closure. Each event's causal depth is one more than the deepest event it depends on, and its key is its primitive's content address together with a digest of its causal past: the address folded with the causal pasts of the events it depends on directly, read as a multiset. The canonical schedule sorts by depth, then key: a licensed transposition swaps two events with no dependence edge between them, so it changes no depth and no key, and two sequentializations of one trace sort to one sequence. Two events at one depth with one key are refused as a `KeyCollision` rather than ordered by arrival, which would make the canonical schedule depend on the recording. The causal past is in the key because an alphabet may legally give two events one address; a repeated primitive at two depths is no tie, since the depth separates it first.

## The certificate normal form

`normalize` runs the recorded path under the skolemization replay uses and refuses anything it cannot confirm, so a returned normal form is a replay receipt: the path fired step by step from the peak and landed on the join. It drops steps that fire and change nothing, groups repeated primitives under one content address with an integer multiplicity, and records the canonical schedule, which it replays before returning. A canonical schedule that does not fire, or lands elsewhere, is the kill signal: the independence relation licensed a commutation the semantics does not have, a defect in position or overlap bookkeeping. Normal-form equality implies replay equivalence, and the converse is false by design: the engine's fused certificate is one boundary reached by a two-step path and a one-step path, replay-equal and normal-form-distinct. Replay stays the oracle, and a negative answer here means "not identified", never "distinct". `ReplayWitness` has private fields and one constructor, `normalize_certified`, so holding one is holding the receipt; `TraceletNf` is a plain value whose receipt property its holder keeps.

`ReplayWitness::into_parts` consumes the receipt into its normal form and causal order without copying either. Certificate-algebra consumers can keep both views while growing a pathway. The integration witness `tests::oracle::composed_tracelets_replay_and_normalize_through_the_public_algebra` composes through `gandr-theory-decomposition-spaces` in both modes, replays the resulting certificate, and checks its exact certified schedule and target-last order.

## Replay plans

`ReplayWitness::replay_plan` groups the certified derivation's events by causal depth: each level is an antichain of the order, its steps in canonical order, and the number of levels is the critical-path fuel a complete replay consumes. `replay_level` fires one level from a term already replayed, and `replay_with_fuel` fires every level from the skolemized peak, declining with `replay_fuel::Absent::InsufficientFuel` when the fuel is below the critical path. The plan keeps the batch boundaries rather than flattening them into one schedule, so a parallel or on-demand replay reads what may fire together. The levels name cells and positions and no metavariable, so a relabelled twin plans the same levels with the same fuel.

## Content addresses

`PrimId`, `CellAddress` and `CausalPast` are 128-bit FNV-1a digests over `core::hash::Hash` writes, each domain separated by its own prefix. The integer writers of `Hash` are native-endian at the target's word width, so an address is stable for one build of one target and no further: it orders events and keys factors within one process, and nothing persists or transmits one. A fixed-endian encoding of cell content, addressed by the storage tier's content pointers, would turn an ordering key into an identity a reader trusts across processes and make this crate a storage consumer for a use it does not have. The addresses change to that encoding when a certificate, an event or a web is first written to storage or sent to another process. An address orders and is nowhere the identity witness: two structurally distinct cells colliding inside one normal form are refused, and across two normal forms the compared values carry the primitive certificates themselves.

## The causal web and refinement

`causal_web` moves one event order into its canonical coordinates as a conflict-free two-colour web: green is the order's precedence, white its complement on distinct events. It computes no second dependence relation; it materializes the order's precedence by one pass in recorded order, folding each direct dependence's finished ancestor row, latest dependence first and skipping one already reached. A per-pair reachability search would cost a search per ordered pair, which a long dependence chain makes quartic; the fold makes a chain quadratic. `refines(finer, coarser)` decides one fragment: two webs over the same labelled events, where `finer` keeps every precedence of `coarser` and adds precedence only to pairs `coarser` leaves independent. It answers `Refines` with the `SliceChain` naming each added pair, `DoesNotRefine` with the first pair in canonical order whose required relation is missing, and `Refused` with a named frontier for anything needing a correspondence between different events: an equal-size label mismatch, a size mismatch, or a malformed web. Over one fixed event set it checks that an order respects a happens-before or that a schedule weakens one. It offers no web over events a caller supplies, no comparison across event sets, no conflict relation and no persistence, and a web over n events holds n² bits.

## The flow projection

`project_flow` traces every atom occurrence of a leg from the peak or the event that created it to the event that consumed it or the conclusion, labelling each vertex with its cell's position-free content address. Flow equality is decided on a canonical vertex order, refused for a flow whose vertices the key cannot tell apart, and is sound only under the convexity discharge the flow was taken under, which every flow carries. Flow equality is strictly finer than replay equivalence: two replay-equivalent certificates can carry different flows. The projection has no consumer; it witnesses the shift quotient and is not certificate identity.

## The footprint relation

`match_footprint` splits an application's match image into the addresses it reads and the addresses it writes, and `footprint_independence` licenses two applications whose writes avoid each other's reads and writes. It sits beside the shift guard as a measurement: every pair the guard licenses the polarized test licenses too, and the differential table records where the polarized reading would license a pair the guard refuses. It has no consumer and replaces nothing.

## Oracle tests over the engine

Three tests read the engine's outputs through this crate's normalizer: every certificate completion emits is certified and replays along its plan, a relabelled twin schedules and replays identically, and the batches the overlap support schedules replay along their plans. Each claims something about this crate's normalizer over the engine's outputs, so they live in this crate's integration suite, over the sequent alphabet the engine's own suites use. Placing them in the engine would need a dev-dependency from the engine onto a crate above it, inverting the layering in the dev graph. They move to the engine when an engine specification clause takes the certified normal form as its witness.

## Specification evidence

Nontrivial implementations and their fixture oracles carry executable `#[spec]` obligations and an item-local `# Adequacy` argument. Enforcement with `--cfg anodized_panic` checks those obligations during the existing unit and integration suites. The hypotheses state the input domain, the observer and the mutations it separates; generated cases are sampled evidence, not universal proofs.

The boundary witnesses cover empty orders and replay plans, fuel and lookup refusal priority, repeated and absent factors, layered dependencies, flow ports and peak anchors, reversed web coordinates, and template cache and admission transitions. The finite cube checks the exact verdict for every ordered pair of its six paths. Content hashing is checked against the published FNV-128 vectors in
[draft-eastlake-fnv-25, Appendix C](https://www.ietf.org/archive/id/draft-eastlake-fnv-25.html#appendix-C);
the content-faithfulness corpus remains a finite collision witness rather than a claim that a finite digest is injective.

Two generator returns remain exempt: their opaque `impl Strategy` return cannot appear in the attribute's evaluation closure under enforcement. The local corpus trait and its two abstract methods also remain exempt: trait instrumentation emits qualifier constants rejected by the lint wall. Both concrete implementations carry executable obligations. These exemptions are removed when the attribute implementation supports the return form and emits lint-compatible trait qualifiers; no lint is relaxed to admit them. The ignored `tests::template::verdict_table` witness is run explicitly with `--ignored --nocapture` to exercise the rendered report.

## The guarded template

`price_family`, the build-local `TemplateAddress::of` and `ArmAddress::of` constructors, and `InheritanceCache::lookup`/`record_check` expose the pricing and cache policy independently of `CellAlphabet`. The separate `price_family_memoized` accepts exactly positive costs with `c <= s` and representable `s + T*c < F`; equality, invalid bounds and overflow refuse. The caller must establish a per-check bound and count every distinct obligation before replay. This entails both `s < F` and `T*c < F` without replacing the original floor gate. The staging producer in `gandr-core-checker::template` supplies its own syntax, an enforced per-check fuel allowance and ordinary replay. Tracelet anti-unification and its admission path keep their existing behavior. Neither address equality nor a cached inheritance verdict authorizes admission.

The memo-aware staging measurements, its enforced bound and its refusal witnesses are documented with the [producer](../core-checker/docs/staging.md). The bound concerns abstract nodes and replay fuel, not discovery or complete readmission time. Neither this API nor the staging producer changes the kernel's admission rules.

A family of certificates that fire the same cells at the same positions from peaks differing only below what those cells read is one certificate written many times. `anti_unify_tracelets` folds it into a `GuardedTemplate`: the alphabet's least general generalization of the members' peaks and joins, taken jointly so a point met in both is one point; the shared paths; and at each point where the members differ an entry holding one arm per distinct member subterm, keyed by the arm's content address and guarded by its own nominal atom. A member is not stored. `GuardedTemplate::instantiate` rebuilds it from its own peak's substitution, choosing each entry's arm by content, and `GuardedTemplate::admit` replays what was rebuilt. An entry whose point is absent from the generalized peak cannot be chosen that way, and the family is refused.

- **The gate is the cannot-lose criterion.** `s` is the template's size in pattern nodes — the generalized peak and join, one node per recorded step, every arm's nodes and one guard atom per arm — and `F` the family's plain size, every member's peak, join and steps summed. A template is emitted only when `s < ⌊F / s⌋`, which gives `s < F`, the compressed form no larger than the plain one, and `s · s < F`, the price of checking it without memoization, at once. The price is taken before any check, so a family that cannot pay costs one anti-unification and no replay. `s` is independent of the family's size `k`, because no member is stored: with a guard reference per member, `s ≥ k`, so `f ≤ F / k`, a member's mean size, which the skeleton in `s` already reaches, and no family would pay.
- **The quadratic dissolves into the distinct-content floor.** Each arm is admitted by an inheritance check: the shared paths replayed from the generalized peak with that arm in place and every other point a skolem constant, against the join with the arm in place. A cell that discriminates on an entry finds the skolem constant, or an arm it does not fire on, and the check is stuck there, so the check is also the discrimination-transparency check. It is memoized per content triple — the region's address, the entry, the arm body's address — in an `InheritanceCache`, an ordered map that lives for one run, so a family of `k` members over `d` arms per entry checks `d` triples per entry and reads the other `k − d` lookups per entry from the cache, whatever `k` is.
- **The cache is never trusted; replay is.** `InheritanceCache::record` writes any verdict for any triple, and a producer reading a lie emits a template it should have refused. Admission does not consult the cache: a member covered by the lie is rebuilt and replayed, and refused exactly as its own replay refuses it.
- **The flow is the family's identity where arms carry no atom.** The template's flow is its carrier's. Over the sequent alphabet, whose only atom is the command at the root, every member's flow equals it. Over an alphabet whose every node is a command position, a member whose arm has more than one node carries more atom occurrences than the template's metavariable does, and its flow differs.
- **Alternatives.** A template per member group without a pricing gate loses wherever members share little, and the measured classes show most do not pay: one varying entry and every member distinct grow `s` with the family. A per-member check without the cache keeps the quadratic. Checking an arm with the other entries instantiated to one member's arms makes the verdict depend on that member, so it cannot be memoized per triple. The design this follows generalizes the peaks alone, takes each member's join by replay, and checks discrimination transparency per cell at the recorded positions; generalizing the joins with the peaks gives the inheritance check a pattern to land on without reading a skolemized replay back into one, and refuses by name a family whose joins differ where its peaks do not, while the replay check subsumes the per-cell one.
- **Limits.** Checking an arm with every other entry a skolem constant is conservative: when an entry stands at a position a recorded cell reads — which an honest family never has, since its members share every head a cell reads — every other entry's check stops there too. The generated corpus pays only where it is regular: over the fused certificates of both alphabets and the sequent alphabet's completion certificates, families of 64 members with two small arms per entry are emitted with `s` between 14 and 32 and `f` between 38 and 46; families of 2 and 8 members, families with one entry varying across members, and families whose every member is distinct do not pay.
- **Reversal.** A family source whose members share larger arms, or a producer that groups members by skeleton across a whole store, can lower the size at which the gate pays; a consumer that needs the template persisted, or the cache across runs, moves the cache to the memo with its own key and invalidation.

## Boundary wrappers

The crate owns the nominal wrappers its own signatures cross: counts, indices and verdicts over events, flows and webs. It reads `StepIndependence` from the engine and `FiringPermission` and `PositionStep` from the substrate. A wrapper in the substrate would make every new reader a substrate change; a wrapper a second crate reads moves to the lowest crate both depend on.

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
