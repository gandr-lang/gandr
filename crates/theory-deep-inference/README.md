# gandr-theory-deep-inference

The identity relations on derivations: when two derivations that fire the same cells in different orders are one derivation, and the structure that decides it.

<!-- toc -->
- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Where the detail lives](#where-the-detail-lives)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** The identity layer over the rewriting engine's derivations, generic over `CellAlphabet`. `derive_shift_equivalence` earns the witness that two adjacent applications commute; `event_order` builds the finite partial order of one recorded derivation's events, with its canonical schedule, its layering and the exchange witness between two of its sequentializations; `normalize` and `normalize_certified` factor a derivation into content-addressed primitives with multiplicities, scheduled canonically, and compare the result by `nf_equal`, `nf_equal_across_stores`, `certified_nf_equal` and `tracelets_nf_equal`; `ReplayPlan` projects a certified derivation into antichain levels with its critical-path fuel; `causal_web` and `refines` read the order as a two-colour web and compare two webs over one event set; `project_flow` and `flows_equal` give a leg's atomic flow; `match_footprint` and `footprint_independence` give the polarized read and write footprint the shift guard is measured against; `anti_unify_tracelets` folds a family of certificates sharing one skeleton into a `GuardedTemplate` where that pays, each member admitted by instantiation and replay.

**Why.** Completion and fusion produce many certificates for one boundary, and a consumer that keys, deduplicates or schedules them needs to know when two are the same derivation without replaying both every time. Replay in `gandr-theory-coherent-resolutions` stays the semantic oracle; every relation here is a sound fast path below it, decidable from certificate data, whose positive answer implies replay equivalence and whose negative answer is never read as distinctness. The causal order also answers what a scheduler needs: which steps could fire together, and how much sequential fuel a complete replay consumes.

**How.** One independence relation, the shift guard, decides which adjacent applications commute: incomparable positions, no overlap between the two cells, and the alphabet's convexity discharge, confirmed by replaying both sequentializations from one peak with the engine's `replay_from_peak`. The causal order reads that relation as dependence, layers events by causal depth and orders each layer by a content-derived key that digests the event's causal past, refusing a tie rather than breaking it by arrival. The normal form, the replay plan, the web and the flow are read off that one order; none computes a second dependence relation. Every walk keeps its stack on the heap, so a derivation far longer than the thread's stack is ordered, normalized and projected. Absence and refusal are values: a lookup that finds nothing returns `Maybe` with its reason, and a refused operation returns `Result` with a typed obstruction.

## Provided features

- `derive_shift_equivalence`, `ShiftEquivalence`, `ShiftObstruction`: the earned witness that two adjacent applications commute, its two sequentializations confirmed by replay from one peak, and the conjunct that refuses a pair.
- The shift witness's tiles form an asynchronous graph: symmetric, deterministic, and satisfying the cube property over the fixture family, searched rather than assumed.
- `event_order`, `EventOrder`, `DerivationEvent`, `EventKey`, `ExchangeWitness`, `Transposition`, `ExchangeObstruction`, `KeyCollision`, `event_lookup`, `exchange_application`: the finite event partial order of one derivation, its canonical schedule and layering, and the exchange witness between two sequentializations.
- `normalize`, `normalize_certified`, `TraceletNf`, `ReplayWitness`, `PrimCert`, `NormalFormObstruction`, `schedule_resolution`: the certificate normal form and its replay receipt.
- `nf_equal`, `nf_equal_across_stores`, `certified_nf_equal`, `tracelets_nf_equal`: the four normal-form relations, each a sound under-approximation of replay equivalence.
- `ReplayPlan`, `replay_fuel`: antichain replay levels with critical-path fuel, replayed level by level or whole.
- `prim_address`, `cell_address`, `causal_past_address`, `PrimId`, `CellAddress`, `CausalPast`: build-local content addresses that order and key within one process.
- `causal_web`, `CausalWeb`, `DependenceBits`, `WebRelation`, `refines`, `RefinementVerdict`, `RefinementCounterexample`, `SliceChain`, `SliceStep`, `HomomorphismFrontier`, `web_lookup`: the two-colour web of one event order, and refinement between two webs over one event set with a witness either way and named frontiers for everything else.
- `project_flow`, `tracelet_flow`, `Flow`, `FlowThread`, `FlowEnd`, `TraceletFlow`, `FlowObstruction`, `flows_equal`, `legs_flow_equal`, `tracelets_flow_equal`, `flow_canonical`: the atomic-flow projection of a leg and of a certificate, and flow equality.
- `match_footprint`, `MatchFootprint`, `footprint_independence`, `FootprintIndependence`, `FootprintObstruction`: the read and write footprint of one application and the polarized independence test.
- Every walk keeps its stack on the heap: a dependence chain far longer than a small thread's stack is ordered, normalized, projected to a flow and a web, and dropped inside that thread.
- `anti_unify_tracelets`, `GuardedTemplate`, `TemplateEntry`, `TemplateArm`, `TemplateRefusal`, `TemplateObstruction`, `InheritanceCache`, `InheritanceKey`, `InheritanceVerdict`, `TemplateLeg`, `TemplateAddress`, `ArmAddress`, `ProductionCounts`, `FamilyCostReport`, `inheritance_lookup`: the guarded template of a certificate family, emitted only below its expansion factor, its inheritance check memoized per content triple for one run, members admitted by instantiation and replay, and the family's cost with the template and without.
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

Run the tests:

```sh
cargo nextest run -p gandr-theory-deep-inference
RUSTFLAGS="--cfg anodized_panic" CARGO_TARGET_DIR=target/enforcing cargo nextest run -p gandr-theory-deep-inference
```

## Where the detail lives

Mechanism, decisions with their alternatives and reversals, and witnesses live in the rustdoc beside the code:

| Topic | Module |
| ----- | ------ |
| Shift equivalence | [`shift`](src/shift.rs) |
| The causal order | [`causal`](src/causal.rs) |
| The certificate normal form, replay plans, content addresses | [`normal_form`](src/normal_form.rs) |
| The causal web and refinement | [`causal_web`](src/causal_web.rs) |
| The flow projection | [`flow`](src/flow.rs) |
| The footprint relation | [`footprint`](src/footprint.rs) |
| The guarded template | [`template`](src/template.rs) |
| Boundary wrappers | [`boundary`](src/boundary.rs) |
| An example of a refused pair, oracle tests over the engine, specification evidence, references | [`src/lib.rs`](src/lib.rs) |

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
