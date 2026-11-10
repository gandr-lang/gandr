# gandr-surface-dispatcher

Routes an understood `gandr` driver invocation to the outcome the driver renders, and composes the surface pipeline the `check`, `test` and `run` verbs run: parse, lower, check, settle, over every source under the paths given, and for `run` the run stage after the check: focus, run on the L machine, read back. The `fmt` verb reaches the same paths and lays each source out through `gandr-surface-format`.

<!-- toc -->
- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Where the detail lives](#where-the-detail-lives)
- [References](#references)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** `dispatch` maps an `Invocation` to an `Outcome`. A bare invocation maps to `Outcome::Status`, `check` and `test` to the `Walk` of `Outcome::Run`, `run` to `Outcome::Script` and `stage` to `Outcome::Stage`. `Walk::visit` composes each import-connected component once and hands each source its share of the verdict in walk order ([`walk`](src/walk.rs), [`compose`](src/compose.rs)). A `RunReport` counts each step, and its `verdict` is the gate of the driver's exit code. [`script`](src/script.rs) and [`stage`](src/stage.rs) state the run and the stage verbs.

**Why.** The driver owns the argument surface and the process boundary; what an understood invocation does belongs to a library, so routing, composition and the gate can be enumerated without a process.

**How.** `dispatch` is a total match over the closed `Invocation` enum.

## Provided features

- `Invocation`, `Outcome`, `StatusReport` and `dispatch`: routing.
- `Width` and `Threads`: how many threads a walk lowers its sources on, the host's physical performance cores by default.
- `compose`, `compose_on`, `Scheduling`, `Composed`, `ComposeFault`, `LoweringCount` and `ParsedBytes`: the composition, on either schedule.
- `lower_source`, `lower_parsed`, `Lowering`, `Lowered` and `judge_module`: the composition's two halves, for a caller that keeps the lowered module beside the verdicts; `lower_parsed` lowers a parse the caller made.
- `lay_out`, `Laid`, `laid::Absent`, `lower_unit_source`, `lower_parsed_unit` and `judge_member`: one source composed over its import closure. `lower_closure`, `lower_resumed_unit`, `Unheld`, `JudgedClosure`, `lower_onto_closure`, `judge_member_after` and `Checking`: a closure lowered and judged once for every document laid after it. `Recorded` and `Recording`: a revision that moves no lowered node takes the verdicts of the one before ([`compose`](src/compose.rs)).
- `judge`, `Judged`, `Admission` and `admitted::Absent`: the judging half split at the kernel admission, under a `HostGrant`; `Admission::admit_resuming` and `Resumption` resume its leading declarations from an earlier readmission's record; `install_verdict_cache` keeps kernel verdicts in `StoredVerdicts` ([`verdicts`](src/verdicts.rs), [`receipts`](src/receipts.rs)). `install_admission_policy` and `admitted_tally`: the admission policy ([`tier`](src/tier.rs)).
- `spellings` and `failures` on `Composed::Settled`: the `TypeSpellings` and the `Failures` that a face reads each checker refusal through ([`compose`](src/compose.rs)).
- `Entries` and `entries`: what one step prints under a verb, in order, each a diagnostic the diagnostics model builds ([`entry`](src/entry.rs)).
- `Lints`, `Reach` and `Entries::linting`: the lints an invocation enables and where each reaches ([`report`](src/report.rs)). `inferred` and `runs` on `Composed::Settled` hold what `explicit-exits` and `explicit-runs` report ([`compose`](src/compose.rs)).
- `shadowed` on `Composed::Settled`: every builtin the source's declarations and binders shadowed under the warn-and-allow policy.
- `adapt`: the lowering's module as checker declaration input.
- `TypeTable`, `TypedSpan`, `Subject`, `Declared`, `typing::Absent` and `checked_against::Absent`: the type of every node of one source a face can point at, from one typed run of the checker. `TypeTable::of_parsed`, `of_parsed_unit` and `of_parsed_after` type a parse the caller holds ([`typed`](src/typed.rs)). `TypeTable::shadows` and `hidden_at`: each binder that hides a binding.
- `SourceRoot` and `classify`: the root a source sits under, by its path.
- `Walk`, `Walk::visit`, `Step`, `Standing`, `Standing::of` and `SourceFault`: the walk at any width, and the standing a step or a session submission carries.
- `HostGrant`, `OperationName`, `WorldName`, `AuthorityError` and `Walk::granting`: the host operations every capability a checked declaration holds is bounded by, and the worlds every declaration is entered at, read against the worlds each module declares; `compose` and `test` judge under neither.
- `RunReport`, `RunVerdict`, `SourceCounts`, `SourceCount`, `Verb`, `Goals`, `Shown` and `shown`: the runner's report, the gate and what each verb prints.
- `Exercised` and `Row`: the fragment's exercised table.
- `Program`, `Evaluation`, `ValueSpelling`, `Unfinished`, `Unrunnable`, `RunStatus`, `last_declared::Absent` and `declaration_name::Absent`: the run stage.
- `Script`, `ScriptRun`, `Ran`, `execute`, `run_source` and `host`: the run and host verbs; where migrations go is [`worlds`](src/evaluate/worlds.rs)'s.
- `ProgramSpec`, `SpecError`, `Staging`, `StageRun`, `Staged`, `StageFault`, `StageVerdict`, `PoolFault` and `RunDigest`: the stage verb.
- `Formatting`, `FormatStep`, `FormatFault`, `Rewrite` and `walk_step::Absent`: the format verb, and why its traversal reaches nothing further.
- `Census`, `CensusStep`, `CensusFault` and `CellRow`: the cells verb ([`cells`](src/cells.rs)).
- `measure`, `Measure`, `measured::Absent`, `Walk::measuring`, `Positioning`, `ArtifactPositions`, `Placed` and `positioned::Absent`: each declaration's artifact sizes and tally ([`measure`](src/measure.rs)).
- `Generations`, `Watch`, `Retired`, `Submitted`, `Delivered`, `delivery::Absent`: keyed jobs on the pool; a newer key retires a slot's older generation ([generation](src/generation.rs)).
- The corpus's two roots, run through the walk, and their witnesses: [`src/lib.rs`](src/lib.rs) § The corpus runs through the walk.

## Expected features

- **A renderer.** The caller renders each `Outcome`, and each diagnostic `entries` yields from a `Step`: `gandr-surface-render-terminal` lays one out for a terminal, `gandr-surface-lsp` publishes it to an editor. A diagnostic carries the lines of source it covers, its loci and the types its refusal names, so a face renders it without composing the source again.
- **A file system.** `Walk::visit` lists directories and reads sources, `Formatting::step` reads them and writes a changed layout back, and `Census::step` reads them; every failure to do so is a fault step, never a panic.
- **Threads.** `Walk::visit`, `Staging::run` and `Formatting::visit` fork on the driver's [`Pool`](src/pool.rs).

## Examples

```rust
use core::ops::ControlFlow;

use gandr_surface_dispatcher::Goals;
use gandr_surface_dispatcher::Invocation;
use gandr_surface_dispatcher::Outcome;
use gandr_surface_dispatcher::Pool;
use gandr_surface_dispatcher::Step;
use gandr_surface_dispatcher::Width;
use gandr_surface_dispatcher::dispatch;

fn run(paths: Vec<std::path::PathBuf>) {
    let invocation = Invocation::Check { goals: Goals::Gated, paths, width: Width::PerformanceCores };
    let Outcome::Run { verb, walk, width } = dispatch(invocation)
    else {
        return;
    };
    let ControlFlow::Continue(report) = walk.visit(&Pool::new(width), |step| -> ControlFlow<core::convert::Infallible> {
        if let Step::Fault { path, fault } = step {
            eprintln!("{}: {fault}", path.display());
        }
        ControlFlow::Continue(())
    });
    println!("{report}\nverdict: {}", report.verdict(verb));
}
```

Run the tests:

```sh
cargo nextest run -p gandr-surface-dispatcher
```

## Where the detail lives

Mechanism, decisions with their alternatives and reversals, and witnesses live in the rustdoc beside the code:

| Topic | Module |
| ----- | ------ |
| Routing, specification evidence, optional tracing | [`src/lib.rs`](src/lib.rs) |
| One composition, the kernel's re-derivation, a component judged once | [`compose`](src/compose.rs), [`component`](src/component.rs) |
| The run stage, native universe-path boundaries | [`evaluate`](src/evaluate.rs) |
| What each verb prints of a step | [`entry`](src/entry.rs) |
| Reading before judging, forking by component, judgement in walk order | [`walk`](src/walk.rs) |
| The driver's pool, the reader | [`pool`](src/pool.rs), [`reader`](src/reader.rs) |
| The default width | [`width`](src/width.rs) |
| Membership, the pending set | [`root`](src/root.rs) |
| Faults, unsettled declarations and goals | [`report`](src/report.rs) |
| The exercised table | [`exercised`](src/exercised.rs) |
| The stage verb | [`stage`](src/stage.rs) |
| The format verb | [`format`](src/format.rs) |
| The ledger verb | [`ledger`](src/ledger.rs) |

## References

- `Gavazzo-2022-quantitative_metric_rewriting_abstract_nonexpansive_graded_systems` — exemplar: § 8.2's Lemma 9, the stretch of one step bounded by how often the contractum writes a hole — the count the census reports per cell.
- `vault:01a178aa-d585-7822-9cf0-40459729a925` — background: the package design's typed manifests — metadata is gandr, so the manifest is output, never read.
- `vault:01a17cb3-d471-72b2-9bd2-70a46f74c3de` — background: one store.
- `vault:01a178aa-6e2c-7720-a0bd-c5e1f9c4e08e` — background: the quantities design (§ quant-try-first) — the census reports each cell's counts.
- `vault:01a178aa-6a53-7ec2-b60c-2de66202cf07` — lineage: the refusal `FootprintsOverlap`, which no exercised row counts.
- `vault:01a178aa-6b8e-7d60-a533-ec9379c0462a` — background: the futures try-first.
- `vault:01a178aa-6917-7983-b5cd-86e2af86b3ec` — lineage: a thunk's captures, which the writer rule leaves unread.
- `vault:01a178aa-ce14-7610-bcad-5aab5f9c0b0f` — lineage: § kernel-verdict-reuse — only a cache a driver installs recalls; the rest recheck.
- `vault:01a1897b-d199-7d10-a325-587b76db2508` — lineage: § The design — the stored strata.
- `vault:01a178ab-17e5-7352-bc0b-3caa7f1e476c` — lineage: the storage programme's worlds.
- `vault:01a17f02-42f0-7920-bede-5615d3bade8c` — background: the compilation ruling — a run is a local artifact.
- `vault:01a178aa-9a6d-7c20-a9c5-131d35beda06` — background: a source its flow refuses answers at no site.
- `vault:01a178ab-289d-7702-b010-1c47ae9fd427` — background: a failed translation refuses its importer.
- `vault:01a18584-cd93-7e42-9b53-9deb10b838fc` — background: the blind check the tier meets a pair by.
- `vault:01a18572-6e13-7412-bc74-aa6a24d157c4` — background: Catt's artifact sizes.
- `vault:01a178aa-655f-72f2-97ee-298c0647e1e5` — background: the sharing ratio of iterated composites.
- `vault:01a051fd-25fd-7f24-a5d4-a72eca18a687` — lineage: the shared and unshared sizes of one table.
- `vault:01a178aa-a419-7ab1-82e7-40a4f95938c6` — anchor: the first adapter of exact reals, a handle to a plan the host holds.
- `vault:01a1aa2d-a69c-7030-91e0-337d68d88151` — anchor: § presented-spaces-crates puts the adapter of stage C here.
- `vault:01a178aa-a7bd-7d03-a728-feae5af9d1a8` — anchor: a draw's native handler.
- `vault:01a178ab-2ecf-7893-afda-f14010a8acbe` — exemplar: the namespace design — a shadow is an event, never a prohibition.
- `Taylor-2010-lambda_calculus_real_analysis` — exemplar: Taylor, _JLA_ 2:5, 2010, `doi:10.4115/jla.2010.2.5` — the laws a cut owes.
- `Escardó-2004-synthetic_topology_data_types_classical_spaces` — exemplar: Escardó, _ENTCS_ 87, 2004, `doi:10.1016/j.entcs.2004.09.017` — a comparison as an open.
- `Ahrens-2025-weighted_rewriting_semiring_semantics_abstract_reduction_systems` — newest: Ahrens, Kassing, Giesl and Katoen, 2025, `arXiv:2505.08496` — a row's bound as a semiring product.
- `Hadzihasanovic-2023-higherdimensional_subdiagram_matching` — newest: Hadzihasanovic and Kessler, 2023, `arXiv:2304.09216` — a fresh name for each internal wire.

## License

Apache-2.0 WITH LLVM-exception. The licence text is at the repository root.
