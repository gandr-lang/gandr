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

**What.** `dispatch` maps an `Invocation` to an `Outcome`. A bare invocation routes to `Outcome::Status`. `Invocation::Check` and `Invocation::Test` route to `Outcome::Run`: a `Walk` over the paths given, the `Verb` it runs under and the `Width` it is visited at. `Walk::visit` reads every source under the paths and carries each import-connected component once through the composition — parse, lower once, `adapt`, judge, the kernel's re-derivation, the `Program` that runs an accepted declaration, and the settle comparison — and hands each source its share of the verdict, in walk order. Each step is counted into a `RunReport`, whose `verdict` is the gate the driver's exit code reports. `Invocation::Run` routes to `Outcome::Script`: a `Script` of one path and its arguments, composed as `check` would, which runs its entry or hosts its worlds as [`script`](src/script.rs) states. `Invocation::Stage` routes to `Outcome::Stage`, a `Staging` checked as [`stage`](src/stage.rs) states.

**Why.** The driver owns the argument surface and the process boundary; what an understood invocation does belongs to a library, so routing, composition and the gate can be enumerated without a process. The composition sits here, above the corpus library and the checker, because the settle comparison and the root guard must fire on the same pass that gates.

**How.** `dispatch` is a total match over the closed `Invocation` enum.

## Provided features

- `Invocation`, `Outcome`, `StatusReport` and `dispatch`: routing.
- `Width` and `Threads`: how many threads a walk lowers its sources on, the host's physical performance cores by default.
- `compose`, `Composed`, `ComposeFault`, `LoweringCount` and `ParsedBytes`: the composition.
- `lower_source`, `lower_parsed`, `Lowering`, `Lowered` and `judge_module`: the composition's two halves, for a caller that keeps the lowered module beside the verdicts; `lower_parsed` lowers a parse the caller made.
- `lay_out`, `Laid`, `laid::Absent`, `lower_unit_source`, `lower_parsed_unit` and `judge_member`: one source composed over its import closure, the component it makes when given alone; a source read whole is parsed once per process, and a settled file read from disk once while a `stat` reads it unchanged. `lower_closure`, `lower_resumed_unit` and `Unheld`: an import closure lowered once and resumed for each document laid after it. `JudgedClosure`, `lower_onto_closure`, `judge_member_after` and `Checking`: the closure's own declarations judged, focused, settled and spelled once, and each document judged after them on a copy of the state they left. `Recorded` and `Recording`: a revision whose lowering moves no node of the one judged before it takes that judgement's verdicts, and settles and spells again at its own spans.
- `judge`, `Judged`, `Admission` and `admitted::Absent`: the judging half split at the kernel admission, under a `HostGrant`, for a caller that renders the report before the kernel is offered the module; `Admission::admit_resuming` and `Resumption` resume its leading declarations from an earlier readmission's record; `install_verdict_cache` keeps kernel verdicts ([`verdicts`](src/verdicts.rs)).
- `spellings` and `failures` on `Composed::Settled`: the diagnostics model's `TypeSpellings` of the types a module's checker refusals compare and its failures name, spelled while its arena was at hand, and the `Failures` the checking machine kept for each refused body, by admission position.
- `Entries` and `entries`: what one step prints under a verb, in order, each a diagnostic the diagnostics model builds — refusals, unsettled declarations, goals, shadowing warnings, lint findings and ledger lines.
- `Lints`, `Reach` and `Entries::linting`: the lints an invocation enables; a lint reaches every source when enabled, and otherwise only the declarations and modules whose attribute asks for it, `Lints::asking_effects` narrowing `explicit-runs` to the runs that perform an effect. `inferred` on `Composed::Settled` holds the exits the lowering inferred, which the `explicit-exits` lint reports, and `runs` the runs the checker inferred, which the `explicit-runs` lint reports.
- `shadowed` on `Composed::Settled`: every builtin the source's declarations and binders shadowed under the warn-and-allow policy, in the order shadowed, copied out of the lowered module's `Recognition` before its origin table moves; a face reports each as a warning.
- `adapt`: the lowering's module as checker declaration input.
- `TypeTable`, `TypedSpan`, `Subject`, `Declared`, `typing::Absent` and `checked_against::Absent`: the type of every node of one source a face can point at — each binder, term and written type with its span, spelled when a face asks, with the type a term was checked against when it differs — and each declaration's type or refusal under both its signature's and its definition's keys, from one typed run of the checker; `TypeTable::of_parsed` and `TypeTable::of_parsed_unit` type a parse the caller holds, and `TypeTable::of_parsed_after` types it after a judged closure's state.
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
- `Generations`, `Watch`, `Retired`, `Submitted`, `Delivered`, `delivery::Absent`: keyed jobs on the pool; a newer key retires a slot's older generation ([generation](src/generation.rs)).
- The corpus's two roots, run through the walk, and their witnesses: [`src/lib.rs`](src/lib.rs) § The corpus runs through the walk.

Each nontrivial operation states a contract or an exemption, and an adequacy claim naming its witnesses. The boundary evidence includes:

| Surface | Observed boundary |
| ------- | ----------------- |
| [Reports](src/report.rs) and [exercised rows](src/exercised.rs) | Saturating counts preserve unrelated fields; repeated row assignments retain the last value. |
| [Corpus registration](tests/corpus.rs) | A directory with a source extension is traversed rather than registered as a source. |

## Expected features

- **A renderer.** The caller renders each `Outcome`, and each diagnostic `entries` yields from a `Step`: `gandr-surface-render-terminal` lays one out for a terminal, `gandr-surface-lsp` publishes it to an editor. A diagnostic carries the lines of source it covers, its loci and the types its refusal names, so a face renders it without composing the source again.
- **A file system.** `Walk::visit` lists directories and reads sources, `Formatting::step` reads them and writes a changed layout back, and `Census::step` reads them; every failure to do so is a fault step, never a panic.
- **Threads.** `Walk::visit`, `Staging::run` and `Formatting::visit` fork on the driver's [`Pool`](src/pool.rs), whose `rayon` threads start once per process; its default width is the host's physical performance cores ([width](src/width.rs)).

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
| Routing, optional tracing | [`src/lib.rs`](src/lib.rs) |
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
- `vault:01a178aa-d585-7822-9cf0-40459729a925` — background: the package design's typed manifests — metadata is gandr, so `gandr.toml` is output, never read.
- `vault:01a17cb3-d471-72b2-9bd2-70a46f74c3de` — background: one store.
- `vault:01a178aa-6e2c-7720-a0bd-c5e1f9c4e08e` — background: the quantities design (§ quant-try-first) — the census reports each cell's counts.
- `vault:01a178aa-6a53-7ec2-b60c-2de66202cf07` — lineage: the refusal `FootprintsOverlap`, which no exercised row counts.
- `vault:01a178aa-6b8e-7d60-a533-ec9379c0462a` — background: the futures try-first.
- `vault:01a178aa-ce14-7610-bcad-5aab5f9c0b0f` — lineage: § kernel-verdict-reuse — only a cache a driver installs recalls; the rest recheck.
- `vault:01a178ab-17e5-7352-bc0b-3caa7f1e476c` — lineage: the storage programme's worlds.
- `vault:01a17f02-42f0-7920-bede-5615d3bade8c` — background: the compilation ruling — a run is a local artifact.

## License

Apache-2.0 WITH LLVM-exception. The licence text is at the repository root.
