# gandr-surface-dispatcher

Routes an understood `gandr` driver invocation to the outcome the driver renders, and composes the surface pipeline the `check`, `test` and `run` verbs run: parse, lower, check, settle, over every source under the paths given, and for `run` the run stage after the check: focus, run on the L machine, read back. The `fmt` verb reaches the same paths and lays each source out through `gandr-surface-format`.

<!-- toc -->
- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Where the detail lives](#where-the-detail-lives)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** `dispatch` maps an `Invocation` to an `Outcome`. A bare invocation routes to `Outcome::Status`, whose `StatusReport` states that toolchain management is not implemented. `Invocation::Check` and `Invocation::Test` route to `Outcome::Run`: a `Walk` over the paths given, the `Verb` it runs under and the `Width` it is visited at. `Walk::visit` reads every source under the paths and carries each import-connected component once through the composition — parse, lower once, `adapt`, judge, the kernel's re-derivation, the `Program` that runs an accepted declaration, and the settle comparison — and hands each source its share of the verdict, in walk order. Each step is counted into a `RunReport`, whose `verdict` is the gate the driver's exit code reports. `Invocation::Run` routes to `Outcome::Script`: a `Script` of one path, which composes its source as `check` would and runs the last name it declares, its `RunStatus` the exit code `gandr run` reports. `Invocation::Stage` routes to `Outcome::Stage`: a `Staging` of staged programs, each checked through the checker's program entry on a pool of the run's width, its `StageRun` carrying each program's check, the run's digest and its verdict.

**Why.** The driver owns the argument surface and the process boundary; what an understood invocation does belongs to a library, so routing, composition and the gate can be enumerated without a process. The composition sits here, above the corpus library and the checker, because the settle comparison and the root guard must fire on the same pass that gates.

**How.** `dispatch` is a total match over the closed `Invocation` enum. `compose` is `lower_source` then `judge_module`, two short functions, and `judge_module` is `judge` then `Judged::admit`; the only call into the lowering sits in a private module that counts each source it lowers. The walk lists directories with an explicit stack, classifies each source by its canonical path and reads every source through its reader before judging any; it forks parse and lower by component onto the driver's pool, sharing one atomic cursor. A staging builds its programs and hands each to `gandr-core-checker`'s `staging::check` with the pool as the checker's fork.

## Provided features

- `Invocation`, `Outcome`, `StatusReport` and `dispatch`: routing.
- `Width` and `Threads`: how many threads a walk lowers its sources on, the host's physical performance cores by default.
- `compose`, `Composed`, `ComposeFault`, `LoweringCount` and `ParsedBytes`: the composition.
- `lower_source`, `lower_parsed`, `Lowering`, `Lowered` and `judge_module`: the composition's two halves, for a caller that keeps the lowered module beside the verdicts; `lower_parsed` lowers a parse the caller made.
- `lay_out`, `Laid`, `laid::Absent`, `lower_unit_source`, `lower_parsed_unit` and `judge_member`: one source composed over its import closure, the component it makes when given alone; a source read whole is parsed once per process, and a settled file read from disk once while a `stat` reads it unchanged. `lower_closure`, `lower_resumed_unit` and `Unheld`: an import closure lowered once and resumed for each document laid after it. `JudgedClosure`, `lower_onto_closure`, `judge_member_after` and `Checking`: the closure's own declarations judged, focused, settled and spelled once, and each document judged after them on a copy of the state they left.
- `judge`, `Judged`, `Admission` and `admitted::Absent`: the judging half split at the kernel admission, under a `HostGrant`, for a caller that renders the report before the kernel is offered the module; `Admission::admit_resuming` and `Resumption` resume its leading declarations from an earlier readmission's record.
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
- `Exercised` and `Row`: the fragment's exercised table, counted.
- `Program`, `Evaluation`, `ValueSpelling`, `Unfinished`, `Unrunnable`, `RunStatus`, `run_target::Absent` and `declaration_name::Absent`: the run stage.
- `Script`, `ScriptRun`, `Ran`, `execute` and `run_source`: the run verb.
- `ProgramSpec`, `SpecError`, `Staging`, `StageRun`, `Staged`, `StageFault`, `StageVerdict`, `PoolFault` and `RunDigest`: the stage verb.
- `Formatting`, `FormatStep`, `FormatFault`, `Rewrite` and `walk_step::Absent`: the format verb, and why its traversal reaches nothing further.
- The corpus's two roots, run through the walk, and their witnesses: [`src/lib.rs`](src/lib.rs) § The corpus runs through the walk.

Each nontrivial operation states an executable contract or a local exemption, plus a bounded adequacy claim pointing to its witnesses. The boundary evidence includes:

| Surface | Observed boundary |
| ------- | ----------------- |
| [Reports](src/report.rs) and [exercised rows](src/exercised.rs) | Saturating counts preserve unrelated fields; repeated row assignments retain the last value. |
| [Filesystem walk](src/walk.rs) | Explicit links retain their reported path and use their target for classification; a visit at three threads yields the serial visit's rows and report, and a stopped visit hands over nothing more; a diamond of importers is lowered once. |
| [Host width](src/width.rs) | A second hardware thread shares its core; a hybrid processor counts its performance cores alone; a missing, malformed or backwards CPU list reports no count rather than a guess. |
| [Evaluation](src/evaluate.rs) | Each declaration stands at its admission position, a skipped position holding none; terminal classification preserves declaration identity; nested fields retain order and repeated references. |
| [Corpus registration](tests/corpus.rs) | A directory with a source extension is traversed rather than registered as a source. |

## Expected features

- **A renderer.** The caller renders each `Outcome`, and each diagnostic `entries` yields from a `Step`: `gandr-surface-render-terminal` lays one out for a terminal, `gandr-surface-lsp` publishes it to an editor. A diagnostic carries the lines of source it covers, its loci and the types its refusal names, so a face renders it without composing the source again. `StatusReport`'s `Display` writes one sentence and no line terminator; `RunReport`'s writes its counts one per line, without a trailing terminator.
- **A file system.** `Walk::visit` lists directories and reads sources, and `Formatting::step` reads them and writes a changed layout back; every failure to do so is a fault step, never a panic.
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

## License

Apache-2.0 WITH LLVM-exception. The licence text is at the repository root.
