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

**What.** `dispatch` maps an `Invocation` to an `Outcome`. A bare invocation routes to `Outcome::Status`, whose `StatusReport` states that toolchain management is not implemented. `Invocation::Check` and `Invocation::Test` route to `Outcome::Run`: a `Walk` over the paths given, the `Verb` it runs under and the `Width` it is visited at. Advancing the walk with `Walk::step` reads one source at a time and carries it through `compose`, which parses it, lowers it once, adapts the lowered declarations to the checker's input with `adapt`, judges them, has the kernel re-derive every acceptance, builds the `Program` that runs any accepted declaration, and settles each declaration against what it states. `Walk::visit` hands every step to a visitor in the same order; above `Width::SERIAL` it parses and lowers the sources on a pool of threads first, largest first, and judges each in walk order. Each step is counted into a `RunReport`, whose `verdict` is the gate the driver's exit code reports. `Invocation::Run` routes to `Outcome::Script`: a `Script` of one path, which composes its source as `check` would and runs the last name it declares, its `RunStatus` the exit code `gandr run` reports. `Invocation::Stage` routes to `Outcome::Stage`: a `Staging` of staged programs, each checked through the checker's program entry on a pool of the run's width, its `StageRun` carrying each program's check, the run's digest and its verdict.

**Why.** The driver owns the argument surface and the process boundary; what an understood invocation does belongs to a library, so routing, composition and the gate can be enumerated without a process. The composition sits here, above the corpus library and the checker, because the settle comparison and the root guard must fire on the same pass that gates.

**How.** `dispatch` is a total match over the closed `Invocation` enum. `compose` is `lower_source` then `judge_module`, two short functions, and `judge_module` is `judge` then `Judged::admit`; the only call into the lowering sits in a private module that counts it. The walk lists directories with an explicit stack and classifies each source by its canonical path; stepped, it keeps one source's text at a time, and visited wider, it forks parse and lower by source onto scoped threads that share one atomic cursor. A staging builds its programs and hands each to `gandr-core-checker`'s `staging::check` with a `rayon` pool as the checker's fork.

## Provided features

- `Invocation`, `Outcome`, `StatusReport` and `dispatch`: routing.
- `Width` and `Threads`: how many threads a walk lowers its sources on, the host's physical performance cores by default.
- `compose`, `Composed`, `ComposeFault` and `LoweringCount`: the composition.
- `lower_source`, `lower_parsed`, `Lowering`, `Lowered` and `judge_module`: the composition's two halves, for a caller that keeps the lowered module beside the verdicts; `lower_parsed` lowers a parse the caller made.
- `judge`, `Judged`, `Admission` and `admitted::Absent`: the judging half split at the kernel admission, for a caller that renders the report before the kernel is offered the module.
- `spellings` and `failures` on `Composed::Settled`: the diagnostics model's `Spellings` of the types a module's checker refusals compare and its failures name, spelled while its arena was at hand, and the `Failures` the checking machine kept for each refused body, by admission position.
- `Entries` and `entries`: what one step prints under a verb, in order, each a diagnostic the diagnostics model builds — refusals, unsettled declarations, goals, shadowing warnings and ledger lines.
- `shadowed` on `Composed::Settled`: every builtin the source's declarations and binders shadowed under the warn-and-allow policy, in the order shadowed, copied out of the lowered module's `Recognition` before its origin table moves; a face reports each as a warning.
- `adapt`: the lowering's module as checker declaration input.
- `TypeTable`, `TypedSpan`, `Subject`, `Declared`, `typing::Absent` and `checked_against::Absent`: the type of every node of one source a face can point at — each binder, term and written type with its span, spelled when a face asks, with the type a term was checked against when it differs — and each declaration's type or refusal under both its signature's and its definition's keys, from one typed run of the checker.
- `SourceRoot` and `classify`: the root a source sits under, by its path.
- `Walk`, `Walk::visit`, `Step`, `Standing`, `Standing::of`, `SourceFault` and `walk_step::Absent`: the walk at any width, and the standing a step or a session submission carries.
- `RunReport`, `RunVerdict`, `SourceCounts`, `SourceCount`, `Verb`, `Goals`, `Shown` and `shown`: the runner's report, the gate and what each verb prints.
- `Exercised` and `Row`: the fragment's exercised table, counted.
- `Program`, `Evaluation`, `ValueSpelling`, `Unfinished`, `Unrunnable`, `RunStatus`, `run_target::Absent` and `declaration_name::Absent`: the run stage.
- `Script`, `ScriptRun`, `Ran`, `execute` and `run_source`: the run verb.
- `ProgramSpec`, `SpecError`, `Staging`, `StageRun`, `Staged`, `StageFault`, `StageVerdict`, `PoolFault` and `RunDigest`: the stage verb.
- `Formatting`, `FormatStep`, `FormatFault` and `Rewrite`: the format verb.
- The corpus's two roots, run through the walk: `corpus::corpus::the_strict_root_checks_owing_nothing`, `corpus::corpus::the_fixture_root_settles_every_fixture`, `corpus::corpus::the_two_roots_exercise_every_row`, `corpus::corpus::a_run_lowers_each_source_once`; every run outcome they state, and the focusing of every declaration they accept: `corpus::corpus::l_machine_matches_the_outcome_snapshots_on_the_model_corpus`, `corpus::corpus::l_machine_matches_the_outcome_snapshots_on_the_pathological_corpus`, `corpus::corpus::focusing_is_total_on_the_model_corpus`, `corpus::corpus::focusing_is_total_on_the_pathological_corpus`; and the registration witness (`gandr-surface-corpus`'s `root` module, § One walk registers every source): `corpus::corpus::every_corpus_source_is_registered`, `corpus::corpus::a_planted_orphan_is_not_registered`.

Each nontrivial operation states an executable contract or a local exemption, plus a bounded adequacy claim pointing to its witnesses. The boundary evidence includes:

| Surface | Observed boundary |
| ------- | ----------------- |
| [Reports](src/report.rs) and [exercised rows](src/exercised.rs) | Saturating counts preserve unrelated fields; repeated row assignments retain the last value. |
| [Filesystem walk](src/walk.rs) | Late filesystem changes retain pending sources; exhaustion is stable; explicit links retain their reported path and use their target for classification; a visit at three threads yields the serial walk's rows and report, and a stopped visit hands over nothing more. |
| [Host width](src/width.rs) | A second hardware thread shares its core; a hybrid processor counts its performance cores alone; a missing, malformed or backwards CPU list reports no count rather than a guess. |
| [Evaluation](src/evaluate.rs) | Each declaration stands at its admission position, a skipped position holding none; terminal classification preserves declaration identity; nested fields retain order and repeated references. |
| [Corpus registration](tests/corpus.rs) | A directory with a source extension is traversed rather than registered as a source. |

## Expected features

- **A renderer.** The caller renders each `Outcome`, and each diagnostic `entries` yields from a `Step`: `gandr-surface-render-terminal` lays one out for a terminal, `gandr-surface-lsp` publishes it to an editor. A diagnostic carries the lines of source it covers, its loci and the types its refusal names, so a face renders it without composing the source again. `StatusReport`'s `Display` writes one sentence and no line terminator; `RunReport`'s writes its counts one per line, without a trailing terminator.
- **A file system.** `Walk::step` and `Walk::visit` list directories and read sources, and `Formatting::step` reads them and writes a changed layout back; every failure to do so is a fault step, never a panic.
- **Threads.** `Walk::visit` starts scoped threads from `std`; a thread the host refuses to start leaves its sources to the others. `Staging::run` builds a `rayon` pool of its width once per run, and reports a pool the host refuses as `PoolFault`. The default width reads the host's physical performance cores: `hw.perflevel0.physicalcpu` on macOS, the `cpu_core` CPU list and each CPU's core siblings under `/sys/devices` on Linux; a host that reports neither runs on the parallelism `std` reports.

## Examples

```rust
use core::ops::ControlFlow;

use gandr_surface_dispatcher::Goals;
use gandr_surface_dispatcher::Invocation;
use gandr_surface_dispatcher::Outcome;
use gandr_surface_dispatcher::Step;
use gandr_surface_dispatcher::Width;
use gandr_surface_dispatcher::dispatch;

fn run(paths: Vec<std::path::PathBuf>) {
    let invocation = Invocation::Check { goals: Goals::Gated, paths, width: Width::PerformanceCores };
    let Outcome::Run { verb, walk, width } = dispatch(invocation)
    else {
        return;
    };
    let ControlFlow::Continue(report) = walk.visit(width, |step| -> ControlFlow<core::convert::Infallible> {
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
| One composition, the kernel's re-derivation | [`compose`](src/compose.rs) |
| The run stage, native universe-path boundaries | [`evaluate`](src/evaluate.rs) |
| What each verb prints of a step | [`entry`](src/entry.rs) |
| Forking by source, judgement in walk order | [`walk`](src/walk.rs) |
| The default width | [`width`](src/width.rs) |
| Membership, the pending set | [`root`](src/root.rs) |
| Faults, unsettled declarations and goals | [`report`](src/report.rs) |
| The exercised table | [`exercised`](src/exercised.rs) |
| The stage verb | [`stage`](src/stage.rs) |
| The format verb | [`format`](src/format.rs) |

## License

Apache-2.0 WITH LLVM-exception. The licence text is at the repository root.
