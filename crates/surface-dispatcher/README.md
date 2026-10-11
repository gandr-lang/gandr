# gandr-surface-dispatcher

Routes an understood `gandr` driver invocation to the outcome the driver renders, and composes the surface pipeline the `check`, `test` and `run` verbs run: parse, lower, check, settle, over every source under the paths given, and for `run` the run stage after the check: focus, run on the L machine, read back.

<!-- toc -->

- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [One composition serves both verbs](#one-composition-serves-both-verbs)
- [The run stage follows the check](#the-run-stage-follows-the-check)
- [Native universe-path boundaries](#native-universe-path-boundaries)
- [The kernel re-derives every acceptance](#the-kernel-re-derives-every-acceptance)
- [Routing performs no I/O; the walk is the verb's](#routing-performs-no-io-the-walk-is-the-verbs)
- [Sources fork; judgement keeps walk order](#sources-fork-judgement-keeps-walk-order)
- [Membership is location](#membership-is-location)
- [The pending set](#the-pending-set)
- [A fault outranks an unsettled declaration](#a-fault-outranks-an-unsettled-declaration)
- [Goals are reported, never settled](#goals-are-reported-never-settled)
- [The exercised table is read from the report](#the-exercised-table-is-read-from-the-report)
- [Optional tracing](#optional-tracing)
- [License](#license)

<!-- tocstop -->

## Synopsis

**What.** `dispatch` maps an `Invocation` to an `Outcome`. A bare invocation routes to `Outcome::Status`, whose `StatusReport` states that toolchain management is not implemented. `Invocation::Check` and `Invocation::Test` route to `Outcome::Run`: a `Walk` over the paths given, the `Verb` it runs under and the `Width` it is visited at. Advancing the walk with `Walk::step` reads one source at a time and carries it through `compose`, which parses it, lowers it once, adapts the lowered declarations to the checker's input with `adapt`, judges them, has the kernel re-derive every acceptance, builds the `Program` that runs any accepted declaration, and settles each declaration against what it states. `Walk::visit` hands every step to a visitor in the same order; above `Width::SERIAL` it parses and lowers the sources on a pool of threads first, largest first, and judges each in walk order. Each step is counted into a `RunReport`, whose `verdict` is the gate the driver's exit code reports. `Invocation::Run` routes to `Outcome::Script`: a `Script` of one path, which composes its source as `check` would and runs the last name it declares, its `RunStatus` the exit code `gandr run` reports.

**Why.** The driver owns the argument surface and the process boundary; what an understood invocation does belongs to a library, so routing, composition and the gate can be enumerated without a process. The composition sits here, above the corpus library and the checker, because the settle comparison and the root guard must fire on the same pass that gates.

**How.** `dispatch` is a total match over the closed `Invocation` enum. `compose` is `lower_source` then `judge_module`, two short functions; the only call into the lowering sits in a private module that counts it. The walk lists directories with an explicit stack and classifies each source by its canonical path; stepped, it keeps one source's text at a time, and visited wider, it forks parse and lower by source onto scoped threads that share one atomic cursor.

## Provided features

- `Invocation`, `Outcome`, `StatusReport` and `dispatch`: routing. Witnesses: `tests::status_routes_to_the_status_report`, `tests::check_routes_to_a_walk_under_the_check_verb`, `tests::the_test_verb_routes_to_a_walk`.
- `Width` and `Threads`: how many threads a walk lowers its sources on, the host's physical performance cores by default. Witnesses: `width::tests::an_explicit_width_is_exact`, `width::tests::the_host_width_fits_the_process`, `width::tests::second_hardware_threads_share_a_core`, `width::tests::a_hybrid_processor_counts_its_performance_cores`, `width::tests::a_malformed_tree_reports_nothing`.
- `compose`, `Composed`, `ComposeFault` and `LoweringCount`: the composition. Witnesses: `compose::tests::a_module_settles_every_declaration_once`, `compose::tests::a_root_that_is_no_list_of_declarations_is_refused_whole`, `compose::tests::each_composition_lowers_once`, `compose::tests::the_root_decides_what_an_expectation_means`, `compose::tests::a_refusal_at_a_declaration_form_is_unstatable`, `compose::tests::a_kernel_disagreement_is_an_engine_fault`, `compose::tests::the_kernel_artifact_holds_what_crossed_under_its_names`.
- `lower_source`, `Lowering`, `Lowered` and `judge_module`: the composition's two halves, for a caller that keeps the lowered module beside the verdicts. Witnesses: `compose::tests::a_lowering_carries_the_parse_obligations`, `compose::tests::a_module_settles_every_declaration_once`.
- `adapt`: the lowering's module as checker declaration input. Witness: `compose::tests::a_module_settles_every_declaration_once`.
- `SourceRoot` and `classify`: the root a source sits under, by its path. Witnesses: `root::tests::a_path_under_no_root_is_strict`, `root::tests::the_innermost_root_decides`, `root::tests::pending_counts_only_directly_inside_a_fixture_root`, `root::tests::the_file_name_never_classifies`, `root::tests::each_root_settles_under_its_corpus_root`.
- `Walk`, `Walk::visit`, `Step`, `Standing`, `Standing::of`, `SourceFault` and `walk_step::Absent`: the walk at any width, and the standing a step or a session submission carries. Witnesses: `walk::tests::a_tree_is_walked_in_order`, `walk::tests::every_path_answers_in_order`, `walk::tests::each_root_stands_its_sources`, `walk::tests::a_stopped_visit_hands_over_nothing_more`, `corpus::corpus::every_width_composes_the_corpus_alike`.
- `RunReport`, `RunVerdict`, `SourceCounts`, `SourceCount`, `Verb`, `Goals`, `Shown` and `shown`: the runner's report, the gate and what each verb prints. Witnesses: `report::tests::each_count_decides_its_verdict`, `report::tests::each_verb_shows_its_declarations`.
- `Exercised` and `Row`: the fragment's exercised table, counted. Witnesses: `exercised::tests::a_module_carries_exactly_its_rows`, `exercised::tests::an_unsettled_declaration_carries_no_row`, `exercised::tests::a_near_miss_carries_no_refusal_row`, `exercised::tests::absorbing_sums_every_row`.
- `Program`, `Evaluation`, `ValueSpelling`, `Unfinished`, `Unrunnable`, `RunStatus`, `run_target::Absent` and `declaration_name::Absent`: the run stage. Witnesses: `evaluate::tests::a_value_runs_to_its_spelling`, `evaluate::tests::a_run_reaching_a_goal_blames_it`, `evaluate::tests::a_reference_the_machine_cannot_carry_is_never_run`, `evaluate::tests::each_outcome_class_has_its_status`, `evaluate::tests::the_run_target_is_the_last_name_declared`.
- `Script`, `ScriptRun`, `Ran`, `execute` and `run_source`: the run verb. Witnesses: `tests::the_run_verb_routes_to_a_script`, `script::tests::each_kind_of_source_has_its_status`, `run::run::run_source_runs_source_text`, `run::run::run_source_file_runs_a_script_file`, `run::run::run_source_file_accepts_an_executable_shebang_line`, `run::run::run_source_file_reports_the_path_of_an_absent_file`, `run::run::run_source_file_surfaces_a_source_failure_unchanged`.
- The corpus's two roots, run through the walk: `corpus::corpus::the_strict_root_checks_owing_nothing`, `corpus::corpus::the_fixture_root_settles_every_fixture`, `corpus::corpus::the_two_roots_exercise_every_row`, `corpus::corpus::a_run_lowers_each_source_once`; every run outcome they state, and the focusing of every declaration they accept: `corpus::corpus::l_machine_matches_the_outcome_snapshots_on_the_model_corpus`, `corpus::corpus::l_machine_matches_the_outcome_snapshots_on_the_pathological_corpus`, `corpus::corpus::focusing_is_total_on_the_model_corpus`, `corpus::corpus::focusing_is_total_on_the_pathological_corpus`; and the registration witness ([one walk registers every source](../surface-corpus/README.md#one-walk-registers-every-source)): `corpus::corpus::every_corpus_source_is_registered`, `corpus::corpus::a_planted_orphan_is_not_registered`.

Each nontrivial operation states an executable contract or a local exemption, plus a bounded adequacy claim pointing to its witnesses. The boundary evidence includes:

| Surface | Observed boundary |
| ------- | ----------------- |
| [Reports](src/report.rs) and [exercised rows](src/exercised.rs) | Saturating counts preserve unrelated fields; repeated row assignments retain the last value. |
| [Filesystem walk](src/walk.rs) | Late filesystem changes retain pending sources; exhaustion is stable; explicit links retain their reported path and use their target for classification; a visit at three threads yields the serial walk's rows and report, and a stopped visit hands over nothing more. |
| [Host width](src/width.rs) | A second hardware thread shares its core; a hybrid processor counts its performance cores alone; a missing, malformed or backwards CPU list reports no count rather than a guess. |
| [Evaluation](src/evaluate.rs) | Construction accepts sparse admission indices; terminal classification preserves declaration identity; nested fields retain order and repeated references. |
| [Corpus registration](tests/corpus.rs) | A directory with a source extension is traversed rather than registered as a source. |

## Expected features

- **A renderer.** The caller renders each `Outcome` and each `Step`; `gandr-surface-diagnostics` renders a source step. A `Step::Source` carries the source's text, and `Composed::Settled` the module's origin table, so a renderer can quote the lines a refusal covers and locate a checker refusal at its node's origin without composing the source again. `StatusReport`'s `Display` writes one sentence and no line terminator; `RunReport`'s writes its counts one per line, without a trailing terminator.
- **A file system.** `Walk::step` and `Walk::visit` list directories and read sources; every failure to do so is a `Step::Fault`, never a panic.
- **Threads.** `Walk::visit` starts scoped threads from `std`; a thread the host refuses to start leaves its sources to the others. The default width reads the host's physical performance cores: `hw.perflevel0.physicalcpu` on macOS, the `cpu_core` CPU list and each CPU's core siblings under `/sys/devices` on Linux; a host that reports neither runs on the parallelism `std` reports.

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

## One composition serves both verbs

`check` and `test` run the same walk and the same `compose`; they differ only in what `shown` prints and in what `--goals` does to the gate. A source is lowered exactly once per run, under one strictness, and each declaration gets exactly one verdict: the checker's, settled against what it states. `RunReport::lowerings` counts every lowering the crate performs, and the corpus suite asserts it equals the number of sources read. `run` composes its one source through the same `compose`, under the root its path classifies as.

The alternative was a total session pass and a separate strict tier over the same sources, which lowers each source twice and gives each declaration two verdicts that can disagree. The choice reverses only if a verb needs a different lowering of the same source, which would arrive as a parameter of the one composition rather than a second one.

The session (`gandr-surface-session`) is the one other caller. It runs the same two halves `compose` runs — `lower_source`, then `judge_module` — and keeps the lowered module between them to hand the incremental checker, so a submission's verdicts are this composition's and the corpus agreement suite there compares them source by source. The halves are public rather than duplicated there because a second composition is exactly what this section rules out.

## The run stage follows the check

`judge_module` builds the `Program` once the kernel has readmitted every acceptance. Each declaration the checker accepted has its body focused into the command IL by `gandr-core-sequent` and is held as a transparent definition; a declaration owed its body is held opaque, and a refused one, and a code — a type, of which the machine carries no image — are held as the reason they do not run. `Program::evaluate` mints `return c` for the declaration at `c`, runs it on a fresh L machine under a budget of 2²⁴ steps, forces the terminal when it is a thunk, so a suspended computation runs and a function answers `<fun>`, and reads the terminal back into the core. Nothing runs that no caller asked for: the settle comparison runs the declarations that state a `runs` outcome, the session runs what the user entered, and `gandr run` runs one declaration. The alternative was a run pipeline of its own that composed the source again, which lowers twice and could judge differently from the `check` it follows; the choice reverses if building the program shows on the check path's measurements, when it would move behind a request.

| What the run came to | `RunStatus` | `gandr run` exits |
| -------------------- | ----------- | ----------------- |
| `Evaluation::Value`: a value, spelled | `Value` | `0` |
| `Evaluation::Blamed`: the run reached a declaration owed its body — returned it outside any suspension, forced, applied or matched it | `Failed` | `1` |
| `Evaluation::Stuck`, `Evaluation::Unfinished`: any other stop short of a value; the budget spent, the store refusing, a terminal with no reading | `Failed` | `1` |
| `Evaluation::Unrunnable`: the declaration, or one it refers to, was refused or is a code | `Unreached` | `2` |
| `Ran::Refused`, `Ran::NoProgram`: a declaration of the source was refused, or it declares no name | `Unreached` | `2` |

The three statuses are the prior implementation's script contract: `0` for a value, `1` for blame or a stuck configuration, `2` for a source that never reached the machine. A source holding any refusal — the lowering's, the checker's or its root's — does not run even when the target never refers to the refused declaration, as the prior implementation refused a script with an outcome-only refusal; a goal is no refusal, and a run that reaches one is blamed on it. Unrunnable references are found by walking the program's references before any command runs, so a run never starts that would meet a declaration the machine cannot carry.

**The run target is the last name declared.** The prior implementation ran a source's final unnamed expression and called a source without one a source with no program. The fragment has no top-level expression, so the target is the declaration at the highest admission position, and a source declaring no name is `Ran::NoProgram`. The alternative, a distinguished name such as `main`, is a convention the language does not state. The choice reverses when the modules linker lowers a final unnamed expression: that expression becomes the target.

## Native universe-path boundaries

Programmatic native `Path_U` declarations use ordinary checker export and kernel readmission; their portable evidence remains part of the artifact. The command IL does not execute native paths or transport: focusing reports `UniverseTransport` rather than treating a certificate as a runtime closure. The value renderer names a native path `<path>` and leaves unreduced transport under `<computation>`, without executing evidence while printing it. Dependency discovery traverses native classifiers, maps and product components.

**Choice.** Keep admission, evaluation and presentation as separate observations. A path accepted by the kernel is not thereby executable in every downstream machine. **Reversal.** The run stage can acquire a native path image only with corresponding focusing, evaluation and readback rules; no parser syntax or coercion from `Flow_U` is implied here.

## The kernel re-derives every acceptance

After the checker judges a module, every declaration it accepted is offered to the kernel through the checker's bridge. A declaration the kernel rejects, or one the bridge refuses for any reason but a reference to a declaration that did not cross, is `ComposeFault::Readmission`: a disagreement between the two checkers is an engine fault, exit `2`, never a verdict about the author's source. A refused declaration crosses as its mark and a reference to it is withheld, and neither is a disagreement.

This goes beyond the slice's plan, which settles the checker's verdicts alone. The kernel is the oracle the checker answers to, and the readmission costs one erasure per accepted declaration; running it on the pass that gates means no acceptance a run reports is the untrusted checker's word alone. The choice reverses if readmission's cost dominates a run, at which point it moves behind a flag that the gate still sets.

What crossed is exported once on the same pass: `Composed::Settled` carries `kernel`, the canonical artifact of every declaration that crossed, in kernel admission order and under the module's structured names, so a caller that persists the kernel environment — the session's kernel checkpoint — never readmits the module itself. The export is one encoding of an environment the readmission already built. The alternative was carrying the readmission and leaving the export to a caller, which would make every caller own the name table and the encoding call. The choice reverses if the export's cost shows in a run that never reads it.

## Routing performs no I/O; the walk is the verb's

`dispatch` reads no file and writes nothing: it builds the grammar the walk parses with, which is computation, and returns. The walk's I/O — listing a directory, reading a source — happens as the driver calls `Walk::step` or `Walk::visit`. Stepped, the walk reads one source at a time, and the step borrows the source's text, so a run over a large tree holds one source in memory. Directories are walked depth-first in byte order of their entries' names. Discovered symbolic links are skipped; other non-directory `.gandr` entries are selected without a regular-file check. A path given explicitly is read as a source whatever its name, following symbolic links.

The alternative was collecting every source before composing any, which holds the tree in memory and delays the first line of output to the last read. The stepped walk keeps that choice; a wider visit departs from it, below, because it must know every source's size before it can schedule the largest first. The choice reverses if a verb needs the whole set before judging any member, such as a cross-source import, which would collect the paths first and still read one source at a time.

## Sources fork; judgement keeps walk order

`Walk::visit` at a width above one reaches every path first, then forks by source: one job per source, its byte length the estimate, the jobs sorted largest first behind one atomic cursor that each thread — the calling thread among them — advances to take the next. A job classifies, reads, parses and lowers its source into an arena of its own, so no source's state is shared; the grammar is the one value every thread reads. The calling thread judges, readmits, settles and counts each source in walk order as its lowering arrives over a channel, holds a lowering that arrives early until its turn, and takes a job itself whenever the next source in walk order has not arrived. A visitor that stops the visit stops the cursor, so no thread starts another source. Every count, verdict and printed byte is the serial walk's: the walk tests compare rows and reports at widths one and three, the corpus suite compares every composition at two, seven and the host's width with the stepped walk's, and the driver's suite compares both streams and the exit at several widths, set by flag and by environment. `Width::SERIAL` is that stepped walk, and the reference every wider visit is tested against.

**Largest first.** A source is the unit because its parse is one fold over its tokens, and the largest source bounds the tail: started first, it ends while the small ones fill the other threads, so the last thread to finish ends on a small source. The alternatives were the walk's own order, which can leave the largest source for last, and recursive halving of the source list, which balances counts rather than bytes. The estimate reverses to a measured cost per source if byte length stops predicting it.

**Judgement stays in walk order.** The checker, the kernel's readmission and the settle comparison run on the calling thread, one source after another, while the pool lowers the sources after it. Each source is judged alone today, so judging on the pool would give the same verdicts, but a checker that consults what earlier sources admitted needs that order, and judgement is under a twentieth of a corpus walk. The choice reverses if judgement grows into the tail of a wide visit, when the sources whose judgement depends on no other move onto the pool.

**The width is the host's physical performance cores.** A source's parse gains little past one thread per performance core: on an Apple M3 Max, sixteen threads, four of them on efficiency cores, walk the corpus 4 % faster than twelve, and on an AMD Ryzen 9 9950X3D thirty-two threads, sixteen of them second hardware threads, walk it 7 % slower than sixteen. So the default is the performance cores, never more than `std` says the process may use, and the host is asked only when a walk has two sources or more. A visit of one source runs on the calling thread alone. The driver's `--jobs` and `GANDR_JOBS` override it. On macOS the count is `hw.perflevel0.physicalcpu`, read through the [`sysctl`](https://crates.io/crates/sysctl) crate, since `std` reports logical CPUs only; the alternatives were `sysctlbyname` through `libc` and `unsafe`, `num_cpus`, which counts efficiency cores, and spawning the `sysctl` command, which costs milliseconds a run. On Linux it is read from sysfs with `std` alone. The default reverses to count efficiency cores or second hardware threads where a wider default measures faster on the process wall, not only on the walk.

**Scoped threads, not `rayon`.** The pool is `std::thread::scope` and the cursor. `rayon` was the recorded choice; on the corpus at twelve threads, with the same cursor and the same in-order consumer, it measured the same — on an Apple M3 Max 7.30 ms with a pool built per visit and 6.93 ms with one built before, against 7.01 ms for scoped threads; on an AMD Ryzen 9 9950X3D 5.49, 5.43 and 5.53 ms — since there is nothing for work stealing to steal from one shared cursor, and it would bring `rayon-core` and the `crossbeam` deque into the driver's build for no measured gain. The choice reverses when the dispatcher forks below the source, by form or declaration, where nested work wants a stealing pool, or when a long-lived process — the session, the language server — keeps a pool warm across runs.

**Held until the visit ends.** A wider visit lists every directory before it reads a source, holds every source's text until the visit ends and each lowering until its source is handed over, where the stepped walk holds one source; the first line of output waits for the first source in walk order. The choice reverses for a tree whose text does not fit in memory, when the cursor gains a bound on how far it may run ahead of the visitor.

## Membership is location

`classify` decides a source's root from the directories containing it, never from its own name or text: the innermost directory named `strict` or `fixture` decides, a directory named `pending` directly inside a `fixture` directory marks the pending set, and a path under none of them is strict. The walk classifies each source by its canonical path, so a relative path and a symbolic link to the same directory classify alike. The strict root settles under `CorpusRoot::Strict`, where `owes` and `refuses` are themselves refusals; the fixture root and the pending set settle under `CorpusRoot::Fixture`.

The alternative was a root named on the command line, which lets one invocation run a fixture source as strict. The choice reverses if a project's layout cannot use the directory names, at which point a configured mapping from directories to roots replaces the names, still by location.

## The pending set

A source under `fixture/pending/` carries a refusal no expectation can state: the lowering refused it as a whole, or refused one of its declarations at the declaration's own form, which files no half an attribute could be read off. `Composed::Settled` carries such refusals as `unstatable`. A pending source carrying either is `Standing::Pending`: counted, its declarations not settled, and printed by `test`. A pending source carrying neither is `Standing::Lowered` and unsettles the run, because every expectation it needs can now be written and it belongs under the fixture root. The [corpus](../surface-corpus/README.md#the-pending-set) describes the set it holds.

The alternative was a `pending` attribute, which the lowering could not read for either kind of refusal. The choice reverses when every refusal can carry an expectation; the pending set then empties.

## A fault outranks an unsettled declaration

`RunReport::verdict` answers `Faulted` when any path faulted — unreadable, naming no `.gandr` source, a grammar that did not build, a tree the parser could not commit, a whole-module refusal of the engine-fault class, a settle comparison handed foreign verdicts, a kernel disagreement — or when any declaration produced an engine-fault refusal, whatever it states. Otherwise it answers `Unsettled` when a strict or fixture source was refused as a whole, a pending source is `Lowered`, or a declaration is unsettled; otherwise `Settled`. The walk continues past a fault, so one run reports every path that faults.

A path that names no source faults rather than settling: a gate over an empty directory would pass vacuously. The alternative was stopping at the first fault, which hides every later one behind it. The choice reverses for a caller that wants fail-fast, which would stop advancing the walk rather than change it.

## Goals are reported, never settled

Under `check --goals` (`Goals::Reported`), a declaration unsettled by its obligations alone — it states and produces _checks_, owing different counts — is printed as a goal and does not fail the run; every other unsettled declaration still does. `shown` and `RunReport::verdict` read the same distinction; the settle comparison and the counts are unchanged, so the run's own settlement still reports the declaration unsettled.

The alternative was settling an owed declaration under `--goals`, which would change what settled means per invocation. The choice reverses if goals need their own exit code, which would be a fourth `RunVerdict` rather than a change to settled.

## The exercised table is read from the report

`Exercised` counts, per row of the fragment's exercised table, the settled declarations carrying it: the four formers' directions read off the formers in each accepted body (the judgement fixes each former's mode, so a lambda or a return in an accepted body was checked, a force or an application synthesised), the subsumption bridge read off the evidence's conversion count, and each refusal row read off the produced refusal — the lowering's unresolved name, unresolved type head and declined reserved form; the checker's shape refusal of a return, its refusal of a lambda where a type is synthesised, and of a thunk that is an unsigned definition's whole body — and the obligation row off an owed verdict. A declaration counts once per row however often the former stands in it, and an unsettled one counts in no row.

The corpus suite asserts every row is carried by the two roots, and that the strict root holds declarations; nothing pins how many. The alternative was a pinned count of fixtures per row, which turns adding a fixture into a failing test. The choice reverses if a row needs a minimum population above one, which would be stated as a bound, not a pin.

## Optional tracing

Enable `tracing` for an INFO span around `dispatch`. It records no argument or outcome payload and installs no subscriber. The [driver](../surface-driver/README.md#optional-tracing) owns output; the [evaluator](../core-nbe/README.md#optional-tracing) uses the same diagnostics interface independently. The dependency is optional and off by default, so ordinary routing has no instrumentation.

The choice is caller-owned structured diagnostics. Printing from this library would seize an output destination; installing a global subscriber would seize process policy. Revisit only when a library-owned diagnostic destination becomes an explicit API requirement, rather than an incidental side effect of dispatch.

## License

Apache-2.0 WITH LLVM-exception. The licence text is at the repository root.
