# gandr-surface-dispatcher

Routes an understood `gandr` driver invocation to the outcome the driver renders, and composes the surface pipeline the `check`, `test` and `run` verbs run: parse, lower, check, settle, over every source under the paths given, and for `run` the run stage after the check: focus, run on the L machine, read back.

<!-- toc -->

- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [One composition serves both verbs](#one-composition-serves-both-verbs)
- [The run stage follows the check](#the-run-stage-follows-the-check)
- [The kernel re-derives every acceptance](#the-kernel-re-derives-every-acceptance)
- [Routing performs no I/O; the walk is the verb's](#routing-performs-no-io-the-walk-is-the-verbs)
- [Membership is location](#membership-is-location)
- [The pending set](#the-pending-set)
- [A fault outranks an unsettled declaration](#a-fault-outranks-an-unsettled-declaration)
- [Goals are reported, never settled](#goals-are-reported-never-settled)
- [The exercised table is read from the report](#the-exercised-table-is-read-from-the-report)
- [Optional tracing](#optional-tracing)
- [License](#license)

<!-- tocstop -->

## Synopsis

**What.** `dispatch` maps an `Invocation` to an `Outcome`. A bare invocation routes to `Outcome::Status`, whose `StatusReport` states that toolchain management is not implemented. `Invocation::Check` and `Invocation::Test` route to `Outcome::Run`: a `Walk` over the paths given and the `Verb` it runs under. Advancing the walk with `Walk::step` reads one source at a time and carries it through `compose`, which parses it, lowers it once, adapts the lowered declarations to the checker's input with `adapt`, judges them, has the kernel re-derive every acceptance, builds the `Program` that runs any accepted declaration, and settles each declaration against what it states. Each step is counted into a `RunReport`, whose `verdict` is the gate the driver's exit code reports. `Invocation::Run` routes to `Outcome::Script`: a `Script` of one path, which composes its source as `check` would and runs the last name it declares, its `RunStatus` the exit code `gandr run` reports.

**Why.** The driver owns the argument surface and the process boundary; what an understood invocation does belongs to a library, so routing, composition and the gate can be enumerated without a process. The composition sits here, above the corpus library and the checker, because the settle comparison and the root guard must fire on the same pass that gates.

**How.** `dispatch` is a total match over the closed `Invocation` enum. `compose` is `lower_source` then `judge_module`, two short functions; the only call into the lowering sits in a private module that counts it. The walk lists directories with an explicit stack, classifies each source by its canonical path, and keeps one source's text at a time.

## Provided features

- `Invocation`, `Outcome`, `StatusReport` and `dispatch`: routing. Witnesses: `tests::status_routes_to_the_status_report`, `tests::check_routes_to_a_walk_under_the_check_verb`, `tests::the_test_verb_routes_to_a_walk`.
- `compose`, `Composed`, `ComposeFault` and `LoweringCount`: the composition. Witnesses: `compose::tests::a_module_settles_every_declaration_once`, `compose::tests::a_root_that_is_no_list_of_declarations_is_refused_whole`, `compose::tests::each_composition_lowers_once`, `compose::tests::the_root_decides_what_an_expectation_means`, `compose::tests::a_refusal_at_a_declaration_form_is_unstatable`, `compose::tests::a_kernel_disagreement_is_an_engine_fault`.
- `lower_source`, `Lowering`, `Lowered` and `judge_module`: the composition's two halves, for a caller that keeps the lowered module beside the verdicts. Witnesses: `compose::tests::a_lowering_carries_the_parse_obligations`, `compose::tests::a_module_settles_every_declaration_once`.
- `adapt`: the lowering's module as the checker's declaration input. Witness: `compose::tests::each_outcome_adapts_to_its_halves`.
- `SourceRoot` and `classify`: the root a source sits under, by its path. Witnesses: `root::tests::a_path_under_no_root_is_strict`, `root::tests::the_innermost_root_decides`, `root::tests::pending_counts_only_directly_inside_a_fixture_root`, `root::tests::the_file_name_never_classifies`, `root::tests::each_root_settles_under_its_corpus_root`.
- `Walk`, `Step`, `Standing`, `Standing::of`, `SourceFault` and `walk_step::Absent`: the walk, and the standing a step or a session submission carries. Witnesses: `walk::tests::a_tree_is_walked_in_order`, `walk::tests::every_path_answers_in_order`, `walk::tests::each_root_stands_its_sources`.
- `RunReport`, `RunVerdict`, `SourceCounts`, `SourceCount`, `Verb`, `Goals`, `Shown` and `shown`: the runner's report, the gate and what each verb prints. Witnesses: `report::tests::each_count_decides_its_verdict`, `report::tests::each_verb_shows_its_declarations`.
- `Exercised` and `Row`: the fragment's exercised table, counted. Witnesses: `exercised::tests::a_module_carries_exactly_its_rows`, `exercised::tests::an_unsettled_declaration_carries_no_row`, `exercised::tests::a_near_miss_carries_no_refusal_row`, `exercised::tests::absorbing_sums_every_row`.
- `Program`, `Evaluation`, `ValueSpelling`, `Unfinished`, `Unrunnable`, `RunStatus`, `run_target::Absent` and `declaration_name::Absent`: the run stage. Witnesses: `evaluate::tests::a_value_runs_to_its_spelling`, `evaluate::tests::a_run_reaching_a_goal_blames_it`, `evaluate::tests::a_reference_the_machine_cannot_carry_is_never_run`, `evaluate::tests::each_outcome_class_has_its_status`, `evaluate::tests::the_run_target_is_the_last_name_declared`.
- `Script`, `ScriptRun`, `Ran`, `execute` and `run_source`: the run verb. Witnesses: `tests::the_run_verb_routes_to_a_script`, `script::tests::each_kind_of_source_has_its_status`, `run::run::run_source_runs_source_text`, `run::run::run_source_file_runs_a_script_file`, `run::run::run_source_file_accepts_an_executable_shebang_line`, `run::run::run_source_file_reports_the_path_of_an_absent_file`, `run::run::run_source_file_surfaces_a_source_failure_unchanged`.
- The corpus's two roots, run through the walk: `corpus::corpus::the_strict_root_checks_owing_nothing`, `corpus::corpus::the_fixture_root_settles_every_fixture`, `corpus::corpus::the_two_roots_exercise_every_row`, `corpus::corpus::a_run_lowers_each_source_once`; every run outcome they state, and the focusing of every declaration they accept: `corpus::corpus::l_machine_matches_the_outcome_snapshots_on_the_model_corpus`, `corpus::corpus::l_machine_matches_the_outcome_snapshots_on_the_pathological_corpus`, `corpus::corpus::focusing_is_total_on_the_model_corpus`, `corpus::corpus::focusing_is_total_on_the_pathological_corpus`; and the registration witness ([one walk registers every source](../surface-corpus/README.md#one-walk-registers-every-source)): `corpus::corpus::every_corpus_source_is_registered`, `corpus::corpus::a_planted_orphan_is_not_registered`.

## Expected features

- **A renderer.** The caller renders each `Outcome` and each `Step`; `gandr-surface-diagnostics` renders a source step. A `Step::Source` carries the source's text, and `Composed::Settled` the module's origin table, so a renderer can quote the lines a refusal covers and locate a checker refusal at its node's origin without composing the source again. `StatusReport`'s `Display` writes one sentence and no line terminator; `RunReport`'s writes its counts one per line, without a trailing terminator.
- **A file system.** `Walk::step` lists directories and reads sources; every failure to do so is a `Step::Fault`, never a panic.

## Examples

```rust
use gandr_surface_dispatcher::Goals;
use gandr_surface_dispatcher::Invocation;
use gandr_surface_dispatcher::Outcome;
use gandr_surface_dispatcher::Step;
use gandr_surface_dispatcher::dispatch;
use quenchant_shape::shape::Maybe;

fn run(paths: Vec<std::path::PathBuf>) {
    let Outcome::Run { verb, mut walk } = dispatch(Invocation::Check { goals: Goals::Gated, paths })
    else {
        return;
    };
    while let Maybe::Present(step) = walk.step() {
        if let Step::Fault { path, fault } = step {
            eprintln!("{}: {fault}", path.display());
        }
    }
    let report = walk.report();
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

**One spelling.** `Evaluation`'s `Display` is the spelling `gandr run` prints, the session's value line shows and a `runs("…")` expectation states byte for byte: an integer or a numeric literal as written, text quoted with Rust's debug escapes, `()`, a pair `(a, b)`, an injection `inl(v)` or `inr(v)`, and `<thunk>`, `<fun>` and `<code>` for what has no first-order reading; a blamed run is `` blame: `x` is owed its body ``. The prior implementation's driver printed a value's debug image (`Int(42)`) while its loop printed `42`; one spelling replaces both. The choice reverses when a printer directed by the value's type lands, and the corpus's stated outcomes are restated in its spelling.

## The kernel re-derives every acceptance

After the checker judges a module, every declaration it accepted is offered to the kernel through the checker's bridge. A declaration the kernel rejects, or one the bridge refuses for any reason but a reference to a declaration that did not cross, is `ComposeFault::Readmission`: a disagreement between the two checkers is an engine fault, exit `2`, never a verdict about the author's source. A refused declaration crosses as its mark and a reference to it is withheld, and neither is a disagreement.

This goes beyond the slice's plan, which settles the checker's verdicts alone. The kernel is the oracle the checker answers to, and the readmission costs one erasure per accepted declaration; running it on the pass that gates means no acceptance a run reports is the untrusted checker's word alone. The choice reverses if readmission's cost dominates a run, at which point it moves behind a flag that the gate still sets.

## Routing performs no I/O; the walk is the verb's

`dispatch` reads no file and writes nothing: it builds the grammar the walk parses with, which is computation, and returns. The walk's I/O — listing a directory, reading a source — happens one source at a time as the driver calls `Walk::step`, and the step borrows the source's text, so a run over a large tree holds one source in memory. Directories are walked depth-first in byte order of their entries' names, reaching directories and regular `.gandr` files and following no symbolic link; a path given explicitly is read as a source whatever its name.

The alternative was collecting every source before composing any, which holds the tree in memory and delays the first line of output to the last read. The choice reverses if a verb needs the whole set before judging any member, such as a cross-source import, which would collect the paths first and still read one source at a time.

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
