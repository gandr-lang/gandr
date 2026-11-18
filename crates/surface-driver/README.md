# gandr-lang

The `gandr` binary is the entry point of the gandr language toolchain. `gandr check` and `gandr test` judge gandr sources. The verdict of the run is the exit code. `gandr run` runs a source as a program. `gandr host` serves the worlds of a source to the run of another process. `gandr stage` judges the programs of a stage on every core. `gandr fmt` formats sources at a page width. `gandr cells` prints the rewriting cells of each source with the count of each hole. `gandr doc` writes the documentation pages of a package. `gandr lsp` serves the language server. `gandr mcp` serves the server of the Model Context Protocol. `gandr view` shows the side view beside an editor. `gandr serve` runs the engine hub that their clients share. `gandr repl` runs the read-evaluate loop. `gandr tui` runs the same loop full-screen.

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

**What.** The package `gandr-lang` builds the `gandr` binary, the entry point of the toolchain, with one verb for each face of gandr: `## Provided features` lists them. Each flag of each verb, what it prints and its exit code is a row of [`main`](src/main.rs)'s verb table, the one home of that detail. The user's [configuration](src/config.rs) names the spelling of each glyph (`≃`, `≅`, `⇝`, `∷`) and `kernel.policy`, whose kernel verdicts `check` recalls. The syntax ledger and the features ledger are written and read by the `ledger` binary ([`gandr-workflow-ledger-tasks`](../workflow-ledger-tasks/README.md)).

**Why.** The driver owns the argument surface and the process boundary, and routes everything after that through `gandr-surface-dispatcher`, which composes the pipeline and decides the gate without a process. The registry name `gandr` belongs to an unrelated crate, so the package is `gandr-lang` and the binary is `gandr`.

**How.** `clap` parses the arguments before anything is written. The driver visits the walk that the dispatcher returns, prints each diagnostic as `gandr-surface-render-terminal` lays it out, then the report and its verdict, and returns the verdict as its exit code. `gandr run` runs the dispatcher's `Script` with the operands after the path and the world bindings of its `--world` flags, and `gandr host` hands the same `Script` the migrations to host instead. `gandr stage` runs the dispatcher's `Staging` at the width the invocation asked for, `gandr fmt` steps its `Formatting`, `gandr cells` its `Census`, and `gandr doc` its `Traversal` into `gandr-surface-lsp`'s `site` or `page`; what each prints and why each fails is [`main`](src/main.rs)'s verb table. `gandr lsp` reaches the hub, starting one when none answers, and hands the standard streams and the connection to `gandr-surface-lsp`'s `relay`, or under `--standalone` the streams to `serve`. `gandr mcp`, `gandr view` and `gandr serve` reach or run the hub as their functions in [`main`](src/main.rs) state. `gandr repl` hands the standard streams to `gandr-surface-repl`'s `run_batch` or `run_interactive` and returns how the loop ended; `gandr tui` checks that standard input and output are a terminal, then hands the terminal to `gandr-surface-tui`'s `run`, or standard output to its `run_smoke` under `--smoke`, and returns how the face ended. Each verb's function in [`main`](src/main.rs) names its witnesses, each spawning the binary.

## Provided features

- The `gandr` binary. Its verbs, what each prints and each exit code are [`main`](src/main.rs)'s verb table:
  - `check` and `test`: the judgement of the sources under each path.
  - `lock`: the lock of each package, resolved again.
  - `lsp`, `mcp`, `view` and `serve`: the faces of an editor, a model and a side view, and the engine hub that they share.
  - `repl` and `tui`: the read-evaluate loop, line by line or full-screen.
  - `run` and `host`: a source run as a program, and the worlds that it migrates to.
  - `stage`, `fmt`, `doc` and `cells`: the staging check, the layout, the documentation and the rewriting cells of the sources.
  - `toolchain`: the installed toolchains, and the one that the driver runs ([`toolchain`](src/toolchain.rs)).
- The Cargo features, each off by default:
  - `counts`: `gandr check --counts` prints the allocations of the run over every thread.
  - `hotpath`: the `hotpath` and `conversion` benches.
  - `instrument`: the hub's build, with the instrument layers, the activity ring and the counting allocator.
  - `malloc-zone`: on macOS, one private malloc zone for every allocation ([`allocator`](src/allocator.rs)).
  - `tracing`: diagnostics on standard error.

## Expected features

- **A file system.** `check`, `test`, `fmt`, `doc` and `cells` read the sources under each path, and `fmt` and `doc` write their output.
- **A terminal.** `tui` needs one on standard input and output. `repl` and `view` edit and draw on one, and print plain rows when piped.
- **The user's directories.** The driver reads the user's configuration file ([`config`](src/config.rs)). The hub keeps each acknowledged call under the user's state directory.
- **A Unix socket.** `lsp`, `mcp` and `view` reach the engine hub of the workspace over one, and start the hub when none runs.
- **The installed toolchains.** The driver selects one by `GANDR_TOOLCHAIN`, then the nearest `gandr-toolchain` file, then the default, and runs its `gandr` ([`toolchain`](src/toolchain.rs)).
- **A network.** `run` binds the network of a program on its first `Net` operation, and `host` takes the migrations of another `gandr run`.

## Examples

```console
$ gandr check crates/surface-corpus/strict
sources: 2 read (2 strict, 0 fixture, 0 pending), 0 refused as a whole, 0 no longer pending, 0 faulted
lowerings: 2
goals: 0
exercised: a lambda checks 2; a return checks 3; …
ledger size: 0
declarations: 11 settled, 0 unsettled
fixtures: 0 settled, 0 unsettled
surviving obligations: 0 undeclared, 0 unproduced
refusals: 0 user absence, 0 unimplemented, 0 malformed source, 0 engine fault
run: settled
seal: sealed
verdict: settled
$ gandr check broken.gandr
error[UnresolvedName]: `missing` is not defined
  ╭▸ broken.gandr:1:14
  │
1 │ def broken = missing ;
  │              ━━━━━━━ not found in this scope
  │
  ╰ note: `broken` is expected to check, and this refusal leaves it unsettled

sources: 1 read (1 strict, 0 fixture, 0 pending), 0 refused as a whole, 0 no longer pending, 0 faulted
…
verdict: unsettled
$ echo $?
1
$ printf 'def answer = 42 ;\n:type answer\n' | gandr repl
▸ def answer = 42 ;
answer : Integer
= 42
▸ :type answer
: Integer
$ gandr tui --smoke
gandr tui: ready
$ gandr run answer.gandr
42
$ gandr run blame.gandr
goal: `later` states checks owing 0; produced checks owing 1
  ╭▸ blame.gandr:1:1
  │
1 │ def later : +U (-F Integer) ;
  ╰╴━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ surviving obligations: 1 undeclared, 0 unproduced

gandr: blame.gandr: `main` blame: `later` is owed its body
$ echo $?
1
$ gandr stage -j 4 pow:0..8 double:0..8
pow:0..8: 9 of 9 certificates readmitted; 15 families: 2 admitted, 0 partial, 13 plain, 0 refused, 0 over the work bound, 0 faulted
double:0..8: 18 of 18 certificates readmitted; 13 families: 4 admitted, 0 partial, 9 plain, 0 refused, 0 over the work bound, 0 faulted
digest: 64155da969400767
verdict: readmitted
$ printf 'def  answer =  42 ;\n' > answer.gandr
$ gandr fmt --check answer.gandr
answer.gandr
$ echo $?
1
$ gandr fmt answer.gandr
answer.gandr
$ cat answer.gandr
def answer = 42 ;
```

## Where the detail lives

Mechanism, decisions with their alternatives and reversals, and witnesses live in the rustdoc beside the code:

| Topic | Module |
| ----- | ------ |
| Verbs, exit codes, unwritable output, tests and their limits, optional tracing | [`main`](src/main.rs) |
| The user's configuration file | [`config`](src/config.rs) |
| The global allocator | [`allocator`](src/allocator.rs) |
| Installed toolchains, their selection and the exec proxy | [`toolchain`](src/toolchain.rs) |

## References

- `vault:01a178aa-6e2c-7720-a0bd-c5e1f9c4e08e` — background: the quantities design (§ quant-try-first) — `gandr cells` reports each cell's counts.
- `vault:01a178aa-ce14-7610-bcad-5aab5f9c0b0f` — lineage: § kernel-verdict-reuse — the installation's key signs; the policy is the user's.
- `vault:01a1897b-d199-7d10-a325-587b76db2508` — lineage: § The design — the stratum store a `check` installs.
- `vault:01a17cb3-d471-72b2-9bd2-70a46f74c3de` — lineage: § build-owner-store — the receipts and the strata a `check` keeps, each in the storage tier's store.
- `vault:01a178aa-d585-7822-9cf0-40459729a925` — background: the package design's typed hydration — a dependent reads each dependency's export by its address and re-admits it through the kernel.
- `vault:01a178ab-17e5-7352-bc0b-3caa7f1e476c` — background: the storage programme's worlds — `gandr host` is the process a migration runs at.
- `vault:01a17f02-42f0-7920-bede-5615d3bade8c` — background: the compilation ruling (§ compilation-recipe-vocabulary) — `gandr run` runs a local artifact, the endpoint of a one-role choreography.
- `vault:01a18572-6e13-7412-bc74-aa6a24d157c4` — background: Catt's artifact sizes, beside `check --measure`.
- `vault:01a051fd-25fd-7f24-a5d4-a72eca18a687` — lineage: the shared and unshared sizes of one table.
- `vault:01a1d2ce-8890-7cf2-a94b-b73109f5689a` — lineage: the shared pool's local hub — the sessions of a face readmit on the host's one pool, which `host_pool` installs.
- `vault:01a178aa-655f-72f2-97ee-298c0647e1e5` — background: the sharing ratio of iterated composites.
- `vault:01a1c68b-1e9e-7942-aa36-b8d9096dec0e` — anchor: § engine-surface-activity.
- `vault:01a1d73a-dd43-75b3-87d1-dd3ce49eff5b` — anchor: the device profile — a device fails on the allocation and not on the average, so the `counts` feature counts each allocation of the process, in `allocator`.
- `Ahrens-2025-weighted_rewriting_semiring_semantics_abstract_reduction_systems` — newest: Ahrens, Kassing, Giesl and Katoen, 2025, `arXiv:2505.08496` — the bound `gandr cells` prints.

## License

Apache-2.0 WITH LLVM-exception. The licence text is at the repository root.
