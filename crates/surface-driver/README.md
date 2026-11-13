# gandr-lang

The `gandr` binary is the entry point of the gandr language toolchain. `gandr check` and `gandr test` judge gandr sources. The verdict of the run is the exit code. `gandr run` runs a source as a program. `gandr host` serves the worlds of a source to the run of another process. `gandr stage` judges the programs of a stage on every core. `gandr fmt` formats sources at a page width. `gandr cells` prints the rewriting cells of each source with the count of each hole. `gandr doc` writes the documentation pages of a package. `gandr lsp` serves the language server. `gandr mcp` serves the server of the Model Context Protocol. `gandr view` shows the side view beside an editor. `gandr serve` runs the engine hub that their clients share. `gandr repl` runs the read-evaluate loop. `gandr tui` runs the same loop full-screen.

<!-- toc -->
- [Synopsis](#synopsis)
- [Examples](#examples)
- [Where the detail lives](#where-the-detail-lives)
- [References](#references)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** The package `gandr-lang` builds the `gandr` binary. `gandr check <paths>` settles every declaration of every source under the paths given and prints each unsettled one; `gandr test <paths>` runs the same pass and also prints every fixture and every pending source. `gandr check --lint explicit-exits` also reports, as a warning with the edit that settles it, every exit a source leaves to be inferred, which a module otherwise asks for through its `explicit_exits` attribute; `--lint explicit-runs` does the same for every run the checker infers where a computation stands in a position that reads a value, and `--lint explicit-runs=effects` for the runs that perform an effect, which the `explicit_runs` attribute asks for. `gandr check --grant read,write` bounds every capability a declaration holds by the host operations named, refusing one that claims another. `gandr run <file> [arguments…]` checks one source as `check` does and runs it on the L machine: a source declaring `def main() -> -F Integer`, or `def main(args : List(String)) -> -F Integer` to read the arguments, is a program and exits with the integer `main` returns or passes to `Proc.exit`; a source declaring no `main` runs nothing and exits `2`, naming `def main` and pointing at `gandr check` and `gandr test`. A run that reaches a hole stops there, names the hole at its line and column and exits `1`. `gandr run --world seat=<key>@<ip:port>` ships each migration to `seat` to the process holding that key, and `gandr host --world seat=<key>@<ip:port> --migrations <n>`, given the same source and that key, runs `n` of them and prints a line for each; a run that may migrate to a world no `--world` binds never starts. `gandr run --manifold <file>` and `gandr host --site <file> [--manifold <file>]` read those bindings from a deployment's files, models of `std.manifold`, the site's secret read from `--secrets` or `GANDR_SECRET_<NAME>`, and `gandr host` prints its peer spelling on standard error once bound; `gandr check` of a manifold judges each world's `requires` against its site, and admits an offer read through a flow or a renaming only as the manifold's `translation` states. `gandr stage <programs>` builds each staged program its spelling names, checks it end to end and prints what the kernel readmitted and how its families were admitted. `gandr fmt <paths>` lays each source out through `gandr-surface-format`, writes back each one whose layout changes and prints its path; `gandr fmt --check` writes nothing. `gandr cells <paths>` prints each rewriting cell of each source at its rule, with its provenance, its growth and each hole's count, its Lipschitz constant under the step; nothing is checked. `gandr doc <path> --out <directory>` writes an HTML site, each public item as a hover shows it, or Markdown pages under `--markdown`. The syntax ledger and the features ledger are written and read by the `ledger` binary ([`gandr-workflow-ledger-tasks`](../workflow-ledger-tasks/README.md)). `gandr lsp` serves `gandr-surface-lsp`'s language server on standard input and output until the client sends `exit`: on Unix through the engine hub of the current directory's workspace, which `gandr serve` runs and `gandr lsp` starts when none answers, and in its own process under `--standalone`; `gandr lsp --capabilities` prints what the server advertises. `gandr mcp`, on Unix, serves `gandr-surface-mcp`'s Model Context Protocol server on standard input and output through the same hub, its tools and resources reading the documents the workspace's editors hold open. `gandr view`, on Unix, attaches to the same hub's render bus and follows the document it checked last: full-screen through `gandr-surface-tui`'s side view on a terminal, its reports as plain rows on a pipe. `gandr repl` runs `gandr-surface-repl`'s read-evaluate loop on standard input and output: the line editor on a terminal, a plain transcript when standard input is piped or under `--batch`. `gandr tui` runs the same loop through `gandr-surface-tui`'s terminal face, full-screen, and `gandr tui --smoke` runs that face once off-screen. A bare `gandr` prints the driver version and states that toolchain management is not implemented. Every verb writes a construct with a glyph (`≃`, `≅`, `⇝`, `∷`) in the spelling `--spelling unicode|ascii` or the user's [configuration](src/config.rs) names, Unicode by default; there `kernel.policy` says whose kernel verdicts `check` recalls, `--recheck` checking every declaration.

**Why.** The driver owns the argument surface and the process boundary, and routes everything after that through `gandr-surface-dispatcher`, which composes the pipeline and decides the gate without a process. The registry name `gandr` belongs to an unrelated crate, so the package is `gandr-lang` and the binary is `gandr`.

**How.** `clap` parses the arguments before anything is written. The driver visits the walk that the dispatcher returns, prints each diagnostic as `gandr-surface-render-terminal` lays it out, then the report and its verdict, and returns the verdict as its exit code. `gandr run` runs the dispatcher's `Script` with the operands after the path and the world bindings of its `--world` flags, and `gandr host` hands the same `Script` the migrations to host instead. `gandr stage` runs the dispatcher's `Staging` at the width the invocation asked for, `gandr fmt` steps its `Formatting`, `gandr cells` its `Census`, and `gandr doc` its `Traversal` into `gandr-surface-lsp`'s `site` or `page`; what each prints and why each fails is [`main`](src/main.rs)'s verb table. `gandr lsp` reaches the hub, starting one when none answers, and hands the standard streams and the connection to `gandr-surface-lsp`'s `relay`, or under `--standalone` the streams to `serve`. `gandr mcp`, `gandr view` and `gandr serve` reach or run the hub as their functions in [`main`](src/main.rs) state. `gandr repl` hands the standard streams to `gandr-surface-repl`'s `run_batch` or `run_interactive` and returns how the loop ended; `gandr tui` checks that standard input and output are a terminal, then hands the terminal to `gandr-surface-tui`'s `run`, or standard output to its `run_smoke` under `--smoke`, and returns how the face ended. Each verb's function in [`main`](src/main.rs) names its witnesses, each spawning the binary.

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
- `vault:01a178aa-655f-72f2-97ee-298c0647e1e5` — background: the sharing ratio of iterated composites.
- `vault:01a1c68b-1e9e-7942-aa36-b8d9096dec0e` — anchor: § engine-surface-activity.
- `Ahrens-2025-weighted_rewriting_semiring_semantics_abstract_reduction_systems` — newest: Ahrens, Kassing, Giesl and Katoen, 2025, `arXiv:2505.08496` — the bound `gandr cells` prints.

## License

Apache-2.0 WITH LLVM-exception. The licence text is at the repository root.
