# gandr-workflow-artifacts

Holds the tree to the list of the files that a program writes: no tracked output, and a clean checkout after the gates.

- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [License](#license)

## Synopsis

**What.** `gandr-workflow-artifacts` installs the `artifacts` binary. The list `.config/replay/artifacts.json` gives each file that a program writes with its kind. `artifacts tracked` refuses a tracked file of an output or of a ratchet. `artifacts clean` refuses a checkout that a run of the gates changed.

**Why.** A file of the tree that a program writes conflicts in each pair of changes that move it. The store of the outputs holds such a value outside the tree. The gate keeps each later file of this kind out of the tree, and it shows a writer that the list does not know.

**How.** `tracked` reads `git ls-files` one time and finds the files of each path of the list by a binary search. A row with `pending` names the unit that takes its files out. It stays until that unit lands, and then the gate refuses it. `clean` reads `git status` one time and names the row of the list that holds each changed file. `--cost` prints each part of the run with its count and its time.

## Provided features

- `artifacts tracked [--root <dir>]` and `artifacts clean [--root <dir>]` print each finding on standard error and exit `1` when there is one. With no finding, each prints its `OK` line and exits `0`. A fault prints `artifacts: <fault>` and exits `2`.
- `read` reads the rows of the list. `tracked`, `entries` and `unclean` judge a tree.

## Expected features

`git` on the path. The lint `disallowed_macros` of `clippy.toml` refuses `expect_file!`, the third refusal of the gate: a test that compares with a file of the tree.

## Examples

```sh
cargo run --locked -p gandr-workflow-artifacts -- tracked
cargo run --locked -p gandr-workflow-artifacts -- clean
cargo nextest run -p gandr-workflow-artifacts
```

## License

Apache-2.0 WITH LLVM-exception. See [Apache-2.0](../../LICENSE.Apache-2.0.txt) and the [LLVM exception](../../LICENSE.LLVM-exception.txt) at the repository root.
