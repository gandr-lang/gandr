# gandr-workflow-tree-rules

Holds each tracked file of the tree to its rules: no merge residue, no path of a home directory, and Markdown only on the list of READMEs.

- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [License](#license)

## Synopsis

**What.** `gandr-workflow-tree-rules` installs the `tree-rules` binary. It judges the name of each tracked file and each line of each tracked file that is not binary.

| Rule | Refuses | Its patterns |
| ---- | ------- | ------------ |
| `residue` | a conflict marker or the residue of a merge tool in a line, and a file named as such residue | `.config/merge-residue/patterns` and `names` |
| `paths` | the path of a home directory in a line, unless a name of `placeholders` follows the home directory | `.config/local-paths/patterns` and `placeholders` |
| `markdown` | a tracked Markdown file that the list of READMEs does not hold | `.config/markdown/readmes` |

**Why.** A conflict marker that lands breaks a build or a reader. The path of a home directory names an account of a host, and the tree is public. A Markdown page outside the list of READMEs is prose that rustdoc does not check.

**How.** One run of `git ls-files` lists the tracked files. The binary judges each name, and reads each regular file one time for each rule of its lines. A file with a NUL in its first 8000 bytes is binary, as git reads it, and no rule reads its lines. The file `cases.json` beside the patterns of `residue` and of `paths` holds the cases of each rule. The tests of the crate read them, and the line scan skips the files that hold such lines by design. `--cost` prints the count of the files and the time of the run.

## Provided features

- `tree-rules [--root <dir>] [--rule <rule>]... [--cost]` prints each finding on standard error as `<path>:<line>: <rule>: <line>`, or `<path>: <rule>: <what>` for a name, and exits `1` when there is one. With no finding, it prints its `OK` line and exits `0`. A fault prints `tree-rules: <fault>` and exits `2`. With no `--rule`, it runs each rule.
- `Rules::read` reads the patterns of each rule. `judge_name` and `judge_text` judge one file.

## Expected features

`git` on the path.

## Examples

```sh
cargo run --locked -p gandr-workflow-tree-rules --bin tree-rules
cargo run --locked -p gandr-workflow-tree-rules --bin tree-rules -- --rule residue
cargo nextest run -p gandr-workflow-tree-rules
```

## License

Apache-2.0 WITH LLVM-exception. See [Apache-2.0](../../LICENSE.Apache-2.0.txt) and the [LLVM exception](../../LICENSE.LLVM-exception.txt) at the repository root.
