# gandr-workflow-parser-report

The parser's report reads today's grammar on each axis that a syntax candidate takes as a measure. It prints one Markdown table row for each measure.

- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Dependencies](#dependencies)
- [License](#license)

## Synopsis

**What.** `gandr-workflow-parser-report` installs the `parser-report` binary. It reads the parser on six axes: latency, throughput, recovery, ambiguity, incremental work and parallel work. It prints one Markdown table, and the binary's documentation states each axis and the source of each measure.

**Why.** A comparison sets each syntax candidate against today's grammar on these axes. The report gives the numbers of today's grammar, so that a candidate has a stated base.

**How.** The binary molds the corpus that `gandr-workflow-sweep` lists, and it counts the decisions of the molder. It types sample sources into a language-server session through the client of the driver's benchmark report. It reads the recovery sweep of `gandr-workflow-ledger-tasks`.

## Provided features

- `census` builds the binary. The parser's molder then keeps its census of decisions. Without the feature, the package builds nothing.

## Expected features

The binary runs from the repository root, which holds the corpus and the syntax exemplars.

## Examples

```sh
mise run parser:report                 # the release build, the table written to target/parser-report.md
mise run parser:report target/a.md     # the table written to another file
```

## Dependencies

Each dependency is a crate of this workspace or is already in the build graph. Each is optional, and the `census` feature turns all of them on with the binary. Cargo then counts each dependency as used only when the binary uses it.

## License

Apache-2.0 WITH LLVM-exception. See [Apache-2.0](../../LICENSE.Apache-2.0.txt) and the [LLVM exception](../../LICENSE.LLVM-exception.txt) at the repository root.
