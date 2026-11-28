# gandr-workflow-references

Reads the citations of the crates and the corpus, and refuses a work older than the citation window at a site that no entry keeps.

- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [License](#license)

## Synopsis

**What.** `gandr-workflow-references` installs the `references` binary. `references window` reads the citations of each source of the tree, the years of the works in `ledger/references.sql`, and the policy `.config/references/window.toml`. It prints each citation of a work older than the cutoff year at a site that no `[[site]]` entry keeps.

**Why.** A new citation of an older work states a construction that a newer work can state better. The window refuses it at its site, and the landing runs the window, so the refusal comes before the change lands.

**How.** One read of each source, and one pass over its lines. A key line of a References section and each DOI or arXiv locator of the documentation is a citation. The year of a work is its row's year, else the year its key or its arXiv identifier carries. An entry that covers a crate or a corpus subject whole is refused. `--cost` prints each part of the run with its count and its time.

## Provided features

- `references window [--root <dir>]` prints each finding on standard error and exits `1` when there is one. With no finding, it prints `references window OK: …` and exits `0`. A fault prints `references: <fault>` and exits `2`.
- `cites::citations` reads the citations of one source. `sources` lists the sources of a tree. `window::Policy`, `window::works` and `window::findings` judge them.

## Expected features

The mise task `check:references` holds the other parts of the citations: the lists of the READMEs, the rows of the ledger, the keys of the vault and the citation refresh.

## Examples

```sh
cargo run --locked -p gandr-workflow-references -- window
cargo nextest run -p gandr-workflow-references
```

## License

Apache-2.0 WITH LLVM-exception. See [Apache-2.0](../../LICENSE.Apache-2.0.txt) and the [LLVM exception](../../LICENSE.LLVM-exception.txt) at the repository root.
