# gandr-workflow-coverage-guard

Main's nightly coverage upload against the one before it, filed on one issue when it drops.

- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Dependencies](#dependencies)
- [License](#license)

## Synopsis

**What.** `gandr-workflow-coverage-guard` installs the `coverage-guard` binary. It waits for Codecov to process the upload of a commit of `main`, reads the processed upload of `main` before it, sums each crate's lines from both uploads' files, and prints a Markdown report: both coverages, the change against a threshold, both file counts, and a table of every crate whose coverage or missed lines moved, or that one upload lacks. When the coverage fell by more than the threshold or the upload covers fewer files, it opens or updates one issue titled `coverage: main dropped from X to Y (<sha>)`. An upload Codecov leaves unprocessed is named on the report and skipped, and the newest processed upload stands in its place. Two or more in a row open or update one issue titled `coverage: Codecov left N uploads of main unprocessed (<sha>)`.

**Why.** A coverage number nobody reads drifts unnoticed: a shard dropped from the measurement, a crate's tests skipped, or a measurement fault that counts lines twice all look like a lower percentage on a page someone has to open. The guard turns the nightly upload into an issue with the per-crate deltas that locate the cause, the morning after.

**How.** Codecov's public API answers the upload's totals, `main`'s upload listing and each upload's files; `curl` fetches them. A coverage is covered lines over measured lines in hundredths of a percent, rounded down as Codecov writes it, so the title quotes the numbers Codecov's page shows. `gh` finds the open issue whose title starts with `coverage: main dropped from `, and edits it or opens one labelled `kind:defect` and `area:ci`. Codecov can leave an upload in `error` for good, so the guard skips an unprocessed upload rather than refusing it, and the run stays green. Codecov's own badge reads its branch head and then shows `unknown`, so the guard writes the badge itself from the newest processed upload. The [crate docs](src/lib.rs) record the decisions, the alternatives and the reversal.

## Provided features

- `coverage-guard --repository OWNER/NAME --sha SHA --threshold POINTS` prints the report; `GITHUB_REPOSITORY` and `GITHUB_SHA` stand in for the first two.
- `--wait SECONDS` bounds the wait for Codecov's processing, fifteen minutes by default.
- `--file-issue` opens or updates the one drop issue when the upload dropped; a steady upload touches no issue. With it, two or more unprocessed uploads in a row open or update their one issue.
- `--badge FILE` writes the newest processed upload's coverage as shields.io endpoint JSON, which `mise run ci:coverage-badge FILE` publishes on the orphan `badges` branch the root README's badge reads.
- `GuardError` names the argument, the address, the commit or the `gh` invocation behind every refusal; a refusal exits 2. An unprocessed upload is no refusal; only no processed upload at all is.

## Expected features

`curl` on the path; with `--file-issue`, `gh` on the path, authenticated for the repository with permission to write issues, and `GH_REPO` or the checkout naming the repository.

## Examples

```sh
mise run ci:coverage-guard --repository gandr-lang/gandr --sha "$(git rev-parse origin/main)" --threshold 0.5
cargo nextest run -p gandr-workflow-coverage-guard
```

## Dependencies

`gandr-workflow-github` runs every `gh` invocation and names the one that failed. Its `read` runs the issue listing again past a transient server error; a write runs once. `serde` and `serde_json` read Codecov's answers and `gh`'s issue listing, with the features the root `Cargo.toml` records.

## License

Apache-2.0 WITH LLVM-exception. See [Apache-2.0](../../LICENSE.Apache-2.0.txt) and the [LLVM exception](../../LICENSE.LLVM-exception.txt) at the repository root.
