# gandr-workflow-hotpath-guard

A commit's failed hotpath checks, filed on one issue per pull request.

- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Dependencies](#dependencies)
- [License](#license)

## Synopsis

**What.** `gandr-workflow-hotpath-guard` installs the `hotpath-guard` binary. It reads a commit's `hotpath / <benchmark>` checks and the pull request the commit heads, and prints a Markdown report of every failed check: its run, its wall-time line, and each site over its policy's threshold with the before/after numbers. When a check failed, it opens or updates the pull request's one issue, titled `perf: #<n> regresses <sites>` and labelled `kind:performance` with the areas. The issue ends with a `## Lint` heading, where the fix states whether a quenchant dylint could have refused the pattern that regressed.

**Why.** The hotpath check is not required: hotpath Cloud posts it after the benchmark upload, which can arrive after the rest of the pipeline, and no pull request waits for it. A red check nobody reads lands with the pull request. The guard turns each failure into an issue the triage lane routes to the authoring lane, while the pull request is still open or after it merged.

**How.** The hotpath guard workflow runs on every completed check run and acts on a failed `hotpath /` one. `gh api` lists the commit's check runs and the pull requests GitHub associates with it; the guard names the one whose head is the commit. It reads every hotpath check of the commit at once, so each failed benchmark's event writes the same issue. The issue is found again by the opening `perf: #<n> regresses `; a commit no pull request carries is keyed by its short form. The labels join the pull request's `area:` labels with the tiers of the crates the sites live in. The [crate docs](src/lib.rs) record the decisions, the alternatives and the reversal.

## Provided features

- `hotpath-guard --sha SHA` prints the report; `--repository OWNER/NAME` defaults to `GITHUB_REPOSITORY`.
- `--file-issue` opens or updates the pull request's one issue when a check failed; a commit with no failed check touches no issue.
- `GuardError` names the argument or the `gh` invocation behind every refusal; a refusal exits 2.

## Expected features

`gh` on the path, authenticated for the repository with permission to read checks and pull requests and, with `--file-issue`, to write issues, and `GH_REPO` or the checkout naming the repository.

## Examples

```sh
mise run ci:hotpath-guard --repository gandr-lang/gandr --sha 914a768fb32501be92e5cb4d28ce6613dfa01022
cargo nextest run -p gandr-workflow-hotpath-guard
```

## Dependencies

`serde` and `serde_json` read `gh`'s answers, with the features the root `Cargo.toml` records.

## License

Apache-2.0 WITH LLVM-exception. See [Apache-2.0](../../LICENSE.Apache-2.0.txt) and the [LLVM exception](../../LICENSE.LLVM-exception.txt) at the repository root.
