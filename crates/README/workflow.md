# The `workflow` crates

The member rows of the `workflow` category of [`crates/README.md`](../README.md#members): one row for each directory, the directory and what it is.

```text
# Rows sort lexicographically by directory; the dependency order is § Layering.
crates/
├── workflow-build-state/          the `build-state` binary: build state kept to one build's units
├── workflow-coverage-guard/       the `coverage-guard` binary: main's coverage upload against the one before it, filed on one issue when it drops
├── workflow-debt-ledger/          the comment and prose gates' debt ledger
├── workflow-github/               the workflow binaries' one `gh` runner
├── workflow-host-tools/           the `host-tools` binary: the tools with no binary for a host's target, built once and copied to its hosts
├── workflow-hotpath-guard/        the `hotpath-guard` binary: a commit's hotpath checks, filed on one issue per regressed function
├── workflow-lane-budget/          the `lane-budget` binary: each CI lane's median job time against its budget
├── workflow-ledger-tasks/         the `ledger` binary: the syntax ledger written, its exemplars verified and swept, the features ledger read
├── workflow-prose/                the `prose` binary: the parsed sentence rules against the prose ledger
├── workflow-spec-cost/            the `spec-cost` and `spec-cost-ratio` binaries: what specifications cost the tests
├── workflow-sweep/                the corpus sources a sweep test visits: a stated sample per pull request, all of it nightly
└── workflow-test-timing/          the `test-timing` binary: nextest priorities from merge-queue timings
```
