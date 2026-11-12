# gandr-surface-ledger

The ledgers of gandr's own surface: the syntax ledger read off the grammar, the exemplars that show its rows, the recovery sweep over those exemplars, and the features ledger. The crate stands above `gandr-surface-dispatcher`, so an edit of a ledger rebuilds this crate and the driver, and never the dispatcher.

<!-- toc -->
- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Where the detail lives](#where-the-detail-lives)
- [References](#references)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** `LedgerTask::run` builds and writes the syntax ledger, verifies its exemplars, sweeps them for recovery, or reads the features ledger. The driver runs one task for each `gandr ledger` verb, and the Model Context Protocol server reads the features ledger for `ledger_list` and `ledger_show`.

**Why.** A ledger consumes the dispatcher's verdicts, and no part of the dispatcher reads a ledger. One home per fact puts a consumer above its producer. So the ledger leaves the dispatcher's front end, which is on the chain of every build of the driver.

**How.** Each module states its mechanism and its decisions in its rustdoc. The witnesses of an item are the unit tests of its module. The driver's `tests::cli` cases run each verb end to end.

## Provided features

- `LedgerTask`, `LedgerRun` and `LedgerFault`: a `gandr ledger` verb, what it did and why it failed ([`ledger`](src/ledger.rs)).
- `SyntaxLedger`: every rule of the built-in grammar and every attribute of the lowering's registry, under the grammar's fingerprint ([`ledger`](src/ledger.rs)).
- `ExemplarReport`, `ExemplarFinding` and `ExemplarFault`: the verification of the exemplar directory ([`ledger::exemplars`](src/ledger/exemplars.rs)).
- `RecoveryReport`, `RecoveryFinding` and `RecoveryTally`: the sweep of each literal tile's near miss and deletion ([`ledger::recovery`](src/ledger/recovery.rs)).
- `FeatureLedger`, `Feature`, `FeatureId`, `Area`, `Status`, `ShownFeature` and `Malformed`: the features ledger, read as the guide an author writes from ([`ledger::features`](src/ledger/features.rs)).

## Expected features

- **The tree.** The syntax ledger reads its exemplars under `corpus/ledger`, and the features ledger reads `ledger/features.sql` under a root. The binary holds the copy of the features ledger it was built with.
- **The dispatcher.** The recovery sweep composes each mutant through `gandr-surface-dispatcher` on its pool, and reads its first error through the dispatcher's entries.

## Where the detail lives

| Topic | Module |
| ----- | ------ |
| The syntax ledger, its notation and its internal rules | [`ledger`](src/ledger.rs), [`ledger::standing`](src/ledger/standing.rs), [`ledger::decisions`](src/ledger/decisions.rs) |
| The exemplars of the rules, the attributes and the diagnostics | [`ledger::exemplars`](src/ledger/exemplars.rs), [`ledger::exemplars::diagnostics`](src/ledger/exemplars/diagnostics.rs) |
| The recovery sweep | [`ledger::recovery`](src/ledger/recovery.rs) |
| The features ledger | [`ledger::features`](src/ledger/features.rs) |

## References

- `vault:01a178aa-5497-7042-b9f4-56ce571601b1` — anchor: the build-out map, its seam test. A crate boundary encloses a strongly connected component of the module graph, and the ledger is outside the dispatcher's component.

## License

Apache-2.0 WITH LLVM-exception. The licence text is at the repository root.
