# gandr-surface-lsp-diagnostics

The diagnostics of gandr's language server: the recheck of a document, the kernel tiers, the repairs and fills of a hole, a model's proposals and the checkpoints that a save keeps. Each family reads the core of the families, `gandr-surface-lsp-core`. This crate compiles beside `gandr-surface-lsp-navigation`, and `gandr-surface-lsp` compiles over both.

<!-- toc -->
- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Where the detail lives](#where-the-detail-lives)
- [References](#references)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** The recheck of a document in its session, its kernel admission and the settle of that admission. The kernel tier of each declaration. The quick fixes that repair a malformed form or fill a hole, the trial of a model's fill, and the checkpoints that a save keeps and an open restores.

**Why.** No family of this crate reads the navigation. So this crate compiles beside the navigation, and an edit of a diagnostics family recompiles neither the navigation nor the core.

**How.** Each module states its mechanism and its decisions in its rustdoc. The witnesses of an item are tests of this crate, or tests of `gandr-surface-lsp` that read the item through the server, spelled with that package's name. The tests of this crate also hold the tests of the core that run a recheck.

## Provided features

- `open`, `lay`, `judge_laid`, `admission`, `settle` and `trial`: the recheck of a document, its admission and the trial of its candidates ([`recheck`](src/recheck.rs)).
- `Tiers`, `Tier` and `Tiered`: the kernel tier of each declaration of an open document ([`tier`](src/tier.rs)).
- `repairs`, `holes`, `fills` and `checked`: the quick fixes of a malformed form and of a hole ([`fix`](src/fix.rs)).
- `check`: the trial of a model's fill against the published diagnostics ([`proposal`](src/proposal.rs)).
- `Saved`: the checkpoints that a save keeps and an open restores ([`saved`](src/saved.rs)).

## Expected features

- **The core of the families.** The recheck reads the reading and the hover's table that `gandr-surface-lsp-core` holds.
- **The `hotpath` feature.** With it, a recheck is timed and its allocations are counted for the benchmark report.

## Where the detail lives

| Topic | Module |
| ----- | ------ |
| The recheck and the admission | [`recheck`](src/recheck.rs) |
| Kernel tiers | [`tier`](src/tier.rs) |
| Quick fixes | [`fix`](src/fix.rs) |
| A model's proposals | [`proposal`](src/proposal.rs) |
| Saves | [`saved`](src/saved.rs) |

## References

- `vault:01a1c68b-1e9e-7942-aa36-b8d9096dec0e` — anchor: the warrants that `tier` draws.
- `vault:01a178aa-6917-7983-b5cd-86e2af86b3ec` — anchor: § kernel-reassessment-design item 9.

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
