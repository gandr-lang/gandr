# gandr-surface-lsp-core

The core of the families of gandr's language server: the reading of a held text and the hover's table of a judged copy, with the requests that read them directly. The navigation and the diagnostics compile over this crate, beside each other, and `gandr-surface-lsp` compiles over the three.

<!-- toc -->
- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Where the detail lives](#where-the-detail-lives)
- [References](#references)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** The one reading of a held text, and what a judged copy keeps for its hovers. Hover, completion, definitions, signature help and the context stack, the semantic tokens of a judged copy, the formatting edits and the workspace's symbols. The path table of the workspace's sources, the sweep that judges the sources no editor holds, the store that a hub reads for its renderers and the identity of the running build. The report that the render bus carries for a document, and the sink that each job of a recheck runs at.

**Why.** A cold build compiles the server after the dispatcher and the session. The families of the server read both, but no family reads the server's state. So the families compile in crates of their own, below the server. This crate holds the families that the other two read.

**How.** Each module states its mechanism and its decisions in its rustdoc. The witnesses of an item are tests of this crate, or tests of a crate above it that read the item, spelled with that package's name. The `fixture` feature gives the tests of the crates above the helpers that they read.

## Provided features

- `Reading`, `Declaration`, `Tile` and `ImportAt`: the one parse of a held text that every structural request answers from ([`reading`](src/reading.rs)).
- `Hovering`, `hover`, `hovering` and `hovering_laid`: what a judged copy keeps for its requests, and what a hover shows ([`hover`](src/hover.rs)).
- `completions`, `resolved` and `Names`: the names and keywords that the word at a cursor completes to ([`complete`](src/complete.rs)).
- `targets`, `Locator` and `Placed`: where a written name is declared ([`goto`](src/goto.rs)).
- `help`, `stack`, `card` and `Signatures`: signature help and the context stack ([`signature`](src/signature.rs)).
- `classified`: the semantic tokens of a judged copy ([`tokens`](src/tokens.rs)).
- `edits` and `Scope`: the formatting of a document or of its forms ([`format`](src/format.rs)).
- `Found`, `Query` and `declared`: the workspace's symbols ([`search`](src/search.rs)).
- `Files`: the path table of the workspace's sources ([`files`](src/files.rs)); `Moves` and `added`: the paths that a rename of files moves and the imports that they need ([`relocate`](src/relocate.rs)).
- `Sweep`: the workspace's diagnostics for the sources that no editor holds ([`sweep`](src/sweep.rs)).
- `Stored`: the store that a hub reads for its renderers, on Unix ([`stored`](src/stored.rs)); `Build` and `running`: the identity of the running build ([`build`](src/build.rs)).
- `report`: the render bus's report of a document ([`view`](src/view.rs)); `Job` and `Subscription`: the sink of each job of a recheck ([`instrument`](src/instrument.rs)).

## Expected features

- **The dispatcher and the session.** A hover table, a completion and a definition read the type table that the dispatcher judges and the session holds.
- **The base of the server.** The protocol, the positions and the markup come from `gandr-surface-lsp-base`.

## Where the detail lives

| Topic | Module |
| ----- | ------ |
| The reading of a held text | [`reading`](src/reading.rs) |
| Hover and the hover table | [`hover`](src/hover.rs) |
| Completion | [`complete`](src/complete.rs) |
| Definitions | [`goto`](src/goto.rs) |
| Signature help | [`signature`](src/signature.rs) |
| Semantic tokens | [`tokens`](src/tokens.rs) |
| Formatting | [`format`](src/format.rs) |
| The workspace's symbols and files | [`search`](src/search.rs), [`files`](src/files.rs), [`relocate`](src/relocate.rs) |
| The workspace's diagnostics | [`sweep`](src/sweep.rs) |
| The store and the build | [`stored`](src/stored.rs), [`build`](src/build.rs) |
| The render bus's report | [`view`](src/view.rs) |
| The hub's fold of the activity ring | [`activity`](src/activity.rs) |

## References

- `vault:01a178aa-9a6d-7c20-a9c5-131d35beda06` — background: an item slot offers `flow`.
- `vault:01a178ab-289d-7702-b010-1c47ae9fd427` — background: `flow` supplies an import's translation.
- `vault:01a17f02-42f0-7920-bede-5615d3bade8c` — background: a renaming in a `flow` body is free.
- `vault:01a1c68b-1e9e-7942-aa36-b8d9096dec0e` — anchor: the activity fold, the derivation pane and the store pane.

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
