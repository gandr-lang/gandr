# gandr-surface-lsp-navigation

The navigation of gandr's language server: references, highlights, rename, the call hierarchy, inlay hints, copied sources, shadowing and the documentation site. Each family reads the hover's table of a judged copy, which `gandr-surface-lsp-core` holds. This crate compiles beside `gandr-surface-lsp-diagnostics`, and `gandr-surface-lsp` compiles over both.

<!-- toc -->
- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Where the detail lives](#where-the-detail-lives)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** Where the documents of a workspace use a name, the highlights and the linked edits of a name, and the rename of a name. The call hierarchy of a declared value, the inlay hints of a binder, and the sources that a copied range names. The lens and the diagnostic over a shadowing binder. A package's documentation, as Markdown pages and as a static HTML site.

**Why.** No family of this crate reads the diagnostics. So this crate compiles beside the diagnostics, and an edit of a navigation family recompiles neither the diagnostics nor the core.

**How.** Each module states its mechanism and its decisions in its rustdoc. The witnesses of an item are tests of this crate, or tests of `gandr-surface-lsp` that read the item through the server, spelled with that package's name.

## Provided features

- `placed`, `located`, `highlights`, `mirrored` and `declared`: where a name is written, used, highlighted and edited together ([`uses`](src/uses.rs)).
- `prepared`, `sites`, `text_edits` and `NewName`: the rename of a name in every document of a workspace ([`rename`](src/rename.rs)).
- `items`, `callers` and `callees`: the call hierarchy of a declared value ([`calls`](src/calls.rs)).
- `hints` and `hint_at`: the inlay hints of a binder that writes no type ([`inlay`](src/inlay.rs)).
- `copied`: the sources that a copied range of a document names ([`paste`](src/paste.rs)).
- `lenses`, `resolved` and `diagnostics`: the views of a shadowing binder ([`shadowed`](src/shadowed.rs)).
- `page`, `index`, `Page` and `Entry`: a package's documentation as Markdown ([`doc`](src/doc.rs)); `site` and `sourced`: the documentation as an HTML site ([`site`](src/site.rs)).

## Expected features

- **The core of the families.** Each family reads the hover's table, the reading and the definitions that `gandr-surface-lsp-core` holds.

## Where the detail lives

| Topic | Module |
| ----- | ------ |
| References, highlights and linked edits | [`uses`](src/uses.rs) |
| Rename | [`rename`](src/rename.rs) |
| The call hierarchy | [`calls`](src/calls.rs) |
| Inlay hints | [`inlay`](src/inlay.rs) |
| Paste with imports | [`paste`](src/paste.rs) |
| Shadowing binders | [`shadowed`](src/shadowed.rs) |
| The documentation | [`doc`](src/doc.rs), [`site`](src/site.rs) |

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
