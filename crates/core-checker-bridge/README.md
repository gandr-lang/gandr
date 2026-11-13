# gandr-core-checker-bridge

The kernel bridge of the core checking judgement. The kernel re-derives each declaration that the judgement accepts, and the bridge exports it under the producer's names. The kernel replays one template for a whole family of staged equations. The bridge compiles over `gandr-core-checker-base`, so an edit of the bridge rebuilds neither the base nor a crate that reads only the base.

<!-- toc -->
- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Where the detail lives](#where-the-detail-lives)
- [References](#references)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** `bridge::readmit` erases each declaration of a judged `ModuleReport` and offers it to the kernel's one checked entry. `template` drafts a family of staging equations from its last template, prices it, and admits it through the kernel's guarded admission.

**Why.** The kernel is the authority on every acceptance. The judgement does not need the bridge, so the bridge is a crate over the base.

**How.** Each module states its mechanism and its decisions in its rustdoc. The witnesses of an item are tests of this crate, or tests of the base's integration target named with the base's package. The tests build on the base's `fixture` feature.

## Provided features

- `bridge`: readmission into a fresh kernel environment, whole or resumed from a record, with each origin's account and time; [`bridge`](src/bridge.rs) names its entry points.
- `bridge::readmit_retiring`: a readmission polled between its steps.
- `bridge::Refusal::Hole` and `bridge::Refusal::Unknown`: a hole or the unknown type where the kernel stands.
- `template`: guarded families of staging equations with ordinary replay as authority, the `template::Memo` that drafts a family from its key's last template, and the adapter into the kernel's guarded admission.

## Expected features

- **One arena per report.** `bridge::readmit` takes, mutably, the arena the report was judged over, and refuses an id that does not resolve there as a dangling node.
- **`alloc`.** The crate is `no_std` with `alloc`.

## Where the detail lives

| Topic | Module |
| ----- | ------ |
| Readmission, erasure, lifts and unfoldings, static operators, holes and marks, the audit, splits, deep handlers and export | [`bridge`](src/bridge.rs) |
| Guarded staging families, drafts and their controller | [`template`](src/template.rs), [`template::memo`](src/template/memo.rs), [`template::draft`](src/template/draft.rs) |

## References

- `vault:01a178aa-ce14-7610-bcad-5aab5f9c0b0f` — background: § kernel-verdict-reuse — a resumed readmission signs only its own checks.
- `vault:01a178aa-6917-7983-b5cd-86e2af86b3ec` — lineage: one skeleton replays every certificate.

## License

Apache-2.0 WITH LLVM-exception. The licence text is at the repository root.
