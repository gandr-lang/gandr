# gandr-core-checker

This crate gives the core judgement one name for its consumers. It re-exports the [base](../core-checker-base/README.md) and the [bridge](../core-checker-bridge/README.md) at each path that a consumer names. It also holds the staged programs and the elaboration session.

<!-- toc -->
- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Where the detail lives](#where-the-detail-lives)
- [References](#references)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** The judgement, the module run and the refusal vocabulary come from the base; readmission and the staging templates come from the bridge. The top adds `staging`, a staged program checked end to end, and `elaborating`, the session that fills a hole and resumes what waited.

**Why.** A consumer names one crate. A staged program reads the bridge's templates, and the session readmits what it resumes, so both stand over the two lower crates.

**How.** [`src/lib.rs`](src/lib.rs) states the judgement's shape and re-exports each path. Each module states its mechanism and its decisions in its rustdoc.

## Provided features

- Every public path of the base and the bridge, at the path it had when the three crates were one.
- `staging::check`, `staging::Program`, `staging::Allowance`, `staging::Checked`, `staging::Readmission`, `staging::Stages`, `staging::ProgramError` and `staging::SourceIndex`: a staged program checked end to end on the caller's fork.
- `elaborating::Session`: a hole filled, and each declaration that waited on it resumed and readmitted.

## Expected features

- **The lower crates' expectations.** Each expectation of the base and the bridge holds here.
- **`alloc`.** The crate is `no_std` with `alloc`.

## Examples

The crate rustdoc's example lives in [`src/lib.rs`](src/lib.rs).

## Where the detail lives

| Topic | Module |
| ----- | ------ |
| Staged programs and their forks | [`staging`](src/staging.rs) |
| The elaboration session | [`elaborating`](src/elaborating.rs) |
| Measurement dependencies and the admission observer | [`examples/staging_templates.rs`](examples/staging_templates.rs) |

## References

- `Wood-2024-framework_semiringannotated_type_systems` — dependency: the usage annotations of λR and their subusaging, which the access rules read, § 4.2

## License

Apache-2.0 WITH LLVM-exception. The licence text is at the repository root.
