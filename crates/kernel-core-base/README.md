# gandr-kernel-core-base

The record of the kernel. It keeps the admitted entries and the staged declarations, the content names, the support that a check reads, and the verdict keys and receipts. The crate also holds the term rewrites and the refusals of the kernel. The judgement in `gandr-kernel-core` admits each declaration into this record. An edit of the judgement rebuilds neither this crate nor a crate that reads only this crate.

<!-- toc -->
- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Where the detail lives](#where-the-detail-lives)
- [References](#references)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** The data of the kernel. `Entries` holds each admitted declaration with its block, its unit and its key, and `Staging` builds the content of the next one. `ContentTable` names each record by its content, and `SupportContext` holds the binders and the entries that a check reads. `KernelError` and its modules name each refusal. `VerdictKey` and the receipts recall a verdict that a believed signer attests.

**Why.** The record, its rewriting and its refusals name no module of the judgement, and the judgement names each of them. So the record compiles first, and an edit of the judgement does not rebuild it.

**How.** `gandr-kernel-core` imports each module of this crate under its old name and re-exports each path that a consumer names today; [`src/lib.rs`](src/lib.rs) lists the modules. The judgement's build script writes the build identity, and the judgement passes it as a `BuildIdentity` to each derivation of a key, so a key binds the files of both crates. The tests that admit through `Environment` are tests of `gandr-kernel-core`.

## Provided features

- **The record.** `Entries`, `AdmittedDeclaration`, `Staging`, `StagedDeclaration` and the counts of outstanding content.
- **Recorded verdicts.** `Environment::recalling` admits a declaration whose entry key a trusted signer's verified `Receipt` attests, without the check; `Environment::receipt` signs only what this kernel checked itself ([`verdict`](src/verdict.rs)).
- **Admitted results.** `Environment::admitting` states an `AdmissionPolicy`; `Environment::admitted` counts what it took ([`admitted`](src/admitted.rs)).
- **The forked drain.** `Environment::forking`: a check's long last drain runs apart through a `SharedFork` ([`fork`](src/fork.rs)).
- **Sealing.** An abstract type carries its representation and the extent of its minting admission; [`seal`](src/seal.rs) states what reads the atom as its representation.
- **The content key.** `ContentTable`, `MintNames`, `support_key`, `content_digest`, `NodeSupport` and `SupportContext`: content ids, mint names, memo keys and content digests ([`encoding`](src/encoding.rs)).
- **The rewrites.** `shift_value_type` and `substitute_comp_type`, de Bruijn shifting and substitution as memoized machines.
- **Accounting.** `ExpansionCensus`: each goal expanded, recalled or answered by a kept outcome, per plane, kept on its entry ([`census`](src/census.rs)).
- **Errors.** `KernelError`, whose payloads are content; [`error`](src/error.rs) states why.
- **Levels and presented spaces.** `LevelContext` and `Presentations`.
- **Fixtures.** With the `fixture` feature, the readings and the generators that the tests of this crate and of the judgement build on.

## Expected features

- **The judgement passes the build identity.** No derivation of a key reads a file; the caller gives the identity, as [`verdict`](src/verdict.rs) states.
- **The arena outlives the record that names it.** An entry names nodes of the term arena that it does not own, as [`env`](src/env.rs) states.
- **The specification facade's `cfg`.** `#[spec(...)]` clauses are checked at runtime only when the whole build graph is compiled with `--cfg anodized_panic`.
- **`alloc`.** The crate is `no_std` with `alloc`.

## Where the detail lives

Mechanism, rules, decisions with their alternatives and reversals, and witnesses live in the rustdoc beside the code:

| Topic | Module |
| ----- | ------ |
| The admitted record and its staging | [`env`](src/env.rs), [`admitted`](src/admitted.rs), [`weakening`](src/weakening.rs) |
| Content names and keys | [`encoding`](src/encoding.rs), [`hashed`](src/hashed.rs) |
| What a check reads and owes | [`support`](src/support.rs), [`census`](src/census.rs), [`fork`](src/fork.rs) |
| Rewriting | [`rewrite`](src/rewrite.rs) |
| Refusals and their witnesses | [`error`](src/error.rs), [`witness`](src/witness.rs), [`occurrence`](src/occurrence.rs) |
| Verdict keys and receipts | [`verdict`](src/verdict.rs) |
| Levels, presented spaces, seals and theory rules | [`levels`](src/levels.rs), [`presented`](src/presented.rs), [`seal`](src/seal.rs), [`theory_rules`](src/theory_rules.rs) |
| Fixtures | [`fixture`](src/fixture.rs), [`generated`](src/generated.rs) |

## References

- `Grodin-2026-potential_functions_types` — background: Grodin and coauthors, 2026 — amortised cost.
- `vault:01a05203-4468-7931-8246-761a8f853a27` — lineage: the incremental memoization results (§ successor-synthesized-context) — the memo records an entry by the context its judgement synthesized.
- `vault:01a12317-453f-7980-9c86-68f75917f3a6` — lineage: the bicontextual core (§ bicontextual-judgement, § codebruijn-carrier, § footprint-from-support) — the judgement returns the binders it read as its output.
- `vault:01a178aa-655f-72f2-97ee-298c0647e1e5` — anchor: content addressing as strictified descent (§ storage-conjecture-chunk-descent) — a record's name is its key up to an identification, with the identification as a parameter; `RecordName` takes `Exact`, the identity on content.
- `vault:01a178aa-6917-7983-b5cd-86e2af86b3ec` — lineage: the kernel re-assessment's design (§ kernel-reassessment-design); the `# References` of `encoding` and `support` name the items each takes.
- `vault:01a178aa-ce14-7610-bcad-5aab5f9c0b0f` — lineage: § kernel-verdict-reuse — keys, receipts and the re-check.
- `vault:01a178ab-081c-74a0-bd58-f8db4f9573c8` — lineage: the incremental programme's kernel support reuse — a declaration checks under the entries its content reaches, and the kernel refuses a read outside them rather than trust the support.
- `vault:01a1897b-d199-7d10-a325-587b76db2508` — lineage: § The design — a stratum receipt.

## License

Apache-2.0 WITH LLVM-exception. The licence text is at the repository root.
