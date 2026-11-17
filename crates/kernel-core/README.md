# gandr-kernel-core

The certified kernel's judgements: the defunctionalized checking machine, type formation, conversion, the admission choke point, the check memo wired as the default path on both machines, and the sequential replay of an untrusted engine's conversion trace.

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

**What.** `Environment` admits declarations through one checked choke point, `add_decl`, and one warned bypass, `add_decl_unchecked`; `audit` reports what an admitted declaration transitively rests on. Beneath the choke point sit a bidirectional checking machine, a type-formation walk that computes a type's universe level, and structural conversion. Beside it sits the replay of an untrusted engine's conversion trace. [`src/lib.rs`](src/lib.rs) names what the crates beside it own; this crate re-derives each obligation.

**Why.** The kernel grants a producer no credence: every declaration is re-checked before admission, including one a decoder built from untrusted bytes. Such a term can be arbitrarily deep and heavily shared, so the checker must be total on adversarial depth and must not pay for a shared subterm once per occurrence.

**How.** The checker is a defunctionalized machine over explicit stacks. It is total on depth. Conversion is structural comparison with a positive-only id-equality fast path. Both machines consult a content-keyed check memo per call, then the environment's kept outcomes. [`src/lib.rs`](src/lib.rs) states how admission truncates the arena, and why the four are decided together.

## Provided features

- **Admission.** `Environment` with `stage`, `add_decl`, `add_decl_unchecked`, `abandon`, `seal`, `replay` and `audit`; `StagedDeclaration`, `CheckedId`, `AdmittedDeclaration`, `ArtifactRefusal` and `AxiomReport`.
- **The record.** `Environment` reads and writes the record of [`gandr-kernel-core-base`](../kernel-core-base/README.md): its verdicts, admitted results, forked drain, seals, content key, rewrites, census and errors.
- **The checking machine.** `check_declaration_with_memo`, the opt-in entry that returns a verdict and never a `CheckedId`; only `Environment` admits.
- **Type formation.** An iterative walk computing a type's universe level; [`check`](src/check.rs) tables its gates.
- **Conversion.** `convert_value_type`, `convert_comp_type` and their `convertible_*` forms over `Convertibility`; [`conv`](src/conv.rs) states the comparison.
- **Conversion replay.** `replay`: a conversion trace replayed against an engine's `EngineClaim` for two `ReplaySides`, answering a `KernelVerdict` (the classes are in [`replay`](src/replay.rs)); `read_step`: an open returned code's step re-derived by the kernel's own reading, with no trace.
- **The descent skeleton.** `Descent` and `descent::replay`: one replay for a conversion trace and a guarded family with its rows.
- **Native formers.** Nominal data and structural records, recursive data with the structural fixpoint, the native List former, universe paths, session codes, element and function identity and the bridge (`element_identity`), and the directed family (`flow_universe`), whose certificates replay on readmission, all through ordinary admission.
- **Rule languages beside admission.** Identity and bridge recursion (`identity_recursion`), guarded higher fields (`higher_field`), the experimental stage universe (`stage`) and guarded admission of staging-equation families (`admission`); none of them admits a declaration on its own authority.

## Expected features

- **Staging discipline.** A producer resolves every staged declaration by admitting, bypassing or abandoning it. A staged declaration left unresolved keeps its content in the arena and blocks the admission of every declaration staged before it.
- **Receipt scope.** A `CheckedId` names a position, not an environment identity. Use it only with the corresponding admission history.
- **A vouched bypass.** `add_decl_unchecked` performs no checking: the caller vouches for the declaration, and `audit` reports every declaration that rests on it.
- **Reduced codes.** Conversion fires no reduction, so two codes convert only when they are structurally equal. A producer hands the kernel reduced codes to avoid a refusal. [`replay`](src/replay.rs) states the one exception.

## Examples

The rustdoc of [`Environment`](src/environment.rs) holds the admission example. The example stages a declaration, admits it, refuses a second one and audits the environment.

[`src/lib.rs`](src/lib.rs) names what each integration test holds. Run them with the unit tests, then the enforcing twin:

```sh
cargo nextest run -p gandr-kernel-core
RUSTFLAGS="--cfg anodized_panic" cargo nextest run -p gandr-kernel-core
```

## Where the detail lives

Mechanism, rule tables, decisions and specification detail live in the rustdoc beside the code:

| Topic | Module |
| ----- | ------ |
| The four decisions, the memo's binding conditions and collapse law, arithmetic and absence, specification boundaries | [`src/lib.rs`](src/lib.rs) |
| The checking machine, its correspondence table, universes and the lift, static operators, the native List | [`src/check.rs`](src/check.rs) |
| Nominal data and records; accessibility under the stage order; the structural fixpoint typed by stages | [`src/check/former.rs`](src/check/former.rs), [`src/check/occurrence.rs`](src/check/occurrence.rs), [`src/check/recursion.rs`](src/check/recursion.rs), [`src/stage_order.rs`](src/stage_order.rs) |
| Admission, the audit, replay; each role's holder | [`src/environment.rs`](src/environment.rs), [`src/builtin.rs`](src/builtin.rs) |
| Conversion and its discharged set | [`src/conv.rs`](src/conv.rs) |
| Conversion replay, its decisions and laws | [`src/replay.rs`](src/replay.rs) |
| The descent skeleton and its two instances | [`src/descent.rs`](src/descent.rs) |
| Universe paths | [`src/path_universe.rs`](src/path_universe.rs) |
| The directed family: formation, `stay`, `then`, `ride` and its telescope form, the covariance gate, certificate admission and the permanent refusals | [`src/flow_universe.rs`](src/flow_universe.rs) |
| Element and function identity: formation, `here`, transport and its telescope over a dependent motive, higher fields, higher and quantified evaluation; the bridge's formation and fibre, and its refusal at a sealed atom | [`src/element_identity.rs`](src/element_identity.rs) |
| Identity and bridge recursion, function identity, the bridge clauses and their decision | [`src/identity_recursion.rs`](src/identity_recursion.rs), [`src/identity_recursion/recursive.rs`](src/identity_recursion/recursive.rs) |
| Guarded higher fields | [`src/higher_field.rs`](src/higher_field.rs) |
| Session codes and certificates | [`src/session.rs`](src/session.rs) |
| The stage universe and residual readmission | [`src/stage.rs`](src/stage.rs) |
| Guarded admission of equation families | [`src/admission.rs`](src/admission.rs) |
| The replay of a match's cover derivation against its tree | [`src/check/cover.rs`](src/check/cover.rs) |

## References

- `vault:01a178aa-6917-7983-b5cd-86e2af86b3ec` — lineage: the kernel re-assessment's design (§ kernel-reassessment-design); the `# References` of `replay` and `descent` name the items each takes.
- `vault:01a178ab-081c-74a0-bd58-f8db4f9573c8` — lineage: the incremental programme's kernel support reuse — a declaration checks under the entries its content reaches, and the kernel refuses a read outside them rather than trust the support.
- `vault:01a16be2-3ad1-73e2-9e54-d28a053edcaa` — exemplar: sharing as descent (§ sharing-rule-descent, § sharing-rule-probe) — a cover glued once and replayed.
- `vault:01a1897b-d199-7d10-a325-587b76db2508` — lineage: § The design — a stratum receipt.
- `Courant-2026-lazy_concurrent_convertibility_checker` — lineage: § 4.2's weak-head machine with environments, which the replay runs.
- `vault:01a183de-4ab1-7660-a88a-04b9e8d318e3` — exemplar: the source page of Beniamino Accattoli. "Back to the Future of Lambda: Refreshing the Lambda-Calculus for the 21st Century." Habilitation, Institut Polytechnique de Paris, 2025. `hal:tel-05454767` — § 3.9's practical values, which the replay's alias keeps.
- `vault:01a1567c-2c32-7ed3-a102-45e54f702b4f` — anchor: Eremondi and Kammar, "Coverage Semantics for Dependent Pattern Matching", ESOP 2025, `doi:10.1007/978-3-031-91118-7_11` — § 5's `var`, `split` and `compose`, which the replay walks.
- `vault:01a1567c-2c32-7ed3-a102-45dc5330206a` — anchor: the coverage design (§ coverage-evidence-form) — the derivation that the kernel replays step by step.
- `vault:01a1aa2d-a69c-7030-91e0-337d68d88151` — anchor: the presented-spaces plan (§ presented-spaces-crates) — the field label on each refusal of a patched type's replayed formation.
- `vault:01a183fc-63df-77a0-9df0-1c3f0b02ddf6` — anchor: Kovács, _POPL_, 2026, `doi:10.1145/3776685` — the signatures, `E` and `F` of § 2.2, whose holders the kernel validates.
- `vault:01a178aa-fe00-7121-9fe8-2df35cbb1aeb` — anchor: the trace-certificate design — the replay runs a held operand's steps, which the trace does not record.
- `vault:01a1b48c-2d17-7fc1-80ce-cb35e5cffd0e` — background: Ljungström and Mörtberg, LICS 2023, `arXiv:2302.00151` — § 2.2's eliminator of the spheres, in `words`.
- `vault:01a178ab-289d-7702-b010-1c47ae9fd427` — anchor: the loop carried past two empty images of a cell, in `words`.
- `vault:01a156e3-93c7-7e62-9a50-b38b2da60284` — anchor: the loops design (§ loops-shapes) — productivity as a guard on observations, in `check::guard`.
- `vault:01a1d73a-dd43-75b3-87d1-dd3ce49eff5b` — anchor: the device profile — a device fails on the allocation and not on the average, so the `counts` feature counts each frame that the machines pop, in `check`.

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
