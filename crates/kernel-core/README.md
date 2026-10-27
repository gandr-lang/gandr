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

**What.** `Environment` admits declarations through one checked choke point, `add_decl`, and one warned bypass, `add_decl_unchecked`; `audit` reports what an admitted declaration transitively rests on. Beneath the choke point sit a bidirectional checking machine, a type-formation walk that computes a type's universe level, and structural conversion. Beside it, `replay` rechecks a term-conversion verdict an untrusted engine reached, decision by decision, from the trace that engine recorded. Representation, the sharing format and the decode budgets belong to `gandr-kernel-term`, the universe algebra to `gandr-kernel-strata`, the memo's storage to `gandr-kernel-check-memo`, and the decision vocabulary to `gandr-kernel-conversion-trace`; this crate is what re-derives an obligation.

**Why.** The kernel grants a producer no credence: every declaration is re-checked before admission, including one a decoder built from untrusted bytes. Such a term can be arbitrarily deep and heavily shared, so the checker must be total on adversarial depth and must not pay for a shared subterm once per occurrence.

**How.** The checker is a defunctionalized machine over explicit stacks, so it is total on depth; conversion is structural comparison with a positive-only id-equality fast path; both machines consult a content-keyed check memo that lives for one check call; and admission truncates the arena on both verdicts, clamped at the admission floor. [`src/lib.rs`](src/lib.rs) states why the four are decided together.

## Provided features

- **Admission.** `Environment` with `stage`, `add_decl`, `add_decl_unchecked`, `abandon`, `seal`, `replay` and `audit`; `StagedDeclaration`, `CheckedId`, `AdmittedDeclaration`, `ArtifactRefusal` and `AxiomReport`.
- **Recorded verdicts.** `Environment::recalling` keys each lone checked admission by `VerdictKey`, a BLAKE3 chain over the kernel's build and every segment admitted before it, and admits a key a trusted signer's verified `Receipt` attests as `Admission::Recalled` without the check; `Environment::receipt` signs, with a `KernelSigner`, only what this kernel checked itself, and `handed_on` passes the chain to a resumed run without its records. `TrustPolicy`, `VerdictSource`, `StoredReceipt`, `VerdictRecord` and `KernelIdentity` in [`verdict`](src/verdict.rs). A rejection, a bypass, a mutual block or an open seal ends the chain; refusals are never recorded.
- **Sealing.** An abstract type carries its representation and the extent of its minting admission: the declarations inside it are checked with the atom read as its representation, every later one against the bare atom (`seal`), and a replayed artifact re-derives both from the recorded extent.
- **The checking machine.** `check_declaration`, the default path with a fresh memo, and `check_declaration_with_memo`, the opt-in entry that returns a verdict and never a `CheckedId`.
- **Type formation.** An iterative walk computing a type's universe level, gating lift strictness, level scope, a sealed atom's kind, and the code a decode of either family owes.
- **Conversion.** `convert_value_type`, `convert_comp_type` and their `convertible_*` forms: structural comparison of two types, descending into the terms they carry, over `Convertibility`.
- **Conversion replay.** `replay`: a conversion trace replayed against an engine's `EngineClaim` for two `ReplaySides`, answering a `KernelVerdict` — certified convertible, certified not convertible, or declined with a `ReplayDecline`, a refused trace's `ReplayRefusal` classed as an ill-formed query, a foreign answer or a path disagreement (`RefusalClass`); `read_step`: an open returned code's step re-derived by the kernel's own reading, with no trace.
- **Native formers.** Nominal data and structural records, recursive data with the structural fixpoint, the native List former, universe paths, session codes, element and function identity and the bridge (`element_identity`), and the directed family (`flow_universe`: `Flow`, `stay`, `then`, `ride` and its telescope form, with forward, function and session certificates replayed on readmission), all through ordinary admission.
- **Rule languages beside admission.** Identity and bridge recursion (`identity_recursion`), guarded higher fields (`higher_field`), the experimental stage universe (`stage`) and guarded admission of staging-equation families (`admission`); none of them admits a declaration on its own authority.
- **The content key.** `ContentTable`, `support_key`, `content_digest`, `NodeSupport` and `SupportContext`: content ids, the memo key as one name in the content table built from its members' names, and content digests. A key names a reference to a plain definition by its declared type, body and rank among the definitions of that content, and every other constant by its admission position. It names the binders a goal reads as the support the goal's node carries from `gandr-kernel-term` names them, with no walk over the term.
- **The rewrites.** `shift_value_type` and `substitute_comp_type`, de Bruijn shifting and substitution as memoized machines.
- **Accounting.** `ExpansionCensus`: goal expansions and memo recalls per plane, the observation every measurement here is asserted through.
- **Errors.** `KernelError`, whose payloads are content — a head former and the offending node's content digest — because admission truncates the arena and an arena id would dangle.

## Expected features

- **Staging discipline.** A producer resolves every staged declaration by admitting, bypassing or abandoning it. A staged declaration left unresolved keeps its content in the arena and blocks the admission of every declaration staged before it.
- **Receipt scope.** A `CheckedId` names a position, not an environment identity. Use it only with the corresponding admission history.
- **A vouched bypass.** `add_decl_unchecked` performs no checking: the caller vouches for the declaration, and `audit` reports every declaration that rests on it.
- **A trace in the kernel's terms.** A replay's caller translates its sides and the bodies it allows unfolding into the replay's arena, maps each trace identifier to the constant it names or `ReplayNode::Other`, and maps its engine's verdict to an `EngineClaim`. A body is a closed value, an operator's body is closed beyond its parameters, and a constant given neither is opaque.
- **Reduced codes.** Conversion fires no reduction, so two codes convert only when they are structurally equal. A producer hands the kernel reduced codes to avoid a refusal.
- **`--cfg anodized_panic` for enforcement.** Built with this `cfg` across the whole dependency graph, the `#[spec]` attributes check their clauses at runtime and panic on a violation. The enforcing test lane sets it.

## Examples

Stage a declaration, admit it, watch an ill-typed one refused, and audit what the admitted one rests on.

```rust
use gandr_kernel_core::Environment;
use gandr_kernel_core::KernelError;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::LevelSignature;

fn example() -> Result<(), KernelError> {
    let mut environment = Environment::new();

    let unit = {
        let mut staging = environment.stage();
        let declared = staging.arena().value_type_unit();
        let body = staging.arena().value_unit();
        staging.def(LevelSignature::monomorphic(), declared, body)
    };
    let admitted = environment.add_decl(unit)?;

    let ill_typed = {
        let mut staging = environment.stage();
        let declared = staging.arena().value_type_base(BaseType::Integer);
        let body = staging.arena().value_unit();
        staging.def(LevelSignature::monomorphic(), declared, body)
    };
    assert!(environment.add_decl(ill_typed).is_err());

    let report = environment.audit(admitted);
    assert!(report.axioms().is_empty());
    assert!(report.unchecked_admissions().is_empty());
    Ok(())
}
```

`tests/acceptance.rs` carries the memo measurements and the poisoned-entry cases; `tests/adversarial_depth.rs` the depth totality; `tests/sealed_export.rs` a sealed module's export replayed and its rewritten copies refused. Run them with the unit tests, then the enforcing twin:

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
| Admission, staging order, the audit, replay | [`src/env.rs`](src/env.rs) |
| The seal rule: a manifest atom read as its representation | [`src/seal.rs`](src/seal.rs) |
| Conversion and its discharged set | [`src/conv.rs`](src/conv.rs) |
| Conversion replay, its decisions and laws | [`src/replay.rs`](src/replay.rs) |
| The content table, the memo key and the binders a goal reads | [`src/encoding.rs`](src/encoding.rs), [`src/support.rs`](src/support.rs) |
| Shifting and substitution | [`src/rewrite.rs`](src/rewrite.rs) |
| Universe paths | [`src/path_universe.rs`](src/path_universe.rs) |
| The directed family: formation, `stay`, `then`, `ride` and its telescope form, the covariance gate, certificate admission and the permanent refusals | [`src/flow_universe.rs`](src/flow_universe.rs) |
| Element and function identity: formation, `here`, transport and its telescope over a dependent motive, higher fields, higher and quantified evaluation; the bridge's formation and fibre, and its refusal at a sealed atom | [`src/element_identity.rs`](src/element_identity.rs) |
| Identity and bridge recursion, function identity, the bridge clauses and their decision | [`src/identity_recursion.rs`](src/identity_recursion.rs), [`src/identity_recursion/recursive.rs`](src/identity_recursion/recursive.rs) |
| Guarded higher fields | [`src/higher_field.rs`](src/higher_field.rs) |
| Session codes and certificates | [`src/session.rs`](src/session.rs) |
| The stage universe and residual readmission | [`src/stage.rs`](src/stage.rs) |
| Guarded admission of equation families | [`src/admission.rs`](src/admission.rs) |

## References

- `vault:01a178aa-6917-7983-b5cd-86e2af86b3ec` — lineage: the kernel re-assessment's design (§ kernel-reassessment-design items 2 and 10) — a key names the constants it reaches by content, in table-local records.
- `vault:01a178aa-6917-7983-b5cd-86e2af86b3ec` — lineage: the kernel re-assessment's design (§ kernel-reassessment-design items 1 and 3) — the key reads the binders a goal reads off the support its node carries, derived by the kernel from its own nodes.
- `vault:01a12317-453f-7980-9c86-68f75917f3a6` — lineage: the bicontextual core (§ codebruijn-carrier, § footprint-from-support) — the syntactic layer of a goal's demanded context is carried on its node and read off it; the judgement does not return the layer conversion consults.
- `vault:01a178aa-ce14-7610-bcad-5aab5f9c0b0f` — lineage: § kernel-verdict-reuse — keys, receipts and the re-check.

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
