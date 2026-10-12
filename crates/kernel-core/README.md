# gandr-kernel-core

The certified kernel's judgements: the defunctionalized checking machine, type formation, conversion, the admission choke point, the check memo wired as the default path on both machines, and the sequential replay of an untrusted engine's conversion trace.

<!-- toc -->
- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Where the detail lives](#where-the-detail-lives)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** `Environment` admits declarations through one checked choke point, `add_decl`, and one warned bypass, `add_decl_unchecked`; `audit` reports what an admitted declaration transitively rests on. Beneath the choke point sit a bidirectional checking machine, a type-formation walk that computes a type's universe level, and structural conversion. Beside it, `replay` rechecks a term-conversion verdict an untrusted engine reached, decision by decision, from the trace that engine recorded. Representation, the sharing format and the decode budgets belong to `gandr-kernel-term`, the universe algebra to `gandr-kernel-strata`, the memo's storage to `gandr-kernel-check-memo`, and the decision vocabulary to `gandr-kernel-conversion-trace`; this crate is what re-derives an obligation.

**Why.** The kernel grants a producer no credence: every declaration is re-checked before admission, including one a decoder built from untrusted bytes. Such a term can be arbitrarily deep and heavily shared, so the checker must be total on adversarial depth and must not pay for a shared subterm once per occurrence.

**How.** The checker is a defunctionalized machine over explicit stacks, so it is total on depth; conversion is structural comparison with a positive-only id-equality fast path; both machines consult a content-keyed check memo that lives for one check call; and admission truncates the arena on both verdicts, clamped at the admission floor. [`src/lib.rs`](src/lib.rs) states why the four are decided together.

## Provided features

- **Admission.** `Environment` with `stage`, `add_decl`, `add_decl_unchecked`, `abandon` and `audit`; `StagedDeclaration`, `CheckedId`, `AdmittedDeclaration` and `AxiomReport`.
- **The checking machine.** `check_declaration`, the default path with a fresh memo, and `check_declaration_with_memo`, the opt-in entry that returns a verdict and never a `CheckedId`.
- **Type formation.** An iterative walk computing a type's universe level, gating lift strictness, level scope, a sealed atom's kind, and the code a decode of either family owes.
- **Conversion.** `convert_value_type`, `convert_comp_type` and their `convertible_*` forms: structural comparison of two types, descending into the terms they carry, over `Convertibility`.
- **Conversion replay.** `replay`: a conversion trace replayed against an engine's `EngineClaim` for two `ReplaySides`, answering a `KernelVerdict` — certified convertible, certified not convertible, or declined with a `ReplayDecline`.
- **Native formers.** Nominal data and structural records, recursive data with the structural fixpoint, the native List former, universe paths, session codes, and element and function identity (`element_identity`), all through ordinary admission.
- **Rule languages beside admission.** Universe flows (`flow_universe`), identity and bridge recursion (`identity_recursion`), guarded higher fields (`higher_field`), the experimental stage universe (`stage`) and guarded admission of staging-equation families (`admission`); none of them admits a declaration on its own authority.
- **The content key.** `ContentTable`, `encode_support`, `content_digest`, `NodeSupport` and `SupportContext`: content ids, canonical support encodings and their digests.
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

`tests/acceptance.rs` carries the memo measurements and the poisoned-entry cases; `tests/adversarial_depth.rs` the depth totality. Run them with the unit tests, then the enforcing twin:

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
| Nominal data and records; strict positivity; the structural fixpoint | [`src/check/former.rs`](src/check/former.rs), [`src/check/occurrence.rs`](src/check/occurrence.rs), [`src/check/descent.rs`](src/check/descent.rs) |
| Admission, staging order, the audit | [`src/env.rs`](src/env.rs) |
| Conversion and its discharged set | [`src/conv.rs`](src/conv.rs) |
| Conversion replay, its decisions and laws | [`src/replay.rs`](src/replay.rs) |
| The content key, the digest and the binder slice | [`src/encoding.rs`](src/encoding.rs), [`src/support.rs`](src/support.rs) |
| Shifting and substitution | [`src/rewrite.rs`](src/rewrite.rs) |
| Universe paths | [`src/path_universe.rs`](src/path_universe.rs) |
| Universe flows | [`src/flow_universe.rs`](src/flow_universe.rs) |
| Element and function identity: formation, `here`, transport, higher fields and higher evaluation | [`src/element_identity.rs`](src/element_identity.rs) |
| Identity and bridge recursion, function identity | [`src/identity_recursion.rs`](src/identity_recursion.rs), [`src/identity_recursion/recursive.rs`](src/identity_recursion/recursive.rs) |
| Guarded higher fields | [`src/higher_field.rs`](src/higher_field.rs) |
| Session codes and certificates | [`src/session.rs`](src/session.rs) |
| The stage universe and residual readmission | [`src/stage.rs`](src/stage.rs) |
| Guarded admission of equation families | [`src/admission.rs`](src/admission.rs) |

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
