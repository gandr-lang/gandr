# The experimental stage universe

The one-subject page for the `stage` module of `gandr-kernel-core`: the staging language it checks, the replay that admits a staged equation, and the readmission of a residual as an ordinary declaration. The crate's [README](../README.md) states the rest of the kernel.

<!-- toc -->

- [Experimental stage universe](#experimental-stage-universe)
- [Experimental stage readmission](#experimental-stage-readmission)

<!-- tocstop -->

## Experimental stage universe

The `stage` module checks a one-depth structural staging language. An ordinary hypothesis `j : In M` admits the inner universe `U₀(M)`; its codes describe naturals and structural arrows. `Lift(A)` classifies meta programs producing inner terms. Quote and splice leave the telescope unchanged. Their two round trips are conversion rules, including over open variables.

Formation keeps arrow domains and codomains at one stage. Natural iteration stays within its scrutinee's stage. A proposed elimination from an inner type or its code universe into the outer framework returns `StageError::InnerToOuter`. Missing or wrong-model tokens return `MissingHypothesis`; nested lifts return `StageMismatch`.

`replay` independently forms both endpoints, derives every elementary reduct, and checks congruence only over previously proved child equations. Its local equivalence table connects checked equations, carries no imported answers, and is discarded on return. The ordinary check memo and its six binding conditions are unchanged. The auxiliary arena retains replay scratch syntax; callers own its lifetime and each walk has an explicit work budget.

The representation is in [kernel-term](../../kernel-term/README.md#experimental-stage-syntax), the producer in [core-nbe](../../core-nbe/docs/staging.md#experimental-stage-normalization), and residual readmission in [core-checker](../../core-checker/README.md#experimental-stage-readmission). The fragment has one structural stage depth and an auxiliary arena; native formers, artifact encoding and surface syntax are separate integration boundaries.

**Placement.** A separate rule language keeps native codecs and all existing core walks unchanged. Flat arenas, finite worklists and call-local DAG tables avoid recursive ownership and repeated expansion of shared rewrite nodes. The alternative is native former integration across every walker and codec; choose it when persisted staged declarations become the requested boundary. No dependency is added. Normalization strategy remains outside the kernel.

The rules follow András Kovács, _Staged Compilation with Two-Level Type Theory_, ICFP 2022, §2, [doi:10.1145/3547641](https://doi.org/10.1145/3547641). His [TFP 2026 slides](https://andraskovacs.github.io/pdfs/tfp26prez.pdf), “The problem with sub-structural typing”, identify why linear application cannot support the same lifted application: the free-variable supports need not be disjoint. This fragment permits weakening and contraction throughout.

## Experimental stage readmission

`gandr_core_checker::stage::compile` replays a [stage certificate](#experimental-stage-universe), then extracts its quoted natural function into backward-referencing first-order register instructions. Open captures and every residual constructor other than the single input, natural literals and multiplication are refused.

`Program::admit` translates that program to a CBPV thunk with one top-level lambda, sequencing binds and direct primitive calls. `Environment::add_decl` checks the declaration. Object naturals use nonnegative integer literals; multiplication is an explicitly admitted typed axiom, visible in the audit. The kernel proves typing and staging conversion, not arithmetic properties of that primitive. `Program::execute` supplies checked machine-natural arithmetic, returning `Overflow` instead of wrapping.

The end-to-end witness independently interprets the admitted CBPV body and compares it with exponentiation over the same bounded grid as the producer's witness. It also checks the axiom audit, absent unchecked admissions, open capture refusal and a normal form whose certificate derivation was removed.
