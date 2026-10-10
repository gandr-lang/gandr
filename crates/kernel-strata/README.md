# gandr-kernel-strata

The certified kernel's level oracle: universe levels over zero, variables, successor and binary maximum, held in canonical form, with order and entailment oracles that return checkable evidence in both directions.

<!-- toc -->

- [Synopsis](#synopsis)
- [References](#references)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Evidence and its validators](#evidence-and-its-validators)
- [The level language](#the-level-language)
- [Specification attributes](#specification-attributes)
- [Differential suites](#differential-suites)
- [Relationship to `gandr-theory-orders`](#relationship-to-gandr-theory-orders)
- [License](#license)

<!-- tocstop -->

## Synopsis

**What.** `Level` is a universe level over zero, level variables, successor and binary maximum, held in canonical form. `Level::leq_with_evidence` and `Level::lt_with_evidence` decide the order over all valuations; `LandmarkPoset::admit` admits a declared set of order constraints over level variables; `LandmarkPoset::entails_leq_with_evidence` and `entails_lt_with_evidence` decide the order under those constraints. Every decision returns checkable evidence either way. The crate holds levels only: the universe rule is one call into `Level::lt` and belongs to the kernel proper.

**Why.** Universe stratification keeps `U_l : U_l` underivable, and the kernel's soundness rests on the level order it consults. An oracle that returns evidence instead of a bare verdict concentrates that trust in small validators, and a wrong decision comes with evidence its validator refuses, so the decision procedure is self-incriminating under mutation. The crate is `no_std` over `core` and `alloc` and depends on no other workspace crate, the narrowest form of the trusted base's dependency wall.

**How.** Every level is semantically a finite join `max(c, x_1 + o_1, …, x_k + o_k)` of a constant part and per-variable offsets. With dominated components removed and atoms keyed by variable, that join is a sorted canonical form: two levels denote the same function exactly when their canonical forms are identical, so canonical-form identity is level equality, and the smart constructors make a non-canonical level unrepresentable. `l ≤ m` holds over all valuations exactly when every atom of `l` is dominated by a same-variable atom of `m` and `l`'s constant part by `m`'s value at the zero valuation. Declared constraints compile to Horn clauses over the variables, and loop-checking decides admission as a dichotomy: a least model gives an explicit homomorphism into `ℕ`, and a diverging saturation gives a replayable pumping derivation showing none exists. Entailment under an admitted poset is the minimal-model computation over the same clauses.

## References

- Marc Bezem and Thierry Coquand. "Loop-checking and the uniform word problem for join-semilattices with an inflationary endomorphism." _Theoretical Computer Science_ 913 (2022), pages 1–7. `doi:10.1016/j.tcs.2022.01.017` — the decision procedure, the loop-checking dichotomy (corollary 3.5, admission), entailment by minimal models (corollary 3.4), the shift-by-one device (lemma 2.1), and the worked example the admission and divergence goldens replay.
- Per Martin-Löf. _Intuitionistic Type Theory_. Notes by Giovanni Sambin. Bibliopolis, Naples, 1984. `isbn:978-88-7088-105-9` — the universe stratification this crate is the level layer of.

## Provided features

- `Level`, `LevelVar` and `LevelVarIndex`: the canonical form and its variables. `Level::zero`, `Level::var`, `Level::succ` and `Level::max` construct; `Level::eval` evaluates under a valuation; `Level::lt` and `Level::leq` decide.
- `Level::leq_with_evidence` and `Level::lt_with_evidence`: the order oracle, returning a `LeqWitness` or a `LeqRefutation`. `validate_witness` and `validate_refutation` check either against the two levels.
- `LandmarkConstraint`, `LandmarkPoset` and `LandmarkPoset::admit`: constraint declaration and admission. Admission returns `AdmissionOutcome::Admitted`, a poset carrying its `ConsistencyWitness`, or `AdmissionOutcome::Loop` with a `LoopWitness`; `validate_consistency` and `validate_loop_witness` check them.
- `LandmarkPoset::entails_leq_with_evidence` and `entails_lt_with_evidence`: entailment under an admitted poset, returning an `EntailmentWitness` or an `EntailmentCountermodel`; `validate_entailment_witness` and `validate_entailment_countermodel` check them.
- `LevelError`, `EvidenceError`, `PosetError` and `PosetEvidenceError`: every failure as a typed value.

## Expected features

- **`--cfg anodized_panic` for enforcement.** Built with this `cfg` across the whole dependency graph, the `#[spec]` attributes check their clauses at runtime and panic on a violation. The enforcing test lane sets it.

## Examples

Consumers reach the crate through the kernel and the core checker; a direct call decides an order and checks its evidence.

```rust
use gandr_kernel_strata::Level;
use gandr_kernel_strata::LevelError;
use gandr_kernel_strata::LevelVar;
use gandr_kernel_strata::LevelVarIndex;
use gandr_kernel_strata::validate_witness;

fn example() -> Result<(), LevelError> {
    let variable = LevelVar::new(LevelVarIndex::from(0));
    let level = Level::var(variable);
    let above = level.succ()?;
    let witness = level
        .lt_with_evidence(&above)
        .expect("a variable is strictly below its successor");
    assert_eq!(validate_witness(&level, &above, &witness), Ok(()));
    Ok(())
}
```

Run the tests, including the property differential that pins empty-poset entailment to the free-fragment oracle, then the enforcing twin:

```sh
cargo nextest run -p gandr-kernel-strata
RUSTFLAGS="--cfg anodized_panic" cargo nextest run -p gandr-kernel-strata
```

## Evidence and its validators

Evidence types keep their fields private, so a witness is unforgeable outside the oracle. Each validator recomputes what the evidence claims rather than trusting it.

A derivation records only clause index and shift for each step; a validator recomputes every conclusion. Clause indices refer to one documented, deterministic compilation (declaration order, ascending variable order within a constraint), so an index means the same thing to the oracle, the validators and a reviewer.

The firing log behind a derivation carries, at each step, the atom its instance concluded. Truncating the log to the prefix that covers the goals therefore needs neither a clause lookup nor arithmetic, and its one `None` means exactly that the log does not cover the goals.

Saturation reports divergence from the resulting model, not only from updates made during the current run. An infinite seed is therefore divergent even with no clauses and no firing log. The executable postcondition checks this model/status correspondence, and a zero-update witness preserves both the infinite component and its finite sibling. Counting only newly infinite updates would misclassify that admitted seed.

`EvidenceSubject` names what a seed or goal refers to: a declared level variable, or the pinned bottom generator that carries constants. The crate's `Option` returns — `Level::offset_of`, `ModelValue::as_finite` and the model lookups — are genuine absence, and each specification says so. A violated constraint is reported by `ConstraintIndex`.

Order shifts and counter-valuation spikes use checked addition, never saturation: truncating a natural-number successor would change the relation in the [level algebra](#references). An unrepresentable shift routes to refusal; a validator rejects an insufficient atom or constant bound. The comparison's zero-valuation overflow branch is unreachable because its components are u64-wide and its arithmetic is u128-wide. Widening components requires a distinct overflow carrier before that exclusion changes: a zero valuation does not refute every unrepresentable-spike case. The alternative, saturating the widened sums, hides that obligation. Ceiling witnesses check strict irreflexivity, a spike exactly one past u64::MAX and rejection of a forged strict bound; they do not claim to exercise an unreachable u128 overflow.

## The level language

Declared constraints are variable-only: each side has constant part `0` and at least one atom. Query constants ride a pinned bottom generator `⊥`, ordered below every in-scope variable by clauses added at query time. That encoding is sound, conservative and loop-immune because no declared clause mentions `⊥`; the module docs of `poset` carry the argument. With no constraints declared, entailment agrees with the free-fragment oracle on every input.

The stratification design excludes level inference and unification, generalization, displacement, constraint hypotheses beyond the declared landmark poset, `imax`, and cumulativity.

## Specification attributes

The `# Specification` prose states each obligation. Executable `#[spec(...)]` predicates check canonical constructors, exact arithmetic and refusal boundaries, comparison modes, evidence validity, compilation inputs and replay conclusions. Private algorithm helpers and the differential suites' generators, evaluators and assertion helpers carry the same discipline as public entry points.

Each nontrivial item has a `# Adequacy` hypothesis naming its input domain, observer and defect classes, with links to runnable witnesses. The evidence includes independent semantic and entailment differentials, adversarial certificates, numeric ceilings, empty domains, exact derivation limits and the first covering log prefix. Replay establishes coverage; the shortest-prefix witness separately establishes minimality.

The predicates run under `--cfg anodized_panic`; normal builds do not repeat their checking traversals. Admission and replay check the portions of their postconditions available from retained data rather than taking owned snapshots of consumed inputs. Least-model identity and termination remain mathematical obligations, with termination stated in `- intension:` clauses.

Const-compatible predicates check cross-domain shifts, finite-model projection and strictness without removing compile-time availability. Explicit `- executable: none` clauses explain the remaining boundaries: opaque iterators cannot be consumed by a postcondition; a strategy's full support concerns future draws; and data-item invariants are not checked at construction or relate the value to external operands. Their adequacy witnesses still apply.

## Differential suites

The property suites generate free level terms as a flat, id-addressed arena: a node vector in topological order, every child an index into an earlier slot, the root at the last slot. Reference evaluation, canonical-form construction and successor counting are each one forward pass over that vector, so the suites carry no recursive type and no explicit frame stack. A shared node denotes one value, so sharing is semantically transparent.

## Relationship to `gandr-theory-orders`

The two crates share no machinery, and the kernel takes no dependency on the theory crate. `gandr-theory-orders` maintains a total order over opaque handles for constant-time comparison. This crate decides a partial order over level terms, quantified over all valuations, and returns a certificate either way. Neither operation is expressible in the other's vocabulary, and the trusted base depends on no workspace crate outside the kernel category.

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
