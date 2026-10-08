# gandr-kernel-strata

The certified kernel's level oracle: the universe-level algebra over zero, level variables, successor and binary maximum, held in always-canonical form, with an order oracle that returns checkable evidence in both directions.

It holds **levels only** — no terms, no types, and not even the universe rule, which is one call into the strict-order predicate and belongs to the kernel proper. It is `no_std` over `core` and `alloc` and depends on no other crate, which is the sharpest form of the trusted base's dependency wall.

## Status

Ported from the `kernel-strata` crate of the pre-reboot prototype and revised against the reboot constraints. The revisions, all constraint-driven:

- **No owning-pointer recursion in the test generators.** The prototype's differential suites generated free level terms as a `Box`-recursive `Ast` enum. Terms are now a flat, id-addressed arena: a node vector in topological order where every child is an index into an earlier slot, with the root at the last slot. Every fold — reference evaluation, canonical-form construction, successor counting — is one forward pass over that vector rather than a traversal, so the suites carry no recursive type and no explicit frame stack. Sharing between nodes comes for free and is semantically transparent, since a shared node denotes one value.
- **No collapsed failure modes in prefix extraction.** The prototype's witness truncation returned a bare `Option` in which "the log does not cover the goals", "a log step named an unknown clause", and "the concluded offset overflowed" were the same `None`. Each firing-log step now carries the atom its instance concluded, so truncation needs neither a clause lookup nor arithmetic: two of the three failure modes are gone by construction and the surviving `None` means exactly what the caller reports. The public derivation format is unchanged — it still records only clause and shift, because a validator recomputes the conclusion rather than trusting it.
- **Absent variable against distinct generator.** The prototype encoded "which goal or seed this evidence names" as `Option<LevelVar>`, with `None` standing for the pinned bottom generator that carries constants. That is a semantic case, not an absence, so it is now the two-case `EvidenceSubject`. The `Option` returns that remain — `Level::offset_of`, `ModelValue::as_finite`, the two model lookups — are genuine absence and each says so in its contract.
- **Wrapped indices in the evidence vocabulary.** A violated constraint is reported with a `ConstraintIndex` rather than a bare `usize`.
- **Contract clauses in the fixed grammar.** The prototype carried an ad-hoc `- termination:` clause on the saturation and derivation engines and an abbreviated `- fails, panics, intension: as …` line on one method. Termination reasoning now lives in `- intension:`, which is where a promised property of how a computation proceeds belongs, and every clause is written out.
- **References resolve away from their original artifact.** Tracker identifiers, internal design-record section numbers, and slice numbering are gone; the loop-checking results are cited by author, title, venue and DOI at the point of use.

Everything already conformant in the prototype is preserved: no recursion of any kind, transparent newtype wrappers instead of bare primitives, no `as` casts, checked or saturating arithmetic throughout, typed errors with no `unwrap`/`expect`/`panic` outside tests, and evidence types whose fields are private so a witness is unforgeable outside the oracle.

## What it provides

- The level type **is** the canonical form: a finite join of a constant part and per-variable offsets, dominated components removed and atoms keyed by variable. The smart constructors maintain it, so a non-canonical level is unrepresentable rather than merely rejected, and canonical-form identity is the level-equality oracle.
- An order oracle deciding `l ≤ m` over all valuations by domination, returning either a witness pairing each left atom with its dominating bound or a refutation carrying a concrete counter-valuation. Both have validators, so trust concentrates in the checkers and the decision procedure is self-incriminating under mutation.
- A landmark poset: a fixed declared set of order constraints over level variables, admitted by loop-checking as a dichotomy with evidence on each side — an admitted poset carrying an explicit homomorphism into the naturals, or a replayable pumping derivation showing none can exist.
- Entailment under an admitted poset, again with a forward-derivation witness or a countermodel, each with its validator. With no constraints declared, entailment agrees with the free-fragment oracle on every input, which a property differential pins.

## The contract attributes

The `# Specification` prose stays the statement of record; a combined `#[spec(...)]` attribute mirrors it where the clause is a cheap runtime predicate. Eleven items carry one:

- the five checked-arithmetic faces — `LevelOffset::succ`, `LevelConstant::succ`, `LevelValue::checked_add_offset`, `HornOffset::checked_add` and `HornOffset::checked_add_shift` — each stating its refusal boundary as an `is_ok()` equivalence against the complementary operation, so a guard that moved off the ceiling is caught;
- `Level::canonicalized`, whose predicate is the canonical-constant invariant read off the _result_. It repeats the body's `max` scan, so the function costs twice its atom walk — the same order, over a map the size of a declaration's level arity;
- `LandmarkConstraint::leq` and `equal`, each pinning the relation it declares, which is what separates the two adjacent constructors;
- `compile`'s `requires`, re-reading the variable-only guard the constraint constructor established, and `push_family`'s nonempty body;
- `HornClause::new`, whose `Some`-exactly-when-nonempty is the constructor guard stated on the output.

`Level::succ`, `Level::eval`, `LandmarkPoset::admit`, `consistency_certificate`, and `horn::saturate` retain prose-only postconditions. `leq_with_evidence` and `lt_with_evidence` use independent oracle witnesses: their validators re-walk the atoms with a `BTreeMap` lookup each on the kernel’s hottest comparison path.

`anodized` supplies core-only specification helpers with default features disabled. The enforcing test lane selects `--cfg anodized_panic` for the whole dependency graph; no logic/BigInt dependency is enabled.

## Not provided

Declared constraints are variable-only, and query constants ride a pinned bottom generator internal to the encoding. The crate deliberately refuses level inference and unification, generalization, displacement, constraint hypotheses beyond the declared landmark poset, `imax`, and cumulativity — these are exclusions of the stratification design rather than unbuilt steps. A constant-time variable-plus-offset constructor remains a follow-up.

## Relationship to `gandr-theory-orders`

The two crates share no machinery and the kernel takes no dependency on the theory crate. `gandr-theory-orders` maintains a **total** order over opaque element handles for constant-time comparison, which is a data-structure problem for the incremental checking layer. This crate decides a **partial** order over universe-level terms, quantified over all valuations, and returns a certificate either way. Neither operation is expressible in the other's vocabulary, so there is nothing to reuse; and the dependency wall would refuse the dependency in any case, since a `kernel-*` crate depends only on other `kernel-*` crates and on `core` and `alloc`.

## Using it

`cargo test -p gandr-kernel-strata --all-targets` runs the suite, including the property differential that pins the no-constraints agreement between entailment and the free-fragment oracle. Consumers reach the crate through the kernel and the core checker rather than directly.

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

## Theoretical ideas relied on

Universe stratification with levels as a separate certified layer; a sorted canonical form as the decision procedure for the word problem on the free fragment; loop-checking as a dichotomy with evidence on both sides; and the certificate posture at its smallest scale — an oracle that returns checkable evidence instead of a bare verdict, so the validators rather than the procedure carry the trust.

## Primary references

- Marc Bezem and Thierry Coquand. "Loop-checking and the uniform word problem for join-semilattices with an inflationary endomorphism." _Theoretical Computer Science_ 913 (2022), pages 1–7. `doi:10.1016/j.tcs.2022.01.017` — the decision procedure, the loop-checking dichotomy, and the worked example the admission and divergence goldens replay.
- Per Martin-Löf. _Intuitionistic Type Theory_. Bibliopolis, 1984. `isbn:978-8870881052` — the universe stratification this crate is the level layer of. Locator unverified: the ISBN identifies a printing and has not been checked against a title page.

## License

Apache-2.0 WITH LLVM-exception.
