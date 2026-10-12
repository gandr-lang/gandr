# Recursive data, fixpoints and derived eliminators

How `gandr-core-checker` refuses an inadmissible self occurrence, checks a fixpoint and replays its claim, and derives the eliminator a recursive declaration is consumed by. The crate's [README](../README.md) states the rest of the crate; the kernel's [descent module](../../kernel-core/src/check/descent.rs) states the rule both checkers enforce.

<!-- toc -->
- [References](#references)
- [Both checkers refuse by the same names](#both-checkers-refuse-by-the-same-names)
- [A fixpoint is a checking form](#a-fixpoint-is-a-checking-form)
- [Recursion keeps admission order](#recursion-keeps-admission-order)
- [The derived eliminator](#the-derived-eliminator)
- [Definitions by eliminator](#definitions-by-eliminator)
- [The decision](#the-decision)
- [Witnesses](#witnesses)
<!-- tocstop -->

## References

- Conor McBride. "Elimination with a Motive." _Types for Proofs and Programs (TYPES 2000)_, LNCS 2277, Springer (2002). <https://doi.org/10.1007/3-540-45842-5_13> — the eliminator stated over an explicit motive, which the fold takes as an input.
- Eduardo Giménez. "Structural recursive definitions in type theory." _ICALP 1998_, LNCS 1443, Springer (1998). <https://doi.org/10.1007/BFb0055070> — the guarded fixpoint the fold is written over.

## Both checkers refuse by the same names

Both checkers run the same occurrence walk before a data declaration forms, and refuse by the same names: `NegativeOccurrence`, `NestedOccurrence`, `IndexOccurrence`, `NonUniformOccurrence` and `CrossBlockReference`, each carrying the kernel's `OccurrenceSite` and each classified as malformed source. A declaration the checker admits, the kernel admits on readmission; one it refuses never reaches the bridge.

## A fixpoint is a checking form

A fixpoint checks against any computation type `C`, its body checked at `C` under a binder of `U C`; in synthesis position it is refused, naming the form. A structural-descent claim is replayed by the checker's own descent walk before the body is checked. A claim that fails is `DescentNotReplayed`, naming the fixpoint and the kernel's `DescentRefusal`, and readmission re-derives the same verdict. A partial fixpoint carries no claim and is checked at any computation type.

## Recursion keeps admission order

The crate recorded that the `rec { … }` form and its guarded fixed point would reverse [resolution by admission position](../README.md#resolution-by-admission-position), admitting a body that refers to its own declaration. The fixpoint here does not need that reversal. It binds its own thunk as a variable, `fix x. M` with `x : U C`, so a recursive body refers to that binder, never to its own admission position, and erases to the kernel's former without a self-referential constant. One resolution rule then serves the checker, the bridge and the kernel's admission prefix. A data declaration's self occurrence is the one exception, read through the declaration's own signature while that declaration forms.

## The derived eliminator

`eliminator::derive` writes, per declaration and motive, the fold

```text
elim_T[C] : U (Π p̄ : P̄. U M_1 → … → U M_n → Π (x : T p̄). C)
elim_T[C] = thunk (λp̄. λm̄. fix_SD rec. λx. case x [C] of { c_i ↦ λf̄. (force m_i) f̄ h̄ })
M_i       = Π f̄ : F̄_i. U H_1 → … → U H_r → C[c_i f̄ / x]
```

with one hypothesis per recursive field, in field order. A direct field `f : T p̄` has `H = C[f / x]` and `h = thunk ((force rec) f)`. A function field `f : U (Π ȳ. F (T p̄))` has `H = Π ȳ. C` and `h = thunk (λȳ. t ← (force f) ȳ; (force rec) t)`. Its hypothesis ranges over the function's results, where no scrutinee is in scope, so a motive naming its scrutinee at such a declaration is `DerivationRefusal::DependentMotiveAtFunctionField`.

The fold is untrusted. A producer files the eliminator as an ordinary definition: the checker judges it, the kernel readmits it, and both replay its fixpoint's structural-descent claim.

## Definitions by eliminator

A definition by eliminator is an application `force (elim_T[C]) p̄ m̄ x`. `length`, `append` and `map` over `List A`, and `plus` over Nat, each:

- check, and normalise through `core-nbe` to the expected numeral or list;
- readmit through the kernel with an empty axiom audit;
- export to the same bytes on every run;
- carry a conversion whose trace the kernel replays, both the convertible and the apart verdict.

A Tree with a function field derives its eliminator too, and a depth defined through it checks, readmits and normalises.

## The decision

**Choice.** The eliminator is derived source over the kernel's one fixpoint, with the motive explicit, rather than a checker-native recursor former.

**Alternatives.** A native recursor needs a kernel rule per signature. Compiling pattern-matching definitions to case trees belongs to the lowering, which this fold serves rather than replaces.

**Reversal.** A derivation the descent replay cannot follow, such as a nested occurrence's hypothesis through another family's eliminator, needs a generalised descent rule first.

## Witnesses

`recursive_data::recursive_data::recursive_blocks_are_admitted_in_both_checkers`, `recursive_data::recursive_data::occurrences_are_refused_by_name_in_both_checkers`, `recursive_data::recursive_data::descent_claims_replay_or_are_refused_by_name`, `recursive_data::recursive_data::a_fixpoint_checks_at_every_computation_type`, `recursive_data::recursive_data::derived_eliminators_are_admitted_and_readmitted`, `recursive_data::recursive_data::definitions_by_eliminator_normalise`, `recursive_data::recursive_data::the_kernel_replays_a_conversion_through_a_definition_by_eliminator` and `recursive_data::recursive_data::the_export_is_deterministic`.
