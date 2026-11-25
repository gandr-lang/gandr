# gandr-theory-reductions

This crate holds the reductions of one complex onto another for gandr: the collapse, the inclusion, a witness for each inverse law, and the replay that checks them, with two reductions in sequence and reductions of one type side by side. It holds no search: a matching, a strategy of rules or a cover derivation finds a reduction elsewhere and states it here.

<!-- toc -->
- [Synopsis](#synopsis)
- [References](#references)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Where the detail lives](#where-the-detail-lives)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** A `Reduction` gives a collapse `φ` from its source cells to its target cells, an inclusion `ι` back, a section from each source composite to `ι ∘ φ` of it, and a retraction from `φ ∘ ι` of each target composite back to it. Its `replay` checks each of them and names each `Refusal`. `Then` sets two reductions in sequence, and `Sum` sets reductions of one type side by side, each value named with its `PartIndex`. Both are reductions again.

**Why.** A Morse collapse, a cover of a match and a block of rules each state a reduction, and a reader replays one value. The crate with the search for a matching is not what a reader needs, so the interface is a crate of its own.

**How.** The trait reads the caller's composites and witnesses through its own maps, so the crate names no complex. A composite of two reductions replays both, then checks that the first target is the second source, that `φ` after `ι` gives each target cell back, and that each section closes. A sum replays each part in part order, and a refusal names its part.

## References

- `Doré-2023-computing_spaces_type_theory` — exemplar: Maximilian Doré, "Computing Spaces in Type Theory", DPhil thesis, University of Oxford, 2023 — § 3.5, the collapse and the inclusion of a graph with both inverse proofs; § 3.6, their lift to an equality of types, which composes.
- `Ara-2025-polygraphs_rewriting_higher_categories` — newest: Dimitri Ara, Albert Burroni, Yves Guiraud, Philippe Malbos, François Métayer and Samuel Mimram, _Polygraphs: From Rewriting to Higher Categories_, Cambridge University Press, 2025, `doi:10.1017/9781009498968` — § 7.4.2, the retraction that each elementary Tietze transformation carries.
- `Waas-2025-stratified_homotopy_theory_generalized_simple_homotopy_theory_foundations_applications_intersections` — newest: Lukas Waas, "Stratified Homotopy Theory and Generalized Simple Homotopy Theory: Foundations, Applications and Intersections", doctoral dissertation, Heidelberg University, 2025 — § 2.1, simple homotopy equivalence and Whitehead torsion as its complete obstruction; Example 2.3.2.2, the obstruction group of based chains over a ring, trivial over the integers.
- `vault:01a1aa2d-a69c-7030-91e0-337d68d88151` — anchor: § presented-spaces-normal-forms. Reductions compose in sequence and from local to global.

## Provided features

- `Reduction`, `Then`, `Answer`: a reduction with its collapse, its inclusion, both inverse witnesses and its replay, two reductions in sequence, and what a step gives.
- `Sum`, `Summand`, `PartIndex`, `SumFault`: reductions of one type side by side as one reduction, a value of one part with its part, the place of a part, and why a sum cannot answer.
- `Refusal`, `Closure`, `matched`: each refusal of a replay by name, whether a witness closes, and the check that two lists of cells agree.
- `MorseError`, `Budget`, `Count`: the caller's own fault, a walk past its budget or a sum past the integers, and the units that a walk and a check count in.

## Expected features

- The specification facade's `cfg(anodized_panic)` turns every `#[spec]` clause into a runtime check.

## Examples

`tests/words.rs` states a reduction of words that removes one letter, as one Tietze move does, and composes two of them:

```rust,ignore
let mut both = Removal::new("abc", 'c', "bb").then(Removal::new("ab", 'b', "a"));
assert_eq!(both.replay(), Ok(()));
assert_eq!(both.collapse(&vec!['c', 'b']), Ok(vec!['a', 'a', 'a']));
```

```sh
mise exec -- cargo nextest run -p gandr-theory-reductions
```

## Where the detail lives

The trait of a reduction and the sequence of two reductions are in `src/reduction.rs`, and the sum of reductions is in `src/sum.rs`. The refusals of a replay and the closure of a witness are in `src/refusal.rs`, and the fault of a complex with its units is in `src/error.rs`. `gandr-theory-discrete-morse` reads an equivalence along an acyclic matching as a reduction.

## License

`Apache-2.0 WITH LLVM-exception`, the workspace licence, whose text is at the repository root.
