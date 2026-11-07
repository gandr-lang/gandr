# gandr-theory-ordered-algebras

One law checker for the ordered semirings of gandr, with the max-plus semiring and the Lawvere quantale over exact dyadics, and the usage semiring of the core language's grades.

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

**What.** An `OrderedSemiring` states a carrier, an order, a zero, a one, an addition and a multiplication. `check` decides sixteen laws on it: the semiring laws, the laws of the order, and the monotonicity of both operations. A law that fails returns a `LawFailure` that names the instance, the law and the elements that break it.

**Why.** A grade, a weight, a distance and a cost are each a value of an ordered semiring, and gandr takes its grade algebra as a parameter. One checker states the laws once, so each algebra gandr uses is checked against the same statement. The core checker's access rules read the usage semiring here, so the checker runs the operations whose laws the suite decides.

**How.** A law of arity `k` reads every `k`-tuple of the elements a carrier gives: the whole carrier when it is finite, and the elements an instance generates when it is not. The checker allocates nothing but a counterexample. An operation whose exact result lies past the represented elements refuses with `Outside`, and the checker reports that law as undecided at those elements.

## References

- `vault:01a1aa2d-a69c-7030-91e0-337d68d88151` — exemplar: the frame's ordered algebras, and the probe that checks their laws with one checker.
- `vault:01a178aa-6e2c-7720-a0bd-c5e1f9c4e08e` — exemplar: the grades read as counts, costs and distances, and the semiring that carries each kind.
- `Wood-2024-framework_semiringannotated_type_systems` — dependency: James Wood. "A Framework for Semiring-Annotated Type Systems". Doctoral thesis, University of Strathclyde, 2024 — § 4.1's posemiring laws of Definitions 4.1.1 and 4.1.2, which `Law` states, and the linearity posemiring of Example 4.1.3, which `Usage` is, in the reverse order, so a sum of uses lies at or below a bound: the dual-context calculus as the instance at `{0, 1, ω}`.
- `Ahrens-2025-weighted_rewriting_semiring_semantics_abstract_reduction_systems` — dependency: Emma Ahrens, Jan-Christoph Kassing, Jürgen Giesl and Joost-Pieter Katoen. "Weighted Rewriting: Semiring Semantics for Abstract Reduction Systems". 2025, [arXiv:2505.08496](https://arxiv.org/abs/2505.08496) — § 2's semiring of Definition 5 with the monotone partial order of footnote 3, which the laws state; no law states the complete lattice of Definition 7, which an infinite reduction needs.

## Provided features

- `OrderedSemiring`, `Carrier`: the signature, and the elements a check reads.
- `Law`, `check`, `check_law`: the sixteen laws, and the checker of all of them or of one.
- `Decided`, `LawFailure`, `Counterexample`: what a check decided, and the instance, the law and the elements of a failure.
- `Tropical`, `MaxPlus`: the max-plus semiring over exact dyadics with `−∞`.
- `Lawvere`, `Distance`: the Lawvere quantale of extended non-negative dyadics, under the reverse order.
- `Usage`, `Usages`: the usage semiring `{0, 1, ω}` that the core language's grades read, and its instance on the whole carrier.

## Expected features

- The specification facade's `cfg(anodized_panic)` turns every `#[spec]` clause into a runtime check.

## Examples

```rust
use gandr_theory_exact_reals::Dyadic;
use gandr_theory_ordered_algebras::{MaxPlus, Tropical, check};

let semiring = Tropical::generated(vec![
    MaxPlus::NegativeInfinity,
    MaxPlus::Finite(Dyadic::from(-1_i64)),
    MaxPlus::Finite(Dyadic::ZERO),
    MaxPlus::Finite(Dyadic::from(2_i64)),
]);
let decided = check(&semiring).unwrap();
assert_eq!(usize::from(decided.laws()), 16);
```

```sh
mise exec -- cargo nextest run -p gandr-theory-ordered-algebras
```

## Where the detail lives

The signature is in `src/signature.rs`, the laws and the checker are in `src/law.rs`, the max-plus and Lawvere instances are in `src/instance.rs`, and the usage semiring is in `src/usage.rs`. The bound of each grade of the core language is checked in `gandr-core-term`'s suite `tests::grades`.

## License

`Apache-2.0 WITH LLVM-exception`, the workspace licence, whose text is at the repository root.
