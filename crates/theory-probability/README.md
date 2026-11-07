# gandr-theory-probability

This crate holds finite distributions with exact weights for gandr: the finite Giry monad, the product of two distributions and the marginals of a joint, the restriction to an event, and the decision whether a joint is the product of its marginals. It is the measure of the algebra family that holds probability.

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

**What.** A `Distribution` puts an exact positive weight on each point of a finite support, and the weights sum to one. A weight is the `Rational` of `theory-cellular-sheaves`. `point`, `uniform`, `map` and `bind` are the finite Giry monad: the unit, a uniform choice over a set, the pushforward and the Kleisli extension. `product` gives the joint of two independent distributions, and `first_marginal` and `second_marginal` give each component of a joint. `condition` restricts a distribution to an event and divides each weight by the weight of the event. `independent` decides whether a joint is the product of its marginals, and otherwise gives the first pair where they differ as an `Independence`.

**Why.** Probability is the second instance of the logic that holds gandr's names: in Simpson's atomic sheaf logic, equivalence is equality in distribution and independence is the probabilistic one. The exact model of `std.rand.Eff` enumerates the answers of the draws of a run, and the exemplars that reason about randomness and about nondeterministic sessions read its distribution. One crate states the distributions, so each of them reads one form.

**How.** The support is in ascending order, each point once. So two distributions are equal in distribution exactly when their forms are equal, and the derived equality decides it. Every constructor ends in that form: a stable sort, then one merge of equal points by the sum of their weights. The results of a Kleisli extension are ascending runs, so the sort merges `k` runs in `O(n log k)` comparisons, and a product comes out in order with no sort. A weight past the 128-bit integers is refused by name, never rounded, and so is an event of weight zero.

## References

- `Simpson-2026-equivalence_conditional_independence_atomic_sheaf_logic` — exemplar: Alex Simpson, "Equivalence and Conditional Independence in Atomic Sheaf Logic", _Journal of the ACM_ 73(3), 2026, `doi:10.1145/3809163` — Definitions 8.5 and 8.7, equality in distribution as equal laws and independence as a product of probabilities, and § 10.1, the finite probability spaces as a full subcategory.
- `Li-2024-nominal_approach_probabilistic_separation_logic` — background: John M. Li, Jon Aytac, Philip Johnson-Freyd, Amal Ahmed and Steven Holtzen, "A Nominal Approach to Probabilistic Separation Logic", LICS 2024, `doi:10.1145/3661814.3662135` — § 3, discrete state separated by the product of probability spaces, and Definition 3.5, the independent combination.
- `vault:01a1aa2d-a69c-7030-91e0-337d68d88151` — exemplar: the probability of the presented-spaces frame.

## Provided features

- `Distribution`: a finite support in canonical order with exact weights, the finite Giry monad, the product, the marginals, the restriction to an event and the decision of independence.
- `Independence`: the verdict on a joint, independent or the first pair whose weight is not the product of its marginal weights.
- `ProbabilityError`: every refusal, a weight past the integers, a set or an event with no weight, or weights that are not a distribution.

## Expected features

- The specification facade's `cfg(anodized_panic)` turns every `#[spec]` clause into a runtime check.

## Examples

```rust
use gandr_theory_cellular_sheaves::{Integer, Rational};
use gandr_theory_probability::{Distribution, Independence};

let half = Rational::new(Integer::from(1_i128), Integer::from(2_i128)).unwrap();
let quarter = Rational::new(Integer::from(1_i128), Integer::from(4_i128)).unwrap();
// The sum of two fair coins.
let coin = Distribution::uniform([0_u8, 1]).unwrap();
let sum = coin.bind(|&first| coin.map(|&second| first + second)).unwrap();
assert_eq!(sum.points(), [(0, quarter), (1, half), (2, quarter)]);
// Two coins tossed apart are independent.
let pair = coin.product(&coin).unwrap();
assert_eq!(pair.independent().unwrap(), Independence::Independent);
// Given that the sum is at least one, the first coin shows one with weight two thirds.
let seen = pair.condition(|&(first, second)| first + second >= 1).unwrap();
let two_thirds = Rational::new(Integer::from(2_i128), Integer::from(3_i128)).unwrap();
assert_eq!(seen.first_marginal().unwrap().weight(&1), two_thirds);
```

```sh
mise exec -- cargo nextest run -p gandr-theory-probability
mise exec -- cargo bench -p gandr-theory-probability
```

## Where the detail lives

The distribution, its canonical form, the monad, the product and the restriction to an event are in `src/distribution.rs`. The marginals and the decision of independence are in `src/joint.rs`, and the refusals are in `src/error.rs`.

## License

`Apache-2.0 WITH LLVM-exception`, the workspace licence, whose text is at the repository root.
