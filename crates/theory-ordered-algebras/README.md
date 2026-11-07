# gandr-theory-ordered-algebras

One law checker for the ordered semirings and commutative rings of gandr, with the max-plus semiring and the Lawvere quantale over exact dyadics, the usage semiring of the core language's grades, and the exact amplitudes of Clifford+T circuits with their gates.

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

**What.** An `OrderedSemiring` states a carrier, an order, a zero, a one, an addition and a multiplication. `check` decides sixteen laws on it: the semiring laws, the laws of the order, and the monotonicity of both operations. A law that fails returns a `LawFailure` that names the instance, the law and the elements that break it. A `CommutativeRing` adds a negation, and `check_ring` adds the commutativity of the product and the inverse of the sum under the discrete order. `Amplitude` is an element of `ℤ[1/√2, i]` at its least scale, so equal amplitudes have equal forms, and the gates `H`, `S`, `T` and `CNOT` are unitary matrices over it.

**Why.** A grade, a weight, a distance and a cost are each a value of an ordered semiring, and gandr takes its grade algebra as a parameter. One checker states the laws once, so each algebra gandr uses is checked against the same statement. The core checker's access rules read the usage semiring here, so the checker runs the operations whose laws the suite decides.

**How.** A law of arity `k` reads every `k`-tuple of the elements a carrier gives: the whole carrier when it is finite, and the elements an instance generates when it is not. The checker allocates nothing but a counterexample. An operation whose exact result lies past the represented elements refuses with `Outside`, and the checker reports that law as undecided at those elements. An amplitude holds four 128-bit coefficients and a scale; a `State` holds a register's vector and a scratch vector of the same size, so a gate allocates nothing, and a refused step leaves the state as it was.

## References

- `vault:01a1aa2d-a69c-7030-91e0-337d68d88151` — exemplar: the frame's ordered algebras, and the probe that checks their laws with one checker.
- `vault:01a178aa-6e2c-7720-a0bd-c5e1f9c4e08e` — exemplar: the grades read as counts, costs and distances, and the semiring that carries each kind.
- `Wood-2024-framework_semiringannotated_type_systems` — dependency: James Wood. "A Framework for Semiring-Annotated Type Systems". Doctoral thesis, University of Strathclyde, 2024 — § 4.1's posemiring laws of Definitions 4.1.1 and 4.1.2, which `Law` states, and the linearity posemiring of Example 4.1.3, which `Usage` is, in the reverse order, so a sum of uses lies at or below a bound: the dual-context calculus as the instance at `{0, 1, ω}`.
- `Ahrens-2025-weighted_rewriting_semiring_semantics_abstract_reduction_systems` — dependency: Emma Ahrens, Jan-Christoph Kassing, Jürgen Giesl and Joost-Pieter Katoen. "Weighted Rewriting: Semiring Semantics for Abstract Reduction Systems". 2025, [arXiv:2505.08496](https://arxiv.org/abs/2505.08496) — § 2's semiring of Definition 5 with the monotone partial order of footnote 3, which the laws state; no law states the complete lattice of Definition 7, which an infinite reduction needs.
- `Jeandel-2018-complete_axiomatisation_zxcalculus_clifford+t_quantum_mechanics` — dependency: Emmanuel Jeandel, Simon Perdrix and Renaud Vilmart. "A Complete Axiomatisation of the ZX-Calculus for Clifford+T Quantum Mechanics". LICS 2018, [arXiv:1705.11151](https://arxiv.org/abs/1705.11151) — § 8's Proposition 10: the Clifford+T fragment represents exactly the matrices over `D[e^{iπ/4}]`, `D = ℤ[1/2]`, which is `ℤ[1/√2, i]`; § 5.1's unique form over the dyadics.

## Provided features

- `OrderedSemiring`, `CommutativeRing`, `Carrier`: the signatures, and the elements a check reads.
- `Law`, `RingLaw`, `check`, `check_law`, `check_ring`, `check_ring_law`: the sixteen laws and the two a ring adds, and the checkers of all of them or of one.
- `Decided`, `LawFailure`, `Counterexample`: what a check decided, and the instance, the law and the elements of a failure.
- `Tropical`, `MaxPlus`: the max-plus semiring over exact dyadics with `−∞`.
- `Lawvere`, `Distance`: the Lawvere quantale of extended non-negative dyadics, under the reverse order.
- `Usage`, `Usages`: the usage semiring `{0, 1, ω}` that the core language's grades read, and its instance on the whole carrier.
- `Amplitude`, `RealAmplitude`, `Coefficient`, `Scale`: the exact amplitudes `ℤ[1/√2, i]` and the real subring `ℤ[1/√2]` of their squared moduli, each at its least scale, with exact sums, products, negations and conjugates.
- `Amplitudes`, `RealAmplitudes`: the two rings under the discrete order, on the elements a check generates.
- `Gate`, `State`, `QubitCount`, `QubitIndex`, `CircuitRefusal`: the gates `H`, `S`, `T` and `CNOT` as unitary matrices, and the state vector of a register of at most 20 qubits that a circuit acts on.

## Expected features

- The specification facade's `cfg(anodized_panic)` turns every `#[spec]` clause into a runtime check.
- A coefficient, or a partial product or sum of coefficients, past the 128-bit integers is refused, never rounded. A circuit of unitary gates keeps each coefficient at most `2^k` at scale `k`, so its scale bounds what it can reach.

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
mise exec -- cargo bench -p gandr-theory-ordered-algebras
```

## Where the detail lives

The signatures are in `src/signature.rs`, the laws and the checkers are in `src/law.rs`, the max-plus and Lawvere instances are in `src/instance.rs`, the usage semiring is in `src/usage.rs`, the amplitudes are in `src/amplitude.rs`, and the gates and the state vector are in `src/gate.rs`. The bound of each grade of the core language is checked in `gandr-core-term`'s suite `tests::grades`. The library `std.quantum` holds the same amplitudes in gandr, and `corpus/model/quantum/amplitudes.gandr` runs `H T H` on `|0⟩` to them.

## License

`Apache-2.0 WITH LLVM-exception`, the workspace licence, whose text is at the repository root.
