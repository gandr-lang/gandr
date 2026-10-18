# gandr-theory-shapes

Finite shapes for gandr: decidable subshapes of finite carriers, the outer pushout of two of them, and conjunctive entailment between face formulas, decided with a derivation or a countermodel that a validator checks without the decision procedure.

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

**What.** A shape parameter in the sense of FaceTT whose shapes are finite carriers `Fin(m)` and nothing else. A `Subshape` is a decidable subset of a carrier with its complement, meet, union and inclusion; a `Cofibration` is an inclusion presented with its complement in the target; a `UnionSquare` is the outer pushout of two subshapes over their meet, partitioning the carrier into four blocks, with `mediator` gluing two maps that agree on the meet into the one map out of the union. Face formulas are flat tables over `⊤`, `⊥`, `∧`, `∨` and membership atoms `x ∈ S`. A `Problem` is an entailment query whose premise and conclusion are conjunctions of atoms; `decide` answers it with `Evidence::Holds(Derivation)` or `Evidence::Refuted(Countermodel)`. There is no interval, no endpoint face and no Glue. The crate is `no_std` and depends on `core`, `alloc` and the specification facade.

**Why.** Extension types over first-order data — records, and metavariables whose boundary is constrained — restrict along a decidable subshape of a finite carrier, and their boundary questions are atomic or conjunctive. That band is decided in polynomial time, by intersection and inclusion; the composite language with disjunctions is coNP-complete even over finite membership alone, so it is refused at admission rather than offered. Bridges in gandr are interval-free, the local theory of internal parametricity without an interval in observational form, so the shape theory needs no interval for them; the cubical interval and Glue are the alternative not taken, and a consumer that needs a diagonal or an interval reverses the decision with its fixture.

**How.** `decide` intersects the premise's atoms variable by variable over raw membership tables, then tests each conclusion atom for inclusion. A `Derivation` is one of four forms — an empty carrier, a `⊥` the premise reaches, premise atoms on one variable meeting in the empty subshape, or for each conclusion atom the premise atoms whose meet it includes — and `Derivation::validate` checks the citations against the query with the subshape operations. `Countermodel::validate` checks a total assignment's bounds and evaluates both formulas at it. Neither validator calls the decision, and every answer in the agreement suite is checked against a separately written truth-table evaluator. Formulas are tables with every child before its parent, so admission, decision and validation are loops; indices cross the API as `Point`, `PointCount`, `Variable` and `NodeId`.

## References

- Maximilian Schönlank, Andreas Nuyts and Dominique Devriese. "Towards FaceTT: a generalization of intensional type systems with glue". TYPES 2026, [abstract 42](https://types2026.cse.chalmers.se/abstracts/42.pdf) and [slides](https://types2026.cse.chalmers.se/slides/42.pdf) — the shape parameter, face theories over `⊤`, `⊥`, `∧`, `∨`, and decidable atomic entailment as the algorithmic assumption.
- Ambrus Kaposi and Szumi Xie. "Second-Order Generalised Algebraic Theories: Signatures and First-Order Semantics". FSCD 2024, [doi:10.4230/LIPIcs.FSCD.2024.10](https://doi.org/10.4230/LIPIcs.FSCD.2024.10) — the structural theory of signatures (Definition 13), whose substitution gives every representable sort its diagonal; why an affine interval is not a shape sort here.
- Robert Rose and Daniel R. Licata. "Complexity of Cubical Cofibration Logics I: coNP-Complete Examples". TYPES 2024, [doi:10.4230/LIPIcs.TYPES.2024.9](https://doi.org/10.4230/LIPIcs.TYPES.2024.9) — the coNP bar the composite language meets.
- Thorsten Altenkirch, Yorgo Chamoun, Ambrus Kaposi and Michael Shulman. "Internal Parametricity, without an Interval". POPL 2024, [doi:10.1145/3632920](https://doi.org/10.1145/3632920) — bridges as a local theory without an interval.
- Cyril Cohen, Thierry Coquand, Simon Huber and Anders Mörtberg. "Cubical Type Theory: a constructive interpretation of the univalence axiom". TYPES 2015, [doi:10.4230/LIPIcs.TYPES.2015.5](https://doi.org/10.4230/LIPIcs.TYPES.2015.5) — the interval, its face lattice and Glue.

## Provided features

- `Subshape`, `Membership`, `SetOperation`, `Inclusion`: decidable subshapes of a finite carrier, their complement, meet, union and inclusion with the least escaping point.
- `Cofibration`: an inclusion with its complement in the target.
- `UnionSquare`, `Block`, `Leg`: the outer pushout of two subshapes over their meet and its universal map, `UnionSquare::mediator`.
- `Formula`, `Node`: face formulas over membership atoms as flat, shared tables.
- `Problem`: an admitted query in the conjunctive band, with each side's conjuncts listed.
- `decide`, `Evidence`, `Derivation`, `Citation`, `Countermodel`: the decision with evidence either way, and the two validators.
- `ShapeError`: every refusal of construction, admission and evidence, by the index it concerns.
- `Point`, `PointCount`, `Variable`, `NodeId`: the indices and sizes a query crosses.

## Expected features

- The specification facade's `cfg(anodized_panic)` turns every `#[spec]` clause into a runtime check; `decide`'s clause then validates its own evidence on every call.

## Examples

```rust
use gandr_theory_shapes::{decide, Evidence, Formula, Node, NodeId, Point, PointCount, Problem, Subshape, Variable};

let carrier = PointCount::from(3_usize);
let atom = |inside: &[usize]| {
    let points: Vec<Point> = inside.iter().copied().map(Point::from).collect();
    Node::Member(Variable::from(0_usize), Subshape::new(carrier, &points).unwrap())
};
// x ∈ {0,1} ∧ x ∈ {1,2} ⊢ x ∈ {1}
let premise = Formula::new(vec![atom(&[0, 1]), atom(&[1, 2]), Node::And(NodeId::from(0_usize), NodeId::from(1_usize))]).unwrap();
let conclusion = Formula::new(vec![atom(&[1])]).unwrap();
let problem = Problem::new(vec![carrier], premise, conclusion).unwrap();
let Ok(Evidence::Holds(derivation)) = decide(&problem) else { panic!() };
assert_eq!(derivation.validate(&problem), Ok(()));
```

```sh
mise exec -- cargo nextest run -p gandr-theory-shapes
```

## Where the detail lives

The decision record — finite shapes and no interval, the conjunctive band and why the composite language is refused, evidence by meets and inclusions rather than case trees — and the references are in `src/lib.rs`. Subshapes, inclusions and the union square are in `src/finite.rs`; formulas, admission and the conjuncts of a side in `src/formula.rs`; the decision and both validators in `src/oracle.rs`; the refusals in `src/error.rs`.

## License

`Apache-2.0 WITH LLVM-exception`, the workspace licence, whose text is at the repository root.
