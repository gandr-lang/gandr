# gandr-theory-shapes

Finite shapes for gandr: decidable subshapes of finite carriers, the outer pushout of two of them, and entailment between face formulas in the conjunctive band, its column disjunctions and the monotone band, with a derivation or a countermodel that a validator checks without the decision procedure.

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

**What.** A shape parameter in the sense of FaceTT whose shapes are finite carriers `Fin(m)` and nothing else. A `Subshape` is a decidable subset of a carrier with its complement, meet, union and inclusion; a `Cofibration` is an inclusion presented with its complement in the target; a `UnionSquare` is the outer pushout of two subshapes over their meet, partitioning the carrier into four blocks, with `mediator` gluing two maps that agree on the meet into the one map out of the union. Face formulas are flat tables over `⊤`, `⊥`, `∧`, `∨` and membership atoms `x ∈ S`. A `Problem` is an entailment query whose premise is a conjunction of atoms and whose conclusion is a conjunction of atoms and column disjunctions `x ∈ S₁ ∨ … ∨ x ∈ Sₙ`, every atom on one variable; `decide` answers it with `Evidence::Holds(Derivation)` or `Evidence::Refuted(Countermodel)`. A `Problem` of the monotone band holds free connectives over monotone atoms, and its `Band` holds the normal form of each side. There is no interval, no endpoint face and no Glue. The crate is `no_std` and depends on `core`, `alloc`, the specification facade and `gandr-theory-stone-duality`.

**Why.** Extension types over first-order data — records, and metavariables whose boundary is constrained — restrict along a decidable subshape of a finite carrier, and their boundary questions are atomic or conjunctive. A match's coverage over one column is a column disjunction: one atom per arm over the column's constructors, covered when `⊤` entails it, and a countermodel is a constructor no arm takes. A column disjunction is membership in a union over one finite carrier, never over an interval. Intersection, union and inclusion decide that band in polynomial time. The composite language is coNP-complete over finite membership alone. So admission refuses a disjunction across variables or in a premise beside an atom that is not monotone. A query whose every atom is monotone is a pair of polynomials of the free distributive lattice. The monotone band decides that pair in normal form, within a budget of 1024 terms. Bridges in gandr are interval-free, the local theory of internal parametricity without an interval in observational form, so the shape theory needs no interval for them; the cubical interval and Glue are the alternative not taken, and a consumer that needs a diagonal or an interval reverses the decision with its fixture.

**How.** `decide` intersects the premise's atoms variable by variable over raw membership tables, unites each column disjunction's atoms, then tests each conclusion conjunct for inclusion. A `Derivation` has one of five forms. The four forms of the conjunctive band are an empty carrier, a reached `⊥`, disjoint premise atoms on one variable, and a citation of premise atoms for each conclusion conjunct. The fifth form covers each premise term of the monotone band by a conclusion term above it. `Derivation::validate` checks each form against the query. `Countermodel::validate` checks a total assignment's bounds and evaluates both formulas at it. Neither validator calls the decision, and every answer in the agreement suite is checked against a separately written truth-table evaluator. Formulas are tables with every child before its parent, so admission, decision and validation are loops; indices cross the API as `Point`, `PointCount`, `Variable`, `NodeId` and `TermIndex`.

## References

- Maximilian Schönlank, Andreas Nuyts and Dominique Devriese. "Towards FaceTT: a generalization of intensional type systems with glue". TYPES 2026, [abstract 42](https://types2026.cse.chalmers.se/abstracts/42.pdf) and [slides](https://types2026.cse.chalmers.se/slides/42.pdf) — the shape parameter, face theories over `⊤`, `⊥`, `∧`, `∨`, and decidable atomic entailment as the algorithmic assumption.
- Ambrus Kaposi and Szumi Xie. "Second-Order Generalised Algebraic Theories: Signatures and First-Order Semantics". FSCD 2024, [doi:10.4230/LIPIcs.FSCD.2024.10](https://doi.org/10.4230/LIPIcs.FSCD.2024.10) — the structural theory of signatures (Definition 13), whose substitution gives every representable sort its diagonal; why an affine interval is not a shape sort here.
- Robert Rose and Daniel R. Licata. "Complexity of Cubical Cofibration Logics I: coNP-Complete Examples". TYPES 2024, [doi:10.4230/LIPIcs.TYPES.2024.9](https://doi.org/10.4230/LIPIcs.TYPES.2024.9) — the coNP bar the composite language meets.
- Thorsten Altenkirch, Yorgo Chamoun, Ambrus Kaposi and Michael Shulman. "Internal Parametricity, without an Interval". POPL 2024, [doi:10.1145/3632920](https://doi.org/10.1145/3632920) — bridges as a local theory without an interval.
- Cyril Cohen, Thierry Coquand, Simon Huber and Anders Mörtberg. "Cubical Type Theory: a constructive interpretation of the univalence axiom". TYPES 2015, [doi:10.4230/LIPIcs.TYPES.2015.5](https://doi.org/10.4230/LIPIcs.TYPES.2015.5) — the interval, its face lattice and Glue.
- `vault:01a1897b-d199-7d10-a325-587b76db2508` — lineage: the shape parameter is a store of names, read from `gandr-theory-nominal-automata` at a `Boundary`.
- `vault:01a1aa2d-a69c-7030-91e0-337d68d88151` — anchor: the presented-spaces frame, whose face formulas form a lattice with a free monotone part, where the monotone band decides.

## Provided features

- `Subshape`, `Membership`, `SetOperation`, `Inclusion`: decidable subshapes of a finite carrier, their complement, meet, union and inclusion with the least escaping point.
- `Cofibration`: an inclusion with its complement in the target.
- `UnionSquare`, `Block`, `Leg`: the outer pushout of two subshapes over their meet and its universal map, `UnionSquare::mediator`.
- `Formula`, `Node`: face formulas over membership atoms as flat, shared tables.
- `Problem`, `Band`: an admitted query, with each side's conjuncts in the conjunctive band and each side's normal form in the monotone band.
- `decide`, `Evidence`, `Derivation`, `Citation`, `Countermodel`: the decision with evidence either way, and the two validators.
- `ShapeError`: every refusal of construction, admission and evidence, by the index it concerns.
- `Point`, `PointCount`, `Variable`, `NodeId`, `TermIndex`: the indices and sizes a query crosses.
- `Boundary`, `BoundaryError`: a carrier as a store of names from `gandr-theory-nominal-automata`, in name order; a face read by names, a point's name read back, and the mediator refusing a disagreement by its name.

## Expected features

- The specification facade's `cfg(anodized_panic)` turns every `#[spec]` clause into a runtime check; `decide`'s clause then validates its own evidence on every call.
- **Names in, `Fin(m)` out.** A `Boundary` holds a carrier's names in a register store of `gandr-theory-nominal-automata`, which refuses a name held twice. The registers run in name order, so every ordering of one list of names builds one boundary and one problem over it decides to one answer. The nominal reading is the carrier's: a face fixed is a set of names retained, an inclusion releases the names its source lacks, and a leak is a name left unreleased at an accepting boundary. The decision keeps its membership tables over `Fin(m)`: a meet over stores costs 1.8 to 17.6 times a meet over the tables.

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

`src/lib.rs` holds the decision record and the references: finite shapes and no interval, the conjunctive band, its column disjunctions and the monotone band, the refusal of the rest of the composite language, and evidence by meets, inclusions and covers rather than case trees. Subshapes, inclusions and the union square are in `src/finite.rs`; named carriers and their nominal reading in `src/boundary.rs`; formulas, admission, the conjuncts of a side and the normal forms of the monotone band in `src/formula.rs`; the decision and both validators in `src/oracle.rs`; the refusals in `src/error.rs`.

## License

`Apache-2.0 WITH LLVM-exception`, the workspace licence, whose text is at the repository root.
