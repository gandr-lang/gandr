# gandr-theory-e-graphs

This crate holds a proof-producing e-graph for gandr. It closes the equations over the term table of a Lawvere theory under congruence. A proof forest gives each equality an explanation, and a checker replays that explanation. The crate also follows egg in three parts: it rebuilds after the unions, it keeps an analysis on each class, and it saturates in phases. It is the crate of the rewriting family that closes equations under congruence and explains each equality that it finds.

Congruence closure is ground completion, so an e-graph is a convergent ground rewriting system. Completion replays its certificates, and an explanation is a certificate of that kind.

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

**What.** An `EGraph` holds terms of a `TermTable` from `theory-coherent-resolutions`. `add` holds a term with each of its arguments. `equation` states an input equation over the table's terms, and `apply` joins the two sides of one of its instances. `rebuild` restores congruence. `find`, `members` and `classes` read the classes. `explain` gives the `Explanation` of the equality of two terms of one class, and `Explanation::replay` checks it against the table and the equations alone. `saturate` runs rounds of matches within a `Budget`. An `Analysis` keeps a datum on each class; `Size` keeps the size of the smallest term that a class represents. `redundant` lists each union inside one class with its `Reason`.

**Why.** A ground block needs no termination certificate, because ground completion always ends. So the e-graph decides what a ground block joins, and its explanations carry the decision to a checker that does not trust it. A redundant union is a loop of its class, which the coherent e-graph reads. An analysis is the verdict memo's shape: a datum on each class, kept as a join.

**How.** The table interns each distinct term once, so a place is a term's identity and the e-graph adds no second table of terms. Each class has a root in a union-find with path compression, a cycle through its members, a list of its parents and a datum; each node has at most one edge of the proof forest. A union adds one forest edge from the node of the smaller class, whose path to its root turns round first, and puts the merged class on the worklist. The rebuild deduplicates the worklist and repairs each class once: it sorts the class's parents by their head and their children's classes, joins each two with one signature by congruence, keeps one parent for each signature, runs `modify`, and makes each parent's datum again. A round of `saturate` reads every match of every equation before it applies one, so the order of the equations does not change the classes.

## References

- `Willsey-2021-egg_fast_extensible_equality_saturation` — exemplar: Max Willsey, Chandrakana Nandi, Yisu Remy Wang, Oliver Flatt, Zachary Tatlock and Pavel Panchekha, "egg: Fast and Extensible Equality Saturation", _Proc. ACM Program. Lang._ 5 (POPL), 2021, `doi:10.1145/3434304` — § 3.1, the deferred rebuild and its deduplicated worklist; § 3.3, the read and write phases; § 4.1, the e-class analysis interface and its invariant.
- `vault:01a1aa2d-a69c-7030-91e0-337d68d88151` — exemplar: § presented-spaces-egraphs, an e-graph as ground completion with its loops.
- `vault:01a178aa-4f9c-7221-a972-619f184e507e` — exemplar: the adoption programme, which takes egg's three mechanisms as specifications.
- `vault:01a178aa-f8ad-73d0-bbe7-c395c922e4f9` — exemplar: rung 3 of the rewriting ladder, a congruence layer over the existing arena.

## Provided features

- `EGraph`, `Joined`, `Tally`, `Members`, `Classes`: the e-graph over a term table, whether a union merges two classes, its counts, and the members of a class and the classes.
- `Equation`, `EquationPlace`, `Reason`, `Direction`, `Redundant`: an input equation and its place, the reason of a union, the side that a step starts from, and a union inside one class.
- `Explanation`, `Proof`, `Step`, `StepReason`, `ProofPlace`, `StepPlace`, `Position`, `Refusal`: the chain of reasons between two terms of one class, and each refusal of its replay by name.
- `Analysis`, `Growth`, `Size`: the e-class analysis interface, whether a join grows its datum, and the size of the smallest term of a class.
- `Budget`, `Run`, `Outcome`, `Count`: the limits of a saturation, what it did and how it stopped.
- `EGraphError`: every refusal of the e-graph.

## Expected features

- The specification facade's `cfg(anodized_panic)` turns every `#[spec]` clause into a runtime check.

## Examples

```rust
use gandr_theory_coherent_resolutions::{Operation, TermTable};
use gandr_theory_e_graphs::EGraph;

// `a = b` joins `f(a)` and `f(b)` once the rebuild restores congruence.
let mut table = TermTable::default();
let a = table.op(Operation::from(0_usize), Vec::new()).unwrap();
let b = table.op(Operation::from(1_usize), Vec::new()).unwrap();
let fa = table.op(Operation::from(2_usize), vec![a]).unwrap();
let fb = table.op(Operation::from(2_usize), vec![b]).unwrap();
let mut graph = EGraph::new(table, ());
graph.add(fa).unwrap();
graph.add(fb).unwrap();
let equation = graph.equation(a, b).unwrap();
graph.apply(equation, Vec::new()).unwrap();
graph.rebuild().unwrap();
assert_eq!(graph.find(fa), graph.find(fb));
// The explanation replays against the table and the equations alone.
let explanation = graph.explain(fa, fb).unwrap();
assert!(explanation.replay(graph.table(), graph.equations(), (fa, fb)).is_ok());
```

```sh
mise exec -- cargo nextest run -p gandr-theory-e-graphs
```

## Where the detail lives

The classes, the union, the proof forest and the rebuild are in `src/egraph.rs`. The explanations and the check that replays them are in `src/egraph/explain.rs`. The phases of a saturation, and how a pattern finds its matches, are in `src/egraph/saturate.rs`. The analysis interface and `Size` are in `src/analysis.rs`.

## License

`Apache-2.0 WITH LLVM-exception`, the workspace licence, whose text is at the repository root.
