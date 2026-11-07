# gandr-theory-discrete-morse

This crate holds discrete Morse theory on finite cell complexes for gandr: an acyclic matching that pairs cells with their faces, the check of a matching, the greedy matching, Brown's collapsing scheme with the critical cells that remain, and the reduct of a complex onto its critical cells. It is the crate of the cell family that collapses a space onto its critical cells.

The reduct keeps the homology alone. #5954 owes its equivalence up to homotopy type, after Doré's thesis, § 3.6.

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

**What.** A `Complex` gives the faces of a cell one dimension down, each with its `Incidence`, and says whether a cell lies in the complex. A `Scheme` is a complex that gives the `Class` of each cell: critical, redundant with its partner one dimension up, or collapsible with its partner one dimension down. `collapse` checks a scheme as an acyclic matching on the cells a caller gives, keeps the critical cells among them, and counts each fault in `Faults`. `greedy` builds an acyclic `Matching` on a finite complex, and `Matching::on` reads it as a scheme, so `collapse` checks it too. `reduct` builds the `Reduct` along an acyclic matching: the critical cells by rank and then by place, the Morse boundary of each over the integers, and the walk of its gradient. A `GradedPoset` is a complex whose faces are the cells one rank down.

**Why.** Completion's critical pairs are the critical cells of Brown's collapsing scheme on the bar complex of a rule block. The Euler characteristic of a face poset is the alternating count of the critical cells of an acyclic matching on it. One crate states the matching, its check and both ways to build one, so the probes and completion read one collapse.

**How.** A bar complex has more cells than a caller can list, so the check reads the given cells and walks the gradient from each redundant cell, past the given cells, up to a `Budget`. A walk past its budget is refused, never cut short. The greedy matching pairs a cell only when no path of the gradient runs back from the upper cell to the lower one, so the gradient stays acyclic by construction. The reduct orders the redundant cells that each critical cell's paths reach, each after every cell whose paths reach it, and then sums the weight that reaches each cell once. So a walk reads each partner's faces twice, and it follows no path twice.

## References

- `Doré-2023-computing_spaces_type_theory` — background: Maximilian Doré, "Computing Spaces in Type Theory", DPhil thesis, University of Oxford, 2023 — § 3.4, a matching as a function whose fixed points are the critical cells, and acyclicity as a gradient path to a critical cell.
- `Guiraud-2019-convergent_presentations_polygraphic_resolutions_associative_algebras` — background: Yves Guiraud, Eric Hoffbeck and Philippe Malbos, "Convergent Presentations and Polygraphic Resolutions of Associative Algebras", _Mathematische Zeitschrift_ 293, 2019, `doi:10.1007/s00209-018-2185-z` — a collapsing scheme that contracts the standard resolution onto the rules and the critical pairs.
- `Curry-2015-discrete_morse_theory_computing_cellular_sheaf_cohomology` — exemplar: Justin Curry, Robert Ghrist and Vidit Nanda, "Discrete Morse Theory for Computing Cellular Sheaf Cohomology", _Foundations of Computational Mathematics_ 16, 2016, `arXiv:1312.6454` — Definition 2.4 and Theorem 2.6, the reduction along a matching whose pairs are invertible, which keeps the cohomology.
- `vault:01a1aa2d-a69c-7030-91e0-337d68d88151` — exemplar: the collapse of the presented-spaces frame.

## Provided features

- `Complex`, `Incidence`, `Standing`, `Invertibility`: the caller's complex and the incidence of each face.
- `Scheme`, `Class`: a matching that gives the class of each cell.
- `collapse`, `Collapse`, `Faults`, `Budget`, `Count`: the check of a scheme on a set of cells, its critical cells and its faults.
- `greedy`, `Matching`, `Matched`: the greedy acyclic matching on a finite complex, and the matching read as a scheme.
- `reduct`, `Reduct`, `Place`: the reduct along an acyclic matching, its critical cells, the Morse boundary of each and the walk of its gradient.
- `MorseError`: every refusal, the caller's own fault, a walk past its budget, or a sum past the integers.

## Expected features

- The specification facade's `cfg(anodized_panic)` turns every `#[spec]` clause into a runtime check.

## Examples

```rust
use gandr_theory_discrete_morse::{Budget, Faults, collapse, greedy, reduct};
use gandr_theory_graded_posets::GradedPoset;
use gandr_theory_stone_duality::{Comparison, Element, ElementCount};

// Two points below one edge: the edge pairs with one point.
let poset = GradedPoset::new(vec!['p', 'q', 'e'], |lower, upper| {
    if *upper == 'e' && *lower != 'e' { Comparison::Below } else { Comparison::NotBelow }
}, ElementCount::from(3_usize))
.unwrap();
let cells: Vec<Element> = (0..3).map(Element::from).collect();
let mut complex = &poset;
let matching = greedy(&mut complex, &cells).unwrap();
assert_eq!(matching.critical().count(), 1);
let checked = collapse(&mut matching.on(&mut complex), &cells, Budget::from(3)).unwrap();
assert_eq!(checked.faults(), Faults::default());
// The reduct keeps the one critical point, with no boundary.
let reduced = reduct(&mut matching.on(&mut complex), &cells, Budget::from(3)).unwrap();
assert_eq!(reduced.cells().len(), 1);
```

```sh
mise exec -- cargo nextest run -p gandr-theory-discrete-morse
```

## Where the detail lives

The complex and the incidence are in `src/complex.rs`, the scheme and its check in `src/collapse.rs`, and the cycle search of a gradient in `src/gradient.rs`. The greedy matching is in `src/greedy.rs`, the graded poset as a complex in `src/poset.rs`, and the reduct with the order of its walks in `src/reduct.rs`.

## License

`Apache-2.0 WITH LLVM-exception`, the workspace licence, whose text is at the repository root.
