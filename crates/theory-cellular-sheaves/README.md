# gandr-theory-cellular-sheaves

This crate holds cellular sheaves over finite graded posets for gandr: a stalk on each cell, a restriction map from each cell to each cell above it, the gluing of sections over a cover, and cohomology over the rationals through a tower of levels. It is the second crate of the cell family, which presents a space by its cells and their faces.

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

**What.** A `Sheaf` holds a `GradedPoset`, a stalk width for each cell, and an entry map for each pair of a cell and a cell above it: for each entry of the upper stalk, the entry of the lower stalk that it reads. `Sheaf::glue` takes the sections of a cover and gives the glued section, or each pair of members whose restrictions differ, with the cell and the first entry where they differ. `Sheaf::cochains` gives the coboundaries over the rationals from an orientation, and `Tower` gives the cohomology of each level of a tower and the rank of the map each bonding map induces on it. `Sheaf::oriented` reads the poset as a complex over the integers for a Morse matching, and `Sheaf::reduce` reduces the cochains along a matching whose signed maps are invertible, onto the critical cells alone.

**Why.** A face cover splits a term over the faces of a shape, and two arms must agree where their faces overlap. That condition is the gluing condition of a sheaf over the faces and their meets. The cohomology of a space comes through the finite levels of its tower, each level a sheaf on a graded poset. One crate states both, so the shapes crate's face cover and the towers read one sheaf.

**How.** The maps compose, which `Sheaf::new` checks, so the gluing compares two sections only at the least cells above both. Each set of cells is one bit row of the graded poset, so a sheaf holds at most 64 cells. The coboundaries are exact matrices over the rationals, and their ranks come from Gauss–Jordan elimination. An entry past the 128-bit integers is refused, never rounded. A reduction checks each matched map before any walk. Then it sums the block that reaches each face once, in the order of the Morse crate's walk, so the reduced cochains keep the sheaf's cohomology.

## References

- `Ghrist-2022-cellular_sheaves_lattices_tarski_laplacian` — background: Robert Ghrist and Hans Riess, "Cellular Sheaves of Lattices and the Tarski Laplacian", _Homology, Homotopy and Applications_ 24, 2022, `doi:10.4310/HHA.2022.v24.n1.a16` — a cellular sheaf on a poset and its global sections.
- `Cherubini-2024-foundation_synthetic_stone_duality` — background: Felix Cherubini, Thierry Coquand, Freek Geerligs and Hugo Moeneclaey, "A Foundation for Synthetic Stone Duality", 2024, `arXiv:2412.03203` — cohomology through a tower of finite levels.
- `Curry-2015-discrete_morse_theory_computing_cellular_sheaf_cohomology` — exemplar: Justin Curry, Robert Ghrist and Vidit Nanda, "Discrete Morse Theory for Computing Cellular Sheaf Cohomology", _Foundations of Computational Mathematics_ 16, 2016, `arXiv:1312.6454` — a matching compatible with a sheaf, and the reduced cochains with the same cohomology.
- `Hansen-2020-laplacians_cellular_sheaves_theory_applications` — background: Jakob Hansen. "Laplacians of Cellular Sheaves: Theory and Applications". Doctoral thesis, University of Pennsylvania, 2020 — Theorem 1.6.1 and § 1.7, the cohomology as the kernel of the Hodge Laplacian, with an inner product on each stalk; the crate computes it by exact ranks over the rationals, with no inner product.
- `Ljungström-2025-computational_synthetic_cohomology_theory_homotopy_type_theory` — background: Axel Ljungström and Anders Mörtberg. "Computational Synthetic Cohomology Theory in Homotopy Type Theory". _Mathematical Structures in Computer Science_ 35, 2025, [doi:10.1017/S0960129525000131](https://doi.org/10.1017/S0960129525000131) — cohomology as maps into Eilenberg–MacLane spaces, with any coefficient group, computed in the type theory; the crate computes cellular cohomology outside the type theory, over the rationals alone.
- `vault:01a1aa2d-a69c-7030-91e0-337d68d88151` — exemplar: the cell family of the presented-spaces frame.

## Provided features

- `Sheaf`: the stalks and the entry maps over a graded poset, checked to compose.
- `Gluing`, `Section`, `Obstruction`: the verdict on the sections of a cover.
- `CochainComplex`, `Matrix`, `Cohomology`: the coboundaries over the rationals, their ranks and the cohomology by degree.
- `Tower`, `Image`: the levels of a tower, where each bonding map sends each cell, and the rank of each induced map.
- `Oriented`, `Reduced`: the poset as a complex over the integers for a matching, and the cochains reduced along it.
- `SheafError`: every refusal, by the cell, the degree or the level it concerns.

## Expected features

- The specification facade's `cfg(anodized_panic)` turns every `#[spec]` clause into a runtime check.

## Examples

```rust
use gandr_theory_cellular_sheaves::{Entry, Gluing, Sheaf, Width};
use gandr_theory_graded_posets::GradedPoset;
use gandr_theory_stone_duality::{Comparison, Element, ElementCount};

// Two points below one edge, the constant sheaf: one entry on each cell.
let poset = GradedPoset::new(vec!['p', 'q', 'e'], |lower, upper| {
    if *upper == 'e' && *lower != 'e' { Comparison::Below } else { Comparison::NotBelow }
}, ElementCount::from(3_usize))
.unwrap();
let sheaf = Sheaf::new(poset, |_| Width::from(1), |_, _| [Entry::from(0)]).unwrap();
let (p, q) = (Element::from(0), Element::from(1));
let agreeing: [(Element, &[u8]); 2] = [(p, &[7]), (q, &[7])];
assert!(matches!(sheaf.glue(&agreeing), Ok(Gluing::Glued(_))));
let parting: [(Element, &[u8]); 2] = [(p, &[7]), (q, &[8])];
assert!(matches!(sheaf.glue(&parting), Ok(Gluing::Obstructed(_))));
```

```sh
mise exec -- cargo nextest run -p gandr-theory-cellular-sheaves
```

## Where the detail lives

The sheaf and its gluing are in `src/sheaf.rs`, with the reason a site of opens reads its order reversed. The cochains and the cohomology are in `src/cochain.rs`, the exact matrices in `src/matrix.rs`, the tower in `src/tower.rs`, and the reduction along a matching in `src/reduce.rs`.

## License

`Apache-2.0 WITH LLVM-exception`, the workspace licence, whose text is at the repository root.
