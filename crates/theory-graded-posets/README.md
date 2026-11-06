# gandr-theory-graded-posets

This crate holds finite graded posets for gandr: cells as data with a boundary and a rank, the lattice of subcomplexes, and its spectrum, which is the poset again. It is the first crate of the cell family, which presents a space by its cells and their faces.

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

**What.** A `GradedPoset` holds cells of the caller's type, such as the points of a face of a shape, and an order on them that the caller states. The cells below a cell are its boundary, and its `Rank` is the length of the longest chain below it. A subcomplex is a set of cells that holds the boundary of each of its cells. `GradedPoset::subcomplexes` gives the lattice of subcomplexes, and `GradedPoset::read_back` gives its spectrum with two monotone maps between the spectrum and the poset, which show that they are the same poset.

**Why.** A face formula reads the faces of a shape as sets of points, and the lattice those sets generate loses a face that is the union of smaller faces. As cells, the faces keep their identity: the join-irreducible subcomplexes are the closures of the cells, so the spectrum is the face poset again on every corpus shape. The cell family's later crates, discrete Morse theory and cellular sheaves, build on these posets.

**How.** The order is one row of words for each cell, the cell's closure, one bit for each cell. A poset of at most 64 cells keeps one word for each cell, and a wider poset keeps one word for each 64 cells in each row. The caller states the most cells it admits, and a poset with more is refused by its count before any order is computed. `GradedPoset::new` closes the pairs its caller states by Warshall's closure. `GradedPoset::by_inclusion` orders the cells by inclusion of the points each holds and compares no pair: a cell's row meets one row for each point it lacks. The subcomplexes are the down-sets of that order, which finite Stone duality enumerates under a `Budget` for a poset of at most 64 cells. The ranks take one pass over the cells by the size of their closure.

## References

- Clemens Berger and Mai Gehrke. "Stone duality for spectral sheaves and the patch monad". Journal of Pure and Applied Algebra, 2023, [doi:10.1016/j.jpaa.2022.107306](https://doi.org/10.1016/j.jpaa.2022.107306) — the duality that reads the lattice of subcomplexes back as the poset.
- `vault:01a1aa2d-a69c-7030-91e0-337d68d88151` — exemplar: the cell family of the presented-spaces frame.

## Provided features

- `CellRow`: a cell's closure or boundary, read off the order's words.
- `GradedPoset`: cells as data, their order as rows of words, each cell's closure, boundary and rank, and the lattice of subcomplexes.
- `Rank`: the length of the longest chain below a cell.
- `ReadBack`: the lattice of subcomplexes, its spectrum, and the monotone maps from the spectrum to the cells and back.

## Expected features

- The specification facade's `cfg(anodized_panic)` turns every `#[spec]` clause into a runtime check.

## Examples

```rust
use gandr_theory_graded_posets::GradedPoset;
use gandr_theory_stone_duality::{Budget, Comparison, ElementCount};

// The faces `{port}`, `{host, port}` and `{host, port, tls}` as masks.
let cells = vec![0b010_u64, 0b011, 0b111];
let poset = GradedPoset::new(cells, |lower, upper| {
    if lower & !upper == 0 { Comparison::Below } else { Comparison::NotBelow }
}, ElementCount::from(3_usize))
.unwrap();
let read = poset.read_back(Budget::from(8)).unwrap();
// A chain of three cells has four subcomplexes, and its spectrum is the chain.
assert_eq!(read.subcomplexes().members().len(), 4);
assert_eq!(read.spectrum().points().len(), 3);
```

```sh
mise exec -- cargo nextest run -p gandr-theory-graded-posets
```

## Where the detail lives

The graded poset, its ranks, its subcomplexes and the read-back are in `src/graded.rs`, and the order's rows are in `src/rows.rs`. The choice to read the subcomplexes through finite Stone duality is in `src/lib.rs`.

## License

`Apache-2.0 WITH LLVM-exception`, the workspace licence, whose text is at the repository root.
