//! Finite graded posets whose cells are data: the first crate of the cell
//! family, which presents a space by its cells and their faces.
//!
//! A cell carries data of the caller's type, such as the points of a face of
//! a shape. An order on that data says which cell lies below which. The cells
//! below a cell are its boundary, and the rank of a cell is the length of the
//! longest chain below it. A subcomplex holds the boundary of each of its
//! cells. The subcomplexes form a finite distributive lattice, and the
//! spectrum of that lattice is the poset again: its join-irreducible members
//! are the closures of the cells. The crate computes each of these, and two
//! monotone maps show that the spectrum is the poset.
//!
//! The order is one row of words for each cell, one word for each 64 cells.
//! Each caller states the most cells it admits. A poset with more cells is
//! refused by its count. An order by inclusion of points compares no pair.
//! The lattice of subcomplexes can grow to two to the number of cells, so its
//! enumeration takes a budget. Finite Stone duality enumerates it and reads
//! the spectrum, so those two hold at most 64 cells.
//!
//! The cells form the cell poset of a cellular sheaf, after Curry, Ghrist and
//! Nanda, and the caller orients their faces. Its results hold for oriented
//! graded posets of any dimension, the level of Kessler's thesis:
//! [`GradedPoset::traverse`] runs her traversal of a molecule, and
//! [`Traversal::key`] names it up to isomorphism. The crate keeps the closure
//! of the order, not her face data.
//!
//! # Items
//!
//! | Item | What it holds |
//! | ---- | ------------- |
//! | [`CellRow`] | a cell's closure or boundary, read off the order's words |
//! | [`Face`] | the side of a cell that a face one rank below it lies on |
//! | [`GradedPoset`] | the cells as data, their order as rows of words, their boundary and rank, and the lattice of subcomplexes |
//! | [`Key`] | a molecule's faces written as places in traversal order, rank by rank: equal exactly for isomorphic molecules |
//! | [`Place`] | a cell's place among the cells of its rank, in traversal order |
//! | [`Rank`] | the length of the longest chain below a cell |
//! | [`ReadBack`] | the lattice of subcomplexes, its spectrum, and the two maps between the spectrum and the poset |
//! | [`Traversal`] | the cells of a molecule in the order that Kessler's traversal marks them |
//! | [`TraversalError`] | why the traversal refuses a poset: the cell where a poset that is not a molecule stops it |
//!
//! # References
//!
//! - Clemens Berger and Mai Gehrke, "Stone duality for spectral sheaves and the
//!   patch monad", JPAA 2023, `doi:10.1016/j.jpaa.2022.107306` — background:
//!   the duality between finite distributive lattices and finite posets that
//!   reads the lattice of subcomplexes back as the poset.
//! - `vault:01a1aa2d-a69c-7030-91e0-337d68d88151` — exemplar: the cell family
//!   of the presented-spaces frame, a finite graded poset with its cells as
//!   data.
//! - Justin Curry, Robert Ghrist and Vidit Nanda. "Discrete Morse Theory for
//!   Computing Cellular Sheaf Cohomology." _Foundations of Computational
//!   Mathematics_ 16 (2016), 875–897. `arXiv:1312.6454` — the cell poset that a
//!   cellular sheaf lives on, each cell with its boundary and rank.
//! - Diana-Maria Kessler. _Computational Aspects of Rewriting in
//!   Higher-Dimensional Diagrams_. Doctoral thesis, Tallinn University of
//!   Technology (2025). `doi:10.23658/TALTECH.47/2025` — oriented graded
//!   posets, and the traversal that keys a molecule up to isomorphism in `O(n²
//!   log n)`, which [`GradedPoset::traverse`] computes. The thesis supersedes
//!   Amar Hadzihasanovic and Diana Kessler, "Data Structures for Topologically
//!   Sound Higher-Dimensional Diagram Rewriting", EPTCS 380 (2023),
//!   `doi:10.4204/EPTCS.380.7`.

#![no_std]

extern crate alloc;

mod graded;
mod rows;
mod traversal;

pub use graded::GradedPoset;
pub use graded::Rank;
pub use graded::ReadBack;
pub use rows::CellRow;
pub use traversal::Face;
pub use traversal::Key;
pub use traversal::Place;
pub use traversal::Traversal;
pub use traversal::TraversalError;
