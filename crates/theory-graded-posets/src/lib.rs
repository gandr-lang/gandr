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
//! The order is one bit row for each cell, so a poset holds at most 64 cells,
//! the bits of one machine word. A poset with more cells is refused by its
//! count before any order is computed. The lattice of subcomplexes can grow
//! to two to the number of cells, so its enumeration takes a budget and
//! refuses the poset past it.
//!
//! Finite Stone duality holds the bit rows, enumerates the down-sets and reads
//! the spectrum, so this crate adds no second enumeration over the same words
//! and uses that crate's types. A poset past one machine word would need sets
//! wider than that crate holds.
//!
//! # Items
//!
//! | Item | What it holds |
//! | ---- | ------------- |
//! | [`GradedPoset`] | the cells as data, their order as bit rows, their boundary and rank, and the lattice of subcomplexes |
//! | [`Rank`] | the length of the longest chain below a cell |
//! | [`ReadBack`] | the lattice of subcomplexes, its spectrum, and the two maps between the spectrum and the poset |
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

#![no_std]

extern crate alloc;

mod graded;

pub use graded::GradedPoset;
pub use graded::Rank;
pub use graded::ReadBack;
