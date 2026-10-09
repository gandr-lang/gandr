//! The second inhabitant of the cell-alphabet trait, and the adversaries built
//! over it: a test-facing crate that no production crate links.
//!
//! The workspace ships one production alphabet, so a measured property of an
//! engine generic over [`CellAlphabet`] would otherwise be a property of that
//! one alphabet rather than of the trait. [`ToyAlphabet`] is a first-order term
//! language — `Zero`, `Succ`, `Add` and metavariables — implementing the trait
//! from outside the substrate; its terms nest commands, so it is where two
//! applications in one term can be exercised at all.
//!
//! [`Lying`] is the toy alphabet in every answer but the ones an
//! [`AlphabetLie`] overrides: [`IncomparablePositions`] calls every position
//! pair disjoint, and [`NonLocalSplice`] disturbs a sibling of the position it
//! splices.
//!
//! The crate is `no_std` and depends on `alloc`, the substrate and
//! `quenchant-shape`. Its `README.md` carries the design and the references.
//!
//! [`CellAlphabet`]: gandr_theory_cell_complexes::CellAlphabet

#![no_std]

extern crate alloc;

mod adversarial;
mod toy;

pub use crate::adversarial::AlphabetLie;
pub use crate::adversarial::IncomparablePositions;
pub use crate::adversarial::Lying;
pub use crate::adversarial::NonLocalSplice;
pub use crate::adversarial::lying_cell;
pub use crate::toy::Toy;
pub use crate::toy::ToyAlphabet;
pub use crate::toy::ToyMeta;
pub use crate::toy::ToyOrient;
pub use crate::toy::ToyPos;
pub use crate::toy::ToyProv;
pub use crate::toy::ToySubst;
pub use crate::toy::ToyVar;
pub use crate::toy::toy_cell;
