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
//! pair disjoint, [`NonLocalSplice`] disturbs a sibling of the position it
//! splices, [`WithheldConvexity`] withholds the convexity warrant, and
//! [`CollidingAddresses`] hashes every orientation tag ([`LyingOrient`]) to
//! nothing.
//!
//! The crate is `no_std` and depends on `alloc`, the substrate and
//! `quenchant-shape`. Its `README.md` carries the design and the references.
//!
//! # Test-only by construction
//!
//! This crate is reached through `[dev-dependencies]` only. Cargo cannot say so
//! — the crate depends on the substrate alone, so a production crate depending
//! on it closes no cycle — so
//! `tests::workspace::no_production_crate_links_the_tools_crate` asks the
//! resolver: `cargo tree --invert` over normal and build edges, from this
//! crate, lists no other package. The alternative, a `test-support` feature on
//! the substrate carrying the toy, loses: it puts the toy in the substrate's
//! published surface, and feature unification lets any production build that
//! enables it link the adversaries. The decision reverses if a second alphabet
//! outside the tests needs the toy's term language as a real one; that alphabet
//! is then a crate of its own, not a feature.
//!
//! The crate is `no_std` and depends on `alloc`, the substrate and
//! `quenchant-shape`; the workspace witness alone uses `std`, to run `cargo`.
//!
//! # References
//!
//! - Franz Baader and Tobias Nipkow. _Term Rewriting and All That_. Cambridge
//!   University Press, 1998. `doi:10.1017/CBO9781139172752` — first-order
//!   terms, positions and their prefix order, matching and syntactic
//!   unification with the occurs check, and the critical-pair lemma, whose case
//!   of rewrites at disjoint positions is what `IncomparablePositions` and
//!   `NonLocalSplice` each falsify from a different side.
//!
//! [`CellAlphabet`]: gandr_theory_cell_complexes::CellAlphabet

#![no_std]

extern crate alloc;

mod adversarial;
mod toy;

pub use crate::adversarial::AlphabetLie;
pub use crate::adversarial::CollidingAddresses;
pub use crate::adversarial::IncomparablePositions;
pub use crate::adversarial::Lying;
pub use crate::adversarial::LyingOrient;
pub use crate::adversarial::NonLocalSplice;
pub use crate::adversarial::WithheldConvexity;
pub use crate::adversarial::lying_cell;
pub use crate::adversarial::reoriented_lying_cell;
pub use crate::toy::Toy;
pub use crate::toy::ToyAlphabet;
pub use crate::toy::ToyMeta;
pub use crate::toy::ToyOrient;
pub use crate::toy::ToyPos;
pub use crate::toy::ToyProv;
pub use crate::toy::ToySubst;
pub use crate::toy::ToyVar;
pub use crate::toy::toy_cell;
