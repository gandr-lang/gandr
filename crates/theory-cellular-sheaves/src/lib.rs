//! Cellular sheaves over finite graded posets: the second crate of the cell
//! family, which presents a space by its cells and their faces.
//!
//! A cellular sheaf puts a stalk on each cell of a graded poset and an entry
//! map on each pair of a cell and a cell above it: for each entry of the upper
//! stalk, the entry of the lower stalk that it reads. The maps compose.
//! Sections on the cells of a cover glue when, at each cell above two of them,
//! their restrictions agree. The crate decides this, and it names the cell and
//! the first entry where two sections differ.
//!
//! The crate also computes cohomology over the rationals. The coboundary from
//! degree `d` sends the sections on the cells of rank `d` to rank `d + 1`
//! through the same maps, each with the sign that an orientation gives. A
//! tower is a sequence of levels, each a sheaf, with a bonding map from each
//! level to the one before it. The crate gives each level's cohomology and the
//! rank of the map that each bonding map induces on it. A sheaf also reduces
//! along a matching whose maps are invertible, onto cochains on its critical
//! cells alone, with the same cohomology.
//!
//! The cells and their order are a [`GradedPoset`]. A sheaf holds each set of
//! cells as one bit row, so it refuses a poset of more than 64 cells.
//!
//! # Items
//!
//! | Item | What it holds |
//! | ---- | ------------- |
//! | [`Sheaf`] | the poset, a stalk width for each cell, and an entry map for each pair of a cell and a cell above it |
//! | [`Gluing`], [`Section`], [`Obstruction`], [`Agreement`] | the verdict on the sections of a cover, the glued section or each pair that differs, and the verdict on one pair |
//! | [`CochainComplex`], [`Matrix`], [`Cohomology`] | the coboundaries over the rationals, their ranks and the cohomology by degree |
//! | [`Rational`], [`Integer`] | an exact rational in lowest terms over 128-bit integers, which `theory-probability` also takes as a weight, and its parts |
//! | [`Tower`], [`Image`] | the levels of a tower, where each bonding map sends each cell, and the rank of the map it induces on cohomology |
//! | [`Oriented`], [`Reduced`] | the poset as a complex over the integers for a matching, and the cochains reduced along it |
//! | [`Entry`], [`Width`], [`Dimension`], [`CoverIndex`], [`Level`], [`Incidence`] | the names of an entry, a width, a dimension, a cover member, a level and an incidence |
//! | [`SheafError`] | every refusal, by the cell or the degree it concerns |
//!
//! # References
//!
//! - `Ghrist-2022-cellular_sheaves_lattices_tarski_laplacian` — background: a
//!   cellular sheaf on a poset, with a restriction map from each cell to each
//!   cell above it, and its global sections as the sections that agree on each
//!   relation. Robert Ghrist and Hans Riess, "Cellular Sheaves of Lattices and
//!   the Tarski Laplacian", _Homology, Homotopy and Applications_ 24, 2022,
//!   `doi:10.4310/HHA.2022.v24.n1.a16`.
//! - `Cherubini-2024-foundation_synthetic_stone_duality` — background: Felix
//!   Cherubini, Thierry Coquand, Freek Geerligs and Hugo Moeneclaey, "A
//!   Foundation for Synthetic Stone Duality", 2024, `arXiv:2412.03203` — § 6,
//!   the cohomology of a compact Hausdorff space through a tower of finite
//!   levels, the interval and the circle among them.
//! - `Hansen-2020-laplacians_cellular_sheaves_theory_applications` —
//!   background: Theorem 1.6.1 and § 1.7 read the cohomology off the kernel of
//!   the Hodge Laplacian, with an inner product on each stalk. The crate
//!   computes the cohomology of each degree by exact ranks over the rationals,
//!   with no inner product. Jakob Hansen, "Laplacians of Cellular Sheaves:
//!   Theory and Applications", doctoral thesis, University of Pennsylvania,
//!   2020.
//! - `Ljungström-2025-computational_synthetic_cohomology_theory_homotopy_type_theory`
//!   — background: cohomology as maps into Eilenberg–MacLane spaces, with any
//!   coefficient group, and computed in the type theory itself. The crate
//!   computes cellular cohomology outside the type theory, over the rationals
//!   alone. Axel Ljungström and Anders Mörtberg, "Computational Synthetic
//!   Cohomology Theory in Homotopy Type Theory", _Mathematical Structures in
//!   Computer Science_ 35, 2025, `doi:10.1017/S0960129525000131`.
//! - `vault:01a1aa2d-a69c-7030-91e0-337d68d88151` — exemplar: the cell family
//!   of the presented-spaces frame, a sheaf over a finite graded poset.
//!
//! [`GradedPoset`]: gandr_theory_graded_posets::GradedPoset

#![no_std]

extern crate alloc;

/// Defines a transparent newtype over one primitive with `From` conversions
/// both ways.
macro_rules! wrapper {
    ($(#[$meta:meta])* $vis:vis struct $name:ident($raw:ty);) => {
        $(#[$meta])*
        #[repr(transparent)]
        $vis struct $name($raw);

        impl From<$raw> for $name
        {
            /// Wraps the primitive.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            fn from(value: $raw) -> Self
            {
                Self(value)
            }
        }

        impl From<$name> for $raw
        {
            /// Unwraps the primitive.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            fn from(value: $name) -> Self
            {
                value.0
            }
        }
    };
}

mod cochain;
mod error;
mod index;
mod matrix;
mod reduce;
mod sheaf;
mod tower;

pub use cochain::CochainComplex;
pub use cochain::Cohomology;
pub use error::SheafError;
pub use index::CoverIndex;
pub use index::Dimension;
pub use index::Entry;
pub use index::Incidence;
pub use index::Integer;
pub use index::Level;
pub use index::Width;
pub use matrix::Matrix;
pub use matrix::Rational;
pub use reduce::Oriented;
pub use reduce::Reduced;
pub use sheaf::Agreement;
pub use sheaf::Gluing;
pub use sheaf::Obstruction;
pub use sheaf::Section;
pub use sheaf::Sheaf;
pub use tower::Image;
pub use tower::Tower;
