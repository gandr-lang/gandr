//! Discrete Morse theory on finite cell complexes: the crate of the cell
//! family that collapses a space onto its critical cells.
//!
//! A matching pairs some cells of a complex, each with a face of it one
//! dimension down. The cells that no pair holds are the critical cells. The
//! incidence of the face in each pair must be one or minus one. The gradient
//! is the graph that runs down from each cell to its faces, and up along each
//! pair. A matching is acyclic when its gradient has no cycle. Then the
//! complex contracts onto a complex of its critical cells, so its homology is
//! the homology of the critical cells.
//!
//! The crate reads the caller's complex through [`Complex`], so a complex is
//! any set of cells that can give the faces of a cell. A [`Scheme`] gives the
//! class of each cell itself, as Brown's collapsing scheme does on a bar
//! complex. [`collapse()`] checks such a scheme on a set of cells and keeps
//! their critical cells. [`greedy()`] builds an acyclic matching on a finite
//! complex.
//!
//! # Items
//!
//! | Item | What it holds |
//! | ---- | ------------- |
//! | [`Complex`], [`Incidence`], [`Standing`], [`Invertibility`] | the caller's complex, the incidence of a face, and whether a cell lies in the complex |
//! | [`Scheme`], [`Class`] | a matching that gives the class of each cell, and the class: critical, or paired up or down |
//! | [`collapse()`], [`Collapse`], [`Faults`], [`Budget`], [`Count`] | the check of a scheme on a set of cells, its critical cells and its faults |
//! | [`greedy()`], [`Matching`], [`Matched`] | the greedy acyclic matching on a finite complex, and the matching read as a scheme |
//! | [`MorseError`] | every refusal: the caller's own fault, or a walk past its budget |
//!
//! A [`GradedPoset`] is a [`Complex`]: the faces of a cell are the cells of
//! its boundary one rank down, each with the incidence one.
//!
//! # References
//!
//! - `Doré-2023-computing_spaces_type_theory` — background: § 3.4 states a
//!   matching as a function whose fixed points are the critical cells, and its
//!   acyclicity as a gradient path from each cell to a critical cell.
//!   Maximilian Doré, "Computing Spaces in Type Theory", doctoral thesis,
//!   University of Oxford, 2023.
//! - `Guiraud-2019-convergent_presentations_polygraphic_resolutions_associative_algebras`
//!   — background: the introduction and § 5.3 contract the standard resolution
//!   of a convergent presentation onto its rules, critical pairs and critical
//!   triples by a collapsing scheme. Yves Guiraud, Eric Hoffbeck and Philippe
//!   Malbos, "Convergent Presentations and Polygraphic Resolutions of
//!   Associative Algebras", _Mathematische Zeitschrift_ 293, 2019,
//!   `doi:10.1007/s00209-018-2185-z`.
//! - `vault:01a1aa2d-a69c-7030-91e0-337d68d88151` — exemplar: the collapse of
//!   the presented-spaces frame, which keeps the critical cells and the pairing
//!   of the cells that cancel.
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

mod collapse;
mod complex;
mod error;
mod gradient;
mod greedy;
mod poset;

pub use collapse::Budget;
pub use collapse::Class;
pub use collapse::Collapse;
pub use collapse::Count;
pub use collapse::Faults;
pub use collapse::Scheme;
pub use collapse::collapse;
pub use complex::Complex;
pub use complex::Incidence;
pub use complex::Invertibility;
pub use complex::Standing;
pub use error::MorseError;
pub use greedy::Matched;
pub use greedy::Matching;
pub use greedy::greedy;
