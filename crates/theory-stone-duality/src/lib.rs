//! The finite case of Stone duality: a space read as the algebra of its
//! observations, and the algebra read back as the space.
//!
//! A finite poset and the distributive lattice of its down-sets describe one
//! space twice. The poset is the spectrum of the lattice. Its elements are
//! the join-irreducible members of the lattice, ordered by inclusion. A
//! monotone map between two posets is a lattice homomorphism between their
//! lattices, in the other direction. The crate computes each side from the
//! other and checks that both round trips are identities.
//!
//! The free distributive lattice on `n` generators is the one case a consumer
//! writes most. Its elements are polynomials in the generators, each in a
//! normal form: an antichain of terms, a term the meet of a set of
//! generators. Its spectrum is the cube on `n` axes, and a polynomial reads as
//! a monotone truth table on the cube.
//!
//! Every set is one machine word. A term is a set of at most 64 generators,
//! and a finite poset or lattice of sets has at most 64 elements or points.
//! An enumeration that can grow past its input takes a budget, and it refuses
//! the input when the count passes the budget.
//!
//! # Items
//!
//! | Item | What it holds |
//! | ---- | ------------- |
//! | [`Term`], [`Polynomial`] | the free distributive lattice in normal form: meet, join, order and evaluation at a vertex |
//! | [`Homomorphism`] | a homomorphism of free distributive lattices: the polynomial each generator goes to, and substitution |
//! | [`Vertex`], [`Table`], [`CubeMap`] | the cube as the spectrum of the free lattice: truth tables and monotone maps of cubes |
//! | [`ElementSet`], [`FinitePoset`] | a finite poset with its principal down-sets, and the enumeration of its down-sets |
//! | [`SetRing`], [`Spectrum`] | a finite distributive lattice of sets, its join-irreducible members and its representation by down-sets |
//! | [`MonotoneMap`] | a monotone map of finite posets, its preimage homomorphism, and the map read back from it |
//! | [`DualityError`] | every refusal, by the index it concerns |
//!
//! # References
//!
//! - Clemens Berger and Mai Gehrke, "Stone duality for spectral sheaves and the
//!   patch monad", JPAA 2023, `doi:10.1016/j.jpaa.2022.107306` — Stone duality
//!   between spectral spaces and bounded distributive lattices, which this
//!   crate states for finite posets.
//! - `vault:01a1aa2d-a69c-7030-91e0-337d68d88151` — exemplar: a space presented
//!   by its points and again by its algebra of observations.

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

/// The set bits of a word, lowest first, each read as `$wrap` of its index.
macro_rules! ones {
    ($word:expr, $wrap:expr) => {{
        let mut rest: u64 = $word;
        core::iter::from_fn(move || {
            if rest == 0 {
                return None;
            }
            let lowest = rest.trailing_zeros();
            rest &= !(1_u64.checked_shl(lowest).unwrap_or(0));
            usize::try_from(lowest).map_or(None, |index| Some($wrap(index)))
        })
    }};
}

mod error;
mod finite;
mod free;
mod index;

pub use error::DualityError;
pub use finite::ElementSet;
pub use finite::FinitePoset;
pub use finite::MonotoneMap;
pub use finite::SetRing;
pub use finite::Spectrum;
pub use free::CubeMap;
pub use free::Homomorphism;
pub use free::Polynomial;
pub use free::Table;
pub use free::Term;
pub use free::Vertex;
pub use index::Budget;
pub use index::Comparison;
pub use index::Element;
pub use index::ElementCount;
pub use index::Generator;
pub use index::GeneratorCount;
pub use index::Membership;
pub use index::WIDEST;
pub use index::WIDEST_CUBE;
