//! Finite distributions with exact weights: the measure of the algebra
//! family that holds probability.
//!
//! A distribution puts an exact positive weight on each point of a finite
//! support, and the weights sum to one. A weight is a [`Rational`] of the
//! sheaf crate, so a weight past the 128-bit integers is refused, never
//! rounded. The support is in one canonical order, so two distributions are
//! equal in distribution when their forms are equal.
//!
//! The crate gives the finite Giry monad: a point, a uniform choice, the
//! pushforward and the Kleisli extension. It also gives the product of two
//! distributions, the marginal of each component of a joint, the restriction
//! to an event, and the decision whether a joint is the product of its
//! marginals.
//!
//! # Items
//!
//! | Item | What it holds |
//! | ---- | ------------- |
//! | [`Distribution`] | a finite support in canonical order, each point with its exact weight, and the monad, the product and the restriction to an event |
//! | [`Independence`] | the verdict on a joint: independent, or the first pair whose weight is not the product of its marginal weights |
//! | [`ProbabilityError`] | every refusal: a weight past the integers, a set or an event with no weight, or weights that are not a distribution |
//!
//! # References
//!
//! - `Simpson-2026-equivalence_conditional_independence_atomic_sheaf_logic` —
//!   exemplar: Definitions 8.5 and 8.7 state equality in distribution as equal
//!   laws, and independence as a product of probabilities. § 10.1 names the
//!   finite probability spaces as a full subcategory. The crate decides both
//!   relations on finite supports. Alex Simpson, "Equivalence and Conditional
//!   Independence in Atomic Sheaf Logic", _Journal of the ACM_ 73(3), 2026,
//!   `doi:10.1145/3809163`.
//! - `Li-2024-nominal_approach_probabilistic_separation_logic` — background: §
//!   3 separates discrete state by the product of probability spaces, and
//!   Definition 3.5 asks of an independent combination that each pair weighs
//!   the product of its components. John M. Li, Jon Aytac, Philip
//!   Johnson-Freyd, Amal Ahmed and Steven Holtzen, "A Nominal Approach to
//!   Probabilistic Separation Logic", LICS 2024, `doi:10.1145/3661814.3662135`.
//! - `vault:01a1aa2d-a69c-7030-91e0-337d68d88151` — exemplar: the probability
//!   of the presented-spaces frame, where independence is the separation of
//!   supports that the nominal site states.
//!
//! [`Rational`]: gandr_theory_cellular_sheaves::Rational

#![no_std]

extern crate alloc;

mod distribution;
mod error;
mod joint;

pub use distribution::Distribution;
pub use error::ProbabilityError;
pub use joint::Independence;
