//! Finite distributions with exact weights, and exact inference over a
//! factor graph: the measure of the algebra family that holds probability.
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
//! Exact inference reads a factor graph as a presented space: the variables
//! and the factors are cells, a factor's scope is its faces, and its weights
//! are its data. Sum-product over any ordered semiring is the measure, and
//! agreement on the separators of a junction tree is the gluing condition.
//! The probability semiring gives the marginals, and the max-times semiring
//! gives the most likely assignment.
//!
//! # Items
//!
//! | Item | What it holds |
//! | ---- | ------------- |
//! | [`Distribution`] | a finite support in canonical order, each point with its exact weight, and the monad, the product and the restriction to an event |
//! | [`Independence`] | the verdict on a joint: independent, or the first pair whose weight is not the product of its marginal weights |
//! | [`ProbabilityError`] | every refusal of a distribution: a weight past the integers, a set or an event with no weight, or weights that are not a distribution |
//! | [`Variable`], [`Arity`], [`Value`] | a variable by its number, the number of its values, and one value |
//! | [`Scope`], [`Table`] | variables in ascending order with their arities, and one weight for each assignment of them |
//! | [`FactorGraph`] | the arities of the variables and the factors over them |
//! | [`JunctionTree`], [`Calibrated`], [`Assignment`] | a tree of cliques with the running intersection property, the beliefs that sum-product gives, and the greatest assignment of them |
//! | [`Family`], [`Gluing`], [`Disagreement`], [`Possibility`] | local tables over a cover, the verdict on their gluing with the first entry where two differ, and the witness that no joint has them as marginals |
//! | [`Probability`], [`MaxTimes`] | the probability and the max-times semirings over the non-negative rationals |
//! | [`InferenceError`] | every refusal of inference: a scope, a table, a tree or an order that is not well formed, or a weight past the carrier |
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
mod factor;
mod glue;
mod joint;
mod junction;
mod semiring;
mod table;

pub use distribution::Distribution;
pub use error::InferenceError;
pub use error::ProbabilityError;
pub use factor::FactorGraph;
pub use glue::Disagreement;
pub use glue::Family;
pub use glue::Gluing;
pub use glue::Possibility;
pub use joint::Independence;
pub use junction::Assignment;
pub use junction::Calibrated;
pub use junction::JunctionTree;
pub use semiring::MaxTimes;
pub use semiring::Probability;
pub use table::Arity;
pub use table::Scope;
pub use table::Table;
pub use table::Value;
pub use table::Variable;
