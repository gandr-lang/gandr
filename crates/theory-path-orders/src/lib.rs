//! Path orders over the terms of second-order algebraic theories: the data an
//! ordering reads, as traits a caller implements over its own terms, and each
//! ordering an algorithm module generic over them, returning one evidence
//! type a checker replays.
//!
//! A caller presents each side of a comparison as positioned nodes
//! ([`Term`]), each node one of five formers — a signature symbol applied to
//! arguments, a rule variable bare or instantiated, an abstraction of one name,
//! an occurrence of a bound name — and a left side's variables by whether they
//! are values ([`Valued`]). It states the precedence as data: each symbol's
//! place and status ([`Precedence`]). An ordering decides whether the left
//! side stands above the right and, when it does, returns [`Evidence`]: the
//! derivation of the comparison, one step per pair of subterms, each naming
//! the clause that orients it. Its checker replays a derivation without
//! search, whoever built it.
//!
//! The crate is `no_std` over `core` and `alloc` and depends on no other
//! workspace crate.
//!
//! # Items
//!
//! - [`term`]: the term view, [`Term`], [`Valued`], [`Former`], [`Node`].
//! - [`precedence`]: the precedence as data, [`Precedence`], [`Place`],
//!   [`Rank`], [`Status`].
//! - [`evidence`]: the evidence, [`Evidence`], [`Derivation`], [`Step`],
//!   [`Clause`], [`Cover`].
//! - [`lpo`]: the lexicographic path order with status, read at an
//!   instantiation as the computability path order reads a variable applied to
//!   terms; [`lpo::orient`] and [`lpo::check`].
//!
//! # References
//!
//! The papers the crate draws on are in its `README.md`, § References, and
//! each ordering's module names the definitions it implements.

#![no_std]

extern crate alloc;

pub mod evidence;
pub mod lpo;
pub mod precedence;
pub mod term;

pub use crate::evidence::Argument;
pub use crate::evidence::Clause;
pub use crate::evidence::Cover;
pub use crate::evidence::CoverIndex;
pub use crate::evidence::Derivation;
pub use crate::evidence::Evidence;
pub use crate::evidence::Relation;
pub use crate::evidence::Step;
pub use crate::precedence::Place;
pub use crate::precedence::Precedence;
pub use crate::precedence::Rank;
pub use crate::precedence::Status;
pub use crate::term::Former;
pub use crate::term::Node;
pub use crate::term::Term;
pub use crate::term::Valuation;
pub use crate::term::Valued;
