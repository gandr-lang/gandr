//! A proof-producing e-graph over the term table of a Lawvere theory: the
//! crate of the rewriting family that closes equations under congruence and
//! explains each equality that it finds.
//!
//! Congruence closure is ground completion, so an e-graph is a convergent
//! ground rewriting system, and its explanations are certificates that
//! completion replays. The nodes of an [`EGraph`] are the places of a
//! [`TermTable`], which holds each distinct term once, so the e-graph adds no
//! second table. It adds a union-find, a cycle through the members of each
//! class, the parents of each class and a proof forest. Each union keeps its
//! [`Reason`]: an input [`Equation`] at an instance, or a congruence.
//! [`EGraph::explain`] gives an [`Explanation`], and [`Explanation::replay`]
//! checks it against the table and the equations alone. The e-graph is
//! untrusted, and the replay is the check.
//!
//! A union puts its class on a worklist, and [`EGraph::rebuild`] repairs each
//! class once (egg, § 3). An [`Analysis`] keeps on each class the join of its
//! nodes' data (egg, § 4.1). [`EGraph::saturate`] reads every match, then
//! applies each match, then rebuilds (egg, § 3.3), so the order of the
//! equations does not change the classes. A union inside one class is kept
//! as a [`Redundant`] union with its reason: these are the loops that a
//! coherent e-graph reads.
//!
//! # Items
//!
//! | Item | What it holds |
//! | ---- | ------------- |
//! | [`EGraph`], [`Joined`], [`Tally`], [`Members`], [`Classes`] | the e-graph over a term table, whether a union merges two classes, its counts, and the members of a class and the classes |
//! | [`Equation`], [`EquationPlace`], [`Reason`], [`Direction`], [`Redundant`] | an input equation and its place, the reason of a union, the side of an equation that a step starts from, and a union inside one class |
//! | [`Explanation`], [`Proof`], [`Step`], [`StepReason`], [`ProofPlace`], [`StepPlace`], [`Position`], [`Refusal`] | the chain of reasons between two terms of one class, each refusal of its replay by name |
//! | [`Analysis`], [`Growth`], [`Size`] | the e-class analysis interface, whether a join grows its datum, and the size of the smallest term that a class represents |
//! | [`Budget`], [`Run`], [`Outcome`], [`Count`] | the limits of a saturation, what it did and how it stopped |
//! | [`EGraphError`] | every refusal: a place outside the table or the e-graph, two classes apart, or an equation that does not match |
//!
//! # References
//!
//! - `Willsey-2021-egg_fast_extensible_equality_saturation` — exemplar: § 3.1,
//!   a merge that only puts the class on a worklist, and a rebuild that
//!   deduplicates the worklist and repairs each class once; § 3.3, the read and
//!   write phases, which make the rewrites unordered; § 4.1, the analysis
//!   interface, a join-semilattice and the invariant that each class holds the
//!   join of its nodes' data with `modify` at a fixed point. Max Willsey,
//!   Chandrakana Nandi, Yisu Remy Wang, Oliver Flatt, Zachary Tatlock and Pavel
//!   Panchekha, "egg: Fast and Extensible Equality Saturation", _Proc. ACM
//!   Program. Lang._ 5 (POPL), 2021, `doi:10.1145/3434304`.
//! - `vault:01a1aa2d-a69c-7030-91e0-337d68d88151` — exemplar: §
//!   presented-spaces-egraphs, an e-graph as ground completion with its loops,
//!   and the four units of the rewriting ladder's rung 3 that this crate
//!   starts.
//! - `vault:01a178aa-4f9c-7221-a972-619f184e507e` — exemplar: the adoption
//!   programme takes egg's three mechanisms as specifications, so the crate
//!   builds the rebuild, the analysis and the phases, and no egg engine.
//! - `vault:01a178aa-f8ad-73d0-bbe7-c395c922e4f9` — exemplar: rung 3 of the
//!   rewriting ladder puts the congruence layer over the existing arena, so the
//!   nodes are the places of a `TermTable` and the crate adds no table.
//!
//! [`TermTable`]: gandr_theory_coherent_resolutions::TermTable

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

mod analysis;
mod egraph;
mod error;

pub use analysis::Analysis;
pub use analysis::Growth;
pub use analysis::Size;
pub use egraph::Budget;
pub use egraph::Classes;
pub use egraph::Count;
pub use egraph::Direction;
pub use egraph::EGraph;
pub use egraph::Equation;
pub use egraph::EquationPlace;
pub use egraph::Explanation;
pub use egraph::Joined;
pub use egraph::Members;
pub use egraph::Outcome;
pub use egraph::Position;
pub use egraph::Proof;
pub use egraph::ProofPlace;
pub use egraph::Reason;
pub use egraph::Redundant;
pub use egraph::Refusal;
pub use egraph::Run;
pub use egraph::Step;
pub use egraph::StepPlace;
pub use egraph::StepReason;
pub use egraph::Tally;
pub use error::EGraphError;
