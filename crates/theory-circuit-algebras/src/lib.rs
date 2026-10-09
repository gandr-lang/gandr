//! The diagram view of gandr's circuit algebras: monogamous acyclic wirings
//! with interfaces, the spine reading of a command pattern, embedding-based
//! matching with its convexity check, and the diagram normal form.
//!
//! A [`Wiring`] is one diagram with an interface: [`Generator`]s (the
//! hyperedges, each a [`GeneratorLabel`] over ordered source and target
//! [`Wire`]s) and a discrete [`Interface`] of input and output ports. It is
//! built only by [`Wiring::assemble`], which refuses everything outside the
//! monogamous acyclic fragment — a fan-in, a fan-out, an out-of-range wire, a
//! repeated port, a produced input, a consumed output, an undeclared open wire
//! and a directed cycle — so every theorem the matcher and the canon quote has
//! its hypotheses as an invariant of the type. [`read_spine`] reads a sequent
//! command pattern as a wiring.
//!
//! [`embeddings`] finds every [`Embedding`] of a pattern wiring into a target
//! wiring by wire-driven propagation from one seed per pattern component, and
//! decides convexity by one of two computed routes: discharged for a strongly
//! connected pattern over the acyclic target, swept through the image's whole
//! complement otherwise. An [`Embedding`] is a certificate:
//! [`Embedding::check`] re-derives every conjunct it claims from the two
//! diagrams and refuses a forgery by the conjunct it fails.
//!
//! [`canonicalize`] renumbers a wiring into its [`CanonicalDiagram`], whose
//! equality is diagram identity rather than presentation identity, and returns
//! the [`Relabelling`] that [`Relabelling::verify`] checks against the input.
//! [`same_diagram`] decides whether two wirings denote one diagram, with both
//! relabellings on one arm and the located [`DiagramDivergence`] on the other.
//!
//! The crate is `no_std` and depends on `core`, `alloc`, the cell-shape
//! substrate `gandr-theory-cell-complexes` and the shape vocabulary of
//! `quenchant-shape`. No rewriting engine depends on it: a matcher reaches an
//! engine only where the engine is instantiated. The papers it draws on are in
//! its `README.md`, § References.

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

/// The wires of the given indices, in order: a fixture's port list.
#[cfg(test)]
macro_rules! wires {
    ($($index:literal),* $(,)?) => {
        [$(crate::interface::Wire::from($index)),*]
    };
}

/// The generators of the given positions, in order: a fixture's image.
#[cfg(test)]
macro_rules! edges {
    ($($index:literal),* $(,)?) => {
        [$(crate::interface::Edge::from($index)),*]
    };
}

mod interface;
mod matching;
mod normal_form;

pub use crate::interface::BijectionClash;
pub use crate::interface::ComponentCount;
pub use crate::interface::ComponentIndex;
pub use crate::interface::Components;
pub use crate::interface::Edge;
pub use crate::interface::EdgeCount;
pub use crate::interface::Generator;
pub use crate::interface::GeneratorLabel;
pub use crate::interface::GeneratorName;
pub use crate::interface::GeneratorSort;
pub use crate::interface::Interface;
pub use crate::interface::PairCount;
pub use crate::interface::PartialBijection;
pub use crate::interface::Seam;
pub use crate::interface::Wire;
pub use crate::interface::WireCount;
pub use crate::interface::Wiring;
pub use crate::interface::WiringObstruction;
pub use crate::interface::component_lookup;
pub use crate::interface::generator_lookup;
pub use crate::interface::spine::SpineObstruction;
pub use crate::interface::spine::SpineReading;
pub use crate::interface::spine::read_spine;
pub use crate::interface::spine::spine_port;
pub use crate::interface::wire_consumer;
pub use crate::interface::wire_image;
pub use crate::interface::wire_preimage;
pub use crate::interface::wire_producer;
pub use crate::matching::AdmittedIndex;
pub use crate::matching::Ambiguity;
pub use crate::matching::Connectivity;
pub use crate::matching::ConvexityRefusal;
pub use crate::matching::ConvexityWarrant;
pub use crate::matching::Discriminator;
pub use crate::matching::Divergence;
pub use crate::matching::Embedding;
pub use crate::matching::EmbeddingObstruction;
pub use crate::matching::MatchBudget;
pub use crate::matching::MatchCount;
pub use crate::matching::MatchObstruction;
pub use crate::matching::Matching;
pub use crate::matching::SeamHalf;
pub use crate::matching::SearchSteps;
pub use crate::matching::ambiguity;
pub use crate::matching::connectivity;
pub use crate::matching::convexity_warrant;
pub use crate::matching::embedding_image;
pub use crate::matching::embeddings;
pub use crate::matching::embeddings_by_sweep;
pub use crate::normal_form::CanonicalDiagram;
pub use crate::normal_form::Canonicalization;
pub use crate::normal_form::DiagramDivergence;
pub use crate::normal_form::DiagramEquality;
pub use crate::normal_form::Leg;
pub use crate::normal_form::PortCount;
pub use crate::normal_form::PortPosition;
pub use crate::normal_form::Relabelling;
pub use crate::normal_form::RelabellingDefect;
pub use crate::normal_form::SharedCanon;
pub use crate::normal_form::canonicalize;
pub use crate::normal_form::relabelled_generator;
pub use crate::normal_form::relabelled_wire;
pub use crate::normal_form::same_diagram;
