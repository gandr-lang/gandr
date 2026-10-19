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
//! `quenchant-shape`.
//!
//! # Example
//!
//! Decide that two presentations denote one diagram and check the evidence.
//!
//! ```rust
//! use gandr_theory_circuit_algebras::DiagramEquality;
//! use gandr_theory_circuit_algebras::Generator;
//! use gandr_theory_circuit_algebras::GeneratorLabel;
//! use gandr_theory_circuit_algebras::GeneratorSort;
//! use gandr_theory_circuit_algebras::Interface;
//! use gandr_theory_circuit_algebras::Wire;
//! use gandr_theory_circuit_algebras::WireCount;
//! use gandr_theory_circuit_algebras::Wiring;
//! use gandr_theory_circuit_algebras::canonicalize;
//! use gandr_theory_circuit_algebras::same_diagram;
//!
//! fn example() -> Result<(), Box<dyn core::error::Error>>
//! {
//!     let value = |name: &str| GeneratorLabel::new(name, GeneratorSort::Value);
//!     let wires =
//!         |indices: &[usize]| -> Vec<Wire> { indices.iter().copied().map(Wire::from).collect() };
//!     // f: (0) -> (1), then g: (1) -> (2)
//!     let left = Wiring::assemble(
//!         WireCount::from(3),
//!         vec![
//!             Generator::new(value("f"), wires(&[0]), wires(&[1])),
//!             Generator::new(value("g"), wires(&[1]), wires(&[2])),
//!         ],
//!         Interface::new(wires(&[0]), wires(&[2])),
//!     )?;
//!     // The same composite, its wires renumbered and its generators relisted.
//!     let right = Wiring::assemble(
//!         WireCount::from(3),
//!         vec![
//!             Generator::new(value("g"), wires(&[0]), wires(&[1])),
//!             Generator::new(value("f"), wires(&[2]), wires(&[0])),
//!         ],
//!         Interface::new(wires(&[2]), wires(&[1])),
//!     )?;
//!     let DiagramEquality::Same(shared) = same_diagram(&left, &right)
//!     else {
//!         return Err("two presentations of one diagram".into());
//!     };
//!     assert_eq!(Ok(()), shared.left().verify(&left, shared.form()));
//!     assert_eq!(Ok(()), shared.right().verify(&right, shared.form()));
//!     assert_eq!(shared.form(), canonicalize(&left).form());
//!     Ok(())
//! }
//! ```
//!
//! # Crate boundary
//!
//! No rewriting engine depends on this crate. A matcher reaches an engine only
//! through a seam supplied where the engine is instantiated, so the engines
//! stay generic over the cell alphabet and this crate stays a leaf above the
//! substrate.
//!
//! The crate takes no edge to `gandr-theory-graphs`. It needs weakly connected
//! components for its seeds and the component partition, and port-ordered
//! traversal; that crate's algorithms read port-blind successor rows and do not
//! offer components.
//!
//! - **Alternatives.** Adding a components procedure to `gandr-theory-graphs`
//!   with this crate as its one reader spreads one unit across two crates and
//!   still leaves port order here; taking the edge for cycle evidence alone
//!   puts a graph library under the substrate's path for one call.
//! - **Reversal.** `gandr-theory-graphs` gains a components procedure for a
//!   second reader, or a later alphabet needs a wiring's condensation.
//!
//! # Specification attributes
//!
//! Nontrivial operations carry executable `#[spec]` predicates beside their `#
//! Adequacy` witnesses. The predicates cover state transitions, certificate
//! correspondence and refusal payloads without repeating allocating graph
//! searches. Reachability, convexity and presentation invariance additionally
//! rely on the named fixture and differential witnesses. The opaque port-image
//! iterator and generated-presentation strategy carry reasoned backend
//! exemptions.
//!
//! # References
//!
//! - Filippo Bonchi, Fabio Gadducci, Aleks Kissinger, Paweł Sobociński, and
//!   Fabio Zanasi. "String Diagram Rewrite Theory II: Rewriting with Symmetric
//!   Monoidal Structure." _Mathematical Structures in Computer Science_ 32, 4
//!   (2022), pages 511–541. `doi:10.1017/S0960129522000317`; preprint
//!   `arXiv:2104.14686` — monogamous acyclic hypergraphs with interfaces as the
//!   representation of symmetric monoidal string diagrams, convex matching,
//!   left-connectedness, and the example of two disjoint matches that interfere
//!   through a path outside both, which the blocking-shape test pins.
//! - Paweł Sobociński, Paul W. Wilson, and Fabio Zanasi. "CARTOGRAPHER: A Tool
//!   for String Diagrammatic Reasoning (Tool Paper)." In _8th Conference on
//!   Algebra and Coalgebra in Computer Science (CALCO 2019)_, `LIPIcs` 139,
//!   pages 20:1–20:7, 2019. `doi:10.4230/LIPIcs.CALCO.2019.20` — diagrams as
//!   hypergraph cospans with ordered ports, matched and rewritten under
//!   convexity, the representation `Wiring` reads.
//! - Piergiulio Katis, Nicoletta Sabadini, and Robert F. C. Walters. "Feedback,
//!   Trace and Fixed-Point Semantics." _RAIRO – Theoretical Informatics and
//!   Applications_ 36, 2 (2002). `doi:10.1051/ita:2002009` — feedback as a
//!   primitive distinct from trace, the ground for cutting a delayed back-edge
//!   open rather than reading the closed loop.
//! - Pierre-Louis Curien and Hugo Herbelin. "The Duality of Computation." In
//!   _Proceedings of the Fifth ACM SIGPLAN International Conference on
//!   Functional Programming (ICFP '00)_, pages 233–243, September 2000.
//!   `doi:10.1145/351240.351262` — the command `⟨p | c⟩` of a producer against
//!   a consumer that the spine reading lays out as a diagram.
//! - Jovana Obradović. "Cyclic operads: syntactic, algebraic and categorified
//!   aspects." Doctoral thesis, Université Paris Diderot – Paris 7 – Sorbonne
//!   Paris Cité, 2017. `hal:tel-01676983` — the corolla and edge
//!   decompositions, the two extremes the canon's edge orientation is chosen
//!   between.
//! - Antonin Delpeuch and Jamie Vicary. "Normalization for Planar String
//!   Diagrams and a Quadratic Equivalence Algorithm." _Logical Methods in
//!   Computer Science_ 18, 1 (2022), paper 10.
//!   `doi:10.46298/lmcs-18(1:10)2022`; preprint `arXiv:1804.07832` — the planar
//!   quotient, up to exchange moves, that does not stand in for the symmetric
//!   one the canon decides.
//! - Shahn Majid and Konstanze Rietsch. "Planar Spider Theorem and Asymmetric
//!   Frobenius Algebras." Preprint, 2021. `arXiv:2109.12106` — the spider
//!   normal form for diagrams whose wires merge, outside the monogamous
//!   fragment and not built here.

// Module documentation that predates the shape lint: 33 headings outside the
// vocabulary, 5 decision records and 6 budgets exceeded. Each allow leaves with
// the rewrite that clears its count.
#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    allow(
        module_doc_heading,
        doc_decision_record,
        module_doc_budget,
        reason = "module documentation that predates the shape lint"
    )
)]
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
