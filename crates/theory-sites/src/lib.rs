//! The carrier's shapes as a site with stick-free objects: a morphism class
//! over the wirings `gandr-theory-circuit-algebras` admits, its degree, and
//! the finite checks of its generalized Reedy structure.
//!
//! A circuit algebra has two units: the identity wire, a bare wire from an
//! input port to an output port with no operation on it, is the unit of
//! contraction; the empty diagram is the unit of the external product. The
//! site keeps the second and drops the first: **a stick is not a shape**.
//!
//! # Objects
//!
//! A [`Shape`] is the graph a carrier [`Wiring`] presents. Each generator is a
//! vertex; each wire records its producer and its consumer, either a vertex or
//! an open end. A wire open at one end is a leg, attached at both inner, and
//! open at both a stick, which the constructors refuse with
//! `ShapeObstruction::Stick` naming the wire; a vertex with no incident wire is
//! a point. A wire with no operation on it may run between two vertices of a
//! shape; alone, it is never an object. Generator labels, the order of a
//! generator's ports and the order of the interface are forgotten: they are
//! what an element of a presheaf carries, as the corolla's symmetric-group
//! action does in the published graphical categories. Two shapes are one object
//! when a bijection of vertices carries one multiset of wire ends onto the
//! other. The empty shape `∅` and the point `•`, one vertex with no ports, are
//! objects; so is every disconnected shape without a stick.
//!
//! Forgetting the port order is a choice. The alternative keeps it, which makes
//! every corolla rigid and the site a category over the signature's arities; it
//! is the reading to take if a presheaf on the site must tell two orders of one
//! generator's inputs apart, which the carrier's normal form does not.
//!
//! The record of why the objects are stick-free is four tests on raw wirings,
//! read as graphs before admission so that a bare wire can stand as an object:
//! `negatives::sticks_as_objects_admit_no_degree`,
//! `negatives::connected_objects_lose_the_point_deletion`,
//! `negatives::vertex_end_fusions_are_not_closed` and
//! `negatives::contraction_lowering_loses_the_factorization`. Each asserts the
//! one fact that rules its alternative out.
//!
//! # Maps
//!
//! A [`SiteMap`] `f : G → K` is a pair `(S, φ)`: `S` sends each vertex `v` of
//! `G` to a set `S_v` of vertices of `K`, and `φ` sends each wire of `G` to a
//! wire of `K`. It is a map exactly when three clauses hold.
//!
//! - **Disjointness.** Distinct vertices have disjoint images.
//! - **Boundary.** With `Im = φ(wires G)`, `in(S_v)` is the set of wires of `K`
//!   consumed in `S_v` whose producer lies outside `S_v` or which lie in `Im`,
//!   and `out(S_v)` the wires produced in `S_v` whose consumer lies outside
//!   `S_v` or which lie in `Im`. `φ` restricts to a bijection from the wires
//!   `v` consumes onto `in(S_v)`, and from the wires `v` produces onto
//!   `out(S_v)`.
//! - **Fusion.** A wire of `K` with two or more preimages has no inner wire of
//!   `G` among them, at most one preimage with a producer and at most one with
//!   a consumer.
//!
//! The boundary clause reads `S_v` as the sub-graph substituted for `v`, whose
//! inner wires are the wires of `K` inside it and outside `Im`. The fusion
//! clause reads a wire with two preimages as a contraction, an output leg
//! joined to an input leg; on stick-free sources the boundary clause already
//! implies it, and it stays in the class as the statement of what a contraction
//! is. Composition takes the union of images and composes the wire functions;
//! the identity sends each vertex to itself and each wire to itself.
//!
//! A map is **raising** when its kernel `{v : S_v = ∅}` is empty, and
//! **lowering** when it is a deletion followed by an isomorphism: images of at
//! most one vertex covering the target, `φ` bijective. The maps in both classes
//! are the isomorphisms. The **degree** of a shape is its vertices plus its
//! inner wires.
//!
//! # What the class borrows
//!
//! - **Substitution.** A graphical map sends a vertex to a sub-graph with the
//!   same boundary and identifies an output leg with an input leg for a
//!   contracting coface (Hackney, Robertson and Yau).
//! - **Admissibility.** The non-unital monad substitutes no graph with a stick
//!   component, so no vertex goes to a bare wire, and the unit of contraction
//!   is absent (Raynor, Definition 5.6).
//! - **The external unit.** The empty graph is an admissible zero-graph: `S_v =
//!   ∅` exactly when `v` has no ports (Raynor, Remark 3.22). Deleting such a
//!   vertex is the one codegeneracy the class holds, and it is not an
//!   isomorphism.
//!
//! # What the class decides
//!
//! - **Stick-free objects.** Admissibility, no stick components, is taken for
//!   the objects as it is for the substituted graphs, and enforced at
//!   construction. Alternatives: keeping sticks leaves no degree, since `↑ → ↑↑
//!   → ↑` composes to the identity through a non-invertible raising map;
//!   connected objects, the restriction the published graphical categories
//!   make, lose the factorization of `ε : • → •`, the point deleted and
//!   included back, which passes only through `∅`; restricting fusions to an
//!   output leg joined to an input leg is not closed under composition, since
//!   two sticks sent to the legs of `C(1,1)` and the corolla then substituted
//!   by `p→q` compose to a fusion of two sticks, so its closure holds a stick
//!   fusion again. Reversal: a consumer whose presheaves must hold a value at
//!   the bare wire, which brings the contraction unit back and with it the
//!   stick fusions that leave no degree.
//! - **Contraction raises.** A fusion is part of the map that performs it and
//!   is never factored out first, as an inner coface raises the graphical
//!   degree by the inner edge it creates. Alternative: contraction in the
//!   lowering class, ordered by vertices plus wires; it loses the factorization
//!   of `C(1,1) → p→q`, whose lowering half would join the corolla's legs into
//!   a loop the acyclic carrier refuses. Reversal: a wheeled carrier, where
//!   contracting a corolla's own legs is a shape.
//! - **Point deletion is the kernel's codegeneracy.** A map deletes exactly the
//!   points in its kernel, and every deletion has a section; deletions out of a
//!   shape are addressed by their kernels, and the point-count grade sets them
//!   apart from the point-free core, where every map raises. Alternative: no
//!   deletion, as in the graphical categories, where every vertex has a
//!   non-empty image; then `• → ∅` is no map and the empty graph, which the
//!   monad admits as the external product's unit, is never substituted.
//!   Reversal: a consumer that never restricts a presheaf along the removal of
//!   a constant.
//! - **No vertex reuse.** Images are disjoint, so a fold `• ⊔ • → •` and an
//!   étale cover are not maps, though the full Kleisli subcategory over the
//!   non-unital monad holds them. A fold retracts an inclusion, which leaves no
//!   degree; its restriction on a Segal object is the diagonal the product
//!   already determines. Reversal: a consumer whose presheaves must see that
//!   diagonal as data.
//!
//! A circuit algebra substitutes disconnected graphs, so an image may be
//! disconnected, and a restriction map needs no convex rewrite site.
//!
//! # The strata
//!
//! [`SegalStratum`] certifies the shapes of degree at most `n`: the corollas
//! through the corolla condition, and each shape of degree two to `n` as the
//! colimit of its corollas along its grafting pushouts through the [`segal`]
//! condition, over the families of maps out of the corollas whose images are
//! disjoint. Over it: graphical species with generators at each profile,
//! their elements at the corollas, the labellings of every shape, and an
//! [`Equivalence`] of species generated on its corollas, with its extension
//! to the free algebras and the corolla restriction [`restrict`] that
//! reflects a natural isomorphism back. The `segal` and `stratum` modules
//! state the alphabet and the range each statement fixes. A catalogue of the
//! chains alone, [`Family::Chains`], certifies the same way, and [`fills`]
//! checks that a diagram's cells meet along a shape's inner wires.
//!
//! The conditions read a site through [`Level`], its objects, maps and
//! classes at a bound; the catalogue is level one. A [`Wreath`] over the
//! wiring catalogue and a level is the next level: an outer shape whose
//! vertices each carry an object of the level below, so a pasting diagram of
//! dimension `n` is a shape of the `n`-th level. Restricted to the chains at
//! every level, the wreath holds Θₙ's objects under the site's maps, and
//! [`Level::find`] names an object it does not hold.
//!
//! [`segal`]: crate::segal()
//!
//! # Boundary wrappers
//!
//! Every count and index a signature here crosses is a transparent wrapper
//! (`ShapeSize`, `PointCount`, `ShapeIndex`, `CaseCount`, `Degree`,
//! `GeneratorBound`, …) converting with `From` both ways; the carrier's `Edge`,
//! `Wire`, `EdgeCount` and `WireCount` name vertices and wires.
//!
//! # References
//!
//! - Clemens Berger and Ieke Moerdijk. "On an Extension of the Notion of Reedy
//!   Category." _Mathematische Zeitschrift_ 269, 3–4 (2011), pages 977–1004.
//!   `doi:10.1007/s00209-010-0770-x`; preprint `arXiv:0809.3341` — the
//!   generalized Reedy axioms the checks run at the bound: the two classes
//!   meeting in the isomorphisms, the degree, the factorization unique up to
//!   unique isomorphism, and the rigidity axiom (iv), with its dual for the
//!   opposite category.
//! - Philip Hackney, Marcy Robertson, and Donald Yau. "On Factorizations of
//!   Graphical Maps." _Homology, Homotopy and Applications_ 20, 2 (2018), pages
//!   217–238. `doi:10.4310/HHA.2018.v20.n2.a11`; preprint `arXiv:1705.08546` —
//!   graphical maps as an edge map and a vertex-to-sub-graph map, contracting
//!   cofaces, the degree `|Vt| + |Edge_i|` and the generalized Reedy structure
//!   on connected graphs.
//! - Philip Hackney, Marcy Robertson, and Donald Yau. _Infinity Properads and
//!   Infinity Wheeled Properads_. Lecture Notes in Mathematics 2147, Springer,
//!   2015. `doi:10.1007/978-3-319-20547-2`; preprint `arXiv:1410.6716` — outer
//!   and inner contracting cofaces, and that each creates one inner edge.
//! - Sophie Raynor. "Modular Operads, Iterated Distributive Laws and a Nerve
//!   Theorem for Circuit Algebras." Preprint, 2024–2026. `arXiv:2412.20262` —
//!   the non-unital circuit-algebra monad over graphs without stick components
//!   (Definition 5.6), the external product's unit (Definition 3.21, Remark
//!   3.22), the empty graph as an admissible zero-graph, and the full Kleisli
//!   subcategory whose maps include folds.
//! - Michael Shulman. "Univalence for Inverse Diagrams and Homotopy
//!   Canonicity." _Mathematical Structures in Computer Science_ 25, 5 (2015).
//!   `doi:10.1017/S0960129514000565`; preprint `arXiv:1203.3253` — diagrams
//!   over an inverse category built in type theory by induction on degree, each
//!   stage a limit over the maps out of an object; a presheaf on the site is a
//!   diagram on its opposite, whose maps out of a shape are the site's latching
//!   maps into it.
//! - André Joyal and Joachim Kock. "Coherence for Weak Units." _Documenta
//!   Mathematica_ 18 (2013), pages 71–110. `doi:10.4171/dm/392`; preprint
//!   `arXiv:0907.4553` — a weak unit as a cancellable pseudo-idempotent, the
//!   property the unit check runs on scalars.
//! - `Henry-2018-nonunital_polygraphs_form_presheaf_category` — background: the
//!   dropped stick's parallel one level up: polygraphs whose generators have no
//!   identity as source or target form a presheaf category (Corollary 2.4.9),
//!   as the site has a degree because no stick is an object.
//!
//! [`Wiring`]: gandr_theory_circuit_algebras::Wiring

// Module documentation that predates the shape lint: 16 headings outside the
// vocabulary, 10 decision records, 4 budgets exceeded and 1 duplicated
// paragraph. Each allow leaves with the rewrite that clears its count.
#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    allow(
        module_doc_heading,
        doc_decision_record,
        module_doc_budget,
        module_doc_duplication,
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

mod catalogue;
mod conditions;
mod degree;
mod diagram;
mod level;
mod map;
#[cfg(test)]
mod negatives;
mod outcome;
mod point_count;
mod segal;
mod shape;
mod stratum;
mod units;
mod wreath;

pub use catalogue::Catalogue;
pub use catalogue::Family;
pub use catalogue::ShapeIndex;
pub use catalogue::hom_lookup;
pub use catalogue::shape_class;
pub use catalogue::shape_lookup;
pub use conditions::FactorizationDefect;
pub use conditions::FactorizationFailure;
pub use conditions::Part;
pub use conditions::PushoutOutcomes;
pub use conditions::Scope;
pub use conditions::Site;
pub use conditions::closure;
pub use conditions::codegeneracies;
pub use conditions::corolla;
pub use conditions::degree_order;
pub use conditions::deletion_classes;
pub use conditions::direct_core;
pub use conditions::dual_rigidity;
pub use conditions::factorization;
pub use conditions::identities;
pub use conditions::intersection;
pub use conditions::invertibility;
pub use conditions::latching;
pub use conditions::pushouts;
pub use conditions::rigidity;
pub use conditions::split_lowering;
pub use degree::Degree;
pub use diagram::Boundary;
pub use diagram::Unfilled;
pub use diagram::fills;
pub use level::Level;
pub use map::CompositionMismatch;
pub use map::ImageForm;
pub use map::Invertibility;
pub use map::MapForm;
pub use map::MapObstruction;
pub use map::Membership;
pub use map::SiteMap;
pub use map::VertexSet;
pub use map::WireForm;
pub use map::homs;
pub use outcome::CaseCount;
pub use outcome::Chain;
pub use outcome::MapCase;
pub use outcome::Outcome;
pub use outcome::Tally;
pub use outcome::Verdict;
pub use outcome::outcome_witness;
pub use point_count::core_decomposition;
pub use point_count::grounded_stratum;
pub use segal::Cocone;
pub use segal::Cocones;
pub use segal::Graft;
pub use segal::Inclusion;
pub use segal::Leg;
pub use segal::SegalDefect;
pub use segal::SegalFailure;
pub use segal::segal;
pub use shape::ClassCount;
pub use shape::End;
pub use shape::Ends;
pub use shape::PointCount;
pub use shape::Shape;
pub use shape::ShapeBudget;
pub use shape::ShapeKey;
pub use shape::ShapeObstruction;
pub use shape::ShapeSize;
pub use shape::VertexKind;
pub use shape::WireKind;
pub use shape::shapes_up_to;
pub use stratum::Bijection;
pub use stratum::Corolla;
pub use stratum::Defect;
pub use stratum::Element;
pub use stratum::ElementIndex;
pub use stratum::Equivalence;
pub use stratum::GeneratorCount;
pub use stratum::GeneratorIndex;
pub use stratum::Labelling;
pub use stratum::Natural;
pub use stratum::Port;
pub use stratum::PortCount;
pub use stratum::Profile;
pub use stratum::SegalStratum;
pub use stratum::Species;
pub use stratum::Table;
pub use stratum::Uncertified;
pub use stratum::Vacuity;
pub use stratum::restrict;
pub use stratum::stratum_corolla;
pub use units::GeneratorBound;
pub use units::UnitOutcomes;
pub use units::labelled_by_arity;
pub use units::merge;
pub use units::scalars;
pub use units::unit_property;
pub use wreath::Wreath;
pub use wreath::WreathKey;
pub use wreath::WreathMap;
pub use wreath::WreathShape;
pub use wreath::WreathShapeObstruction;
