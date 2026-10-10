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
//! A [`Shape`] is a [`Wiring`] the carrier admits, read as a graph, with no
//! stick component. Each generator is a vertex; each wire records its
//! producer and its consumer, either a vertex or an open end. A wire open at
//! one end is a leg; attached at both, inner; open at both, a stick, which
//! the constructors refuse by naming it. A wire with no operation on it may
//! run between two vertices of a shape; alone, it is never an object. The
//! generator labels, the order of a generator's ports and the order of the
//! interface are forgotten: they are the data an element of a presheaf
//! carries, as the symmetric-group action on a corolla's value does in the
//! published graphical categories. Two shapes are the same object when a
//! bijection of vertices carries one multiset of wire ends onto the other.
//! The empty shape `∅` and the arity-zero corolla `•`, the point, are
//! objects.
//!
//! # Maps
//!
//! A [`SiteMap`] `f : G → K` is a pair `(S, φ)`: `S` sends each vertex `v` of
//! `G` to a set `S_v` of vertices of `K`, and `φ` sends each wire of `G` to a
//! wire of `K`. It is a map exactly when:
//!
//! - **disjointness**: distinct vertices have disjoint images;
//! - **boundary**: with `Im = φ(wires G)`, let `in(S_v)` be the wires of `K`
//!   consumed in `S_v` whose producer lies outside `S_v` or which lie in `Im`,
//!   and `out(S_v)` the wires produced in `S_v` whose consumer lies outside
//!   `S_v` or which lie in `Im`. Then `φ` restricts to a bijection from the
//!   wires `v` consumes onto `in(S_v)`, and from the wires `v` produces onto
//!   `out(S_v)`;
//! - **fusion**: a wire of `K` with two or more preimages has no inner wire of
//!   `G` among them, at most one preimage with a producer and at most one with
//!   a consumer.
//!
//! The boundary clause reads `S_v` as the sub-graph substituted for `v`; the
//! wires of `K` inside it and outside `Im` are its inner wires. The fusion
//! clause reads a wire with two preimages as a contraction, an output leg
//! joined to an input leg; on stick-free sources the boundary clause already
//! implies it. Composition is union of images and composition of wire
//! functions; the identity sends each vertex to itself and each wire to
//! itself.
//!
//! A map is **raising** when no vertex is deleted, its kernel `{v : S_v = ∅}`
//! empty, and **lowering** when it is a deletion followed by an isomorphism:
//! images of at most one vertex covering the target, `φ` bijective. The
//! **degree** of a shape is its vertices plus its inner wires.
//!
//! # What the class borrows
//!
//! - The substitution reading of a graphical category's maps: a vertex goes to
//!   a sub-graph with the same boundary, and a contracting coface identifies an
//!   output leg with an input leg (Hackney, Robertson and Yau).
//! - The non-unital monad's admissibility, no stick components (Raynor,
//!   Definition 5.6), taken for the substituted sub-graphs and for the objects
//!   both.
//! - The external product's unit: `S_v = ∅` exactly when `v` has no ports, the
//!   empty graph substituted at the point (Raynor, Remark 3.22). Deleting a
//!   point is the one codegeneracy the class holds.
//!
//! # What the class decides
//!
//! - **Stick-free objects.** No object has a stick component. Keeping sticks
//!   leaves no degree, since `↑ → ↑↑ → ↑` composes to the identity; connected
//!   objects lose the point's deletion, which lands on `∅`; restricting fusions
//!   to an output leg and an input leg is not closed under composition.
//! - **Contraction raises.** A fusion is part of the map that performs it,
//!   never factored out first; placed in the lowering class it loses the
//!   factorization of `C(1,1) → p→q`.
//! - **Point deletion is the kernel's codegeneracy.** A map deletes the points
//!   in its kernel; deletions are split, addressed by their kernels, and graded
//!   apart by point count.
//! - **No vertex reuse.** Images are disjoint, so a fold `• ⊔ • → •` and an
//!   étale cover are not maps, though the full Kleisli subcategory holds them.
//!
//! [`Wiring`]: gandr_theory_circuit_algebras::Wiring

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
mod map;
#[cfg(test)]
mod negatives;
mod outcome;
mod point_count;
mod shape;
mod units;

pub use catalogue::Catalogue;
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
pub use shape::End;
pub use shape::Ends;
pub use shape::PointCount;
pub use shape::Shape;
pub use shape::ShapeKey;
pub use shape::ShapeObstruction;
pub use shape::ShapeSize;
pub use shape::VertexKind;
pub use shape::WireKind;
pub use shape::shapes_up_to;
pub use units::GeneratorBound;
pub use units::UnitOutcomes;
pub use units::labelled_by_arity;
pub use units::merge;
pub use units::scalars;
pub use units::unit_property;
