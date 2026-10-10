//! Maps of shapes: the morphism class the crate root states.
//!
//! A [`SiteMap`] is a candidate pair `(S, φ)`; [`SiteMap::validate`] is the
//! class, and every map the suites count passes it. [`homs`] enumerates the
//! maps between two shapes by candidate generation and that one validator.
//! The clauses are stated on graphs; the crate's negatives run the same
//! validator on graphs with stick components, which no shape has.

use alloc::boxed::Box;
use alloc::vec;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
use gandr_theory_circuit_algebras::Edge;
use gandr_theory_circuit_algebras::EdgeCount;
use gandr_theory_circuit_algebras::Leg;
use gandr_theory_circuit_algebras::Wire;
use gandr_theory_circuit_algebras::WireCount;

use crate::outcome::Verdict;
use crate::shape::End;
use crate::shape::Ends;
use crate::shape::Graph;
use crate::shape::Shape;
use crate::shape::VertexKind;
use crate::shape::WireKind;

#[cfg(test)]
mod tests;

/// Whether a vertex or a wire lies in a set, or a map in a class.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Membership
{
    /// It lies in the set.
    Inside,
    /// It does not.
    Outside,
}

/// The most vertices a vertex set holds.
const WORD: usize = 64;

/// A set of vertices of one shape, as one machine word.
///
/// # Specification
/// - ensures: holds vertices `0` to `63`; [`VertexSet::single`] of a later
///   vertex is empty, which no shape reaches because a shape holds at most 64
///   vertices.
/// - provides: the vertex images `S_v` of a map.
/// - panics: none.
/// - executable: none — a type carries no runtime predicate; the constructors'
///   postconditions check the word they build.
///
/// # Adequacy
/// - hypothesis: L3 — membership, union, difference, member order and count
///   over sets reaching the first and the last bit, and the empty set past it.
/// - witness: `tests::maps::vertex_sets_hold_the_first_and_last_vertex`
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct VertexSet(u64);

impl VertexSet
{
    /// The empty set.
    pub const EMPTY: Self = Self(0);

    /// The set holding only `vertex`.
    ///
    /// # Specification
    /// - ensures: the set whose one member is `vertex`, or the empty set for a
    ///   vertex past the sixty-fourth.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — vertices zero, sixty-three and sixty-four, the last
    ///   giving the empty set.
    /// - witness: `tests::maps::vertex_sets_hold_the_first_and_last_vertex`
    #[inline]
    #[must_use]
    #[spec(ensures: |set| if usize::from(vertex) < WORD {
        set.0.is_power_of_two() && usize::try_from(set.0.trailing_zeros()) == Ok(usize::from(vertex))
    } else {
        set.0 == 0
    })]
    pub fn single(vertex: Edge) -> Self
    {
        let shift = u32::try_from(usize::from(vertex)).unwrap_or(u32::MAX);
        Self(1_u64.checked_shl(shift).unwrap_or(0))
    }

    /// The vertices `0` to `count - 1`.
    ///
    /// # Specification
    /// - ensures: every vertex below `count`, capped at sixty-four.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — sixty-four vertices fill the word; every hom count
    ///   and coverage reading goes through it.
    /// - witness: `tests::maps::vertex_sets_hold_the_first_and_last_vertex`
    /// - witness: `tests::maps::map_forms_read_back`
    #[inline]
    #[must_use]
    #[spec(ensures: |set| [
        usize::try_from(set.0.count_ones()) == Ok(usize::from(count).min(WORD)),
        set.members().all(|vertex| usize::from(vertex) < usize::from(count)),
    ])]
    pub fn below(count: EdgeCount) -> Self
    {
        (0 .. usize::from(count)).fold(Self::EMPTY, |set, vertex| {
            set.union(Self::single(Edge::from(vertex)))
        })
    }

    /// The union of two sets.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn union(
        self,
        other: Self,
    ) -> Self
    {
        Self(self.0 | other.0)
    }

    /// The intersection of two sets.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn intersection(
        self,
        other: Self,
    ) -> Self
    {
        Self(self.0 & other.0)
    }

    /// The members of `self` outside `other`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn without(
        self,
        other: Self,
    ) -> Self
    {
        Self(self.0 & !other.0)
    }

    /// Whether `vertex` is a member.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn contains(
        self,
        vertex: Edge,
    ) -> Membership
    {
        if self.intersection(Self::single(vertex)) == Self::EMPTY {
            Membership::Outside
        }
        else {
            Membership::Inside
        }
    }

    /// Whether `end` attaches to a member.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn holds_end(
        self,
        end: End,
    ) -> Membership
    {
        match end {
            | End::Open => Membership::Outside,
            | End::Vertex(vertex) => self.contains(vertex),
        }
    }

    /// The members, in increasing order.
    ///
    /// # Specification
    /// - ensures: each member once, least first.
    /// - panics: none.
    /// - executable: none — the backend lowers the body to a closure whose
    ///   return type cannot name this opaque iterator.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a set of the first and the last vertex lists them in
    ///   order, and every image the enumerator builds is read back through it.
    /// - witness: `tests::maps::vertex_sets_hold_the_first_and_last_vertex`
    /// - witness: `tests::maps::the_enumerator_agrees_with_brute_force`
    #[inline]
    pub fn members(self) -> impl Iterator<Item = Edge>
    {
        let mut rest = self.0;
        core::iter::from_fn(move || {
            if rest == 0 {
                return None;
            }
            let Ok(vertex) = usize::try_from(rest.trailing_zeros())
            else {
                return None;
            };
            rest &= rest.saturating_sub(1);
            Some(Edge::from(vertex))
        })
    }

    /// How many members the set has.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn count(self) -> EdgeCount
    {
        EdgeCount::from(usize::try_from(self.0.count_ones()).unwrap_or(usize::MAX))
    }
}

impl fmt::Display for VertexSet
{
    /// Writes the members in braces: `{0,2}`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str("{")?;
        for (index, vertex) in self.members().enumerate() {
            let separator = if index == 0 { "" } else { "," };
            write!(f, "{separator}{}", usize::from(vertex))?;
        }
        f.write_str("}")
    }
}

/// Why a candidate pair is not a map of the class.
///
/// # Specification
/// - provides: the clause broken and the vertex, vertices or wire that break
///   it. On shapes the boundary clause implies the fusion clause, so
///   [`MapObstruction::Fusion`] arises only on graphs with a stick component.
/// - executable: none — a refusal on its own lacks the candidate and the two
///   graphs it was decided against; the validator's predicate checks each
///   variant's payload against them.
///
/// # Adequacy
/// - hypothesis: L3 — each variant is produced by a hand-built candidate
///   breaking only its clause and asserted with its exact payload, the fusion
///   refusal on a graph with a stick.
/// - witness: `map::tests::each_clause_refuses_by_variant`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum MapObstruction
{
    /// The candidate has a different number of vertex images than the
    /// source has vertices.
    ImageCount
    {
        /// The source's vertex count.
        expected: EdgeCount,
        /// The candidate's image count.
        found: EdgeCount,
    },
    /// The candidate has a different number of wire images than the source
    /// has wires.
    WireImageCount
    {
        /// The source's wire count.
        expected: WireCount,
        /// The candidate's wire image count.
        found: WireCount,
    },
    /// A vertex image holds a vertex the target does not have.
    ImageOutOfRange
    {
        /// The source vertex whose image overruns.
        vertex: Edge,
    },
    /// A wire image is a wire the target does not have.
    WireOutOfRange
    {
        /// The source wire whose image overruns.
        wire: Wire,
    },
    /// Two vertices share a target vertex.
    Overlap
    {
        /// The earlier vertex.
        first: Edge,
        /// The later vertex.
        second: Edge,
    },
    /// A vertex's ports do not biject onto its image's boundary on one side.
    Boundary
    {
        /// The vertex.
        vertex: Edge,
        /// The side whose bijection fails.
        leg: Leg,
    },
    /// A target wire with several preimages is not a contraction chain.
    Fusion
    {
        /// The target wire.
        wire: Wire,
    },
}

impl fmt::Display for MapObstruction
{
    /// Names the clause the candidate breaks.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match *self {
            | Self::ImageCount { .. } => "one vertex image per source vertex",
            | Self::WireImageCount { .. } => "one wire image per source wire",
            | Self::ImageOutOfRange { .. } => "a vertex image inside the target",
            | Self::WireOutOfRange { .. } => "a wire image inside the target",
            | Self::Overlap { .. } => "disjointness",
            | Self::Boundary { .. } => "boundary",
            | Self::Fusion { .. } => "fusion",
        })
    }
}

impl core::error::Error for MapObstruction
{
}

/// Why two maps do not compose.
///
/// # Specification
/// - provides: the vertex or wire of the first map's image that the second map
///   has no image for.
/// - executable: none — a refusal on its own lacks the two maps; the
///   composite's predicate checks the payload against them.
///
/// # Adequacy
/// - hypothesis: L3 — a vertex image and a wire image each past the second
///   map's source are refused with the exact vertex and wire.
/// - witness: `map::tests::composition_refuses_a_missing_image`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum CompositionMismatch
{
    /// The first map's image names a vertex the second map has no image
    /// for.
    Vertex
    {
        /// The vertex.
        vertex: Edge,
    },
    /// The first map's wire image names a wire the second map has no image
    /// for.
    Wire
    {
        /// The wire.
        wire: Wire,
    },
}

/// Whether a map has an inverse in the class.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Invertibility
{
    /// The map is an isomorphism.
    Invertible,
    /// The map is not.
    NotInvertible,
}

/// A candidate map `(S, φ)` from one shape to another.
///
/// # Specification
/// - ensures: nothing on its own; [`SiteMap::validate`] decides whether the
///   pair is a map of the class between two given shapes.
/// - provides: the morphisms of the site.
/// - panics: none.
/// - executable: none — a candidate holds no invariant of its own; the
///   validator's predicate is where the class is checked.
///
/// # Adequacy
/// - hypothesis: L2 — the hom-set counts of hand-checked pairs are pinned, and
///   the enumerator agrees with a brute-force enumeration of every pair `(S,
///   φ)` at small sizes.
/// - witness: `tests::maps::hom_counts_match_hand_counts`
/// - witness: `tests::maps::the_enumerator_agrees_with_brute_force`
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct SiteMap
{
    /// The image `S_v` of each source vertex, in vertex order.
    images: Box<[VertexSet]>,
    /// The image `φ(w)` of each source wire, in wire order.
    wires: Box<[Wire]>,
}

impl SiteMap
{
    /// The candidate with the given vertex and wire images.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new(
        images: Vec<VertexSet>,
        wires: Vec<Wire>,
    ) -> Self
    {
        Self {
            images: images.into_boxed_slice(),
            wires: wires.into_boxed_slice(),
        }
    }

    /// The identity of `shape`.
    ///
    /// # Specification
    /// - ensures: each vertex to itself and each wire to itself, an invertible
    ///   map of the class from `shape` to `shape`.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the identity laws and validity are checked for every
    ///   shape at the bound; L3 — the identity of a corolla reads back as a
    ///   bijection onto its singletons.
    /// - witness: `tests::maps::the_class_is_a_category_at_the_bound`
    /// - witness: `tests::maps::map_forms_read_back`
    #[inline]
    #[must_use]
    #[spec(ensures: |ref identity| [
        identity.validate(shape, shape).is_ok(),
        identity.invertibility(shape) == Invertibility::Invertible,
    ])]
    pub fn identity(shape: &Shape) -> Self
    {
        Self {
            images: shape.vertices().map(VertexSet::single).collect(),
            wires: (0 .. usize::from(shape.wire_count()))
                .map(Wire::from)
                .collect(),
        }
    }

    /// The vertex images, in source vertex order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn images(&self) -> &[VertexSet]
    {
        &self.images
    }

    /// The wire images, in source wire order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn wires(&self) -> &[Wire]
    {
        &self.wires
    }

    /// The image of one source vertex, empty for a vertex past the source.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn image(
        &self,
        vertex: Edge,
    ) -> VertexSet
    {
        self.images
            .get(usize::from(vertex))
            .copied()
            .unwrap_or(VertexSet::EMPTY)
    }

    /// The union of the vertex images.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn image_union(&self) -> VertexSet
    {
        self.images
            .iter()
            .fold(VertexSet::EMPTY, |union, image| union.union(*image))
    }

    /// The kernel: the source vertices sent to the empty set.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn kernel(&self) -> VertexSet
    {
        self.images
            .iter()
            .enumerate()
            .filter(|entry| *entry.1 == VertexSet::EMPTY)
            .fold(VertexSet::EMPTY, |kernel, entry| {
                kernel.union(VertexSet::single(Edge::from(entry.0)))
            })
    }

    /// The target wires some source wire reaches, one mark per target wire.
    ///
    /// # Specification
    /// trivial.
    fn wire_marks(
        &self,
        target: Graph<'_>,
    ) -> Vec<Membership>
    {
        let mut marks = vec![Membership::Outside; usize::from(target.wire_count())];
        for wire in self.wires.iter().copied() {
            if let Some(mark) = marks.get_mut(usize::from(wire)) {
                *mark = Membership::Inside;
            }
        }
        marks
    }

    /// The ends of the source wires sent to `target`.
    ///
    /// # Specification
    /// trivial.
    fn preimages(
        &self,
        source: Graph<'_>,
        target: Wire,
    ) -> Vec<Ends>
    {
        source
            .ends()
            .iter()
            .zip(self.wires.iter())
            .filter(|pair| *pair.1 == target)
            .map(|pair| *pair.0)
            .collect()
    }

    /// Whether the pair is a map of the class from `source` to `target`.
    ///
    /// # Specification
    /// - ensures: `Ok` exactly when the images have the source's shape, lie in
    ///   the target, and satisfy disjointness, boundary and fusion as the crate
    ///   root states them; the first clause broken, in that order, otherwise. A
    ///   shape has no stick, so the boundary clause implies the fusion clause
    ///   and the fusion refusal never arises here.
    /// - fails: the first clause broken.
    /// - panics: none.
    ///
    /// # Errors
    /// The [`MapObstruction`] naming the first clause broken.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the hom counts of hand-checked pairs and the
    ///   brute-force agreement observe every clause together on shapes, and
    ///   every candidate the brute force tries is validated here, so a fusion
    ///   refusal on a shape would trip the predicate.
    /// - witness: `tests::maps::hom_counts_match_hand_counts`
    /// - witness: `tests::maps::the_enumerator_agrees_with_brute_force`
    #[inline]
    #[spec(ensures: |ref result| !matches!(*result, Err(MapObstruction::Fusion { .. })))]
    pub fn validate(
        &self,
        source: &Shape,
        target: &Shape,
    ) -> Result<(), MapObstruction>
    {
        self.check(source.graph(), target.graph())
    }

    /// The class's validator on two graphs, sticks admitted: the clauses the
    /// crate root states, decided in their order.
    ///
    /// # Specification
    /// - ensures: `Ok` exactly when the images have the source's shape, lie in
    ///   the target, and satisfy disjointness, boundary and fusion; on `Ok` the
    ///   images are pairwise disjoint and inside the target; each refusal's
    ///   payload names a part that breaks its clause.
    /// - fails: the first clause broken: the image counts, the ranges,
    ///   disjointness, the boundary of each vertex in order, input side first,
    ///   then fusion of each target wire in order.
    /// - panics: none.
    ///
    /// # Errors
    /// The [`MapObstruction`] naming the first clause broken.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each clause is broken by a hand-built candidate on
    ///   raw graphs and observed by its variant and payload, the fusion clause
    ///   through a stick fused with an inner wire; L2 — the negatives validate
    ///   stick fusions and contractions on graphs read from raw wirings.
    /// - witness: `map::tests::each_clause_refuses_by_variant`
    /// - witness: `negatives::sticks_as_objects_admit_no_degree`
    /// - witness: `negatives::vertex_end_fusions_are_not_closed`
    #[spec(ensures: |ref result| match *result {
        Ok(()) => self.images.len() == usize::from(source.vertex_count())
            && self.wires.len() == usize::from(source.wire_count())
            && self.wires.iter().all(|wire| usize::from(*wire) < usize::from(target.wire_count()))
            && self.image_union().without(VertexSet::below(target.vertex_count())) == VertexSet::EMPTY
            && usize::from(self.image_union().count())
                == self.images.iter().fold(0_usize, |total, image| total.saturating_add(usize::from(image.count()))),
        Err(MapObstruction::ImageCount { expected, found }) => expected == source.vertex_count() && found != expected,
        Err(MapObstruction::WireImageCount { expected, found }) => expected == source.wire_count() && found != expected,
        Err(MapObstruction::ImageOutOfRange { vertex }) => {
            self.image(vertex).without(VertexSet::below(target.vertex_count())) != VertexSet::EMPTY
        },
        Err(MapObstruction::WireOutOfRange { wire }) => {
            self.wires.get(usize::from(wire)).is_some_and(|image| usize::from(*image) >= usize::from(target.wire_count()))
        },
        Err(MapObstruction::Overlap { first, second }) => {
            usize::from(first) < usize::from(second) && self.image(first).intersection(self.image(second)) != VertexSet::EMPTY
        },
        Err(MapObstruction::Boundary { vertex, .. }) => usize::from(vertex) < usize::from(source.vertex_count()),
        Err(MapObstruction::Fusion { wire }) => self.wires.iter().filter(|image| **image == wire).count() >= 2,
    })]
    pub(crate) fn check(
        &self,
        source: Graph<'_>,
        target: Graph<'_>,
    ) -> Result<(), MapObstruction>
    {
        self.check_ranges(source, target)?;
        self.check_disjointness()?;
        let marks = self.wire_marks(target);
        for vertex in source.vertices() {
            self.check_side(source, target, &marks, (vertex, Leg::Input))?;
            self.check_side(source, target, &marks, (vertex, Leg::Output))?;
        }
        self.check_fusion(source, target)
    }

    /// The image counts and the target's ranges.
    ///
    /// # Specification
    /// - ensures: `Ok` exactly when there is one vertex image per source vertex
    ///   and one wire image per source wire, every image inside the target.
    /// - fails: the counts first, vertex images before wire images, then the
    ///   first image out of range, vertex images before wire images.
    /// - panics: none.
    /// - executable: none — the payload predicate on the class's validator
    ///   checks every refusal this step returns, and it runs first there.
    ///
    /// # Errors
    /// - [`MapObstruction::ImageCount`], [`MapObstruction::WireImageCount`]: a
    ///   count differs from the source's.
    /// - [`MapObstruction::ImageOutOfRange`],
    ///   [`MapObstruction::WireOutOfRange`]: an image past the target.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each of the four refusals by a candidate failing only
    ///   it, with its exact payload.
    /// - witness: `map::tests::each_clause_refuses_by_variant`
    fn check_ranges(
        &self,
        source: Graph<'_>,
        target: Graph<'_>,
    ) -> Result<(), MapObstruction>
    {
        if self.images.len() != usize::from(source.vertex_count()) {
            return Err(MapObstruction::ImageCount {
                expected: source.vertex_count(),
                found: EdgeCount::from(self.images.len()),
            });
        }
        if self.wires.len() != usize::from(source.wire_count()) {
            return Err(MapObstruction::WireImageCount {
                expected: source.wire_count(),
                found: WireCount::from(self.wires.len()),
            });
        }
        let room = VertexSet::below(target.vertex_count());
        if let Some(index) = self
            .images
            .iter()
            .position(|image| image.without(room) != VertexSet::EMPTY)
        {
            return Err(MapObstruction::ImageOutOfRange {
                vertex: Edge::from(index),
            });
        }
        if let Some(index) = self
            .wires
            .iter()
            .position(|wire| usize::from(*wire) >= usize::from(target.wire_count()))
        {
            return Err(MapObstruction::WireOutOfRange {
                wire: Wire::from(index),
            });
        }
        Ok(())
    }

    /// The disjointness clause.
    ///
    /// # Specification
    /// - ensures: `Ok` exactly when no two images share a vertex.
    /// - fails: the first later vertex whose image meets an earlier one, with
    ///   the earliest such earlier vertex.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`MapObstruction::Overlap`]: two images share a vertex.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two vertices sent to overlapping images are refused
    ///   with both named; L2 — the enumerator never builds an overlap, so the
    ///   brute force observes every overlapping candidate refused.
    /// - witness: `map::tests::each_clause_refuses_by_variant`
    /// - witness: `tests::maps::the_enumerator_agrees_with_brute_force`
    #[spec(ensures: |result| match result {
        Ok(()) => usize::from(self.image_union().count())
            == self.images.iter().fold(0_usize, |total, image| total.saturating_add(usize::from(image.count()))),
        Err(MapObstruction::Overlap { first, second }) => usize::from(first) < usize::from(second)
            && self.image(first).intersection(self.image(second)) != VertexSet::EMPTY
            && self.images.iter().take(usize::from(second)).enumerate().all(|later| {
                self.images.iter().take(later.0).all(|earlier| earlier.intersection(*later.1) == VertexSet::EMPTY)
            }),
        Err(_) => false,
    })]
    fn check_disjointness(&self) -> Result<(), MapObstruction>
    {
        let mut seen = VertexSet::EMPTY;
        for (index, image) in self.images.iter().copied().enumerate() {
            if image.intersection(seen) != VertexSet::EMPTY {
                let first = self
                    .images
                    .iter()
                    .position(|earlier| earlier.intersection(image) != VertexSet::EMPTY)
                    .unwrap_or(index);
                return Err(MapObstruction::Overlap {
                    first: Edge::from(first),
                    second: Edge::from(index),
                });
            }
            seen = seen.union(image);
        }
        Ok(())
    }

    /// The boundary clause on one side of one vertex.
    ///
    /// # Specification
    /// - requires: the ranges and disjointness have passed, so every image lies
    ///   inside `target` and `marks` holds one mark per target wire.
    /// - ensures: `Ok` exactly when the source wires `vertex` consumes (on the
    ///   input side) or produces (on the output side), sent through `φ` and
    ///   sorted, are the target wires consumed (produced) in `S_vertex` whose
    ///   other end lies outside it or which `φ` reaches.
    /// - fails: the two lists differ.
    /// - panics: none.
    /// - executable: none — the expected list is the clause itself, computed
    ///   here; a predicate would recompute it, and the hom counts and the
    ///   brute-force agreement observe it instead.
    ///
    /// # Errors
    /// - [`MapObstruction::Boundary`]: the vertex and side whose bijection
    ///   fails.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a corolla's legs sent to each other's images are
    ///   refused on the input side; L2 — the hand-checked hom counts include a
    ///   pair with no map because a sink has no output to match its image's
    ///   output leg, and the brute force tries every wire function.
    /// - witness: `map::tests::each_clause_refuses_by_variant`
    /// - witness: `tests::maps::hom_counts_match_hand_counts`
    /// - witness: `tests::maps::the_enumerator_agrees_with_brute_force`
    fn check_side(
        &self,
        source: Graph<'_>,
        target: Graph<'_>,
        marks: &[Membership],
        (vertex, leg): (Edge, Leg),
    ) -> Result<(), MapObstruction>
    {
        let image = self.image(vertex);
        let near = |ends: Ends| match leg {
            | Leg::Input => ends.consumer(),
            | Leg::Output => ends.producer(),
        };
        let far = |ends: Ends| match leg {
            | Leg::Input => ends.producer(),
            | Leg::Output => ends.consumer(),
        };
        let expected: Vec<Wire> = target
            .ends()
            .iter()
            .copied()
            .zip(marks.iter().copied())
            .enumerate()
            .filter(|entry| {
                let (ends, mark) = entry.1;
                image.holds_end(near(ends)) == Membership::Inside
                    && (image.holds_end(far(ends)) == Membership::Outside
                        || mark == Membership::Inside)
            })
            .map(|entry| Wire::from(entry.0))
            .collect();
        let mut actual: Vec<Wire> = source
            .ends()
            .iter()
            .copied()
            .zip(self.wires.iter().copied())
            .filter(|pair| near(pair.0) == End::Vertex(vertex))
            .map(|pair| pair.1)
            .collect();
        actual.sort_unstable();
        if actual == expected {
            Ok(())
        }
        else {
            Err(MapObstruction::Boundary { vertex, leg })
        }
    }

    /// The fusion clause.
    ///
    /// # Specification
    /// - ensures: `Ok` exactly when every target wire with two or more
    ///   preimages has no inner preimage, at most one preimage with a producer
    ///   and at most one with a consumer.
    /// - fails: the first target wire whose preimages break it.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`MapObstruction::Fusion`]: the target wire.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a stick fused with an inner wire is refused at the
    ///   inner wire's image, and two sticks fused onto one are admitted.
    /// - witness: `map::tests::each_clause_refuses_by_variant`
    /// - witness: `negatives::sticks_as_objects_admit_no_degree`
    #[spec(ensures: |result| match result {
        Ok(()) => (0 .. usize::from(target.wire_count())).all(|index| {
            let group = self.preimages(source, Wire::from(index));
            group.len() < 2 || (group.iter().all(|ends| ends.kind() != WireKind::Inner)
                && group.iter().filter(|ends| ends.producer() != End::Open).count() <= 1
                && group.iter().filter(|ends| ends.consumer() != End::Open).count() <= 1)
        }),
        Err(MapObstruction::Fusion { wire }) => self.preimages(source, wire).len() >= 2,
        Err(_) => false,
    })]
    fn check_fusion(
        &self,
        source: Graph<'_>,
        target: Graph<'_>,
    ) -> Result<(), MapObstruction>
    {
        for wire in (0 .. usize::from(target.wire_count())).map(Wire::from) {
            let preimages = self.preimages(source, wire);
            if preimages.len() < 2 {
                continue;
            }
            let inner = preimages.iter().any(|ends| ends.kind() == WireKind::Inner);
            let produced = preimages
                .iter()
                .filter(|ends| ends.producer() != End::Open)
                .count();
            let consumed = preimages
                .iter()
                .filter(|ends| ends.consumer() != End::Open)
                .count();
            if inner || produced > 1 || consumed > 1 {
                return Err(MapObstruction::Fusion { wire });
            }
        }
        Ok(())
    }

    /// The composite `next ∘ self`: first `self`, then `next`.
    ///
    /// # Specification
    /// - ensures: each vertex image is the union of `next`'s images of its
    ///   members, and each wire image is `next`'s image of `self`'s.
    /// - fails: `self` names a vertex or wire `next` has no image for.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`CompositionMismatch::Vertex`]: an image member past `next`'s source.
    /// - [`CompositionMismatch::Wire`]: a wire image past `next`'s source.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — associativity, the identity laws and closure of the
    ///   class under composition are checked over every composable pair at the
    ///   bound; L3 — a hand-computed composite is pinned, and both mismatches
    ///   are refused with their payloads.
    /// - witness: `tests::maps::the_class_is_a_category_at_the_bound`
    /// - witness: `tests::maps::a_contraction_composes_with_a_deletion`
    /// - witness: `map::tests::composition_refuses_a_missing_image`
    #[inline]
    #[spec(ensures: |ref result| match *result {
        Ok(ref composite) => composite.images.len() == self.images.len()
            && composite.wires.len() == self.wires.len()
            && composite.wires.iter().zip(self.wires.iter()).all(|pair| next.wires.get(usize::from(*pair.1)) == Some(pair.0))
            && composite.images.iter().zip(self.images.iter()).all(|pair| {
                pair.1.members().fold(VertexSet::EMPTY, |union, member| union.union(next.image(member))) == *pair.0
            }),
        Err(CompositionMismatch::Vertex { vertex }) => usize::from(vertex) >= next.images.len()
            && self.images.iter().any(|image| image.contains(vertex) == Membership::Inside),
        Err(CompositionMismatch::Wire { wire }) => usize::from(wire) >= next.wires.len() && self.wires.contains(&wire),
    })]
    pub fn then(
        &self,
        next: &Self,
    ) -> Result<Self, CompositionMismatch>
    {
        let mut images: Vec<VertexSet> = Vec::with_capacity(self.images.len());
        for image in self.images.iter().copied() {
            let mut union = VertexSet::EMPTY;
            for vertex in image.members() {
                let further = next
                    .images
                    .get(usize::from(vertex))
                    .copied()
                    .ok_or(CompositionMismatch::Vertex { vertex })?;
                union = union.union(further);
            }
            images.push(union);
        }
        let mut wires: Vec<Wire> = Vec::with_capacity(self.wires.len());
        for wire in self.wires.iter().copied() {
            let further = next
                .wires
                .get(usize::from(wire))
                .copied()
                .ok_or(CompositionMismatch::Wire { wire })?;
            wires.push(further);
        }
        Ok(Self::new(images, wires))
    }

    /// Whether the map is in the raising class: no vertex is deleted.
    ///
    /// # Specification
    /// - ensures: [`Membership::Inside`] exactly when every vertex image is
    ///   non-empty, so the kernel is empty.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the identity, a contraction and the inclusion of the
    ///   empty shape are raising, and the deletion of a point and the
    ///   endomorphism deleting and re-including it are not.
    /// - witness: `tests::maps::the_two_classes_sort_the_fixtures`
    #[inline]
    #[must_use]
    #[spec(ensures: |answer| (answer == Membership::Inside) == self.images.iter().all(|image| *image != VertexSet::EMPTY))]
    pub fn raising(&self) -> Membership
    {
        if self.kernel() == VertexSet::EMPTY {
            Membership::Inside
        }
        else {
            Membership::Outside
        }
    }

    /// Whether the map, read against `target`, is in the lowering class: a
    /// deletion followed by an isomorphism.
    ///
    /// # Specification
    /// - ensures: [`Membership::Inside`] exactly when every image holds at most
    ///   one vertex, the images cover the target's vertices and `φ` is a
    ///   bijection onto the target's wires; then the target has as many
    ///   vertices as the source keeps and as many wires as the source has.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the identity and the deletion of a point are
    ///   lowering; a contraction, the inclusion of the empty shape and the
    ///   endomorphism deleting and re-including a point are not.
    /// - witness: `tests::maps::the_two_classes_sort_the_fixtures`
    #[inline]
    #[must_use]
    #[spec(ensures: |answer| answer == Membership::Outside || (
        self.wires.len() == usize::from(target.wire_count())
            && usize::from(self.image_union().count()) == usize::from(target.vertex_count())
            && self.images.iter().all(|image| usize::from(image.count()) <= 1)
    ))]
    pub fn lowering(
        &self,
        target: &Shape,
    ) -> Membership
    {
        let form = self.form(target);
        let small = matches!(form.images, ImageForm::Singletons | ImageForm::AtMostOne);
        if small && form.cover == Membership::Inside && form.wires == WireForm::Bijective {
            Membership::Inside
        }
        else {
            Membership::Outside
        }
    }

    /// Whether the map is an isomorphism onto `target`.
    ///
    /// # Specification
    /// - ensures: [`Invertibility::Invertible`] exactly when every image is a
    ///   single vertex, the images cover the target, and `φ` is a bijection
    ///   onto the target's wires: exactly when the map is both raising and
    ///   lowering.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — at the bound a map is invertible here exactly when
    ///   some map of the class composes with it to both identities.
    /// - witness: `tests::maps::invertibility_matches_two_sided_inverses`
    #[inline]
    #[must_use]
    #[spec(ensures: |answer| (answer == Invertibility::Invertible)
        == (self.raising() == Membership::Inside && self.lowering(target) == Membership::Inside))]
    pub fn invertibility(
        &self,
        target: &Shape,
    ) -> Invertibility
    {
        let singletons = self
            .images
            .iter()
            .all(|image| usize::from(image.count()) == 1);
        let covers = self.image_union() == VertexSet::below(target.vertex_count());
        let bijective = self.form(target).wires == WireForm::Bijective;
        if singletons && covers && bijective {
            Invertibility::Invertible
        }
        else {
            Invertibility::NotInvertible
        }
    }

    /// The shape of the map's vertex images and wire function, read off
    /// against its target.
    ///
    /// # Specification
    /// - ensures: `images` is [`ImageForm::Singletons`] when every image is one
    ///   vertex, [`ImageForm::AtMostOne`] when every image is empty or one
    ///   vertex and some is empty, and [`ImageForm::Larger`] otherwise; `cover`
    ///   says whether the images' union is the target's vertex set; `wires`
    ///   sorts `φ` as bijective, injective only, surjective only, or neither.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an identity, a deletion, a contraction, an inclusion
    ///   of the empty shape, a contraction missing a wire and an inclusion
    ///   beside a point, each read back to its hand-written form; together they
    ///   reach every arm of all three readings.
    /// - witness: `tests::maps::map_forms_read_back`
    #[inline]
    #[must_use]
    #[spec(ensures: |form| [
        match form.images {
            ImageForm::Singletons => self.images.iter().all(|image| usize::from(image.count()) == 1),
            ImageForm::AtMostOne => self.images.iter().all(|image| usize::from(image.count()) <= 1)
                && self.images.contains(&VertexSet::EMPTY),
            ImageForm::Larger => self.images.iter().any(|image| usize::from(image.count()) >= 2),
        },
        (form.cover == Membership::Inside) == (self.image_union() == VertexSet::below(target.vertex_count())),
        match form.wires {
            WireForm::Bijective => self.wires.len() == usize::from(target.wire_count()),
            WireForm::Injective => self.wires.len() < usize::from(target.wire_count()),
            WireForm::Surjective => self.wires.len() > usize::from(target.wire_count()),
            WireForm::Neither => true,
        },
    ])]
    pub fn form(
        &self,
        target: &Shape,
    ) -> MapForm
    {
        let images = if self
            .images
            .iter()
            .all(|image| usize::from(image.count()) == 1)
        {
            ImageForm::Singletons
        }
        else if self
            .images
            .iter()
            .all(|image| usize::from(image.count()) <= 1)
        {
            ImageForm::AtMostOne
        }
        else {
            ImageForm::Larger
        };
        let cover = if self.image_union() == VertexSet::below(target.vertex_count()) {
            Membership::Inside
        }
        else {
            Membership::Outside
        };
        let mut sorted: Vec<Wire> = self.wires.to_vec();
        sorted.sort_unstable();
        sorted.dedup();
        let injective = sorted.len() == self.wires.len();
        let surjective = self
            .wire_marks(target.graph())
            .iter()
            .all(|mark| *mark == Membership::Inside);
        let wires = match (injective, surjective) {
            | (true, true) => WireForm::Bijective,
            | (true, false) => WireForm::Injective,
            | (false, true) => WireForm::Surjective,
            | (false, false) => WireForm::Neither,
        };
        MapForm {
            images,
            cover,
            wires,
        }
    }
}

/// How a map's vertex images are sized.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ImageForm
{
    /// Every image is one vertex.
    Singletons,
    /// Every image is empty or one vertex, and some image is empty.
    AtMostOne,
    /// Some image has two or more vertices.
    Larger,
}

/// How a map's wire function behaves.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum WireForm
{
    /// A bijection onto the target's wires.
    Bijective,
    /// Injective and not onto.
    Injective,
    /// Onto and not injective: some fusion.
    Surjective,
    /// Neither injective nor onto.
    Neither,
}

/// A map's sizes of images and its wire function, read off against its
/// target.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct MapForm
{
    /// How the vertex images are sized.
    pub images: ImageForm,
    /// Whether the images cover the target's vertices.
    pub cover: Membership,
    /// How the wire function behaves.
    pub wires: WireForm,
}

impl fmt::Display for SiteMap
{
    /// Writes the vertex images and then the wire images:
    /// `S={0},{} φ=0,1`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str("S=")?;
        for (index, image) in self.images.iter().enumerate() {
            let separator = if index == 0 { "" } else { "," };
            write!(f, "{separator}{image}")?;
        }
        f.write_str(" φ=")?;
        for (index, wire) in self.wires.iter().enumerate() {
            let separator = if index == 0 { "" } else { "," };
            write!(f, "{separator}{}", usize::from(*wire))?;
        }
        Ok(())
    }
}

wrapper! {
    /// How many choices one position of an odometer has.
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    struct Choices(usize);
}

wrapper! {
    /// The choice one position of an odometer holds.
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    struct Choice(usize);
}

/// Where an odometer stands.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Progress
{
    /// The first reading has not been taken.
    Fresh,
    /// Some reading has been taken.
    Running,
    /// Every reading has been taken.
    Done,
}

/// A mixed-radix counter: every assignment of a choice below each
/// position's base, least position fastest.
struct Odometer
{
    /// Each position's number of choices.
    bases: Vec<Choices>,
    /// Each position's current choice.
    digits: Vec<Choice>,
    /// Where the counter stands.
    progress: Progress,
}

impl Odometer
{
    /// The counter over `bases`, empty when some base is zero.
    ///
    /// # Specification
    /// trivial.
    fn new(bases: Vec<Choices>) -> Self
    {
        let progress = if bases.iter().any(|base| usize::from(*base) == 0) {
            Progress::Done
        }
        else {
            Progress::Fresh
        };
        Self {
            digits: vec![Choice(0); bases.len()],
            bases,
            progress,
        }
    }

    /// Moves to the next reading.
    ///
    /// # Specification
    /// - ensures: the least position whose choice can grow grows by one and
    ///   every lesser position returns to zero; [`Progress::Done`] exactly when
    ///   no position could grow, every choice then back at zero.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the hom enumerator built on the counter agrees with
    ///   an independent brute force over every pair at the bound; a skipped or
    ///   repeated reading loses or doubles a map.
    /// - witness: `tests::maps::the_enumerator_agrees_with_brute_force`
    #[spec(ensures: |progress| (progress == Progress::Done) == self.digits.iter().all(|digit| digit.0 == 0))]
    fn advance(&mut self) -> Progress
    {
        for (digit, base) in self.digits.iter_mut().zip(self.bases.iter()) {
            let next = digit.0.saturating_add(1);
            if next < base.0 {
                digit.0 = next;
                return Progress::Running;
            }
            digit.0 = 0;
        }
        Progress::Done
    }
}

impl Iterator for Odometer
{
    type Item = Vec<Choice>;

    /// The next reading.
    ///
    /// # Specification
    /// - ensures: each reading has one choice per position, each below its
    ///   base; the first reading is every choice zero.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — as [`Odometer::advance`].
    /// - witness: `tests::maps::the_enumerator_agrees_with_brute_force`
    #[inline]
    #[spec(ensures: |ref reading| reading.as_ref().is_none_or(|choices| {
        choices.len() == self.bases.len() && choices.iter().zip(self.bases.iter()).all(|pair| pair.0.0 < pair.1.0)
    }))]
    fn next(&mut self) -> Option<Self::Item>
    {
        self.progress = match self.progress {
            | Progress::Done => return None,
            | Progress::Fresh => Progress::Running,
            | Progress::Running => self.advance(),
        };
        match self.progress {
            | Progress::Done => None,
            | Progress::Fresh | Progress::Running => Some(self.digits.clone()),
        }
    }
}

/// Every map of the class from `source` to `target`, in sorted order.
///
/// # Specification
/// - ensures: exactly the pairs `(S, φ)` [`SiteMap::validate`] accepts, each
///   once, in strictly increasing order.
/// - panics: none.
/// - intension: assigns each target vertex to one source vertex or to none,
///   discards assignments a vertex's arity rules out, offers each source wire
///   the target wires whose ends lie in its ends' images, and validates each
///   combination.
///
/// # Adequacy
/// - hypothesis: L2 — the counts of hand-checked pairs are pinned, and the
///   result equals a brute-force enumeration over every `(S, φ)` for every pair
///   of shapes at the bound.
/// - witness: `tests::maps::hom_counts_match_hand_counts`
/// - witness: `tests::maps::the_enumerator_agrees_with_brute_force`
#[inline]
#[must_use]
#[spec(ensures: |ref maps| [
    maps.iter().all(|map| map.validate(source, target).is_ok()),
    maps.iter().zip(maps.iter().skip(1)).all(|pair| pair.0 < pair.1),
])]
pub fn homs(
    source: &Shape,
    target: &Shape,
) -> Vec<SiteMap>
{
    let owners = usize::from(source.vertex_count()).saturating_add(1);
    let bases = vec![Choices(owners); usize::from(target.vertex_count())];
    let mut maps: Vec<SiteMap> = Vec::new();
    for assignment in Odometer::new(bases) {
        let images = images_from(&assignment, source.vertex_count());
        if plausible(source, target, &images) == Verdict::Fails {
            continue;
        }
        let candidates = wire_candidates(source, target, &images);
        let choices: Vec<Choices> = candidates.iter().map(|list| Choices(list.len())).collect();
        for picks in Odometer::new(choices) {
            let wires: Vec<Wire> = picks
                .iter()
                .zip(candidates.iter())
                .filter_map(|pair| pair.1.get(pair.0.0).copied())
                .collect();
            let map = SiteMap::new(images.clone(), wires);
            if map.validate(source, target).is_ok() {
                maps.push(map);
            }
        }
    }
    maps.sort_unstable();
    maps
}

/// The vertex images an owner assignment gives: target vertex `u` joins
/// the image of the source vertex it names, or no image when it names the
/// source's vertex count.
///
/// # Specification
/// - ensures: one image per source vertex, pairwise disjoint, whose union is
///   the target vertices assigned an owner below `sources`.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — the enumerator's agreement with the brute force, which
///   tries every image list, observes a lost or misplaced owner.
/// - witness: `tests::maps::the_enumerator_agrees_with_brute_force`
#[spec(ensures: |ref images| [
    images.len() == usize::from(sources),
    usize::from(images.iter().fold(VertexSet::EMPTY, |union, image| union.union(*image)).count())
        == assignment.iter().filter(|owner| owner.0 < usize::from(sources)).count(),
])]
fn images_from(
    assignment: &[Choice],
    sources: EdgeCount,
) -> Vec<VertexSet>
{
    let mut images = vec![VertexSet::EMPTY; usize::from(sources)];
    for (vertex, owner) in assignment.iter().enumerate() {
        if let Some(image) = images.get_mut(owner.0) {
            *image = image.union(VertexSet::single(Edge::from(vertex)));
        }
    }
    images
}

/// Whether every vertex's arity fits its image's boundary bounds: only a
/// point has an empty image, and a vertex consumes at least the wires
/// entering its image from outside and at most all wires consumed in it,
/// and likewise for production.
///
/// # Specification
/// - ensures: [`Verdict::Fails`] only when no wire function makes `images` a
///   map from `source` to `target`: a ported vertex with an empty image, or a
///   vertex whose arity on one side is below the wires entering its image from
///   outside or above all the wires its image touches on that side.
/// - panics: none.
/// - executable: none — the claim quantifies over every wire function; the
///   brute force, which never consults this pruning, observes a valid map it
///   wrongly discards.
///
/// # Adequacy
/// - hypothesis: L2 — the enumerator agrees with a brute force over every `(S,
///   φ)` at the bound, so a discarded valid image list loses maps.
/// - witness: `tests::maps::the_enumerator_agrees_with_brute_force`
fn plausible(
    source: &Shape,
    target: &Shape,
    images: &[VertexSet],
) -> Verdict
{
    let fits = source.vertices().zip(images.iter().copied()).all(|pair| {
        let (vertex, image) = pair;
        if image == VertexSet::EMPTY {
            return source.vertex_kind(vertex) == VertexKind::Point;
        }
        let consumes = source
            .ends()
            .iter()
            .filter(|ends| ends.consumer() == End::Vertex(vertex))
            .count();
        let produces = source
            .ends()
            .iter()
            .filter(|ends| ends.producer() == End::Vertex(vertex))
            .count();
        let inside = |end: End| image.holds_end(end) == Membership::Inside;
        let all_in = target
            .ends()
            .iter()
            .filter(|ends| inside(ends.consumer()))
            .count();
        let strict_in = target
            .ends()
            .iter()
            .filter(|ends| inside(ends.consumer()) && !inside(ends.producer()))
            .count();
        let all_out = target
            .ends()
            .iter()
            .filter(|ends| inside(ends.producer()))
            .count();
        let strict_out = target
            .ends()
            .iter()
            .filter(|ends| inside(ends.producer()) && !inside(ends.consumer()))
            .count();
        strict_in <= consumes && consumes <= all_in && strict_out <= produces && produces <= all_out
    });
    if fits { Verdict::Holds } else { Verdict::Fails }
}

/// The target wires each source wire may go to: a wire attached at an end
/// goes to a wire attached inside that end's image.
///
/// # Specification
/// - ensures: one list per source wire, in target wire order; every map with
///   these vertex images sends each source wire to a wire in its list.
/// - panics: none.
/// - executable: none — the claim quantifies over every valid map; the brute
///   force, which offers every target wire, observes a valid choice missing
///   here.
///
/// # Adequacy
/// - hypothesis: L2 — as [`plausible`]: a missing candidate loses a map the
///   brute force finds.
/// - witness: `tests::maps::the_enumerator_agrees_with_brute_force`
fn wire_candidates(
    source: &Shape,
    target: &Shape,
    images: &[VertexSet],
) -> Vec<Vec<Wire>>
{
    let image_of = |end: End| match end {
        | End::Open => None,
        | End::Vertex(vertex) => Some(
            images
                .get(usize::from(vertex))
                .copied()
                .unwrap_or(VertexSet::EMPTY),
        ),
    };
    let fits = |constraint: Option<VertexSet>, end: End| {
        constraint.is_none_or(|image| image.holds_end(end) == Membership::Inside)
    };
    source
        .ends()
        .iter()
        .map(|ends| {
            let producer = image_of(ends.producer());
            let consumer = image_of(ends.consumer());
            target
                .ends()
                .iter()
                .enumerate()
                .filter(|entry| {
                    fits(producer, entry.1.producer()) && fits(consumer, entry.1.consumer())
                })
                .map(|entry| Wire::from(entry.0))
                .collect()
        })
        .collect()
}
