//! The site at a size bound: every shape class of a family and every map
//! between two.
//!
//! A catalogue holds the shapes of one [`Family`], with every map of the class
//! between two of them: the full sub-site on the family's shapes. The
//! [`Family::Wirings`] are every stick-free wiring the carrier admits. The
//! [`Family::Chains`] are the chains of one vertex or more, the pasting schemes
//! of composable 1-cells, with the empty shape and the point. The
//! [`Family::Profiles`] are the shapes whose every vertex has one of a set of
//! profiles, with the empty shape and the point: the shapes a species
//! inhabiting those corollas can fill. [`SegalStratum::certify`] reads a
//! catalogue of any family alike.
//!
//! A catalogue carries its reach, the highest degree a stratum over it may
//! name. The wirings and the chains reach their top shape's degree. The
//! profiles reach the top degree of any wiring at the bound: above their own
//! top shape every wiring holds a vertex of another profile, where a species
//! inhabiting the profiles has no element.
//!
//! Shapes are enumerated up to the bound through `Wiring::assemble`, so the
//! carrier decides which shapes exist, and the constructors refuse a stick by
//! naming its wire. Maps between two shapes are enumerated by assigning target
//! vertices to source vertices and wires to wires, and each candidate passes
//! the one validator that states the class.
//!
//! # What a bound proves
//!
//! A shape's size is its vertices plus its wires. The enumeration at a bound is
//! exhaustive, so a hold proves the condition for every case whose shapes have
//! size at most the bound, and says nothing of larger shapes. The
//! factorization's middle is no larger than the map's source, and each
//! condition other than the pushout quantifies only over the shapes of its
//! case, so a failure there is a counter-example at every larger bound. The
//! pushout quantifies over all cocones, so its failure is the argument above,
//! which holds at every size. The catalogue orders classes by size and then by
//! key, pairs and triples by total size and then by index, and each condition
//! stops at its first failing case, so the counter-example it reports has the
//! least total size, ties broken by that order.
//!
//! The catalogue computes every hom set between every pair of classes, and the
//! closure check every composable pair over every triple, so the cost grows
//! with the square and the cube of the class count. Size five holds 81 classes
//! and runs every check in under half a minute in release; size six holds 223.
//! At size seven the wirings hold 631 classes and take about seven seconds to
//! build and certify at degree four; the chains hold 5 and take under a
//! millisecond. The magma's profiles `(2, 1)` and `(0, 1)` hold 11 and take
//! about twenty milliseconds to build and certify at degree seven. `W ≀ W` at
//! total size five builds in about twenty milliseconds, and its conditions run
//! in under a minute. The chain restriction at total size thirteen holds 114
//! objects and builds in under a tenth of a second; at seventeen it holds 530
//! and takes about ten seconds.
//!
//! [`SegalStratum::certify`]: crate::SegalStratum::certify

use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::vec;
use alloc::vec::Vec;

use anodized::spec;
use gandr_theory_circuit_algebras::Edge;
use gandr_theory_circuit_algebras::EdgeCount;
use gandr_theory_circuit_algebras::WireCount;
use quenchant_shape::shape::Maybe;

use crate::degree::Degree;
use crate::map::Membership;
use crate::map::SiteMap;
use crate::map::VertexSet;
use crate::map::homs;
use crate::shape::End;
use crate::shape::Shape;
use crate::shape::ShapeBudget;
use crate::shape::ShapeKey;
use crate::shape::ShapeObstruction;
use crate::shape::ShapeSize;
use crate::shape::WireKind;
use crate::shape::shapes_up_to;
use crate::stratum::PortCount;
use crate::stratum::Profile;

wrapper! {
    /// A shape's position in a catalogue.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct ShapeIndex(usize);
}

quenchant_shape::reason_enum! {
    /// Why a catalogue holds no shape at an index.
    pub mod shape_lookup {
        /// The reason the lookup finds no shape.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// The index is past the catalogue's last shape.
            OutOfRange,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a level holds no class for an object.
    pub mod shape_class {
        /// The reason the lookup finds no class.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// The object's class is larger than the bound of the level that
            /// would hold it.
            PastTheBound,
            /// The object lies outside the family of some level.
            OutsideTheFamily,
        }
    }
}

/// Which shapes a catalogue holds, and each level of a wreath.
///
/// # Specification
/// - provides: the family's membership test, which [`Level::find`] reads, one
///   level at a time, to name a class a level does not hold.
///
/// # Adequacy
/// - hypothesis: L3 — the 3-chain, the empty shape and the point lie in the
///   chains, and `C(2,1)`, the closed chain and two chains side by side do not;
///   a magma's shapes lie in its two profiles, and a shape holding a vertex of
///   another profile does not.
/// - witness: `tests::chains::the_chains_hold_the_chain_and_refuse_the_rest`
/// - witness: `tests::theta::a_cycle_at_the_outer_level_is_refused_by_name`
/// - witness: `tests::profiles::the_profiles_hold_the_shapes_their_corollas_fill`
///
/// [`Level::find`]: crate::Level::find
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Family
{
    /// Every stick-free wiring the carrier admits.
    Wirings,
    /// The chains of one vertex or more, the empty shape and the point. A
    /// chain of `n` vertices is the pasting scheme of `n` composable 1-cells.
    /// The empty shape is the external product's unit, and the point is the
    /// arity-zero corolla the [`corolla`](crate::corolla()) condition reads.
    Chains,
    /// The shapes whose every vertex has one of these profiles, the empty
    /// shape and the point. A species inhabiting only these corollas has no
    /// element at a shape outside them. The point is kept as the chains keep
    /// it, for the [`corolla`](crate::corolla()) condition.
    Profiles(BTreeSet<Profile>),
}

impl Family
{
    /// Whether `shape` lies in the family.
    ///
    /// # Specification
    /// - ensures: every shape lies in the wirings. A shape lies in the chains
    ///   when it has no wire and at most one vertex, or when it has one wire
    ///   more than vertices, one input leg, one output leg, and each vertex
    ///   consumes one wire and produces one. A shape lies in the profiles when
    ///   it has no wire and at most one vertex, or when each of its vertices
    ///   has one of them.
    /// - panics: none.
    /// - intension: one pass over the wires for the chains. An admitted shape
    ///   has no directed cycle, so those legs leave no vertex off the one path
    ///   from the open input to the open output. One pass over the wires per
    ///   vertex for the profiles.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as the type.
    /// - witness: `tests::chains::the_chains_hold_the_chain_and_refuse_the_rest`
    /// - witness: `tests::profiles::the_profiles_hold_the_shapes_their_corollas_fill`
    #[inline]
    #[must_use]
    #[spec(ensures: |ref membership| match *self {
        Self::Wirings => *membership == Membership::Inside,
        Self::Chains => *membership == Membership::Outside
            || (shape.ends().is_empty() && usize::from(shape.vertex_count()) <= 1)
            || shape.ends().len() == usize::from(shape.vertex_count()).saturating_add(1),
        Self::Profiles(ref profiles) => (*membership == Membership::Inside)
            == ((shape.ends().is_empty() && usize::from(shape.vertex_count()) <= 1)
                || (0 .. usize::from(shape.vertex_count())).all(|vertex| profiles.contains(&profile_at(shape, Edge::from(vertex))))),
    })]
    pub fn holds(
        &self,
        shape: &Shape,
    ) -> Membership
    {
        let vertices = shape.vertex_count();
        let alone = shape.ends().is_empty() && usize::from(vertices) <= 1;
        match *self {
            Self::Wirings => Membership::Inside,
            Self::Chains => {
                if alone {
                    return Membership::Inside;
                }
                let at = |end: End| match end {
                    End::Open => VertexSet::EMPTY,
                    End::Vertex(vertex) => VertexSet::single(vertex),
                };
                let (consumers, producers) = shape.ends().iter().fold(
                    (VertexSet::EMPTY, VertexSet::EMPTY),
                    |(consumers, producers), ends| {
                        (
                            consumers.union(at(ends.consumer())),
                            producers.union(at(ends.producer())),
                        )
                    },
                );
                let one = WireCount::from(1_usize);
                if shape.ends().len() == usize::from(vertices).saturating_add(1)
                    && shape.count_of(WireKind::InputLeg) == one
                    && shape.count_of(WireKind::OutputLeg) == one
                    && consumers.count() == vertices
                    && producers.count() == vertices
                {
                    Membership::Inside
                }
                else {
                    Membership::Outside
                }
            },
            Self::Profiles(ref profiles) => {
                if alone
                    || (0 .. usize::from(vertices))
                        .all(|vertex| profiles.contains(&profile_at(shape, Edge::from(vertex))))
                {
                    Membership::Inside
                }
                else {
                    Membership::Outside
                }
            },
        }
    }
}

/// The profile of `vertex` in `shape`: the wires it consumes and the wires it
/// produces, counted.
///
/// # Specification
/// - ensures: the counts of the wires whose consumer is `vertex` and of those
///   whose producer is, as [`Legs::of`](crate::stratum::Legs::of) lists them.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the magma's two corollas read as the binary and the
///   nullary profile, and a vertex of a third profile keeps its shape out.
/// - witness: `tests::profiles::the_profiles_hold_the_shapes_their_corollas_fill`
#[spec(ensures: |profile| profile == crate::stratum::Legs::of(shape, vertex).profile())]
fn profile_at(
    shape: &Shape,
    vertex: Edge,
) -> Profile
{
    let at = End::Vertex(vertex);
    let (inputs, outputs) =
        shape
            .ends()
            .iter()
            .fold((0_usize, 0_usize), |(inputs, outputs), ends| {
                (
                    inputs.saturating_add(usize::from(ends.consumer() == at)),
                    outputs.saturating_add(usize::from(ends.producer() == at)),
                )
            });
    Profile {
        inputs: PortCount::from(inputs),
        outputs: PortCount::from(outputs),
    }
}

quenchant_shape::reason_enum! {
    /// Why a catalogue holds no hom set for a pair of indices.
    pub mod hom_lookup {
        /// The reason the lookup finds no hom set.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// An index is past the catalogue's last shape.
            OutOfRange,
        }
    }
}

/// Every shape class of a family of size at most a bound, and every map of
/// the class between any two of them.
///
/// # Specification
/// - ensures: the shapes are the family's classes of [`shapes_up_to`] of the
///   bound, in its order, and the hom set of a pair is [`homs`] of the pair. No
///   shape's degree exceeds the reach.
/// - provides: the finite site the suites quantify over.
/// - panics: none.
/// - executable: none — a type carries no runtime predicate; the constructors'
///   postconditions check the counts they build.
///
/// # Adequacy
/// - hypothesis: L2 — a pinned hom count read through the catalogue, a
///   relabelled shape found at its class and the lookup refusals by variant;
///   the chains at a bound are the wiring catalogue's classes the family holds.
/// - witness: `tests::maps::the_catalogue_serves_pinned_hom_sets`
/// - witness: `tests::chains::the_chain_catalogue_is_the_full_sub_site_on_the_chains`
#[derive(Clone, Debug)]
pub struct Catalogue
{
    /// The family the shapes lie in.
    family: Family,
    /// The highest degree a stratum over the catalogue may name.
    reach: Degree,
    /// The shapes, one per class, ordered by size and key.
    shapes: Box<[Shape]>,
    /// Each class's index.
    classes: BTreeMap<ShapeKey, ShapeIndex>,
    /// The hom sets, row-major: source index times count plus target index.
    homs: Box<[Box<[SiteMap]>]>,
}

impl Catalogue
{
    /// The catalogue of the wirings at `bound`.
    ///
    /// # Specification
    /// - ensures: as the type states, one class index per shape.
    /// - fails: as [`shapes_up_to`] under [`ShapeBudget::EVERY`].
    /// - panics: none.
    /// - intension: one [`homs`] call per ordered pair of classes.
    ///
    /// # Errors
    /// Any [`ShapeObstruction`] [`shapes_up_to`] returns.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — as the type; every condition's case count at the
    ///   bound reads the hom sets built here.
    /// - witness: `tests::maps::the_catalogue_serves_pinned_hom_sets`
    /// - witness: `tests::reedy::the_class_is_a_category_with_two_classes`
    #[inline]
    #[spec(ensures: |ref result| result.as_ref().map_or(true, |catalogue| {
        catalogue.homs.len() == catalogue.shapes.len().saturating_mul(catalogue.shapes.len())
            && catalogue.classes.len() == catalogue.shapes.len()
            && catalogue.shapes.iter().all(|shape| shape.size() <= bound)
    }))]
    pub fn build(bound: ShapeSize) -> Result<Self, ShapeObstruction>
    {
        Self::within(bound, ShapeBudget::EVERY)
    }

    /// The catalogue of the wirings at `bound`, if it holds no more classes
    /// than `budget`.
    ///
    /// # Specification
    /// - ensures: as [`Catalogue::build`], and no more classes than `budget`.
    /// - fails: as [`shapes_up_to`], before any hom set is built.
    /// - panics: none.
    /// - intension: a bound past the budget costs the enumeration up to its
    ///   first class past the budget, and builds no hom set.
    ///
    /// # Errors
    /// Any [`ShapeObstruction`] [`shapes_up_to`] returns, and
    /// [`ShapeObstruction::PastTheBudget`] above all.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the 31 classes at bound four build under a budget of
    ///   31 and are refused under 30, naming 31 counted.
    /// - witness: `tests::shapes::the_enumeration_stops_at_the_first_class_past_its_budget`
    #[inline]
    #[spec(ensures: |ref result| result.as_ref().map_or(true, |catalogue| {
        catalogue.homs.len() == catalogue.shapes.len().saturating_mul(catalogue.shapes.len())
            && catalogue.classes.len() == catalogue.shapes.len()
            && catalogue.shapes.len() <= usize::from(budget)
            && catalogue.shapes.iter().all(|shape| shape.size() <= bound)
    }))]
    pub fn within(
        bound: ShapeSize,
        budget: ShapeBudget,
    ) -> Result<Self, ShapeObstruction>
    {
        let shapes = shapes_up_to(bound, budget)?;
        Ok(Self::of(Family::Wirings, Degree::top(&shapes), shapes))
    }

    /// The catalogue of the chains at `bound`: the empty shape, the point and
    /// each chain no larger than `bound`.
    ///
    /// # Specification
    /// - ensures: as the type states, every shape in [`Family::Chains`] and one
    ///   class index per shape.
    /// - fails: as [`Shape::chain`], a chain past 64 vertices within `bound`.
    /// - panics: none.
    /// - intension: the chain of `n` vertices has size `2n + 1`, so the bound
    ///   holds the chains to `(bound - 1) / 2` vertices.
    ///
    /// # Errors
    /// [`ShapeObstruction::TooManyVertices`] for a bound past 129.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — at size 7 the shapes are the wiring catalogue's
    ///   classes the family holds, with the same hom sets.
    /// - witness: `tests::chains::the_chain_catalogue_is_the_full_sub_site_on_the_chains`
    #[inline]
    #[spec(ensures: |ref result| result.as_ref().map_or(true, |catalogue| {
        catalogue.homs.len() == catalogue.shapes.len().saturating_mul(catalogue.shapes.len())
            && catalogue.classes.len() == catalogue.shapes.len()
            && catalogue.shapes.iter().all(|shape| shape.size() <= bound && Family::Chains.holds(shape) == Membership::Inside)
    }))]
    pub fn chains(bound: ShapeSize) -> Result<Self, ShapeObstruction>
    {
        let mut shapes = vec![
            Shape::default(),
            Shape::from_ends(EdgeCount::from(1_usize), Vec::new())?,
        ];
        let mut length = 1_usize;
        loop {
            let chain = Shape::chain(EdgeCount::from(length))?;
            if chain.size() > bound {
                break;
            }
            shapes.push(chain);
            length = length.saturating_add(1);
        }
        shapes.retain(|shape| shape.size() <= bound);
        let reach = Degree::top(&shapes);
        Ok(Self::of(Family::Chains, reach, shapes))
    }

    /// The catalogue of the shapes at `bound` whose every vertex has one of
    /// `profiles`, with the empty shape and the point: the full sub-site on
    /// them, reaching the degree of every wiring at `bound`.
    ///
    /// # Specification
    /// - ensures: as the type states, every shape in [`Family::Profiles`] of
    ///   `profiles` and one class index per shape; the shapes are the wiring
    ///   catalogue's classes at `bound` the family holds, in its order, and the
    ///   reach is the top degree among all those classes.
    /// - fails: as [`shapes_up_to`] under [`ShapeBudget::EVERY`].
    /// - panics: none.
    /// - intension: the wirings at `bound` are enumerated and filtered, and the
    ///   hom sets are built among the shapes kept alone, which is where the
    ///   cost lies.
    ///
    /// # Errors
    /// Any [`ShapeObstruction`] [`shapes_up_to`] returns.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — at size 5 the magma's shapes are the wiring
    ///   catalogue's classes the family holds, with the same hom sets; at size
    ///   7 its eleven shapes top out at degree five and it reaches seven.
    /// - witness: `tests::profiles::the_profile_catalogue_is_the_full_sub_site_on_its_shapes`
    #[inline]
    #[spec(ensures: |ref result| result.as_ref().map_or(true, |catalogue| {
        catalogue.homs.len() == catalogue.shapes.len().saturating_mul(catalogue.shapes.len())
            && catalogue.classes.len() == catalogue.shapes.len()
            && catalogue.shapes.iter().all(|shape| shape.size() <= bound && catalogue.family.holds(shape) == Membership::Inside)
    }))]
    pub fn profiles(
        bound: ShapeSize,
        profiles: BTreeSet<Profile>,
    ) -> Result<Self, ShapeObstruction>
    {
        let family = Family::Profiles(profiles);
        let mut shapes = shapes_up_to(bound, ShapeBudget::EVERY)?;
        let reach = Degree::top(&shapes);
        shapes.retain(|shape| family.holds(shape) == Membership::Inside);
        Ok(Self::of(family, reach, shapes))
    }

    /// The catalogue of `family` over `shapes`, one per class, ordered by size
    /// and key, reaching `reach`.
    ///
    /// # Specification
    /// - requires: `shapes` lie in `family`, one per class, ordered by size and
    ///   key, and none has a degree past `reach`.
    /// - ensures: one class index per shape and one hom set per ordered pair.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — as the type, through the three public builders.
    /// - witness: `tests::maps::the_catalogue_serves_pinned_hom_sets`
    /// - witness: `tests::chains::the_chain_catalogue_is_the_full_sub_site_on_the_chains`
    /// - witness: `tests::profiles::the_profile_catalogue_is_the_full_sub_site_on_its_shapes`
    #[spec(
        requires: shapes.iter().all(|shape| Degree::of(shape) <= reach),
        ensures: |ref catalogue| catalogue.homs.len() == catalogue.shapes.len().saturating_mul(catalogue.shapes.len())
            && catalogue.classes.len() == catalogue.shapes.len()
    )]
    fn of(
        family: Family,
        reach: Degree,
        shapes: Vec<Shape>,
    ) -> Self
    {
        let classes = shapes
            .iter()
            .enumerate()
            .map(|entry| (entry.1.key(), ShapeIndex(entry.0)))
            .collect();
        let mut sets: Vec<Box<[SiteMap]>> =
            Vec::with_capacity(shapes.len().saturating_mul(shapes.len()));
        for source in &shapes {
            for target in &shapes {
                sets.push(homs(source, target).into_boxed_slice());
            }
        }
        Self {
            family,
            reach,
            shapes: shapes.into_boxed_slice(),
            classes,
            homs: sets.into_boxed_slice(),
        }
    }

    /// The family the shapes lie in.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn family(&self) -> &Family
    {
        &self.family
    }

    /// The highest degree a stratum over the catalogue may name: its top
    /// shape's degree, or for the profiles the top degree of any wiring at
    /// the bound.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn reach(&self) -> Degree
    {
        self.reach
    }

    /// The shapes, ordered by size and key.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn shapes(&self) -> &[Shape]
    {
        &self.shapes
    }

    /// Every index with its shape, in order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn entries(&self) -> impl Iterator<Item = (ShapeIndex, &Shape)>
    {
        self.shapes
            .iter()
            .enumerate()
            .map(|entry| (ShapeIndex(entry.0), entry.1))
    }

    /// The shape at `index`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn shape(
        &self,
        index: ShapeIndex,
    ) -> Maybe<&Shape, shape_lookup::Absent>
    {
        self.shapes.get(index.0).map_or(
            Maybe::Absent(shape_lookup::Absent::OutOfRange),
            Maybe::Present,
        )
    }

    /// Each class's index, by its key.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    pub(crate) const fn classes(&self) -> &BTreeMap<ShapeKey, ShapeIndex>
    {
        &self.classes
    }

    /// The maps from the shape at `source` to the shape at `target`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn maps(
        &self,
        source: ShapeIndex,
        target: ShapeIndex,
    ) -> Maybe<&[SiteMap], hom_lookup::Absent>
    {
        let count = self.shapes.len();
        if source.0 >= count || target.0 >= count {
            return Maybe::Absent(hom_lookup::Absent::OutOfRange);
        }
        let position = source.0.saturating_mul(count).saturating_add(target.0);
        self.homs
            .get(position)
            .map_or(Maybe::Absent(hom_lookup::Absent::OutOfRange), |set| {
                Maybe::Present(set)
            })
    }
}
