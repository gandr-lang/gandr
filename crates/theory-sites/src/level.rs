//! A level: what the conditions read of a finite site, its objects at a bound,
//! its maps, their composition, the two classes and the degree.
//!
//! A [`Level`] holds one object per isomorphism class and every map between
//! two of them. Its objects and maps compose, sort into the raising and the
//! lowering class, and carry a degree and a size; the [`Site`] of a level reads
//! nothing else, so every condition stated over a site runs at any level. The
//! wiring [`Catalogue`] is level one. A [`Wreath`] over the wiring catalogue
//! and a level is the level above it, so level `k + 1` is the wreath over level
//! `k`. A family of maps out of one object is jointly raising when it factors
//! through no lowering map but an isomorphism: at level one, when the maps'
//! kernels meet in no point. A wreath map raises when its inner maps out of
//! each column are jointly raising, which is why the level states the joint
//! reading rather than the single one.
//!
//! A [`HomIndex`] names a map of a level by its hom set and its position
//! there. A wreath map keeps an index for its outer map and for each inner
//! map, never a copy, so a map lives once, in its hom set. The map operations
//! of a level take the level, so they read each map from its set, and
//! [`Level::then`] finds a composite by its index.
//!
//! [`Site`]: crate::Site
//! [`Wreath`]: crate::Wreath

use alloc::collections::BTreeMap;
use core::cmp::Ordering;
use core::fmt;
use core::hash::Hash;
use core::hash::Hasher;
use core::marker::PhantomData;

use anodized::spec;
use quenchant_shape::shape::Maybe;

use crate::catalogue::Catalogue;
use crate::catalogue::Family;
use crate::catalogue::ShapeIndex;
use crate::catalogue::shape_class;
use crate::degree::Degree;
use crate::map::CompositionMismatch;
use crate::map::Invertibility;
use crate::map::Membership;
use crate::map::SiteMap;
use crate::map::VertexSet;
use crate::shape::Shape;
use crate::shape::ShapeKey;
use crate::shape::ShapeSize;

wrapper! {
    /// A map's position in its hom set, which ascends.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct MapPosition(usize);
}

/// A map of a level, named by the hom set that holds it and its position
/// there.
///
/// # Specification
/// - provides: the name a [`crate::WreathMap`] keeps for its outer map and for
///   each inner map, in place of a copy; [`Level::map_at`] reads the map.
/// - ensures: only a level mints an index, from a hom set it holds, so an index
///   names one map of one set. Two indices into one set order as their maps do,
///   because each set ascends.
/// - executable: none — a type carries no runtime predicate; the minting
///   methods check each position against its set.
///
/// # Adequacy
/// - hypothesis: L2 — the wreath's maps, built from indices, keep the counts
///   and the conditions pinned at the bounds.
/// - witness: `tests::wreath::the_wreath_holds_one_object_per_class`
/// - witness: `tests::wreath::the_wreath_is_a_generalized_reedy_category`
pub struct HomIndex<Map>
{
    /// The index of the source object.
    source: ShapeIndex,
    /// The index of the target object.
    target: ShapeIndex,
    /// The position in the hom set from the source to the target.
    at: MapPosition,
    /// The type of the maps the hom set holds.
    map: PhantomData<fn() -> Map>,
}

impl<Map> HomIndex<Map>
{
    /// The index of the map's source object.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn source(&self) -> ShapeIndex
    {
        self.source
    }

    /// The index of the map's target object.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn target(&self) -> ShapeIndex
    {
        self.target
    }

    /// The map's position in its hom set.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn at(&self) -> MapPosition
    {
        self.at
    }

    /// The index of the map at `at` in the hom set from `source` to `target`,
    /// a position the caller has checked against the set.
    ///
    /// # Specification
    /// trivial.
    const fn minted(
        source: ShapeIndex,
        target: ShapeIndex,
        at: MapPosition,
    ) -> Self
    {
        Self {
            source,
            target,
            at,
            map: PhantomData,
        }
    }

    /// The two objects and the position, which order the index and tell it
    /// apart.
    ///
    /// # Specification
    /// trivial.
    const fn parts(&self) -> (ShapeIndex, ShapeIndex, MapPosition)
    {
        (self.source, self.target, self.at)
    }
}

impl<Map> Clone for HomIndex<Map>
{
    /// A copy of the index.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn clone(&self) -> Self
    {
        *self
    }
}

impl<Map> Copy for HomIndex<Map>
{
}

impl<Map> PartialEq for HomIndex<Map>
{
    /// Whether the two indices name one map of one hom set.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn eq(
        &self,
        other: &Self,
    ) -> bool
    {
        self.parts() == other.parts()
    }
}

impl<Map> Eq for HomIndex<Map>
{
}

impl<Map> PartialOrd for HomIndex<Map>
{
    /// The order of [`Ord`].
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn partial_cmp(
        &self,
        other: &Self,
    ) -> Option<Ordering>
    {
        Some(self.cmp(other))
    }
}

impl<Map> Ord for HomIndex<Map>
{
    /// By source, then target, then position: within one hom set, the order
    /// of the maps.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn cmp(
        &self,
        other: &Self,
    ) -> Ordering
    {
        self.parts().cmp(&other.parts())
    }
}

impl<Map> Hash for HomIndex<Map>
{
    /// Hashes the two objects and the position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn hash<H>(
        &self,
        state: &mut H,
    ) where
        H: Hasher,
    {
        self.parts().hash(state);
    }
}

impl<Map> fmt::Debug for HomIndex<Map>
{
    /// Writes the two objects and the position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.debug_struct("HomIndex")
            .field("source", &self.source)
            .field("target", &self.target)
            .field("at", &self.at)
            .finish()
    }
}

impl<Map> fmt::Display for HomIndex<Map>
{
    /// Writes `source→target#position`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(
            f,
            "{}→{}#{}",
            usize::from(self.source),
            usize::from(self.target),
            usize::from(self.at)
        )
    }
}

/// A finite site the conditions read: one object per isomorphism class at a
/// bound, every map between two of them, and the operations on both.
///
/// # Specification
/// - provides: the objects and hom sets a [`crate::Site`] indexes, and the
///   composition, identities, classes, degree and size its conditions read.
/// - requires: no two objects are isomorphic; each hom set ascends; `then` of a
///   map into an object and a map out of it is a map between the outer two.
pub trait Level
{
    /// An object, one per isomorphism class; the default is the empty
    /// object.
    type Object: Clone + Default + fmt::Debug + fmt::Display + Ord;
    /// An object's isomorphism class: two objects key alike exactly when an
    /// isomorphism carries one onto the other.
    type Key: Clone + fmt::Debug + Ord;
    /// A map between two objects.
    type Map: Clone + fmt::Debug + fmt::Display + Ord;

    /// The objects, one per isomorphism class.
    ///
    /// # Specification
    /// trivial.
    fn objects(&self) -> &[Self::Object];

    /// Every map from the object at `source` to the object at `target`,
    /// ascending; empty past the objects.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Clause cost
    /// - bound: one read of the hom set at its position among the pairs; no map
    ///   is built.
    fn hom(
        &self,
        source: ShapeIndex,
        target: ShapeIndex,
    ) -> &[Self::Map];

    /// The index of the map at `at` in the hom set from `source` to `target`;
    /// absent past the set.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn index_at(
        &self,
        source: ShapeIndex,
        target: ShapeIndex,
        at: MapPosition,
    ) -> Option<HomIndex<Self::Map>>
    {
        (usize::from(at) < self.hom(source, target).len())
            .then(|| HomIndex::minted(source, target, at))
    }

    /// The index of `map` in the hom set from `source` to `target`; absent
    /// when the set holds no map equal to it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn index_of(
        &self,
        source: ShapeIndex,
        target: ShapeIndex,
        map: &Self::Map,
    ) -> Option<HomIndex<Self::Map>>
    {
        self.hom(source, target)
            .binary_search(map)
            .ok()
            .map(|at| HomIndex::minted(source, target, MapPosition::from(at)))
    }

    /// The map `index` names; absent past its hom set.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn map_at(
        &self,
        index: HomIndex<Self::Map>,
    ) -> Option<&Self::Map>
    {
        self.hom(index.source, index.target)
            .get(usize::from(index.at))
    }

    /// The identity of the object at `at`; absent past the objects.
    ///
    /// # Specification
    /// trivial.
    fn identity(
        &self,
        at: ShapeIndex,
    ) -> Option<Self::Map>;

    /// `first`, then `next`. At a level whose maps keep indices, each part of
    /// the composite is found in its hom set by its index.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// - [`CompositionMismatch`]: `first`'s image names a vertex or wire `next`
    ///   has no image for.
    /// - [`CompositionMismatch::Unheld`]: no hom set of the level holds a part
    ///   of the composite.
    fn then(
        &self,
        first: &Self::Map,
        next: &Self::Map,
    ) -> Result<Self::Map, CompositionMismatch>;

    /// Whether `map` is a map from `source` to `target`.
    ///
    /// # Specification
    /// trivial.
    fn admits(
        &self,
        map: &Self::Map,
        source: &Self::Object,
        target: &Self::Object,
    ) -> Membership;

    /// Whether `family`, maps out of one object, factors through no lowering
    /// map but an isomorphism; the empty family names no source and is
    /// outside.
    ///
    /// # Specification
    /// trivial.
    fn jointly_raising(
        &self,
        family: &[&Self::Map],
    ) -> Membership;

    /// Whether `map` is raising: the family of `map` alone is jointly
    /// raising.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn raising(
        &self,
        map: &Self::Map,
    ) -> Membership
    {
        self.jointly_raising(&[map])
    }

    /// Whether `map`, into `target`, is lowering.
    ///
    /// # Specification
    /// trivial.
    fn lowering(
        &self,
        map: &Self::Map,
        target: &Self::Object,
    ) -> Membership;

    /// Whether `map`, into `target`, is an isomorphism.
    ///
    /// # Specification
    /// trivial.
    fn invertibility(
        &self,
        map: &Self::Map,
        target: &Self::Object,
    ) -> Invertibility;

    /// The degree of `object`.
    ///
    /// # Specification
    /// trivial.
    fn degree(object: &Self::Object) -> Degree;

    /// Whether `object` is grounded: no shape of it, at any level, holds a
    /// point. An empty shape is grounded, so an outer vertex carrying the
    /// empty column keeps its object.
    ///
    /// # Specification
    /// trivial.
    fn grounded(object: &Self::Object) -> Membership;

    /// The size of `object`, which the level's bound bounds.
    ///
    /// # Specification
    /// trivial.
    fn size(object: &Self::Object) -> ShapeSize;

    /// The families the level's objects lie in, one per level, outermost
    /// first.
    ///
    /// # Specification
    /// trivial.
    fn families(&self) -> &[Family];

    /// Whether `object` lies in `families`, outermost first: its shape at
    /// each level in that level's family.
    ///
    /// # Specification
    /// trivial.
    fn lies_in(
        families: &[Family],
        object: &Self::Object,
    ) -> Membership;

    /// The isomorphism class of `object`.
    ///
    /// # Specification
    /// trivial.
    fn key(object: &Self::Object) -> Self::Key;

    /// Each class's index, by its key.
    ///
    /// # Specification
    /// trivial.
    fn class_index(&self) -> &BTreeMap<Self::Key, ShapeIndex>;

    /// The index of `object`'s class: absent as outside the family when it
    /// does not lie in [`Level::families`], and as past the bound otherwise.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn find(
        &self,
        object: &Self::Object,
    ) -> Maybe<ShapeIndex, shape_class::Absent>
    {
        found(self, object)
    }
}

/// The index of `object`'s class at `level`, the lookup every level shares.
///
/// # Specification
/// - ensures: the index of the object keyed as `object` is; absent exactly when
///   no object keys alike, as outside the family when `object` does not lie in
///   the level's families and as past the bound otherwise.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a relabelled shape and Θ₂'s objects found at their
///   classes, a shape and a Θ₂ object past the bound refused as such, and
///   `C(2,1)`, an outer bigon and a bigon column refused as outside the chains.
///   Each level keys every object it lists in its class index, one entry each,
///   so the predicate reads absence from that index.
/// - witness: `tests::maps::the_catalogue_serves_pinned_hom_sets`
/// - witness: `tests::chains::the_chains_hold_the_chain_and_refuse_the_rest`
/// - witness: `tests::theta::the_chain_restriction_holds_theta_two_at_the_bound`
/// - witness: `tests::theta::the_chain_restriction_is_the_full_sub_site_of_the_wreath`
/// - witness: `tests::theta::a_cycle_at_the_outer_level_is_refused_by_name`
#[spec(ensures: |ref answer| match *answer {
    Maybe::Present(index) => level.objects().get(usize::from(index))
        .is_some_and(|held| L::key(held) == L::key(object)),
    Maybe::Absent(reason) => !level.class_index().contains_key(&L::key(object))
        && (reason == shape_class::Absent::OutsideTheFamily)
            == (L::lies_in(level.families(), object) == Membership::Outside),
})]
fn found<L>(
    level: &L,
    object: &L::Object,
) -> Maybe<ShapeIndex, shape_class::Absent>
where
    L: Level + ?Sized,
{
    if let Some(index) = level.class_index().get(&L::key(object)) {
        return Maybe::Present(*index);
    }
    Maybe::Absent(match L::lies_in(level.families(), object) {
        Membership::Inside => shape_class::Absent::PastTheBound,
        Membership::Outside => shape_class::Absent::OutsideTheFamily,
    })
}

impl Level for Catalogue
{
    type Key = ShapeKey;
    type Map = SiteMap;
    type Object = Shape;

    /// The catalogue's shapes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn objects(&self) -> &[Shape]
    {
        self.shapes()
    }

    /// The catalogue's hom set, empty past its shapes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn hom(
        &self,
        source: ShapeIndex,
        target: ShapeIndex,
    ) -> &[SiteMap]
    {
        match self.maps(source, target) {
            quenchant_shape::shape::Maybe::Present(maps) => maps,
            quenchant_shape::shape::Maybe::Absent(_) => &[],
        }
    }

    /// [`SiteMap::identity`] of the shape at `at`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn identity(
        &self,
        at: ShapeIndex,
    ) -> Option<SiteMap>
    {
        self.shapes().get(usize::from(at)).map(SiteMap::identity)
    }

    /// [`SiteMap::then`].
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn then(
        &self,
        first: &SiteMap,
        next: &SiteMap,
    ) -> Result<SiteMap, CompositionMismatch>
    {
        first.then(next)
    }

    /// Whether [`SiteMap::validate`] admits the map.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn admits(
        &self,
        map: &SiteMap,
        source: &Shape,
        target: &Shape,
    ) -> Membership
    {
        if map.validate(source, target).is_ok() {
            Membership::Inside
        }
        else {
            Membership::Outside
        }
    }

    /// Whether the family's kernels meet in no point: a common point of the
    /// kernels is a deletion every map of the family factors through.
    ///
    /// # Specification
    /// - ensures: inside exactly when the family is non-empty and the
    ///   intersection of its kernels is empty.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the wreath's raising class reads it at every column,
    ///   and its conditions are pinned at the bound.
    /// - witness: `tests::wreath::the_wreath_is_a_generalized_reedy_category`
    #[inline]
    #[spec(ensures: |answer| (answer == Membership::Inside) == (!family.is_empty()
        && family.iter().fold(None, |meet: Option<VertexSet>, map| Some(meet.map_or_else(|| map.kernel(), |meet| meet.intersection(map.kernel())))) == Some(VertexSet::EMPTY)))]
    fn jointly_raising(
        &self,
        family: &[&SiteMap],
    ) -> Membership
    {
        let meet = family
            .iter()
            .map(|map| map.kernel())
            .reduce(VertexSet::intersection);
        if meet == Some(VertexSet::EMPTY) {
            Membership::Inside
        }
        else {
            Membership::Outside
        }
    }

    /// [`SiteMap::lowering`].
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn lowering(
        &self,
        map: &SiteMap,
        target: &Shape,
    ) -> Membership
    {
        map.lowering(target)
    }

    /// [`SiteMap::invertibility`].
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn invertibility(
        &self,
        map: &SiteMap,
        target: &Shape,
    ) -> Invertibility
    {
        map.invertibility(target)
    }

    /// [`Degree::of`].
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn degree(object: &Shape) -> Degree
    {
        Degree::of(object)
    }

    /// Whether the shape holds no point.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn grounded(object: &Shape) -> Membership
    {
        if usize::from(object.point_count()) == 0 {
            Membership::Inside
        }
        else {
            Membership::Outside
        }
    }

    /// [`Shape::size`].
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn size(object: &Shape) -> ShapeSize
    {
        object.size()
    }

    /// The catalogue's one family, as a slice of one.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn families(&self) -> &[Family]
    {
        core::slice::from_ref(self.family())
    }

    /// Whether the first of `families` holds `object`; outside when there is
    /// none.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn lies_in(
        families: &[Family],
        object: &Shape,
    ) -> Membership
    {
        families
            .first()
            .map_or(Membership::Outside, |family| family.holds(object))
    }

    /// [`Shape::key`].
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn key(object: &Shape) -> ShapeKey
    {
        object.key()
    }

    /// The catalogue's class index.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn class_index(&self) -> &BTreeMap<ShapeKey, ShapeIndex>
    {
        self.classes()
    }
}
