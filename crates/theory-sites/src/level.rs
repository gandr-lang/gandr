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
//! [`Site`]: crate::Site
//! [`Wreath`]: crate::Wreath

use core::fmt;

use anodized::spec;

use crate::catalogue::Catalogue;
use crate::catalogue::ShapeIndex;
use crate::degree::Degree;
use crate::map::CompositionMismatch;
use crate::map::Invertibility;
use crate::map::Membership;
use crate::map::SiteMap;
use crate::map::VertexSet;
use crate::shape::Shape;
use crate::shape::ShapeSize;

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
    fn hom(
        &self,
        source: ShapeIndex,
        target: ShapeIndex,
    ) -> &[Self::Map];

    /// The identity of `object`.
    ///
    /// # Specification
    /// trivial.
    fn identity(object: &Self::Object) -> Self::Map;

    /// `first`, then `next`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// - [`CompositionMismatch`]: `first`'s image names a vertex or wire `next`
    ///   has no image for.
    fn then(
        first: &Self::Map,
        next: &Self::Map,
    ) -> Result<Self::Map, CompositionMismatch>;

    /// Whether `map` is a map from `source` to `target`.
    ///
    /// # Specification
    /// trivial.
    fn admits(
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
    fn jointly_raising(family: &[&Self::Map]) -> Membership;

    /// Whether `map` is raising: the family of `map` alone is jointly
    /// raising.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn raising(map: &Self::Map) -> Membership
    {
        Self::jointly_raising(&[map])
    }

    /// Whether `map`, into `target`, is lowering.
    ///
    /// # Specification
    /// trivial.
    fn lowering(
        map: &Self::Map,
        target: &Self::Object,
    ) -> Membership;

    /// Whether `map`, into `target`, is an isomorphism.
    ///
    /// # Specification
    /// trivial.
    fn invertibility(
        map: &Self::Map,
        target: &Self::Object,
    ) -> Invertibility;

    /// The degree of `object`.
    ///
    /// # Specification
    /// trivial.
    fn degree(object: &Self::Object) -> Degree;

    /// The size of `object`, which the level's bound bounds.
    ///
    /// # Specification
    /// trivial.
    fn size(object: &Self::Object) -> ShapeSize;
}

impl Level for Catalogue
{
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

    /// [`SiteMap::identity`].
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn identity(object: &Shape) -> SiteMap
    {
        SiteMap::identity(object)
    }

    /// [`SiteMap::then`].
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn then(
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
    fn jointly_raising(family: &[&SiteMap]) -> Membership
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

    /// [`Shape::size`].
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn size(object: &Shape) -> ShapeSize
    {
        object.size()
    }
}
