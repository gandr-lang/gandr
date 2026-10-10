//! The site at a size bound: every shape class and every map between two.

use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use anodized::spec;
use quenchant_shape::shape::Maybe;

use crate::map::SiteMap;
use crate::map::homs;
use crate::shape::Shape;
use crate::shape::ShapeKey;
use crate::shape::ShapeObstruction;
use crate::shape::ShapeSize;
use crate::shape::shapes_up_to;

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
    /// Why a catalogue holds no class for a shape.
    pub mod shape_class {
        /// The reason the lookup finds no class.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// The shape's class is larger than the catalogue's bound.
            PastTheBound,
        }
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

/// Every shape class of size at most a bound, and every map of the class
/// between any two of them.
///
/// # Specification
/// - ensures: the shapes are [`shapes_up_to`] of the bound in its order, and
///   the hom set of a pair is [`homs`] of the pair.
/// - provides: the finite site the suites quantify over.
/// - panics: none.
/// - executable: none — a type carries no runtime predicate; the constructor's
///   postcondition checks the counts it builds.
///
/// # Adequacy
/// - hypothesis: L2 — a pinned hom count read through the catalogue, a
///   relabelled shape found at its class and the lookup refusals by variant.
/// - witness: `tests::maps::the_catalogue_serves_pinned_hom_sets`
#[derive(Clone, Debug)]
pub struct Catalogue
{
    /// The shapes, one per class, ordered by size and key.
    shapes: Box<[Shape]>,
    /// Each class's index.
    classes: BTreeMap<ShapeKey, ShapeIndex>,
    /// The hom sets, row-major: source index times count plus target index.
    homs: Box<[Box<[SiteMap]>]>,
}

impl Catalogue
{
    /// The catalogue at `bound`.
    ///
    /// # Specification
    /// - ensures: as the type states, one class index per shape.
    /// - fails: as [`shapes_up_to`].
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
        let shapes = shapes_up_to(bound)?;
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
        Ok(Self {
            shapes: shapes.into_boxed_slice(),
            classes,
            homs: sets.into_boxed_slice(),
        })
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
        match self.shapes.get(index.0) {
            | Some(shape) => Maybe::Present(shape),
            | None => Maybe::Absent(shape_lookup::Absent::OutOfRange),
        }
    }

    /// The index of `shape`'s class.
    ///
    /// # Specification
    /// - ensures: the index whose shape has `shape`'s key, when the class is
    ///   within the bound; absent exactly when no shape of the catalogue has
    ///   that key.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a relabelled shape found at its class and a shape
    ///   past the bound refused.
    /// - witness: `tests::maps::the_catalogue_serves_pinned_hom_sets`
    #[inline]
    #[spec(ensures: |ref answer| match *answer {
        Maybe::Present(index) => self.shapes.get(index.0).is_some_and(|found| found.key() == shape.key()),
        Maybe::Absent(_) => self.shapes.iter().all(|found| found.key() != shape.key()),
    })]
    pub fn find(
        &self,
        shape: &Shape,
    ) -> Maybe<ShapeIndex, shape_class::Absent>
    {
        match self.classes.get(&shape.key()) {
            | Some(index) => Maybe::Present(*index),
            | None => Maybe::Absent(shape_class::Absent::PastTheBound),
        }
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
        match self.homs.get(position) {
            | Some(set) => Maybe::Present(set),
            | None => Maybe::Absent(hom_lookup::Absent::OutOfRange),
        }
    }
}
