//! The wreath of the wiring site over a level: an outer shape whose vertices
//! each carry an object of the level, the next level of the site.
//!
//! A [`WreathShape`] is an outer shape of the wiring site with one inner object
//! per outer vertex. Its vertices are the cells of the higher dimension, and
//! the inner objects the pasting diagrams each cell spans; a vertex carrying
//! the empty shape is a whisker, the external product's unit, and no level
//! holds a stick. A [`WreathMap`] sends the outer shape by a site map and each
//! inner object by one inner map to each vertex of that outer vertex's image:
//! the wreath over the vertex functor, which reads a shape as its vertex set
//! and a map as its vertex assignment. Composition follows the images, through
//! the one middle vertex whose image holds the end. The degree is the outer
//! degree plus the inner degrees, the size the outer size plus the inner
//! sizes. A wreath map is raising when its outer map is and, at each source
//! vertex, its inner maps are jointly raising, so one inner map may delete a
//! point another keeps; it is lowering when its outer map and every inner map
//! are. A [`Wreath`] is a [`Level`], so the conditions run over it and a wreath
//! may carry another.
//!
//! An object keys by its class: the least, over the orders of its outer
//! vertices, of the relabelled outer ends with the columns' keys in that order.
//! [`Level::find`] reads the key, so it finds an object written in any vertex
//! order. It names an object it does not hold as outside the family when some
//! level's shape lies outside that level's family, and as past the bound
//! otherwise.
//!
//! The chain restriction wreathes the chain catalogue over the chain
//! restriction one level down; at level one it is the chain catalogue. Its
//! objects are Θₙ's: `[n](m_1, …, m_n)` is the outer chain of `n` vertices
//! carrying the chain of `m_i` vertices at vertex `i`, or the empty shape when
//! `m_i` is zero, and the 0-cell is an outer wire. Its maps are the site's,
//! fewer than Θₙ's: faces only, with the empty column initial.
//!
//! # The two units, one level up
//!
//! Inside a column whose inner shape is empty, a span of two lowering maps has
//! the empty object as its pushout, and the pushed-out map lowers
//! (`tests::wreath::a_column_pushes_out_only_by_deleting_its_vertex`).
//!
//! The finding is the site's two-units distinction at the wreath level. At
//! level one the stick, the contraction unit, is refused as an object, since
//! no degree exists with it. The empty diagram, the external product's unit,
//! stays. Its one shadow among shapes is the isolated point. The point's
//! deletion is the one codegeneracy the class keeps, and `Grounded` fences it.
//! At level two the empty inner shape sits on an outer vertex and reads as an
//! identity 1-cell. The external product's unit of level one is the
//! contraction unit of level two. Its deletion is the level-two point
//! deletion, and the failing pushout is a span of two such deletions
//! collapsing to the empty object. Level two cannot refuse that object, since
//! it is the whisker, which the probe certifies. So the level-two answer is
//! the `Grounded` move, fencing the degeneracy and keeping the object, never
//! the stick move.
//!
//! The level-two unit is a fat object. The site does not drop it, which is the
//! stick move. The site does not read it as an identity map, which is the
//! Eilenberg-Zilber move. It is an object of a direct category, and the nerve
//! theorem characterises its Segal condition. That is the `Grounded` move,
//! now with a published nerve theorem (de Jong, Kraus, Paoli and Pradal 2026,
//! Theorems 4.22 and 4.23). Its proof machinery, monads with arities, is the
//! machinery the vault already uses for the circuit nerve.
//!
//! # One site, two uses
//!
//! One site serves two uses. The wiring site indexes the ambient model, where
//! a type is a diagram over the arities and a higher cell is an identity type.
//! The same site, under the wreath, indexes the cells. There the Segal
//! condition at a level certifies the composite over a pasting shape. The two
//! uses coincide at level one, because a 1-pasting is a wiring of 1-cells and
//! the chains are Δ. The univalence warrant is Shulman's inverse EI theorem
//! over the level-one site. A wreath level inherits it only through directness
//! with automorphisms, which the level's certificate re-derives from the level
//! below. This site drops Eilenberg-Zilber. So Berger and Moerdijk's wreath
//! theorem is not the warrant.
//!
//! # References
//!
//! - `Berger-2007-iterated_wreath_product_simplex_category_iterated_loop_spaces`
//!   — lineage: the wreath over a category over Γ (Definition 3.1, Remark
//!   3.4), Θₙ as the iterated wreath of Δ (Definition 3.3), with the dimension
//!   `m + Σ dim A_i` and the two classes (Proposition 3.14).
//! - `vault:01a1897b-d199-7d10-a325-587b76db2508` — lineage: § The design, the
//!   iterated site — one site under the wreath product, the stick refused at
//!   each level and the empty inner shape kept.
//! - `deJong-2026-study_kocks_fat_delta` — background: Theorems 4.22 and 4.23,
//!   the fat Δ as relative semiordinals, a direct category whose nerve theorem
//!   characterises its Segal condition.
//! - `Shulman-2017-univalence_inverse_ei_diagrams` — background: the univalent
//!   universe over inverse EI diagrams, the level-one warrant.

use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::vec;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
use gandr_theory_circuit_algebras::Edge;
use gandr_theory_circuit_algebras::EdgeCount;

use crate::catalogue::Catalogue;
use crate::catalogue::Family;
use crate::catalogue::ShapeIndex;
use crate::degree::Degree;
use crate::level::Level;
use crate::map::CompositionMismatch;
use crate::map::Invertibility;
use crate::map::Membership;
use crate::map::SiteMap;
use crate::map::VertexSet;
use crate::shape::Ends;
use crate::shape::Shape;
use crate::shape::ShapeSize;
use crate::shape::VertexOrders;

/// An object of a wreath: an outer shape, and one inner object per outer
/// vertex, in vertex order; the default is the empty outer shape.
#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct WreathShape<Object>
{
    /// The outer shape.
    outer: Shape,
    /// The inner objects, one per outer vertex.
    columns: Box<[Object]>,
}

impl<Object> WreathShape<Object>
{
    /// The object over `outer` carrying `columns`, one per outer vertex, in
    /// vertex order.
    ///
    /// # Specification
    /// - ensures: the object holds `outer` and `columns`, in order.
    /// - fails: [`WreathShapeObstruction::Columns`] when the columns are not
    ///   one per outer vertex.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`WreathShapeObstruction::Columns`]: the column count differs from the
    ///   outer vertex count.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — Θ₂'s objects built here are found at their classes,
    ///   and a column short is refused with both counts.
    /// - witness: `tests::theta::the_chain_restriction_holds_theta_two_at_the_bound`
    /// - witness: `tests::theta::a_cycle_at_the_outer_level_is_refused_by_name`
    #[inline]
    #[spec(ensures: |ref result| match *result {
        Ok(ref object) => object.columns.len() == usize::from(object.outer.vertex_count()),
        Err(WreathShapeObstruction::Columns { vertices, columns }) => vertices != columns,
    })]
    pub fn new(
        outer: Shape,
        columns: Vec<Object>,
    ) -> Result<Self, WreathShapeObstruction>
    {
        let vertices = outer.vertex_count();
        if columns.len() != usize::from(vertices) {
            return Err(WreathShapeObstruction::Columns {
                vertices,
                columns: EdgeCount::from(columns.len()),
            });
        }
        Ok(Self {
            outer,
            columns: columns.into_boxed_slice(),
        })
    }

    /// The outer shape.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn outer(&self) -> &Shape
    {
        &self.outer
    }

    /// The inner objects, one per outer vertex, in vertex order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn columns(&self) -> &[Object]
    {
        &self.columns
    }
}

impl<Object> fmt::Display for WreathShape<Object>
where
    Object: fmt::Display,
{
    /// Writes the outer shape, then the inner objects in angle brackets,
    /// separated by `|`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(f, "{} ⟨", self.outer)?;
        for (position, column) in self.columns.iter().enumerate() {
            let separator = if position == 0 { "" } else { " | " };
            write!(f, "{separator}{column}")?;
        }
        f.write_str("⟩")
    }
}

/// Why no wreath object stands over an outer shape and its columns.
///
/// # Specification
/// - provides: the refusal [`WreathShape::new`] names, with both counts.
/// - executable: none — a type-level block has no body and no call boundary to
///   check.
///
/// # Adequacy
/// - hypothesis: L3 — a column short is refused with both counts.
/// - witness: `tests::theta::a_cycle_at_the_outer_level_is_refused_by_name`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum WreathShapeObstruction
{
    /// The columns are not one per outer vertex.
    Columns
    {
        /// The outer vertex count.
        vertices: EdgeCount,
        /// The column count given.
        columns: EdgeCount,
    },
}

impl fmt::Display for WreathShapeObstruction
{
    /// Names the refusal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::Columns { vertices, columns } => write!(
                f,
                "{} columns over {} outer vertices",
                usize::from(columns),
                usize::from(vertices)
            ),
        }
    }
}

impl core::error::Error for WreathShapeObstruction
{
}

/// A wreath object's isomorphism class: the least, over the orders of its
/// outer vertices, of the relabelled outer ends with the columns' keys in that
/// order.
///
/// # Specification
/// - provides: the class [`Level::find`] looks an object up by, so two objects
///   share a key exactly when an outer automorphism with inner isomorphisms
///   carries one to the other.
/// - executable: none — a type-level block has no body and no call boundary to
///   check.
///
/// # Adequacy
/// - hypothesis: L3 — both column orders over a pair of points share one key.
/// - witness: `tests::wreath::the_wreath_holds_one_object_per_class`
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct WreathKey<Key>
{
    /// How many outer vertices the class's objects have.
    vertices: EdgeCount,
    /// The sorted outer wire ends under the least vertex order.
    ends: Box<[Ends]>,
    /// The columns' keys under that order.
    columns: Box<[Key]>,
}

/// One source vertex's inner maps, each with the image vertex it maps to.
type Column<Map> = Box<[(Edge, Map)]>;

/// A map of a wreath: an outer map and, for each source vertex, one inner map
/// to each vertex of its image, in vertex order.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct WreathMap<Map>
{
    /// The outer map.
    outer: SiteMap,
    /// Per source vertex, each image vertex with the inner map to it.
    columns: Box<[Column<Map>]>,
}

impl<Map> WreathMap<Map>
{
    /// The outer map.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn outer(&self) -> &SiteMap
    {
        &self.outer
    }

    /// The inner maps out of the source's column at `vertex`, each with the
    /// image vertex it maps to; empty past the source's vertices.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn column(
        &self,
        vertex: Edge,
    ) -> &[(Edge, Map)]
    {
        self.columns
            .get(usize::from(vertex))
            .map_or(&[], |column| &**column)
    }
}

impl<Map> fmt::Display for WreathMap<Map>
where
    Map: fmt::Display,
{
    /// Writes the outer map, then each source vertex's inner maps in angle
    /// brackets as `v→w map`, columns separated by `|`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(f, "{} ⟨", self.outer)?;
        for (vertex, column) in self.columns.iter().enumerate() {
            if vertex != 0 {
                f.write_str(" | ")?;
            }
            for (position, entry) in column.iter().enumerate() {
                let separator = if position == 0 { "" } else { ", " };
                write!(
                    f,
                    "{separator}{vertex}→{} {}",
                    usize::from(entry.0),
                    entry.1
                )?;
            }
        }
        f.write_str("⟩")
    }
}

/// The wreath of the wiring site over a level at a bound: every object of
/// total size at most the bound, one per isomorphism class, and every map
/// between two of them.
///
/// # Specification
/// - ensures: the objects are the classes whose outer shape the outer catalogue
///   holds and whose inner objects the inner level holds, two objects one class
///   when an outer automorphism carries one's inner objects onto the other's;
///   ordered by total size, then by outer index and inner indices, each keyed
///   by its class. The hom set of a pair is every outer map with every choice
///   of inner maps, ascending. The families are the outer catalogue's, then the
///   inner level's.
/// - panics: none.
/// - executable: none — a type carries no runtime predicate; the constructor's
///   postcondition checks its counts and bound.
///
/// # Adequacy
/// - hypothesis: L2 — the object and map counts are pinned at two bounds, and
///   the two orders of a pair of points' columns are one object.
/// - witness: `tests::wreath::the_wreath_holds_one_object_per_class`
#[derive(Clone, Debug)]
pub struct Wreath<Inner: Level>
{
    /// The objects, one per class.
    objects: Box<[WreathShape<Inner::Object>]>,
    /// Each class's index, by its key.
    classes: BTreeMap<WreathKey<Inner::Key>, ShapeIndex>,
    /// The families the objects lie in, one per level, outermost first.
    families: Box<[Family]>,
    /// The hom sets, row-major: source index times count plus target index.
    homs: Box<[HomSet<Inner::Map>]>,
}

/// An object as its outer shape's index and its columns' indices.
type Class = (ShapeIndex, Box<[ShapeIndex]>);

/// The maps between two objects, ascending.
type HomSet<Map> = Box<[WreathMap<Map>]>;

impl<Inner: Level> Wreath<Inner>
{
    /// The wreath of the wiring site's `outer` catalogue over `inner`, every
    /// object of total size at most `bound`.
    ///
    /// # Specification
    /// - ensures: every object's total size is at most `bound`, the sizes
    ///   ascend, each object keys apart from the others, and there is one hom
    ///   set per ordered pair of objects.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the counts at total sizes three and four are the
    ///   probe's, 19 objects with 537 maps and 65 with 6707.
    /// - witness: `tests::wreath::the_wreath_holds_one_object_per_class`
    #[inline]
    #[must_use]
    #[spec(ensures: |ref wreath| [
        wreath.objects.iter().all(|object| Self::size(object) <= bound),
        wreath.objects.windows(2).all(|pair| pair.first().map(Self::size) <= pair.get(1).map(Self::size)),
        wreath.classes.len() == wreath.objects.len(),
        wreath.homs.len() == wreath.objects.len().saturating_mul(wreath.objects.len()),
    ])]
    pub fn build(
        outer: &Catalogue,
        inner: &Inner,
        bound: ShapeSize,
    ) -> Self
    {
        let classes = Self::classes(outer, inner, bound);
        let objects: Box<[WreathShape<Inner::Object>]> = classes
            .iter()
            .filter_map(|class| {
                let outer_shape = outer.shapes().get(usize::from(class.0))?.clone();
                let columns = class
                    .1
                    .iter()
                    .filter_map(|column| inner.objects().get(usize::from(*column)).cloned())
                    .collect();
                Some(WreathShape {
                    outer: outer_shape,
                    columns,
                })
            })
            .collect();
        let mut homs: Vec<HomSet<Inner::Map>> =
            Vec::with_capacity(classes.len().saturating_mul(classes.len()));
        for source in &classes {
            for target in &classes {
                homs.push(Self::maps_between(outer, inner, source, target));
            }
        }
        let keys = objects
            .iter()
            .enumerate()
            .map(|(index, object)| (<Self as Level>::key(object), ShapeIndex::from(index)))
            .collect();
        let families = core::iter::once(outer.family().clone())
            .chain(inner.families().iter().cloned())
            .collect();
        Self {
            objects,
            classes: keys,
            families,
            homs: homs.into_boxed_slice(),
        }
    }

    /// The classes of total size at most `bound`, each in its least form
    /// under the outer automorphisms, ordered by total size and then by
    /// index.
    ///
    /// # Specification
    /// trivial.
    fn classes(
        outer: &Catalogue,
        inner: &Inner,
        bound: ShapeSize,
    ) -> Vec<Class>
    {
        let sizes: Vec<ShapeSize> = inner.objects().iter().map(Inner::size).collect();
        let mut found: BTreeSet<(ShapeSize, Class)> = BTreeSet::new();
        let mut automorphisms: Vec<Vec<Edge>> = Vec::new();
        let mut tuples: Vec<Vec<ShapeIndex>> = Vec::new();
        for (index, shape) in outer.entries() {
            let Some(rest) = usize::from(bound).checked_sub(usize::from(shape.size()))
            else {
                continue;
            };
            automorphisms.clear();
            automorphisms.extend(
                <Catalogue as Level>::hom(outer, index, index)
                    .iter()
                    .filter(|map| map.invertibility(shape) == Invertibility::Invertible)
                    .map(|map| {
                        shape
                            .vertices()
                            .filter_map(|vertex| map.image(vertex).members().next())
                            .collect()
                    }),
            );
            within(
                (&sizes, shape.vertex_count()),
                ShapeSize::from(rest),
                &mut tuples,
            );
            for tuple in &tuples {
                let least = automorphisms
                    .iter()
                    .map(|permutation| {
                        let mut moved = tuple.clone();
                        for (vertex, column) in permutation.iter().zip(tuple) {
                            if let Some(slot) = moved.get_mut(usize::from(*vertex)) {
                                *slot = *column;
                            }
                        }
                        moved
                    })
                    .min()
                    .unwrap_or_else(|| tuple.clone());
                let total = least
                    .iter()
                    .filter_map(|column| sizes.get(usize::from(*column)))
                    .fold(usize::from(shape.size()), |sum, size| {
                        sum.saturating_add(usize::from(*size))
                    });
                found.insert((ShapeSize::from(total), (index, least.into_boxed_slice())));
            }
        }
        found.into_iter().map(|(_, class)| class).collect()
    }

    /// Every map from the class `source` to the class `target`, ascending.
    ///
    /// # Specification
    /// trivial.
    fn maps_between(
        outer: &Catalogue,
        inner: &Inner,
        source: &Class,
        target: &Class,
    ) -> HomSet<Inner::Map>
    {
        let (source_columns, target_columns) = (&source.1, &target.1);
        let mut found: Vec<WreathMap<Inner::Map>> = Vec::new();
        let mut slots: Vec<(Edge, Edge, &[Inner::Map])> = Vec::new();
        let mut choice: Vec<ShapeIndex> = Vec::new();
        for map in <Catalogue as Level>::hom(outer, source.0, target.0) {
            slots.clear();
            slots.extend(
                source_columns
                    .iter()
                    .enumerate()
                    .flat_map(|(vertex, column)| {
                        map.image(Edge::from(vertex)).members().map(move |end| {
                            let options = target_columns
                                .get(usize::from(end))
                                .map_or(&[][..], |target| inner.hom(*column, *target));
                            (Edge::from(vertex), end, options)
                        })
                    }),
            );
            if slots.iter().any(|slot| slot.2.is_empty()) {
                continue;
            }
            choice.clear();
            choice.resize(slots.len(), ShapeIndex::from(0));
            loop {
                let mut columns: Vec<Vec<(Edge, Inner::Map)>> =
                    vec![Vec::new(); source_columns.len()];
                for (&(vertex, end, options), &picked) in slots.iter().zip(&choice) {
                    if let (Some(column), Some(chosen)) = (
                        columns.get_mut(usize::from(vertex)),
                        options.get(usize::from(picked)),
                    ) {
                        column.push((end, chosen.clone()));
                    }
                }
                found.push(WreathMap {
                    outer: map.clone(),
                    columns: columns.into_iter().map(Vec::into_boxed_slice).collect(),
                });
                if advance(&mut choice, &slots) == Membership::Outside {
                    break;
                }
            }
        }
        found.sort();
        found.into_boxed_slice()
    }
}

/// Into `out`, every tuple of inner indices, one per outer vertex, whose
/// sizes sum to at most `budget`, in lexicographic order.
///
/// # Specification
/// trivial.
fn within(
    (sizes, length): (&[ShapeSize], EdgeCount),
    budget: ShapeSize,
    out: &mut Vec<Vec<ShapeIndex>>,
)
{
    out.clear();
    let mut prefix: Vec<ShapeIndex> = Vec::with_capacity(usize::from(length));
    // One frame per position of the prefix and one past it: the next index
    // to try there, and the budget left.
    let mut frames: Vec<(usize, usize)> = vec![(0, usize::from(budget))];
    while let Some(frame) = frames.last_mut() {
        if prefix.len() >= usize::from(length) {
            out.push(prefix.clone());
            frames.pop();
            prefix.pop();
            continue;
        }
        let (start, left) = *frame;
        let next = sizes
            .iter()
            .enumerate()
            .skip(start)
            .find(|&(_, size)| usize::from(*size) <= left);
        if let Some((index, size)) = next {
            frame.0 = index.saturating_add(1);
            prefix.push(ShapeIndex::from(index));
            frames.push((0, left.saturating_sub(usize::from(*size))));
        }
        else {
            frames.pop();
            prefix.pop();
        }
    }
}

/// Moves `choice` to the next choice of one option per slot, odometer order;
/// outside once every choice is taken.
///
/// # Specification
/// trivial.
fn advance<Choice>(
    choice: &mut [ShapeIndex],
    slots: &[(Edge, Edge, &[Choice])],
) -> Membership
{
    for (picked, slot) in choice.iter_mut().zip(slots) {
        let next = usize::from(*picked).saturating_add(1);
        if next < slot.2.len() {
            *picked = ShapeIndex::from(next);
            return Membership::Inside;
        }
        *picked = ShapeIndex::from(0);
    }
    Membership::Outside
}

/// Into `out`, the columns' keys with the key at vertex `v` moved to the
/// position `order` labels `v` with.
///
/// # Specification
/// trivial.
fn placed<'key, Key>(
    order: &[Edge],
    columns: &'key [Key],
    out: &mut Vec<&'key Key>,
)
{
    out.clear();
    out.extend(columns);
    for (vertex, column) in columns.iter().enumerate() {
        if let Some(slot) = order
            .get(vertex)
            .and_then(|label| out.get_mut(usize::from(*label)))
        {
            *slot = column;
        }
    }
}

impl<Inner: Level> Level for Wreath<Inner>
{
    type Key = WreathKey<Inner::Key>;
    type Map = WreathMap<Inner::Map>;
    type Object = WreathShape<Inner::Object>;

    /// The wreath's objects.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn objects(&self) -> &[Self::Object]
    {
        &self.objects
    }

    /// The wreath's hom set, empty past its objects.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn hom(
        &self,
        source: ShapeIndex,
        target: ShapeIndex,
    ) -> &[Self::Map]
    {
        let position = usize::from(source)
            .saturating_mul(self.objects.len())
            .saturating_add(usize::from(target));
        self.homs.get(position).map_or(&[], |maps| &**maps)
    }

    /// The outer identity, with each column's inner identity to itself.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn identity(object: &Self::Object) -> Self::Map
    {
        WreathMap {
            outer: SiteMap::identity(&object.outer),
            columns: object
                .columns
                .iter()
                .enumerate()
                .map(|(vertex, column)| Box::from([(Edge::from(vertex), Inner::identity(column))]))
                .collect(),
        }
    }

    /// The outer composite, with each inner map composed onward through the
    /// middle vertex it maps to.
    ///
    /// # Specification
    /// - ensures: a composite's outer map is the outer maps' composite, with
    ///   one column per source vertex of `first`.
    /// - fails: the outer maps do not compose, an inner pair does not, or a
    ///   middle vertex has no column in `next`.
    ///
    /// # Errors
    /// - [`CompositionMismatch`]: the outer maps', or an inner pair's.
    /// - [`CompositionMismatch::Vertex`]: a middle vertex `next` has no column
    ///   for.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the identity laws and the closure of each class run
    ///   over every composable pair at the bound.
    /// - witness: `tests::wreath::the_wreath_is_a_generalized_reedy_category`
    #[inline]
    #[spec(ensures: |result| result.as_ref().map_or(true, |map| {
        first.outer.then(&next.outer).is_ok_and(|outer| outer == map.outer)
            && map.columns.len() == first.columns.len()
    }))]
    fn then(
        first: &Self::Map,
        next: &Self::Map,
    ) -> Result<Self::Map, CompositionMismatch>
    {
        let outer = first.outer.then(&next.outer)?;
        let mut columns: Vec<Column<Inner::Map>> = Vec::with_capacity(first.columns.len());
        for column in &first.columns {
            let mut composed: Vec<(Edge, Inner::Map)> = Vec::new();
            for entry in column {
                let middle = entry.0;
                let onward = next
                    .columns
                    .get(usize::from(middle))
                    .ok_or(CompositionMismatch::Vertex { vertex: middle })?;
                for step in onward {
                    composed.push((step.0, Inner::then(&entry.1, &step.1)?));
                }
            }
            composed.sort_by_key(|pair| pair.0);
            columns.push(composed.into_boxed_slice());
        }
        Ok(WreathMap {
            outer,
            columns: columns.into_boxed_slice(),
        })
    }

    /// Whether the outer map is a map of the outer shapes, each column lists
    /// its outer image in order, and each inner map is a map of its two
    /// columns.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn admits(
        map: &Self::Map,
        source: &Self::Object,
        target: &Self::Object,
    ) -> Membership
    {
        let fits = map.outer.validate(&source.outer, &target.outer).is_ok()
            && map.columns.len() == source.columns.len()
            && map
                .columns
                .iter()
                .zip(source.columns.iter())
                .enumerate()
                .all(|(vertex, (column, from))| {
                    column
                        .iter()
                        .map(|entry| entry.0)
                        .eq(map.outer.image(Edge::from(vertex)).members())
                        && column.iter().all(|entry| {
                            target.columns.get(usize::from(entry.0)).is_some_and(|to| {
                                Inner::admits(&entry.1, from, to) == Membership::Inside
                            })
                        })
                });
        if fits {
            Membership::Inside
        }
        else {
            Membership::Outside
        }
    }

    /// Whether the outer kernels meet in no point and, at each source vertex,
    /// the inner maps of the whole family out of it are jointly raising; a
    /// vertex an outer map deletes carries no inner map, and constrains
    /// nothing there.
    ///
    /// # Specification
    /// - ensures: inside only when the family is non-empty and its outer
    ///   kernels meet in no point.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a point's column sent to two points, kept at one and
    ///   deleted at the other, raises; deleted at both, it does not.
    /// - witness: `tests::wreath::a_column_raises_when_one_inner_map_keeps_it`
    #[inline]
    #[spec(ensures: |answer| answer == Membership::Outside
        || family.iter().map(|map| map.outer.kernel()).reduce(VertexSet::intersection) == Some(VertexSet::EMPTY))]
    fn jointly_raising(family: &[&Self::Map]) -> Membership
    {
        let Some(first) = family.first()
        else {
            return Membership::Outside;
        };
        let meet = family
            .iter()
            .map(|map| map.outer.kernel())
            .reduce(VertexSet::intersection);
        if meet != Some(VertexSet::EMPTY) {
            return Membership::Outside;
        }
        let mut at: Vec<&Inner::Map> = Vec::new();
        let columns_raise = (0 .. first.columns.len()).all(|vertex| {
            at.clear();
            at.extend(
                family
                    .iter()
                    .filter_map(|map| map.columns.get(vertex))
                    .flat_map(|column| column.iter().map(|entry| &entry.1)),
            );
            Inner::jointly_raising(&at) == Membership::Inside
        });
        if columns_raise {
            Membership::Inside
        }
        else {
            Membership::Outside
        }
    }

    /// Whether the outer map is lowering and every inner map is lowering into
    /// its column.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn lowering(
        map: &Self::Map,
        target: &Self::Object,
    ) -> Membership
    {
        let lowers = map.outer.lowering(&target.outer) == Membership::Inside
            && map
                .columns
                .iter()
                .flat_map(|column| column.iter())
                .all(|entry| {
                    target
                        .columns
                        .get(usize::from(entry.0))
                        .is_some_and(|to| Inner::lowering(&entry.1, to) == Membership::Inside)
                });
        if lowers {
            Membership::Inside
        }
        else {
            Membership::Outside
        }
    }

    /// Whether the outer map is an isomorphism and so is each column's one
    /// inner map.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn invertibility(
        map: &Self::Map,
        target: &Self::Object,
    ) -> Invertibility
    {
        let inverts = map.outer.invertibility(&target.outer) == Invertibility::Invertible
            && map.columns.iter().all(|column| {
                column.len() == 1
                    && column.iter().all(|entry| {
                        target.columns.get(usize::from(entry.0)).is_some_and(|to| {
                            Inner::invertibility(&entry.1, to) == Invertibility::Invertible
                        })
                    })
            });
        if inverts {
            Invertibility::Invertible
        }
        else {
            Invertibility::NotInvertible
        }
    }

    /// Whether the outer shape and every column are grounded.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn grounded(object: &Self::Object) -> Membership
    {
        let grounded = <Catalogue as Level>::grounded(&object.outer) == Membership::Inside
            && object
                .columns
                .iter()
                .all(|column| Inner::grounded(column) == Membership::Inside);
        if grounded {
            Membership::Inside
        }
        else {
            Membership::Outside
        }
    }

    /// The outer degree plus the inner degrees.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn degree(object: &Self::Object) -> Degree
    {
        Degree::from(
            object
                .columns
                .iter()
                .fold(usize::from(Degree::of(&object.outer)), |sum, column| {
                    sum.saturating_add(usize::from(Inner::degree(column)))
                }),
        )
    }

    /// The outer size plus the inner sizes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn size(object: &Self::Object) -> ShapeSize
    {
        ShapeSize::from(
            object
                .columns
                .iter()
                .fold(usize::from(object.outer.size()), |sum, column| {
                    sum.saturating_add(usize::from(Inner::size(column)))
                }),
        )
    }

    /// The wreath's families, outermost first.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn families(&self) -> &[Family]
    {
        &self.families
    }

    /// The wreath's class index.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn class_index(&self) -> &BTreeMap<WreathKey<Inner::Key>, ShapeIndex>
    {
        &self.classes
    }

    /// Whether the first of `families` holds the outer shape and the rest hold
    /// every column; outside when there is no first.
    ///
    /// # Specification
    /// - ensures: inside exactly when `families` has a first family holding the
    ///   outer shape and the inner level places every column in the rest.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an outer bigon and a bigon column each lie outside
    ///   the chains, and Θ₂'s objects lie in them.
    /// - witness: `tests::theta::a_cycle_at_the_outer_level_is_refused_by_name`
    #[inline]
    #[spec(ensures: |answer| (answer == Membership::Inside) == families.split_first().is_some_and(|(first, rest)| {
        first.holds(&object.outer) == Membership::Inside
            && object.columns.iter().all(|column| Inner::lies_in(rest, column) == Membership::Inside)
    }))]
    fn lies_in(
        families: &[Family],
        object: &Self::Object,
    ) -> Membership
    {
        let Some((first, rest)) = families.split_first()
        else {
            return Membership::Outside;
        };
        if first.holds(&object.outer) == Membership::Inside
            && object
                .columns
                .iter()
                .all(|column| Inner::lies_in(rest, column) == Membership::Inside)
        {
            Membership::Inside
        }
        else {
            Membership::Outside
        }
    }

    /// The least, over the orders of the outer vertices, of the relabelled
    /// outer ends with the columns' keys in that order.
    ///
    /// # Specification
    /// - ensures: the key keeps the outer vertex count and one column key per
    ///   outer vertex; two objects key alike exactly when an outer isomorphism
    ///   carries one's columns onto columns keyed alike in the other.
    /// - panics: none.
    /// - intension: tries every order of the outer vertices, so the cost is the
    ///   outer vertex count's factorial times the wires' sorting cost.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every wreath built at the pinned bounds keys each
    ///   object apart, and a relabelled object is found at its class; a key
    ///   that missed an order would split a class or merge two.
    /// - witness: `tests::wreath::the_wreath_holds_one_object_per_class`
    /// - witness: `tests::theta::the_chain_restriction_is_the_full_sub_site_of_the_wreath`
    #[inline]
    #[spec(ensures: |ref key| key.vertices == object.outer.vertex_count() && key.columns.len() == object.columns.len())]
    fn key(object: &Self::Object) -> Self::Key
    {
        let columns: Vec<Inner::Key> = object.columns.iter().map(Inner::key).collect();
        let mut orders = VertexOrders::new(object.outer.vertex_count());
        let mut ends = object.outer.relabelled(orders.order());
        let mut least: Vec<&Inner::Key> = Vec::with_capacity(columns.len());
        placed(orders.order(), &columns, &mut least);
        let mut candidate: Vec<&Inner::Key> = Vec::with_capacity(columns.len());
        while orders.advance() == Membership::Inside {
            let relabelled = object.outer.relabelled(orders.order());
            placed(orders.order(), &columns, &mut candidate);
            if (&relabelled, &candidate) < (&ends, &least) {
                ends = relabelled;
                core::mem::swap(&mut least, &mut candidate);
            }
        }
        WreathKey {
            vertices: object.outer.vertex_count(),
            ends,
            columns: least.into_iter().cloned().collect(),
        }
    }
}
