//! The Segal condition: each shape the colimit of its corollas along its
//! grafting pushouts, checked shape by shape against every shape of the
//! catalogue.
//!
//! # The cocone
//!
//! A shape's [`Cocone`] is the carrier's constructor list read as a diagram:
//! one [`Inclusion`] of its corolla at each vertex, in vertex order, and one
//! [`Graft`] per inner wire, naming the output leg of the producer's corolla
//! and the input leg of the consumer's corolla the wire glues. Grafting is the
//! pushout along the wire the two legs share, and a stick is not a shape, so
//! the pushout has no apex object: a map out of the stick would be a wire of
//! the target, and a family of maps out of the corollas agrees along a graft
//! when it sends the two glued legs to one wire. Read vertex by vertex, the
//! cocone is the iterated grafting pushouts: the first `i` corollas glued
//! along the grafts among them are the sub-shape on the first `i` vertices,
//! and the next corolla is glued to it along its grafts to them, or along the
//! empty shape, the external product's unit, when it has none.
//!
//! # The condition
//!
//! [`segal`] holds at degree `n` when every shape of degree two to `n` in the
//! catalogue is the colimit of its cocone: for every shape `K` of the
//! catalogue, restriction along the inclusions is a bijection from the maps
//! `G → K` onto the families of maps `C_v → K`, one per vertex, that agree
//! along every graft. The alphabet is the whole morphism class, deletions and
//! substitutions among its maps; the range is the catalogue's shapes, so a
//! verdict holds at the bound and says nothing past it. A shape of degree at
//! most one is the empty shape or a corolla, its own cocone.
//!
//! The families counted are fixed in the statement, by [`Cocones`]. The class
//! holds no fold: distinct vertices have disjoint images. A family sending two
//! vertices into one image therefore restricts from no map, and over the
//! blanket alphabet, every agreeing family, the condition fails at the first
//! shape with two vertices one map can send to one place: the two points `• ⊔
//! •` against `•`, where the identity twice is a family no map induces. Over
//! the families the class admits, those whose images are disjoint, it holds at
//! every shape at the bound. The fold the class omits restricts on a Segal
//! object to the diagonal of a product, which the product already determines
//! (crate root, no vertex reuse), so the admitted families are the alphabet
//! the statement is true in. The blanket statement is not a weaker true
//! statement; it is false at degree two.
//!
//! What the checks find, over the catalogue of size at most five and every
//! degree it reaches (the `suites` example prints these rows):
//!
//! | Cocones | Degree | Verdict | Cases | Smallest counter-example |
//! | ------- | ------ | ------- | ----- | ------------------------ |
//! | admitted | ≤ 5 | holds | 5265 | — |
//! | blanket | ≤ 5 | fails | 2 | `[2v;]` against `[1v;]`: the identity of the point twice |
//!
//! The refusals other than [`SegalDefect::Unmediated`] are theorems of the
//! class at a catalogue shape: a vertex's corolla is never larger than its
//! shape, so the catalogue holds it; the class's disjointness and composition
//! make every restriction an admitted family; and a map is determined by its
//! vertex and wire images, every wire of a stick-free shape meeting a vertex,
//! so no two maps restrict alike. The condition decides them all the same.
//!
//! # Cost
//!
//! For a shape `G` and a test shape `K` the condition reads the hom sets the
//! catalogue holds: each map `G → K` composed with each inclusion, and the
//! agreeing families searched vertex by vertex, each corolla's maps into `K`
//! tried in turn and a partial family abandoned at the first graft it breaks
//! or, over the admitted families, the first overlap. The search visits at
//! most the product over the vertices of `|Hom(C_v, K)|` families and keeps
//! only the agreeing ones; at size five every degree runs in well under a
//! second in release.
//!
//! # Decisions
//!
//! - **The admitted families are the alphabet.** The alternative, the blanket
//!   alphabet, makes the condition false at every shape with two vertices of
//!   one profile, so no stratum above the corollas would exist. Reversal: a
//!   class that holds the folds, where the blanket families are the admitted
//!   ones.
//! - **The whole class is the test alphabet.** The stratum's naturality reads
//!   only maps that send each vertex to one vertex, and a colimit over the
//!   whole class restricts to that subcategory: the map a family of such maps
//!   induces sends each vertex where its corolla's map does. Checking the whole
//!   class is the stronger statement at a small cost. Reversal: a bound at
//!   which the whole class is too large to search.

use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
use gandr_theory_circuit_algebras::Edge;
use gandr_theory_circuit_algebras::Wire;
use quenchant_shape::shape::Maybe;

use crate::catalogue::Catalogue;
use crate::catalogue::ShapeIndex;
use crate::degree::Degree;
use crate::map::Membership;
use crate::map::SiteMap;
use crate::map::VertexSet;
use crate::outcome::Outcome;
use crate::outcome::Tally;
use crate::shape::End;
use crate::shape::Shape;
use crate::stratum::Profile;

wrapper! {
    /// A position among one cell's candidate maps into a test shape.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Choice(usize);
}

/// Which families of maps out of the corollas a Segal statement counts.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Cocones
{
    /// The families whose images are disjoint: the families the class's
    /// disjointness clause admits.
    Admitted,
    /// Every family that agrees along the grafts, including those that send
    /// two vertices into one image.
    Blanket,
}

/// One vertex's corolla and an inclusion of it at the vertex.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Inclusion
{
    /// The corolla's position in the catalogue.
    pub corolla: ShapeIndex,
    /// A map of the class from the corolla onto the vertex alone.
    pub map: SiteMap,
}

/// One leg of a vertex's corolla: the vertex, and the corolla's wire.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Leg
{
    /// The vertex.
    pub vertex: Edge,
    /// The wire of the vertex's corolla.
    pub wire: Wire,
}

/// An inner wire of a shape as the pushout it is: the output leg of its
/// producer's corolla glued to the input leg of its consumer's.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Graft
{
    /// The inner wire.
    pub wire: Wire,
    /// The producer's leg the inclusion sends onto the wire.
    pub producer: Leg,
    /// The consumer's leg the inclusion sends onto the wire.
    pub consumer: Leg,
}

/// A shape's Segal cocone: its corollas at its vertices and the grafts that
/// glue them.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Cocone
{
    /// The shape's position in the catalogue.
    shape: ShapeIndex,
    /// One inclusion per vertex, in vertex order.
    inclusions: Box<[Inclusion]>,
    /// One graft per inner wire, in wire order.
    grafts: Box<[Graft]>,
}

impl Cocone
{
    /// The shape's position in the catalogue.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn shape(&self) -> ShapeIndex
    {
        self.shape
    }

    /// One inclusion per vertex, in vertex order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn inclusions(&self) -> &[Inclusion]
    {
        &self.inclusions
    }

    /// One graft per inner wire, in wire order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn grafts(&self) -> &[Graft]
    {
        &self.grafts
    }

    /// The cocone of the shape at `shape` with `inclusions` and `grafts`, as
    /// a replay checked them.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn replayed(
        shape: ShapeIndex,
        inclusions: Box<[Inclusion]>,
        grafts: Box<[Graft]>,
    ) -> Self
    {
        Self {
            shape,
            inclusions,
            grafts,
        }
    }

    /// The cocone of the catalogue's shape at `index`.
    ///
    /// # Specification
    /// - requires: `shape` is the catalogue's shape at `index`, and `corollas`
    ///   holds the catalogue's corolla of each profile.
    /// - ensures: one inclusion per vertex, each a raising map from the corolla
    ///   of the vertex's legs whose one image is the vertex, the first such in
    ///   the hom set; one graft per inner wire, each leg the corolla wire its
    ///   inclusion sends onto it.
    /// - fails: [`SegalDefect::Uncovered`] at the first vertex whose corolla or
    ///   inclusion the catalogue does not hold.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`SegalDefect`] — as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two disjoint corollas have two inclusions and no
    ///   graft, and the graft of a constant into a binary operation glues the
    ///   constant's output leg to an input leg of the operation.
    /// - witness: `tests::stratum::a_shape_of_degree_two_is_the_colimit_of_its_corollas`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |cocone| {
        cocone.inclusions.len() == usize::from(shape.vertex_count())
            && cocone.inclusions.iter().zip(shape.vertices()).all(|(inclusion, vertex)| inclusion.map.images() == [VertexSet::single(vertex)])
            && cocone.grafts.iter().all(|graft| shape.ends().get(usize::from(graft.wire)).is_some_and(|ends| {
                ends.producer() == End::Vertex(graft.producer.vertex) && ends.consumer() == End::Vertex(graft.consumer.vertex)
            }))
    }))]
    fn of(
        catalogue: &Catalogue,
        corollas: &BTreeMap<Profile, ShapeIndex>,
        (index, shape): (ShapeIndex, &Shape),
    ) -> Result<Self, SegalDefect>
    {
        let mut inclusions = Vec::with_capacity(usize::from(shape.vertex_count()));
        for vertex in shape.vertices() {
            let uncovered = SegalDefect::Uncovered { vertex };
            let Some(&corolla) = corollas.get(&Profile::at(shape, vertex))
            else {
                return Err(uncovered);
            };
            let Maybe::Present(maps) = catalogue.maps(corolla, index)
            else {
                return Err(uncovered);
            };
            let Some(map) = maps.iter().find(|map| {
                map.raising() == Membership::Inside && map.images() == [VertexSet::single(vertex)]
            })
            else {
                return Err(uncovered);
            };
            inclusions.push(Inclusion {
                corolla,
                map: map.clone(),
            });
        }
        let leg = |vertex: Edge, wire: Wire| -> Result<Leg, SegalDefect> {
            inclusions
                .get(usize::from(vertex))
                .and_then(|inclusion| {
                    inclusion
                        .map
                        .wires()
                        .iter()
                        .position(|image| *image == wire)
                })
                .map(|position| Leg {
                    vertex,
                    wire: Wire::from(position),
                })
                .ok_or(SegalDefect::Uncovered { vertex })
        };
        let mut grafts = Vec::new();
        for (position, ends) in shape.ends().iter().enumerate() {
            let (End::Vertex(producer), End::Vertex(consumer)) = (ends.producer(), ends.consumer())
            else {
                continue;
            };
            let wire = Wire::from(position);
            let producer = leg(producer, wire)?;
            let consumer = leg(consumer, wire)?;
            grafts.push(Graft {
                wire,
                producer,
                consumer,
            });
        }
        Ok(Self {
            shape: index,
            inclusions: inclusions.into_boxed_slice(),
            grafts: grafts.into_boxed_slice(),
        })
    }
}

/// How a shape fails to be the colimit of its cocone against a test shape.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum SegalDefect
{
    /// The catalogue holds no corolla of a vertex's legs, or no inclusion of
    /// it at the vertex.
    Uncovered
    {
        /// The vertex.
        vertex: Edge,
    },
    /// A map out of the shape whose restriction is no family the statement
    /// counts.
    Stray
    {
        /// The map.
        map: SiteMap,
    },
    /// A family two maps restrict to.
    Ambiguous
    {
        /// The family, one map per vertex.
        family: Box<[SiteMap]>,
    },
    /// A family no map restricts to.
    Unmediated
    {
        /// The family, one map per vertex.
        family: Box<[SiteMap]>,
    },
}

impl fmt::Display for SegalDefect
{
    /// Names the defect and writes its maps, separated by ` ; `.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        let family = |f: &mut fmt::Formatter<'_>, name: &str, maps: &[SiteMap]| -> fmt::Result {
            f.write_str(name)?;
            for (position, map) in maps.iter().enumerate() {
                let separator = if position == 0 { " " } else { " ; " };
                write!(f, "{separator}{map}")?;
            }
            Ok(())
        };
        match *self {
            Self::Uncovered { vertex } => {
                write!(f, "no corolla included at vertex {}", usize::from(vertex))
            },
            Self::Stray { ref map } => write!(f, "a map restricting to no family: {map}"),
            Self::Ambiguous { family: ref maps } => {
                family(f, "a family two maps restrict to:", maps)
            },
            Self::Unmediated { family: ref maps } => {
                family(f, "a family no map restricts to:", maps)
            },
        }
    }
}

/// A shape that is not the colimit of its cocone, the test shape it fails
/// against, and how.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct SegalFailure
{
    /// The shape.
    pub shape: Shape,
    /// The shape the restriction is no bijection into.
    pub test: Shape,
    /// How it fails.
    pub defect: SegalDefect,
}

impl fmt::Display for SegalFailure
{
    /// Writes the shape, the test shape and the defect.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(f, "{} against {}: {}", self.shape, self.test, self.defect)
    }
}

/// Whether every shape of degree two to `degree` is the colimit of its
/// corollas along its grafting pushouts, over the families `cocones` counts.
///
/// # Specification
/// - ensures: holds exactly when, for every shape `G` of degree two to `degree`
///   and every shape `K` of the catalogue, restriction along `G`'s [`Cocone`]
///   is a bijection from the maps `G → K` onto the families of maps from its
///   corollas into `K` that agree along every graft and, for
///   [`Cocones::Admitted`], have disjoint images; after one case per pair,
///   shapes in catalogue order and test shapes within each; the first failing
///   pair otherwise.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — the admitted outcome holds at size four over every
///   degree, its case count one per shape of degree two or more and test shape;
///   L3 — the blanket outcome fails at the two points against the point, with
///   the identity twice as the family no map induces.
/// - witness: `tests::stratum::a_shape_of_degree_two_is_the_colimit_of_its_corollas`
#[inline]
#[must_use]
#[spec(ensures: |ref outcome| match *outcome {
    Outcome::Holds { cases } => usize::from(cases) == catalogue.shapes().iter().filter(|shape| within(shape, degree) == Membership::Inside).count().saturating_mul(catalogue.shapes().len()),
    Outcome::Fails { ref witness, .. } => within(&witness.shape, degree) == Membership::Inside,
})]
pub fn segal(
    catalogue: &Catalogue,
    degree: Degree,
    cocones: Cocones,
) -> Outcome<SegalFailure>
{
    walk(catalogue, degree, cocones).0
}

/// Whether `shape` is of degree two to `degree`, a shape the condition at
/// `degree` reads.
///
/// # Specification
/// trivial.
fn within(
    shape: &Shape,
    degree: Degree,
) -> Membership
{
    let of = Degree::of(shape);
    if of >= Degree::from(2_usize) && of <= degree {
        Membership::Inside
    }
    else {
        Membership::Outside
    }
}

/// The condition's outcome, and the cocone of every shape it read.
///
/// # Specification
/// - ensures: the outcome [`segal`] states; the cocones of the shapes of degree
///   two to `degree` in catalogue order, up to the failing shape.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the stratum at degree two holds the cocones the condition
///   read, and the blanket alphabet stops at the two points.
/// - witness: `tests::stratum::a_shape_of_degree_two_is_the_colimit_of_its_corollas`
#[spec(ensures: |ref ret| ret.1.iter().all(|cocone| {
    matches!(catalogue.shape(cocone.shape), Maybe::Present(shape) if within(shape, degree) == Membership::Inside)
}))]
pub fn walk(
    catalogue: &Catalogue,
    degree: Degree,
    cocones: Cocones,
) -> (Outcome<SegalFailure>, Vec<Cocone>)
{
    let corollas: BTreeMap<Profile, ShapeIndex> = catalogue
        .entries()
        .filter(|entry| Degree::of(entry.1) == Degree::from(1_usize))
        .map(|(index, shape)| (Profile::at(shape, Edge::from(0_usize)), index))
        .collect();
    let mut tally = Tally::default();
    let mut read = Vec::new();
    for (index, shape) in catalogue.entries() {
        if within(shape, degree) == Membership::Outside {
            continue;
        }
        let cocone = match Cocone::of(catalogue, &corollas, (index, shape)) {
            Ok(cocone) => cocone,
            Err(defect) => {
                tally.count();
                let failure = SegalFailure {
                    shape: shape.clone(),
                    test: shape.clone(),
                    defect,
                };
                return (tally.fails(failure), read);
            },
        };
        for (test, form) in catalogue.entries() {
            tally.count();
            if let Err(defect) = colimit(catalogue, &cocone, test, cocones) {
                let failure = SegalFailure {
                    shape: shape.clone(),
                    test: form.clone(),
                    defect,
                };
                return (tally.fails(failure), read);
            }
        }
        read.push(cocone);
    }
    (tally.holds(), read)
}

/// Whether `cocone`'s shape is the colimit of its corollas against the
/// catalogue's shape at `test`.
///
/// # Specification
/// - ensures: `Ok` exactly when restriction along the inclusions sends the maps
///   into `test` one to one onto the agreeing families `cocones` counts.
/// - fails: [`SegalDefect::Stray`] at the first map whose restriction is no
///   such family; otherwise, family by family in search order,
///   [`SegalDefect::Unmediated`] for one no map restricts to and
///   [`SegalDefect::Ambiguous`] for one two maps restrict to.
/// - panics: none.
///
/// # Errors
/// - [`SegalDefect`] — as above.
///
/// # Adequacy
/// - hypothesis: L3 — the two points against the point: the three maps restrict
///   to three of the four agreeing families, and the identity twice is
///   unmediated.
/// - witness: `tests::stratum::a_shape_of_degree_two_is_the_colimit_of_its_corollas`
#[spec(ensures: |ref ret| match *ret {
    Err(SegalDefect::Unmediated { ref family } | SegalDefect::Ambiguous { ref family }) => family.len() == cocone.inclusions.len(),
    Ok(()) | Err(_) => true,
})]
fn colimit(
    catalogue: &Catalogue,
    cocone: &Cocone,
    test: ShapeIndex,
    cocones: Cocones,
) -> Result<(), SegalDefect>
{
    let hom = |source: ShapeIndex| match catalogue.maps(source, test) {
        Maybe::Present(maps) => maps,
        Maybe::Absent(_) => &[],
    };
    let candidates: Vec<&[SiteMap]> = cocone
        .inclusions
        .iter()
        .map(|inclusion| hom(inclusion.corolla))
        .collect();
    let found = families(&candidates, |chosen, cursor| {
        agrees((&candidates, &cocone.grafts, cocones), chosen, cursor)
    });
    let restrict =
        |position: usize, map: &SiteMap| cocone.inclusions.get(position)?.map.then(map).ok();
    bijection(&candidates, &found, hom(cocone.shape), restrict).map_err(|mismatch| match mismatch {
        Mismatch::Stray { map } => SegalDefect::Stray { map },
        Mismatch::Unmediated { family } => SegalDefect::Unmediated { family },
        Mismatch::Ambiguous { family } => SegalDefect::Ambiguous { family },
    })
}

/// How restriction along a cocone fails to be a bijection onto its families,
/// at any level.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Mismatch<Map>
{
    /// A map whose restriction is no family counted.
    Stray
    {
        /// The map.
        map: Map,
    },
    /// A family no map restricts to.
    Unmediated
    {
        /// The family, one map per cell.
        family: Box<[Map]>,
    },
    /// A family two maps restrict to.
    Ambiguous
    {
        /// The family, one map per cell.
        family: Box<[Map]>,
    },
}

/// Whether restriction sends `maps` one to one onto `found`: each map
/// restricted along every cell by `restrict` lands on one family, and every
/// family is hit once.
///
/// # Specification
/// - ensures: `Ok` exactly when every map restricts, cell by cell, to a
///   candidate of that cell, the restrictions form a family of `found`, and
///   each family of `found` is the restriction of exactly one map.
/// - fails: [`Mismatch::Stray`] at the first map that does not restrict to a
///   family of `found`; otherwise, in the order of `found`,
///   [`Mismatch::Unmediated`] for a family no map hits and
///   [`Mismatch::Ambiguous`] for one two maps hit.
/// - panics: none.
///
/// # Errors
/// - [`Mismatch`] — as above.
///
/// # Adequacy
/// - hypothesis: L3 — the two points against the point at level one; at level
///   two the whisker and the composites, and a cover with its outer graft left
///   out, which leaves a family unmediated.
/// - witness: `tests::stratum::a_shape_of_degree_two_is_the_colimit_of_its_corollas`
/// - witness: `tests::stratum::the_whisker_and_both_composites_are_certified_at_level_two`
/// - witness: `ascent::tests::a_cover_without_its_outer_graft_leaves_a_family_unmediated`
#[spec(ensures: |ref ret| match *ret {
    Err(Mismatch::Unmediated { ref family } | Mismatch::Ambiguous { ref family }) => family.len() == candidates.len(),
    Ok(()) | Err(_) => true,
})]
pub fn bijection<Map, Restrict>(
    candidates: &[&[Map]],
    found: &[Box<[Choice]>],
    maps: &[Map],
    restrict: Restrict,
) -> Result<(), Mismatch<Map>>
where
    Map: Clone + PartialEq,
    Restrict: Fn(usize, &Map) -> Option<Map>,
{
    let mut hits = alloc::vec![0_usize; found.len()];
    let mut restricted = Vec::with_capacity(candidates.len());
    for map in maps {
        let stray = || Mismatch::Stray { map: map.clone() };
        restricted.clear();
        for (cell, options) in candidates.iter().enumerate() {
            let Some(leg) = restrict(cell, map)
            else {
                return Err(stray());
            };
            let Some(position) = options.iter().position(|option| *option == leg)
            else {
                return Err(stray());
            };
            restricted.push(Choice(position));
        }
        let Ok(at) = found.binary_search_by(|family| family.as_ref().cmp(restricted.as_slice()))
        else {
            return Err(stray());
        };
        if let Some(count) = hits.get_mut(at) {
            *count = count.saturating_add(1);
        }
    }
    for (family, &count) in found.iter().zip(&hits) {
        if count == 1 {
            continue;
        }
        let maps: Box<[Map]> = family
            .iter()
            .zip(candidates)
            .filter_map(|(&position, options)| options.get(position.0).cloned())
            .collect();
        return Err(if count == 0 {
            Mismatch::Unmediated { family: maps }
        }
        else {
            Mismatch::Ambiguous { family: maps }
        });
    }
    Ok(())
}

/// Every family of one candidate per cell that `agrees` keeps, as candidate
/// positions, in increasing order.
///
/// # Specification
/// - ensures: each family `agrees` admits at every prefix once, in
///   lexicographic order of its positions, each position within its cell's
///   candidates; none when a cell has no candidate or there is no cell.
/// - panics: none.
/// - intension: a search over the cells in order with an explicit stack of
///   chosen positions, abandoning a partial family at the first candidate
///   `agrees` refuses beside the cells chosen before it.
///
/// # Adequacy
/// - hypothesis: L3 — the two points against the point have four blanket
///   families and three admitted ones, the identity twice excluded.
/// - witness: `tests::stratum::a_shape_of_degree_two_is_the_colimit_of_its_corollas`
#[spec(ensures: |ref found| found.iter().zip(found.iter().skip(1)).all(|(first, second)| first < second)
    && found.iter().all(|family| family.len() == candidates.len()
        && family.iter().zip(candidates).all(|(&position, options)| position.0 < options.len())))]
pub fn families<Map, Agrees>(
    candidates: &[&[Map]],
    agrees: Agrees,
) -> Vec<Box<[Choice]>>
where
    Agrees: Fn(&[Choice], Choice) -> Membership,
{
    let mut found = Vec::new();
    let mut chosen: Vec<Choice> = Vec::with_capacity(candidates.len());
    let mut cursor = Choice(0);
    loop {
        let level = chosen.len();
        let options = candidates.get(level).copied().unwrap_or_default();
        if level == candidates.len() || cursor.0 >= options.len() {
            if level == candidates.len() && level > 0 {
                found.push(chosen.as_slice().into());
            }
            let Some(last) = chosen.pop()
            else {
                return found;
            };
            cursor = Choice(last.0.saturating_add(1));
            continue;
        }
        if agrees(&chosen, cursor) == Membership::Inside {
            chosen.push(cursor);
            cursor = Choice(0);
        }
        else {
            cursor = Choice(cursor.0.saturating_add(1));
        }
    }
}

/// Whether the candidate at `cursor` for the vertex after `chosen` keeps the
/// partial family agreeing: along every graft it shares with an earlier
/// vertex, and, for [`Cocones::Admitted`], disjoint from their images.
///
/// # Specification
/// trivial.
fn agrees(
    (candidates, grafts, cocones): (&[&[SiteMap]], &[Graft], Cocones),
    chosen: &[Choice],
    cursor: Choice,
) -> Membership
{
    let level = chosen.len();
    let pick = |vertex: usize, position: Choice| {
        let options = candidates.get(vertex)?;
        options.get(position.0)
    };
    let Some(map) = pick(level, cursor)
    else {
        return Membership::Outside;
    };
    let earlier = |vertex: Edge| {
        let vertex = usize::from(vertex);
        let &position = chosen.get(vertex)?;
        pick(vertex, position)
    };
    let joined = grafts.iter().all(|graft| {
        let (producer, consumer) = (graft.producer, graft.consumer);
        let (mine, theirs) = if usize::from(producer.vertex) == level {
            (producer, consumer)
        }
        else if usize::from(consumer.vertex) == level {
            (consumer, producer)
        }
        else {
            return true;
        };
        if usize::from(theirs.vertex) >= level {
            return true;
        }
        let Some(other) = earlier(theirs.vertex)
        else {
            return false;
        };
        map.wires().get(usize::from(mine.wire)) == other.wires().get(usize::from(theirs.wire))
    });
    let image = map.image_union();
    let disjoint = || {
        (0 .. level).all(|vertex| {
            earlier(Edge::from(vertex))
                .is_some_and(|other| other.image_union().intersection(image) == VertexSet::EMPTY)
        })
    };
    if joined && (cocones == Cocones::Blanket || disjoint()) {
        Membership::Inside
    }
    else {
        Membership::Outside
    }
}
