//! The stratum across levels: the Segal certificate of level two, built from
//! level one's.
//!
//! # The cells
//!
//! An object of level two is an outer shape whose vertices carry shapes of
//! level one, the columns. Its cells are one per vertex of each column: the
//! column's outer vertex, as the corolla of its outer legs, carrying the
//! corolla of that vertex's inner legs. An empty column has one cell, the outer
//! corolla carrying the empty shape: the whisker's 1-cell. A cell's
//! [`Inclusion`]s are read off the level-one certificate: the outer corolla's
//! inclusion at the column's vertex from the outer shape's [`crate::Cocone`],
//! and the inner corolla's at the cell's vertex from the column's. Level two
//! finds the one wreath map carrying both and never builds a cocone of level
//! one again.
//!
//! # The grafts
//!
//! The cocone glues the cells by two kinds of graft. An outer graft is a graft
//! of the outer shape's level-one cocone: an inner wire of the outer shape,
//! glueing every cell of its producer's column to every cell of its
//! consumer's. An inner graft is a graft of a column's level-one cocone: an
//! inner wire of the column, glueing two cells of that column.
//!
//! A family of maps out of the cells into a test object agrees when the cells
//! of one column take one outer map, the columns' outer maps agree along every
//! outer graft and have disjoint images, and, within a column, at each vertex
//! of the column's outer image, the inner maps agree along every inner graft
//! and have disjoint images. These are the admitted families of level one,
//! read once at each level. The condition holds at an object when restriction
//! along the cells is a bijection from its maps into each test object onto
//! the agreeing families.
//!
//! # What the certificate reads
//!
//! The certificate reads the grafting pushouts and the raising maps, never a
//! lowering span. [`WreathStratum::certify`] checks that the grounded objects
//! of level two, with the empty column among them, form a direct category with
//! automorphisms, the condition the level-one univalence warrant climbs
//! through. The pushout inside an empty column, whose pushed-out map lowers,
//! stays outside what it reads. The empty column is the level-two unit, a fat
//! object, and [`crate::Wreath`] states why the site keeps it.
//!
//! # The pinwheel
//!
//! A shape whose cells meet in a cycle has no composite: its cells cover it,
//! and their union does not determine its maps. No level holds one. The
//! carrier refuses a wiring with a directed cycle as
//! `WiringObstruction::DirectedCycle`, at the outer level and in every column:
//! Leclerc and Mimram's Lemma 3, that a pasting scheme is acyclic. So the
//! cells of a level-two object are ordered within each column, and the
//! columns along the outer shape. The condition names an agreeing family no
//! map restricts to [`LevelDefect::Unmediated`]. Over `W ≀ W` at total size
//! seven no object reaches it; a cover with its outer graft left out does.
//!
//! # References
//!
//! - `Ruit-2024-pasting_theorem_iterated_segal_spaces` — exemplar: the pasting
//!   theorem this certificate instances, a composable shape the union of its
//!   cover (Theorem 3.49, Corollaries 3.52 and 3.55), proved by induction on
//!   the dimension; § 3.2 and Example 3.54, the pinwheel, a shape whose cover
//!   does not determine its maps.

#[cfg(test)]
mod tests;

use alloc::boxed::Box;
use alloc::vec;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
use gandr_theory_circuit_algebras::Edge;
use quenchant_shape::shape::Maybe;

use crate::catalogue::Catalogue;
use crate::catalogue::ShapeIndex;
use crate::conditions::Site;
use crate::conditions::direct_core;
use crate::degree::Degree;
use crate::level::Level;
use crate::map::Membership;
use crate::map::SiteMap;
use crate::map::VertexSet;
use crate::outcome::MapCase;
use crate::outcome::Outcome;
use crate::outcome::Tally;
use crate::segal::Choice;
use crate::segal::Graft;
use crate::segal::Inclusion;
use crate::segal::Mismatch;
use crate::segal::bijection;
use crate::segal::families;
use crate::shape::Shape;
use crate::stratum::SegalStratum;
use crate::wreath::Wreath;
use crate::wreath::WreathMap;
use crate::wreath::WreathShape;

/// Level two over the wiring site: the wreath of the catalogue over itself.
type Two = Wreath<Catalogue>;

/// An object of level two.
type TwoShape = WreathShape<Shape>;

/// A map of level two.
type TwoMap = WreathMap<SiteMap>;

/// Where a cell sits in its column.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Spot
{
    /// The column is empty, and the cell is its 1-cell.
    Empty,
    /// The cell covers this vertex of the column.
    Vertex(Edge),
}

/// One cell of a level-two object and its inclusion.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Cell
{
    /// The outer vertex whose column holds the cell.
    pub column: Edge,
    /// Where the cell sits in that column.
    pub spot: Spot,
    /// The cell's object in the wreath.
    pub object: ShapeIndex,
    /// The wreath map from the cell onto its place.
    pub map: TwoMap,
}

/// An inner graft: a graft of a column's level-one cocone, its legs the
/// column's vertices.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct InnerGraft
{
    /// The outer vertex whose column it glues.
    pub column: Edge,
    /// The column's graft.
    pub graft: Graft,
}

/// A level-two object's Segal cocone: its cells and the grafts that glue
/// them.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct WreathCocone
{
    /// The object's position in the wreath.
    object: ShapeIndex,
    /// The cells, column by column, each column's in vertex order.
    cells: Box<[Cell]>,
    /// The outer shape's grafts, their legs the outer vertices.
    outer: Box<[Graft]>,
    /// The columns' grafts.
    inner: Box<[InnerGraft]>,
}

impl WreathCocone
{
    /// The object's position in the wreath.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn object(&self) -> ShapeIndex
    {
        self.object
    }

    /// The cells, column by column.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn cells(&self) -> &[Cell]
    {
        &self.cells
    }

    /// The outer grafts.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn outer(&self) -> &[Graft]
    {
        &self.outer
    }

    /// The inner grafts.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn inner(&self) -> &[InnerGraft]
    {
        &self.inner
    }
}

/// How a level-two object fails to be the colimit of its cells against a
/// test object.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum LevelDefect
{
    /// The level-one certificate holds no cocone of the outer shape or of a
    /// column, or the wreath holds no cell or inclusion of the column at
    /// this outer vertex.
    Uncovered
    {
        /// The outer vertex.
        column: Edge,
    },
    /// A map out of the object whose restriction is no agreeing family.
    Stray
    {
        /// The map.
        map: TwoMap,
    },
    /// An agreeing family two maps restrict to.
    Ambiguous
    {
        /// The family, one map per cell.
        family: Box<[TwoMap]>,
    },
    /// An agreeing family no map restricts to: the cells cover the object, and
    /// their union does not determine its maps.
    Unmediated
    {
        /// The family, one map per cell.
        family: Box<[TwoMap]>,
    },
}

impl fmt::Display for LevelDefect
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
        let family = |f: &mut fmt::Formatter<'_>, name: &str, maps: &[TwoMap]| -> fmt::Result {
            f.write_str(name)?;
            for (position, map) in maps.iter().enumerate() {
                let separator = if position == 0 { " " } else { " ; " };
                write!(f, "{separator}{map}")?;
            }
            Ok(())
        };
        match *self {
            Self::Uncovered { column } => {
                write!(
                    f,
                    "no cell included at outer vertex {}",
                    usize::from(column)
                )
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

/// A level-two object that is not the colimit of its cells, the test object
/// it fails against, and how.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct LevelFailure
{
    /// The object.
    pub object: TwoShape,
    /// The object the restriction is no bijection into.
    pub test: TwoShape,
    /// How it fails.
    pub defect: LevelDefect,
}

impl fmt::Display for LevelFailure
{
    /// Writes the object, the test object and the defect.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(f, "{} against {}: {}", self.object, self.test, self.defect)
    }
}

/// Why level two is not certified at a degree.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum LevelUncertified
{
    /// The degree is zero, or above every object of the wreath.
    Degree
    {
        /// The degree asked for.
        degree: Degree,
    },
    /// The grounded objects are not a direct category with automorphisms: a
    /// map between two of them lowers, or keeps the degree without being
    /// invertible. The level-one warrant does not climb.
    Direct
    {
        /// The first such map.
        case: Box<MapCase<TwoShape, TwoMap>>,
    },
    /// An object of degree two to the degree is not the colimit of its
    /// cells.
    Condition
    {
        /// The first failure.
        failure: Box<LevelFailure>,
    },
}

impl fmt::Display for LevelUncertified
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
            Self::Degree { degree } => {
                write!(f, "no level-two object of degree {}", usize::from(degree))
            },
            Self::Direct { ref case } => write!(
                f,
                "the grounded objects are not direct: {} from {} to {}",
                case.map(),
                case.source(),
                case.target()
            ),
            Self::Condition { ref failure } => write!(f, "{failure}"),
        }
    }
}

impl core::error::Error for LevelUncertified
{
}

/// Level two certified at a degree from level one's certificate, which it
/// holds.
///
/// The wreath of a catalogue over itself whose grounded objects are a direct
/// category with automorphisms and whose objects of degree two to the degree
/// are each the colimit of their cells.
#[derive(Clone, Debug)]
pub struct WreathStratum<'level>
{
    /// The wreath.
    wreath: &'level Two,
    /// Level one's certificate over the wreath's catalogue.
    below: SegalStratum,
    /// The degree.
    degree: Degree,
    /// The cocone of each object of degree two to the degree, in wreath
    /// order.
    cocones: Vec<WreathCocone>,
}

impl<'level> WreathStratum<'level>
{
    /// Certifies `wreath`, built over `below`'s catalogue as both its outer and
    /// its inner level, at `degree`, consuming `below`.
    ///
    /// # Specification
    /// - ensures: certified exactly when `degree` is at least one and no
    ///   greater than some object's degree, the grounded objects are direct
    ///   with automorphisms, and every object of degree two to `degree` is the
    ///   colimit of its cells against every object of the wreath.
    /// - fails: [`LevelUncertified::Degree`] for a degree out of range; then
    ///   [`LevelUncertified::Direct`] at the first map between grounded objects
    ///   out of order; then [`LevelUncertified::Condition`] at the first object
    ///   and test object.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`LevelUncertified`] — as above.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — over the chain restriction at total size thirteen the
    ///   whisker, the horizontal composite and the vertical composite are
    ///   certified, with the cocone counts pinned; L3 — over `W ≀ W` two
    ///   2-cells each the other's source are refused by the carrier.
    /// - witness: `tests::stratum::the_whisker_and_both_composites_are_certified_at_level_two`
    /// - witness: `tests::stratum::two_cells_each_the_others_source_are_refused_at_level_two`
    #[inline]
    #[spec(ensures: |ref result| match *result {
        Ok(ref stratum) => stratum.cocones.iter().all(|cocone| {
            wreath.objects().get(usize::from(cocone.object)).is_some_and(|object| within(object, degree) == Membership::Inside)
        }),
        Err(LevelUncertified::Condition { ref failure }) => within(&failure.object, degree) == Membership::Inside,
        Err(_) => true,
    })]
    pub fn certify(
        wreath: &'level Two,
        degree: Degree,
        below: SegalStratum,
    ) -> Result<Self, LevelUncertified>
    {
        if degree < Degree::from(1_usize)
            || wreath
                .objects()
                .iter()
                .all(|object| Two::degree(object) < degree)
        {
            return Err(LevelUncertified::Degree { degree });
        }
        if let Outcome::Fails { witness, .. } = direct_core(&Site::new(wreath)) {
            return Err(LevelUncertified::Direct {
                case: Box::new(witness),
            });
        }
        let (outcome, cocones) = walk(wreath, &below, degree);
        if let Outcome::Fails { witness, .. } = outcome {
            return Err(LevelUncertified::Condition {
                failure: Box::new(witness),
            });
        }
        Ok(Self {
            wreath,
            below,
            degree,
            cocones,
        })
    }

    /// The degree.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn degree(&self) -> Degree
    {
        self.degree
    }

    /// The wreath.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn wreath(&self) -> &'level Two
    {
        self.wreath
    }

    /// Level one's certificate, which this one is built from.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn below(&self) -> &SegalStratum
    {
        &self.below
    }

    /// The cocone of each object of degree two to the degree, in wreath
    /// order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn cocones(&self) -> &[WreathCocone]
    {
        &self.cocones
    }
}

/// Whether `object` is of degree two to `degree`, an object the condition at
/// `degree` reads.
///
/// # Specification
/// trivial.
fn within(
    object: &TwoShape,
    degree: Degree,
) -> Membership
{
    let of = Two::degree(object);
    if of >= Degree::from(2_usize) && of <= degree {
        Membership::Inside
    }
    else {
        Membership::Outside
    }
}

/// Whether every object of degree two to `degree` of `wreath` is the colimit
/// of its cells, over `below`, level one's certificate of the catalogue the
/// wreath is built over.
///
/// # Specification
/// - ensures: holds exactly when, for every object of degree two to `degree`
///   and every object of the wreath, restriction along the object's cells is a
///   bijection from its maps into the test object onto the agreeing families;
///   after one case per pair; the first failing pair otherwise.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — the chain restriction holds at total size thirteen, and
///   the wirings' wreath at total size five, the case count pinned; L3 — two
///   2-cells each the other's source are refused by the carrier.
/// - witness: `tests::stratum::the_whisker_and_both_composites_are_certified_at_level_two`
/// - witness: `tests::stratum::two_cells_each_the_others_source_are_refused_at_level_two`
#[inline]
#[must_use]
#[spec(ensures: |ref outcome| match *outcome {
    Outcome::Holds { .. } => true,
    Outcome::Fails { ref witness, .. } => within(&witness.object, degree) == Membership::Inside,
})]
pub fn segal_two(
    wreath: &Two,
    below: &SegalStratum,
    degree: Degree,
) -> Outcome<LevelFailure>
{
    walk(wreath, below, degree).0
}

/// The condition's outcome, and the cocone of every object it read.
///
/// # Specification
/// - ensures: the outcome [`segal_two`] states; the cocones of the objects of
///   degree two to `degree` in wreath order, up to the failing object.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — the cocone counts at degrees five and eleven over the
///   chain restriction, and at total size five over `W ≀ W`, are pinned.
/// - witness: `tests::stratum::the_whisker_and_both_composites_are_certified_at_level_two`
/// - witness: `tests::stratum::two_cells_each_the_others_source_are_refused_at_level_two`
#[spec(ensures: |ref ret| ret.1.iter().all(|cocone| {
    wreath.objects().get(usize::from(cocone.object)).is_some_and(|object| within(object, degree) == Membership::Inside)
}))]
fn walk(
    wreath: &Two,
    below: &SegalStratum,
    degree: Degree,
) -> (Outcome<LevelFailure>, Vec<WreathCocone>)
{
    let mut tally = Tally::default();
    let mut read = Vec::new();
    for (position, object) in wreath.objects().iter().enumerate() {
        if within(object, degree) == Membership::Outside {
            continue;
        }
        let index = ShapeIndex::from(position);
        let cocone = match cocone(wreath, below, (index, object)) {
            Ok(cocone) => cocone,
            Err(defect) => {
                tally.count();
                return (
                    tally.fails(LevelFailure {
                        object: object.clone(),
                        test: object.clone(),
                        defect,
                    }),
                    read,
                );
            },
        };
        for (at, test) in wreath.objects().iter().enumerate() {
            tally.count();
            if let Err(defect) = colimit(wreath, &cocone, ShapeIndex::from(at)) {
                return (
                    tally.fails(LevelFailure {
                        object: object.clone(),
                        test: test.clone(),
                        defect,
                    }),
                    read,
                );
            }
        }
        read.push(cocone);
    }
    (tally.holds(), read)
}

/// Level one's cocone of `shape`, from `below`: its corolla inclusions, one per
/// vertex, and its grafts. A shape of one vertex and no inner wire is its own
/// corolla; the empty shape has no inclusion.
///
/// # Specification
/// trivial.
fn level_one(
    below: &SegalStratum,
    shape: &Shape,
) -> Maybe<(Vec<Inclusion>, Vec<Graft>), ()>
{
    let catalogue = below.catalogue();
    let Maybe::Present(index) = <Catalogue as Level>::find(catalogue, shape)
    else {
        return Maybe::Absent(());
    };
    if Degree::of(shape) < Degree::from(2_usize) {
        let own = shape.vertices().map(|_| Inclusion {
            corolla: index,
            map: SiteMap::identity(shape),
        });
        return Maybe::Present((own.collect(), Vec::new()));
    }
    below
        .cocones()
        .iter()
        .find(|cocone| cocone.shape() == index)
        .map_or(Maybe::Absent(()), |cocone| {
            Maybe::Present((cocone.inclusions().to_vec(), cocone.grafts().to_vec()))
        })
}

/// The cocone of the wreath's object `object` at `index`.
///
/// # Specification
/// - ensures: one cell per vertex of each non-empty column and one per empty
///   column, column by column; the outer grafts are the outer shape's level-one
///   grafts and the inner grafts each column's.
/// - fails: [`LevelDefect::Uncovered`] at the first outer vertex whose column,
///   corolla, cell or inclusion level one or the wreath does not hold.
/// - panics: none.
///
/// # Errors
/// - [`LevelDefect::Uncovered`] — as above.
///
/// # Adequacy
/// - hypothesis: L2 — the whisker's, the horizontal composite's and the
///   vertical composite's spots and graft counts are pinned.
/// - witness: `tests::stratum::the_whisker_and_both_composites_are_certified_at_level_two`
#[spec(ensures: |ref ret| ret.as_ref().map_or(true, |cocone| {
    cocone.object == index && cocone.cells.iter().all(|cell| usize::from(cell.column) < object.columns().len())
}))]
fn cocone(
    wreath: &Two,
    below: &SegalStratum,
    (index, object): (ShapeIndex, &TwoShape),
) -> Result<WreathCocone, LevelDefect>
{
    let catalogue = below.catalogue();
    let first = LevelDefect::Uncovered {
        column: Edge::from(0_usize),
    };
    let Maybe::Present((outer_inclusions, outer_grafts)) = level_one(below, object.outer())
    else {
        return Err(first);
    };
    let corolla = |at: ShapeIndex| match catalogue.shape(at) {
        Maybe::Present(shape) => Some(shape.clone()),
        Maybe::Absent(_) => None,
    };
    let mut cells = Vec::new();
    let mut inner = Vec::new();
    for (position, (outer, column)) in outer_inclusions.iter().zip(object.columns()).enumerate() {
        let vertex = Edge::from(position);
        let uncovered = LevelDefect::Uncovered { column: vertex };
        let outer_corolla = corolla(outer.corolla).ok_or_else(|| uncovered.clone())?;
        let places: Vec<(Spot, Shape, Maybe<SiteMap, ()>)> =
            if usize::from(column.vertex_count()) == 0 {
                vec![(Spot::Empty, Shape::default(), Maybe::Absent(()))]
            }
            else {
                let Maybe::Present((inclusions, grafts)) = level_one(below, column)
                else {
                    return Err(uncovered);
                };
                inner.extend(grafts.into_iter().map(|graft| InnerGraft {
                    column: vertex,
                    graft,
                }));
                let mut places = Vec::with_capacity(inclusions.len());
                for (at, inclusion) in inclusions.into_iter().enumerate() {
                    let shape = corolla(inclusion.corolla).ok_or_else(|| uncovered.clone())?;
                    places.push((
                        Spot::Vertex(Edge::from(at)),
                        shape,
                        Maybe::Present(inclusion.map),
                    ));
                }
                places
            };
        for (spot, column_shape, inner_map) in places {
            let cell = WreathShape::new(outer_corolla.clone(), vec![column_shape])
                .map_err(|_columns| uncovered.clone())?;
            let Maybe::Present(at) = wreath.find(&cell)
            else {
                return Err(uncovered);
            };
            let map = wreath
                .hom(at, index)
                .iter()
                .find(|map| {
                    *map.outer() == outer.map
                        && match inner_map {
                            Maybe::Present(ref inner_map) => {
                                matches!(map.column(Edge::from(0_usize)), [(to, onto)] if *to == vertex && onto == inner_map)
                            },
                            Maybe::Absent(()) => true,
                        }
                })
                .cloned()
                .ok_or_else(|| uncovered.clone())?;
            cells.push(Cell {
                column: vertex,
                spot,
                object: at,
                map,
            });
        }
    }
    Ok(WreathCocone {
        object: index,
        cells: cells.into_boxed_slice(),
        outer: outer_grafts.into_boxed_slice(),
        inner: inner.into_boxed_slice(),
    })
}

/// Whether `cocone`'s object is the colimit of its cells against the wreath's
/// object at `test`.
///
/// # Specification
/// - ensures: `Ok` exactly when restriction along the cells sends the maps into
///   `test` one to one onto the agreeing families.
/// - fails: as [`bijection`].
/// - panics: none.
///
/// # Errors
/// - [`LevelDefect`] — as above.
///
/// # Adequacy
/// - hypothesis: L2 — over the chain restriction the whole cover of the outer
///   2-chain of empty columns is a colimit against every test object, and with
///   its outer graft left out it leaves a family unmediated.
/// - witness: `ascent::tests::a_cover_without_its_outer_graft_leaves_a_family_unmediated`
/// - witness: `tests::stratum::the_whisker_and_both_composites_are_certified_at_level_two`
#[spec(ensures: |ref ret| match *ret {
    Err(LevelDefect::Unmediated { ref family } | LevelDefect::Ambiguous { ref family }) => family.len() == cocone.cells.len(),
    Ok(()) | Err(_) => true,
})]
fn colimit(
    wreath: &Two,
    cocone: &WreathCocone,
    test: ShapeIndex,
) -> Result<(), LevelDefect>
{
    let candidates: Vec<&[TwoMap]> = cocone
        .cells
        .iter()
        .map(|cell| wreath.hom(cell.object, test))
        .collect();
    let found = families(&candidates, |chosen, cursor| {
        agrees(cocone, &candidates, chosen, cursor)
    });
    let restrict =
        |position: usize, map: &TwoMap| Two::then(&cocone.cells.get(position)?.map, map).ok();
    bijection(
        &candidates,
        &found,
        wreath.hom(cocone.object, test),
        restrict,
    )
    .map_err(|mismatch| match mismatch {
        Mismatch::Stray { map } => LevelDefect::Stray { map },
        Mismatch::Unmediated { family } => LevelDefect::Unmediated { family },
        Mismatch::Ambiguous { family } => LevelDefect::Ambiguous { family },
    })
}

/// Whether the candidate at `cursor` for the cell after `chosen` keeps the
/// partial family agreeing with every earlier cell: one outer map per column,
/// the outer grafts and the outer images apart across columns, the inner
/// grafts and the inner images apart within one.
///
/// # Specification
/// trivial.
fn agrees(
    cocone: &WreathCocone,
    candidates: &[&[TwoMap]],
    chosen: &[Choice],
    cursor: Choice,
) -> Membership
{
    let level = chosen.len();
    let pick = |cell: usize, position: Choice| candidates.get(cell)?.get(usize::from(position));
    let (Some(map), Some(mine)) = (pick(level, cursor), cocone.cells.get(level))
    else {
        return Membership::Outside;
    };
    let kept = chosen.iter().enumerate().all(|(earlier, &position)| {
        let (Some(other), Some(theirs)) = (pick(earlier, position), cocone.cells.get(earlier))
        else {
            return false;
        };
        let agreement = if mine.column == theirs.column {
            same_column(cocone, (mine, map), (theirs, other))
        }
        else {
            across_columns(cocone, (mine, map), (theirs, other))
        };
        agreement == Membership::Inside
    });
    if kept {
        Membership::Inside
    }
    else {
        Membership::Outside
    }
}

/// Whether two cells of one column agree: one outer map, and at each vertex
/// of its image the inner maps agree along every inner graft joining the two
/// cells and have disjoint images.
///
/// # Specification
/// trivial.
fn same_column(
    cocone: &WreathCocone,
    (mine, map): (&Cell, &TwoMap),
    (theirs, other): (&Cell, &TwoMap),
) -> Membership
{
    if map.outer() != other.outer() {
        return Membership::Outside;
    }
    let (left, right) = (
        map.column(Edge::from(0_usize)),
        other.column(Edge::from(0_usize)),
    );
    let (Spot::Vertex(at), Spot::Vertex(there)) = (mine.spot, theirs.spot)
    else {
        return Membership::Inside;
    };
    let kept = left.iter().zip(right).all(|(first, second)| {
        let glued = cocone
            .inner
            .iter()
            .filter(|inner| inner.column == mine.column)
            .all(|inner| {
                let (producer, consumer) = (inner.graft.producer, inner.graft.consumer);
                let wire = |map: &SiteMap, leg: crate::segal::Leg| {
                    map.wires().get(usize::from(leg.wire)).copied()
                };
                if producer.vertex == at && consumer.vertex == there {
                    wire(&first.1, producer) == wire(&second.1, consumer)
                }
                else if consumer.vertex == at && producer.vertex == there {
                    wire(&first.1, consumer) == wire(&second.1, producer)
                }
                else {
                    true
                }
            });
        first.0 == second.0
            && glued
            && first.1.image_union().intersection(second.1.image_union()) == VertexSet::EMPTY
    });
    if kept {
        Membership::Inside
    }
    else {
        Membership::Outside
    }
}

/// Whether two cells of different columns agree: their outer maps agree along
/// every outer graft joining the two columns and have disjoint images.
///
/// # Specification
/// trivial.
fn across_columns(
    cocone: &WreathCocone,
    (mine, map): (&Cell, &TwoMap),
    (theirs, other): (&Cell, &TwoMap),
) -> Membership
{
    let wire = |map: &TwoMap, leg: crate::segal::Leg| {
        map.outer().wires().get(usize::from(leg.wire)).copied()
    };
    let glued = cocone.outer.iter().all(|graft| {
        let (producer, consumer) = (graft.producer, graft.consumer);
        if producer.vertex == mine.column && consumer.vertex == theirs.column {
            wire(map, producer) == wire(other, consumer)
        }
        else if consumer.vertex == mine.column && producer.vertex == theirs.column {
            wire(map, consumer) == wire(other, producer)
        }
        else {
            true
        }
    });
    let apart = map
        .outer()
        .image_union()
        .intersection(other.outer().image_union())
        == VertexSet::EMPTY;
    if glued && apart {
        Membership::Inside
    }
    else {
        Membership::Outside
    }
}
