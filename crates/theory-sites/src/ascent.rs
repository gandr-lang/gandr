//! The stratum across levels: the Segal certificate of level `n + 1`, built
//! from level `n`'s.
//!
//! # The cells
//!
//! An object of level `n + 1` is an outer shape whose vertices carry objects
//! of level `n`, the columns. Its cells are one per cell of each column: the
//! column's outer vertex, as the corolla of its outer legs, carrying that cell
//! of the column. A column of level one has one cell per vertex, the corolla
//! of that vertex's inner legs. A column above level one has the cells its own
//! cocone names. An empty column has one cell, the outer corolla carrying the
//! empty object: the whisker's 1-cell. A cell's inclusion is read off the
//! certificates below: the outer corolla's inclusion at the column's vertex
//! from the outer shape's [`crate::Cocone`], and the column's cell from the
//! column's cocone at level `n`. Level `n + 1` finds the one wreath map
//! carrying both and never builds a cocone of a lower level again.
//!
//! # The certificate below
//!
//! A [`Certificate`] is what the level above reads of a level: each column's
//! cells, the glue between them, and whether two cells' maps agree.
//! [`SegalStratum`] answers it at level one, and a [`WreathStratum`] at its own
//! level, so level three is `WreathStratum<WreathStratum>`. The outer shape of
//! every level is a level-one shape, so every level reads level one's cocone
//! of its outer shape, which each certificate carries as its floor.
//!
//! # The grafts
//!
//! The cocone glues the cells by two kinds of glue. An outer graft is a graft
//! of the outer shape's level-one cocone: an inner wire of the outer shape,
//! glueing every cell of its producer's column to every cell of its
//! consumer's. A column's glue is the glue of its own cocone. At level one it
//! is a graft, an inner wire of the column glueing two cells of that column.
//! Above level one it is the column's object, whose cocone glues its cells.
//!
//! A family of maps out of the cells into a test object agrees when the cells
//! of one column take one outer map, the columns' outer maps agree along every
//! outer graft and have disjoint images, and, within a column, at each vertex
//! of the column's outer image, the inner maps agree as the level below reads
//! agreement. At level one they agree along every graft and have disjoint
//! images. These are the admitted families of level one, read once at each
//! level. The condition holds at an object when restriction along the cells
//! is a bijection from its maps into each test object onto the agreeing
//! families.
//!
//! # What the certificate reads
//!
//! The certificate reads the grafting pushouts and the raising maps, never a
//! lowering span. [`WreathStratum::certify`] checks that the grounded objects
//! of the level, with the empty column among them, form a direct category
//! with automorphisms, the condition the level-one univalence warrant climbs
//! through. The pushout inside an empty column, whose pushed-out map lowers,
//! stays outside what it reads. The empty column is the unit of the level, a
//! fat object, and [`crate::Wreath`] states why the site keeps it.
//!
//! # The evidence
//!
//! Over the chains to total size 13 and `W ≀ W` to 5, the grounded objects
//! of level two and their raising maps form a direct category with
//! automorphisms (766 and 709 cases), the condition the certificate carries.
//! Every level-two object to the bound is the colimit of its cells, and none
//! of `W ≀ W` fails to size 7. Over the chains at level three to total size
//! 11, the grounded objects form a direct category with automorphisms (271
//! cases), and every object of degree two to the top is the colimit of its
//! cells: 150 cocones of 401 cells, read from level two's 51 (22,950 cases).
//! To total size 13 the same holds over 410 cocones of 1,338 cells. Over the
//! level-three schemes to total size 13, the site's 1,008 maps are each a map
//! of Θ₃ by Definition 1, no two alike.
//!
//! # The pinwheel
//!
//! A shape whose cells meet in a cycle has no composite: its cells cover it,
//! and their union does not determine its maps. No level holds one. The
//! carrier refuses a wiring with a directed cycle as
//! `WiringObstruction::DirectedCycle`, at the outer level and in every column:
//! Leclerc and Mimram's Lemma 3, that a pasting scheme is acyclic. So the
//! cells of an object are ordered within each column, and the columns along
//! the outer shape. The condition names an agreeing family no map restricts to
//! [`LevelDefect::Unmediated`]. Over `W ≀ W` at total size seven no object
//! reaches it. A cover with its outer graft left out does.
//!
//! # References
//!
//! - `Ruit-2024-pasting_theorem_iterated_segal_spaces` — exemplar: the pasting
//!   theorem this certificate instances, a composable shape the union of its
//!   cover (Theorem 3.49, Corollaries 3.52 and 3.55), proved by induction on
//!   the dimension; § 3.2 and Example 3.54, the pinwheel, a shape whose cover
//!   does not determine its maps.
//! - `Leclerc-2026-cellular_type_theory` — background: Lemma 3, a pasting
//!   scheme is acyclic, the pinwheel's refusal; Definition 1, Θₙ₊₁ as `Δ ≀ Θₙ`,
//!   which `tests::oracle` enumerates beside the site's maps at levels two and
//!   three; § 2.6.2, the Segal condition at a wedge, which this cover meets
//!   once a column split reads its 1-cell at the shared inner wire.

#[cfg(test)]
mod tests;

mod image;

use alloc::boxed::Box;
use alloc::sync::Arc;
use alloc::vec;
use alloc::vec::Vec;
use core::fmt;
use core::hash::Hash;

use anodized::spec;
use gandr_theory_circuit_algebras::Edge;
use gandr_theory_circuit_algebras::Wire;
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
use crate::segal::Leg;
use crate::segal::Mismatch;
use crate::segal::bijection;
use crate::segal::families;
use crate::shape::Shape;
use crate::stratum::SegalStratum;
use crate::stratum::image::Word;
use crate::wreath::Wreath;
use crate::wreath::WreathMap;
use crate::wreath::WreathShape;

/// An object of the level a certificate certifies.
type ObjectOf<Below> = <<Below as Certificate>::Level as Level>::Object;

/// A map of the level a certificate certifies.
type MapOf<Below> = <<Below as Certificate>::Level as Level>::Map;

/// The level above a certificate's: the wreath of the wiring site over it.
type Above<Below> = Wreath<<Below as Certificate>::Level>;

/// A column's cover, as a certificate names it.
type CoverOf<Below> = Cover<ObjectOf<Below>, MapOf<Below>, <Below as Certificate>::Glue>;

/// How an object of the level above a certificate's fails the condition.
type FailureOf<Below> = LevelFailure<ObjectOf<Below>, MapOf<Below>>;

/// The condition's outcome over the level above a certificate's, and the
/// cocones it read.
type Walked<Below> = (Outcome<FailureOf<Below>>, Vec<AboveCocone<Below>>);

/// A cell's place in its column: its spot, its object of the level below,
/// and its inclusion into the column, absent at an empty column.
type Place<Below> = (Spot, ObjectOf<Below>, Maybe<MapOf<Below>, ()>);

/// The cocone of an object of the level above a certificate's.
type AboveCocone<Below> = WreathCocone<MapOf<Below>, <Below as Certificate>::Glue>;

/// A column's cells, as the level above reads them.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Cover<Object, Map, Glue>
{
    /// The column is empty, and its one cell is the outer corolla carrying the
    /// empty object.
    Empty,
    /// The column's cells, each its object with its inclusion into the column,
    /// and the glue between them.
    Cells
    {
        /// The cells, in the order the column's cocone holds them.
        cells: Vec<(Object, Map)>,
        /// The glue between the cells.
        glue: Vec<Glue>,
    },
}

/// The certificate of a level, as the level above reads it: each column's
/// cells and their glue, whether two cells' maps agree, and level one's
/// certificate of every outer shape.
///
/// # Specification
/// - provides: a column's cover and the agreement of two of its cells' maps,
///   read off the level's own certificate, and the glue's words in an image.
/// - requires: [`Certificate::cover`] names a column's cells in the order its
///   cocone holds them, [`Certificate::agree`] answers the agreement that
///   cocone's colimit reads, and [`Certificate::read_glue`] reads back what
///   [`Certificate::write_glue`] writes.
pub trait Certificate: Clone + fmt::Debug
{
    /// The certified level.
    type Level: Level + Clone + fmt::Debug;
    /// What glues a column's cells: a graft at level one, and the column's
    /// object above it.
    type Glue: Copy + fmt::Debug + Eq + Hash + Ord;

    /// The level's number, one at the catalogue: the level above's image
    /// leads with its successor.
    ///
    /// # Specification
    /// trivial.
    const LEVEL: u8;

    /// The certified level.
    ///
    /// # Specification
    /// trivial.
    fn level(&self) -> &Self::Level;

    /// Level one's certificate, which every level's outer shape reads.
    ///
    /// # Specification
    /// trivial.
    fn floor(&self) -> &SegalStratum;

    /// The cells of `column`, an object of the level, and their glue; absent
    /// when the certificate holds no cocone of it.
    ///
    /// # Specification
    /// trivial.
    fn cover(
        &self,
        column: &ObjectOf<Self>,
    ) -> Maybe<CoverOf<Self>, ()>;

    /// Whether the maps out of the cells at `mine` and `theirs` of one
    /// column's cover, glued by `glue`, agree as that cover's colimit reads
    /// agreement.
    ///
    /// # Specification
    /// trivial.
    fn agree(
        &self,
        glue: &[ColumnGlue<Self::Glue>],
        mine: (Edge, &MapOf<Self>),
        theirs: (Edge, &MapOf<Self>),
    ) -> Membership;

    /// Hands each word of `glue`, in order, to `word`.
    ///
    /// # Specification
    /// trivial.
    fn write_glue(
        glue: Self::Glue,
        word: &mut dyn FnMut(usize),
    );

    /// The glue the next words `word` yields spell; none when it runs out.
    ///
    /// # Specification
    /// trivial.
    fn read_glue(word: &mut dyn FnMut() -> Option<usize>) -> Option<Self::Glue>;
}

impl Certificate for SegalStratum
{
    type Glue = Graft;
    type Level = Catalogue;

    const LEVEL: u8 = 1;

    /// The catalogue.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn level(&self) -> &Catalogue
    {
        self.catalogue()
    }

    /// This certificate, level one's.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn floor(&self) -> &SegalStratum
    {
        self
    }

    /// The empty column, or the column's corollas with their inclusions and
    /// its grafts, from its level-one cocone.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn cover(
        &self,
        column: &Shape,
    ) -> Maybe<Cover<Shape, SiteMap, Graft>, ()>
    {
        if usize::from(column.vertex_count()) == 0 {
            return Maybe::Present(Cover::Empty);
        }
        let Maybe::Present((inclusions, glue)) = level_one(self, column)
        else {
            return Maybe::Absent(());
        };
        let mut cells = Vec::with_capacity(inclusions.len());
        for inclusion in inclusions {
            let Maybe::Present(corolla) = self.catalogue().shape(inclusion.corolla)
            else {
                return Maybe::Absent(());
            };
            cells.push((corolla.clone(), inclusion.map));
        }
        Maybe::Present(Cover::Cells { cells, glue })
    }

    /// Whether the two corollas' maps agree along every graft joining them
    /// and have disjoint images.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn agree(
        &self,
        glue: &[ColumnGlue<Graft>],
        (at, map): (Edge, &SiteMap),
        (there, other): (Edge, &SiteMap),
    ) -> Membership
    {
        let wire = |map: &SiteMap, leg: Leg| map.wires().get(usize::from(leg.wire)).copied();
        let glued = glue.iter().all(|inner| {
            let (producer, consumer) = (inner.glue.producer, inner.glue.consumer);
            if producer.vertex == at && consumer.vertex == there {
                wire(map, producer) == wire(other, consumer)
            }
            else if consumer.vertex == at && producer.vertex == there {
                wire(map, consumer) == wire(other, producer)
            }
            else {
                true
            }
        });
        if glued && map.image_union().intersection(other.image_union()) == VertexSet::EMPTY {
            Membership::Inside
        }
        else {
            Membership::Outside
        }
    }

    /// Hands the graft's wire, then each leg's vertex and wire, to `word`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn write_glue(
        glue: Graft,
        word: &mut dyn FnMut(usize),
    )
    {
        for each in graft_words(glue) {
            word(usize::from(each));
        }
    }

    /// The graft the next five words spell, as [`Certificate::write_glue`]
    /// writes it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn read_glue(word: &mut dyn FnMut() -> Option<usize>) -> Option<Graft>
    {
        let mut words = [Word::from(0_usize); GRAFT_WORDS];
        for slot in &mut words {
            *slot = Word::from(word()?);
        }
        Some(graft_from(words))
    }
}

/// How many words spell a graft: its wire, then each leg's vertex and wire.
const GRAFT_WORDS: usize = 5;

/// `graft`'s words: its wire, then its producer's and its consumer's vertex
/// and wire.
///
/// # Specification
/// trivial.
fn graft_words(graft: Graft) -> [Word; GRAFT_WORDS]
{
    [
        usize::from(graft.wire),
        usize::from(graft.producer.vertex),
        usize::from(graft.producer.wire),
        usize::from(graft.consumer.vertex),
        usize::from(graft.consumer.wire),
    ]
    .map(Word::from)
}

/// The graft `words` spell, as [`graft_words`] writes it.
///
/// # Specification
/// trivial.
fn graft_from(words: [Word; GRAFT_WORDS]) -> Graft
{
    let [wire, from, out, to, into] = words.map(usize::from);
    Graft {
        wire: Wire::from(wire),
        producer: Leg {
            vertex: Edge::from(from),
            wire: Wire::from(out),
        },
        consumer: Leg {
            vertex: Edge::from(to),
            wire: Wire::from(into),
        },
    }
}

impl<Below: Certificate> Certificate for WreathStratum<Below>
{
    type Glue = ShapeIndex;
    type Level = Above<Below>;

    const LEVEL: u8 = Below::LEVEL.saturating_add(1);

    /// The wreath.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn level(&self) -> &Above<Below>
    {
        &self.wreath
    }

    /// Level one's certificate, which the level below carries.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn floor(&self) -> &SegalStratum
    {
        self.below.floor()
    }

    /// The empty column, the column as its own cell below degree two, or the
    /// cells of the column's cocone, glued by the column's object.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn cover(
        &self,
        column: &WreathShape<ObjectOf<Below>>,
    ) -> Maybe<Cover<WreathShape<ObjectOf<Below>>, WreathMap<MapOf<Below>>, ShapeIndex>, ()>
    {
        if usize::from(column.outer().vertex_count()) == 0 {
            return Maybe::Present(Cover::Empty);
        }
        let Maybe::Present(index) = self.wreath.find(column)
        else {
            return Maybe::Absent(());
        };
        if <Above<Below>>::degree(column) < Degree::from(2_usize) {
            return Maybe::Present(Cover::Cells {
                cells: vec![(column.clone(), <Above<Below>>::identity(column))],
                glue: Vec::new(),
            });
        }
        let Some(cocone) = self.cocone_at(index)
        else {
            return Maybe::Absent(());
        };
        let objects = self.wreath.objects();
        let cells: Option<Vec<_>> = cocone
            .cells
            .iter()
            .map(|cell| {
                objects
                    .get(usize::from(cell.object))
                    .map(|object| (object.clone(), cell.map.clone()))
            })
            .collect();
        cells.map_or(Maybe::Absent(()), |cells| {
            Maybe::Present(Cover::Cells {
                cells,
                glue: vec![index],
            })
        })
    }

    /// Whether the two cells of the column's cocone agree as that cocone's
    /// colimit reads them.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn agree(
        &self,
        glue: &[ColumnGlue<ShapeIndex>],
        (at, map): (Edge, &WreathMap<MapOf<Below>>),
        (there, other): (Edge, &WreathMap<MapOf<Below>>),
    ) -> Membership
    {
        let Some(&ColumnGlue { glue: object, .. }) = glue.first()
        else {
            return Membership::Inside;
        };
        let Some(cocone) = self.cocone_at(object)
        else {
            return Membership::Outside;
        };
        match (
            cocone.cells.get(usize::from(at)),
            cocone.cells.get(usize::from(there)),
        ) {
            (Some(mine), Some(theirs)) => pair(cocone, &self.below, (mine, map), (theirs, other)),
            _ => Membership::Outside,
        }
    }

    /// Hands the column's object's index to `word`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn write_glue(
        glue: ShapeIndex,
        word: &mut dyn FnMut(usize),
    )
    {
        word(usize::from(glue));
    }

    /// The object index the next word spells.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn read_glue(word: &mut dyn FnMut() -> Option<usize>) -> Option<ShapeIndex>
    {
        word().map(ShapeIndex::from)
    }
}

/// Where a cell sits in its column.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Spot
{
    /// The column is empty, and the cell is its 1-cell.
    Empty,
    /// The cell covers the column's cell at this position: at level one, the
    /// column's vertex.
    Vertex(Edge),
}

/// One cell of an object and its inclusion.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Cell<Map = SiteMap>
{
    /// The outer vertex whose column holds the cell.
    pub column: Edge,
    /// Where the cell sits in that column.
    pub spot: Spot,
    /// The cell's object in the wreath.
    pub object: ShapeIndex,
    /// The wreath map from the cell onto its place.
    pub map: WreathMap<Map>,
}

/// The glue of a column's cover, its legs the column's cells.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ColumnGlue<Glue = Graft>
{
    /// The outer vertex whose column it glues.
    pub column: Edge,
    /// The column's glue.
    pub glue: Glue,
}

/// An object's Segal cocone: its cells and the glue between them.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct WreathCocone<Map = SiteMap, Glue = Graft>
{
    /// The object's position in the wreath.
    object: ShapeIndex,
    /// The cells, column by column, each column's in its cover's order.
    cells: Box<[Cell<Map>]>,
    /// The outer shape's grafts, their legs the outer vertices.
    outer: Box<[Graft]>,
    /// The columns' glue, column by column.
    inner: Box<[ColumnGlue<Glue>]>,
}

impl<Map, Glue> WreathCocone<Map, Glue>
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
    pub const fn cells(&self) -> &[Cell<Map>]
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

    /// The columns' glue.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn inner(&self) -> &[ColumnGlue<Glue>]
    {
        &self.inner
    }

    /// The glue of the column at `column`, which the cocone holds column by
    /// column.
    ///
    /// # Specification
    /// trivial.
    fn glue_of(
        &self,
        column: Edge,
    ) -> &[ColumnGlue<Glue>]
    {
        let start = self.inner.partition_point(|glue| glue.column < column);
        let end = self.inner.partition_point(|glue| glue.column <= column);
        self.inner.get(start .. end).unwrap_or(&[])
    }
}

/// How an object fails to be the colimit of its cells against a test object.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum LevelDefect<Map = SiteMap>
{
    /// The certificate below holds no cocone of the outer shape or of a
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
        map: WreathMap<Map>,
    },
    /// An agreeing family two maps restrict to.
    Ambiguous
    {
        /// The family, one map per cell.
        family: Box<[WreathMap<Map>]>,
    },
    /// An agreeing family no map restricts to: the cells cover the object, and
    /// their union does not determine its maps.
    Unmediated
    {
        /// The family, one map per cell.
        family: Box<[WreathMap<Map>]>,
    },
}

impl<Map: fmt::Display> fmt::Display for LevelDefect<Map>
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
        let family =
            |f: &mut fmt::Formatter<'_>, name: &str, maps: &[WreathMap<Map>]| -> fmt::Result {
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

/// An object that is not the colimit of its cells, the test object it fails
/// against, and how.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct LevelFailure<Object = Shape, Map = SiteMap>
{
    /// The object.
    pub object: WreathShape<Object>,
    /// The object the restriction is no bijection into.
    pub test: WreathShape<Object>,
    /// How it fails.
    pub defect: LevelDefect<Map>,
}

impl<Object, Map> fmt::Display for LevelFailure<Object, Map>
where
    WreathShape<Object>: fmt::Display,
    Map: fmt::Display,
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

/// Why a level is not certified at a degree.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum LevelUncertified<Object = Shape, Map = SiteMap>
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
        case: Box<MapCase<WreathShape<Object>, WreathMap<Map>>>,
    },
    /// An object of degree two to the degree is not the colimit of its
    /// cells.
    Condition
    {
        /// The first failure.
        failure: Box<LevelFailure<Object, Map>>,
    },
}

impl<Object, Map> fmt::Display for LevelUncertified<Object, Map>
where
    WreathShape<Object>: fmt::Display,
    WreathMap<Map>: fmt::Display,
    Map: fmt::Display,
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
                write!(
                    f,
                    "no object of degree {} at the level",
                    usize::from(degree)
                )
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

impl<Object, Map> core::error::Error for LevelUncertified<Object, Map>
where
    Object: fmt::Debug,
    Map: fmt::Debug + fmt::Display,
    WreathShape<Object>: fmt::Display,
    WreathMap<Map>: fmt::Display,
{
}

/// The level above `Below` certified at a degree from `Below`, which it
/// holds: level two over [`SegalStratum`], and level `n + 1` over level
/// `n`'s stratum.
///
/// The wreath of the wiring catalogue over the level below whose grounded
/// objects are a direct category with automorphisms and whose objects of
/// degree two to the degree are each the colimit of their cells.
#[derive(Clone, Debug)]
pub struct WreathStratum<Below: Certificate = SegalStratum>
{
    /// The wreath.
    wreath: Arc<Above<Below>>,
    /// The certificate of the level below.
    below: Below,
    /// The degree.
    degree: Degree,
    /// The cocone of each object of degree two to the degree, in wreath
    /// order.
    cocones: Vec<AboveCocone<Below>>,
}

impl<Below: Certificate> WreathStratum<Below>
{
    /// Certifies `wreath`, built over `below`'s floor catalogue as its outer
    /// level and `below`'s level as its inner, at `degree`, consuming `below`.
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
    ///   2-cells each the other's source are refused by the carrier; L2 — the
    ///   chains at level three certify to total size eleven over level two's
    ///   stratum, with the cocone counts pinned.
    /// - witness: `tests::stratum::the_whisker_and_both_composites_are_certified_at_level_two`
    /// - witness: `tests::stratum::two_cells_each_the_others_source_are_refused_at_level_two`
    /// - witness: `tests::stratum::the_chains_at_level_three_are_certified_from_level_two`
    #[inline]
    #[spec(ensures: |ref result| match *result {
        Ok(ref stratum) => stratum.cocones.iter().all(|cocone| {
            stratum.wreath.objects().get(usize::from(cocone.object)).is_some_and(|object| {
                within(<Above<Below>>::degree(object), degree) == Membership::Inside
            })
        }),
        Err(LevelUncertified::Condition { ref failure }) => {
            within(<Above<Below>>::degree(&failure.object), degree) == Membership::Inside
        },
        Err(_) => true,
    })]
    pub fn certify(
        wreath: Arc<Above<Below>>,
        degree: Degree,
        below: Below,
    ) -> Result<Self, LevelUncertified<ObjectOf<Below>, MapOf<Below>>>
    {
        if degree < Degree::from(1_usize)
            || wreath
                .objects()
                .iter()
                .all(|object| <Above<Below>>::degree(object) < degree)
        {
            return Err(LevelUncertified::Degree { degree });
        }
        if let Outcome::Fails { witness, .. } = direct_core(&Site::new(&*wreath)) {
            return Err(LevelUncertified::Direct {
                case: Box::new(witness),
            });
        }
        let (outcome, cocones) = walk(&wreath, &below, degree);
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
    pub fn wreath(&self) -> &Above<Below>
    {
        &self.wreath
    }

    /// The certificate of the level below, which this one is built from.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn below(&self) -> &Below
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
    pub fn cocones(&self) -> &[AboveCocone<Below>]
    {
        &self.cocones
    }

    /// The cocone of the wreath's object at `object`; none past the degree.
    ///
    /// # Specification
    /// trivial.
    fn cocone_at(
        &self,
        object: ShapeIndex,
    ) -> Option<&AboveCocone<Below>>
    {
        let position = self
            .cocones
            .binary_search_by_key(&object, |cocone| cocone.object)
            .ok()?;
        self.cocones.get(position)
    }
}

/// Whether an object of degree `of` is of degree two to `degree`, an object
/// the condition at `degree` reads.
///
/// # Specification
/// trivial.
fn within(
    of: Degree,
    degree: Degree,
) -> Membership
{
    if of >= Degree::from(2_usize) && of <= degree {
        Membership::Inside
    }
    else {
        Membership::Outside
    }
}

/// Whether every object of degree two to `degree` of `wreath` is the colimit
/// of its cells, over `below`, the certificate of the level the wreath is
/// built over.
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
///   2-cells each the other's source are refused by the carrier; L2 — the
///   chains at level three hold at total size eleven, the case count pinned.
/// - witness: `tests::stratum::the_whisker_and_both_composites_are_certified_at_level_two`
/// - witness: `tests::stratum::two_cells_each_the_others_source_are_refused_at_level_two`
/// - witness: `tests::stratum::the_chains_at_level_three_are_certified_from_level_two`
#[inline]
#[must_use]
#[spec(ensures: |ref outcome| match *outcome {
    Outcome::Holds { .. } => true,
    Outcome::Fails { ref witness, .. } => {
        within(<Above<Below>>::degree(&witness.object), degree) == Membership::Inside
    },
})]
pub fn segal_above<Below>(
    wreath: &Above<Below>,
    below: &Below,
    degree: Degree,
) -> Outcome<FailureOf<Below>>
where
    Below: Certificate,
{
    walk(wreath, below, degree).0
}

/// The condition's outcome, and the cocone of every object it read.
///
/// # Specification
/// - ensures: the outcome [`segal_above`] states; the cocones of the objects of
///   degree two to `degree` in wreath order, up to the failing object.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — the cocone counts at degrees five and eleven over the
///   chain restriction, at total size five over `W ≀ W`, and at level three
///   over the chains at total size eleven, are pinned.
/// - witness: `tests::stratum::the_whisker_and_both_composites_are_certified_at_level_two`
/// - witness: `tests::stratum::two_cells_each_the_others_source_are_refused_at_level_two`
/// - witness: `tests::stratum::the_chains_at_level_three_are_certified_from_level_two`
#[spec(ensures: |ref ret| ret.1.iter().all(|cocone| {
    wreath.objects().get(usize::from(cocone.object)).is_some_and(|object| {
        within(<Above<Below>>::degree(object), degree) == Membership::Inside
    })
}))]
fn walk<Below>(
    wreath: &Above<Below>,
    below: &Below,
    degree: Degree,
) -> Walked<Below>
where
    Below: Certificate,
{
    let mut tally = Tally::default();
    let mut read = Vec::new();
    for (position, object) in wreath.objects().iter().enumerate() {
        if within(<Above<Below>>::degree(object), degree) == Membership::Outside {
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
            if let Err(defect) = colimit(wreath, below, &cocone, ShapeIndex::from(at)) {
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
/// - ensures: one cell per cell of each non-empty column's cover and one per
///   empty column, column by column; the outer grafts are the outer shape's
///   level-one grafts and the columns' glue each column's cover's.
/// - fails: [`LevelDefect::Uncovered`] at the first outer vertex whose column,
///   corolla, cell or inclusion the certificates below or the wreath do not
///   hold.
/// - panics: none.
///
/// # Errors
/// - [`LevelDefect::Uncovered`] — as above.
///
/// # Adequacy
/// - hypothesis: L2 — the whisker's, the horizontal composite's and the
///   vertical composite's spots and graft counts are pinned, and at level three
///   the cells of the vertical composite's suspension.
/// - witness: `tests::stratum::the_whisker_and_both_composites_are_certified_at_level_two`
/// - witness: `tests::stratum::the_chains_at_level_three_are_certified_from_level_two`
#[spec(ensures: |ref ret| ret.as_ref().map_or(true, |cocone| {
    cocone.object == index && cocone.cells.iter().all(|cell| usize::from(cell.column) < object.columns().len())
}))]
fn cocone<Below>(
    wreath: &Above<Below>,
    below: &Below,
    (index, object): (ShapeIndex, &WreathShape<ObjectOf<Below>>),
) -> Result<AboveCocone<Below>, LevelDefect<MapOf<Below>>>
where
    Below: Certificate,
{
    let floor = below.floor();
    let catalogue = floor.catalogue();
    let first = LevelDefect::Uncovered {
        column: Edge::from(0_usize),
    };
    let Maybe::Present((outer_inclusions, outer_grafts)) = level_one(floor, object.outer())
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
        let places: Vec<Place<Below>> = match below.cover(column) {
            Maybe::Absent(()) => return Err(uncovered),
            Maybe::Present(Cover::Empty) => {
                vec![(Spot::Empty, ObjectOf::<Below>::default(), Maybe::Absent(()))]
            },
            Maybe::Present(Cover::Cells {
                cells: covered,
                glue,
            }) => {
                inner.extend(glue.into_iter().map(|glue| ColumnGlue {
                    column: vertex,
                    glue,
                }));
                covered
                    .into_iter()
                    .enumerate()
                    .map(|(at, (shape, map))| {
                        (Spot::Vertex(Edge::from(at)), shape, Maybe::Present(map))
                    })
                    .collect()
            },
        };
        for (spot, column_object, inner_map) in places {
            let cell = WreathShape::new(outer_corolla.clone(), vec![column_object])
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
///   its outer graft left out it leaves a family unmediated; at level three the
///   suspension of the vertical composite, with its column's glue left out,
///   does too.
/// - witness: `ascent::tests::a_cover_without_its_outer_graft_leaves_a_family_unmediated`
/// - witness: `ascent::tests::a_level_three_cover_without_its_column_glue_leaves_a_family_unmediated`
/// - witness: `tests::stratum::the_whisker_and_both_composites_are_certified_at_level_two`
#[spec(ensures: |ref ret| match *ret {
    Err(LevelDefect::Unmediated { ref family } | LevelDefect::Ambiguous { ref family }) => family.len() == cocone.cells.len(),
    Ok(()) | Err(_) => true,
})]
fn colimit<Below>(
    wreath: &Above<Below>,
    below: &Below,
    cocone: &AboveCocone<Below>,
    test: ShapeIndex,
) -> Result<(), LevelDefect<MapOf<Below>>>
where
    Below: Certificate,
{
    let candidates: Vec<&[WreathMap<MapOf<Below>>]> = cocone
        .cells
        .iter()
        .map(|cell| wreath.hom(cell.object, test))
        .collect();
    let found = families(&candidates, |chosen, cursor| {
        agrees(cocone, below, &candidates, chosen, cursor)
    });
    let restrict = |position: usize, map: &WreathMap<MapOf<Below>>| {
        <Above<Below>>::then(&cocone.cells.get(position)?.map, map).ok()
    };
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
/// partial family agreeing with every earlier cell.
///
/// # Specification
/// trivial.
fn agrees<Below>(
    cocone: &AboveCocone<Below>,
    below: &Below,
    candidates: &[&[WreathMap<MapOf<Below>>]],
    chosen: &[Choice],
    cursor: Choice,
) -> Membership
where
    Below: Certificate,
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
        pair(cocone, below, (mine, map), (theirs, other)) == Membership::Inside
    });
    if kept {
        Membership::Inside
    }
    else {
        Membership::Outside
    }
}

/// Whether the maps out of two cells of `cocone` agree: within one column
/// as [`same_column`] reads them, across two as [`across_columns`] does.
///
/// # Specification
/// trivial.
fn pair<Below>(
    cocone: &AboveCocone<Below>,
    below: &Below,
    mine: (&Cell<MapOf<Below>>, &WreathMap<MapOf<Below>>),
    theirs: (&Cell<MapOf<Below>>, &WreathMap<MapOf<Below>>),
) -> Membership
where
    Below: Certificate,
{
    if mine.0.column == theirs.0.column {
        same_column(cocone, below, mine, theirs)
    }
    else {
        across_columns(cocone, mine, theirs)
    }
}

/// Whether two cells of one column agree: one outer map, and at each vertex
/// of its image the inner maps agree as the certificate below reads
/// agreement.
///
/// # Specification
/// trivial.
fn same_column<Below>(
    cocone: &AboveCocone<Below>,
    below: &Below,
    (mine, map): (&Cell<MapOf<Below>>, &WreathMap<MapOf<Below>>),
    (theirs, other): (&Cell<MapOf<Below>>, &WreathMap<MapOf<Below>>),
) -> Membership
where
    Below: Certificate,
{
    if map.outer() != other.outer() {
        return Membership::Outside;
    }
    let (Spot::Vertex(at), Spot::Vertex(there)) = (mine.spot, theirs.spot)
    else {
        return Membership::Inside;
    };
    let glue = cocone.glue_of(mine.column);
    let (left, right) = (
        map.column(Edge::from(0_usize)),
        other.column(Edge::from(0_usize)),
    );
    let kept = left.iter().zip(right).all(|(first, second)| {
        first.0 == second.0
            && below.agree(glue, (at, &first.1), (there, &second.1)) == Membership::Inside
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
fn across_columns<Map, Glue>(
    cocone: &WreathCocone<Map, Glue>,
    (mine, map): (&Cell<Map>, &WreathMap<Map>),
    (theirs, other): (&Cell<Map>, &WreathMap<Map>),
) -> Membership
{
    let wire =
        |map: &WreathMap<Map>, leg: Leg| map.outer().wires().get(usize::from(leg.wire)).copied();
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
