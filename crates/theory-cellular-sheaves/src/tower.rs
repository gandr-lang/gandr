//! A tower of sheaves and the maps that its bonding maps induce on
//! cohomology.
//!
//! A tower is a sequence of levels, the first the coarsest. Each level is a
//! sheaf with an orientation, and a bonding map sends each level onto the one
//! before it. The bonding map sends each cell onto a cell of the same rank,
//! or collapses it into a cell of lower rank. Its pull-back sends the
//! cochains of the coarser level to those of the finer level: a cell that the
//! map collapses carries zero, and any other cell reads its image's cochain
//! through a stalk map, with the sign that the map gives. The crate checks
//! that the pull-back commutes with the coboundaries, so it induces a map on
//! cohomology, and it gives the rank of that map in each degree.
//!
//! The image of the induced map in degree `d` is spanned by the pulled-back
//! cocycles of the coarser level, taken modulo the coboundaries of the finer
//! level. Its rank is the rank of the finer coboundary into `d` beside the
//! pulled-back cocycles, less the rank of that coboundary alone.

use alloc::vec::Vec;

use anodized::spec;
use gandr_theory_graded_posets::Rank;
use gandr_theory_stone_duality::Element;

use crate::cochain::CochainComplex;
use crate::cochain::Cohomology;
use crate::error::SheafError;
use crate::index::Dimension;
use crate::index::Entry;
use crate::index::Incidence;
use crate::index::Level;
use crate::index::Slot;
use crate::index::Width;
use crate::matrix::Matrix;
use crate::matrix::Rational;
use crate::sheaf::Sheaf;

/// Where a bonding map sends a cell of the finer level.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Image<Map>
{
    /// Onto a cell of the coarser level of the same rank.
    Onto
    {
        /// The cell of the coarser level.
        cell: Element,
        /// The sign of the map on the cell: negative where it reverses the
        /// cell's orientation.
        incidence: Incidence,
        /// For each entry of the finer cell's stalk, the entry of the image's
        /// stalk that it reads.
        entries: Map,
    },
    /// Into a cell of lower rank, so the cell carries zero.
    Collapsed,
}

/// A tower of sheaves: each level's cohomology, and the rank of the map each
/// bonding map induces on it.
///
/// # Specification
/// - ensures: one complex and one cohomology for each level, and one list of
///   induced ranks for each level after the first; each bonding map's pull-back
///   commutes with the coboundaries.
/// - provides: each level's cohomology and each induced rank.
/// - panics: none.
/// - executable: none — a type-level block: the invariant is [`Tower::new`]'s
///   and [`Tower::push`]'s, which make it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Tower<Cell>
{
    /// The sheaf of the finest level, which the next bonding map reaches.
    finest: Sheaf<Cell>,
    /// The cochain complex of each level.
    complexes: Vec<CochainComplex>,
    /// The cohomology of each level.
    cohomologies: Vec<Cohomology>,
    /// For each level after the first, the rank of the induced map in each
    /// degree of that level.
    induced: Vec<Vec<Dimension>>,
}

impl<Cell> Tower<Cell>
{
    /// The tower of one level: `sheaf` with the incidences `orientation`
    /// gives.
    ///
    /// # Specification
    /// - ensures: one level, with its cohomology.
    /// - fails: incidences that are not those of a complex are refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`SheafError::NotAComplex`]: the incidences are not those of a
    ///   complex.
    /// - [`SheafError::Overflow`]: an entry passes the integers.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the first level of both towers has the cohomology of
    ///   its space.
    /// - witness: `tests::towers::every_level_of_both_towers_has_the_cohomology_of_its_space`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |tower| tower.complexes.len() == 1 && tower.induced.is_empty()))]
    #[inline]
    pub fn new<Orient>(
        sheaf: Sheaf<Cell>,
        orientation: Orient,
    ) -> Result<Self, SheafError>
    where
        Orient: FnMut(&Cell, &Cell) -> Incidence,
    {
        let complex = sheaf.cochains(orientation)?;
        let cohomology = complex.cohomology()?;
        Ok(Self {
            finest: sheaf,
            complexes: Vec::from([complex]),
            cohomologies: Vec::from([cohomology]),
            induced: Vec::new(),
        })
    }

    /// Adds `finer` as the next level, with the incidences `orientation`
    /// gives and the bonding map onto the last level that `image` gives.
    ///
    /// # Specification
    /// - ensures: one more level, with its cohomology and the rank of the
    ///   induced map in each of its degrees; on a refusal the tower is
    ///   unchanged.
    /// - fails: an image of another rank, a stalk map of another width or past
    ///   its image's stalk, and a pull-back that does not commute with the
    ///   coboundaries are each refused by name.
    /// - panics: none.
    /// - intension: `image` is called once for each cell of `finer`, in cell
    ///   order.
    ///
    /// # Errors
    /// - [`SheafError::NotAComplex`]: the incidences are not those of a
    ///   complex.
    /// - [`SheafError::ImageRank`]: a cell goes onto a cell of another rank.
    /// - [`SheafError::ImageWidth`]: a stalk map holds another number of
    ///   entries than its cell's stalk.
    /// - [`SheafError::ImageEntryOutside`]: a stalk map reads past its image's
    ///   stalk.
    /// - [`SheafError::CellOutside`]: an image lies past the coarser level.
    /// - [`SheafError::NotACochainMap`]: the pull-back does not commute with
    ///   the coboundary from a degree.
    /// - [`SheafError::Overflow`]: an entry passes the integers.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — each bonding map of both towers through level 5, each
    ///   inducing an isomorphism; L3 — a loop's image with its sign reversed
    ///   breaks the square from degree zero, and an edge sent onto a point is
    ///   refused by its rank.
    /// - witness: `tests::towers::each_bonding_map_induces_an_isomorphism_on_cohomology`
    /// - witness: `tests::towers::a_bonding_map_that_breaks_a_square_is_refused`
    /// - witness: `tests::towers::an_edge_sent_onto_a_point_is_refused_by_its_rank`
    #[spec(ensures: |ref ret| ret.is_ok() || !matches!(*ret, Err(SheafError::LevelOutside(_) | SheafError::OutsideSupport(_))))]
    #[inline]
    pub fn push<Orient, Images, Map>(
        &mut self,
        finer: Sheaf<Cell>,
        orientation: Orient,
        mut image: Images,
    ) -> Result<(), SheafError>
    where
        Orient: FnMut(&Cell, &Cell) -> Incidence,
        Images: FnMut(&Cell) -> Image<Map>,
        Map: IntoIterator<Item = Entry>,
    {
        let complex = finer.cochains(orientation)?;
        let level = Level::from(self.complexes.len());
        let coarse = self
            .complexes
            .last()
            .ok_or(SheafError::LevelOutside(level))?;
        let degrees = usize::from(complex.degrees());
        let mut pulls = Vec::with_capacity(degrees);
        for degree in (0 .. degrees).map(Rank::from) {
            pulls.push(Matrix::zero(
                complex.dimension(degree),
                coarse.dimension(degree),
            )?);
        }
        for (cell, finer_cell) in finer.poset().cells().iter().enumerate() {
            let cell = Element::from(cell);
            let Image::Onto {
                cell: onto,
                incidence,
                entries,
            } = image(finer_cell)
            else {
                continue;
            };
            let rank = finer.poset().rank(cell).map_err(SheafError::Poset)?;
            let onto_rank = self.finest.poset().rank(onto).map_err(SheafError::Poset)?;
            if onto_rank != rank {
                return Err(SheafError::ImageRank { cell, image: onto });
            }
            let width = finer.width(cell)?;
            let onto_width = self.finest.width(onto)?;
            let row_start = complex.slot(cell)?;
            let column_start = coarse.slot(onto)?;
            let pull = pulls
                .get_mut(usize::from(rank))
                .ok_or(SheafError::CellOutside(cell))?;
            let sign = Rational::of_incidence(incidence);
            let mut held = 0_usize;
            for entry in entries {
                if usize::from(entry) >= usize::from(onto_width) {
                    return Err(SheafError::ImageEntryOutside { cell, entry });
                }
                if held < usize::from(width) {
                    let row = usize::from(row_start).saturating_add(held);
                    let column = usize::from(column_start).saturating_add(usize::from(entry));
                    pull.add(Slot::from(row), Slot::from(column), sign)?;
                }
                held = held.saturating_add(1);
            }
            if held != usize::from(width) {
                return Err(SheafError::ImageWidth {
                    cell,
                    width: Width::from(held),
                });
            }
        }
        for degree in (0 .. degrees).map(Rank::from) {
            let next = Rank::from(usize::from(degree).saturating_add(1));
            let pull = pull_at(&pulls, &complex, coarse, degree)?;
            let next_pull = pull_at(&pulls, &complex, coarse, next)?;
            let finer_first = complex.coboundary_or_zero(degree)?.product(&pull)?;
            let pull_first = next_pull.product(&coarse.coboundary_or_zero(degree)?)?;
            if finer_first != pull_first {
                return Err(SheafError::NotACochainMap { level, degree });
            }
        }
        let mut induced = Vec::with_capacity(degrees);
        for (degree, pull) in pulls.iter().enumerate() {
            let degree = Rank::from(degree);
            let boundaries = match usize::from(degree).checked_sub(1) {
                Some(lower) => complex.coboundary_or_zero(Rank::from(lower))?,
                None => Matrix::zero(complex.dimension(degree), Dimension::default())?,
            };
            let cocycles = match coarse.coboundary(degree) {
                Ok(coboundary) => coboundary.kernel()?,
                Err(_) => Matrix::identity(coarse.dimension(degree))?,
            };
            let pulled = pull.product(&cocycles)?;
            let spanned = boundaries.beside(&pulled)?.rank()?;
            let bounded = boundaries.rank()?;
            induced.push(Dimension::from(
                usize::from(spanned).saturating_sub(usize::from(bounded)),
            ));
        }
        let cohomology = complex.cohomology()?;
        self.finest = finer;
        self.complexes.push(complex);
        self.cohomologies.push(cohomology);
        self.induced.push(induced);
        Ok(())
    }

    /// The cohomology of a level.
    ///
    /// # Specification
    /// - provides: the cohomology computed when the level joined.
    /// - fails: a level past the tower is refused by name.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`SheafError::LevelOutside`]: `level` lies past the tower.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every level of both towers; L3 — the level past the
    ///   last is refused.
    /// - witness: `tests::towers::every_level_of_both_towers_has_the_cohomology_of_its_space`
    #[spec(ensures: |ref ret| ret.is_ok() || *ret == Err(SheafError::LevelOutside(level)))]
    #[inline]
    pub fn cohomology(
        &self,
        level: Level,
    ) -> Result<&Cohomology, SheafError>
    {
        self.cohomologies
            .get(usize::from(level))
            .ok_or(SheafError::LevelOutside(level))
    }

    /// The rank of the map that the bonding map into `level` induces on the
    /// cohomology of degree `degree`: zero past the level's highest rank.
    ///
    /// # Specification
    /// - provides: the rank computed when the level joined.
    /// - fails: the first level, which no bonding map reaches, and a level past
    ///   the tower are refused by name.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`SheafError::LevelOutside`]: `level` is the first level or lies past
    ///   the tower.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — each bonding map of both towers induces a map of full
    ///   rank in degrees zero and one; L3 — the first level is refused.
    /// - witness: `tests::towers::each_bonding_map_induces_an_isomorphism_on_cohomology`
    #[spec(ensures: |ref ret| ret.is_ok() || *ret == Err(SheafError::LevelOutside(level)))]
    #[inline]
    pub fn induced(
        &self,
        level: Level,
        degree: Rank,
    ) -> Result<Dimension, SheafError>
    {
        let ranks = usize::from(level)
            .checked_sub(1)
            .and_then(|into| self.induced.get(into))
            .ok_or(SheafError::LevelOutside(level))?;
        Ok(ranks.get(usize::from(degree)).copied().unwrap_or_default())
    }
}

/// The pull-back in degree `degree`, or the zero map from the coarser
/// level's cochains of that degree where the finer level has none.
///
/// # Specification
/// - ensures: the finer level's dimension as its rows and the coarser level's
///   as its columns.
/// - fails: a shape past the machine word is refused.
/// - panics: none.
///
/// # Errors
/// - [`SheafError::Overflow`]: the shape passes the machine word.
///
/// # Adequacy
/// - hypothesis: L2 — the top degree of each level of both towers maps through
///   the zero pull-back above it.
/// - witness: `tests::towers::each_bonding_map_induces_an_isomorphism_on_cohomology`
#[spec(ensures: |ref ret| ret.as_ref().map_or(true, |matrix| matrix.rows() == finer.dimension(degree)))]
fn pull_at(
    pulls: &[Matrix],
    finer: &CochainComplex,
    coarse: &CochainComplex,
    degree: Rank,
) -> Result<Matrix, SheafError>
{
    if let Some(pull) = pulls.get(usize::from(degree)) {
        return Ok(pull.clone());
    }
    Matrix::zero(finer.dimension(degree), coarse.dimension(degree))
}
