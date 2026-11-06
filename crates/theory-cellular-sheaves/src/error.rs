//! The typed refusals of the sheaf's constructions.

use core::fmt;

use gandr_theory_discrete_morse::Budget;
use gandr_theory_graded_posets::Rank;
use gandr_theory_stone_duality::DualityError;
use gandr_theory_stone_duality::Element;

use crate::index::Entry;
use crate::index::Level;
use crate::index::Width;

/// A malformed input to one of the sheaf's constructions, named by the cell,
/// the degree or the level it concerns.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SheafError
{
    /// A cell lies at or past the count of its poset.
    CellOutside(Element),
    /// The graded poset refused to read a cell.
    Poset(DualityError),
    /// The map from the first cell to the second, which is above it, has this
    /// width, and the stalk of the second cell has another.
    RestrictionWidth
    {
        /// The cell the map starts at.
        lower: Element,
        /// The cell the map ends at.
        upper: Element,
        /// The number of entries the map holds.
        width: Width,
    },
    /// The map from the first cell to the second reads this entry, which lies
    /// past the stalk of the first cell.
    EntryOutside
    {
        /// The cell the map starts at.
        lower: Element,
        /// The cell the map ends at.
        upper: Element,
        /// The entry past the lower stalk.
        entry: Entry,
    },
    /// At this entry of the upper stalk, the map from the lower cell to the
    /// upper cell differs from the map through the middle cell.
    NotFunctorial
    {
        /// The cell the maps start at.
        lower: Element,
        /// The cell between them.
        middle: Element,
        /// The cell the maps end at.
        upper: Element,
        /// The first entry of the upper stalk where the two maps differ.
        entry: Entry,
    },
    /// A section on this cell has this width, and the cell's stalk has
    /// another.
    SectionWidth
    {
        /// The cell of the section.
        cell: Element,
        /// The number of values the section holds.
        width: Width,
    },
    /// A glued section is read at a cell above no member of its cover.
    OutsideSupport(Element),
    /// The coboundary from this degree, followed by the coboundary from the
    /// next degree, is not zero: the orientation is not one of a complex.
    NotAComplex(Rank),
    /// No coboundary starts at this degree.
    DegreeOutside(Rank),
    /// A bonding map sends the first cell onto the second, which has another
    /// rank.
    ImageRank
    {
        /// The cell of the finer level.
        cell: Element,
        /// Its image in the coarser level.
        image: Element,
    },
    /// The stalk map of a bonding map at this cell has this width, and the
    /// cell's stalk has another.
    ImageWidth
    {
        /// The cell of the finer level.
        cell: Element,
        /// The number of entries the map holds.
        width: Width,
    },
    /// The stalk map of a bonding map at this cell reads this entry, which
    /// lies past the stalk of the cell's image.
    ImageEntryOutside
    {
        /// The cell of the finer level.
        cell: Element,
        /// The entry past the image's stalk.
        entry: Entry,
    },
    /// The pull-back of the bonding map into this level does not commute with
    /// the coboundary from this degree.
    NotACochainMap
    {
        /// The finer level of the bonding map.
        level: Level,
        /// The degree where the two composites differ.
        degree: Rank,
    },
    /// A level lies past the tower, or it is the first level, which no
    /// bonding map reaches.
    LevelOutside(Level),
    /// A matching pairs the first cell with the second, and the map from the
    /// first to the second, with the sign of the first cell's incidence, is
    /// not invertible. The first cell is no face of the second, its incidence
    /// is zero, the two stalks have other widths, or the map reads one entry
    /// twice.
    NotInvertible
    {
        /// The redundant cell of the pair.
        lower: Element,
        /// Its partner, one rank up.
        upper: Element,
    },
    /// The walk of a reduction's gradient reaches more redundant cells than
    /// this budget.
    PastBudget(Budget),
    /// Exact arithmetic over the rationals passes the integers it holds.
    Overflow,
    /// Two matrices, or a matrix and a row or a column, do not fit together:
    /// unreachable for the matrices the crate builds.
    ShapeMismatch,
}

impl fmt::Display for SheafError
{
    /// Renders the refusal and the cell, the degree or the level it names.
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
            Self::CellOutside(cell) => {
                write!(f, "cell {} outside its poset", usize::from(cell))
            },
            Self::Poset(error) => write!(f, "the poset refused: {error}"),
            Self::RestrictionWidth {
                lower,
                upper,
                width,
            } => write!(
                f,
                "the map from cell {} to cell {} has {} entries, not the width of its upper stalk",
                usize::from(lower),
                usize::from(upper),
                usize::from(width)
            ),
            Self::EntryOutside {
                lower,
                upper,
                entry,
            } => write!(
                f,
                "the map from cell {} to cell {} reads entry {} past the lower stalk",
                usize::from(lower),
                usize::from(upper),
                usize::from(entry)
            ),
            Self::NotFunctorial {
                lower,
                middle,
                upper,
                entry,
            } => write!(
                f,
                "the map from cell {} to cell {} differs from the map through cell {} at entry {}",
                usize::from(lower),
                usize::from(upper),
                usize::from(middle),
                usize::from(entry)
            ),
            Self::SectionWidth { cell, width } => write!(
                f,
                "a section on cell {} has {} values, not the width of its stalk",
                usize::from(cell),
                usize::from(width)
            ),
            Self::OutsideSupport(cell) => {
                write!(
                    f,
                    "cell {} lies above no member of the cover",
                    usize::from(cell)
                )
            },
            Self::NotAComplex(degree) => write!(
                f,
                "the two coboundaries from degree {} compose to a map that is not zero",
                usize::from(degree)
            ),
            Self::DegreeOutside(degree) => {
                write!(f, "no coboundary starts at degree {}", usize::from(degree))
            },
            Self::ImageRank { cell, image } => write!(
                f,
                "the bonding map sends cell {} onto cell {} of another rank",
                usize::from(cell),
                usize::from(image)
            ),
            Self::ImageWidth { cell, width } => write!(
                f,
                "the stalk map at cell {} has {} entries, not the width of its stalk",
                usize::from(cell),
                usize::from(width)
            ),
            Self::ImageEntryOutside { cell, entry } => write!(
                f,
                "the stalk map at cell {} reads entry {} past the stalk of its image",
                usize::from(cell),
                usize::from(entry)
            ),
            Self::NotACochainMap { level, degree } => write!(
                f,
                "the pull-back into level {} does not commute with the coboundary from degree {}",
                usize::from(level),
                usize::from(degree)
            ),
            Self::LevelOutside(level) => {
                write!(f, "level {} has no bonding map into it", usize::from(level))
            },
            Self::NotInvertible { lower, upper } => write!(
                f,
                "the matching pairs cell {} with cell {}, and the map between them is not invertible",
                usize::from(lower),
                usize::from(upper)
            ),
            Self::PastBudget(budget) => write!(
                f,
                "the walk of the gradient reaches more than {} redundant cells",
                usize::from(budget)
            ),
            Self::Overflow => f.write_str("exact arithmetic past the integers it holds"),
            Self::ShapeMismatch => f.write_str("two matrices that do not fit together"),
        }
    }
}

impl core::error::Error for SheafError
{
}
