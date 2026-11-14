//! A cellular sheaf over a finite graded poset, and the gluing of sections
//! over a cover.
//!
//! A sheaf puts a stalk of some width on each cell, and a map on each pair of
//! a cell and a cell above it. The maps compose: the map from a cell to a
//! cell above it equals the map through each cell between them.
//!
//! The maps are of one of two kinds. An entry map names, for each entry of
//! the upper stalk, the entry of the lower stalk that it reads. A sheaf of
//! entry maps holds sections of values of any kind. A linear map is a
//! homomorphism of modules over the rationals, from the lower stalk to the
//! upper stalk. A sheaf of linear maps holds sections of rationals.
//!
//! Each map of a sheaf of linear maps is a matrix or an entry map. A matrix
//! has a row for each entry of the upper stalk and a column for each entry
//! of the lower stalk. An entry map is the fast path: it reads one entry
//! where a matrix sums a row.
//!
//! A cover is a list of cells, each with a section: one value for each entry
//! of its stalk. Two members of a cover overlap at the cells above both. The
//! sections glue when, at each overlap, the two restrictions agree. The maps
//! compose, so the crate compares them only at the least cells of each
//! overlap: in a site whose overlaps have a least cell, that cell alone. A
//! glued section holds a value at each entry of each cell above a member.
//!
//! A sheaf on the opens of a space runs each map the other way, from an open
//! to each smaller open: a face of a cover restricts to the meet of two faces.
//! Such a site is this poset with its order reversed. Its cells are ordered by
//! reverse inclusion, so the meet of two faces is the least cell above both,
//! and the maps keep the values at the smaller cell's points.

use alloc::borrow::Cow;
use alloc::vec;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
use gandr_theory_graded_posets::GradedPoset;
use gandr_theory_stone_duality::DualityError;
use gandr_theory_stone_duality::Element;
use gandr_theory_stone_duality::ElementCount;
use gandr_theory_stone_duality::ElementSet;
use gandr_theory_stone_duality::Membership;
use gandr_theory_stone_duality::WIDEST;

use crate::error::SheafError;
use crate::index::CoverIndex;
use crate::index::Dimension;
use crate::index::Entry;
use crate::index::Slot;
use crate::index::Width;
use crate::matrix::Matrix;
use crate::matrix::Rational;

/// The kind of map that a sheaf holds from each cell to each cell above it:
/// [`EntryMaps`] or [`LinearMaps`].
///
/// # Specification
/// - provides: the table of a sheaf's maps, the map of one pair of cells, the
///   terms of a map, and the first entry where a map differs from the composite
///   of two others.
/// - panics: none.
/// - executable: none — a type-level block: a required-trait declaration has no
///   body.
pub trait Maps: Sized
{
    /// The maps of one sheaf, one for each pair of a cell and a cell above
    /// it.
    type Table: Clone + fmt::Debug + Eq;
    /// The map of one pair of cells, borrowed from a table.
    type Map<'table>: Copy;

    /// The map from the first of `cells` to the second in `table`, a table of
    /// `count` cells, whose upper stalk has `width` entries.
    ///
    /// # Specification
    /// - requires: the first cell lies strictly below the second, and `width`
    ///   is the width of the second cell's stalk.
    /// - provides: the map that the sheaf's constructor stored for the pair.
    /// - fails: a pair past the table is refused by its lower cell.
    /// - panics: none.
    /// - executable: none — a type-level block: a required-trait declaration
    ///   has no body.
    ///
    /// # Errors
    /// - [`SheafError::CellOutside`]: the pair lies past the table, unreachable
    ///   for a sheaf that a constructor makes.
    fn map(
        table: &Self::Table,
        count: ElementCount,
        cells: (Element, Element),
        width: Width,
    ) -> Result<Self::Map<'_>, SheafError>;

    /// Calls `each` with each nonzero term of `map`, times `scale`.
    ///
    /// # Specification
    /// - ensures: `each` takes, once for each nonzero coefficient, the entry of
    ///   the upper stalk, the entry of the lower stalk and the coefficient
    ///   times `scale`.
    /// - fails: a product past the integers, or a refusal of `each`, is
    ///   refused.
    /// - panics: none.
    /// - executable: none — a type-level block: a required-trait declaration
    ///   has no body.
    /// - intension: the entries of the upper stalk in order, and for each the
    ///   entries of the lower stalk in order.
    ///
    /// # Errors
    /// - [`SheafError::Overflow`]: a product passes the integers.
    /// - each refusal of `each`.
    fn terms<Each>(
        map: Self::Map<'_>,
        scale: Rational,
        each: Each,
    ) -> Result<(), SheafError>
    where
        Each: FnMut(Entry, Entry, Rational) -> Result<(), SheafError>;

    /// The first entry of the upper stalk of `chain` at which `direct`
    /// differs from `through` after `below`, or their agreement.
    ///
    /// # Specification
    /// - requires: `direct` is the map from the lowest cell of `chain` to its
    ///   highest, `through` the map from its middle cell to its highest, and
    ///   `below` the map from its lowest cell to its middle cell.
    /// - provides: the least entry of the highest stalk where `direct` and the
    ///   composite differ.
    /// - fails: a map read past its stalk or a product past the integers is
    ///   refused.
    /// - panics: none.
    /// - executable: none — a type-level block: a required-trait declaration
    ///   has no body.
    ///
    /// # Errors
    /// - [`SheafError::Overflow`]: a product passes the integers.
    /// - [`SheafError::EntryOutside`], [`SheafError::ShapeMismatch`]:
    ///   unreachable for maps a constructor checked.
    fn differs(
        direct: Self::Map<'_>,
        through: Self::Map<'_>,
        below: Self::Map<'_>,
        chain: Chain,
    ) -> Result<Difference, SheafError>;
}

/// A kind of map through which a section of `Value`s restricts.
///
/// # Specification
/// - provides: the value at one entry of the upper stalk that a map gives a
///   section of its lower stalk.
/// - panics: none.
/// - executable: none — a type-level block: a required-trait declaration has no
///   body.
pub trait Restricts<Value>: Maps
{
    /// The value at `entry` of the upper stalk that `map`, the map between
    /// `cells`, gives `section`.
    ///
    /// # Specification
    /// - requires: `section` has one value for each entry of the lower stalk.
    /// - provides: the value that the entry reads, or the sum that the entry's
    ///   row gives.
    /// - fails: an entry or a read past the map, or a sum past the integers, is
    ///   refused.
    /// - panics: none.
    /// - executable: none — a type-level block: a required-trait declaration
    ///   has no body.
    ///
    /// # Errors
    /// - [`SheafError::EntryOutside`]: `entry` or its read lies past the map.
    /// - [`SheafError::Overflow`]: a sum passes the integers.
    fn restricted<'section>(
        map: Self::Map<'_>,
        cells: (Element, Element),
        section: &'section [Value],
        entry: Entry,
    ) -> Result<Restricted<'section, Value>, SheafError>;
}

/// The kind of a sheaf whose maps are entry maps: its sections hold values of
/// any kind.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum EntryMaps {}

/// The kind of a sheaf whose maps are homomorphisms of modules over the
/// rationals, each a matrix or an entry map: its sections hold rationals.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum LinearMaps {}

/// The map that a sheaf of linear maps holds from a cell to a cell above it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Restriction<Map>
{
    /// An entry map: for each entry of the upper stalk, the entry of the lower
    /// stalk that it reads.
    Entries(Map),
    /// A matrix with a row for each entry of the upper stalk and a column for
    /// each entry of the lower stalk.
    Matrix(Matrix),
}

/// The entry maps of a sheaf: for each pair of cells, where its map starts in
/// one list of entries.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EntryTable
{
    /// For each pair of cells, the lower first, the start of the map from the
    /// lower to the upper in `entries`. Only a pair whose lower cell lies
    /// strictly below its upper cell is read.
    starts: Vec<usize>,
    /// The entry maps, one after the other.
    entries: Vec<Entry>,
}

/// The linear maps of a sheaf: for each pair of cells, its entry map or its
/// matrix.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LinearTable
{
    /// For each pair of cells, the lower first, where its map lies. Only a
    /// pair whose lower cell lies strictly below its upper cell is read.
    places: Vec<Place>,
    /// The entry maps, one after the other.
    entries: Vec<Entry>,
    /// The matrices.
    matrices: Vec<Matrix>,
}

/// Where the map of one pair of cells lies in a table of linear maps.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Place
{
    /// An entry map, which starts at this place in the entries.
    Entries(usize),
    /// A matrix, at this place in the matrices.
    Matrix(usize),
}

/// A linear map of one pair of cells, borrowed from its table.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum LinearMap<'table>
{
    /// An entry map: for each entry of the upper stalk, the entry of the lower
    /// stalk that it reads.
    Entries(&'table [Entry]),
    /// A matrix with a row for each entry of the upper stalk and a column for
    /// each entry of the lower stalk.
    Matrix(&'table Matrix),
}

/// Three cells, each strictly below the next, and the widths of their stalks.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Chain
{
    /// The lowest cell.
    pub lower: Element,
    /// The middle cell.
    pub middle: Element,
    /// The highest cell.
    pub upper: Element,
    /// The widths of the lowest, the middle and the highest cell's stalks.
    pub widths: (Width, Width, Width),
}

/// The value at one entry of a restriction: read from the section, or summed
/// from it by a row of a matrix.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Restricted<'section, Value>
{
    /// The value of the section that an entry map reads.
    Read(&'section Value),
    /// The sum that a row of a matrix gives.
    Summed(Value),
}

impl<Value> Restricted<'_, Value>
{
    /// The value.
    ///
    /// # Specification
    /// trivial.
    const fn value(&self) -> &Value
    {
        match *self {
            Self::Read(value) | Self::Summed(ref value) => value,
        }
    }

    /// The value, copied out of the section where it was read.
    ///
    /// # Specification
    /// trivial.
    const fn owned(self) -> Value
    where
        Value: Copy,
    {
        match self {
            Self::Read(&value) | Self::Summed(value) => value,
        }
    }
}

/// A pair of a cell and a cell strictly above it, as a constructor meets it.
struct Above<'poset, Cell>
{
    /// The lower cell.
    lower: Element,
    /// The upper cell.
    upper: Element,
    /// The data of the lower cell.
    lower_cell: &'poset Cell,
    /// The data of the upper cell.
    upper_cell: &'poset Cell,
    /// The width of the lower cell's stalk.
    lower_width: Width,
    /// The width of the upper cell's stalk.
    upper_width: Width,
}

impl Maps for EntryMaps
{
    type Map<'table> = &'table [Entry];
    type Table = EntryTable;

    /// The entry map of the pair: one entry for each entry of the upper stalk.
    ///
    /// # Specification
    /// - provides: the entries that `Sheaf::new` stored for the pair.
    /// - fails: a pair past the table is refused by its lower cell.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`SheafError::CellOutside`]: the pair lies past the table.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every gluing and every coboundary of every face cover
    ///   and of both towers reads its maps through it, so a map read at the
    ///   wrong pair changes a verdict.
    /// - witness: `tests::sheaf::a_cover_glues_where_its_sections_agree_on_the_overlap`
    /// - witness: `tests::towers::every_level_of_both_towers_has_the_cohomology_of_its_space`
    #[spec(ensures: |ref ret| ret.as_ref().map_or_else(|error| *error == SheafError::CellOutside(cells.0), |map| map.len() == usize::from(width)))]
    #[inline]
    fn map(
        table: &EntryTable,
        count: ElementCount,
        (lower, upper): (Element, Element),
        width: Width,
    ) -> Result<&[Entry], SheafError>
    {
        let outside = SheafError::CellOutside(lower);
        let start = table
            .starts
            .get(usize::from(pair(count, lower, upper)))
            .copied()
            .ok_or(outside)?;
        let end = start.checked_add(usize::from(width)).ok_or(outside)?;
        table.entries.get(start .. end).ok_or(outside)
    }

    /// Calls `each` once for each entry of the upper stalk, with the entry it
    /// reads and `scale`.
    ///
    /// # Specification
    /// - ensures: `each` takes each entry, its read and `scale`, in order.
    /// - fails: a refusal of `each` is refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - each refusal of `each`.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every coboundary of both towers is written through
    ///   it, so a lost or a misplaced term breaks a cohomology.
    /// - witness: `tests::towers::every_level_of_both_towers_has_the_cohomology_of_its_space`
    #[spec(ensures: |ref ret| ret.is_ok() || ret.is_err())]
    #[inline]
    fn terms<Each>(
        map: &[Entry],
        scale: Rational,
        mut each: Each,
    ) -> Result<(), SheafError>
    where
        Each: FnMut(Entry, Entry, Rational) -> Result<(), SheafError>,
    {
        for (row, &column) in map.iter().enumerate() {
            each(Entry::from(row), column, scale)?;
        }
        Ok(())
    }

    /// The first entry at which the direct map reads another entry than the
    /// map through the middle cell.
    ///
    /// # Specification
    /// - provides: the least entry where the two reads differ.
    /// - fails: a read past the middle stalk is refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`SheafError::EntryOutside`]: unreachable for maps `Sheaf::new`
    ///   checked.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a chain of three cells whose direct map swaps the two
    ///   entries its composite keeps separates the refusal.
    /// - witness: `tests::sheaf::a_map_that_does_not_compose_is_refused`
    #[spec(ensures: |ref ret| ret.is_ok() || matches!(*ret, Err(SheafError::EntryOutside { .. })))]
    #[inline]
    fn differs(
        direct: &[Entry],
        through: &[Entry],
        below: &[Entry],
        chain: Chain,
    ) -> Result<Difference, SheafError>
    {
        entries_differ(direct, through, below, chain)
    }
}

impl<Value> Restricts<Value> for EntryMaps
{
    /// The value of `section` at the entry that the map reads at `entry`.
    ///
    /// # Specification
    /// - provides: a borrow of the value read.
    /// - fails: an entry past the map, or a read past the section, is refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`SheafError::EntryOutside`]: `entry` lies past the map, or its read
    ///   past the section.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every choice of values zero and one on every small
    ///   face cover, against the union square's first point of difference.
    /// - witness: `tests::sheaf::a_cover_glues_where_its_sections_agree_on_the_overlap`
    #[spec(ensures: |ref ret| ret.is_ok() || matches!(*ret, Err(SheafError::EntryOutside { .. })))]
    #[inline]
    fn restricted<'section>(
        map: &[Entry],
        (lower, upper): (Element, Element),
        section: &'section [Value],
        entry: Entry,
    ) -> Result<Restricted<'section, Value>, SheafError>
    {
        let outside = SheafError::EntryOutside {
            lower,
            upper,
            entry,
        };
        let read = map.get(usize::from(entry)).copied().ok_or(outside)?;
        section
            .get(usize::from(read))
            .map(Restricted::Read)
            .ok_or(outside)
    }
}

impl Maps for LinearMaps
{
    type Map<'table> = LinearMap<'table>;
    type Table = LinearTable;

    /// The entry map or the matrix of the pair.
    ///
    /// # Specification
    /// - provides: the map that `Sheaf::linear` stored for the pair.
    /// - fails: a pair past the table is refused by its lower cell.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`SheafError::CellOutside`]: the pair lies past the table.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the projective line's two charts read their matrices
    ///   into the overlap, and the cohomology reads them back.
    /// - witness: `tests::linear::the_projective_line_s_twist_by_minus_two_has_one_class_in_degree_one`
    #[spec(ensures: |ref ret| ret.is_ok() || *ret == Err(SheafError::CellOutside(cells.0)))]
    #[inline]
    fn map(
        table: &LinearTable,
        count: ElementCount,
        (lower, upper): (Element, Element),
        width: Width,
    ) -> Result<LinearMap<'_>, SheafError>
    {
        let outside = SheafError::CellOutside(lower);
        let place = table
            .places
            .get(usize::from(pair(count, lower, upper)))
            .copied()
            .ok_or(outside)?;
        match place {
            Place::Entries(start) => {
                let end = start.checked_add(usize::from(width)).ok_or(outside)?;
                table
                    .entries
                    .get(start .. end)
                    .map(LinearMap::Entries)
                    .ok_or(outside)
            },
            Place::Matrix(index) => table
                .matrices
                .get(index)
                .map(LinearMap::Matrix)
                .ok_or(outside),
        }
    }

    /// Calls `each` with each read of an entry map, or with each nonzero
    /// entry of a matrix, times `scale`.
    ///
    /// # Specification
    /// - ensures: `each` takes, for an entry map, each entry, its read and
    ///   `scale`; for a matrix, each row, column and nonzero entry times
    ///   `scale`.
    /// - fails: a product past the integers, or a refusal of `each`, is
    ///   refused.
    /// - panics: none.
    /// - intension: the rows in order, and in each row the columns in order.
    ///
    /// # Errors
    /// - [`SheafError::Overflow`]: a product passes the integers.
    /// - each refusal of `each`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the projective line's coboundary holds each chart's
    ///   matrix with the sign of its incidence, entry by entry.
    /// - witness: `tests::linear::the_projective_line_s_twist_by_minus_two_has_one_class_in_degree_one`
    #[spec(ensures: |ref ret| ret.is_ok() || ret.is_err())]
    #[inline]
    fn terms<Each>(
        map: LinearMap<'_>,
        scale: Rational,
        mut each: Each,
    ) -> Result<(), SheafError>
    where
        Each: FnMut(Entry, Entry, Rational) -> Result<(), SheafError>,
    {
        match map {
            LinearMap::Entries(entries) => EntryMaps::terms(entries, scale, each),
            LinearMap::Matrix(matrix) => {
                for row in 0 .. usize::from(matrix.rows()) {
                    for column in 0 .. usize::from(matrix.columns()) {
                        let coefficient = matrix.at(Slot::from(row), Slot::from(column))?;
                        if coefficient == Rational::ZERO {
                            continue;
                        }
                        let term = scale.times(coefficient)?;
                        each(Entry::from(row), Entry::from(column), term)?;
                    }
                }
                Ok(())
            },
        }
    }

    /// The first entry of the highest stalk at which the direct map differs
    /// from the composite: entry by entry for three entry maps, and row by row
    /// as matrices otherwise.
    ///
    /// # Specification
    /// - provides: the least row where the direct map and the composite differ.
    /// - fails: a product past the integers is refused.
    /// - panics: none.
    /// - intension: three entry maps compare as entry maps, with no matrix
    ///   built. Any other three build each entry map as a matrix, then the one
    ///   product.
    ///
    /// # Errors
    /// - [`SheafError::Overflow`]: a product passes the integers.
    /// - [`SheafError::EntryOutside`], [`SheafError::ShapeMismatch`]:
    ///   unreachable for maps `Sheaf::linear` checked.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a chain of three cells whose direct matrix doubles
    ///   one entry of the composite separates the refusal, at that entry.
    /// - witness: `tests::linear::matrices_that_do_not_compose_are_refused`
    #[spec(ensures: |ref ret| ret.is_ok() || matches!(*ret, Err(SheafError::Overflow | SheafError::EntryOutside { .. } | SheafError::ShapeMismatch)))]
    #[inline]
    fn differs(
        direct: LinearMap<'_>,
        through: LinearMap<'_>,
        below: LinearMap<'_>,
        chain: Chain,
    ) -> Result<Difference, SheafError>
    {
        if let (
            LinearMap::Entries(direct),
            LinearMap::Entries(through),
            LinearMap::Entries(below),
        ) = (direct, through, below)
        {
            return entries_differ(direct, through, below, chain);
        }
        let (lower, middle, upper) = chain.widths;
        let direct = dense(direct, upper, lower)?;
        let through = dense(through, upper, middle)?;
        let below = dense(below, middle, lower)?;
        let composite = through.product(&below)?;
        for row in 0 .. usize::from(upper) {
            for column in 0 .. usize::from(lower) {
                let at = (Slot::from(row), Slot::from(column));
                if direct.at(at.0, at.1)? != composite.at(at.0, at.1)? {
                    return Ok(Difference::At(Entry::from(row)));
                }
            }
        }
        Ok(Difference::Agree)
    }
}

impl Restricts<Rational> for LinearMaps
{
    /// The rational at `entry` that the map gives `section`: the read of an
    /// entry map, or the sum of the entry's row of a matrix against the
    /// section.
    ///
    /// # Specification
    /// - provides: the read value, or the summed value.
    /// - fails: an entry past the map, a read past the section, or a sum past
    ///   the integers, is refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`SheafError::EntryOutside`]: `entry` lies past the map, or its read
    ///   past the section.
    /// - [`SheafError::Overflow`]: a sum passes the integers.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two sections on the projective line's charts glue
    ///   through a twist by one half exactly when the halved values agree.
    /// - witness: `tests::linear::a_section_glues_through_a_matrix_where_its_scaled_values_agree`
    #[spec(ensures: |ref ret| ret.is_ok() || matches!(*ret, Err(SheafError::EntryOutside { .. } | SheafError::Overflow)))]
    #[inline]
    fn restricted<'section>(
        map: LinearMap<'_>,
        cells: (Element, Element),
        section: &'section [Rational],
        entry: Entry,
    ) -> Result<Restricted<'section, Rational>, SheafError>
    {
        match map {
            LinearMap::Entries(entries) => EntryMaps::restricted(entries, cells, section, entry),
            LinearMap::Matrix(matrix) => {
                if usize::from(entry) >= usize::from(matrix.rows()) {
                    return Err(SheafError::EntryOutside {
                        lower: cells.0,
                        upper: cells.1,
                        entry,
                    });
                }
                let mut sum = Rational::ZERO;
                for (column, &value) in section.iter().enumerate() {
                    let coefficient =
                        matrix.at(Slot::from(usize::from(entry)), Slot::from(column))?;
                    if coefficient == Rational::ZERO {
                        continue;
                    }
                    let term = coefficient.times(value)?;
                    sum = sum.plus(term)?;
                }
                Ok(Restricted::Summed(sum))
            },
        }
    }
}

/// A cellular sheaf over a graded poset of at most 64 cells: a stalk width
/// for each cell and a map of the kind `Kind` for each pair of a cell and a
/// cell above it.
///
/// # Specification
/// - ensures: one width and one star for each cell; the map from a cell to a
///   cell above it reads the cell's stalk into the stalk above; the maps
///   compose.
/// - provides: the poset, the widths, the gluing of a cover and the cochains.
/// - panics: none.
/// - executable: none — a type-level block: the invariant is [`Sheaf::new`]'s
///   and [`Sheaf::linear`]'s, which make it.
///
/// # Adequacy
/// - hypothesis: L2 — the face covers of every corpus shape and of every small
///   carrier glue as the union square decides; L3 — a map past its stalk, a map
///   of the wrong width and a map that does not compose are each refused by
///   name; L3 — the projective line's twist by minus two has one class in
///   degree one.
/// - witness: `tests::sheaf::a_map_that_does_not_compose_is_refused`
/// - witness: `tests::sheaf::a_map_past_its_stalk_is_refused`
/// - witness: `tests::linear::the_projective_line_s_twist_by_minus_two_has_one_class_in_degree_one`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Sheaf<Cell, Kind = EntryMaps>
where
    Kind: Maps,
{
    /// The cells and their order.
    poset: GradedPoset<Cell>,
    /// The width of each cell's stalk, in cell order.
    widths: Vec<Width>,
    /// The map of each pair of a cell and a cell strictly above it.
    maps: Kind::Table,
    /// Each cell's star: the cell and every cell above it.
    stars: Vec<ElementSet>,
}

impl<Cell> Sheaf<Cell, EntryMaps>
{
    /// The sheaf of entry maps on `poset` whose stalk at each cell has the
    /// width `width` gives, and whose map from each cell to each cell above it
    /// is the one `restriction` gives.
    ///
    /// # Specification
    /// - ensures: each map holds one entry for each entry of its upper stalk,
    ///   each inside its lower stalk, and the maps compose.
    /// - fails: a poset of more than 64 cells is refused by its count, since
    ///   each set of cells is one bit row; a map of another width, a map that
    ///   reads past its lower stalk, and a map that differs from the map
    ///   through a cell between are each refused by the cells they name.
    /// - panics: none.
    /// - intension: `width` is called once for each cell in cell order.
    ///   `restriction` is called once for each pair of a cell and a cell
    ///   strictly above it: for each upper cell in cell order, each lower cell
    ///   in cell order. The composition check reads each chain of three cells
    ///   once.
    ///
    /// # Errors
    /// - [`SheafError::RestrictionWidth`]: a map holds another number of
    ///   entries than its upper stalk.
    /// - [`SheafError::EntryOutside`]: a map reads an entry past its lower
    ///   stalk.
    /// - [`SheafError::NotFunctorial`]: a map differs from the map through a
    ///   cell between its two cells.
    /// - [`SheafError::Poset`]: the poset has more than 64 cells.
    /// - [`SheafError::CellOutside`]: unreachable for a poset that
    ///   [`GradedPoset::new`] makes.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the face covers of every corpus shape and of every
    ///   small carrier, each with its maps to the meets; L3 — a map past its
    ///   stalk, a map one entry short and a chain of three cells whose maps do
    ///   not compose separate the three refusals; L3 — a tower's level of 127
    ///   and of 128 cells separates the count refusal.
    /// - witness: `tests::sheaf::a_map_that_does_not_compose_is_refused`
    /// - witness: `tests::sheaf::a_map_past_its_stalk_is_refused`
    /// - witness: `tests::sheaf::a_map_of_another_width_is_refused`
    /// - witness: `tests::towers::the_level_past_the_cell_budget_is_refused_by_its_count`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |sheaf| sheaf.widths.len() == sheaf.poset.cells().len()
        && sheaf.stars.len() == sheaf.poset.cells().len()))]
    #[inline]
    pub fn new<Widths, Restrict, Map>(
        poset: GradedPoset<Cell>,
        width: Widths,
        mut restriction: Restrict,
    ) -> Result<Self, SheafError>
    where
        Widths: FnMut(&Cell) -> Width,
        Restrict: FnMut(&Cell, &Cell) -> Map,
        Map: IntoIterator<Item = Entry>,
    {
        let count = counted(&poset)?;
        let mut starts = vec![0_usize; usize::from(count).saturating_mul(usize::from(count))];
        let mut entries = Vec::new();
        let (widths, stars) = framed(&poset, width, |above| {
            let start = held(
                &mut entries,
                restriction(above.lower_cell, above.upper_cell),
                &above,
            )?;
            let slot = starts
                .get_mut(usize::from(pair(count, above.lower, above.upper)))
                .ok_or(SheafError::CellOutside(above.lower))?;
            *slot = start;
            Ok(())
        })?;
        let sheaf = Self {
            poset,
            widths,
            maps: EntryTable { starts, entries },
            stars,
        };
        sheaf.composes()?;
        Ok(sheaf)
    }

    /// The entry of `lower`'s stalk that the map from `lower` to `upper`
    /// reads at `entry`: `entry` itself when the two cells are one.
    ///
    /// # Specification
    /// - requires: `lower` is `upper` or lies below it, and `entry` lies in
    ///   `upper`'s stalk.
    /// - ensures: the entry lies in `lower`'s stalk.
    /// - fails: a pair or an entry outside the maps is refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`SheafError::EntryOutside`]: `entry` lies past the map, or the pair
    ///   is past the poset.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every reduction of both towers reads its maps through
    ///   it, so a map read at the wrong pair changes a cohomology.
    /// - witness: `tests::towers::every_level_of_both_towers_keeps_its_cohomology_on_its_reduct`
    #[spec(ensures: |ref ret| ret.is_ok() || matches!(*ret, Err(SheafError::EntryOutside { .. })))]
    pub(crate) fn read(
        &self,
        lower: Element,
        upper: Element,
        entry: Entry,
    ) -> Result<Entry, SheafError>
    {
        if lower == upper {
            return Ok(entry);
        }
        let outside = SheafError::EntryOutside {
            lower,
            upper,
            entry,
        };
        let map = self.map(lower, upper).map_err(|_| outside)?;
        map.get(usize::from(entry)).copied().ok_or(outside)
    }
}

impl<Cell> Sheaf<Cell, LinearMaps>
{
    /// The sheaf of linear maps on `poset` whose stalk at each cell has the
    /// width `width` gives, and whose map from each cell to each cell above it
    /// is the entry map or the matrix that `restriction` gives.
    ///
    /// # Specification
    /// - ensures: each entry map holds one entry for each entry of its upper
    ///   stalk, each inside its lower stalk; each matrix has a row for each
    ///   entry of its upper stalk and a column for each entry of its lower
    ///   stalk; the maps compose.
    /// - fails: a poset of more than 64 cells is refused by its count; an entry
    ///   map of another width or past its lower stalk, a matrix of other rows
    ///   or other columns, and a map that differs from the composite through a
    ///   cell between are each refused by the cells they name.
    /// - panics: none.
    /// - intension: `width` is called once for each cell in cell order.
    ///   `restriction` is called once for each pair of a cell and a cell
    ///   strictly above it: for each upper cell in cell order, each lower cell
    ///   in cell order. The composition check reads each chain of three cells
    ///   once.
    ///
    /// # Errors
    /// - [`SheafError::RestrictionWidth`]: an entry map holds another number of
    ///   entries, or a matrix another number of rows, than its upper stalk.
    /// - [`SheafError::RestrictionColumns`]: a matrix has another number of
    ///   columns than its lower stalk.
    /// - [`SheafError::EntryOutside`]: an entry map reads an entry past its
    ///   lower stalk.
    /// - [`SheafError::NotFunctorial`]: a map differs from the composite
    ///   through a cell between its two cells.
    /// - [`SheafError::Overflow`]: a composite passes the integers.
    /// - [`SheafError::Poset`]: the poset has more than 64 cells.
    /// - [`SheafError::CellOutside`]: unreachable for a poset that
    ///   [`GradedPoset::new`] makes.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the projective line's two charts restrict into their
    ///   overlap by matrices that read nothing at one entry, and the sheaf is
    ///   admitted; a matrix of other rows and a matrix of other columns are
    ///   each refused by its pair; a chain of three cells whose matrices do not
    ///   compose is refused at the entry where they differ.
    /// - witness: `tests::linear::the_projective_line_s_twist_by_minus_two_has_one_class_in_degree_one`
    /// - witness: `tests::linear::a_matrix_of_another_shape_is_refused`
    /// - witness: `tests::linear::matrices_that_do_not_compose_are_refused`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |sheaf| sheaf.widths.len() == sheaf.poset.cells().len()
        && sheaf.stars.len() == sheaf.poset.cells().len()))]
    #[inline]
    pub fn linear<Widths, Restrict, Map>(
        poset: GradedPoset<Cell>,
        width: Widths,
        mut restriction: Restrict,
    ) -> Result<Self, SheafError>
    where
        Widths: FnMut(&Cell) -> Width,
        Restrict: FnMut(&Cell, &Cell) -> Restriction<Map>,
        Map: IntoIterator<Item = Entry>,
    {
        let count = counted(&poset)?;
        let mut places =
            vec![Place::Entries(0); usize::from(count).saturating_mul(usize::from(count))];
        let mut entries = Vec::new();
        let mut matrices = Vec::new();
        let (widths, stars) = framed(&poset, width, |above| {
            let place = match restriction(above.lower_cell, above.upper_cell) {
                Restriction::Entries(map) => Place::Entries(held(&mut entries, map, &above)?),
                Restriction::Matrix(matrix) => {
                    if usize::from(matrix.rows()) != usize::from(above.upper_width) {
                        return Err(SheafError::RestrictionWidth {
                            lower: above.lower,
                            upper: above.upper,
                            width: Width::from(usize::from(matrix.rows())),
                        });
                    }
                    if usize::from(matrix.columns()) != usize::from(above.lower_width) {
                        return Err(SheafError::RestrictionColumns {
                            lower: above.lower,
                            upper: above.upper,
                            columns: matrix.columns(),
                        });
                    }
                    matrices.push(matrix);
                    Place::Matrix(matrices.len().saturating_sub(1))
                },
            };
            let slot = places
                .get_mut(usize::from(pair(count, above.lower, above.upper)))
                .ok_or(SheafError::CellOutside(above.lower))?;
            *slot = place;
            Ok(())
        })?;
        let sheaf = Self {
            poset,
            widths,
            maps: LinearTable {
                places,
                entries,
                matrices,
            },
            stars,
        };
        sheaf.composes()?;
        Ok(sheaf)
    }
}

impl<Cell, Kind> Sheaf<Cell, Kind>
where
    Kind: Maps,
{
    /// Checks that each map equals the composite through each cell between
    /// its two cells.
    ///
    /// # Specification
    /// - ensures: for each chain of three cells, the map from the lowest to the
    ///   highest equals the map through the middle after the map into it.
    /// - fails: the first chain and entry where they differ is refused.
    /// - panics: none.
    /// - intension: the chains in order of their highest cell, then their
    ///   middle cell, then their lowest cell, each in cell order.
    ///
    /// # Errors
    /// - [`SheafError::NotFunctorial`]: two maps differ at an entry.
    /// - [`SheafError::Overflow`]: a composite of matrices passes the integers.
    /// - [`SheafError::CellOutside`], [`SheafError::EntryOutside`],
    ///   [`SheafError::ShapeMismatch`]: unreachable, as the cells come from the
    ///   poset and the maps were checked.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a chain of three cells whose direct map swaps the two
    ///   entries its composite keeps separates the refusal for entry maps, and
    ///   a direct matrix that doubles one entry of the composite separates it
    ///   for matrices.
    /// - witness: `tests::sheaf::a_map_that_does_not_compose_is_refused`
    /// - witness: `tests::linear::matrices_that_do_not_compose_are_refused`
    #[spec(ensures: |ref ret| ret.is_ok() || matches!(*ret, Err(SheafError::NotFunctorial { .. } | SheafError::Overflow | SheafError::CellOutside(_) | SheafError::EntryOutside { .. } | SheafError::ShapeMismatch)))]
    fn composes(&self) -> Result<(), SheafError>
    {
        for upper in (0 .. self.widths.len()).map(Element::from) {
            let upper_width = self.width(upper)?;
            let below_upper = self.poset.boundary(upper).map_err(SheafError::Poset)?;
            for middle in below_upper.elements() {
                let middle_width = self.width(middle)?;
                let through = self.map(middle, upper)?;
                let below_middle = self.poset.boundary(middle).map_err(SheafError::Poset)?;
                for lower in below_middle.elements() {
                    let chain = Chain {
                        lower,
                        middle,
                        upper,
                        widths: (self.width(lower)?, middle_width, upper_width),
                    };
                    let direct = self.map(lower, upper)?;
                    let below = self.map(lower, middle)?;
                    if let Difference::At(entry) = Kind::differs(direct, through, below, chain)? {
                        return Err(SheafError::NotFunctorial {
                            lower,
                            middle,
                            upper,
                            entry,
                        });
                    }
                }
            }
        }
        Ok(())
    }

    /// The cells and their order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn poset(&self) -> &GradedPoset<Cell>
    {
        &self.poset
    }

    /// The width of a cell's stalk.
    ///
    /// # Specification
    /// - provides: the width the constructor read for `cell`.
    /// - fails: a cell at or past the count is refused by name.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`SheafError::CellOutside`]: `cell` is at or past the count.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the face cover of the config shape gives each face
    ///   and its meet the width of its points, and a cell past the count is
    ///   refused.
    /// - witness: `tests::sheaf::a_cover_glues_where_its_sections_agree_on_the_overlap`
    #[spec(ensures: |ref ret| ret.is_ok() || *ret == Err(SheafError::CellOutside(cell)))]
    #[inline]
    pub fn width(
        &self,
        cell: Element,
    ) -> Result<Width, SheafError>
    {
        self.widths
            .get(usize::from(cell))
            .copied()
            .ok_or(SheafError::CellOutside(cell))
    }

    /// The map from `lower` to `upper`.
    ///
    /// # Specification
    /// - requires: `lower` lies strictly below `upper`.
    /// - provides: the map that the constructor stored for the pair.
    /// - fails: a cell past the poset is refused by name.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`SheafError::CellOutside`]: a cell lies past the poset.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every coboundary of both towers and of the projective
    ///   line reads its maps through it, so a map read at the wrong pair
    ///   changes a cohomology.
    /// - witness: `tests::towers::every_level_of_both_towers_has_the_cohomology_of_its_space`
    /// - witness: `tests::linear::the_projective_line_s_twist_by_minus_two_has_one_class_in_degree_one`
    #[spec(ensures: |ref ret| ret.is_ok() || matches!(*ret, Err(SheafError::CellOutside(_))))]
    pub(crate) fn map(
        &self,
        lower: Element,
        upper: Element,
    ) -> Result<Kind::Map<'_>, SheafError>
    {
        let width = self.width(upper)?;
        Kind::map(
            &self.maps,
            ElementCount::from(self.widths.len()),
            (lower, upper),
            width,
        )
    }

    /// The value at `entry` of `upper`'s stalk that `section`, a section on
    /// `lower`, restricts to: its own value when the two cells are one.
    ///
    /// # Specification
    /// - requires: `lower` is `upper` or lies below it, and `section` has the
    ///   width of `lower`'s stalk.
    /// - provides: the value read, or the value summed.
    /// - fails: an entry outside the map or the section, or a sum past the
    ///   integers, is refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`SheafError::EntryOutside`]: `entry` or its read lies outside.
    /// - [`SheafError::CellOutside`]: a cell lies past the poset.
    /// - [`SheafError::Overflow`]: a sum passes the integers.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every comparison and every glued section of every
    ///   face cover reads through it; L3 — a section on a chart of the
    ///   projective line restricts through its matrix.
    /// - witness: `tests::sheaf::a_cover_glues_where_its_sections_agree_on_the_overlap`
    /// - witness: `tests::linear::a_section_glues_through_a_matrix_where_its_scaled_values_agree`
    #[spec(ensures: |ref ret| ret.is_ok() || matches!(*ret, Err(SheafError::EntryOutside { .. } | SheafError::CellOutside(_) | SheafError::Overflow)))]
    fn value_at<'section, Value>(
        &self,
        (lower, upper): (Element, Element),
        section: &'section [Value],
        entry: Entry,
    ) -> Result<Restricted<'section, Value>, SheafError>
    where
        Kind: Restricts<Value>,
    {
        if lower == upper {
            return section.get(usize::from(entry)).map(Restricted::Read).ok_or(
                SheafError::EntryOutside {
                    lower,
                    upper,
                    entry,
                },
            );
        }
        let map = self.map(lower, upper)?;
        Kind::restricted(map, (lower, upper), section, entry)
    }

    /// A cell's star: the cell and every cell above it.
    ///
    /// # Specification
    /// - provides: the star the constructor computed for `cell`.
    /// - fails: a cell at or past the count is refused by name.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`SheafError::CellOutside`]: `cell` is at or past the count.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every overlap of every face cover is the meet of two
    ///   stars, so a lost cell drops a comparison.
    /// - witness: `tests::sheaf::a_cover_glues_where_its_sections_agree_on_the_overlap`
    #[spec(ensures: |ref ret| ret.map_or(true, |star| star.contains(cell) == Membership::Inside))]
    fn star(
        &self,
        cell: Element,
    ) -> Result<ElementSet, SheafError>
    {
        self.stars
            .get(usize::from(cell))
            .copied()
            .ok_or(SheafError::CellOutside(cell))
    }

    /// The least cells of a set of cells: those with no other member of the
    /// set below them.
    ///
    /// # Specification
    /// - ensures: each returned cell lies in `set`, and no other member of
    ///   `set` lies below it.
    /// - fails: a member past the poset is refused by name.
    /// - panics: none.
    /// - intension: in cell order.
    ///
    /// # Errors
    /// - [`SheafError::CellOutside`]: a member lies past the poset.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two edges between the same two points overlap at no
    ///   least cell, and each point is a least cell of the overlap; L2 — every
    ///   face cover overlaps at its meet alone.
    /// - witness: `tests::sheaf::an_overlap_with_two_least_cells_compares_at_each`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |least| least.iter().all(|&cell| set.contains(cell) == Membership::Inside)))]
    fn least(
        &self,
        set: ElementSet,
    ) -> Result<Vec<Element>, SheafError>
    {
        let mut least = Vec::new();
        for cell in set.elements() {
            let closure = self.poset.closure(cell).map_err(SheafError::Poset)?;
            let own = ElementSet::single(cell).map_err(SheafError::Poset)?;
            if closure.meet(set) == own {
                least.push(cell);
            }
        }
        Ok(least)
    }

    /// The first entry of `overlap`'s stalk at which the restrictions of two
    /// sections differ, or their agreement.
    ///
    /// # Specification
    /// - requires: `overlap` lies above both cells, and each section has the
    ///   width of its cell's stalk.
    /// - provides: the least entry where the two restrictions differ.
    /// - fails: a map read outside its stalk, a section too short or a sum past
    ///   the integers is refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`SheafError::Overflow`]: a sum of a matrix's row passes the integers.
    /// - [`SheafError::EntryOutside`], [`SheafError::CellOutside`]: unreachable
    ///   for a sheaf a constructor makes and a section `Sheaf::glue` checked.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every choice of values zero and one on every small
    ///   face cover, against the union square's first point of difference; L3 —
    ///   the projective line's charts differ through a twist by one half at the
    ///   first entry where the halved values differ.
    /// - witness: `tests::sheaf::a_cover_glues_where_its_sections_agree_on_the_overlap`
    /// - witness: `tests::linear::a_section_glues_through_a_matrix_where_its_scaled_values_agree`
    #[spec(ensures: |ref ret| ret.is_ok() || matches!(*ret, Err(SheafError::EntryOutside { .. } | SheafError::CellOutside(_) | SheafError::Overflow)))]
    fn difference<Value>(
        &self,
        (left_cell, left): (Element, &[Value]),
        (right_cell, right): (Element, &[Value]),
        overlap: Element,
    ) -> Result<Difference, SheafError>
    where
        Kind: Restricts<Value>,
        Value: Eq,
    {
        let width = self.width(overlap)?;
        for entry in (0 .. usize::from(width)).map(Entry::from) {
            let from_left = self.value_at((left_cell, overlap), left, entry)?;
            let from_right = self.value_at((right_cell, overlap), right, entry)?;
            if from_left.value() != from_right.value() {
                return Ok(Difference::At(entry));
            }
        }
        Ok(Difference::Agree)
    }

    /// Checks that a section has one value for each entry of its cell's
    /// stalk.
    ///
    /// # Specification
    /// - ensures: the section's width is its cell's stalk width.
    /// - fails: a cell past the poset, or a section of another width, is
    ///   refused by its cell.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`SheafError::CellOutside`]: the cell lies past the poset.
    /// - [`SheafError::SectionWidth`]: the section has another number of values
    ///   than the cell's stalk.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a section one value short is refused through both the
    ///   gluing and the pair comparison.
    /// - witness: `tests::sheaf::a_section_of_another_width_is_refused`
    #[spec(ensures: |ref ret| ret.is_ok() || matches!(*ret, Err(SheafError::CellOutside(_) | SheafError::SectionWidth { .. })))]
    fn fits<Value>(
        &self,
        (cell, section): (Element, &[Value]),
    ) -> Result<(), SheafError>
    {
        let width = self.width(cell)?;
        if section.len() != usize::from(width) {
            return Err(SheafError::SectionWidth {
                cell,
                width: Width::from(section.len()),
            });
        }
        Ok(())
    }

    /// Whether the sections of two cells agree at each cell above both.
    ///
    /// # Specification
    /// - requires: each section has one value for each entry of its cell's
    ///   stalk.
    /// - ensures: the two differ exactly when their restrictions differ at a
    ///   cell above both; then the answer names the least cell of the overlap
    ///   where they differ, and the first entry there.
    /// - fails: a cell past the poset, or a section of another width, is
    ///   refused by its cell; a sum of a matrix's row past the integers is
    ///   refused.
    /// - panics: none.
    /// - intension: the least cells of the overlap in cell order, each read
    ///   once, so a caller that changes one member of a cover compares only the
    ///   pairs that hold it.
    ///
    /// # Errors
    /// - [`SheafError::CellOutside`]: a cell lies past the poset.
    /// - [`SheafError::SectionWidth`]: a section has another number of values
    ///   than its cell's stalk.
    /// - [`SheafError::Overflow`]: a sum of a matrix's row passes the integers.
    /// - [`SheafError::EntryOutside`]: unreachable for a sheaf a constructor
    ///   makes.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the config shape's two faces agree and differ at
    ///   their meet; L2 — every gluing of every face cover compares its pairs
    ///   through it; L3 — the projective line's two charts agree through a
    ///   twist by one half.
    /// - witness: `tests::sheaf::a_cover_glues_where_its_sections_agree_on_the_overlap`
    /// - witness: `tests::sheaf::an_overlap_with_two_least_cells_compares_at_each`
    /// - witness: `tests::linear::a_section_glues_through_a_matrix_where_its_scaled_values_agree`
    #[spec(ensures: |ref ret| ret.is_ok() || matches!(*ret, Err(SheafError::CellOutside(_) | SheafError::SectionWidth { .. } | SheafError::EntryOutside { .. } | SheafError::Overflow)))]
    #[inline]
    pub fn compare<Value>(
        &self,
        left: (Element, &[Value]),
        right: (Element, &[Value]),
    ) -> Result<Agreement, SheafError>
    where
        Kind: Restricts<Value>,
        Value: Eq,
    {
        self.fits(left)?;
        self.fits(right)?;
        let left_star = self.star(left.0)?;
        let right_star = self.star(right.0)?;
        for least in self.least(left_star.meet(right_star))? {
            if let Difference::At(entry) = self.difference(left, right, least)? {
                return Ok(Agreement::Differ {
                    overlap: least,
                    entry,
                });
            }
        }
        Ok(Agreement::Agree)
    }

    /// The gluing of the sections of `cover`: the glued section, or each pair
    /// of members whose restrictions differ.
    ///
    /// # Specification
    /// - requires: each member's section has one value for each entry of its
    ///   cell's stalk.
    /// - ensures: the gluing obstructs exactly when two members' restrictions
    ///   differ at a cell above both. Each obstruction names the pair, the
    ///   least cell of their overlap where the restrictions differ, and the
    ///   first entry there. A glued section holds, at each cell above a member,
    ///   the restriction of the first member below it.
    /// - fails: a member past the poset, or a section of another width, is
    ///   refused by its cell; a sum of a matrix's row past the integers is
    ///   refused.
    /// - panics: none.
    /// - intension: the pairs in cover order, the earlier member first; the
    ///   least cells of each overlap in cell order, and one obstruction for
    ///   each pair at most.
    ///
    /// # Errors
    /// - [`SheafError::CellOutside`]: a member lies past the poset.
    /// - [`SheafError::SectionWidth`]: a section has another number of values
    ///   than its cell's stalk.
    /// - [`SheafError::Overflow`]: a sum of a matrix's row passes the integers.
    /// - [`SheafError::EntryOutside`], [`SheafError::OutsideSupport`]:
    ///   unreachable for a sheaf a constructor makes.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every choice of values zero and one on the face cover
    ///   of every corpus shape and every small carrier, against the union
    ///   square's mediator pair by pair, separates a lost overlap, a wrong
    ///   entry or a wrong pair; L3 — the config shape's two faces glue on their
    ///   meet and are obstructed there, and a section one value short is
    ///   refused; L3 — the projective line's two charts glue through a twist by
    ///   one half, and the glued section holds the halved values on the
    ///   overlap.
    /// - witness: `tests::sheaf::a_cover_glues_where_its_sections_agree_on_the_overlap`
    /// - witness: `tests::sheaf::a_section_of_another_width_is_refused`
    /// - witness: `tests::sheaf::an_overlap_with_two_least_cells_compares_at_each`
    /// - witness: `tests::linear::a_section_glues_through_a_matrix_where_its_scaled_values_agree`
    #[spec(ensures: |ref ret| match *ret {
        Ok(Gluing::Obstructed(ref obstructions)) => !obstructions.is_empty(),
        Ok(Gluing::Glued(_)) => true,
        Err(error) => matches!(error, SheafError::CellOutside(_) | SheafError::SectionWidth { .. }
            | SheafError::EntryOutside { .. } | SheafError::OutsideSupport(_) | SheafError::Overflow),
    })]
    #[inline]
    pub fn glue<Value>(
        &self,
        cover: &[(Element, &[Value])],
    ) -> Result<Gluing<Value>, SheafError>
    where
        Kind: Restricts<Value>,
        Value: Copy + Eq,
    {
        let mut support = ElementSet::EMPTY;
        for &member in cover {
            self.fits(member)?;
            let star = self.star(member.0)?;
            support = support.union(star);
        }
        let mut obstructions = Vec::new();
        for (first, &left) in cover.iter().enumerate() {
            for (second, &right) in cover.iter().enumerate().skip(first.saturating_add(1)) {
                match self.compare(left, right)? {
                    Agreement::Agree => {},
                    Agreement::Differ { overlap, entry } => obstructions.push(Obstruction {
                        members: (CoverIndex::from(first), CoverIndex::from(second)),
                        overlap,
                        entry,
                    }),
                }
            }
        }
        if !obstructions.is_empty() {
            return Ok(Gluing::Obstructed(obstructions));
        }
        let section = self.section(cover, support)?;
        Ok(Gluing::Glued(section))
    }

    /// The glued section of `cover` on `support`, the cells above its members.
    ///
    /// # Specification
    /// - requires: the sections of `cover` agree at each overlap, and `support`
    ///   is the union of the members' stars.
    /// - ensures: each cell of `support` holds the restriction of the first
    ///   member below it.
    /// - fails: a map read outside its stalk, or a sum past the integers, is
    ///   refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`SheafError::Overflow`]: a sum of a matrix's row passes the integers.
    /// - [`SheafError::EntryOutside`], [`SheafError::OutsideSupport`],
    ///   [`SheafError::CellOutside`]: unreachable for a cover `Sheaf::glue`
    ///   checked.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the config shape's glued section holds each face's
    ///   values and the shared value at the meet; L3 — the projective line's
    ///   glued section holds the halved values on the overlap.
    /// - witness: `tests::sheaf::a_cover_glues_where_its_sections_agree_on_the_overlap`
    /// - witness: `tests::linear::a_section_glues_through_a_matrix_where_its_scaled_values_agree`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |section| section.support == support))]
    fn section<Value>(
        &self,
        cover: &[(Element, &[Value])],
        support: ElementSet,
    ) -> Result<Section<Value>, SheafError>
    where
        Kind: Restricts<Value>,
        Value: Copy,
    {
        let mut bounds = Vec::with_capacity(support.elements().count().saturating_add(1));
        let mut values = Vec::new();
        bounds.push(0);
        for cell in support.elements() {
            let mut below = None;
            for &(member, section) in cover {
                let star = self.star(member)?;
                if star.contains(cell) == Membership::Inside {
                    below = Some((member, section));
                    break;
                }
            }
            let (member, section) = below.ok_or(SheafError::OutsideSupport(cell))?;
            let width = self.width(cell)?;
            for entry in (0 .. usize::from(width)).map(Entry::from) {
                let value = self.value_at((member, cell), section, entry)?;
                values.push(value.owned());
            }
            bounds.push(values.len());
        }
        Ok(Section {
            support,
            bounds,
            values,
        })
    }
}

/// The count of `poset`'s cells.
///
/// # Specification
/// - provides: the count, at most 64.
/// - fails: a poset of more than 64 cells is refused by its count, since each
///   set of cells is one bit row.
/// - panics: none.
///
/// # Errors
/// - [`SheafError::Poset`]: the poset has more than 64 cells.
///
/// # Adequacy
/// - hypothesis: L3 — a tower's level of 127 and of 128 cells separates the
///   count refusal.
/// - witness: `tests::towers::the_level_past_the_cell_budget_is_refused_by_its_count`
#[spec(ensures: |ref ret| ret.as_ref().map_or(true, |count| usize::from(*count) <= WIDEST))]
fn counted<Cell>(poset: &GradedPoset<Cell>) -> Result<ElementCount, SheafError>
{
    let count = poset.cells().len();
    if count > WIDEST {
        return Err(SheafError::Poset(DualityError::TooManyElements(
            ElementCount::from(count),
        )));
    }
    Ok(ElementCount::from(count))
}

/// The width of each cell of `poset` and each cell's star, with `record`
/// called once for each pair of a cell and a cell strictly above it.
///
/// # Specification
/// - ensures: one width and one star for each cell, in cell order.
/// - fails: a refusal of `record`, or a cell the poset refuses, is refused.
/// - panics: none.
/// - intension: `width` is called once for each cell in cell order. `record` is
///   called for each upper cell in cell order, each lower cell in cell order.
///
/// # Errors
/// - each refusal of `record`.
/// - [`SheafError::Poset`], [`SheafError::CellOutside`]: unreachable for a
///   poset that `GradedPoset::new` makes.
///
/// # Adequacy
/// - hypothesis: L2 — every sheaf of every test is framed through it, so a lost
///   pair or a lost star cell changes a gluing or a cohomology.
/// - witness: `tests::sheaf::a_cover_glues_where_its_sections_agree_on_the_overlap`
/// - witness: `tests::linear::the_projective_line_s_twist_by_minus_two_has_one_class_in_degree_one`
#[spec(ensures: |ref ret| ret.as_ref().map_or(true, |&(ref widths, ref stars)| widths.len() == poset.cells().len()
    && stars.len() == poset.cells().len()))]
fn framed<Cell, Widths, Record>(
    poset: &GradedPoset<Cell>,
    width: Widths,
    mut record: Record,
) -> Result<(Vec<Width>, Vec<ElementSet>), SheafError>
where
    Widths: FnMut(&Cell) -> Width,
    Record: FnMut(Above<'_, Cell>) -> Result<(), SheafError>,
{
    let widths: Vec<Width> = poset.cells().iter().map(width).collect();
    let mut stars = vec![ElementSet::EMPTY; poset.cells().len()];
    for (upper, upper_cell) in poset.cells().iter().enumerate() {
        let upper = Element::from(upper);
        let own = ElementSet::single(upper).map_err(SheafError::Poset)?;
        let closure = poset.closure(upper).map_err(SheafError::Poset)?;
        for lower in closure.elements() {
            let star = stars
                .get_mut(usize::from(lower))
                .ok_or(SheafError::CellOutside(lower))?;
            *star = star.union(own);
        }
        let upper_width = widths
            .get(usize::from(upper))
            .copied()
            .ok_or(SheafError::CellOutside(upper))?;
        for lower in closure.elements().filter(|&lower| lower != upper) {
            let lower_cell = poset
                .cells()
                .get(usize::from(lower))
                .ok_or(SheafError::CellOutside(lower))?;
            let lower_width = widths
                .get(usize::from(lower))
                .copied()
                .ok_or(SheafError::CellOutside(lower))?;
            record(Above {
                lower,
                upper,
                lower_cell,
                upper_cell,
                lower_width,
                upper_width,
            })?;
        }
    }
    Ok((widths, stars))
}

/// Pushes the entry map `map` of `above` onto `entries`, and gives where it
/// starts.
///
/// # Specification
/// - ensures: on success, `entries` holds one more entry for each entry of the
///   upper stalk, each inside the lower stalk.
/// - fails: an entry past the lower stalk, or another number of entries than
///   the upper stalk, is refused by the pair.
/// - panics: none.
///
/// # Errors
/// - [`SheafError::EntryOutside`]: an entry lies past the lower stalk.
/// - [`SheafError::RestrictionWidth`]: the map holds another number of entries
///   than the upper stalk.
///
/// # Adequacy
/// - hypothesis: L3 — a map past its stalk and a map one entry short separate
///   the two refusals.
/// - witness: `tests::sheaf::a_map_past_its_stalk_is_refused`
/// - witness: `tests::sheaf::a_map_of_another_width_is_refused`
#[spec(ensures: |ref ret| ret.is_ok() || matches!(*ret, Err(SheafError::EntryOutside { .. } | SheafError::RestrictionWidth { .. })))]
fn held<Cell, Map>(
    entries: &mut Vec<Entry>,
    map: Map,
    above: &Above<'_, Cell>,
) -> Result<usize, SheafError>
where
    Map: IntoIterator<Item = Entry>,
{
    let start = entries.len();
    for entry in map {
        if usize::from(entry) >= usize::from(above.lower_width) {
            return Err(SheafError::EntryOutside {
                lower: above.lower,
                upper: above.upper,
                entry,
            });
        }
        entries.push(entry);
    }
    let width = Width::from(entries.len().saturating_sub(start));
    if width != above.upper_width {
        return Err(SheafError::RestrictionWidth {
            lower: above.lower,
            upper: above.upper,
            width,
        });
    }
    Ok(start)
}

/// The first entry at which the entry map `direct` reads another entry than
/// `below` reads at the read of `through`.
///
/// # Specification
/// - provides: the least entry where the two reads differ.
/// - fails: a read past the middle stalk is refused.
/// - panics: none.
///
/// # Errors
/// - [`SheafError::EntryOutside`]: `through` reads past `below`, unreachable
///   for maps a constructor checked.
///
/// # Adequacy
/// - hypothesis: L3 — a chain of three cells whose direct map swaps the two
///   entries its composite keeps separates the refusal.
/// - witness: `tests::sheaf::a_map_that_does_not_compose_is_refused`
#[spec(ensures: |ref ret| ret.is_ok() || matches!(*ret, Err(SheafError::EntryOutside { .. })))]
fn entries_differ(
    direct: &[Entry],
    through: &[Entry],
    below: &[Entry],
    chain: Chain,
) -> Result<Difference, SheafError>
{
    for (entry, (&read, &middle)) in direct.iter().zip(through).enumerate() {
        let composite =
            below
                .get(usize::from(middle))
                .copied()
                .ok_or(SheafError::EntryOutside {
                    lower: chain.lower,
                    upper: chain.middle,
                    entry: middle,
                })?;
        if read != composite {
            return Ok(Difference::At(Entry::from(entry)));
        }
    }
    Ok(Difference::Agree)
}

/// `map` as a matrix of `rows` rows and `columns` columns: an entry map built
/// with one 1 in each row, a matrix borrowed.
///
/// # Specification
/// - requires: `rows` and `columns` are the widths of the map's upper and lower
///   stalks.
/// - ensures: the matrix sends each section as the map does.
/// - fails: a read past the columns, or a shape past the machine word, is
///   refused.
/// - panics: none.
///
/// # Errors
/// - [`SheafError::ShapeMismatch`]: a read lies past the columns, unreachable
///   for an entry map a constructor checked.
/// - [`SheafError::Overflow`]: the shape passes the machine word.
///
/// # Adequacy
/// - hypothesis: L3 — a chain of an entry map and two matrices compares through
///   it.
/// - witness: `tests::linear::matrices_that_do_not_compose_are_refused`
#[spec(ensures: |ref ret| ret.as_ref().map_or(true, |matrix| usize::from(matrix.rows()) == usize::from(rows)
    && usize::from(matrix.columns()) == usize::from(columns)))]
fn dense(
    map: LinearMap<'_>,
    rows: Width,
    columns: Width,
) -> Result<Cow<'_, Matrix>, SheafError>
{
    match map {
        LinearMap::Matrix(matrix) => Ok(Cow::Borrowed(matrix)),
        LinearMap::Entries(entries) => {
            let mut matrix = Matrix::zero(
                Dimension::from(usize::from(rows)),
                Dimension::from(usize::from(columns)),
            )?;
            for (row, &column) in entries.iter().enumerate() {
                matrix.add(
                    Slot::from(row),
                    Slot::from(usize::from(column)),
                    Rational::ONE,
                )?;
            }
            Ok(Cow::Owned(matrix))
        },
    }
}

/// The place of the pair of `lower` and `upper` in a table of `count` cells
/// by `count`.
///
/// # Specification
/// trivial.
fn pair(
    count: ElementCount,
    lower: Element,
    upper: Element,
) -> Slot
{
    Slot::from(
        usize::from(lower)
            .saturating_mul(usize::from(count))
            .saturating_add(usize::from(upper)),
    )
}

/// Whether two maps, or two restrictions, agree.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Difference
{
    /// They agree at every entry.
    Agree,
    /// They first differ at this entry.
    At(Entry),
}

/// Whether the sections of two cells agree where the cells overlap.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Agreement
{
    /// The restrictions agree at every cell above both.
    Agree,
    /// The restrictions differ.
    Differ
    {
        /// The least cell of the overlap where they differ.
        overlap: Element,
        /// The first entry of that cell's stalk where they differ.
        entry: Entry,
    },
}

/// Where two members of a cover differ.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Obstruction
{
    /// The two members, the earlier first.
    pub members: (CoverIndex, CoverIndex),
    /// The least cell of their overlap where their restrictions differ.
    pub overlap: Element,
    /// The first entry of that cell's stalk where they differ.
    pub entry: Entry,
}

/// The verdict on the sections of a cover.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Gluing<Value>
{
    /// The sections agree at each overlap, and glue to this section.
    Glued(Section<Value>),
    /// These pairs of members differ, in cover order; never empty.
    Obstructed(Vec<Obstruction>),
}

/// A section on the cells above the members of a cover: one value for each
/// entry of each such cell's stalk.
///
/// # Specification
/// - ensures: one bound more than the cells of the support, the first zero and
///   the last the number of values, rising by each cell's width.
/// - provides: the support and the values at each of its cells.
/// - panics: none.
/// - executable: none — a type-level block: the invariant is `Sheaf::glue`'s,
///   which makes it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Section<Value>
{
    /// The cells the section holds values at.
    support: ElementSet,
    /// Where each cell's values start in `values`, in cell order, and where
    /// the last ends.
    bounds: Vec<usize>,
    /// The values, cell after cell.
    values: Vec<Value>,
}

impl<Value> Section<Value>
{
    /// The cells the section holds values at: each cell above a member of
    /// its cover.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn support(&self) -> ElementSet
    {
        self.support
    }

    /// The values at a cell of the support, one for each entry of its stalk.
    ///
    /// # Specification
    /// - provides: the restriction to `cell` of the first member below it.
    /// - fails: a cell outside the support is refused by name.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`SheafError::OutsideSupport`]: `cell` lies above no member.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the config shape's glued section reads each face's
    ///   values and the meet's shared value, and refuses a cell outside.
    /// - witness: `tests::sheaf::a_cover_glues_where_its_sections_agree_on_the_overlap`
    #[spec(ensures: |ref ret| ret.as_ref().map_or_else(|error| *error == SheafError::OutsideSupport(cell), |_| true))]
    #[inline]
    pub fn at(
        &self,
        cell: Element,
    ) -> Result<&[Value], SheafError>
    {
        if self.support.contains(cell) == Membership::Outside {
            return Err(SheafError::OutsideSupport(cell));
        }
        let place = self
            .support
            .elements()
            .take_while(|&member| member != cell)
            .count();
        let start = self.bounds.get(place).copied();
        let end = self.bounds.get(place.saturating_add(1)).copied();
        start
            .zip(end)
            .and_then(|(start, end)| self.values.get(start .. end))
            .ok_or(SheafError::OutsideSupport(cell))
    }
}
