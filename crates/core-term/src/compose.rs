//! Unbiased composition as the core holds it: the stratum a composite is made
//! at and the shape its cells fill.
//!
//! [`Value::Compose`] is `compose[n, k](Γ, d)`. Its [`Composite`] is the
//! [`Stratum`] `n` and `k` write and the [`Pasting`] Γ names. The cells of `d`
//! are the node's children in vertex order, and so is the composite the
//! lowering realises from them: the left-nested fold `(c₁ then c₂) then …`,
//! whose every motive fixes the first cell's start. `gandr-core-checker`'s
//! `compose` module certifies the stratum, reads Γ as a shape of it and checks
//! that the cells fill it; evaluation and the kernel read the realisation.
//!
//! # Decisions
//!
//! - **The realisation is a child.** A composite of paths is a transport per
//!   cell, and each motive names the carrier and the start, which only a typed
//!   reading knows. The lowering reads them as it reads them for `then`, so the
//!   node carries a term evaluation runs and the bridge erases to, and nothing
//!   downstream rebuilds it. The alternative, a realisation the checker records
//!   by node, leaves evaluation with a node it cannot run. Reversal: a core
//!   composition former of its own in both checkers and the kernel.
//! - **Γ is named, not read off the cells.** At dimension one the chain is the
//!   cells' count, but a shape above it is not, so the former takes the shape
//!   the wreath's levels extend. Reversal: none at dimension one.
//!
//! # References
//!
//! - `vault:01a1897b-d199-7d10-a325-587b76db2508` — exemplar: unbiased
//!   composition is a term former at a certified stratum, and the node holds
//!   the cells' left-nested fold as its realisation.
//!
//! [`Value::Compose`]: crate::Value::Compose

use anodized::spec;
use gandr_theory_sites::Degree;
use gandr_theory_sites::ShapeSize;

use crate::CoreArena;
use crate::arena::ValueId;
use crate::arena::ValueTypeId;
use crate::syntax::Computation;
use crate::syntax::Value;
use crate::ua::Stratum;

#[cfg(test)]
mod tests;

/// How many cells a pasting shape holds: its vertex count.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct CellCount(usize);

impl From<usize> for CellCount
{
    /// The count of `cells`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(cells: usize) -> Self
    {
        Self(cells)
    }
}

impl From<CellCount> for usize
{
    /// The number of cells.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: CellCount) -> Self
    {
        count.0
    }
}

/// The column heights of a level-two pasting `[m](a₁, …, aₘ)`, packed.
///
/// Column by column, `aᵢ` one bits and a zero bit, the least significant
/// first, under a leading one bit that marks the length.
///
/// A shape of `m` columns and `Σ aᵢ` 2-cells takes `m + Σ aᵢ` bits.
/// [`Heights::new`] refuses a shape past the 63 bits below the mark, and the
/// lowering refuses its spelling.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Heights(u64);

impl Heights
{
    /// The heights of `columns`, when their marks fit in 63 bits.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Heights::columns`] answers `columns` back.
    /// - fails: none for more than 63 marks, the columns and their 2-cells
    ///   counted together.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the whisker's heights read back, and 64 marks do not
    ///   pack.
    /// - witness: `compose::tests::heights_read_back_what_they_pack`
    #[spec(ensures: |ret| ret.is_none_or(|heights| heights.columns().eq(columns.iter().copied())))]
    #[inline]
    #[must_use]
    pub fn new(columns: &[CellCount]) -> Option<Self>
    {
        let mut bits = 0_u64;
        let mut length = 0_u32;
        for &CellCount(height) in columns {
            for _cell in 0 .. height {
                bits |= 1_u64.checked_shl(length)?;
                length = length.checked_add(1)?;
            }
            length = length.checked_add(1)?;
        }
        if length > 63 {
            return None;
        }
        Some(Self(bits | 1_u64.checked_shl(length)?))
    }

    /// Each column's height, the first first.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn columns(self) -> impl Iterator<Item = CellCount>
    {
        let length = 63_u32.saturating_sub(self.0.leading_zeros());
        let mut height = 0_usize;
        (0 .. length).filter_map(move |bit| {
            if self
                .0
                .checked_shr(bit)
                .is_some_and(|shifted| shifted & 1 == 1)
            {
                height = height.saturating_add(1);
                None
            }
            else {
                let column = CellCount(height);
                height = 0;
                Some(column)
            }
        })
    }
}

/// The position of a column in a level-two shape, from zero.
///
/// A shape packs at most 63 columns ([`Heights`]), so a byte holds every
/// position, and a refusal that names one stays as small as it was.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Column(u8);

impl TryFrom<usize> for Column
{
    type Error = core::num::TryFromIntError;

    /// The column at `position`, when a byte holds it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn try_from(position: usize) -> Result<Self, Self::Error>
    {
        u8::try_from(position).map(Self)
    }
}

impl From<Column> for usize
{
    /// The column's position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(column: Column) -> Self
    {
        Self::from(column.0)
    }
}

/// Where a composite's cells fail to meet: along the outer chain's points,
/// or along the 1-cells inside one column of a level-two shape.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Seam
{
    /// The chain the cells, or the columns, compose along.
    Outer,
    /// The chain of a column's 2-cells, composing along their 1-cells.
    Column(Column),
}

/// Γ in `compose[n, k](Γ, d)`: a shape of the site's chain sub-site, or of
/// its wreath over itself.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Pasting
{
    /// `chain(m)`: the chain of `m` composable 1-cells.
    Chain
    {
        /// Its cell count, `m`.
        cells: CellCount,
    },
    /// `chain(m, (a₁, …, aₘ))`: the level-two shape `[m](a₁, …, aₘ)`, the
    /// outer chain of `m` columns, column `i` the chain of `aᵢ` 2-cells.
    Columns
    {
        /// The columns' heights.
        heights: Heights,
    },
}

impl Pasting
{
    /// How many cells the shape's composite reads: `m` for a chain, and one
    /// per 2-cell and per empty column for a level-two shape.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn cells(self) -> CellCount
    {
        match self {
            Self::Chain { cells } => cells,
            Self::Columns { heights } => CellCount(
                heights
                    .columns()
                    .map(|CellCount(height)| height.max(1))
                    .fold(0_usize, usize::saturating_add),
            ),
        }
    }
}

/// The stratum a composite is made at and the shape it composes.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Composite
{
    /// The degree and the catalogue bound written in the head.
    pub stratum: Stratum,
    /// The shape its cells fill.
    pub pasting: Pasting,
}

impl Composite
{
    /// The composite `p then q` is: `compose[3, 5](chain(2), (p, q))`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the 2-chain at degree 3 and bound 5, the least stratum the
    ///   2-chain is a shape of: size `2·2 + 1` and degree `2·2 − 1`.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the stratum is the 2-chain's own degree and size, the
    ///   least a stratum reading it reaches.
    /// - witness: `compose::tests::the_binary_composite_is_the_least_stratum_of_two_cells`
    #[spec(ensures: |ret| matches!(ret.pasting, Pasting::Chain { cells } if usize::from(cells) == 2))]
    #[inline]
    #[must_use]
    pub fn binary() -> Self
    {
        Self {
            stratum: Stratum {
                degree: Degree::from(3_usize),
                bound: ShapeSize::from(5_usize),
            },
            pasting: Pasting::Chain {
                cells: CellCount(2),
            },
        }
    }
}

/// The composite of `cells` at `composite`, its realisation the left-nested
/// `then` fold over `carrier` from `start`.
///
/// # Specification
/// - requires: `carrier` and `start` are read in the context the composite
///   stands in, `start` being the first cell's left endpoint.
/// - ensures: a [`Value::Compose`] holding `cells` in order, its realisation
///   [`crate::identity::then`] of the composite so far and the next cell for
///   each cell past the first, the first cell returned for one cell, and the
///   reflexivity at `start` returned for none.
/// - provides: the one realisation the lowering and the tests build.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — three cells realise as the transport of the first two's
///   composite along the third; one cell realises as itself returned.
/// - witness: `compose::tests::three_cells_realise_as_the_left_nested_fold`
#[spec(ensures: |ret| matches!(arena.value(ret), Some(&Value::Compose { composite: held, cells: ref held_cells, realised })
    if held == composite && **held_cells == *cells
        && match cells.len() {
            0 | 1 => matches!(arena.computation(realised), Some(&Computation::Return(_))),
            _ => matches!(arena.computation(realised), Some(&Computation::PathTransport { path, .. }) if cells.last() == Some(&path)),
        }))]
#[inline]
#[must_use]
pub fn compose(
    arena: &mut CoreArena,
    composite: Composite,
    (carrier, start): (ValueTypeId, ValueId),
    cells: &[ValueId],
) -> ValueId
{
    let mut written = cells.iter().copied();
    let realised = if let Some(first) = written.next() {
        let mut realised = arena.computation_return(first);
        let mut sofar = first;
        for cell in written {
            realised = crate::identity::then(arena, carrier, start, sofar, cell);
            sofar = arena.value_returned(realised);
        }
        realised
    }
    else {
        let reflexive = arena.value_here(start);
        arena.computation_return(reflexive)
    };
    arena.value_compose(composite, cells.into(), realised)
}

/// A path type as the level-two realisation reads it: `Path(carrier, left,
/// right)`.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Ends
{
    /// The type the endpoints inhabit.
    pub carrier: ValueTypeId,
    /// The left endpoint.
    pub left: ValueId,
    /// The right endpoint.
    pub right: ValueId,
}

/// One column of a level-two composite folded so far: the carrier and the
/// outer start, the end reached, the sources' and the targets' folds, and the
/// 2-cell between them, none while every column so far is empty.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Folded
{
    /// The type the 1-cells inhabit, `A`.
    carrier: ValueTypeId,
    /// The first column's start, `x₀`.
    start: ValueId,
    /// The last column's end.
    end: ValueId,
    /// The fold of the columns' sources.
    source: ValueId,
    /// The fold of the columns' targets.
    target: ValueId,
    /// The 2-cell from `source` to `target`.
    cell: Option<ValueId>,
}

/// The composite of `cells` at the level-two `composite`, each cell beside its
/// path type, and that composite's path type.
///
/// Column by column, a column of `a > 0` 2-cells folds vertically with
/// [`crate::identity::then`] one layer up, and an empty column's 1-cell `f`
/// stands as `here(f)`. The columns fold horizontally by the whiskers the
/// filler generator lifts by: the 2-cell so far right-whiskered by the next
/// column's source, then the fold of the targets so far left-whiskering the
/// next column's 2-cell. A whisker by an empty column, or of one, is left out,
/// since transport along `here` returns its base.
///
/// # Specification
/// - requires: `cells` are the composite's cells in column order, each beside
///   the path type it stands at, all in one context.
/// - ensures: a [`Value::Compose`] holding the cells in order and the fold as
///   its realisation, beside `Path(Path(A, x₀, xₘ), s, t)`, `s` and `t` the
///   `then` folds of the columns' sources and targets.
/// - fails: none for a pasting that is no level-two shape, cells of another
///   count than it reads, or a 2-cell whose carrier is no path type.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the whisker `[2](1, 0)` realises as the right whisker
///   alone, the horizontal composite `[2](1, 1)` as the right whisker then the
///   left, and a chain pasting or a cell short realises none.
/// - witness: `compose::tests::a_level_two_composite_folds_its_columns_by_whiskers`
#[spec(ensures: |ret| ret.is_none_or(|(node, _)| matches!(arena.value(node), Some(&Value::Compose { composite: held, .. }) if held == composite)))]
#[inline]
#[must_use]
pub fn compose_columns(
    arena: &mut CoreArena,
    composite: Composite,
    cells: &[(ValueId, Ends)],
) -> Option<(ValueId, Ends)>
{
    let Pasting::Columns { heights } = composite.pasting
    else {
        return None;
    };
    let mut rest = cells;
    let mut folded: Option<Folded> = None;
    for CellCount(height) in heights.columns() {
        let (column, tail) = rest.split_at_checked(height.max(1))?;
        rest = tail;
        let (&(first, first_ends), _) = column.split_first()?;
        let &(_, last_ends) = column.last()?;
        let (carrier, from, to, source, target, cell) = if height == 0 {
            (
                first_ends.carrier,
                first_ends.left,
                first_ends.right,
                first,
                first,
                None,
            )
        }
        else {
            let Some(&crate::syntax::ValueType::Path {
                carrier,
                left,
                right,
            }) = arena.value_type(first_ends.carrier)
            else {
                return None;
            };
            let mut sofar = first;
            for &(next, _) in column.get(1 ..)? {
                let composite =
                    crate::identity::then(arena, first_ends.carrier, first_ends.left, sofar, next);
                sofar = arena.value_returned(composite);
            }
            (
                carrier,
                left,
                right,
                first_ends.left,
                last_ends.right,
                Some(sofar),
            )
        };
        let column = Folded {
            carrier,
            start: from,
            end: to,
            source,
            target,
            cell,
        };
        folded = Some(folded.map_or(column, |before| beside(arena, before, column)));
    }
    let whole = folded?;
    if !rest.is_empty() {
        return None;
    }
    let value = whole.cell.unwrap_or_else(|| arena.value_here(whole.source));
    let realised = arena.computation_return(value);
    let written: alloc::vec::Vec<ValueId> = cells.iter().map(|&(cell, _)| cell).collect();
    let node = arena.value_compose(composite, written.into(), realised);
    let carrier = arena.value_type_path(whole.carrier, whole.start, whole.end);
    Some((node, Ends {
        carrier,
        left: whole.source,
        right: whole.target,
    }))
}

/// `before` and the next `column` folded horizontally: the sources' and the
/// targets' `then` folds, and the 2-cell so far right-whiskered by the
/// column's source, then the fold of the targets left-whiskering the
/// column's 2-cell, each whisker left out where its 2-cell is none.
///
/// # Specification
/// trivial.
fn beside(
    arena: &mut CoreArena,
    before: Folded,
    column: Folded,
) -> Folded
{
    let ends = (before.carrier, before.start, column.end);
    let sources = crate::identity::then(
        arena,
        before.carrier,
        before.start,
        before.source,
        column.source,
    );
    let sources = arena.value_returned(sources);
    let targets = crate::identity::then(
        arena,
        before.carrier,
        before.start,
        before.target,
        column.target,
    );
    let targets = arena.value_returned(targets);
    let right = before.cell.map(|alpha| {
        crate::identity::whisker(
            arena,
            ends,
            (before.source, column.source),
            crate::identity::Whisker::Right,
            alpha,
        )
    });
    let left = column.cell.map(|beta| {
        crate::identity::whisker(
            arena,
            ends,
            (before.target, column.source),
            crate::identity::Whisker::Left,
            beta,
        )
    });
    let cell = match (right, left) {
        (Some(first), Some(second)) => {
            let composites = arena.value_type_path(before.carrier, before.start, column.end);
            let both = crate::identity::then(arena, composites, sources, first, second);
            Some(arena.value_returned(both))
        },
        (Some(only), None) | (None, Some(only)) => Some(only),
        (None, None) => None,
    };
    Folded {
        carrier: before.carrier,
        start: before.start,
        end: column.end,
        source: sources,
        target: targets,
        cell,
    }
}
