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
//! - **Γ is one Batanin tree.** `chain(m)` and `chain(m, (a₁, …, aₘ))` are the
//!   tree's two smallest instances, never cases of their own, so a level past
//!   two needs no new node. Reversal: none.
//! - **The level is held beside the tree.** `[m](0, …, 0)` at level two is the
//!   identities on the chain `[m]`, and the chain at level one is its
//!   composite: one tree, two cells of different dimension. Reversal: none.
//! - **The tree packs in one word.** Its Dyck word under a mark holds 31 nodes
//!   past the root, so a composite stays `Copy` and no larger than the two-case
//!   pasting it replaced. Every shape the chain budget certifies fits far
//!   within it. Reversal: a stratum certifying a tree past 31 nodes, which then
//!   holds its tree on the heap.
//!
//! # References
//!
//! - `vault:01a1897b-d199-7d10-a325-587b76db2508` — exemplar: unbiased
//!   composition is a term former at a certified stratum, and the node holds
//!   the cells' left-nested fold as its realisation.
//!
//! [`Value::Compose`]: crate::Value::Compose

use core::num::NonZeroU8;

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

/// The level of a pasting: the dimension of the cells it composes.
///
/// A chain is at level one and a shape `[m](a₁, …, aₘ)` at level two. A
/// pasting's level is at least its tree's height, since the empty column of
/// a level-two shape is a leaf at height one. No pasting stands at level zero.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Level(Rank);

/// A level as it packs: one and two by name, a level past two by its
/// dimension, never below three.
///
/// The names leave the tag a byte of unused values, so a node holding a
/// pasting keeps the size the two-case pasting gave it.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Rank
{
    /// Level one.
    One,
    /// Level two.
    Two,
    /// A level of three or more.
    Past(NonZeroU8),
}

impl Level
{
    /// The level of a chain, whose cells are 1-cells.
    pub const ONE: Self = Self(Rank::One);
    /// The level of a shape `[m](a₁, …, aₘ)`, whose cells are 2-cells.
    pub const TWO: Self = Self(Rank::Two);
}

impl TryFrom<usize> for Level
{
    type Error = core::num::TryFromIntError;

    /// The level `dimension`, when a byte holds it and it is not zero.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn try_from(dimension: usize) -> Result<Self, Self::Error>
    {
        Ok(Self(match u8::try_from(dimension)? {
            1 => Rank::One,
            2 => Rank::Two,
            past => Rank::Past(NonZeroU8::try_from(past)?),
        }))
    }
}

impl From<Level> for usize
{
    /// The level's dimension.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(level: Level) -> Self
    {
        match level.0 {
            Rank::One => 1,
            Rank::Two => 2,
            Rank::Past(past) => Self::from(core::num::NonZeroUsize::from(past)),
        }
    }
}

/// Why a tree or a pasting does not pack.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PastingError
{
    /// The tree holds more than the 31 nodes past its root one word packs.
    PastTheWord,
    /// The walk goes around no tree: it goes up before it goes down, or ends
    /// below the root.
    NotATree,
    /// The tree stands taller than the level.
    PastItsLevel,
}

impl core::fmt::Display for PastingError
{
    /// Name what does not pack.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        f.write_str(match *self {
            Self::PastTheWord => "a tree of more than 31 nodes past its root",
            Self::NotATree => "a walk that goes around no tree",
            Self::PastItsLevel => "a tree taller than its level",
        })
    }
}

impl core::error::Error for PastingError
{
}

/// A Batanin tree: a root and the trees grafted under it, in order.
///
/// The globular pasting shapes are these trees. `[m]` is the root over `m`
/// leaves, and `[m](a₁, …, aₘ)` the root over `m` children, child `i` over
/// `aᵢ` leaves. A leaf is a cell the composite reads.
///
/// The tree packs as its Dyck word: child by child, a one bit, the child's
/// own word and a zero bit, the least significant first, under a leading one
/// bit that marks the length. A tree of `t` nodes past its root takes `2t`
/// bits. [`Tree::graft`] refuses a tree past the 63 bits below the mark, and
/// the lowering refuses its spelling.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Tree(u64);

/// The bits a tree's word holds below its mark.
const WORD: u32 = 63;

/// A position in a tree's word, from the least significant bit, or a count of
/// its bits.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Bit(u32);

/// One step of the walk around a tree, children in order: down into a child,
/// or back up out of it.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Step
{
    /// Into the next child.
    Down,
    /// Out of the child, back to its parent.
    Up,
}

/// A tree's word under construction: the children grafted so far.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
struct Graft
{
    /// The children's words, the first least significant.
    bits: u64,
    /// How many bits they take.
    length: u32,
}

impl Graft
{
    /// `child` grafted after the children so far.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the word grows by `child`'s opening bit, its own word and its
    ///   closing bit.
    /// - fails: [`PastingError::PastTheWord`] past the 63 bits below the mark,
    ///   the word unchanged.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Tree::graft`].
    /// - witness: `compose::tests::a_tree_reads_back_what_it_grafts`
    #[spec(captures: [before = *self], ensures: |ret| ret.is_ok() || *self == before)]
    fn push(
        &mut self,
        child: Tree,
    ) -> Result<(), PastingError>
    {
        let inner = child.length().0;
        let end = self
            .length
            .checked_add(inner)
            .and_then(|length| length.checked_add(2))
            .filter(|&end| end <= WORD)
            .ok_or(PastingError::PastTheWord)?;
        let mark = 1_u64.checked_shl(inner).ok_or(PastingError::PastTheWord)?;
        let opening = 1_u64
            .checked_shl(self.length)
            .ok_or(PastingError::PastTheWord)?;
        let below = (child.0 ^ mark)
            .checked_shl(self.length.saturating_add(1))
            .ok_or(PastingError::PastTheWord)?;
        self.bits |= opening | below;
        self.length = end;
        Ok(())
    }

    /// The tree of the children grafted.
    ///
    /// # Specification
    /// trivial.
    fn tree(self) -> Tree
    {
        Tree(self.bits | 1_u64.checked_shl(self.length).unwrap_or(0))
    }
}

impl Tree
{
    /// The point: the root alone.
    pub const POINT: Self = Self(1);

    /// The length of the word below the mark.
    ///
    /// # Specification
    /// trivial.
    fn length(self) -> Bit
    {
        Bit(WORD.saturating_sub(self.0.leading_zeros()))
    }

    /// The step the bit at `at` packs: an opening bit goes down, a closing
    /// one up.
    ///
    /// # Specification
    /// trivial.
    fn step(
        self,
        at: Bit,
    ) -> Step
    {
        if self
            .0
            .checked_shr(at.0)
            .is_some_and(|shifted| shifted & 1 == 1)
        {
            Step::Down
        }
        else {
            Step::Up
        }
    }

    /// The root over `children`, in order.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Tree::children`] answers `children` back.
    /// - fails: [`PastingError::PastTheWord`] for more than 31 nodes past the
    ///   root, the children's own counted.
    /// - panics: none.
    /// - executable: none — the children are an iterator the call consumes.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two columns of one leaf each read back as grafted, 31
    ///   leaves pack, and 32 do not.
    /// - witness: `compose::tests::a_tree_reads_back_what_it_grafts`
    #[inline]
    pub fn graft<Children>(children: Children) -> Result<Self, PastingError>
    where
        Children: IntoIterator<Item = Self>,
    {
        let mut graft = Graft::default();
        for child in children {
            graft.push(child)?;
        }
        Ok(graft.tree())
    }

    /// `[m]`: the root over `cells` leaves.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a tree of height one over `cells` leaves, the point for none.
    /// - fails: [`PastingError::PastTheWord`] past 31 leaves.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Tree::graft`].
    /// - witness: `compose::tests::a_tree_reads_back_what_it_grafts`
    #[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|tree| tree.leaves() == cells))]
    #[inline]
    pub fn chain(cells: CellCount) -> Result<Self, PastingError>
    {
        let mut graft = Graft::default();
        for _cell in 0 .. cells.0 {
            graft.push(Self::POINT)?;
        }
        Ok(graft.tree())
    }

    /// The tree a walk goes around, as [`Tree::walk`] answers it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Tree::walk`] answers `steps` back.
    /// - fails: [`PastingError::NotATree`] for a walk that goes up before it
    ///   goes down, or ends below the root; [`PastingError::PastTheWord`] for
    ///   one of more than 63 steps.
    /// - panics: none.
    /// - executable: none — the steps are an iterator the call consumes.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a grafted tree's walk goes around the tree again, and
    ///   a walk going up first or ending below the root does not.
    /// - witness: `compose::tests::a_tree_reads_back_what_it_grafts`
    #[inline]
    pub fn from_walk<Steps>(steps: Steps) -> Result<Self, PastingError>
    where
        Steps: IntoIterator<Item = Step>,
    {
        let (mut bits, mut length, mut depth) = (0_u64, 0_u32, 0_u32);
        for step in steps {
            if length >= WORD {
                return Err(PastingError::PastTheWord);
            }
            match step {
                Step::Down => {
                    bits |= 1_u64.checked_shl(length).ok_or(PastingError::PastTheWord)?;
                    depth = depth.saturating_add(1);
                },
                Step::Up => {
                    depth = depth.checked_sub(1).ok_or(PastingError::NotATree)?;
                },
            }
            length = length.saturating_add(1);
        }
        if depth != 0 {
            return Err(PastingError::NotATree);
        }
        let mark = 1_u64.checked_shl(length).ok_or(PastingError::PastTheWord)?;
        Ok(Self(bits | mark))
    }

    /// The trees grafted under the root, the first first.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn children(self) -> impl Iterator<Item = Self>
    {
        let Bit(length) = self.length();
        let mut position = 0_u32;
        core::iter::from_fn(move || {
            let start = position;
            let mut depth = 0_u32;
            while position < length {
                let opens = self.step(Bit(position)) == Step::Down;
                position = position.saturating_add(1);
                if opens {
                    depth = depth.saturating_add(1);
                    continue;
                }
                depth = depth.saturating_sub(1);
                if depth == 0 {
                    let inner = position.saturating_sub(start).saturating_sub(2);
                    let mark = 1_u64.checked_shl(inner)?;
                    let below =
                        self.0.checked_shr(start.saturating_add(1))? & mark.saturating_sub(1);
                    return Some(Self(below | mark));
                }
            }
            None
        })
    }

    /// Each child's own child count, the first first: the column heights of
    /// `[m](a₁, …, aₘ)`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn columns(self) -> impl Iterator<Item = CellCount>
    {
        self.children()
            .map(|child| CellCount(child.children().count()))
    }

    /// The walk around the tree from its root, each child entered and left
    /// in order: a `Down` before the child's own walk, an `Up` after it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn walk(self) -> impl Iterator<Item = Step>
    {
        (0 .. self.length().0).map(move |position| self.step(Bit(position)))
    }

    /// The leaves past the root: the cells a composite over the tree reads.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn leaves(self) -> CellCount
    {
        let below = self.0 ^ 1_u64.checked_shl(self.length().0).unwrap_or(0);
        let closed = below & !below.checked_shr(1).unwrap_or(0);
        CellCount(usize::try_from(closed.count_ones()).unwrap_or(usize::MAX))
    }
}

/// The position of a column in a level-two shape, from zero.
///
/// A tree packs at most 31 children ([`Tree`]), so a byte holds every
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

/// Γ in `compose[n, k](Γ, d)`: a Batanin tree at the level of the cells it
/// composes.
///
/// `chain(m)` is the tree `[m]` at level one, and `chain(m, (a₁, …, aₘ))` the
/// tree `[m](a₁, …, aₘ)` at level two. Each is an instance of the one pasting,
/// never a case of its own.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Pasting
{
    /// The dimension of the cells it composes.
    level: Level,
    /// The shape.
    tree: Tree,
}

impl Pasting
{
    /// `tree` at `level`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the pasting answers `level` and `tree` back.
    /// - fails: [`PastingError::PastItsLevel`] for a level below the tree's
    ///   height.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a tree of height three stands at level three and not
    ///   at level two.
    /// - witness: `compose::tests::a_pasting_stands_at_its_tree_s_height_or_above`
    #[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|pasting| pasting.level() == level && pasting.tree() == tree))]
    #[inline]
    pub fn new(
        level: Level,
        tree: Tree,
    ) -> Result<Self, PastingError>
    {
        let (mut depth, mut height) = (0_usize, 0_usize);
        for step in tree.walk() {
            match step {
                Step::Down => {
                    depth = depth.saturating_add(1);
                    height = height.max(depth);
                },
                Step::Up => depth = depth.saturating_sub(1),
            }
        }
        if usize::from(level) < height {
            return Err(PastingError::PastItsLevel);
        }
        Ok(Self { level, tree })
    }

    /// `chain(m)`: the tree `[m]` at level one.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a level-one pasting reading `cells` cells.
    /// - fails: as [`Tree::chain`].
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Tree::graft`].
    /// - witness: `compose::tests::a_tree_reads_back_what_it_grafts`
    #[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|pasting| pasting.level() == Level::ONE && pasting.cells() == cells))]
    #[inline]
    pub fn chain(cells: CellCount) -> Result<Self, PastingError>
    {
        Ok(Self {
            level: Level::ONE,
            tree: Tree::chain(cells)?,
        })
    }

    /// `chain(m, (a₁, …, aₘ))`: the tree `[m](a₁, …, aₘ)` at level two, `m`
    /// the count of `heights`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a level-two pasting whose tree's columns are `heights`.
    /// - fails: [`PastingError::PastTheWord`] for more than 31 nodes past the
    ///   root, the columns and their leaves counted together.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Tree::graft`].
    /// - witness: `compose::tests::a_tree_reads_back_what_it_grafts`
    #[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|pasting| pasting.level() == Level::TWO && pasting.tree().columns().eq(heights.iter().copied())))]
    #[inline]
    pub fn columns(heights: &[CellCount]) -> Result<Self, PastingError>
    {
        let mut graft = Graft::default();
        for &height in heights {
            graft.push(Tree::chain(height)?)?;
        }
        Ok(Self {
            level: Level::TWO,
            tree: graft.tree(),
        })
    }

    /// The dimension of the cells it composes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn level(self) -> Level
    {
        self.level
    }

    /// The shape.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn tree(self) -> Tree
    {
        self.tree
    }

    /// How many cells the shape's composite reads: its tree's leaves, so `m`
    /// for a chain, and one per 2-cell and per empty column at level two.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn cells(self) -> CellCount
    {
        self.tree.leaves()
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
    #[spec(ensures: |ret| ret.pasting.level() == Level::ONE && usize::from(ret.pasting.cells()) == 2)]
    #[inline]
    #[must_use]
    pub fn binary() -> Self
    {
        Self {
            stratum: Stratum {
                degree: Degree::from(3_usize),
                bound: ShapeSize::from(5_usize),
            },
            // `[2]`: two leaves, each an opening bit and a closing one,
            // under the mark.
            pasting: Pasting {
                level: Level::ONE,
                tree: Tree(0b1_0101),
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
    if composite.pasting.level() != Level::TWO {
        return None;
    }
    let mut rest = cells;
    let mut folded: Option<Folded> = None;
    for CellCount(height) in composite.pasting.tree().columns() {
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
