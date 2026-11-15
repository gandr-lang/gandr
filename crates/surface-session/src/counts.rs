//! The counts layer: what the engine did for each declaration of a recheck,
//! counted into one dense column that the account takes into its rows.
//!
//! # A recheck counts into one dense column
//!
//! **Choice.** [`Counts`] is the sink of the counts layer. It holds one
//! [`CountColumn`]: one [`DeclarationCounts`] for each admission position, in
//! a vector that grows to the last position that the recheck counts. An event
//! is one add into the column. The column allocates only when a recheck counts
//! a position past its end. The session counts through
//! [`Instrument::counts`], which answers the column of [`Counts`] and no column
//! for each other sink. A judgement generic over [`Silent`](crate::Silent) gets
//! no column, so it attributes no form and makes no add.
//!
//! | Count | What it counts | Where the session counts it |
//! | --- | --- | --- |
//! | hits, misses | the consults of the checker's goal memo that the memo answered, and the consults that it keyed and held no answer for | the incremental pass, around each item that it judges |
//! | nodes | the arena nodes that the lowering minted and the item's content reaches, and the nodes that the pass minted for the item | the incremental pass |
//! | judged | one when the incremental pass judged the declaration, zero when it adopted it | the incremental pass |
//! | molded | the forms of the declaration's halves that the parse molded | after the lowering |
//! | obligations | the parse's completion obligations inside the declaration's halves | after the lowering |
//! | crossed | one when the admission offered the declaration to the kernel again | when the admission settles |
//! | recalled, expanded, kept | the goals of the kernel's check of the declaration that its memo recalled, that it expanded, and that a kept outcome of an earlier admission answered | when the admission settles |
//!
//! When a judgement ends, the account sets the counts of each row of the
//! revision's own text from the column, with each kernel count at zero. When
//! an admission ends, the account sets the kernel counts of each row from the
//! positions that the admission recorded ([`Positioning::Tallied`]), which
//! reads no clock. So a row holds the counts of the latest recheck, and the
//! counts of a declaration that the recheck adopted read zero judged.
//!
//! **Alternatives.** One method of [`Instrument`] for each event lets each
//! layer count in its own way. But the session must then attribute the molded
//! forms and the obligations for each sink, or ask each sink whether it counts.
//! A column that the account keeps across rechecks needs a reset for each row
//! that a recheck does not reach. A recheck's own column needs none.
//!
//! **Reversal.** A layer that counts an event per declaration that the column
//! does not hold adds a field to [`DeclarationCounts`]. A count that the
//! checker or the kernel makes inside a judgement step, such as a memo consult
//! of one goal, keeps the tally of its context; the column does not change.
//!
//! # What it does not cover
//!
//! The kernel's counts come from the census of each environment entry, which
//! the admission reads after it crosses each declaration. An admission that a
//! later revision retires, or that the kernel stops, records no positions, so
//! its rows keep the kernel counts of zero that the judgement wrote. The
//! inlay and the hover section that render the counts are later units.
//!
//! # References
//!
//! - `vault:01a1c68b-1e9e-7942-aa36-b8d9096dec0e` — anchor: §
//!   engine-surface-layers decides the counts layer, its column and its cost
//!   when it is off.
//! - `vault:01a178aa-6917-7983-b5cd-86e2af86b3ec` — anchor: §
//!   kernel-reassessment-memo names the hits and the misses of the checker's
//!   memo and of the kernel's, which the row counts apart.

use alloc::vec::Vec;

use anodized::spec;
use gandr_core_checker::tally::MemoCount;
use gandr_core_checker::tally::MemoTally;
use gandr_core_incremental::Adoption;
use gandr_kernel_term::ConstantIndex;
use gandr_surface_dispatcher::Placed;
use gandr_surface_dispatcher::Positioning;
use gandr_surface_dispatcher::placement;
use quenchant_shape::shape::Maybe;

use crate::instrument::Instrument;

quenchant_shape::reason_enum! {
    /// Why a sink answers no column, or a row holds no counts.
    pub mod uncounted {
        /// The reason none is held.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The sink's layer is not the counts layer, or the latest
            /// judgement ran at such a sink.
            Unselected,
        }
    }
}

/// How many events of one kind the counts layer counted for one declaration
/// in one recheck.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct EventCount(u64);

impl From<u64> for EventCount
{
    /// The count of `events` events.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(events: u64) -> Self
    {
        Self(events)
    }
}

impl From<EventCount> for u64
{
    /// The count as a number.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: EventCount) -> Self
    {
        count.0
    }
}

/// What the engine did for one declaration in one recheck.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub struct DeclarationCounts
{
    /// The consults of the checker's goal memo.
    memo: MemoTally,
    /// The arena nodes of the declaration's lowering and of its judgement.
    nodes: EventCount,
    /// One when the incremental pass judged the declaration.
    judged: EventCount,
    /// The forms of its halves that the parse molded.
    molded: EventCount,
    /// The parse's completion obligations inside its halves.
    obligations: EventCount,
    /// One when the admission offered it to the kernel again.
    crossed: EventCount,
    /// The goals of the kernel's check that the kernel's memo recalled.
    recalled: EventCount,
    /// The goals of the kernel's check that the kernel expanded.
    expanded: EventCount,
    /// The goals of the kernel's check that a kept outcome answered.
    kept: EventCount,
}

impl DeclarationCounts
{
    /// The consults of the checker's goal memo that the memo answered.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn hits(&self) -> MemoCount
    {
        self.memo.hits()
    }

    /// The consults of the checker's goal memo that it keyed and held no
    /// answer for.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn misses(&self) -> MemoCount
    {
        self.memo.misses()
    }

    /// The arena nodes that the lowering minted and the declaration's content
    /// reaches, and the nodes that the incremental pass minted for it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn nodes(&self) -> EventCount
    {
        self.nodes
    }

    /// One when the incremental pass judged the declaration, zero when it
    /// adopted it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn judged(&self) -> EventCount
    {
        self.judged
    }

    /// The forms of the declaration's halves that the parse molded.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn molded(&self) -> EventCount
    {
        self.molded
    }

    /// The parse's completion obligations inside the declaration's halves.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn obligations(&self) -> EventCount
    {
        self.obligations
    }

    /// One when the admission offered the declaration to the kernel again.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn crossed(&self) -> EventCount
    {
        self.crossed
    }

    /// The goals of the kernel's check that the kernel's memo recalled.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn recalled(&self) -> EventCount
    {
        self.recalled
    }

    /// The goals of the kernel's check that the kernel expanded.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn expanded(&self) -> EventCount
    {
        self.expanded
    }

    /// The goals of the kernel's check that a kept outcome of an earlier
    /// admission answered.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn kept(&self) -> EventCount
    {
        self.kept
    }

    /// These counts with the kernel's counts of the admission that placed the
    /// declaration at `placed`, or with none when it did not cross.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the judgement's counts unchanged; crossed is one exactly when
    ///   `placed` is present, and the kernel's counts are its census, zero when
    ///   it has none.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Counts`].
    /// - witness: `tests::counts::a_second_recheck_counts_no_judged_item`
    #[spec(ensures: |ret| ret.memo == self.memo && ret.nodes == self.nodes
        && ret.molded == self.molded && ret.judged == self.judged
        && (u64::from(ret.crossed) == 1) == matches!(placed, Maybe::Present(_)))]
    #[must_use]
    pub(crate) fn admitted(
        self,
        placed: Maybe<Placed, placement::Absent>,
    ) -> Self
    {
        let (crossed, (recalled, expanded, kept)) = match placed {
            Maybe::Present(placed) => (1, match placed.census() {
                Maybe::Present(census) => (
                    u64::from(census.recalls()),
                    u64::from(census.expansions()),
                    u64::from(census.kept()),
                ),
                Maybe::Absent(_) => (0, 0, 0),
            }),
            Maybe::Absent(_) => (0, (0, 0, 0)),
        };
        Self {
            crossed: EventCount(crossed),
            recalled: EventCount(recalled),
            expanded: EventCount(expanded),
            kept: EventCount(kept),
            ..self
        }
    }
}

/// One [`DeclarationCounts`] for each admission position that a recheck
/// counted, in a dense column.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a position that the recheck never counted reads zero counts.
/// - provides: what the account takes into its rows when the judgement ends.
/// - panics: none.
/// - executable: none — the column has no call boundary of its own; its methods
///   carry the predicates.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Counts`].
/// - witness: `tests::counts::a_second_recheck_counts_no_judged_item`
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct CountColumn(Vec<DeclarationCounts>);

impl CountColumn
{
    /// The counts at `constant`: zero when the recheck counted nothing there.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn at(
        &self,
        constant: ConstantIndex,
    ) -> DeclarationCounts
    {
        self.0
            .get(usize::from(constant))
            .copied()
            .unwrap_or_default()
    }

    /// Write the counts at `constant` with `write`, the column grown to hold
    /// them.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the column holds at least `constant` plus one entries; the
    ///   entry at `constant` is written once, and each other entry is
    ///   unchanged.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Counts`].
    /// - witness: `tests::counts::a_second_recheck_counts_no_judged_item`
    #[spec(captures: [before = self.0.len()],
        ensures: self.0.len() >= before && self.0.len() > usize::from(constant))]
    fn write<Write>(
        &mut self,
        constant: ConstantIndex,
        write: Write,
    ) where
        Write: FnOnce(&mut DeclarationCounts),
    {
        let at = usize::from(constant);
        if at >= self.0.len() {
            self.0
                .resize(at.saturating_add(1), DeclarationCounts::default());
        }
        if let Some(counts) = self.0.get_mut(at) {
            write(counts);
        }
    }

    /// Count the incremental pass's step for the item at `constant`: the
    /// consults `memo` of the checker's memo, `nodes` arena nodes, and whether
    /// the pass judged it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) fn passed(
        &mut self,
        constant: ConstantIndex,
        (memo, nodes, adoption): (MemoTally, EventCount, Adoption),
    )
    {
        self.write(constant, |counts| {
            counts.memo = memo;
            counts.nodes = nodes;
            counts.judged = EventCount(u64::from(adoption == Adoption::Judged));
        });
    }

    /// Count `molded` molded forms and `obligations` completion obligations
    /// inside the halves of the declaration at `constant`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) fn parsed(
        &mut self,
        constant: ConstantIndex,
        (molded, obligations): (EventCount, EventCount),
    )
    {
        self.write(constant, |counts| {
            counts.molded = molded;
            counts.obligations = obligations;
        });
    }
}

/// The sink of the counts layer: one column of counts for each recheck.
///
/// A hub makes one for each job of a recheck, so each column starts empty.
///
/// # Specification
/// - requires: a sink observes. It never changes a verdict, a report or the
///   session's state, the account's counts aside.
/// - ensures: after a judgement, the column holds the counts of each item that
///   the judgement's incremental pass adopted or judged, and the molded forms
///   and obligations of each declaration of the revision's own text. An
///   admission at this sink records the positions and the census of each
///   declaration that crossed.
/// - provides: the counts that the account takes into its rows.
/// - panics: none.
/// - executable: none — the sink's effects are the session's; the witness reads
///   them through the account.
///
/// # Adequacy
/// - hypothesis: L3 — a corpus source rechecked twice at this sink reads, in
///   each row, the hits, misses and judged item of its first judgement, and no
///   judged item in its second; the kernel counts read the census that `gandr
///   check --measure` prints.
/// - witness: `tests::counts::a_second_recheck_counts_no_judged_item`
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Counts
{
    /// The column of the recheck.
    column: CountColumn,
}

impl Counts
{
    /// The column of the recheck.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn column(&self) -> &CountColumn
    {
        &self.column
    }
}

impl Instrument for Counts
{
    /// The column of the recheck.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn counts(&mut self) -> Maybe<&mut CountColumn, uncounted::Absent>
    {
        Maybe::Present(&mut self.column)
    }

    /// Each declaration's position and census, and no clock read.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn positioning(&self) -> Positioning
    {
        Positioning::Tallied
    }
}
