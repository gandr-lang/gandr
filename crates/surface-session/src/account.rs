//! The account: one row for each declaration of the session's latest judged
//! revision, keyed by the declaration's content, with what each phase of the
//! engine reported of it.
//!
//! # A row is a section over the declaration's content
//!
//! **Choice.** [`Account`] keeps one [`AccountRow`] for each declaration of
//! the revision's own text that has a content key. The key is the item's
//! [`ContentKey`], which its incremental checkpoint keeps, so the account
//! reads it and hashes nothing. Two declarations share one row only when
//! their keys agree. A row holds three columns:
//!
//! | Column | Values | Written by | When |
//! | --- | --- | --- | --- |
//! | the checker's verdict | [`CheckerVerdict`] | the judgement | at each judgement |
//! | the kernel tier | [`KernelState`]: pending, or the tier an admission settled | the judgement keeps it or sets pending, the admission writes it | when the admission ends |
//! | the compile tier | [`CompileTier`], or [`compiled::Absent::Uncompiled`] | the emitter's record | never yet: the hub compiles nothing |
//!
//! A judgement keeps the row of each declaration whose key and verdict are
//! unchanged, with its kernel tier, so an edit to a comment or to another
//! declaration moves no row. It writes a new row at pending for each key it
//! has not seen, and sets a row back to pending when its verdict changed. A
//! tier that names another declaration by its position, a withheld one, goes
//! back to pending too, because its support is the readmission environment
//! and not the content alone. The judgement drops the row of each key that
//! the revision does not hold. A kept tier holds until the admission ends,
//! and the admission then writes each row again: the tier it reports, or
//! pending when it reports none, as a disagreement does for each row but the
//! one it stopped at. An admission that a later revision retires reports
//! nothing, so its rows stay as the judgement left them.
//!
//! **Alternatives.** A table keyed by admission position moves every row
//! below an inserted declaration. A table rebuilt at each judgement loses the
//! kernel tier of each unchanged declaration until the next admission ends. A
//! key that holds the readmission environment beside the content would move
//! each dependent's row when a declaration it reads changes, and the session
//! has no such key: a dependent keeps its tier until the admission writes it.
//!
//! **Reversal.** When the attested verdict cache lands, a tier admitted from
//! it is one more value of the kernel column. When the hub compiles each
//! checked declaration, the emitter's record writes the compile column.
//!
//! # References
//!
//! - `vault:01a1c68b-1e9e-7942-aa36-b8d9096dec0e` — anchor: §
//!   engine-surface-items keys the verdict and the tiers by the declaration's
//!   content key and keeps the table across rechecks.

use alloc::collections::BTreeMap;
use alloc::collections::btree_map::Entry;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_checker::Verdict;
use gandr_core_incremental::ContentKey;
use gandr_core_incremental::recall;
use gandr_kernel_term::ConstantIndex;
use gandr_surface_corpus::Produced;
use gandr_surface_dispatcher::KernelTier;
use quenchant_shape::shape::Maybe;

quenchant_shape::reason_enum! {
    /// Why a row has no compile tier.
    pub mod compiled {
        /// The reason none is held.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The hub runs no emitter, so no declaration has a compile
            /// record.
            Uncompiled,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why the account holds no row at a position.
    pub mod unrowed {
        /// The reason no row is held.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The latest judged revision has no declaration of its own text
            /// with a content key at that position: none is there, the
            /// lowering refused it, or its content holds an unresolved node.
            Unkeyed,
        }
    }
}

/// The checker's verdict on a declaration, as a class that names no node of
/// the revision's arena, so a row keeps it across revisions.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum CheckerVerdict
{
    /// A nominal declaration that formed.
    Data,
    /// The body checked against the declared type.
    Checked,
    /// The unsigned body synthesised its type.
    Synthesised,
    /// The body is a hole under a declared type, owed.
    Owed,
    /// The declaration waits on owed holes.
    Suspended,
    /// The lowering, the checker or the corpus refused the declaration.
    Refused,
}

impl CheckerVerdict
{
    /// The class of what a declaration produced.
    ///
    /// # Specification
    /// - requires: nothing; the function is total over what a declaration
    ///   produces.
    /// - ensures: each verdict of the checker is its own class; a checker's
    ///   refusal, a lowering's and a corpus guard's are each
    ///   [`CheckerVerdict::Refused`].
    /// - provides: the verdict column of a row.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a module with a definition, an owed declaration, a
    ///   refused one and a data declaration shows each class in its row.
    /// - witness: `tests::account::each_row_holds_the_verdict_and_then_the_kernel_tier`
    #[spec(ensures: |ret| match *produced {
        Produced::Judged(Verdict::Data) => matches!(ret, Self::Data),
        Produced::Judged(Verdict::Checked { .. }) => matches!(ret, Self::Checked),
        Produced::Judged(Verdict::Synthesised { .. }) => matches!(ret, Self::Synthesised),
        Produced::Judged(Verdict::Owed(_)) => matches!(ret, Self::Owed),
        Produced::Judged(Verdict::Suspended(_)) => matches!(ret, Self::Suspended),
        Produced::Judged(Verdict::Refused(_)) | Produced::Unlowered(_) | Produced::Guarded(_) => matches!(ret, Self::Refused),
    })]
    #[inline]
    #[must_use]
    pub const fn of(produced: &Produced<'_>) -> Self
    {
        match *produced {
            Produced::Judged(Verdict::Data) => Self::Data,
            Produced::Judged(Verdict::Checked { .. }) => Self::Checked,
            Produced::Judged(Verdict::Synthesised { .. }) => Self::Synthesised,
            Produced::Judged(Verdict::Owed(_)) => Self::Owed,
            Produced::Judged(Verdict::Suspended(_)) => Self::Suspended,
            Produced::Judged(Verdict::Refused(_))
            | Produced::Unlowered(_)
            | Produced::Guarded(_) => Self::Refused,
        }
    }
}

/// Where the kernel stands on a declaration, as its row keeps it.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum KernelState
{
    /// No admission has reported on the declaration's content and verdict
    /// yet.
    Pending,
    /// An admission reported this tier.
    Settled(KernelTier),
}

/// How the emitter compiled a declaration.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum CompileTier
{
    /// The portable interpreter runs it.
    Interpreted,
    /// Stencil code runs it.
    Stencil,
    /// Code that the optimiser built runs it.
    Optimised,
}

/// One declaration's row: the checker's verdict, the kernel tier and the
/// compile tier.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct AccountRow
{
    /// The checker's verdict.
    verdict: CheckerVerdict,
    /// Where the kernel stands on it.
    kernel: KernelState,
    /// How the emitter compiled it.
    compile: Maybe<CompileTier, compiled::Absent>,
}

impl AccountRow
{
    /// The checker's verdict.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn verdict(&self) -> CheckerVerdict
    {
        self.verdict
    }

    /// Where the kernel stands on the declaration.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn kernel(&self) -> KernelState
    {
        self.kernel
    }

    /// How the emitter compiled the declaration.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn compile(&self) -> Maybe<CompileTier, compiled::Absent>
    {
        self.compile
    }
}

/// The account of the latest judged revision: one row for each declaration
/// of its own text that has a content key, kept across judgements by key.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one row for each distinct key the latest judgement listed, and no
///   other; the positions ascend.
/// - provides: the table that the language server and the render bus read.
/// - panics: none.
/// - executable: none — the table has no call boundary of its own; its methods
///   carry the predicates.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Account::row_at`].
/// - witness: `tests::account::a_comment_edit_keeps_every_row_and_an_edit_moves_one`
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Account
{
    /// Each row by its key, beside the judgement that listed the key last.
    rows: BTreeMap<ContentKey, (Judgement, AccountRow)>,
    /// The latest judgement's own declarations with a key: each one's
    /// admission position and key, ascending by position.
    declared: Vec<(ConstantIndex, ContentKey)>,
    /// How many judgements the account took.
    judgements: Judgement,
}

/// How many judgements an account took: the mark of the judgement that
/// listed a row's key last, which drops the rows of keys no judgement keeps.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Judgement(u64);

impl Account
{
    /// Take a judgement that lists `declared`: each declaration of the
    /// revision's own text, by its admission position, with its content key
    /// and the checker's verdict, ascending by position.
    ///
    /// # Specification
    /// - requires: `declared` ascends by position.
    /// - ensures: one row for each distinct listed key and no other. A row
    ///   whose key and verdict a previous judgement listed keeps its kernel
    ///   tier, unless the tier is withheld; every other listed row holds the
    ///   listed verdict at [`KernelState::Pending`]. Every row keeps its
    ///   compile tier. A declaration with no key has no row.
    /// - provides: the judgement's half of the account.
    /// - fails: never.
    /// - panics: none.
    /// - economy: one lookup for each declaration, a row allocated only for a
    ///   key the account did not hold, and the list's buffer reused. The
    ///   judgement lists each declaration of the revision's own text, and #4369
    ///   bounds the list by the edit.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a comment edit keeps every row with its tier, and an
    ///   edit to one declaration moves that row alone to pending.
    /// - witness: `tests::account::a_comment_edit_keeps_every_row_and_an_edit_moves_one`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body looks up every listed declaration and sweeps every row once; the check reads each listed declaration and each row once; #4369 bounds the list by the edit"
        )
    )]
    #[spec(ensures: self.declared.windows(2).all(|pair| matches!(pair, [earlier, later] if earlier.0 < later.0))
        && self.rows.values().all(|&(listed, _)| listed == self.judgements)
        && self.declared.iter().all(|&(_, key)| self.rows.contains_key(&key)))]
    pub(crate) fn judged<Declared>(
        &mut self,
        declared: Declared,
    ) where
        Declared: IntoIterator<
            Item = (
                ConstantIndex,
                Maybe<ContentKey, recall::Absent>,
                CheckerVerdict,
            ),
        >,
    {
        self.judgements = Judgement(self.judgements.0.saturating_add(1));
        let judgement = self.judgements;
        self.declared.clear();
        for (constant, key, verdict) in declared {
            let Maybe::Present(key) = key
            else {
                continue;
            };
            self.declared.push((constant, key));
            match self.rows.entry(key) {
                Entry::Occupied(mut occupied) => {
                    let &mut (ref mut listed, ref mut row) = occupied.get_mut();
                    *listed = judgement;
                    if row.verdict != verdict
                        || matches!(
                            row.kernel,
                            KernelState::Settled(KernelTier::Withheld { .. })
                        )
                    {
                        row.verdict = verdict;
                        row.kernel = KernelState::Pending;
                    }
                },
                Entry::Vacant(vacant) => {
                    let _row = vacant.insert((judgement, AccountRow {
                        verdict,
                        kernel: KernelState::Pending,
                        compile: Maybe::Absent(compiled::Absent::Uncompiled),
                    }));
                },
            }
        }
        self.rows.retain(|_, &mut (listed, _)| listed == judgement);
    }

    /// Take an admission of the latest judged revision that reported `tiers`:
    /// each kernel tier it settled, by its admission position, ascending. An
    /// admission that ran whole reports each declaration it judged, and one
    /// that the kernel stopped reports the declaration it stopped at.
    ///
    /// # Specification
    /// - requires: `tiers` ascends by position, and the admission judged the
    ///   latest judged revision.
    /// - ensures: each row at a position `tiers` names holds that tier, and
    ///   each other row is at [`KernelState::Pending`]; the rows and their
    ///   verdicts are unchanged.
    /// - provides: the admission's half of the account.
    /// - fails: never.
    /// - panics: none.
    /// - economy: one pass over the positions and the tiers together, and one
    ///   lookup for each row; nothing allocated. The pass reads each row of the
    ///   revision, and #4369 bounds it by the edit.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a module's rows read pending after the judgement and
    ///   each declaration's tier once its admission ends.
    /// - witness: `tests::account::each_row_holds_the_verdict_and_then_the_kernel_tier`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body writes the row of every listed declaration once; the check reads each listed declaration's row once and searches the tiers for it; #4369 bounds the list by the edit"
        )
    )]
    #[spec(captures: [count = self.rows.len()],
        ensures: self.rows.len() == count
        && self.declared.iter().all(|&(at, key)| self.rows.get(&key).is_some_and(|&(_, row)|
            row.kernel == tiers.binary_search_by_key(&at, |&(constant, _)| constant).ok()
                .and_then(|found| tiers.get(found))
                .map_or(KernelState::Pending, |&(_, tier)| KernelState::Settled(tier)))))]
    pub(crate) fn settled(
        &mut self,
        tiers: &[(ConstantIndex, KernelTier)],
    )
    {
        let mut reported = tiers.iter().peekable();
        for &(at, key) in &self.declared {
            while reported.next_if(|&&(constant, _)| constant < at).is_some() {}
            let kernel = reported
                .next_if(|&&(constant, _)| constant == at)
                .map_or(KernelState::Pending, |&(_, tier)| {
                    KernelState::Settled(tier)
                });
            if let Some(&mut (_, ref mut row)) = self.rows.get_mut(&key) {
                row.kernel = kernel;
            }
        }
    }

    /// The content key and the row of the latest judged revision's
    /// declaration at `constant`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the key the latest judgement listed at `constant`, with its
    ///   row, or [`unrowed::Absent::Unkeyed`] when it listed none there.
    /// - provides: what a face reads for one declaration, by one search of the
    ///   positions and one lookup of the key, with no computation of its own;
    ///   the key names the declaration's card across revisions.
    /// - fails: [`unrowed::Absent::Unkeyed`].
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each declaration of a module reads its own row at its
    ///   position, before and after an edit that shifts no position and one
    ///   that inserts a declaration above it.
    /// - witness: `tests::account::a_comment_edit_keeps_every_row_and_an_edit_moves_one`
    #[spec(ensures: |ret| matches!(ret, Maybe::Present(_))
        == self.declared.binary_search_by_key(&constant, |&(at, _)| at).is_ok())]
    #[inline]
    pub fn row_at(
        &self,
        constant: ConstantIndex,
    ) -> Maybe<(ContentKey, AccountRow), unrowed::Absent>
    {
        self.declared
            .binary_search_by_key(&constant, |&(at, _)| at)
            .ok()
            .and_then(|found| self.declared.get(found))
            .and_then(|&(_, key)| self.rows.get(&key).map(|&(_, row)| (key, row)))
            .map_or(Maybe::Absent(unrowed::Absent::Unkeyed), Maybe::Present)
    }

    /// Each row of the latest judged revision with its declaration's position
    /// and key, ascending by position.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one entry for each declaration the latest judgement listed,
    ///   in its order, each with its row.
    /// - provides: the whole table for a face that renders every row.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the result is a lazy iterator, so the call returns
    ///   no value that a predicate reads; [`Account::judged`] checks the table
    ///   that it walks.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Account::row_at`].
    /// - witness: `tests::account::each_row_holds_the_verdict_and_then_the_kernel_tier`
    #[inline]
    pub fn rows(&self) -> impl Iterator<Item = (ConstantIndex, ContentKey, AccountRow)> + '_
    {
        self.declared.iter().filter_map(|&(constant, key)| {
            self.rows.get(&key).map(|&(_, row)| (constant, key, row))
        })
    }
}
