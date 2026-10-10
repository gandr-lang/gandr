//! The report a settle run returns, and the tally a driver reads its counts
//! from.
//!
//! # The ledger size is always printed
//!
//! A run that settles with obligations left is a run that signed for them, so
//! the rendered tally opens with the ledger size whether the run is settled
//! or not. An assumption a report does not print is one nobody reviews.
//!
//! # Every fixture has a line
//!
//! The rendered report gives a line to every fixture, settled or not, and to
//! every unsettled declaration, fixture or not, before the tally. A settled
//! declaration that carries no expectation is the strict root's ordinary case
//! and is only counted.

use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
use gandr_core_checker::ObligationCount;
use gandr_core_term::FailureClass;
use gandr_surface_lowering::DeclarationCount;
use quenchant_shape::shape::Maybe;

use crate::expectation::Membership;
use crate::root::CorpusRoot;
use crate::settle::DeclarationReport;
use crate::settle::Settlement;
use crate::settle::Surviving;
use crate::settle::produced_refusal;

/// Whether a settled run also has an empty ledger.
///
/// # Specification
/// - requires: the producer owns the correspondence between counts and the
///   declarations or runs represented.
/// - ensures: Distinguishes settled runs with no owed obligations from all
///   other runs; being unsealed does not by itself make a run unsettled.
/// - panics: none.
/// - executable: none — The enum stores no declaration or ledger counts;
///   `Tally::seal` carries the executable relation.
///
/// # Adequacy
/// - hypothesis: L3 — mixed source reports and exact saturation boundaries
///   distinguish categories, dropped fields and arithmetic errors;
///   settled/ledger boundary cases distinguish sealing from settlement. The
///   contributing source relationship is established at producer boundaries
///   rather than inferred from a record alone.
/// - witness: `report::tests::sealed_is_reported_never_gated`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Seal
{
    /// Settled, owing nothing.
    Sealed,
    /// Unsettled, or settled with obligations in the ledger.
    Unsealed,
}

impl fmt::Display for Seal
{
    /// Writes `sealed` or `unsealed`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes distinct sealed and unsealed states.
    /// - fails: propagates a refusing sink as `fmt::Error`.
    /// - panics: none.
    /// - executable: none — the formatter exposes neither emitted text nor
    ///   readable sink state. The witness observes selected declaration
    ///   identities, all distinct numeric payloads, state/class labels and a
    ///   refusing sink.
    ///
    /// # Errors
    /// Returns `fmt::Error` when the sink refuses a write.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a mixed source report separates visible fixtures and
    ///   unsettled names from an omitted settled helper. A tally with distinct
    ///   numeric payloads detects omitted or repeated counts; typed labels, row
    ///   order and exact sink refusals cover the remaining observations without
    ///   fixing sentences.
    /// - witness: `report::tests::reports_select_declarations_and_retain_summary_fields`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match *self {
            | Self::Sealed => "sealed",
            | Self::Unsealed => "unsealed",
        })
    }
}

/// How many of some declarations settled and how many did not.
///
/// # Specification
/// - requires: the producer owns the correspondence between counts and the
///   declarations or runs represented.
/// - ensures: Keeps settled and unsettled declaration totals in separate
///   saturating channels.
/// - panics: none.
/// - executable: none — The record has no contributing declarations; its
///   counting and accumulation methods specify transitions.
///
/// # Adequacy
/// - hypothesis: L3 — mixed source reports and exact saturation boundaries
///   distinguish categories, dropped fields and arithmetic errors;
///   settled/ledger boundary cases distinguish sealing from settlement. The
///   contributing source relationship is established at producer boundaries
///   rather than inferred from a record alone.
/// - witness: `report::tests::the_tally_counts_every_declaration_once`
/// - witness: `report::tests::saturating_tallies_preserve_every_count_channel`
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct SettleCounts
{
    /// The settled declarations.
    settled: DeclarationCount,
    /// The unsettled declarations.
    unsettled: DeclarationCount,
}

impl SettleCounts
{
    /// The settled declarations.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn settled(&self) -> DeclarationCount
    {
        self.settled
    }

    /// The unsettled declarations.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn unsettled(&self) -> DeclarationCount
    {
        self.unsettled
    }

    /// Count one declaration of `settlement`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: increments only the selected settlement count, saturating at
    ///   the largest declaration count; the other count is unchanged.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — real settled and unsettled declarations, plus the
    ///   largest count and its predecessor. Exact selected and unselected
    ///   counts distinguish wrong-channel increments, wraparound and premature
    ///   saturation.
    /// - witness: `report::tests::the_tally_counts_every_declaration_once`
    /// - witness: `report::tests::saturating_tallies_preserve_every_count_channel`
    #[spec(
        captures: before = *self,
        ensures: |_| {
    usize::from(self.settled)
        == usize::from(before.settled)
            .saturating_add(usize::from(settlement == Settlement::Settled))
        && usize::from(self.unsettled)
            == usize::from(before.unsettled)
                .saturating_add(usize::from(settlement == Settlement::Unsettled))
},
    )]
    fn count(
        &mut self,
        settlement: Settlement,
    )
    {
        match settlement {
            | Settlement::Settled => self.settled = one_more(self.settled),
            | Settlement::Unsettled => self.unsettled = one_more(self.unsettled),
        }
    }

    /// Add `other`'s counts to these, saturating.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: adds settled to settled and unsettled to unsettled,
    ///   saturating each channel independently.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — source-derived mixed tallies and distinct ordinary,
    ///   maximal and overflowing channels. Exact sums distinguish omitted or
    ///   swapped fields and nonsaturating arithmetic.
    /// - witness: `report::tests::absorbing_a_tally_sums_every_count`
    /// - witness: `report::tests::saturating_tallies_preserve_every_count_channel`
    #[spec(
        captures: before = *self,
        ensures: |_| {
    usize::from(self.settled)
        == usize::from(before.settled).saturating_add(usize::from(other.settled))
        && usize::from(self.unsettled)
            == usize::from(before.unsettled).saturating_add(usize::from(other.unsettled))
},
    )]
    fn absorb(
        &mut self,
        other: Self,
    )
    {
        self.settled = declarations_sum(self.settled, other.settled);
        self.unsettled = declarations_sum(self.unsettled, other.unsettled);
    }
}

impl fmt::Display for SettleCounts
{
    /// Writes `n settled, m unsettled`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes both settlement count channels.
    /// - fails: propagates a refusing sink as `fmt::Error`.
    /// - panics: none.
    /// - executable: none — the formatter exposes neither emitted text nor
    ///   readable sink state. The witness observes selected declaration
    ///   identities, all distinct numeric payloads, state/class labels and a
    ///   refusing sink.
    ///
    /// # Errors
    /// Returns `fmt::Error` when the sink refuses a write.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a mixed source report separates visible fixtures and
    ///   unsettled names from an omitted settled helper. A tally with distinct
    ///   numeric payloads detects omitted or repeated counts; typed labels, row
    ///   order and exact sink refusals cover the remaining observations without
    ///   fixing sentences.
    /// - witness: `report::tests::reports_select_declarations_and_retain_summary_fields`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(
            f,
            "{} settled, {} unsettled",
            usize::from(self.settled),
            usize::from(self.unsettled)
        )
    }
}

/// How many refused declarations each failure class holds.
///
/// # Specification
/// - requires: the producer owns the correspondence between counts and the
///   declarations or runs represented.
/// - ensures: Keeps one saturating declaration count for each failure class,
///   without conflating categories.
/// - panics: none.
/// - executable: none — The record has no producing refusals; accumulation
///   predicates and independently observed bucket counts establish its
///   interpretation.
///
/// # Adequacy
/// - hypothesis: L3 — mixed source reports and exact saturation boundaries
///   distinguish categories, dropped fields and arithmetic errors;
///   settled/ledger boundary cases distinguish sealing from settlement. The
///   contributing source relationship is established at producer boundaries
///   rather than inferred from a record alone.
/// - witness: `report::tests::saturating_tallies_preserve_every_count_channel`
/// - witness: `report::tests::the_tally_counts_every_declaration_once`
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ClassCounts
{
    /// Refusals of [`FailureClass::UserAbsence`].
    user_absence: DeclarationCount,
    /// Refusals of [`FailureClass::Unrepresentable`].
    unrepresentable: DeclarationCount,
    /// Refusals of [`FailureClass::MalformedSource`].
    malformed_source: DeclarationCount,
    /// Refusals of [`FailureClass::EngineFault`].
    engine_fault: DeclarationCount,
}

impl ClassCounts
{
    /// The classes, in the order a report writes them.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: enumerates every failure class exactly once for accumulation
    ///   and reporting.
    /// - panics: none.
    /// - executable: none — the constant has no invocation for a specification
    ///   attribute; its consumer witness supplies distinct independent counts
    ///   for all four classes.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every failure-class bucket is accumulated and
    ///   observed at a distinct expected count. Omission or duplication changes
    ///   at least one count, without treating display order as semantics.
    /// - witness: `report::tests::saturating_tallies_preserve_every_count_channel`
    const CLASSES: [FailureClass; 4_usize] = [
        FailureClass::UserAbsence,
        FailureClass::Unrepresentable,
        FailureClass::MalformedSource,
        FailureClass::EngineFault,
    ];

    /// The refused declarations of `class`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns the count held for exactly `class`.
    /// - panics: none.
    /// - executable: none — the returned foreign `DeclarationCount` hides its
    ///   scalar and exposes it only through a non-const `From` implementation.
    ///   A const scalar observer in the owning crate is needed to compare the
    ///   selected value here without changing this public const API.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — all four failure classes hold distinct counts in the
    ///   saturation witness. Exact public observations distinguish a swapped or
    ///   constant bucket; source-derived tallies additionally exercise the
    ///   classifier-to-count path.
    /// - witness: `report::tests::saturating_tallies_preserve_every_count_channel`
    /// - witness: `report::tests::the_tally_counts_every_declaration_once`
    #[inline]
    #[must_use]
    pub const fn count(
        &self,
        class: FailureClass,
    ) -> DeclarationCount
    {
        match class {
            | FailureClass::UserAbsence => self.user_absence,
            | FailureClass::Unrepresentable => self.unrepresentable,
            | FailureClass::MalformedSource => self.malformed_source,
            | FailureClass::EngineFault => self.engine_fault,
        }
    }

    /// The count `class` is tallied in.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns an exclusive reference to exactly the count selected
    ///   by `class`, without changing any count.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — accumulation into all four distinct failure-class
    ///   channels, including saturation, is observed through their public
    ///   counts. The predicate records the selected address before the
    ///   exclusive borrow and observes identity without reading through a stale
    ///   reference.
    /// - witness: `report::tests::saturating_tallies_preserve_every_count_channel`
    /// - witness: `report::tests::absorbing_a_tally_sums_every_count`
    #[spec(
        captures: expected = core::ptr::from_ref(
    match class {
        FailureClass::UserAbsence => &self.user_absence,
        FailureClass::Unrepresentable => &self.unrepresentable,
        FailureClass::MalformedSource => &self.malformed_source,
        FailureClass::EngineFault => &self.engine_fault,
    },
),
        ensures: |ret| core::ptr::eq(core::ptr::from_ref(ret), expected),
    )]
    fn slot(
        &mut self,
        class: FailureClass,
    ) -> &mut DeclarationCount
    {
        match class {
            | FailureClass::UserAbsence => &mut self.user_absence,
            | FailureClass::Unrepresentable => &mut self.unrepresentable,
            | FailureClass::MalformedSource => &mut self.malformed_source,
            | FailureClass::EngineFault => &mut self.engine_fault,
        }
    }

    /// Add `other`'s counts to these, saturating.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: adds each failure-class count to the corresponding channel,
    ///   saturating independently.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — all four classes with distinct zero, ordinary and
    ///   overflowing counts. Exact class-indexed sums distinguish omitted
    ///   classes, switched slots and wraparound.
    /// - witness: `report::tests::saturating_tallies_preserve_every_count_channel`
    /// - witness: `report::tests::absorbing_a_tally_sums_every_count`
    #[spec(
        captures: before = *self,
        ensures: |_| {
    Self::CLASSES
        .into_iter()
        .all(|class| {
            usize::from(self.count(class))
                == usize::from(before.count(class))
                    .saturating_add(usize::from(other.count(class)))
        })
},
    )]
    fn absorb(
        &mut self,
        other: Self,
    )
    {
        for class in Self::CLASSES {
            let slot = self.slot(class);
            *slot = declarations_sum(*slot, other.count(class));
        }
    }
}

impl fmt::Display for ClassCounts
{
    /// Writes each class's count, in the order the classes are declared.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes each failure class and its count.
    /// - fails: propagates a refusing sink as `fmt::Error`.
    /// - panics: none.
    /// - executable: none — the formatter exposes neither emitted text nor
    ///   readable sink state. The witness observes selected declaration
    ///   identities, all distinct numeric payloads, state/class labels and a
    ///   refusing sink.
    ///
    /// # Errors
    /// Returns `fmt::Error` when the sink refuses a write.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a mixed source report separates visible fixtures and
    ///   unsettled names from an omitted settled helper. A tally with distinct
    ///   numeric payloads detects omitted or repeated counts; typed labels, row
    ///   order and exact sink refusals cover the remaining observations without
    ///   fixing sentences.
    /// - witness: `report::tests::reports_select_declarations_and_retain_summary_fields`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        let mut separator = "";
        for class in Self::CLASSES {
            write!(f, "{separator}{} {class}", usize::from(self.count(class)))?;
            separator = ", ";
        }
        Ok(())
    }
}

/// The counts of a settle run: what a driver gates on and prints.
///
/// # Specification
/// - requires: the producer owns the correspondence between counts and the
///   declarations or runs represented.
/// - ensures: Separates declarations, fixtures, ledger, directional residuals
///   and refusal classes. Aggregation saturates each count; settlement depends
///   on unsettled declarations, while sealing additionally requires an empty
///   ledger.
/// - panics: none.
/// - executable: none — The record holds no original report or contributing
///   runs; `count`, `absorb`, `settlement` and `seal` provide the executable
///   boundaries.
///
/// # Adequacy
/// - hypothesis: L3 — mixed source reports and exact saturation boundaries
///   distinguish categories, dropped fields and arithmetic errors;
///   settled/ledger boundary cases distinguish sealing from settlement. The
///   contributing source relationship is established at producer boundaries
///   rather than inferred from a record alone.
/// - witness: `report::tests::the_tally_counts_every_declaration_once`
/// - witness: `report::tests::saturating_tallies_preserve_every_count_channel`
/// - witness: `report::tests::sealed_is_reported_never_gated`
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub struct Tally
{
    /// Every declaration, by settlement.
    declarations: SettleCounts,
    /// The fixtures alone, by settlement.
    fixtures: SettleCounts,
    /// The ledger size: the obligations the run's verdicts owe.
    ledger: ObligationCount,
    /// The obligations left unsettled, summed over every declaration.
    surviving: Surviving,
    /// The refused declarations, by failure class.
    refusals: ClassCounts,
}

impl Tally
{
    /// Every declaration, by settlement.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn declarations(&self) -> SettleCounts
    {
        self.declarations
    }

    /// The fixtures alone, by settlement.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn fixtures(&self) -> SettleCounts
    {
        self.fixtures
    }

    /// The ledger size.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn ledger(&self) -> ObligationCount
    {
        self.ledger
    }

    /// The obligations left unsettled.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn surviving(&self) -> Surviving
    {
        self.surviving
    }

    /// The refused declarations, by failure class.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn refusals(&self) -> ClassCounts
    {
        self.refusals
    }

    /// Add `other`'s counts to these, saturating: one tally over several
    /// runs.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: every count is the saturating sum of the two tallies' own.
    /// - provides: one tally a driver aggregates over every source of a run.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — source-derived mixed tallies and independently stated
    ///   boundary totals across declarations, fixtures, ledger, both residual
    ///   channels and all failure classes. Exact fieldwise sums distinguish
    ///   omissions, cross-channel additions and premature or absent saturation.
    /// - witness: `report::tests::absorbing_a_tally_sums_every_count`
    /// - witness: `report::tests::saturating_tallies_preserve_every_count_channel`
    #[spec(
        captures: before = *self,
        ensures: |_| {
    usize::from(self.declarations.settled)
        == usize::from(before.declarations.settled)
            .saturating_add(usize::from(other.declarations.settled))
        && usize::from(self.declarations.unsettled)
            == usize::from(before.declarations.unsettled)
                .saturating_add(usize::from(other.declarations.unsettled))
        && usize::from(self.fixtures.settled)
            == usize::from(before.fixtures.settled)
                .saturating_add(usize::from(other.fixtures.settled))
        && usize::from(self.fixtures.unsettled)
            == usize::from(before.fixtures.unsettled)
                .saturating_add(usize::from(other.fixtures.unsettled))
        && usize::from(self.ledger)
            == usize::from(before.ledger).saturating_add(usize::from(other.ledger))
        && usize::from(self.surviving.undeclared())
            == usize::from(before.surviving.undeclared())
                .saturating_add(usize::from(other.surviving.undeclared()))
        && usize::from(self.surviving.unproduced())
            == usize::from(before.surviving.unproduced())
                .saturating_add(usize::from(other.surviving.unproduced()))
        && ClassCounts::CLASSES
            .into_iter()
            .all(|class| {
                usize::from(self.refusals.count(class))
                    == usize::from(before.refusals.count(class))
                        .saturating_add(usize::from(other.refusals.count(class)))
            })
},
    )]
    #[inline]
    pub fn absorb(
        &mut self,
        other: &Self,
    )
    {
        self.declarations.absorb(other.declarations);
        self.fixtures.absorb(other.fixtures);
        self.ledger = obligations_sum(self.ledger, other.ledger);
        self.surviving = Surviving::new(
            obligations_sum(self.surviving.undeclared(), other.surviving.undeclared()),
            obligations_sum(self.surviving.unproduced(), other.surviving.unproduced()),
        );
        self.refusals.absorb(other.refusals);
    }

    /// Whether the run is settled: the predicate a corpus run is gated on.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: settled exactly when no declaration is unsettled.
    /// - provides: the run's gate.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — settled and unsettled modules, an empty module and a
    ///   settled fixture with an owed obligation. Exact settlement
    ///   distinguishes checking the wrong count or incorrectly gating on the
    ///   ledger.
    /// - witness: `report::tests::the_run_is_settled_only_when_every_declaration_is`
    /// - witness: `report::tests::sealed_is_reported_never_gated`
    #[spec(
        ensures: |ret| {
    (ret == Settlement::Settled) == (usize::from(self.declarations.unsettled) == 0_usize)
},
    )]
    #[inline]
    #[must_use]
    pub fn settlement(&self) -> Settlement
    {
        if usize::from(self.declarations.unsettled) == 0_usize {
            Settlement::Settled
        }
        else {
            Settlement::Unsettled
        }
    }

    /// Whether the run is sealed: settled with an empty ledger. Reported,
    /// never gated.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: sealed exactly when the run is settled and the ledger size is
    ///   zero.
    /// - provides: the strongest property a run reports.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the cross-product of settled/unsettled and
    ///   empty/nonempty ledger states is observed by the source fixtures. Exact
    ///   seal and settlement distinguish dropping either seal condition and
    ///   treating unsealed as unsettled.
    /// - witness: `report::tests::sealed_is_reported_never_gated`
    #[spec(
        ensures: |ret| {
    (ret == Seal::Sealed)
        == (usize::from(self.declarations.unsettled) == 0_usize
            && usize::from(self.ledger) == 0_usize)
},
    )]
    #[inline]
    #[must_use]
    pub fn seal(&self) -> Seal
    {
        match self.settlement() {
            | Settlement::Settled if usize::from(self.ledger) == 0_usize => Seal::Sealed,
            | Settlement::Settled | Settlement::Unsettled => Seal::Unsealed,
        }
    }

    /// Count one settled declaration.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: counts one declaration by settlement, also counting it as a
    ///   fixture when attributed; adds its directional residual obligations and
    ///   its refusal class when present. Every increment saturates; the
    ///   separately supplied ledger is unchanged.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a source mixing attributed and unattributed, settled
    ///   and unsettled, owed and refused declarations, including two
    ///   source-reached refusal classes. Exact per-channel counts distinguish
    ///   double counting, missed fixture membership, lost residuals and ledger
    ///   recomputation.
    /// - witness: `report::tests::the_tally_counts_every_declaration_once`
    /// - witness: `report::tests::absorbing_a_tally_sums_every_count`
    #[spec(
        captures: before = *self,
        ensures: |_| {
    let settlement = declaration.settlement();
    let fixture = declaration.membership() == Membership::Fixture;
    let surviving = declaration.surviving();
    let refusal = declaration.produced().refusal();
    usize::from(self.declarations.settled)
        == usize::from(before.declarations.settled)
            .saturating_add(usize::from(settlement == Settlement::Settled))
        && usize::from(self.declarations.unsettled)
            == usize::from(before.declarations.unsettled)
                .saturating_add(usize::from(settlement == Settlement::Unsettled))
        && usize::from(self.fixtures.settled)
            == usize::from(before.fixtures.settled)
                .saturating_add(
                    usize::from(fixture && settlement == Settlement::Settled),
                )
        && usize::from(self.fixtures.unsettled)
            == usize::from(before.fixtures.unsettled)
                .saturating_add(
                    usize::from(fixture && settlement == Settlement::Unsettled),
                ) && self.ledger == before.ledger
        && usize::from(self.surviving.undeclared())
            == usize::from(before.surviving.undeclared())
                .saturating_add(usize::from(surviving.undeclared()))
        && usize::from(self.surviving.unproduced())
            == usize::from(before.surviving.unproduced())
                .saturating_add(usize::from(surviving.unproduced()))
        && ClassCounts::CLASSES
            .into_iter()
            .all(|class| {
                usize::from(self.refusals.count(class))
                    == usize::from(before.refusals.count(class))
                        .saturating_add(
                            usize::from(
                                matches!(
                                    refusal, Maybe::Present(refused) if refused.classify() ==
                                    class
                                ),
                            ),
                        )
            })
},
    )]
    fn count(
        &mut self,
        declaration: &DeclarationReport<'_>,
    )
    {
        let settlement = declaration.settlement();
        self.declarations.count(settlement);
        if declaration.membership() == Membership::Fixture {
            self.fixtures.count(settlement);
        }
        let surviving = declaration.surviving();
        self.surviving = Surviving::new(
            obligations_sum(self.surviving.undeclared(), surviving.undeclared()),
            obligations_sum(self.surviving.unproduced(), surviving.unproduced()),
        );
        match declaration.produced().refusal() {
            | Maybe::Present(refusal) => {
                let slot = self.refusals.slot(refusal.classify());
                *slot = one_more(*slot);
            },
            | Maybe::Absent(produced_refusal::Absent::Unrefused) => {},
        }
    }
}

impl fmt::Display for Tally
{
    /// Writes the summary: the ledger size first, then every count, the run's
    /// settlement and its seal, one per line.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes the ledger, declaration and fixture counts, both
    ///   residual channels, every refusal class, settlement and seal.
    /// - fails: propagates a refusing sink as `fmt::Error`.
    /// - panics: none.
    /// - executable: none — the formatter exposes neither emitted text nor
    ///   readable sink state. The witness observes selected declaration
    ///   identities, all distinct numeric payloads, state/class labels and a
    ///   refusing sink.
    ///
    /// # Errors
    /// Returns `fmt::Error` when the sink refuses a write.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a mixed source report separates visible fixtures and
    ///   unsettled names from an omitted settled helper. A tally with distinct
    ///   numeric payloads detects omitted or repeated counts; typed labels, row
    ///   order and exact sink refusals cover the remaining observations without
    ///   fixing sentences.
    /// - witness: `report::tests::reports_select_declarations_and_retain_summary_fields`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        writeln!(f, "ledger size: {}", self.ledger)?;
        writeln!(f, "declarations: {}", self.declarations)?;
        writeln!(f, "fixtures: {}", self.fixtures)?;
        writeln!(f, "surviving obligations: {}", self.surviving)?;
        writeln!(f, "refusals: {}", self.refusals)?;
        writeln!(f, "run: {}", self.settlement())?;
        write!(f, "seal: {}", self.seal())
    }
}

/// One settle run over a module: every declaration's report and the ledger
/// size.
///
/// # Specification
/// - requires: the producer owns the correspondence between counts and the
///   declarations or runs represented.
/// - ensures: Retains the supplied root, declaration sequence and checker
///   ledger count. Reports produced by `settle` preserve module order;
///   independently constructed reports retain the caller’s supplied
///   association.
/// - panics: none.
/// - executable: none — The record holds no original module or checker report;
///   `settle` establishes source correspondence and `tally` specifies
///   aggregation.
///
/// # Adequacy
/// - hypothesis: L3 — mixed source reports and exact saturation boundaries
///   distinguish categories, dropped fields and arithmetic errors;
///   settled/ledger boundary cases distinguish sealing from settlement. The
///   contributing source relationship is established at producer boundaries
///   rather than inferred from a record alone.
/// - witness: `settle::tests::a_lowering_refused_declaration_consumes_no_verdict`
/// - witness: `report::tests::the_tally_counts_every_declaration_once`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SettleReport<'source>
{
    /// The root the module was settled under.
    root: CorpusRoot,
    /// One report per declared name, in admission order.
    declarations: Vec<DeclarationReport<'source>>,
    /// The ledger size of the module's verdicts.
    ledger: ObligationCount,
}

impl<'source> SettleReport<'source>
{
    /// The report of a run under `root` over `declarations`, whose verdicts
    /// owe `ledger` obligations.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        root: CorpusRoot,
        declarations: Vec<DeclarationReport<'source>>,
        ledger: ObligationCount,
    ) -> Self
    {
        Self {
            root,
            declarations,
            ledger,
        }
    }

    /// The root the module was settled under.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn root(&self) -> CorpusRoot
    {
        self.root
    }

    /// One report per declared name, in admission order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn declarations(&self) -> &[DeclarationReport<'source>]
    {
        &self.declarations
    }

    /// The ledger size of the module's verdicts.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn ledger(&self) -> ObligationCount
    {
        self.ledger
    }

    /// The run's counts.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: every declaration counted once by settlement, every fixture
    ///   once more among the fixtures, every surviving obligation summed, every
    ///   produced refusal counted under its class, and the ledger size carried.
    /// - provides: the counts a driver gates on and prints.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — mixed source declarations with fixtures, two refusal
    ///   classes and unmatched obligations, plus empty and guarded reports.
    ///   Exact totals distinguish skipped or duplicated declarations, category
    ///   mixing, a lost ledger and conflating the two residual directions.
    /// - witness: `report::tests::the_tally_counts_every_declaration_once`
    /// - witness: `report::tests::the_run_is_settled_only_when_every_declaration_is`
    /// - witness: `report::tests::sealed_is_reported_never_gated`
    #[spec(
        ensures: |ret| {
    let settled = self
        .declarations
        .iter()
        .filter(|declaration| declaration.settlement() == Settlement::Settled)
        .count();
    let fixtures = self
        .declarations
        .iter()
        .filter(|declaration| declaration.membership() == Membership::Fixture)
        .count();
    let settled_fixtures = self
        .declarations
        .iter()
        .filter(|declaration| {
            declaration.membership() == Membership::Fixture
                && declaration.settlement() == Settlement::Settled
        })
        .count();
    let surviving = self
        .declarations
        .iter()
        .fold(
            (0_usize, 0_usize),
            |(undeclared, unproduced), declaration| {
                let residual = declaration.surviving();
                (
                    undeclared.saturating_add(usize::from(residual.undeclared())),
                    unproduced.saturating_add(usize::from(residual.unproduced())),
                )
            },
        );
    ret.ledger == self.ledger && usize::from(ret.declarations.settled) == settled
        && usize::from(ret.declarations.unsettled)
            == self.declarations.len().saturating_sub(settled)
        && usize::from(ret.fixtures.settled) == settled_fixtures
        && usize::from(ret.fixtures.unsettled)
            == fixtures.saturating_sub(settled_fixtures)
        && (
            usize::from(ret.surviving.undeclared()),
            usize::from(ret.surviving.unproduced()),
        ) == surviving
        && ClassCounts::CLASSES
            .into_iter()
            .all(|class| {
                usize::from(ret.refusals.count(class))
                    == self
                        .declarations
                        .iter()
                        .filter(|declaration| {
                            matches!(
                                declaration.produced().refusal(), Maybe::Present(refusal) if
                                refusal.classify() == class
                            )
                        })
                        .count()
            })
},
    )]
    #[inline]
    #[must_use]
    pub fn tally(&self) -> Tally
    {
        let mut tally = Tally {
            ledger: self.ledger,
            ..Tally::default()
        };
        for declaration in &self.declarations {
            tally.count(declaration);
        }
        tally
    }
}

impl fmt::Display for SettleReport<'_>
{
    /// Writes a line for every fixture and every unsettled declaration, in
    /// admission order, then the tally.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes each fixture and each unsettled declaration once in
    ///   stored order, omits settled unattributed rows, and includes the
    ///   complete tally.
    /// - fails: propagates a refusing sink as `fmt::Error`.
    /// - panics: none.
    /// - executable: none — the formatter exposes neither emitted text nor
    ///   readable sink state. The witness observes selected declaration
    ///   identities, all distinct numeric payloads, state/class labels and a
    ///   refusing sink.
    ///
    /// # Errors
    /// Returns `fmt::Error` when the sink refuses a write.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a mixed source report separates visible fixtures and
    ///   unsettled names from an omitted settled helper. A tally with distinct
    ///   numeric payloads detects omitted or repeated counts; typed labels, row
    ///   order and exact sink refusals cover the remaining observations without
    ///   fixing sentences.
    /// - witness: `report::tests::reports_select_declarations_and_retain_summary_fields`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        for declaration in &self.declarations {
            if declaration.membership() == Membership::Fixture
                || declaration.settlement() == Settlement::Unsettled
            {
                writeln!(f, "{declaration}")?;
            }
        }
        fmt::Display::fmt(&self.tally(), f)
    }
}

/// `count` and one more, saturating.
///
/// # Specification
/// - requires: nothing.
/// - ensures: returns the successor unless the count is maximal, in which case
///   it remains maximal.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — counting a declaration at the predecessor of the maximum
///   and at the maximum, with the other channel held distinct. Exact results
///   distinguish off-by-one saturation and wrapping.
/// - witness: `report::tests::saturating_tallies_preserve_every_count_channel`
#[spec(
    ensures: |ret| usize::from(ret) == usize::from(count).saturating_add(1_usize),
)]
fn one_more(count: DeclarationCount) -> DeclarationCount
{
    DeclarationCount::from(usize::from(count).saturating_add(1_usize))
}

/// The saturating sum of two declaration counts.
///
/// # Specification
/// - requires: nothing.
/// - ensures: returns the exact sum when representable and the maximal count
///   otherwise.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — zero, ordinary, exactly maximal and overflowing sums
///   through independent tally channels. Exact boundary results distinguish
///   wrapping, dropped operands and premature saturation.
/// - witness: `report::tests::saturating_tallies_preserve_every_count_channel`
/// - witness: `report::tests::absorbing_a_tally_sums_every_count`
#[spec(
    ensures: |ret| {
    usize::from(ret) == usize::from(left).saturating_add(usize::from(right))
},
)]
fn declarations_sum(
    left: DeclarationCount,
    right: DeclarationCount,
) -> DeclarationCount
{
    DeclarationCount::from(usize::from(left).saturating_add(usize::from(right)))
}

/// The saturating sum of two obligation counts.
///
/// # Specification
/// - requires: nothing.
/// - ensures: returns the exact sum when representable and the maximal count
///   otherwise.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — zero, ordinary, exactly maximal and overflowing sums
///   through independent tally channels. Exact boundary results distinguish
///   wrapping, dropped operands and premature saturation.
/// - witness: `report::tests::saturating_tallies_preserve_every_count_channel`
/// - witness: `report::tests::absorbing_a_tally_sums_every_count`
#[spec(
    ensures: |ret| {
    usize::from(ret) == usize::from(left).saturating_add(usize::from(right))
},
)]
fn obligations_sum(
    left: ObligationCount,
    right: ObligationCount,
) -> ObligationCount
{
    ObligationCount::from(usize::from(left).saturating_add(usize::from(right)))
}

#[cfg(test)]
mod tests
{
    use alloc::string::ToString as _;
    use alloc::vec::Vec;
    use core::fmt;

    use gandr_core_checker::ObligationCount;
    use gandr_core_term::FailureClass;
    use gandr_surface_lowering::DeclarationCount;
    use gandr_surface_syntax::SourceText;

    use super::ClassCounts;
    use super::Seal;
    use super::SettleCounts;
    use super::Tally;
    use crate::fixture::RefusingWriter;
    use crate::fixture::settled;
    use crate::root::CorpusRoot;
    use crate::settle::Settlement;
    use crate::settle::Surviving;

    #[test]
    fn the_run_is_settled_only_when_every_declaration_is()
    {
        let rows = [
            (
                CorpusRoot::Strict,
                r#"def a : Integer ;"#,
                Settlement::Unsettled,
            ),
            (
                CorpusRoot::Strict,
                r#"@[ owes(1) ] def a : Integer ;"#,
                Settlement::Unsettled,
            ),
            (
                CorpusRoot::Strict,
                r#"def a : Integer ; def a = 3 ; def b = a ;"#,
                Settlement::Settled,
            ),
            (
                CorpusRoot::Fixture,
                r#"def a = 3 ; def b : Integer ;"#,
                Settlement::Unsettled,
            ),
            (CorpusRoot::Fixture, r#""#, Settlement::Settled),
        ];

        for (root, source, settlement) in rows {
            let report = settled(root, SourceText::from(source));
            assert_eq!(
                report.tally().settlement(),
                settlement,
                "`{source}` under the {root} root settles the run as pinned"
            );
        }
    }

    #[test]
    fn sealed_is_reported_never_gated()
    {
        let rows = [
            (
                r#"@[ owes(1) ] def a : Integer ;"#,
                Settlement::Settled,
                Seal::Unsealed,
            ),
            (
                r#"def a : Integer ;"#,
                Settlement::Unsettled,
                Seal::Unsealed,
            ),
            (
                r#"@[ owes(1) ] def a = 3 ;"#,
                Settlement::Unsettled,
                Seal::Unsealed,
            ),
            (r#"def a = 3 ;"#, Settlement::Settled, Seal::Sealed),
        ];

        for (source, settlement, seal) in rows {
            let tally = settled(CorpusRoot::Fixture, SourceText::from(source)).tally();
            assert_eq!(
                (tally.settlement(), tally.seal()),
                (settlement, seal),
                "`{source}` is pinned settled or not, sealed or not"
            );
        }
    }

    #[test]
    fn saturating_tallies_preserve_every_count_channel()
    {
        let count = DeclarationCount::from;
        let owed = ObligationCount::from;
        let mut counts = SettleCounts {
            settled: count(usize::MAX.saturating_sub(1_usize)),
            unsettled: count(37_usize),
        };
        counts.count(Settlement::Settled);
        assert_eq!(
            (
                usize::from(counts.settled()),
                usize::from(counts.unsettled())
            ),
            (usize::MAX, 37_usize)
        );
        counts.count(Settlement::Settled);
        counts.count(Settlement::Unsettled);
        assert_eq!(
            (
                usize::from(counts.settled()),
                usize::from(counts.unsettled())
            ),
            (usize::MAX, 38_usize)
        );
        let mut total = Tally {
            declarations: SettleCounts {
                settled: count(usize::MAX),
                unsettled: count(11_usize),
            },
            fixtures: SettleCounts {
                settled: count(usize::MAX.saturating_sub(1_usize)),
                unsettled: count(0_usize),
            },
            ledger: owed(usize::MAX.saturating_sub(1_usize)),
            surviving: Surviving::new(owed(17_usize), owed(usize::MAX)),
            refusals: ClassCounts {
                user_absence: count(0_usize),
                unrepresentable: count(17_usize),
                malformed_source: count(29_usize),
                engine_fault: count(usize::MAX.saturating_sub(1_usize)),
            },
        };
        let other = Tally {
            declarations: SettleCounts {
                settled: count(43_usize),
                unsettled: count(13_usize),
            },
            fixtures: SettleCounts {
                settled: count(1_usize),
                unsettled: count(7_usize),
            },
            ledger: owed(1_usize),
            surviving: Surviving::new(owed(19_usize), owed(1_usize)),
            refusals: ClassCounts {
                user_absence: count(3_usize),
                unrepresentable: count(5_usize),
                malformed_source: count(31_usize),
                engine_fault: count(2_usize),
            },
        };
        total.absorb(&other);
        assert_eq!(
            (
                usize::from(total.declarations().settled()),
                usize::from(total.declarations().unsettled())
            ),
            (usize::MAX, 24_usize)
        );
        assert_eq!(
            (
                usize::from(total.fixtures().settled()),
                usize::from(total.fixtures().unsettled())
            ),
            (usize::MAX, 7_usize)
        );
        assert_eq!(usize::from(total.ledger()), usize::MAX);
        assert_eq!(
            (
                usize::from(total.surviving().undeclared()),
                usize::from(total.surviving().unproduced())
            ),
            (36_usize, usize::MAX)
        );
        assert_eq!(
            [
                FailureClass::UserAbsence,
                FailureClass::Unrepresentable,
                FailureClass::MalformedSource,
                FailureClass::EngineFault
            ]
            .map(|class| usize::from(total.refusals().count(class))),
            [3_usize, 22_usize, 60_usize, usize::MAX]
        );
        let before = total;
        total.absorb(&Tally::default());
        assert_eq!(
            total, before,
            "an empty tally changes no count, including saturated ones"
        );
    }

    #[test]
    fn reports_select_declarations_and_retain_summary_fields()
    {
        let report = settled(
            CorpusRoot::Fixture,
            SourceText::from(
                r#"def hidden_record = 3 ;
@[ owes(1) ] def fixture_hole : Integer ;
def plain_hole : Integer ;
@[ refuses("UnresolvedName") ] def fixture_refusal = missing ;"#,
            ),
        );
        let rendered = report.to_string();
        assert!(!rendered.contains("hidden_record"));
        assert!(rendered.contains(&report.tally().to_string()));
        let mut previous = None;
        for name in ["fixture_hole", "plain_hole", "fixture_refusal"] {
            assert_eq!(rendered.matches(name).count(), 1_usize);
            let position = rendered
                .find(name)
                .expect("the selected declaration has a row");
            assert!(previous.is_none_or(|before| before < position));
            previous = Some(position);
        }
        let count = DeclarationCount::from;
        let owed = ObligationCount::from;
        let tally = Tally {
            declarations: SettleCounts {
                settled: count(1009_usize),
                unsettled: count(1013_usize),
            },
            fixtures: SettleCounts {
                settled: count(101_usize),
                unsettled: count(103_usize),
            },
            ledger: owed(149_usize),
            surviving: Surviving::new(owed(109_usize), owed(113_usize)),
            refusals: ClassCounts {
                user_absence: count(127_usize),
                unrepresentable: count(131_usize),
                malformed_source: count(137_usize),
                engine_fault: count(139_usize),
            },
        };
        let rendered = tally.to_string();
        let mut numbers: Vec<usize> = rendered
            .split(|character: char| !character.is_ascii_digit())
            .filter(|text| !text.is_empty())
            .map(|text| text.parse().expect("a printed count is decimal"))
            .collect();
        numbers.sort_unstable();
        assert_eq!(numbers, [
            101_usize, 103_usize, 109_usize, 113_usize, 127_usize, 131_usize, 137_usize, 139_usize,
            149_usize, 1009_usize, 1013_usize
        ]);
        assert!(rendered.contains(&tally.settlement().to_string()));
        assert!(rendered.contains(&tally.seal().to_string()));
        for class in [
            FailureClass::UserAbsence,
            FailureClass::Unrepresentable,
            FailureClass::MalformedSource,
            FailureClass::EngineFault,
        ] {
            assert!(rendered.contains(&class.to_string()));
        }
        assert_ne!(Seal::Sealed.to_string(), Seal::Unsealed.to_string());
        let formats: [&dyn fmt::Display; 7_usize] = [
            &Seal::Sealed,
            &Seal::Unsealed,
            &tally.declarations,
            &tally.refusals,
            &tally,
            &report,
            &tally.fixtures,
        ];
        for value in formats {
            assert_eq!(
                fmt::Write::write_fmt(&mut RefusingWriter, format_args!("{value}")),
                Err(fmt::Error)
            );
        }
    }

    #[test]
    fn the_tally_counts_every_declaration_once()
    {
        let source = SourceText::from(
            r#"def helper = 3 ;
@[ owes(2) ] def owed : Integer ;
@[ refuses("OutOfFragment") ] def lazy : -F Integer & -F Integer ;
@[ checks ] def wrong : Integer ; def wrong = "text" ;"#,
        );
        let tally = settled(CorpusRoot::Fixture, source).tally();

        assert_eq!(
            (
                usize::from(tally.declarations().settled()),
                usize::from(tally.declarations().unsettled())
            ),
            (2_usize, 2_usize),
            "the helper and the refused lazy product settle; the owed and the wrong do not"
        );
        assert_eq!(
            (
                usize::from(tally.fixtures().settled()),
                usize::from(tally.fixtures().unsettled())
            ),
            (1_usize, 2_usize),
            "the helper is no fixture"
        );
        assert_eq!(
            tally.surviving(),
            Surviving::new(
                ObligationCount::from(0_usize),
                ObligationCount::from(1_usize)
            ),
            "one declared obligation is never produced"
        );
        assert_eq!(usize::from(tally.ledger()), 1_usize, "one hole is owed");
        let refusals = tally.refusals();
        assert_eq!(
            [
                FailureClass::UserAbsence,
                FailureClass::Unrepresentable,
                FailureClass::MalformedSource,
                FailureClass::EngineFault,
            ]
            .map(|class| usize::from(refusals.count(class))),
            [0_usize, 1_usize, 1_usize, 0_usize],
            "each refusal is counted under its own class"
        );
    }

    #[test]
    fn absorbing_a_tally_sums_every_count()
    {
        let mut total = settled(
            CorpusRoot::Fixture,
            SourceText::from(r#"@[ owes(1) ] def a : Integer ; def b = c ;"#),
        )
        .tally();
        let other = settled(
            CorpusRoot::Fixture,
            SourceText::from(r#"@[ owes(1) ] def a = 3 ; @[ refuses("OutOfFragment") ] def b : -F Integer & -F Integer ;"#),
        )
        .tally();
        total.absorb(&other);

        assert_eq!(
            (
                usize::from(total.declarations().settled()),
                usize::from(total.declarations().unsettled()),
                usize::from(total.fixtures().settled()),
                usize::from(total.fixtures().unsettled()),
            ),
            (2_usize, 2_usize, 2_usize, 1_usize),
            "the settlement counts sum"
        );
        assert_eq!(
            (
                usize::from(total.ledger()),
                usize::from(total.surviving().undeclared()),
                usize::from(total.surviving().unproduced()),
            ),
            (1_usize, 0_usize, 1_usize),
            "the ledger and the surviving obligations sum"
        );
        assert_eq!(
            (
                usize::from(total.refusals().count(FailureClass::MalformedSource)),
                usize::from(total.refusals().count(FailureClass::Unrepresentable)),
            ),
            (1_usize, 1_usize),
            "the refusal counts sum by class"
        );
        assert_eq!(
            total.settlement(),
            Settlement::Unsettled,
            "an unsettled part unsettles the whole"
        );
    }
}
