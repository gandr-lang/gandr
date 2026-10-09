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
    /// trivial.
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
    /// trivial.
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
    /// trivial.
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
    /// trivial.
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
    const CLASSES: [FailureClass; 4_usize] = [
        FailureClass::UserAbsence,
        FailureClass::Unrepresentable,
        FailureClass::MalformedSource,
        FailureClass::EngineFault,
    ];

    /// The refused declarations of `class`.
    ///
    /// # Specification
    /// trivial.
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
    /// trivial.
    const fn slot(
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
    /// trivial.
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
    /// trivial.
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
    /// - hypothesis: L3 — a settled and an unsettled tally are absorbed and
    ///   every count is asserted at the sum, so a dropped or swapped field
    ///   breaks one.
    /// - witness: `report::tests::absorbing_a_tally_sums_every_count`
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
    /// - hypothesis: L3 — the strict root's negative rows are each asserted
    ///   unsettled at the run level beside a settled control, and an owed run
    ///   under the fixture root is asserted settled.
    /// - witness: `report::tests::the_run_is_settled_only_when_every_declaration_is`
    /// - witness: `report::tests::sealed_is_reported_never_gated`
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
    /// - hypothesis: L3 — a settled run owing one is asserted unsealed and
    ///   settled, an unsettled run owing nothing unsealed, and a settled run
    ///   owing nothing sealed.
    /// - witness: `report::tests::sealed_is_reported_never_gated`
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
    /// trivial.
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
    /// trivial.
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
    /// - hypothesis: L3 — a module mixing settled and unsettled fixtures, an
    ///   unattributed declaration, refusals of two classes and a surviving
    ///   obligation is asserted at every count.
    /// - witness: `report::tests::the_tally_counts_every_declaration_once`
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
    /// trivial.
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
/// trivial.
fn one_more(count: DeclarationCount) -> DeclarationCount
{
    DeclarationCount::from(usize::from(count).saturating_add(1_usize))
}

/// The saturating sum of two declaration counts.
///
/// # Specification
/// trivial.
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
/// trivial.
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

    use gandr_core_checker::ObligationCount;
    use gandr_core_term::FailureClass;
    use gandr_surface_syntax::SourceText;

    use super::Seal;
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
    fn the_ledger_size_is_printed_settled_or_not()
    {
        let rows = [
            (
                CorpusRoot::Fixture,
                r#"@[ owes(1) ] def a : Integer ;"#,
                "run: settled",
            ),
            (CorpusRoot::Strict, r#"def a : Integer ;"#, "run: unsettled"),
        ];

        for (root, source, run) in rows {
            let rendered = settled(root, SourceText::from(source)).to_string();
            let mut lines = rendered.lines();
            assert_eq!(
                lines.find(|line| line.starts_with("ledger size: ")),
                Some("ledger size: 1"),
                "`{source}` prints its ledger size"
            );
            assert!(
                rendered.lines().any(|line| line == run),
                "`{source}` prints `{run}`: {rendered}"
            );
        }
    }

    #[test]
    fn every_fixture_and_every_unsettled_declaration_has_a_line()
    {
        let source = SourceText::from(
            r#"def helper = 3 ;
@[ owes(1) ] def owed : Integer ;
def silent : Integer ;
@[ refuses("UnresolvedName") ] def broken = missing ;"#,
        );
        let rendered = settled(CorpusRoot::Fixture, source).to_string();
        let mut lines = rendered.lines();

        assert_eq!(
            lines.next(),
            Some("settled `owed` at 17..50: states checks owing 1; produced checks owing 1"),
            "a settled fixture has a line"
        );
        assert_eq!(
            lines.next(),
            Some(
                "unsettled `silent` at 51..73: states checks owing 0; produced checks owing 1; surviving obligations: 1 undeclared, 0 unproduced"
            ),
            "an unsettled declaration without an expectation has a line"
        );
        assert_eq!(
            lines.next(),
            Some(
                "settled `broken` at 74..127: states refuses UnresolvedName; produced refuses UnresolvedName (malformed source)"
            ),
            "a refused fixture names the refusal and its class"
        );
        assert_eq!(
            lines.collect::<alloc::vec::Vec<_>>(),
            [
                "ledger size: 2",
                "declarations: 3 settled, 1 unsettled",
                "fixtures: 2 settled, 0 unsettled",
                "surviving obligations: 1 undeclared, 0 unproduced",
                "refusals: 0 user absence, 0 unrepresentable, 1 malformed source, 0 engine fault",
                "run: unsettled",
                "seal: unsealed",
            ],
            "the settled helper is only counted, and the tally follows"
        );
    }

    #[test]
    fn the_tally_counts_every_declaration_once()
    {
        let source = SourceText::from(
            r#"def helper = 3 ;
@[ owes(2) ] def owed : Integer ;
@[ refuses("OutOfFragment") ] def pair : Integer * Integer ;
@[ checks ] def wrong : Integer ; def wrong = "text" ;"#,
        );
        let tally = settled(CorpusRoot::Fixture, source).tally();

        assert_eq!(
            (
                usize::from(tally.declarations().settled()),
                usize::from(tally.declarations().unsettled())
            ),
            (2_usize, 2_usize),
            "the helper and the refused pair settle; the owed and the wrong do not"
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
            SourceText::from(r#"@[ owes(1) ] def a = 3 ; @[ refuses("OutOfFragment") ] def b : Integer * Integer ;"#),
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
