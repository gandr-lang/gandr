//! The exact distribution of a run's outcomes over every answer of its draws:
//! what a `distributes` expectation states, what the runs of its declaration
//! produce, and the one spelling both are compared in.
//!
//! A run that draws is deterministic once its draws have answers. So the
//! runner runs a declaration once for each sequence of answers, depth first
//! from the start of the run, and reports the outcome of each path with the
//! bits its draws take. A path that draws `n₁, …, n_j` bits weighs
//! `2^-(n₁ + … + n_j)`, and the weights of every path sum to one.
//! [`distributed`] sums them by outcome, one entry for each distinct outcome,
//! into a [`Distribution`] of `theory-probability`.
//!
//! Each side is spelled in the canonical form of its distribution: each point
//! a quoted text that writes its weight, a space and its outcome, in the order
//! of the support. Two distributions are equal exactly when their forms are
//! equal, so the comparison is the equality of the two spellings. A path that
//! draws past [`Bits::QUOTA`] gives no distribution: its spelling names
//! `PastQuota`, which no stated distribution spells. A draw that the exact
//! model declines gives none either: its spelling names `Unanswered` and the
//! task or the world that performs the draw.
//!
//! # References
//!
//! - `vault:01a1aa2d-a69c-7030-91e0-337d68d88151` — anchor: §
//!   presented-spaces-quantities-probability. The exact discrete semantics of a
//!   probability effect is the first consumer of `theory-probability`.

use alloc::collections::BTreeMap;
use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;
use core::fmt;
use core::fmt::Write as _;

use anodized::spec;
use gandr_core_term::CoreArena;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::StringLiteral;
use gandr_surface_lowering::AttributeEntry;
use gandr_surface_lowering::texts;
use gandr_theory_cellular_sheaves::Integer;
use gandr_theory_cellular_sheaves::Rational;
use gandr_theory_probability::Distribution;
use quenchant_shape::shape::Maybe;

use crate::expectation::ExpectationFault;
use crate::expectation::Outcome;
use crate::expectation::Stated;
use crate::run::RunSpelling;
use crate::run::Runner;

/// A count of fair bits: the width of one draw, or the sum of the widths of
/// the draws of one path.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Bits(u32);

impl Bits
{
    /// The most bits one path may draw, so a declaration runs at most
    /// `2^16` times.
    pub const QUOTA: Self = Self(16);
}

impl From<u32> for Bits
{
    /// The count of `bits`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bits: u32) -> Self
    {
        Self(bits)
    }
}

impl From<Bits> for u32
{
    /// The number the count holds.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bits: Bits) -> Self
    {
        bits.0
    }
}

impl fmt::Display for Bits
{
    /// Writes the count in decimal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(f, "{}", self.0)
    }
}

/// A path that draws more bits than the quota: the declaration gives no
/// distribution, never a smaller one.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct PastQuota
{
    /// The bits the path draws, the draw that passes the quota included.
    pub drawn: Bits,
}

/// What performs a draw: the run of the declaration, a task it forks, or a
/// world it migrates a body to.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Performer
{
    /// The run itself, outside any task or world it names.
    Run,
    /// The task a fork starts, by the name the fork gives its channel.
    Task(String),
    /// The world a `migrate` runs its body at, by its declared name.
    World(String),
}

impl fmt::Display for Performer
{
    /// Writes the performer as a noun phrase: `the run`, ``the task `x` `` or
    /// ``the world `x` ``.
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
            Self::Run => f.write_str("the run"),
            Self::Task(ref name) => write!(f, "the task `{name}`"),
            Self::World(ref name) => write!(f, "the world `{name}`"),
        }
    }
}

/// Why the runs of a declaration give no distribution.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Undistributed
{
    /// A path draws past the quota.
    PastQuota(PastQuota),
    /// The exact model declines a draw of one path: what performs the draw,
    /// and the cause of the decline.
    Unanswered
    {
        /// What performs the declined draw.
        performer: Performer,
        /// The cause of the decline, as one clause.
        cause: String,
    },
}

impl From<PastQuota> for Undistributed
{
    /// The path past the quota.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(past: PastQuota) -> Self
    {
        Self::PastQuota(past)
    }
}

/// The spelling of the distribution the runs of the declaration at
/// `constant` give, one run for each sequence of answers to its draws.
///
/// # Specification
/// - requires: `constant` is a declaration of the module being settled that the
///   checker accepted, and that states a distribution.
/// - ensures: [`spelled`] of the distribution whose weight at each outcome is
///   the sum of `2^-bits` over the paths that end in it; a spelling that names
///   `PastQuota` when a path draws past [`Bits::QUOTA`], and one that names
///   `Unanswered` with the performer when the exact model declines a draw.
/// - fails: never; a path with no distribution is an outcome of its own,
///   spelled by name.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — two draws of one bit summed give three outcomes at one
///   quarter, one half and one quarter; a path past the quota and a declined
///   draw of a task are each spelled by name; a run with no draw is one point.
/// - witness: `distribution::tests::the_paths_sum_by_outcome_into_one_distribution`
/// - witness: `distribution::tests::a_path_past_the_quota_gives_no_distribution`
/// - witness: `tests::corpus::a_declined_draw_names_its_task_or_world_5712`
#[inline]
#[spec(ensures: |ref ret| ["\"", "PastQuota: ", "Unanswered: ", "no distribution: ", "a path of "].iter().any(|&head| ret.as_ref().starts_with(head)))]
pub fn distributed<Run>(
    runner: &mut Run,
    constant: ConstantIndex,
) -> RunSpelling
where
    Run: Runner + ?Sized,
{
    let mut weights: BTreeMap<RunSpelling, Rational> = BTreeMap::new();
    let mut fault: Option<String> = None;
    let walked = runner.run_distributed(constant, Bits::QUOTA, &mut |outcome, bits| {
        let summed = share(bits).and_then(|weight| {
            weights
                .get(&outcome)
                .map_or(Some(weight), |&held| held.plus(weight).ok())
        });
        match summed {
            Some(sum) => {
                let _held = weights.insert(outcome, sum);
            },
            None => fault = Some(format!("a path of {bits} bits weighs past the integers")),
        }
    });
    match walked {
        Ok(()) => {},
        Err(Undistributed::PastQuota(PastQuota { drawn })) => {
            return RunSpelling::from(format!(
                "PastQuota: a path draws {drawn} bits, past the quota of {}",
                Bits::QUOTA
            ));
        },
        Err(Undistributed::Unanswered { performer, cause }) => {
            return RunSpelling::from(format!(
                "Unanswered: the exact model answers no draw of {performer}: {cause}"
            ));
        },
    }
    if let Some(fault) = fault {
        return RunSpelling::from(fault);
    }
    match Distribution::new(weights) {
        Ok(distribution) => spelled(&distribution),
        Err(refused) => RunSpelling::from(format!("no distribution: {refused}")),
    }
}

/// The weight `2^-bits` of a path that draws `bits` bits.
///
/// # Specification
/// - ensures: one over two to the `bits`, present while that fits the 128-bit
///   integers.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`distributed`].
/// - witness: `distribution::tests::the_paths_sum_by_outcome_into_one_distribution`
#[spec(ensures: |ret| ret.is_none_or(|weight| i128::from(weight.numerator()) == 1))]
fn share(bits: Bits) -> Option<Rational>
{
    let power = 1_i128.checked_shl(bits.0)?;
    Rational::new(Integer::from(1_i128), Integer::from(power)).ok()
}

/// The canonical spelling of `distribution`: each point, in the order of its
/// support, a quoted text writing its weight, a space and its outcome, the
/// points apart by `, `.
///
/// # Specification
/// - ensures: one quoted text for each point, in the order of the support.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the same points written in two orders spell one text, and
///   an outcome that holds a quote is escaped.
/// - witness: `distribution::tests::a_stated_distribution_spells_its_canonical_form`
#[spec(ensures: |ret| ret.as_ref().matches('"').count() >= distribution.points().len().saturating_mul(2))]
fn spelled(distribution: &Distribution<RunSpelling>) -> RunSpelling
{
    let mut written = String::new();
    for (place, &(ref outcome, weight)) in distribution.points().iter().enumerate() {
        let joint = if place == 0 { "" } else { ", " };
        // Writing to a `String` never fails.
        let _written = write!(
            written,
            "{joint}\"{weight} {}\"",
            outcome.as_ref().escape_debug()
        );
    }
    RunSpelling::from(written)
}

/// What a `distributes` entry states: the canonical spelling of the
/// distribution its texts write, each a weight, a space and an outcome.
///
/// # Specification
/// - requires: `entry` is a `distributes` entry of the declaration being read.
/// - ensures: [`Outcome::Distributes`] of the canonical spelling when each text
///   writes a positive rational weight, a space and an outcome, and the weights
///   sum to one; otherwise [`ExpectationFault::UnwrittenDistribution`] at the
///   entry's span.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a distribution written out of order and with an outcome
///   split in two spells the canonical form; a text with no weight, a weight of
///   zero and weights that do not sum to one are each malformed.
/// - witness: `distribution::tests::a_stated_distribution_spells_its_canonical_form`
/// - witness: `distribution::tests::a_text_that_writes_no_distribution_is_malformed`
#[spec(ensures: |ref ret| match *ret {
    Stated::Verdict(Outcome::Distributes(_)) => true,
    Stated::Malformed(fault) => fault == ExpectationFault::UnwrittenDistribution { span: entry.span() },
    Stated::Verdict(_) => false,
})]
pub fn stated(
    entry: &AttributeEntry,
    arena: &CoreArena,
) -> Stated
{
    let unwritten =
        Stated::Malformed(ExpectationFault::UnwrittenDistribution { span: entry.span() });
    let Maybe::Present(value) = entry.payload()
    else {
        return unwritten;
    };
    let Maybe::Present(written) = texts(arena, value)
    else {
        return unwritten;
    };
    let mut points = Vec::with_capacity(written.len());
    for text in written {
        let Some(weighed) = point(text)
        else {
            return unwritten;
        };
        points.push(weighed);
    }
    Distribution::new(points).map_or(unwritten, |distribution| {
        Stated::Verdict(Outcome::Distributes(spelled(&distribution)))
    })
}

/// The point a `distributes` text writes: the outcome after its first space,
/// weighed by the rational before it, `n/d`, or `n` alone for a denominator
/// of one.
///
/// # Specification
/// - ensures: the outcome and the rational of the two decimal integers, present
///   when the text holds a space, both integers parse and the denominator is
///   not zero.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`stated`].
/// - witness: `distribution::tests::a_text_that_writes_no_distribution_is_malformed`
#[spec(ensures: |ref ret| ret.as_ref().is_none_or(|&(ref outcome, _)| text.as_ref().ends_with(outcome.as_ref())))]
fn point(text: &StringLiteral) -> Option<(RunSpelling, Rational)>
{
    let (weight, outcome) = text.as_ref().split_once(' ')?;
    let (numerator, denominator) = weight.split_once('/').unwrap_or((weight, "1"));
    let numerator: i128 = numerator.parse().ok()?;
    let denominator: i128 = denominator.parse().ok()?;
    let weight = Rational::new(Integer::from(numerator), Integer::from(denominator)).ok()?;
    Some((RunSpelling::from(String::from(outcome)), weight))
}

#[cfg(test)]
mod tests
{
    use alloc::borrow::ToOwned as _;
    use alloc::string::String;
    use alloc::vec::Vec;

    use gandr_core_term::CoreArena;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::Literal;
    use gandr_kernel_term::StringLiteral;
    use gandr_surface_lowering::AttributeEntry;
    use gandr_surface_lowering::AttributeSchema;
    use gandr_surface_lowering::SurfaceName;
    use gandr_surface_syntax::ByteOffset;
    use gandr_surface_syntax::ByteSpan;
    use quenchant_shape::shape::Maybe;

    use super::Bits;
    use super::PastQuota;
    use super::Undistributed;
    use super::distributed;
    use super::stated;
    use crate::expectation::ExpectationFault;
    use crate::expectation::Outcome;
    use crate::expectation::Stated;
    use crate::fixture::registered;
    use crate::fixture::span;
    use crate::run::Channel;
    use crate::run::RunSpelling;
    use crate::run::Runner;
    use crate::run::TracedRun;

    /// A runner whose declaration takes each path of `paths`: an outcome
    /// with the bits its draws take, or why the paths give no distribution.
    #[repr(transparent)]
    struct Paths(Result<Vec<(&'static str, Bits)>, Undistributed>);

    impl Runner for Paths
    {
        /// Spells nothing: only distributions are asked.
        ///
        /// # Specification
        /// trivial.
        fn run(
            &mut self,
            _constant: ConstantIndex,
        ) -> RunSpelling
        {
            RunSpelling::from(String::new())
        }

        /// Spells nothing.
        ///
        /// # Specification
        /// trivial.
        fn run_refused(
            &mut self,
            _constant: ConstantIndex,
        ) -> RunSpelling
        {
            RunSpelling::from(String::new())
        }

        /// Spells nothing.
        ///
        /// # Specification
        /// trivial.
        fn decompose(
            &mut self,
            _constant: ConstantIndex,
        ) -> RunSpelling
        {
            RunSpelling::from(String::new())
        }

        /// Forks no channel.
        ///
        /// # Specification
        /// trivial.
        fn run_traced(
            &mut self,
            _constant: ConstantIndex,
        ) -> TracedRun
        {
            TracedRun {
                run: RunSpelling::from(String::new()),
                channels: Vec::<Channel>::new(),
            }
        }

        /// Spells nothing.
        ///
        /// # Specification
        /// trivial.
        fn reads(
            &mut self,
            _constant: ConstantIndex,
        ) -> RunSpelling
        {
            RunSpelling::from(String::new())
        }

        /// Reports each path.
        ///
        /// # Specification
        /// trivial.
        fn run_distributed(
            &mut self,
            _constant: ConstantIndex,
            _quota: Bits,
            path: &mut dyn FnMut(RunSpelling, Bits),
        ) -> Result<(), Undistributed>
        {
            let paths = self.0.clone()?;
            for (outcome, bits) in paths {
                path(RunSpelling::from(String::from(outcome)), bits);
            }
            Ok(())
        }
    }

    /// The four paths of two draws of one bit summed reach three outcomes,
    /// the middle one twice: one quarter, one half and one quarter. A run
    /// with no draw is one point of weight one.
    #[test]
    fn the_paths_sum_by_outcome_into_one_distribution()
    {
        let two = Bits::from(2);
        let mut summed = Paths(Ok(Vec::from([
            ("0", two),
            ("1", two),
            ("1", two),
            ("2", two),
        ])));
        assert_eq!(
            distributed(&mut summed, ConstantIndex::from(0_usize)).as_ref(),
            r#""1/4 0", "1/2 1", "1/4 2""#
        );
        let mut fixed = |_constant: ConstantIndex| RunSpelling::from(String::from("unit"));
        assert_eq!(
            distributed(&mut fixed, ConstantIndex::from(0_usize)).as_ref(),
            r#""1 unit""#
        );
    }

    /// A path that draws 17 bits is spelled by `PastQuota`, never cut into
    /// a smaller distribution.
    #[test]
    fn a_path_past_the_quota_gives_no_distribution()
    {
        let mut past = Paths(Err(Undistributed::PastQuota(PastQuota {
            drawn: Bits::from(17),
        })));
        assert_eq!(
            distributed(&mut past, ConstantIndex::from(0_usize)).as_ref(),
            "PastQuota: a path draws 17 bits, past the quota of 16"
        );
    }

    /// The `distributes` entry whose payload is `texts`, read out of
    /// `arena`, over the bytes `span`.
    ///
    /// # Specification
    /// trivial.
    fn entry(
        arena: &mut CoreArena,
        texts: &[StringLiteral],
        covered: ByteSpan,
    ) -> AttributeEntry
    {
        let values: Vec<_> = texts
            .iter()
            .map(|text| arena.value_literal(Literal::Text(text.clone())))
            .collect();
        let payload = match *values.as_slice() {
            [only] => only,
            _ => arena.value_tuple(&values),
        };
        AttributeEntry::new(
            registered(SurfaceName::from("distributes")),
            AttributeSchema::Texts,
            Maybe::Present(payload),
            covered,
        )
    }

    /// A distribution written out of order, with one outcome split in two
    /// and an outcome that holds a quote, spells one canonical form.
    #[test]
    fn a_stated_distribution_spells_its_canonical_form()
    {
        let mut arena = CoreArena::new();
        let literals = |written: &[&str]| -> Vec<StringLiteral> {
            written
                .iter()
                .map(|&text| StringLiteral::new(text.to_owned()))
                .collect()
        };
        let covered = span(ByteOffset::from(0_usize), ByteOffset::from(9_usize));
        let written = entry(
            &mut arena,
            &literals(&["1/4 2", "1/8 1", "1/4 0", "3/8 1"]),
            covered,
        );
        let reordered = entry(&mut arena, &literals(&["1/4 0", "1/2 1", "1/4 2"]), covered);
        let canonical = Stated::Verdict(Outcome::Distributes(RunSpelling::from(String::from(
            r#""1/4 0", "1/2 1", "1/4 2""#,
        ))));
        assert_eq!(stated(&written, &arena), canonical);
        assert_eq!(stated(&reordered, &arena), canonical);
        let quoted = entry(&mut arena, &literals(&["1 \"yes\""]), covered);
        assert_eq!(
            stated(&quoted, &arena),
            Stated::Verdict(Outcome::Distributes(RunSpelling::from(String::from(
                r#""1 \"yes\"""#
            ))))
        );
    }

    /// A text with no weight, a weight of zero, a weight that is no number,
    /// and weights that do not sum to one each state no distribution.
    #[test]
    fn a_text_that_writes_no_distribution_is_malformed()
    {
        let mut arena = CoreArena::new();
        let literals = |written: &[&str]| -> Vec<StringLiteral> {
            written
                .iter()
                .map(|&text| StringLiteral::new(text.to_owned()))
                .collect()
        };
        let covered = span(ByteOffset::from(3_usize), ByteOffset::from(7_usize));
        let malformed =
            Stated::Malformed(ExpectationFault::UnwrittenDistribution { span: covered });
        for texts in [
            &["1/2"][..],
            &["0 1", "1 2"][..],
            &["half 1", "1/2 2"][..],
            &["1/2 1", "1/4 2"][..],
            &["1/0 1"][..],
        ] {
            let written = entry(&mut arena, &literals(texts), covered);
            assert_eq!(stated(&written, &arena), malformed, "{texts:?}");
        }
    }
}
