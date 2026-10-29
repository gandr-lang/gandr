//! Coverage as Codecov states it: covered lines over measured lines, in
//! hundredths of a percent rounded down, and the points one coverage moved
//! from another.

use core::cmp::Ordering;
use core::fmt;
use core::str::FromStr;

use anodized::spec;
use quenchant_shape::shape::Maybe;
use serde::Deserialize;

use crate::error::GuardError;

/// Hundredths in a whole percent or a whole point.
const HUNDRED: u64 = 100;

/// Hundredths of a percent in the whole: 100.00 %.
const WHOLE: u64 = 10_000;

/// A quantity in hundredths, written with two decimals.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
struct Hundredths(u64);

impl fmt::Display for Hundredths
{
    /// Writes the whole part, `.`, and the two-digit remainder: `94.47`,
    /// `0.50`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes the quotient by a hundred, `.`, and the remainder
    ///   padded to two digits.
    /// - provides: every percentage and point the report prints.
    /// - fails: propagates the formatter's own write failure.
    /// - panics: none.
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — values under one, with a one-digit remainder and past
    ///   a hundred; an unpadded remainder or a swapped quotient changes the
    ///   text.
    /// - witness: `measure::tests::coverage_reads_as_codecov_writes_it`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        let whole = self.0.checked_div(HUNDRED).unwrap_or_default();
        let part = self.0.checked_rem(HUNDRED).unwrap_or_default();
        write!(f, "{whole}.{part:02}")
    }
}

/// The lines a report, a crate or a file measured, and how many of them a
/// test executed.
///
/// # Specification
/// - provides: what a coverage is computed from; Codecov's `lines` and `hits`
///   totals, partial lines counted as measured and not covered.
#[derive(Clone, Copy, Debug, Default, Deserialize, Eq, PartialEq)]
pub struct Lines
{
    /// Every line the instrumentation measured.
    #[serde(rename = "lines")]
    measured: u64,
    /// The measured lines some test executed.
    #[serde(rename = "hits")]
    covered: u64,
}

/// Why a set of lines has no coverage.
///
/// # Specification
/// - provides: the one reason a coverage is absent.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Unmeasured
{
    /// No line was measured.
    NoLines,
}

impl Lines
{
    /// These lines and `other`'s together.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: each count is the saturating sum of the two.
    /// - provides: a crate's lines from its files'.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two files of one crate summed; a dropped or swapped
    ///   count changes the crate's coverage.
    /// - witness: `report::tests::a_crate_sums_its_files`
    #[spec(ensures: |ret| ret.measured == self.measured.saturating_add(other.measured)
        && ret.covered == self.covered.saturating_add(other.covered))]
    #[must_use]
    #[inline]
    pub fn plus(
        self,
        other: Self,
    ) -> Self
    {
        Self {
            measured: self.measured.saturating_add(other.measured),
            covered: self.covered.saturating_add(other.covered),
        }
    }

    /// The measured lines no test executed.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub const fn missed(self) -> Missed
    {
        Missed(self.measured.saturating_sub(self.covered))
    }

    /// The covered share of the measured lines, in hundredths of a percent
    /// rounded down, as Codecov's default `round: down` states it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Maybe::Present`] holding ⌊covered × 10 000 ÷ measured⌋ when
    ///   any line was measured.
    /// - provides: the number the report compares.
    /// - fails: [`Unmeasured::NoLines`] when no line was measured.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the 10-19 and 10-20 uploads' totals, whose rounded
    ///   and truncated values differ, and no lines; rounding to nearest or
    ///   dividing the other way changes the value.
    /// - witness: `measure::tests::coverage_reads_as_codecov_writes_it`
    #[spec(ensures: |ret| matches!(ret, Maybe::Absent(_)) == (self.measured == 0))]
    #[inline]
    pub fn coverage(self) -> Maybe<Coverage, Unmeasured>
    {
        // Widened, so no count a report can hold overflows the scaling; the
        // quotient is at most 10 000 while covered lines never exceed the
        // measured.
        u128::from(self.covered)
            .saturating_mul(u128::from(WHOLE))
            .checked_div(u128::from(self.measured))
            .map_or(Maybe::Absent(Unmeasured::NoLines), |hundredths| {
                Maybe::Present(Coverage(Hundredths(
                    u64::try_from(hundredths).unwrap_or(u64::MAX),
                )))
            })
    }
}

/// How many measured lines no test executed.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct Missed(u64);

impl fmt::Display for Missed
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

/// A coverage: hundredths of a percent of the measured lines.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
pub struct Coverage(Hundredths);

impl Coverage
{
    /// The coverage of nothing covered.
    pub const ZERO: Self = Self(Hundredths(0));

    /// How far `after` moved from this coverage.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Change::Fell`] by the difference when `after` is lower,
    ///   [`Change::Rose`] by it when higher, [`Change::Held`] when equal.
    /// - provides: the drop the threshold is held against.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a fall, a rise and equality; a reversed subtraction
    ///   or a swapped direction changes the variant or its points.
    /// - witness: `measure::tests::a_change_names_its_direction`
    #[spec(ensures: |ret| matches!(ret, Change::Held) == (self == after))]
    #[inline]
    #[must_use]
    pub fn change_to(
        self,
        after: Self,
    ) -> Change
    {
        let (before, after) = (self.0.0, after.0.0);
        match after.cmp(&before) {
            Ordering::Less => Change::Fell(Points(Hundredths(before.saturating_sub(after)))),
            Ordering::Greater => Change::Rose(Points(Hundredths(after.saturating_sub(before)))),
            Ordering::Equal => Change::Held,
        }
    }

    /// The colour a badge paints this coverage in, over Codecov's default
    /// range of 60 % to 100 %: red below it, then a step every ten points up
    /// to bright green.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub const fn colour(self) -> Colour
    {
        match self.0.0.div_euclid(HUNDRED) {
            90 .. => Colour::BrightGreen,
            80 .. => Colour::Green,
            70 .. => Colour::Yellow,
            60 .. => Colour::Orange,
            _ => Colour::Red,
        }
    }
}

/// A badge's colour, as shields.io names it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Colour
{
    /// Under 60 %.
    Red,
    /// From 60 %.
    Orange,
    /// From 70 %.
    Yellow,
    /// From 80 %.
    Green,
    /// From 90 %.
    BrightGreen,
}

impl fmt::Display for Colour
{
    /// Writes shields.io's name of the colour.
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
            Self::Red => "red",
            Self::Orange => "orange",
            Self::Yellow => "yellow",
            Self::Green => "green",
            Self::BrightGreen => "brightgreen",
        })
    }
}

impl fmt::Display for Coverage
{
    /// Writes the percentage with two decimals and no sign: `94.47`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        self.0.fmt(f)
    }
}

/// Percentage points, in hundredths: how far a coverage moved, or how far it
/// may fall before the guard files.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
pub struct Points(Hundredths);

impl FromStr for Points
{
    type Err = GuardError;

    /// Reads a decimal of at most two fractional digits: `0.5`, `1`, `0.25`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the points the decimal states, in hundredths.
    /// - provides: the threshold from the workflow's argument.
    /// - fails: [`GuardError::Threshold`] when the text is empty, holds a
    ///   character other than digits and one `.`, has more than two fractional
    ///   digits, or overflows.
    /// - panics: none.
    /// - executable: none — the outcome is the parse itself.
    ///
    /// # Errors
    /// As `fails` lists.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a whole number, one and two fractional digits, three,
    ///   a sign, a lone `.` and the empty text; reading `0.5` as five
    ///   hundredths or accepting a third digit changes a parse.
    /// - witness: `measure::tests::a_threshold_reads_points`
    #[inline]
    fn from_str(text: &str) -> Result<Self, Self::Err>
    {
        let refuse = || GuardError::Threshold {
            text: text.to_owned(),
        };
        let (whole, fraction) = text.split_once('.').unwrap_or((text, ""));
        let digits = |part: &str| part.bytes().all(|byte| byte.is_ascii_digit());
        if whole.is_empty() || !digits(whole) || !digits(fraction) || fraction.len() > 2 {
            return Err(refuse());
        }
        let whole = whole.parse::<u64>().ok().ok_or_else(refuse)?;
        let fraction = format!("{fraction:0<2}")
            .parse::<u64>()
            .ok()
            .ok_or_else(refuse)?;
        let hundredths = whole
            .checked_mul(HUNDRED)
            .and_then(|scaled| scaled.checked_add(fraction))
            .ok_or_else(refuse)?;
        Ok(Self(Hundredths(hundredths)))
    }
}

impl fmt::Display for Points
{
    /// Writes the points with two decimals and no sign: `0.50`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        self.0.fmt(f)
    }
}

/// How one coverage moved from another.
///
/// # Specification
/// - provides: the change column and the drop the threshold is held against;
///   ordered from the largest fall to the largest rise.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Change
{
    /// The later coverage is lower by these points.
    Fell(Points),
    /// The two are equal.
    Held,
    /// The later coverage is higher by these points.
    Rose(Points),
}

impl Ord for Change
{
    /// Orders the largest fall first and the largest rise last.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: every fall before [`Change::Held`] before every rise; a
    ///   larger fall before a smaller, a smaller rise before a larger.
    /// - provides: the report's row order, worst first.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two falls, equality and two rises sorted; ordering
    ///   falls by size ascending puts the smaller fall first.
    /// - witness: `measure::tests::changes_order_worst_first`
    #[spec(ensures: |ret| matches!(ret, Ordering::Equal) == (self == other))]
    #[inline]
    fn cmp(
        &self,
        other: &Self,
    ) -> Ordering
    {
        match (*self, *other) {
            (Self::Fell(left), Self::Fell(right)) => right.cmp(&left),
            (Self::Rose(left), Self::Rose(right)) => left.cmp(&right),
            (Self::Held, Self::Held) => Ordering::Equal,
            (Self::Fell(_), Self::Held | Self::Rose(_)) | (Self::Held, Self::Rose(_)) => {
                Ordering::Less
            },
            (Self::Held | Self::Rose(_), Self::Fell(_)) | (Self::Rose(_), Self::Held) => {
                Ordering::Greater
            },
        }
    }
}

impl PartialOrd for Change
{
    /// As [`Ord::cmp`].
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn partial_cmp(
        &self,
        other: &Self,
    ) -> Option<Ordering>
    {
        Some(self.cmp(other))
    }
}

impl fmt::Display for Change
{
    /// Writes the signed points: `-6.53`, `+0.11`, `0.00`.
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
            Self::Fell(points) => write!(f, "-{points}"),
            Self::Held => f.write_str("0.00"),
            Self::Rose(points) => write!(f, "+{points}"),
        }
    }
}

#[cfg(test)]
mod tests
{
    use quenchant_shape::shape::Maybe;

    use super::Change;
    use super::Coverage;
    use super::Hundredths;
    use super::Lines;
    use super::Points;
    use super::Unmeasured;

    #[test]
    fn coverage_reads_as_codecov_writes_it()
    {
        // 10-19: 271 890 of 287 798 is 94.4725 %; 10-20: 282 285 of
        // 320 972 is 87.9470 %, which rounds to 87.95 and Codecov writes as
        // 87.94.
        for (measured, covered, written) in [
            (287_798, 271_890, "94.47"),
            (320_972, 282_285, "87.94"),
            (3, 1, "33.33"),
            (1, 1, "100.00"),
            (200, 1, "0.50"),
        ] {
            let lines = Lines { measured, covered };
            let Maybe::Present(coverage) = lines.coverage()
            else {
                panic!("{lines:?} has lines");
            };
            assert_eq!(coverage.to_string(), written, "{lines:?}");
        }
        assert_eq!(
            Lines::default().coverage(),
            Maybe::Absent(Unmeasured::NoLines)
        );
    }

    #[test]
    fn a_change_names_its_direction()
    {
        let at = |hundredths| Coverage(Hundredths(hundredths));
        assert_eq!(
            at(9447).change_to(at(8794)),
            Change::Fell(Points(Hundredths(653)))
        );
        assert_eq!(
            at(9447).change_to(at(9458)),
            Change::Rose(Points(Hundredths(11)))
        );
        assert_eq!(at(9447).change_to(at(9447)), Change::Held);
        assert_eq!(at(9447).change_to(at(8794)).to_string(), "-6.53");
        assert_eq!(at(9447).change_to(at(9458)).to_string(), "+0.11");
        assert_eq!(at(9447).change_to(at(9447)).to_string(), "0.00");
    }

    #[test]
    fn a_threshold_reads_points()
    {
        for (text, hundredths) in [
            ("0.5", 50),
            ("1", 100),
            ("0.25", 25),
            ("12.05", 1205),
            ("3.", 300),
        ] {
            assert_eq!(
                text.parse::<Points>(),
                Ok(Points(Hundredths(hundredths))),
                "{text}"
            );
        }
        for text in ["", ".", ".5", "0.125", "-1", "+1", "1,5", "a"] {
            assert!(text.parse::<Points>().is_err(), "{text}");
        }
    }

    #[test]
    fn changes_order_worst_first()
    {
        let points = |hundredths| Points(Hundredths(hundredths));
        let mut changes = vec![
            Change::Rose(points(200)),
            Change::Held,
            Change::Fell(points(10)),
            Change::Rose(points(5)),
            Change::Fell(points(700)),
        ];
        changes.sort();
        assert_eq!(changes, [
            Change::Fell(points(700)),
            Change::Fell(points(10)),
            Change::Held,
            Change::Rose(points(5)),
            Change::Rose(points(200)),
        ]);
    }
}
