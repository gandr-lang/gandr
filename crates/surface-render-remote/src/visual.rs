//! The visual language: the warrant palette, its glyphs, the marks that a
//! renderer may emit, and the rules of the blueprint as checks over a
//! rendering of a frame.
//!
//! A renderer reads a [`Frame`], records of named fields in the frame's
//! order, and emits a [`Rendering`] as data: panes of rows of cells. A cell
//! names the field it encodes ([`Place`]) and holds its text, an optional
//! warrant with its glyph, an optional numeral with its unit, an optional
//! sparkline of 32 samples, and the attributes it is painted with. A painter
//! puts the cells on a terminal or a page and adds nothing. So each rule reads
//! the rendering and the frame, never pixels, and a rendering that conforms
//! paints as one that conforms. [`conform`] runs every rule of [`RULES`], and
//! a rendering that it does not pass does not land.
//!
//! Hue carries one variable: the warrant of the thing shown. Each warrant has
//! one colour name, which each host binds to its theme, and one glyph, which a
//! renderer without colour shows:
//!
//! | Warrant | Glyph | Colour name |
//! | --- | --- | --- |
//! | `pending` | `·` | `gandr.warrant.pending` |
//! | `checked` | `✓` | `gandr.warrant.checked` |
//! | `replayed` | `✓✓` | `gandr.warrant.replayed` |
//! | `refused` | `✗` | `gandr.warrant.refused` |
//! | `withheld` | `○` | `gandr.warrant.withheld` |
//!
//! A quantity is a numeral, right-aligned, with three significant digits; its
//! unit is stated once at the head of its column. A count takes an SI prefix,
//! a time is in µs below 1 ms and in ms above, and bytes are in B, KiB and
//! MiB. A sparkline is 32 cells of the eight block elements `▁▂▃▄▅▆▇█` and its
//! last value as a numeral. A label is the name of its field. An absent datum
//! draws nothing.
//!
//! Each rule is one private function named by the rule's slug, over a
//! [`Shown`]: the frame, its rendering, and the frame and rendering before it
//! when there is one. A check reads each cell a fixed number of times, in rows
//! or in columns, and it allocates nothing. A rule that counts the cells of
//! one field counts them in one run of adjacent cells of a row: a latency's two
//! numerals and a comparison's two sides sit side by side. Only a breach
//! allocates, as the entry of the list that [`conform`] answers.
//!
//! # References
//!
//! - `vault:01a1c68b-1e9e-7942-aa36-b8d9096dec0e` — anchor: the engine-surface
//!   blueprint (§ engine-surface-visual, § engine-surface-visual-warrant) — the
//!   twenty rules and their checks, the five warrants, their glyphs and their
//!   colour names.

use alloc::string::String;
use alloc::string::ToString as _;
use alloc::vec::Vec;
use core::fmt;
use core::num::NonZeroU64;
use core::time::Duration;

use anodized::spec;

/// How far a layer vouches for what a mark shows: the one variable that a
/// mark's hue and glyph carry.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(rename_all = "camelCase"))]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Warrant
{
    /// This revision has no verdict yet from the layer shown.
    Pending,
    /// The checker accepted it, and the kernel has not replayed the whole.
    Checked,
    /// The kernel replayed it, or an attested verdict admitted it.
    Replayed,
    /// The kernel refused it.
    Refused,
    /// It did not cross to the kernel, and the mark's text says why.
    Withheld,
}

/// The five warrants, from the weakest claim to the strongest refusal.
pub const WARRANTS: [Warrant; 5] = [
    Warrant::Pending,
    Warrant::Checked,
    Warrant::Replayed,
    Warrant::Refused,
    Warrant::Withheld,
];

impl Warrant
{
    /// The warrant's glyph, the same in every face.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn glyph(self) -> Glyph
    {
        Glyph(match self {
            Self::Pending => "·",
            Self::Checked => "✓",
            Self::Replayed => "✓✓",
            Self::Refused => "✗",
            Self::Withheld => "○",
        })
    }

    /// The warrant's colour name, which each host binds to its theme.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn colour(self) -> Colour
    {
        Colour(match self {
            Self::Pending => "gandr.warrant.pending",
            Self::Checked => "gandr.warrant.checked",
            Self::Replayed => "gandr.warrant.replayed",
            Self::Refused => "gandr.warrant.refused",
            Self::Withheld => "gandr.warrant.withheld",
        })
    }
}

/// A glyph a renderer draws, serialised as its text.
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Glyph(&'static str);

impl From<&'static str> for Glyph
{
    /// The glyph spelled `text`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(text: &'static str) -> Self
    {
        Self(text)
    }
}

impl From<Glyph> for &'static str
{
    /// The glyph's text.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(glyph: Glyph) -> Self
    {
        glyph.0
    }
}

/// The glyphs of a derivation: a premise, a conclusion, a conversion, and the
/// node of a judgement.
pub const DERIVATION_GLYPHS: [Glyph; 4] = [Glyph("⇐"), Glyph("⇒"), Glyph("="), Glyph("·")];

/// The eight block elements a sparkline is drawn with, from the lowest sample
/// to the highest.
pub const BLOCKS: [char; 8] = ['▁', '▂', '▃', '▄', '▅', '▆', '▇', '█'];

/// The samples a sparkline holds.
pub const SAMPLES: usize = 32;

/// A colour that a renderer names; each host binds a name to its theme.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Colour(&'static str);

impl From<&'static str> for Colour
{
    /// The colour named `name`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(name: &'static str) -> Self
    {
        Self(name)
    }
}

impl From<Colour> for &'static str
{
    /// The colour's name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(colour: Colour) -> Self
    {
        colour.0
    }
}

/// The unit of a column of numerals, stated once at its head.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Unit
{
    /// A count, with an SI prefix past 999.
    Count,
    /// A time below 1 ms.
    Microseconds,
    /// A time of 1 ms or more.
    Milliseconds,
    /// Bytes below 1 KiB.
    Bytes,
    /// Kibibytes below 1 MiB.
    Kibibytes,
    /// Mebibytes.
    Mebibytes,
    /// A ratio, `hits/total`.
    Ratio,
}

impl From<Unit> for &'static str
{
    /// The unit's symbol at the head of its column: none for a count and a
    /// ratio.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(unit: Unit) -> Self
    {
        match unit {
            Unit::Count | Unit::Ratio => "",
            Unit::Microseconds => "µs",
            Unit::Milliseconds => "ms",
            Unit::Bytes => "B",
            Unit::Kibibytes => "KiB",
            Unit::Mebibytes => "MiB",
        }
    }
}

/// A count of things.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Count(pub u64);

/// A numeral as a renderer draws it, with its unit.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Numeral
{
    /// The digits drawn, with a count's SI prefix; the unit is the column's.
    pub text: String,
    /// The unit.
    pub unit: Unit,
}

impl From<Count> for Numeral
{
    /// `count` with three significant digits: as it is below 1000, and past
    /// that cut to three digits under the SI prefix of its thousands.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a [`Unit::Count`] numeral; below 1000 the decimal digits of
    ///   `count`; past that a mantissa of three significant digits from 1.00 to
    ///   999, cut and not rounded, and the prefix `k`, `M`, `G`, `T`, `P` or
    ///   `E` of its thousands.
    /// - provides: the one spelling of a count in every face.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the counts at each boundary of a prefix, and the
    ///   largest count, read as three significant digits that the `numerals`
    ///   rule passes.
    /// - witness: `visual::tests::a_count_reads_as_three_significant_digits`
    #[spec(ensures: |ref ret| ret.unit == Unit::Count && patterned(ret).is_some())]
    #[inline]
    fn from(count: Count) -> Self
    {
        let Count(count) = count;
        let mut scale = 1_u128;
        let mut prefixes = ["", "k", "M", "G", "T", "P", "E"].into_iter();
        let mut prefix = prefixes.next().unwrap_or_default();
        while u128::from(count) >= scale.saturating_mul(1000) {
            let Some(next) = prefixes.next()
            else {
                break;
            };
            scale = scale.saturating_mul(1000);
            prefix = next;
        }
        let whole = u128::from(count).checked_div(scale).unwrap_or_default();
        let text = if scale == 1 {
            count.to_string()
        }
        else if whole >= 100 {
            alloc::format!("{whole}{prefix}")
        }
        else if whole >= 10 {
            let tenths = u128::from(count)
                .saturating_mul(10)
                .checked_div(scale)
                .unwrap_or_default()
                .checked_rem(10)
                .unwrap_or_default();
            alloc::format!("{whole}.{tenths}{prefix}")
        }
        else {
            let hundredths = u128::from(count)
                .saturating_mul(100)
                .checked_div(scale)
                .unwrap_or_default()
                .checked_rem(100)
                .unwrap_or_default();
            alloc::format!("{whole}.{hundredths:02}{prefix}")
        };
        Self {
            text,
            unit: Unit::Count,
        }
    }
}

impl Numeral
{
    /// `value`, counted in the base of `unit`, as a numeral in `unit`: a
    /// count is as [`Numeral::from`] spells it, a time counts nanoseconds, a
    /// size counts bytes, and a ratio is the plain digits of `value`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a numeral in `unit`. A time or a size is the quotient of
    ///   `value` by its unit, with three significant digits, cut and not
    ///   rounded: the whole part from 100 up, its digits past the third set to
    ///   zero; one decimal from 10 up; two decimals from 1 up; and below 1, the
    ///   first three significant digits after the point.
    /// - provides: the one spelling of a quantity in every face, for a
    ///   sparkline's last value and its scale.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — times and sizes at each boundary of the cut read as
    ///   three significant digits that the `numerals` rule passes.
    /// - witness: `visual::tests::a_time_and_a_size_read_as_three_significant_digits`
    #[spec(ensures: |ref ret| ret.unit == unit)]
    #[inline]
    #[must_use]
    pub fn of(
        value: Count,
        unit: Unit,
    ) -> Self
    {
        match unit {
            Unit::Count => Self::from(value),
            Unit::Ratio => Self {
                text: value.0.to_string(),
                unit,
            },
            Unit::Microseconds
            | Unit::Milliseconds
            | Unit::Bytes
            | Unit::Kibibytes
            | Unit::Mebibytes => Self {
                text: significant(value, unit),
                unit,
            },
        }
    }
}

/// The quotient of `value` by the base of `unit`, with three significant
/// digits, cut and not rounded, as [`Numeral::of`] states it.
///
/// # Specification
/// trivial.
fn significant(
    value: Count,
    unit: Unit,
) -> String
{
    let per: u128 = match unit {
        Unit::Count | Unit::Ratio | Unit::Bytes => 1,
        Unit::Microseconds => 1_000,
        Unit::Milliseconds => 1_000_000,
        Unit::Kibibytes => 1 << 10_u32,
        Unit::Mebibytes => 1 << 20_u32,
    };
    let value = u128::from(value.0);
    let scaled = |times: u128| {
        value
            .saturating_mul(times)
            .checked_div(per)
            .unwrap_or_default()
    };
    let whole = scaled(1);
    if whole >= 100 {
        let (mut digits, mut zeros) = (whole, 0_usize);
        while digits >= 1000 {
            digits = digits.checked_div(10).unwrap_or_default();
            zeros = zeros.saturating_add(1);
        }
        let mut text = digits.to_string();
        text.extend(core::iter::repeat_n('0', zeros));
        return text;
    }
    if whole >= 10 {
        let tenths = scaled(10).checked_rem(10).unwrap_or_default();
        return alloc::format!("{whole}.{tenths}");
    }
    if whole >= 1 {
        let hundredths = scaled(100).checked_rem(100).unwrap_or_default();
        return alloc::format!("{whole}.{hundredths:02}");
    }
    if value == 0 {
        return String::from("0");
    }
    // Below one: the first power of ten that lifts the quotient to three
    // digits names how many zeros lead the digits after the point.
    let mut places = 3_usize;
    let mut times = 1_000_u128;
    while scaled(times) < 100 && places < 38 {
        places = places.saturating_add(1);
        times = times.saturating_mul(10);
    }
    let mut text = String::from("0.");
    text.extend(core::iter::repeat_n('0', places.saturating_sub(3)));
    text.push_str(&scaled(times).to_string());
    text
}

/// A sparkline: the last 32 samples of a quantity, word-sized, and its last
/// value.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Sparkline
{
    /// One block element per sample, the oldest first.
    pub cells: String,
    /// The last sample, drawn after the cells.
    pub last: Numeral,
    /// The value the highest block stands for.
    pub scale: Numeral,
    /// The span of time the samples cover.
    pub window: Numeral,
}

impl Sparkline
{
    /// The sparkline of `samples` under the column scale `scale`, in `unit`:
    /// none for a ring with no sample.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: present exactly when `samples` holds a value. Its cells are
    ///   [`SAMPLES`] block elements: the lowest block for each slot of the ring
    ///   that no sample fills yet, the oldest slots first, then one block per
    ///   sample, the oldest first, whose height is the sample's share of
    ///   `scale` over the eight blocks. A sample at or over `scale` takes the
    ///   highest block. Its last value and its scale are [`Numeral::of`] in
    ///   `unit`, and its window is the 32 samples it spans.
    /// - provides: the one drawing of a sparkline field in every face, so the
    ///   `sparklines` rule holds of each.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a full ring and a ring of three samples draw their
    ///   exact cells and numerals, the rendering of each breaks no rule, and an
    ///   empty ring draws none.
    /// - witness: `visual::tests::a_ring_draws_thirty_two_cells_and_its_last_value`
    #[spec(ensures: |ref ret| ret.is_some() != samples.values().is_empty()
        && ret.as_ref().is_none_or(|line| line.cells.chars().count() == SAMPLES
            && line.last.unit == unit))]
    #[inline]
    #[must_use]
    pub fn of(
        samples: &Samples,
        scale: Count,
        unit: Unit,
    ) -> Option<Self>
    {
        let values = samples.values();
        let &last = values.last()?;
        let top = u128::from(scale.0);
        let lowest = BLOCKS.first().copied().unwrap_or('▁');
        let highest = BLOCKS.last().copied().unwrap_or('█');
        let mut cells: String =
            core::iter::repeat_n(lowest, SAMPLES.saturating_sub(values.len())).collect();
        cells.extend(values.iter().map(|&Count(value)| {
            let step = u128::from(value)
                .min(top)
                .saturating_mul(7)
                .saturating_add(top.checked_div(2).unwrap_or_default())
                .checked_div(top)
                .unwrap_or_default();
            usize::try_from(step)
                .ok()
                .and_then(|step| BLOCKS.get(step).copied())
                .unwrap_or(highest)
        }));
        Some(Self {
            cells,
            last: Numeral::of(last, unit),
            scale: Numeral::of(scale, unit),
            window: Numeral::from(Count(u64::try_from(SAMPLES).unwrap_or(u64::MAX))),
        })
    }
}

/// What the samples of a sparkline field count: things, or nanoseconds.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum SampleUnit
{
    /// A count of things.
    Count,
    /// A time, in nanoseconds.
    Nanoseconds,
}

/// The ring of a sparkline field: at most [`SAMPLES`] values of one unit, the
/// oldest first, and the most that one value can hold when the producer knows
/// it.
///
/// # Specification
/// - ensures: the ring holds at most [`SAMPLES`] values, whether built by
///   [`Samples::new`] or [`Samples::bounded`] or decoded.
/// - provides: the wire image `{"unit": u, "values": [v, …], "ceiling": c}`
///   under the `serde` feature, with no `ceiling` for a ring that has none,
///   whose decode refuses a longer ring with [`TooManySamples`].
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Samples
{
    /// What each value counts.
    unit: SampleUnit,
    /// The values, the oldest first.
    values: Vec<Count>,
    /// The most that one value can hold: the scale of a live sparkline, which
    /// stays as the values move. A ceiling is never zero, so it costs the ring
    /// one word.
    #[cfg_attr(feature = "serde", serde(skip_serializing_if = "Option::is_none"))]
    ceiling: Option<NonZeroU64>,
}

impl Samples
{
    /// The ring of `values` in `unit`, the oldest first.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the ring holds exactly `values` in `unit`.
    /// - provides: the only way to build a ring, so a renderer never draws more
    ///   than [`SAMPLES`] cells.
    /// - fails: [`TooManySamples`], with the count offered, past [`SAMPLES`]
    ///   values.
    /// - panics: none.
    ///
    /// # Errors
    /// [`TooManySamples`] past [`SAMPLES`] values.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a ring of 32 values builds and decodes, and a ring of
    ///   33 is refused both ways.
    /// - witness: `visual::tests::a_ring_holds_at_most_thirty_two_samples`
    #[spec(captures: [offered = values.len()], ensures: |ref ret| match *ret {
        Ok(ref ring) => offered <= SAMPLES && ring.unit == unit,
        Err(ref refused) => offered > SAMPLES && refused.offered == offered,
    })]
    #[inline]
    pub fn new(
        unit: SampleUnit,
        values: Vec<Count>,
    ) -> Result<Self, TooManySamples>
    {
        if values.len() > SAMPLES {
            return Err(TooManySamples {
                offered: values.len(),
            });
        }
        Ok(Self {
            unit,
            values,
            ceiling: None,
        })
    }

    /// The full ring of `values` in `unit`, the oldest first, none of which
    /// can hold more than `ceiling`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the ring holds exactly `values` in `unit`, under `ceiling`. A
    ///   zero ceiling bounds no value, so the ring keeps none.
    /// - provides: a ring whose length its type states, so it never fails, and
    ///   whose scale stays as its values move.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a bounded ring holds the 32 values that
    ///   [`Samples::new`] admits, and its ceiling survives a round trip.
    /// - witness: `visual::tests::a_ring_holds_at_most_thirty_two_samples`
    #[spec(ensures: |ref ret| ret.values.len() == SAMPLES && ret.unit == unit
        && ret.ceiling() == Some(ceiling).filter(|&Count(most)| most != 0))]
    #[inline]
    #[must_use]
    pub fn bounded(
        unit: SampleUnit,
        values: [Count; SAMPLES],
        ceiling: Count,
    ) -> Self
    {
        Self {
            unit,
            values: Vec::from(values),
            ceiling: NonZeroU64::new(ceiling.0),
        }
    }

    /// What each value counts.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn unit(&self) -> SampleUnit
    {
        self.unit
    }

    /// The values, the oldest first.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn values(&self) -> &[Count]
    {
        &self.values
    }

    /// The most that one value can hold, when the producer states it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn ceiling(&self) -> Option<Count>
    {
        match self.ceiling {
            Some(most) => Some(Count(most.get())),
            None => None,
        }
    }
}

/// The decode image of a [`Samples`] ring: its unit, its values and its
/// ceiling before the length check.
#[cfg(feature = "serde")]
#[derive(serde::Deserialize)]
struct SamplesWire
{
    /// The decoded unit.
    unit: SampleUnit,
    /// The decoded values.
    values: Vec<Count>,
    /// The decoded ceiling, absent for a ring that has none.
    #[serde(default)]
    ceiling: Option<Count>,
}

#[cfg(feature = "serde")]
impl<'input> serde::Deserialize<'input> for Samples
{
    /// Decode a ring and refuse it past [`SAMPLES`] values.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the ring holds exactly the decoded values and
    ///   ceiling.
    /// - fails: the deserializer's error for a malformed image, and a custom
    ///   error carrying the [`TooManySamples`] message for a longer ring.
    /// - panics: none.
    ///
    /// # Errors
    /// The deserializer's error, or the refusal of a longer ring.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Samples::new`].
    /// - witness: `visual::tests::a_ring_holds_at_most_thirty_two_samples`
    #[inline]
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |ring| ring.values.len() <= SAMPLES))]
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'input>,
    {
        let wire = SamplesWire::deserialize(deserializer)?;

        Self::new(wire.unit, wire.values)
            .map(|ring| Self {
                ceiling: wire.ceiling.and_then(|Count(most)| NonZeroU64::new(most)),
                ..ring
            })
            .map_err(serde::de::Error::custom)
    }
}

/// The refusal of a ring of more than [`SAMPLES`] values.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct TooManySamples
{
    /// How many values were offered.
    pub offered: usize,
}

impl fmt::Display for TooManySamples
{
    /// Write the refusal with the count offered.
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
            "a sparkline holds {SAMPLES} samples at most, not {}",
            self.offered
        )
    }
}

impl core::error::Error for TooManySamples
{
}

/// How a renderer paints a cell.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Attribute
{
    /// The cell's text in the named colour.
    Hue(Colour),
    /// The text in a heavier weight: a syntax role in gandr's own faces.
    Bold,
    /// The text slanted: a syntax role in gandr's own faces.
    Italic,
    /// The text in a lighter shade.
    Faint,
    /// The cell drawn partly transparent.
    Opacity,
    /// The cell's ground in the named colour.
    Background(Colour),
    /// A line drawn around the cell.
    Border,
    /// The cell drawn on and off in time.
    Blink,
}

/// What a cell shows of its field: the field's name, or its datum.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Role
{
    /// The name of the field, beside its datum.
    Label,
    /// The field's datum.
    Value,
}

/// Where a cell's text sits in its column.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Align
{
    /// At the column's left edge: a label or a text.
    Left,
    /// At the column's right edge: a numeral or a sparkline.
    Right,
}

/// A field of a frame: its record's position in the frame, and its position in
/// the record.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Place
{
    /// The record's position in the frame.
    pub record: usize,
    /// The field's position in the record.
    pub field: usize,
}

/// One cell of a rendering.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Cell
{
    /// The field the cell encodes; none for a cell that draws nothing.
    pub place: Option<Place>,
    /// What the cell shows of its field.
    pub role: Role,
    /// The text drawn after the glyph: a label, a datum's spelling, a
    /// numeral's digits, or a sparkline's cells and its last value.
    pub text: String,
    /// The glyph drawn first.
    pub glyph: Option<Glyph>,
    /// The warrant the cell shows.
    pub warrant: Option<Warrant>,
    /// The numeral the cell shows.
    pub numeral: Option<Numeral>,
    /// The sparkline the cell shows.
    pub sparkline: Option<Sparkline>,
    /// How the cell is painted.
    pub attributes: Vec<Attribute>,
    /// Where the text sits in its column.
    pub align: Align,
}

impl Cell
{
    /// A cell that draws nothing.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn blank() -> Self
    {
        Self {
            place: None,
            role: Role::Value,
            text: String::new(),
            glyph: None,
            warrant: None,
            numeral: None,
            sparkline: None,
            attributes: Vec::new(),
            align: Align::Left,
        }
    }

    /// The label of the field at `place`, spelled `name`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn label(
        place: Place,
        name: FieldName,
    ) -> Self
    {
        Self {
            place: Some(place),
            role: Role::Label,
            text: String::from(<&str>::from(name)),
            ..Self::blank()
        }
    }

    /// The datum of the field at `place`, spelled `text`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn text(
        place: Place,
        text: String,
    ) -> Self
    {
        Self {
            place: Some(place),
            text,
            ..Self::blank()
        }
    }

    /// The datum of the field at `place`, drawn as `numeral` at the column's
    /// right edge.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn numeral(
        place: Place,
        numeral: Numeral,
    ) -> Self
    {
        Self {
            place: Some(place),
            text: numeral.text.clone(),
            numeral: Some(numeral),
            align: Align::Right,
            ..Self::blank()
        }
    }
}

/// One row of a pane: one line.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Row
{
    /// The cells, one per column.
    pub cells: Vec<Cell>,
}

/// The head of a column: its field's name and the unit of its numerals.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Head
{
    /// The name of the field the column shows.
    pub name: FieldName,
    /// The unit of the column's numerals; none for a column of text.
    pub unit: Option<Unit>,
}

/// A pane: rows of one shape under their column heads.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Pane
{
    /// The column heads; none for a pane whose labels sit beside the marks.
    pub heads: Vec<Head>,
    /// The rows, in the frame's order.
    pub rows: Vec<Row>,
}

/// What a renderer emits for one frame: its panes.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Rendering
{
    /// The panes, top to bottom.
    pub panes: Vec<Pane>,
}

/// The name of a field of a frame, which its label spells.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct FieldName(&'static str);

impl From<&'static str> for FieldName
{
    /// The field named `name`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(name: &'static str) -> Self
    {
        Self(name)
    }
}

impl From<FieldName> for &'static str
{
    /// The field's name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(name: FieldName) -> Self
    {
        name.0
    }
}

/// The revision of the document a datum was computed for.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Revision(pub i64);

/// The datum of a field.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Datum
{
    /// No datum.
    Absent,
    /// A text.
    Text(String),
    /// A count.
    Count(Count),
    /// A time, and the window that bounds it when the producer states one: a
    /// live column keeps the unit of its window as its times move.
    Duration
    {
        /// The time.
        time: Duration,
        /// The span of time that bounds it.
        window: Option<Duration>,
    },
    /// A size in bytes.
    Bytes(Count),
    /// A latency: its median and its 99th percentile over a window.
    Latency
    {
        /// The median.
        p50: Duration,
        /// The 99th percentile.
        p99: Duration,
        /// The span of time the samples cover.
        window: Duration,
    },
    /// A ratio of hits to a total.
    Ratio
    {
        /// The hits.
        hits: Count,
        /// The total.
        total: Count,
    },
    /// The ring of a sparkline field: its last samples, the oldest first.
    Samples(Samples),
    /// A warrant.
    Warrant(Warrant),
    /// A count before and the count after.
    Comparison
    {
        /// The count before.
        before: Count,
        /// The count after.
        after: Count,
    },
}

/// One field of a record.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Field
{
    /// The field's name.
    pub name: FieldName,
    /// Its datum.
    pub datum: Datum,
    /// The revision its datum was computed for.
    pub revision: Revision,
}

/// One record of a frame: the fields of one thing shown.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Record
{
    /// The fields, in the order the frame states them.
    pub fields: Vec<Field>,
}

/// The data a renderer shows: records in the frame's order, at the
/// document's revision.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Frame
{
    /// The document's revision.
    pub revision: Revision,
    /// The records, in the frame's order.
    pub records: Vec<Record>,
}

/// A frame and its rendering, with the frame and the rendering before them
/// when there is one.
#[derive(Clone, Copy, Debug)]
pub struct Shown<'shown>
{
    /// The frame.
    pub frame: &'shown Frame,
    /// Its rendering.
    pub rendering: &'shown Rendering,
    /// The frame and the rendering before them.
    pub before: Option<(&'shown Frame, &'shown Rendering)>,
}

/// The position of a cell in a rendering.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct At
{
    /// The pane.
    pub pane: usize,
    /// The row in the pane.
    pub row: usize,
    /// The cell in the row.
    pub cell: usize,
}

/// Where a rendering breaks a rule.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Spot
{
    /// A cell.
    Cell(At),
    /// A row of a pane.
    Row
    {
        /// The pane.
        pane: usize,
        /// The row.
        row: usize,
    },
    /// A column head of a pane.
    Head
    {
        /// The pane.
        pane: usize,
        /// The head.
        head: usize,
    },
}

/// The slug that names a rule of the visual language.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Slug(&'static str);

impl From<Slug> for &'static str
{
    /// The slug's text.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(slug: Slug) -> Self
    {
        slug.0
    }
}

/// A rule of the visual language: its slug and its check, which answers the
/// first place that breaks the rule.
#[derive(Clone, Copy, Debug)]
pub struct Rule
{
    /// The rule's slug.
    pub slug: Slug,
    /// The rule's check.
    pub check: fn(&Shown<'_>) -> Result<(), Spot>,
}

/// One rule that a rendering breaks, and the first place it breaks it.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Breach
{
    /// The rule's slug.
    pub rule: Slug,
    /// The first place that breaks it.
    pub spot: Spot,
}

/// The rules of the visual language, in the blueprint's order.
pub const RULES: [Rule; 20] = [
    Rule {
        slug: Slug("ink-is-data"),
        check: ink_is_data,
    },
    Rule {
        slug: Slug("no-decoration"),
        check: no_decoration,
    },
    Rule {
        slug: Slug("hue-is-warrant"),
        check: hue_is_warrant,
    },
    Rule {
        slug: Slug("lightness-carries-nothing"),
        check: lightness_carries_nothing,
    },
    Rule {
        slug: Slug("quantity-is-length"),
        check: quantity_is_length,
    },
    Rule {
        slug: Slug("small-multiples"),
        check: small_multiples,
    },
    Rule {
        slug: Slug("sparklines"),
        check: sparklines,
    },
    Rule {
        slug: Slug("numerals"),
        check: numerals,
    },
    Rule {
        slug: Slug("latency-is-two-numbers"),
        check: latency_is_two_numbers,
    },
    Rule {
        slug: Slug("ratio-is-a-pair"),
        check: ratio_is_a_pair,
    },
    Rule {
        slug: Slug("change-in-place"),
        check: change_in_place,
    },
    Rule {
        slug: Slug("density"),
        check: density,
    },
    Rule {
        slug: Slug("alignment"),
        check: alignment,
    },
    Rule {
        slug: Slug("stale-is-pending"),
        check: stale_is_pending,
    },
    Rule {
        slug: Slug("glyph-twins-hue"),
        check: glyph_twins_hue,
    },
    Rule {
        slug: Slug("labels-are-field-names"),
        check: labels_are_field_names,
    },
    Rule {
        slug: Slug("absence-is-blank"),
        check: absence_is_blank,
    },
    Rule {
        slug: Slug("document-order"),
        check: document_order,
    },
    Rule {
        slug: Slug("comparison-in-eye-span"),
        check: comparison_in_eye_span,
    },
    Rule {
        slug: Slug("one-meaning-per-glyph"),
        check: one_meaning_per_glyph,
    },
];

/// Every rule of [`RULES`] that `shown`'s rendering breaks, each with the
/// first place that breaks it.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one breach per rule whose check answers a place, in the order of
///   [`RULES`], with that place; none when every rule holds.
/// - provides: the conformance check of every renderer.
/// - fails: never.
/// - panics: none.
/// - intension: each rule reads each cell once, so the check is linear in the
///   cells, up to the maps keyed by field.
///
/// # Adequacy
/// - hypothesis: L3 — a rendering that keeps the language passes every rule,
///   and each rule refuses a rendering that breaks it.
/// - witness: `visual::tests::a_rendering_that_keeps_the_language_breaks_no_rule`
/// - witness: `visual::tests::each_rule_refuses_the_rendering_that_breaks_it`
#[spec(ensures: |ret| ret.len() <= RULES.len())]
#[inline]
#[must_use]
pub fn conform(shown: &Shown<'_>) -> Vec<Breach>
{
    RULES
        .iter()
        .filter_map(|rule| {
            (rule.check)(shown).err().map(|spot| Breach {
                rule: rule.slug,
                spot,
            })
        })
        .collect()
}

/// Each cell of `rendering` with its position, pane by pane and row by row.
///
/// # Specification
/// trivial.
fn cells(rendering: &Rendering) -> impl Iterator<Item = (At, &Cell)>
{
    rendering.panes.iter().enumerate().flat_map(|(pane, held)| {
        held.rows.iter().enumerate().flat_map(move |(row, line)| {
            line.cells
                .iter()
                .enumerate()
                .map(move |(cell, held)| (At { pane, row, cell }, held))
        })
    })
}

/// The field of `frame` at `place`.
///
/// # Specification
/// trivial.
fn field(
    frame: &Frame,
    place: Place,
) -> Option<&Field>
{
    frame.records.get(place.record)?.fields.get(place.field)
}

/// The field a cell of `frame` encodes.
///
/// # Specification
/// trivial.
fn encoded<'frame>(
    frame: &'frame Frame,
    cell: &Cell,
) -> Option<&'frame Field>
{
    field(frame, cell.place?)
}

/// `Some` when `cell` puts any ink on the page.
///
/// # Specification
/// trivial.
fn ink(cell: &Cell) -> Option<()>
{
    (!cell.text.trim().is_empty()
        || cell.glyph.is_some()
        || cell.warrant.is_some()
        || cell.numeral.is_some()
        || cell.sparkline.is_some()
        || !cell.attributes.is_empty())
    .then_some(())
}

/// `Some` when `datum` is a quantity, which a numeral, a bar or a sparkline
/// shows.
///
/// # Specification
/// trivial.
fn quantity(datum: &Datum) -> Option<()>
{
    match *datum {
        Datum::Count(_)
        | Datum::Duration { .. }
        | Datum::Bytes(_)
        | Datum::Latency { .. }
        | Datum::Ratio { .. }
        | Datum::Samples(_)
        | Datum::Comparison { .. } => Some(()),
        Datum::Absent | Datum::Text(_) | Datum::Warrant(_) => None,
    }
}

/// The first spot `spots` yields, as a breach.
///
/// # Specification
/// trivial.
fn first(mut spots: impl Iterator<Item = Spot>) -> Result<(), Spot>
{
    spots.next().map_or(Ok(()), Err)
}

/// `ink-is-data`: every cell that puts ink on the page, and every column
/// head, names a field of the frame; so a rendering of an empty frame is
/// empty.
///
/// # Specification
/// trivial.
fn ink_is_data(shown: &Shown<'_>) -> Result<(), Spot>
{
    let named = |name: FieldName| {
        shown
            .frame
            .records
            .iter()
            .flat_map(|record| &record.fields)
            .any(|field| field.name == name)
    };
    let heads = shown
        .rendering
        .panes
        .iter()
        .enumerate()
        .flat_map(|(pane, held)| {
            held.heads
                .iter()
                .enumerate()
                .map(move |(head, held)| (pane, head, held.name))
        })
        .filter(|&(_, _, name)| !named(name))
        .map(|(pane, head, _)| Spot::Head { pane, head });
    first(
        cells(shown.rendering)
            .filter(|&(_, cell)| ink(cell).is_some() && encoded(shown.frame, cell).is_none())
            .map(|(at, _)| Spot::Cell(at))
            .chain(heads),
    )
}

/// `no-decoration`: no background, no border, and no line drawn as text that
/// its datum does not hold.
///
/// # Specification
/// trivial.
fn no_decoration(shown: &Shown<'_>) -> Result<(), Spot>
{
    let ruled = |cell: &Cell| {
        let spelled = match encoded(shown.frame, cell).map(|field| &field.datum) {
            Some(&Datum::Text(ref text)) => text.as_str(),
            Some(_) | None => "",
        };
        cell.text
            .chars()
            .any(|drawn| ('\u{2500}' ..= '\u{257f}').contains(&drawn) && !spelled.contains(drawn))
    };
    first(
        cells(shown.rendering)
            .filter(|&(_, cell)| {
                ruled(cell)
                    || cell.attributes.iter().any(|attribute| {
                        matches!(*attribute, Attribute::Background(_) | Attribute::Border)
                    })
            })
            .map(|(at, _)| Spot::Cell(at)),
    )
}

/// `hue-is-warrant`: every hue a renderer paints names one of the five
/// warrant colours.
///
/// # Specification
/// trivial.
fn hue_is_warrant(shown: &Shown<'_>) -> Result<(), Spot>
{
    first(
        cells(shown.rendering)
            .filter(|&(_, cell)| {
                cell.attributes.iter().any(|attribute| match *attribute {
                    Attribute::Hue(colour) => {
                        !WARRANTS.iter().any(|warrant| warrant.colour() == colour)
                    },
                    Attribute::Bold
                    | Attribute::Italic
                    | Attribute::Faint
                    | Attribute::Opacity
                    | Attribute::Background(_)
                    | Attribute::Border
                    | Attribute::Blink => false,
                })
            })
            .map(|(at, _)| Spot::Cell(at)),
    )
}

/// `lightness-carries-nothing`: no shade and no opacity.
///
/// # Specification
/// trivial.
fn lightness_carries_nothing(shown: &Shown<'_>) -> Result<(), Spot>
{
    first(
        cells(shown.rendering)
            .filter(|&(_, cell)| {
                cell.attributes
                    .iter()
                    .any(|attribute| matches!(*attribute, Attribute::Faint | Attribute::Opacity))
            })
            .map(|(at, _)| Spot::Cell(at)),
    )
}

/// `quantity-is-length`: the datum of a quantity renders as a numeral or a
/// sparkline.
///
/// # Specification
/// trivial.
fn quantity_is_length(shown: &Shown<'_>) -> Result<(), Spot>
{
    first(
        cells(shown.rendering)
            .filter(|&(_, cell)| {
                cell.role == Role::Value
                    && ink(cell).is_some()
                    && encoded(shown.frame, cell)
                        .is_some_and(|field| quantity(&field.datum).is_some())
                    && cell.numeral.is_none()
                    && cell.sparkline.is_none()
            })
            .map(|(at, _)| Spot::Cell(at)),
    )
}

/// `small-multiples`: the sparklines of one column share one scale and one
/// window.
///
/// # Specification
/// trivial.
fn small_multiples(shown: &Shown<'_>) -> Result<(), Spot>
{
    first(columns(shown.rendering).flat_map(|column| {
        let mut held: Option<&Sparkline> = None;
        column
            .filter_map(|(at, cell)| Some((at, cell.sparkline.as_ref()?)))
            .filter(move |&(_, sparkline)| {
                let shared = *held.get_or_insert(sparkline);
                shared.scale != sparkline.scale || shared.window != sparkline.window
            })
            .map(|(at, _)| Spot::Cell(at))
    }))
}

/// `sparklines`: a sparkline is 32 block elements and its last value.
///
/// # Specification
/// trivial.
fn sparklines(shown: &Shown<'_>) -> Result<(), Spot>
{
    first(
        cells(shown.rendering)
            .filter(|&(_, cell)| {
                cell.sparkline.as_ref().is_some_and(|sparkline| {
                    let mut blocks = sparkline.cells.chars();
                    let filled = (0 .. SAMPLES)
                        .all(|_| blocks.next().is_some_and(|block| BLOCKS.contains(&block)));
                    !filled || blocks.next().is_some() || sparkline.last.text.is_empty()
                })
            })
            .map(|(at, _)| Spot::Cell(at)),
    )
}

/// `Some` when `numeral` matches its unit's pattern.
///
/// # Specification
/// trivial.
fn patterned(numeral: &Numeral) -> Option<()>
{
    // The integer part of a decimal of at most three significant digits.
    let decimal = |text: &str| -> Option<u128> {
        let (whole, fraction) = text.split_once('.').unwrap_or((text, ""));
        let digits = |part: &str| part.chars().all(|digit| digit.is_ascii_digit());
        if whole.is_empty()
            || !digits(whole)
            || !digits(fraction)
            || (text.contains('.') && fraction.is_empty())
            || (whole.len() > 1 && whole.starts_with('0'))
        {
            return None;
        }
        let leading = whole.trim_start_matches('0');
        let significant = if fraction.is_empty() {
            leading.trim_end_matches('0').len()
        }
        else if leading.is_empty() {
            fraction.trim_start_matches('0').len()
        }
        else {
            leading.len().saturating_add(fraction.len())
        };
        (significant <= 3).then_some(())?;
        Some(whole.parse::<u128>().unwrap_or(u128::MAX))
    };
    let text = numeral.text.as_str();
    match numeral.unit {
        Unit::Count => {
            let mantissa = text.trim_end_matches(['k', 'M', 'G', 'T', 'P', 'E']);
            let prefixed = mantissa.len() < text.len();
            let whole = decimal(mantissa)?;
            (mantissa.len().saturating_add(1) >= text.len()
                && (!prefixed || (1 ..= 999).contains(&whole)))
            .then_some(())
        },
        Unit::Microseconds | Unit::Bytes | Unit::Kibibytes => {
            let bound = if numeral.unit == Unit::Microseconds {
                1000
            }
            else {
                1024
            };
            (decimal(text)? < bound).then_some(())
        },
        Unit::Milliseconds | Unit::Mebibytes => decimal(text).map(|_whole| ()),
        Unit::Ratio => {
            let (hits, total) = text.split_once('/')?;
            let plain = |part: &str| {
                !part.is_empty()
                    && part.chars().all(|digit| digit.is_ascii_digit())
                    && (part.len() == 1 || !part.starts_with('0'))
            };
            (plain(hits) && plain(total)).then_some(())
        },
    }
}

/// `numerals`: every numeral matches its unit's pattern, and the numerals of
/// one column share one unit, which a pane with heads states at the column's
/// head.
///
/// # Specification
/// trivial.
fn numerals(shown: &Shown<'_>) -> Result<(), Spot>
{
    let unpatterned = cells(shown.rendering)
        .filter(|&(_, cell)| {
            cell.numeral
                .iter()
                .chain(
                    cell.sparkline
                        .iter()
                        .flat_map(|line| [&line.last, &line.scale, &line.window]),
                )
                .any(|numeral| patterned(numeral).is_none())
        })
        .map(|(at, _)| Spot::Cell(at));
    let mixed = columns(shown.rendering).flat_map(|column| {
        let mut held: Option<Unit> = None;
        column
            .filter_map(|(at, cell)| {
                let numeral = cell
                    .numeral
                    .as_ref()
                    .or_else(|| cell.sparkline.as_ref().map(|line| &line.last))?;
                Some((at, numeral.unit))
            })
            .filter(move |&(at, unit)| {
                let shared = *held.get_or_insert(unit);
                let headed = shown.rendering.panes.get(at.pane).is_some_and(|pane| {
                    pane.heads.is_empty()
                        || pane
                            .heads
                            .get(at.cell)
                            .is_some_and(|head| head.unit == Some(unit))
                });
                shared != unit || !headed
            })
            .map(|(at, _)| Spot::Cell(at))
    });
    first(unpatterned.chain(mixed))
}

/// Each column of each pane: its cells from the top row down, with their
/// positions.
///
/// # Specification
/// trivial.
fn columns(rendering: &Rendering) -> impl Iterator<Item = impl Iterator<Item = (At, &Cell)>>
{
    rendering.panes.iter().enumerate().flat_map(|(pane, held)| {
        let width = held
            .rows
            .iter()
            .map(|row| row.cells.len())
            .max()
            .unwrap_or_default();
        (0 .. width).map(move |cell| {
            held.rows.iter().enumerate().filter_map(move |(row, line)| {
                line.cells
                    .get(cell)
                    .map(|found| (At { pane, row, cell }, found))
            })
        })
    })
}

/// Each run of adjacent cells of a row that encode one field: the position
/// of its first cell, the field and the cells.
///
/// # Specification
/// trivial.
fn runs(rendering: &Rendering) -> impl Iterator<Item = (At, Place, &[Cell])>
{
    rendering.panes.iter().enumerate().flat_map(|(pane, held)| {
        held.rows.iter().enumerate().flat_map(move |(row, line)| {
            let mut cell = 0_usize;
            line.cells
                .chunk_by(|left, right| left.place == right.place)
                .filter_map(move |run| {
                    let at = At { pane, row, cell };
                    cell = cell.saturating_add(run.len());
                    Some((at, run.first()?.place?, run))
                })
        })
    })
}

/// `latency-is-two-numbers`: a latency renders its p50 and its p99 side by
/// side, or neither.
///
/// # Specification
/// trivial.
fn latency_is_two_numbers(shown: &Shown<'_>) -> Result<(), Spot>
{
    first(
        runs(shown.rendering)
            .filter(|&(_, place, run)| {
                let drawn = run.iter().filter(|cell| cell.numeral.is_some()).count();
                matches!(
                    field(shown.frame, place).map(|field| &field.datum),
                    Some(&Datum::Latency { .. })
                ) && drawn != 0
                    && drawn != 2
            })
            .map(|(at, ..)| Spot::Cell(at)),
    )
}

/// `ratio-is-a-pair`: a ratio renders as `hits/total`.
///
/// # Specification
/// trivial.
fn ratio_is_a_pair(shown: &Shown<'_>) -> Result<(), Spot>
{
    first(
        cells(shown.rendering)
            .filter(|&(_, cell)| {
                let Some(&Datum::Ratio { hits, total }) =
                    encoded(shown.frame, cell).map(|field| &field.datum)
                else {
                    return false;
                };
                let paired = cell
                    .numeral
                    .as_ref()
                    .filter(|numeral| numeral.unit == Unit::Ratio)
                    .and_then(|numeral| numeral.text.split_once('/'))
                    .is_some_and(|(drawn, out_of)| {
                        drawn.parse::<u64>().ok() == Some(hits.0)
                            && out_of.parse::<u64>().ok() == Some(total.0)
                    });
                cell.role == Role::Value && ink(cell).is_some() && !paired
            })
            .map(|(at, _)| Spot::Cell(at)),
    )
}

/// `change-in-place`: nothing blinks, and a cell whose field did not change
/// since the frame before is drawn where and as it was. A field that turned
/// stale changed, because `stale-is-pending` repaints it.
///
/// # Specification
/// trivial.
fn change_in_place(shown: &Shown<'_>) -> Result<(), Spot>
{
    let blinking = cells(shown.rendering)
        .filter(|&(_, cell)| cell.attributes.contains(&Attribute::Blink))
        .map(|(at, _)| Spot::Cell(at));
    let stale = |frame: &Frame, field: &Field| field.revision < frame.revision;
    let moved = shown
        .before
        .into_iter()
        .flat_map(move |(frame, rendering)| {
            cells(rendering)
                .filter(move |&(at, cell)| {
                    let kept = encoded(frame, cell).zip(encoded(shown.frame, cell));
                    kept.is_some_and(|(before, after)| {
                        before.datum == after.datum
                            && stale(frame, before) == stale(shown.frame, after)
                    }) && shown
                        .rendering
                        .panes
                        .get(at.pane)
                        .and_then(|pane| pane.rows.get(at.row))
                        .and_then(|row| row.cells.get(at.cell))
                        != Some(cell)
                })
                .map(|(at, _)| Spot::Cell(at))
        });
    first(blinking.chain(moved))
}

/// `density`: one line per row, no padding within a cell, and no row that
/// draws nothing.
///
/// # Specification
/// trivial.
fn density(shown: &Shown<'_>) -> Result<(), Spot>
{
    let padded = cells(shown.rendering)
        .filter(|&(_, cell)| {
            cell.text.contains(['\n', '\r']) || cell.text.trim() != cell.text.as_str()
        })
        .map(|(at, _)| Spot::Cell(at));
    let empty = shown
        .rendering
        .panes
        .iter()
        .enumerate()
        .flat_map(|(pane, held)| {
            held.rows
                .iter()
                .enumerate()
                .filter(|&(_, row)| row.cells.iter().all(|cell| ink(cell).is_none()))
                .map(move |(row, _)| Spot::Row { pane, row })
        });
    first(padded.chain(empty))
}

/// `alignment`: the rows of a pane have one cell per column, under its head
/// when the pane has heads; labels and texts sit left and numerals right.
///
/// # Specification
/// trivial.
fn alignment(shown: &Shown<'_>) -> Result<(), Spot>
{
    let ragged = shown
        .rendering
        .panes
        .iter()
        .enumerate()
        .flat_map(|(pane, held)| {
            let width = if held.heads.is_empty() {
                held.rows.first().map_or(0, |row| row.cells.len())
            }
            else {
                held.heads.len()
            };
            held.rows
                .iter()
                .enumerate()
                .filter(move |&(_, row)| row.cells.len() != width)
                .map(move |(row, _)| Spot::Row { pane, row })
        });
    let misplaced = cells(shown.rendering)
        .filter(|&(_, cell)| {
            let right = cell.numeral.is_some() || cell.sparkline.is_some();
            ink(cell).is_some() && (cell.align == Align::Right) != right
        })
        .map(|(at, _)| Spot::Cell(at));
    first(ragged.chain(misplaced))
}

/// `stale-is-pending`: a datum computed for an older revision than the
/// frame's renders in the `pending` hue and no other.
///
/// # Specification
/// trivial.
fn stale_is_pending(shown: &Shown<'_>) -> Result<(), Spot>
{
    let pending = Attribute::Hue(Warrant::Pending.colour());
    first(
        cells(shown.rendering)
            .filter(|&(_, cell)| {
                ink(cell).is_some()
                    && encoded(shown.frame, cell)
                        .is_some_and(|field| field.revision < shown.frame.revision)
                    && (!cell.attributes.contains(&pending)
                        || cell.attributes.iter().any(|attribute| {
                            matches!(*attribute, Attribute::Hue(_)) && *attribute != pending
                        }))
            })
            .map(|(at, _)| Spot::Cell(at)),
    )
}

/// `glyph-twins-hue`: every warrant mark carries its warrant's glyph.
///
/// # Specification
/// trivial.
fn glyph_twins_hue(shown: &Shown<'_>) -> Result<(), Spot>
{
    first(
        cells(shown.rendering)
            .filter(|&(_, cell)| {
                cell.warrant
                    .is_some_and(|warrant| cell.glyph != Some(warrant.glyph()))
            })
            .map(|(at, _)| Spot::Cell(at)),
    )
}

/// `labels-are-field-names`: a label spells the name of its field and
/// nothing else.
///
/// # Specification
/// trivial.
fn labels_are_field_names(shown: &Shown<'_>) -> Result<(), Spot>
{
    first(
        cells(shown.rendering)
            .filter(|&(_, cell)| {
                cell.role == Role::Label
                    && encoded(shown.frame, cell)
                        .is_none_or(|field| cell.text != <&str>::from(field.name))
            })
            .map(|(at, _)| Spot::Cell(at)),
    )
}

/// `absence-is-blank`: an absent datum draws nothing, not even its label.
///
/// # Specification
/// trivial.
fn absence_is_blank(shown: &Shown<'_>) -> Result<(), Spot>
{
    first(
        cells(shown.rendering)
            .filter(|&(_, cell)| {
                ink(cell).is_some()
                    && encoded(shown.frame, cell).is_some_and(|field| field.datum == Datum::Absent)
            })
            .map(|(at, _)| Spot::Cell(at)),
    )
}

/// `document-order`: the rows of a pane keep the frame's order.
///
/// # Specification
/// trivial.
fn document_order(shown: &Shown<'_>) -> Result<(), Spot>
{
    let mut last: Option<(usize, usize)> = None;
    first(
        cells(shown.rendering)
            .filter_map(|(at, cell)| Some((at, cell.place?.record)))
            .filter(|&(at, record)| {
                let held = last
                    .filter(|&(pane, _)| pane == at.pane)
                    .map(|(_, held)| held);
                last = Some((at.pane, held.map_or(record, |held| held.max(record))));
                held.is_some_and(|held| record < held)
            })
            .map(|(at, _)| Spot::Cell(at)),
    )
}

/// `comparison-in-eye-span`: a before and an after render as two cells side
/// by side in one row.
///
/// # Specification
/// trivial.
fn comparison_in_eye_span(shown: &Shown<'_>) -> Result<(), Spot>
{
    first(
        runs(shown.rendering)
            .filter(|&(_, place, run)| {
                let drawn = run
                    .iter()
                    .filter(|cell| cell.role == Role::Value && ink(cell).is_some())
                    .count();
                matches!(
                    field(shown.frame, place).map(|field| &field.datum),
                    Some(&Datum::Comparison { .. })
                ) && drawn != 0
                    && drawn != 2
            })
            .map(|(at, ..)| Spot::Cell(at)),
    )
}

/// `one-meaning-per-glyph`: every glyph is a warrant's or a derivation's, and
/// a warrant's own glyph marks that warrant alone.
///
/// # Specification
/// trivial.
fn one_meaning_per_glyph(shown: &Shown<'_>) -> Result<(), Spot>
{
    first(
        cells(shown.rendering)
            .filter(|&(_, cell)| {
                cell.glyph.is_some_and(|glyph| {
                    let owner = WARRANTS.iter().find(|warrant| warrant.glyph() == glyph);
                    !DERIVATION_GLYPHS.contains(&glyph)
                        && owner.is_none_or(|&warrant| cell.warrant != Some(warrant))
                })
            })
            .map(|(at, _)| Spot::Cell(at)),
    )
}

#[cfg(test)]
mod tests;
