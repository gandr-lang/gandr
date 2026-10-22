//! The nightly rotation: the slice of its inputs a rotating sweep visits on a
//! night, so each costly sweep covers the whole corpus over the [`Nights`] it
//! states, inside the nightly budget.

use core::fmt;
use std::time::SystemTime;

use anodized::spec;

use crate::corpus::Source;
use crate::coverage::NIGHTLY_PROFILE;
use crate::coverage::PROFILE;
use crate::coverage::Profile;
use crate::error::SweepError;
use crate::sample::SampleName;

/// The variable naming the night a run visits, in whole UTC days since the
/// Unix epoch; unset, the night the run starts in.
pub const NIGHT: &str = "GANDR_SWEEP_NIGHT";

/// Seconds in a night: a night is a UTC day.
const DAY: u64 = 86_400;

/// A night: whole UTC days since the Unix epoch.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Night(pub u64);

/// Which of a rotation's slices a night visits: its day number modulo the
/// rotation's [`Nights`].
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Slice(pub u64);

/// How many nights a rotating sweep takes to visit all of its inputs.
///
/// One slice of the corpus, or one part of each text, a night, and all of
/// them every `nights` nights. Each rotating sweep states its own, its whole
/// cost over its share of the nightly budget; zero is one night, the whole.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Nights(pub u64);

/// Whether a night's slice holds a source.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Held
{
    /// The run visits the source.
    Tonight,
    /// Another night of the rotation visits it.
    Elsewhen,
}

/// A text a sweep covers part by part.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Text<'text>(pub &'text str);

/// A byte offset into a [`Text`].
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Offset(pub usize);

/// The bytes of a [`Text`] from `start` to `end`, a night covers.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Part
{
    /// Where the part starts: a line start, or the text's start.
    pub start: Offset,
    /// Where the part ends: the next part's start, or the text's end.
    pub end: Offset,
}

impl Night
{
    /// The night `now` falls in.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the whole days between the Unix epoch and `now`.
    /// - provides: the night a run without [`NIGHT`] visits.
    /// - fails: [`SweepError::Night`] when `now` precedes the epoch.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`SweepError::Night`]: `now` precedes the Unix epoch.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the epoch, the last second of its day, the first of
    ///   the next and a time before the epoch; a rounded division or a
    ///   saturated subtraction changes an answer.
    /// - witness: `rotation::tests::a_night_is_a_utc_day`
    #[spec(ensures: |ret| ret.as_ref().map_or(now < SystemTime::UNIX_EPOCH, |night| now.duration_since(SystemTime::UNIX_EPOCH).is_ok_and(|since| since.as_secs().checked_div(DAY) == Some(night.0))))]
    #[inline]
    pub fn of(now: SystemTime) -> Result<Self, SweepError>
    {
        let since = now
            .duration_since(SystemTime::UNIX_EPOCH)
            .map_err(|error| SweepError::Night {
                spelled: String::from("the clock"),
                detail: error.to_string(),
            })?;
        let days = since.as_secs().checked_div(DAY).unwrap_or_default();
        Ok(Self(days))
    }

    /// The night [`NIGHT`] names, or the one the clock is in when it is unset.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`NIGHT`]'s value read as a day number when it is set;
    ///   [`Night::of`] the clock otherwise.
    /// - provides: the night a nightly run visits, replayable by setting
    ///   [`NIGHT`].
    /// - fails: [`SweepError::Night`] when [`NIGHT`] is not a day number or the
    ///   clock precedes the epoch.
    /// - panics: none.
    /// - executable: none — the outcome is the environment's and the clock's.
    ///
    /// # Errors
    /// - [`SweepError::Night`]: as `fails` lists.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — [`Night::of`] carries the clock's arithmetic; this
    ///   reads one variable, which the nightly sweeps run under.
    /// - witness: `rotation::tests::a_night_is_a_utc_day`
    #[inline]
    pub fn asked() -> Result<Self, SweepError>
    {
        match std::env::var(NIGHT) {
            Ok(spelled) => spelled
                .parse()
                .map(Self)
                .map_err(|error: core::num::ParseIntError| SweepError::Night {
                    detail: error.to_string(),
                    spelled,
                }),
            Err(std::env::VarError::NotPresent) => Self::of(SystemTime::now()),
            Err(error @ std::env::VarError::NotUnicode(_)) => Err(SweepError::Night {
                spelled: String::from(NIGHT),
                detail: error.to_string(),
            }),
        }
    }

    /// The slice this night visits of a rotation over `nights`, below
    /// `nights`; the only slice, zero, when `nights` is zero.
    ///
    /// # Specification
    /// trivial.
    const fn slice(
        self,
        nights: Nights,
    ) -> Slice
    {
        match self.0.checked_rem(nights.0) {
            Some(slice) => Slice(slice),
            None => Slice(0),
        }
    }
}

/// Which of its inputs a rotating sweep visits under a whole profile.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Rotation
{
    /// Every input: the `sweeps` profile, a re-record, and every sampled run,
    /// whose sample draws from every input.
    Whole,
    /// The night's slice: the nightly profile.
    Night(Night),
}

impl Rotation
{
    /// The rotation of a run under `profile` on `night`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Rotation::Night`] of `night` exactly under
    ///   [`NIGHTLY_PROFILE`]; [`Rotation::Whole`] otherwise.
    /// - provides: the decision between the whole corpus and the night's slice.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the nightly profile, the `sweeps` profile and a
    ///   pull-request one; a rotation under another profile, or a night other
    ///   than the one given, changes an answer.
    /// - witness: `rotation::tests::only_the_nightly_profile_rotates`
    #[spec(ensures: |ret| (ret == Self::Night(night)) == (profile.0 == NIGHTLY_PROFILE) && (ret == Self::Whole) == (profile.0 != NIGHTLY_PROFILE))]
    #[inline]
    #[must_use]
    pub fn of(
        profile: Profile<'_>,
        night: Night,
    ) -> Self
    {
        if profile.0 == NIGHTLY_PROFILE {
            Self::Night(night)
        }
        else {
            Self::Whole
        }
    }

    /// The rotation the running nextest profile asks for: the night's slice
    /// under [`NIGHTLY_PROFILE`], the whole corpus otherwise.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Rotation::of`] the profile `NEXTEST_PROFILE` names and
    ///   [`Night::asked`], read only under [`NIGHTLY_PROFILE`].
    /// - provides: what [`Sweep::asked`] reads under a whole profile.
    /// - fails: as [`Night::asked`], under [`NIGHTLY_PROFILE`] alone.
    /// - panics: none.
    /// - executable: none — the outcome is the environment's and the clock's.
    ///
    /// # Errors
    /// - [`SweepError::Night`]: as [`Night::asked`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — [`Rotation::of`] and [`Night::asked`] carry the
    ///   decisions; this joins them.
    /// - witness: `rotation::tests::only_the_nightly_profile_rotates`
    ///
    /// [`Sweep::asked`]: crate::Sweep::asked
    #[inline]
    pub fn asked() -> Result<Self, SweepError>
    {
        let profile = std::env::var(PROFILE).unwrap_or_default();
        if profile == NIGHTLY_PROFILE {
            let night = Night::asked()?;
            Ok(Self::of(Profile(&profile), night))
        }
        else {
            Ok(Self::Whole)
        }
    }

    /// Whether the sweep `salt` names, rotating over `nights`, visits
    /// `source` under this rotation.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Held::Tonight`] under [`Rotation::Whole`] and when `nights`
    ///   is zero; otherwise under [`Rotation::Night`], [`Held::Tonight`]
    ///   exactly when the first eight bytes of the BLAKE3 digest of `rotation`,
    ///   a zero byte, `salt`, a zero byte and `source`'s name, read
    ///   little-endian, leave the night's remainder modulo `nights`,
    ///   [`Held::Elsewhen`] otherwise.
    /// - provides: a partition of every corpus into `nights` slices, the same
    ///   on every machine, salted per sweep so two sweeps spread their
    ///   costliest sources over different nights, and moved by nothing but the
    ///   source added or removed when the corpus changes.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a corpus of forty sources over three and over twelve
    ///   consecutive nights and the nights after them; a source in no slice or
    ///   in two, a night that does not wrap, a night count ignored, an unsalted
    ///   digest, or a whole rotation that drops a source fails the witness.
    /// - witness: `rotation::tests::the_nights_partition_the_corpus`
    #[spec(ensures: |ret| (self != Self::Whole && nights.0 != 0) || ret == Held::Tonight)]
    #[inline]
    #[must_use]
    pub fn holds(
        self,
        salt: SampleName,
        nights: Nights,
        source: &Source,
    ) -> Held
    {
        match self {
            Self::Whole => Held::Tonight,
            Self::Night(night) => {
                let mut hasher = blake3::Hasher::new();
                let _domain = hasher.update(b"rotation\0");
                let _salt = hasher.update(salt.0.as_bytes());
                let _separator = hasher.update(&[0]);
                let _source = hasher.update(source.name.as_ref().as_bytes());
                let digest = hasher.finalize();
                let word = digest
                    .as_bytes()
                    .first_chunk::<8>()
                    .map_or(0, |bytes| u64::from_le_bytes(*bytes));
                if word.checked_rem(nights.0).unwrap_or_default() == night.slice(nights).0 {
                    Held::Tonight
                }
                else {
                    Held::Elsewhen
                }
            },
        }
    }

    /// The part of `text` a sweep that rotates within each source covers
    /// under this rotation: all of it under [`Rotation::Whole`], and under
    /// [`Rotation::Night`] the night's part of `nights` consecutive parts, cut
    /// at line starts so that each costs about the same for a sweep whose
    /// work at an offset grows with the offset. The night's part is its day
    /// number modulo `nights`, so the parts turn over every `nights` nights.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: all of `text` under [`Rotation::Whole`]; under
    ///   [`Rotation::Night`], the range from cut `j` to cut `j + 1`, `j` the
    ///   night's day number modulo `nights`, where cut `j` of `nights` is the
    ///   first line start at or past `len × √(j / nights)`, cut 0 is 0 and cut
    ///   `nights` is the text's end; one part, the whole text, when `nights` is
    ///   zero.
    /// - provides: `nights` consecutive parts over `nights` consecutive nights
    ///   that partition the text, each starting at a line start or at the
    ///   text's end, each costing about a `nights`th of a sweep whose work is
    ///   quadratic in the text's length — the typing sweep, which checks the
    ///   text typed so far at every keystroke.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a text of equal lines and one without a newline over
    ///   four and over sixteen consecutive nights, and the whole rotation; a
    ///   gap or an overlap between parts, a cut off a line start, a linear cut,
    ///   a night count ignored, or a night that does not wrap fails the
    ///   witness.
    /// - witness: `rotation::tests::the_nights_part_a_text_at_line_starts`
    #[spec(ensures: |ret| ret.start <= ret.end && ret.end.0 <= text.0.len() && (ret.start.0 == 0 || ret.start.0 == text.0.len() || text.0.as_bytes().get(ret.start.0.saturating_sub(1)) == Some(&b'\n')))]
    #[inline]
    #[must_use]
    pub fn part(
        self,
        text: Text<'_>,
        nights: Nights,
    ) -> Part
    {
        match self {
            Self::Night(night) if nights.0 > 0 => {
                let slice = night.slice(nights);
                Part {
                    start: cut(text, slice, nights),
                    end: cut(text, Slice(slice.0.saturating_add(1)), nights),
                }
            },
            Self::Whole | Self::Night(_) => Part {
                start: Offset(0),
                end: Offset(text.0.len()),
            },
        }
    }
}

/// Where part `of` of `parts` of `text` starts: the first line start at or
/// past `len × √(of / parts)`, the text's end from `parts` on.
///
/// # Specification
/// trivial.
fn cut(
    text: Text<'_>,
    of: Slice,
    parts: Nights,
) -> Offset
{
    if of.0 >= parts.0 {
        return Offset(text.0.len());
    }
    let length = u64::try_from(text.0.len()).unwrap_or(u64::MAX);
    let squared = length
        .saturating_mul(length)
        .saturating_mul(of.0)
        .checked_div(parts.0)
        .unwrap_or_default();
    let target = usize::try_from(squared.isqrt()).unwrap_or(text.0.len());
    if target == 0 {
        return Offset(0);
    }
    Offset(
        text.0
            .as_bytes()
            .get(target.saturating_sub(1) ..)
            .and_then(|rest| rest.iter().position(|&byte| byte == b'\n'))
            .map_or(text.0.len(), |newline| target.saturating_add(newline)),
    )
}

impl fmt::Display for Rotation
{
    /// Names what the rotation visits, and under a night how to replay it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes one line: no rotation, or the night and the [`NIGHT`]
    ///   setting that replays it.
    /// - provides: the line a rotating sweep prints, so its failure names its
    ///   night.
    /// - fails: propagates the formatter's own write failure.
    /// - panics: none.
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — both variants rendered; a dropped night or a swapped
    ///   variant changes the asserted line.
    /// - witness: `rotation::tests::a_night_names_its_replay`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::Whole => f.write_str("no nightly rotation"),
            Self::Night(night) => {
                write!(f, "night {}; replay it with {NIGHT}={}", night.0, night.0)
            },
        }
    }
}

#[cfg(test)]
mod tests
{
    use core::ops::Range;
    use core::time::Duration;
    use std::path::PathBuf;
    use std::time::SystemTime;

    use super::Held;
    use super::Night;
    use super::Nights;
    use super::Part;
    use super::Rotation;
    use super::Text;
    use crate::corpus::Class;
    use crate::corpus::CorpusName;
    use crate::corpus::Source;
    use crate::coverage::Profile;
    use crate::error::SweepError;
    use crate::sample::SampleName;

    /// Forty model sources, nowhere on disk.
    ///
    /// # Specification
    /// trivial.
    fn corpus() -> Vec<Source>
    {
        (0_u8 .. 40_u8)
            .map(|index| {
                let name = CorpusName::from(format!("fixture/model/m{index:02}.gandr").as_str());
                Source {
                    path: PathBuf::from(name.as_ref()),
                    class: Class::of(&name),
                    name,
                }
            })
            .collect()
    }

    #[test]
    fn the_nights_partition_the_corpus()
    {
        let corpus = corpus();
        let salt = SampleName("a sweep");
        let tonight = |rotation: Rotation, salt, nights| -> Vec<&CorpusName> {
            corpus
                .iter()
                .filter(|source| rotation.holds(salt, nights, source) == Held::Tonight)
                .map(|source| &source.name)
                .collect()
        };
        for count in [3, 12] {
            let nights = Nights(count);
            let slices: Vec<Vec<&CorpusName>> = (0 .. count)
                .map(|night| tonight(Rotation::Night(Night(night)), salt, nights))
                .collect();
            for source in &corpus {
                assert_eq!(
                    slices
                        .iter()
                        .filter(|slice| slice.contains(&&source.name))
                        .count(),
                    1,
                    "{} sits in exactly one of {count} nights' slices",
                    source.name
                );
            }
            assert!(
                slices
                    .iter()
                    .filter(|slice| !slice.is_empty())
                    .nth(1)
                    .is_some(),
                "the forty sources spread over the {count} nights: {slices:?}"
            );
            for (night, slice) in (0 .. count).zip(&slices) {
                assert_eq!(
                    &tonight(Rotation::Night(Night(night + count)), salt, nights),
                    slice,
                    "night {night} recurs {count} nights on"
                );
            }
            assert_ne!(
                slices.first(),
                Some(&tonight(
                    Rotation::Night(Night(0)),
                    SampleName("another sweep"),
                    nights
                )),
                "the sweep's name salts its slices"
            );
        }
        assert_ne!(
            tonight(Rotation::Night(Night(0)), salt, Nights(3)).len(),
            tonight(Rotation::Night(Night(0)), salt, Nights(12)).len(),
            "the night count sizes the slice"
        );
        for (rotation, nights) in [
            (Rotation::Whole, Nights(12)),
            (Rotation::Night(Night(5)), Nights(0)),
            (Rotation::Night(Night(5)), Nights(1)),
        ] {
            assert_eq!(
                tonight(rotation, salt, nights).len(),
                corpus.len(),
                "{rotation} over {nights:?} visits every source"
            );
        }
    }

    #[test]
    fn only_the_nightly_profile_rotates()
    {
        assert_eq!(
            Rotation::of(Profile("nightly"), Night(20_379)),
            Rotation::Night(Night(20_379))
        );
        for profile in ["sweeps", "ci-enforcing", "default", ""] {
            assert_eq!(
                Rotation::of(Profile(profile), Night(20_379)),
                Rotation::Whole,
                "{profile}"
            );
        }
        let asked = Rotation::asked().expect("the run's rotation resolves");
        let nightly = std::env::var("NEXTEST_PROFILE").is_ok_and(|profile| profile == "nightly");
        assert_eq!(matches!(asked, Rotation::Night(_)), nightly);
    }

    #[test]
    fn a_night_is_a_utc_day()
    {
        let at = |seconds| {
            Night::of(SystemTime::UNIX_EPOCH + Duration::from_secs(seconds))
                .expect("after the epoch")
        };
        assert_eq!(at(0), Night(0));
        assert_eq!(at(86_399), Night(0), "the last second of the first day");
        assert_eq!(at(86_400), Night(1), "the first second of the next");
        assert_eq!(at(1_760_745_600), Night(20_379), "2025-10-18T00:00:00Z");
        assert!(
            matches!(
                Night::of(SystemTime::UNIX_EPOCH - Duration::from_secs(1)),
                Err(SweepError::Night { .. })
            ),
            "a clock before the epoch is refused"
        );
    }

    #[test]
    fn a_night_names_its_replay()
    {
        assert_eq!(Rotation::Whole.to_string(), "no nightly rotation");
        assert_eq!(
            Rotation::Night(Night(20_379)).to_string(),
            "night 20379; replay it with GANDR_SWEEP_NIGHT=20379"
        );
    }

    #[test]
    fn the_nights_part_a_text_at_line_starts()
    {
        let span = |part: Part| part.start.0 .. part.end.0;
        let line = "abcdefghi\n";
        let text = line.repeat(100);
        let parted = |text: &str, nights: Nights| -> Vec<Range<usize>> {
            (0 .. nights.0)
                .map(|night| span(Rotation::Night(Night(night)).part(Text(text), nights)))
                .collect()
        };
        for count in [4, 16] {
            let parts = parted(&text, Nights(count));
            assert_eq!(parts.first().map(|part| part.start), Some(0));
            assert_eq!(parts.last().map(|part| part.end), Some(text.len()));
            for pair in parts.windows(2) {
                let &[ref earlier, ref later] = pair
                else {
                    continue;
                };
                assert_eq!(
                    earlier.end, later.start,
                    "{parts:?} leave no gap and no overlap"
                );
            }
            for part in &parts {
                assert!(
                    part.start == 0 || text.as_bytes().get(part.start - 1) == Some(&b'\n'),
                    "{part:?} starts at a line start"
                );
            }
        }
        // Typing to offset `n` checks every prefix up to it, so a part from
        // `a` to `b` costs about `b² - a²`: with the cuts at 500, 710 and 870
        // of 1000 bytes, each of four parts costs a quarter, within a line.
        assert_eq!(
            parted(&text, Nights(4)),
            [0 .. 500, 500 .. 710, 710 .. 870, 870 .. 1000],
            "the cuts fall at √(j/4) of the text, on the next line start"
        );
        let cuts = [
            0, 250, 360, 440, 500, 560, 620, 670, 710, 750, 790, 830, 870, 910, 940, 970, 1000,
        ];
        assert_eq!(
            parted(&text, Nights(16)),
            cuts.iter()
                .zip(cuts.iter().skip(1))
                .map(|(&from, &to)| from .. to)
                .collect::<Vec<_>>(),
            "the cuts fall at √(j/16) of the text, on the next line start"
        );
        assert_eq!(
            span(Rotation::Night(Night(4 + 1)).part(Text(&text), Nights(4))),
            500 .. 710,
            "four parts recur four nights on"
        );
        assert_eq!(
            span(Rotation::Night(Night(16 + 1)).part(Text(&text), Nights(16))),
            250 .. 360,
            "sixteen parts recur sixteen nights on"
        );
        let unbroken = "x".repeat(64);
        assert_eq!(
            parted(&unbroken, Nights(4)),
            [0 .. 64, 64 .. 64, 64 .. 64, 64 .. 64],
            "a text without a line break is one part"
        );
        assert_eq!(
            span(Rotation::Whole.part(Text(&text), Nights(16))),
            0 .. text.len()
        );
        assert_eq!(
            span(Rotation::Night(Night(3)).part(Text(&text), Nights(0))),
            0 .. text.len(),
            "no night count is one part"
        );
    }
}
