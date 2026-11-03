//! The parser's report: today's grammar read on each axis a syntax candidate
//! is measured against, one Markdown table row per measure.
//!
//! Run with `mise run parser:report`, which builds it under the release
//! profile and writes `target/parser-report.md`.
//!
//! | Axis | Measure | Read from |
//! | ---- | ------- | --------- |
//! | throughput | bytes and significant tokens per second of the corpus's cold parse | each corpus source parsed [`RUNS`] times, the fastest run kept |
//! | recovery | each mutant's fate over the syntax exemplars | `gandr ledger recovery`'s sweep |
//! | ambiguity | each decision's settling stage, the candidates it read, and the windows and window tokens it molded | the molder's [`DecisionCensus`] over every corpus source |
//!
//! The corpus is the sweeps' corpus, its strict and fixture roots, listed by
//! `gandr-workflow-sweep`.

use core::fmt;
use core::fmt::Write as _;
use core::time::Duration;
use std::io;
use std::io::Write as _;
use std::path::Path;
use std::time::Instant;

use gandr_surface_dispatcher::LedgerRun;
use gandr_surface_dispatcher::LedgerTask;
use gandr_surface_dispatcher::RecoveryTally;
use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::PbgError;
use gandr_surface_grammar::built_in;
use gandr_surface_parser::DecisionCensus;
use gandr_surface_parser::DecisionCount;
use gandr_surface_parser::Lexeme;
use gandr_surface_parser::MeldError;
use gandr_surface_parser::MeldState;
use gandr_surface_parser::Molder;
use gandr_surface_parser::label;
use gandr_surface_parser::parse;
use gandr_surface_syntax::SourceFragment;
use gandr_surface_syntax::SourceText;
use gandr_workflow_sweep::SweepError;

/// How many times each source is parsed cold; the fastest run stands for it,
/// as the acceptance test's latency budget reads it.
const RUNS: u32 = 5;

/// The directory of syntax exemplars the recovery sweep mutates.
const EXEMPLARS: &str = "corpus/ledger";

/// Why the report stopped.
#[derive(Debug)]
enum Failure
{
    /// The built-in grammar did not build.
    Grammar(PbgError),
    /// The corpus could not be listed.
    Corpus(SweepError),
    /// A source could not be read, or the table not written.
    Io(io::Error),
    /// A parse could not assemble its tree.
    Parse(MeldError),
    /// The recovery sweep faulted, its fault rendered.
    Recovery(String),
}

impl From<PbgError> for Failure
{
    /// The grammar's fault.
    ///
    /// # Specification
    /// trivial.
    fn from(fault: PbgError) -> Self
    {
        Self::Grammar(fault)
    }
}

impl From<SweepError> for Failure
{
    /// The corpus listing's fault.
    ///
    /// # Specification
    /// trivial.
    fn from(fault: SweepError) -> Self
    {
        Self::Corpus(fault)
    }
}

impl From<io::Error> for Failure
{
    /// A read's or a write's refusal.
    ///
    /// # Specification
    /// trivial.
    fn from(fault: io::Error) -> Self
    {
        Self::Io(fault)
    }
}

impl From<MeldError> for Failure
{
    /// A parse's fault.
    ///
    /// # Specification
    /// trivial.
    fn from(fault: MeldError) -> Self
    {
        Self::Parse(fault)
    }
}

impl From<fmt::Error> for Failure
{
    /// The table's formatting refusal.
    ///
    /// # Specification
    /// trivial.
    fn from(fault: fmt::Error) -> Self
    {
        Self::Io(io::Error::other(fault))
    }
}

impl fmt::Display for Failure
{
    /// Writes why the report stopped.
    ///
    /// # Specification
    /// trivial.
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::Grammar(ref fault) => write!(f, "the built-in grammar did not build: {fault}"),
            Self::Corpus(ref fault) => write!(f, "the corpus could not be listed: {fault}"),
            Self::Io(ref fault) => write!(f, "a source or the table refused: {fault}"),
            Self::Parse(ref fault) => write!(f, "a parse could not assemble its tree: {fault}"),
            Self::Recovery(ref fault) => write!(f, "the recovery sweep faulted: {fault}"),
        }
    }
}

impl core::error::Error for Failure
{
}

/// A count the report reads.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
struct Tally(usize);

impl Tally
{
    /// This count and `more`.
    ///
    /// # Specification
    /// trivial.
    const fn and(
        self,
        more: Self,
    ) -> Self
    {
        Self(self.0.saturating_add(more.0))
    }
}

impl From<DecisionCount> for Tally
{
    /// The census's count.
    ///
    /// # Specification
    /// trivial.
    fn from(count: DecisionCount) -> Self
    {
        Self(count.0)
    }
}

impl fmt::Display for Tally
{
    /// Writes the count.
    ///
    /// # Specification
    /// trivial.
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(f, "{}", self.0)
    }
}

/// A part of a whole, written as a percentage with one decimal, `48.0%`.
#[derive(Clone, Copy, Debug)]
struct Share
{
    /// The part.
    part: Tally,
    /// The whole.
    whole: Tally,
}

impl fmt::Display for Share
{
    /// Writes the percentage, `0.0%` of an empty whole.
    ///
    /// # Specification
    /// trivial.
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        let tenths = self
            .part
            .0
            .saturating_mul(1000)
            .checked_div(self.whole.0)
            .unwrap_or(0);
        write!(
            f,
            "{}.{}%",
            tenths.checked_div(10).unwrap_or(0),
            tenths.checked_rem(10).unwrap_or(0)
        )
    }
}

/// A count per unit of another, written with two decimals, `3.24`.
#[derive(Clone, Copy, Debug)]
struct Ratio
{
    /// The count.
    part: Tally,
    /// The units it is spread over.
    whole: Tally,
}

impl fmt::Display for Ratio
{
    /// Writes the ratio, `0.00` over no unit.
    ///
    /// # Specification
    /// trivial.
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        let hundredths = self
            .part
            .0
            .saturating_mul(100)
            .checked_div(self.whole.0)
            .unwrap_or(0);
        write!(
            f,
            "{}.{:02}",
            hundredths.checked_div(100).unwrap_or(0),
            hundredths.checked_rem(100).unwrap_or(0)
        )
    }
}

/// A count over a wall time, written per second in whole units.
#[derive(Clone, Copy, Debug)]
struct PerSecond
{
    /// The count.
    count: Tally,
    /// The wall time it took.
    wall: Duration,
}

impl fmt::Display for PerSecond
{
    /// Writes the rate, `0` over no time.
    ///
    /// # Specification
    /// trivial.
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        let count = u128::try_from(self.count.0).unwrap_or(u128::MAX);
        let rate = count
            .saturating_mul(1_000_000_000)
            .checked_div(self.wall.as_nanos())
            .unwrap_or(0);
        write!(f, "{rate}")
    }
}

/// What the corpus's cold parse cost.
#[derive(Clone, Copy, Debug, Default)]
struct Throughput
{
    /// The sources parsed.
    sources: Tally,
    /// The bytes parsed.
    bytes: Tally,
    /// The significant tokens parsed.
    tokens: Tally,
    /// The fastest run of each source, summed.
    wall: Duration,
}

/// Mold `text` once, adding the molder's census to `census`, and count its
/// significant tokens.
///
/// # Specification
/// trivial.
fn census_of(
    pbg: &Pbg,
    text: SourceText<'_>,
    census: &mut DecisionCensus,
) -> Tally
{
    let mut molder = Molder::new(pbg);
    let mut state = MeldState::new(pbg);
    let tokens = label(SourceFragment::from(<&str>::from(text)));
    molder.mold_stream(&mut state, &tokens, text);
    let read = molder.census();
    let add = |total: &mut DecisionCount, more: DecisionCount| {
        total.0 = total.0.saturating_add(more.0);
    };
    add(&mut census.sole, read.sole);
    add(&mut census.least_key, read.least_key);
    add(&mut census.opener, read.opener);
    add(&mut census.next_token, read.next_token);
    add(&mut census.window, read.window);
    add(&mut census.candidates, read.candidates);
    add(&mut census.windows, read.windows);
    add(&mut census.window_tokens, read.window_tokens);
    Tally(
        tokens
            .iter()
            .filter(|token| token.lexeme != Lexeme::Space)
            .count(),
    )
}

/// The fastest of [`RUNS`] cold parses of `text`.
///
/// # Specification
/// trivial.
fn fastest_parse(
    pbg: &Pbg,
    text: SourceText<'_>,
) -> Result<Duration, Failure>
{
    let mut best = Duration::MAX;
    for _ in 0 .. RUNS {
        let start = Instant::now();
        let parsed = parse(pbg, text)?;
        let wall = start.elapsed();
        drop(core::hint::black_box(parsed));
        best = best.min(wall);
    }
    Ok(best)
}

/// The recovery sweep's tally over [`EXEMPLARS`], from the repository root.
///
/// # Specification
/// trivial.
fn recovery() -> Result<RecoveryTally, Failure>
{
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let task = LedgerTask::Recovery {
        directory: root.join(EXEMPLARS),
    };
    match task
        .run()
        .map_err(|fault| Failure::Recovery(fault.to_string()))?
    {
        LedgerRun::Swept(report) => Ok(report.tally()),
        LedgerRun::Written(_)
        | LedgerRun::Verified(_)
        | LedgerRun::Listed(_)
        | LedgerRun::Shown(_) => Err(Failure::Recovery(String::from(
            "the task answered no sweep",
        ))),
    }
}

/// Read every axis this report holds and print its table.
///
/// # Specification
/// trivial.
fn main() -> Result<(), Failure>
{
    let pbg = built_in()?;
    let mut throughput = Throughput::default();
    let mut census = DecisionCensus::default();
    for source in gandr_workflow_sweep::corpus::sources()? {
        let text = std::fs::read_to_string(&source.path)?;
        let text = SourceText::from(text.as_str());
        let tokens = census_of(&pbg, text, &mut census);
        throughput.wall = throughput.wall.saturating_add(fastest_parse(&pbg, text)?);
        throughput.sources = throughput.sources.and(Tally(1));
        throughput.bytes = throughput.bytes.and(Tally(<&str>::from(text).len()));
        throughput.tokens = throughput.tokens.and(tokens);
    }
    let tally = recovery()?;
    let swept = Tally(tally.swept);
    let of_swept = |part: usize| Share {
        part: Tally(part),
        whole: swept,
    };
    let decisions = Tally::from(census.decisions());
    let of_decisions = |part: DecisionCount| Share {
        part: Tally::from(part),
        whole: decisions,
    };
    let mut table = String::from("| Axis | Measure | Reading |\n| --- | --- | --- |\n");
    let rows: [(&str, &str, &dyn fmt::Display); 19] = [
        ("throughput", "sources", &throughput.sources),
        ("throughput", "bytes", &throughput.bytes),
        ("throughput", "significant tokens", &throughput.tokens),
        (
            "throughput",
            "cold parse, ms, the fastest of each source's runs summed",
            &throughput.wall.as_millis(),
        ),
        ("throughput", "bytes per second", &PerSecond {
            count: throughput.bytes,
            wall: throughput.wall,
        }),
        ("throughput", "significant tokens per second", &PerSecond {
            count: throughput.tokens,
            wall: throughput.wall,
        }),
        ("recovery", "mutants swept", &swept),
        (
            "recovery",
            "marked where they were made",
            &of_swept(tally.where_made),
        ),
        ("recovery", "accepted", &of_swept(tally.accepted)),
        (
            "recovery",
            "well formed and refused",
            &of_swept(tally.formed),
        ),
        ("recovery", "closed early", &of_swept(tally.early)),
        ("recovery", "marked elsewhere", &of_swept(tally.elsewhere)),
        ("ambiguity", "decisions", &decisions),
        (
            "ambiguity",
            "settled by one admissible mold",
            &of_decisions(census.sole),
        ),
        (
            "ambiguity",
            "settled by the least local key",
            &of_decisions(census.least_key),
        ),
        (
            "ambiguity",
            "settled by refuting or folding tied openers",
            &of_decisions(census.opener),
        ),
        (
            "ambiguity",
            "settled by the next token",
            &of_decisions(census.next_token),
        ),
        (
            "ambiguity",
            "settled by a lookahead window",
            &of_decisions(census.window),
        ),
        ("ambiguity", "candidates per decision", &Ratio {
            part: Tally::from(census.candidates),
            whole: decisions,
        }),
    ];
    for (axis, measure, reading) in rows {
        writeln!(table, "| {axis} | {measure} | {reading} |")?;
    }
    writeln!(
        table,
        "| ambiguity | windows per windowed decision | {} |",
        Ratio {
            part: Tally::from(census.windows),
            whole: Tally::from(census.window),
        }
    )?;
    writeln!(
        table,
        "| ambiguity | window tokens per decision | {} |",
        Ratio {
            part: Tally::from(census.window_tokens),
            whole: decisions,
        }
    )?;
    io::stdout().write_all(table.as_bytes())?;
    Ok(())
}
