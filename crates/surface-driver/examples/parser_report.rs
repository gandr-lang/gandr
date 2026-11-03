//! The parser's report: today's grammar read on each axis a syntax candidate
//! is measured against, one Markdown table row per measure.
//!
//! Run with `mise run parser:report`, which builds it under the release
//! profile and writes `target/parser-report.md`.
//!
//! | Axis | Measure | Read from |
//! | ---- | ------- | --------- |
//! | latency | each keystroke's time from its change to its settled answer, p50 and p99 | a language-server session per [`SAMPLE`] source, one line typed back a character per change |
//! | throughput | bytes and significant tokens per second of the corpus's cold parse | each corpus source parsed [`RUNS`] times, the fastest run kept |
//! | recovery | each mutant's fate over the syntax exemplars | `gandr ledger recovery`'s sweep |
//! | ambiguity | each decision's settling stage, the candidates it read, and the windows and window tokens it molded | the molder's [`DecisionCensus`] over every corpus source |
//! | incremental | per edit, the tokens re-labelled and the forms re-molded against what the edit touches | a form store per [`SAMPLE`] source, through the latency workload's keystrokes and the edit sweep's form edits |
//!
//! The corpus is the sweeps' corpus, its strict and fixture roots, listed by
//! `gandr-workflow-sweep`. The latency workload's client is the benchmark
//! report's (`benches/shared/lsp.rs`).

#[path = "../benches/shared/lsp.rs"]
mod lsp;

use core::fmt;
use core::fmt::Write as _;
use core::time::Duration;
use std::io;
use std::io::Write as _;
use std::path::Path;
use std::time::Instant;

use gandr_core_fork::Serial;
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
use gandr_surface_session::FormStore;
use gandr_surface_syntax::SourceFragment;
use gandr_surface_syntax::SourceText;
use gandr_workflow_sweep::SweepError;
use quenchant_shape::shape::Maybe;

/// How many times each source is parsed cold; the fastest run stands for it,
/// as the acceptance test's latency budget reads it.
const RUNS: u32 = 5;

/// The directory of syntax exemplars the recovery sweep mutates.
const EXEMPLARS: &str = "corpus/ledger";

/// The latency workload's sources, from the repository root: eight model
/// sources from 1.3 kB to 15 kB, the largest model closure among them. Every
/// candidate types the same keystrokes into them.
const SAMPLE: [&str; 8] = [
    "corpus/model/deployments/offers.gandr",
    "corpus/model/control/accessor-place.gandr",
    "corpus/model/universe/decoded-descent.gandr",
    "corpus/model/identity/group-laws.gandr",
    "corpus/model/modules/prelude-resolve.gandr",
    "corpus/model/identity/model-counter-manifest.gandr",
    "corpus/model/desc/lc/model-record.gandr",
    "corpus/model/specification/niche-realizability.gandr",
];

/// The least code a typed line holds past its indentation: the workload types
/// the first line at or after a source's middle that holds this much and is
/// no comment.
const TYPED: usize = 20;

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
    /// A latency session stopped before its keystrokes were answered.
    Session(lsp::Fault),
    /// A sample source holds no line the latency workload types, by its path.
    Untyped(&'static str),
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

impl From<lsp::Fault> for Failure
{
    /// A latency session's fault.
    ///
    /// # Specification
    /// trivial.
    fn from(fault: lsp::Fault) -> Self
    {
        Self::Session(fault)
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
            Self::Session(ref fault) => write!(f, "a latency session stopped: {fault}"),
            Self::Untyped(path) => write!(
                f,
                "`{path}` holds no line of {TYPED} code characters at or after its middle"
            ),
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

/// A wall time written in milliseconds with one decimal, `61.3`.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Millis(Duration);

impl fmt::Display for Millis
{
    /// Writes the time in tenths of a millisecond, rounded down.
    ///
    /// # Specification
    /// trivial.
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        let tenths = self.0.as_micros().checked_div(100).unwrap_or(0);
        write!(
            f,
            "{}.{}",
            tenths.checked_div(10).unwrap_or(0),
            tenths.checked_rem(10).unwrap_or(0)
        )
    }
}

/// What the latency workload read: how many keystrokes it typed, and the
/// median and the 99th percentile of their times to a settled answer.
#[derive(Clone, Copy, Debug)]
struct Latency
{
    /// The keystrokes typed over every sample source.
    keystrokes: Tally,
    /// The nearest-rank median.
    p50: Duration,
    /// The nearest-rank 99th percentile.
    p99: Duration,
}

/// Why a source yields no keystrokes.
#[derive(Clone, Copy, Debug)]
enum Untyped
{
    /// No line at or after the source's middle holds [`TYPED`] code
    /// characters past its indentation outside a comment.
    NoLine,
}

/// The texts one sample source passes through: the text it opens at, and the
/// text after each keystroke.
struct Keystrokes
{
    /// The source with its typed line's code left out, its indentation kept.
    opened: String,
    /// The source after each keystroke, the last the source itself.
    typed: Vec<String>,
}

/// The texts `text` passes through when its typed line is typed back one
/// character per change: the first line at or after its middle that holds
/// [`TYPED`] code characters past its indentation and is no comment.
///
/// # Specification
/// trivial.
fn keystrokes(text: SourceText<'_>) -> Maybe<Keystrokes, Untyped>
{
    let text = <&str>::from(text);
    let lines: Vec<(usize, &str)> = text
        .split_inclusive('\n')
        .scan(0_usize, |start, line| {
            let at = *start;
            *start = start.saturating_add(line.len());
            Some((at, line))
        })
        .collect();
    let middle = lines.len().checked_div(2).unwrap_or(0);
    let found = lines.iter().skip(middle).find_map(|&(at, line)| {
        let content = line.trim_end_matches(['\n', '\r']);
        let code = content.trim_start();
        let typed = code.chars().count() >= TYPED && !code.starts_with("//");
        typed.then(|| {
            let start = at.saturating_add(content.len().saturating_sub(code.len()));
            (start, start.saturating_add(code.len()))
        })
    });
    let Some((start, end)) = found
    else {
        return Maybe::Absent(Untyped::NoLine);
    };
    let (Some(before), Some(code), Some(after)) =
        (text.get(.. start), text.get(start .. end), text.get(end ..))
    else {
        return Maybe::Absent(Untyped::NoLine);
    };
    let typed = code
        .char_indices()
        .map(|(at, character)| at.saturating_add(character.len_utf8()))
        .filter_map(|typed| code.get(.. typed))
        .map(|typed| format!("{before}{typed}{after}"))
        .collect();
    Maybe::Present(Keystrokes {
        opened: format!("{before}{after}"),
        typed,
    })
}

/// The latency workload: each [`SAMPLE`] source opened in a language-server
/// session with its typed line's code left out, then typed back one
/// character per change, each change timed from its write to its settled
/// answer.
///
/// # Specification
/// trivial.
fn latency() -> Result<Latency, Failure>
{
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let mut times = Vec::new();
    for relative in SAMPLE {
        let path = std::fs::canonicalize(root.join(relative))?;
        let text = std::fs::read_to_string(&path)?;
        let Maybe::Present(Keystrokes { opened, typed }) =
            keystrokes(SourceText::from(text.as_str()))
        else {
            return Err(Failure::Untyped(relative));
        };
        let taken = lsp::live(&path, opened, move |client| {
            let mut taken = Vec::with_capacity(typed.len());
            for text in &typed {
                let start = Instant::now();
                client.change(core::slice::from_ref(text))?;
                taken.push(start.elapsed());
            }
            Ok(taken)
        })?;
        times.extend(taken);
    }
    times.sort_unstable();
    // The nearest rank of the `percent`th percentile, as an index into the
    // sorted times.
    let rank = |percent: usize| {
        times
            .len()
            .saturating_mul(percent)
            .div_ceil(100)
            .saturating_sub(1)
    };
    let at = |percent| times.get(rank(percent)).copied().unwrap_or_default();
    Ok(Latency {
        keystrokes: Tally(times.len()),
        p50: at(50),
        p99: at(99),
    })
}

/// What one part of the incremental script read, summed over its edits.
#[derive(Clone, Copy, Debug, Default)]
struct Incremental
{
    /// The edits.
    edits: Tally,
    /// The tokens the form store's relabel labeled afresh.
    relabeled: Tally,
    /// The tokens each edit touches.
    tokens: Tally,
    /// The forms the form store molded rather than took up.
    molded: Tally,
    /// The forms each edit touches.
    forms: Tally,
}

impl Incremental
{
    /// This reading and `more`.
    ///
    /// # Specification
    /// trivial.
    const fn and(
        self,
        more: Self,
    ) -> Self
    {
        Self {
            edits: self.edits.and(more.edits),
            relabeled: self.relabeled.and(more.relabeled),
            tokens: self.tokens.and(more.tokens),
            molded: self.molded.and(more.molded),
            forms: self.forms.and(more.forms),
        }
    }
}

/// What an edit touches in the revision after it: the tokens and the
/// predicted form runs that meet the bytes the edit rewrote, at least one of
/// each. The rewritten bytes run from the end of the two revisions' longest
/// common prefix to the start of their longest common suffix. A run of bytes
/// meets them when it overlaps them, or holds their point when the edit only
/// deleted.
///
/// # Specification
/// trivial.
fn touched(
    molder: &Molder<'_>,
    before: SourceText<'_>,
    after: SourceText<'_>,
) -> (Tally, Tally)
{
    let old = <&str>::from(before).as_bytes();
    let new = <&str>::from(after).as_bytes();
    let prefix = old
        .iter()
        .zip(new)
        .take_while(|&(left, right)| left == right)
        .count();
    let room = old.len().min(new.len()).saturating_sub(prefix);
    let suffix = old
        .iter()
        .rev()
        .zip(new.iter().rev())
        .take(room)
        .take_while(|&(left, right)| left == right)
        .count();
    let (start, end) = (prefix, new.len().saturating_sub(suffix));
    let meets = |from: usize, to: usize| {
        if start == end {
            from <= start && start <= to
        }
        else {
            from < end && to > start
        }
    };
    let offset = |at: u32| usize::try_from(at).unwrap_or(usize::MAX);
    let tokens = label(SourceFragment::from(<&str>::from(after)));
    let own = tokens
        .iter()
        .filter(|token| meets(offset(token.start), offset(token.end)))
        .count();
    let forms = molder
        .form_runs(&tokens, after)
        .iter()
        .filter(|run| {
            let first = tokens.get(usize::from(run.start()));
            let last = usize::from(run.end())
                .checked_sub(1)
                .and_then(|at| tokens.get(at));
            first
                .zip(last)
                .is_some_and(|(first, last)| meets(offset(first.start), offset(last.end)))
        })
        .count();
    (Tally(own.max(1)), Tally(forms.max(1)))
}

/// The revisions of `revisions` parsed in order through one form store, each
/// after the first read as an edit of the one before it.
///
/// # Specification
/// trivial.
fn script(
    pbg: &Pbg,
    molder: &Molder<'_>,
    revisions: &[String],
) -> Result<Incremental, Failure>
{
    let mut store = FormStore::default();
    let mut read = Incremental::default();
    let mut prior: Maybe<&String, Unparsed> = Maybe::Absent(Unparsed::First);
    for revision in revisions {
        let text = SourceText::from(revision.as_str());
        let (parsed, census) = store.parse(pbg, text, &Serial)?;
        drop(core::hint::black_box(parsed));
        if let Maybe::Present(before) = prior {
            let (tokens, forms) = touched(molder, SourceText::from(before.as_str()), text);
            read = read.and(Incremental {
                edits: Tally(1),
                relabeled: Tally(census.relabeled().0),
                tokens,
                molded: Tally(usize::from(census.molded())),
                forms,
            });
        }
        prior = Maybe::Present(revision);
    }
    Ok(read)
}

/// Why a revision of a script has no revision before it.
#[derive(Clone, Copy, Debug)]
enum Unparsed
{
    /// It is the script's first revision, which the store parses whole.
    First,
}

/// The edit sweep's revisions of `text`: the source, a declaration inserted
/// at its middle form, its first form deleted, its last form moved first,
/// and the source again.
///
/// # Specification
/// trivial.
fn form_edits(
    molder: &Molder<'_>,
    text: SourceText<'_>,
) -> Vec<String>
{
    let original = <&str>::from(text);
    let tokens = label(SourceFragment::from(original));
    let mut starts: Vec<usize> = molder
        .form_runs(&tokens, text)
        .iter()
        .filter_map(|run| tokens.get(usize::from(run.start())))
        .filter_map(|token| usize::try_from(token.start).ok())
        .collect();
    starts.push(original.len());
    let cut = |at: usize| original.split_at_checked(at).unwrap_or((original, ""));
    let middle = starts.get(starts.len().div_euclid(2)).copied().unwrap_or(0);
    let first_end = starts.get(1).copied().unwrap_or(original.len());
    let last_start = starts.iter().rev().nth(1).copied().unwrap_or(0);
    let (head, tail) = cut(middle);
    let (front, last) = cut(last_start);
    vec![
        String::from(original),
        format!("{head}def inserted = 1;\n{tail}"),
        String::from(cut(first_end).1),
        format!("{last}\n{front}"),
        String::from(original),
    ]
}

/// The incremental workload: over each [`SAMPLE`] source, the keystroke
/// part types the latency workload's line back one character per revision,
/// and the form part runs the edit sweep's revisions, each through a form
/// store of its own. Answers the keystroke part's reading, then the form
/// part's.
///
/// # Specification
/// trivial.
fn incremental(pbg: &Pbg) -> Result<(Incremental, Incremental), Failure>
{
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let molder = Molder::new(pbg);
    let mut keystroke = Incremental::default();
    let mut form = Incremental::default();
    for relative in SAMPLE {
        let text = std::fs::read_to_string(root.join(relative))?;
        let source = SourceText::from(text.as_str());
        let Maybe::Present(Keystrokes { opened, typed }) = keystrokes(source)
        else {
            return Err(Failure::Untyped(relative));
        };
        let mut revisions = Vec::with_capacity(typed.len().saturating_add(1));
        revisions.push(opened);
        revisions.extend(typed);
        let typed = script(pbg, &molder, &revisions)?;
        keystroke = keystroke.and(typed);
        let edited = script(pbg, &molder, &form_edits(&molder, source))?;
        form = form.and(edited);
    }
    Ok((keystroke, form))
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
    let latency = latency()?;
    let (keystroke, form) = incremental(&pbg)?;
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
    let rows: [(&str, &str, &dyn fmt::Display); 22] = [
        ("latency", "keystrokes typed", &latency.keystrokes),
        (
            "latency",
            "time from a keystroke to its settled answer, ms, p50",
            &Millis(latency.p50),
        ),
        (
            "latency",
            "time from a keystroke to its settled answer, ms, p99",
            &Millis(latency.p99),
        ),
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
    for (part, read) in [("keystroke", keystroke), ("form", form)] {
        writeln!(table, "| incremental | {part} edits | {} |", read.edits)?;
        writeln!(
            table,
            "| incremental | {part}: tokens re-labelled per edit | {} |",
            Ratio {
                part: read.relabeled,
                whole: read.edits,
            }
        )?;
        writeln!(
            table,
            "| incremental | {part}: tokens re-labelled per token the edit touches | {} |",
            Ratio {
                part: read.relabeled,
                whole: read.tokens,
            }
        )?;
        writeln!(
            table,
            "| incremental | {part}: forms re-molded per form the edit touches | {} |",
            Ratio {
                part: read.molded,
                whole: read.forms,
            }
        )?;
    }
    io::stdout().write_all(table.as_bytes())?;
    Ok(())
}
