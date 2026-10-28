//! The edit loop's measurement: each edit class over a generated module,
//! submitted incrementally and whole, and the heap the edit loop keeps.
//!
//! Run with `cargo run --release -p gandr-surface-session --example
//! edit_loop`. `FORMS` sets the generated module's top-level forms (2000) and
//! `REPEATS` the samples behind each median (9).
//!
//! The module is the session tests' generated module, and the edits their
//! script, applied in order: a change, an insertion, a deletion, a move, a
//! merge, a split, and a top-level return inserted and deleted again. Each
//! timing row is one edit at one root and one width, each column a median
//! wall over the edited revision: the judged column is judging it in a session
//! holding the revision before it — the interactive path, from the text to
//! everything a face renders — and the admitted column is admitting it after
//! that judgement, the kernel's readmission, export and commit; the whole
//! column is a fresh session's first submission of it, and the check column
//! the dispatcher's composition of it, the path `gandr check` takes. The
//! molded column is the judgement's forms molded of the revision's forms, and
//! the share column the judged wall as a share of the whole.
//!
//! The memory rows are heap bytes still allocated when each measured scope
//! closes, counted on the calling thread at one thread's width, so every
//! molding runs where it is counted: the lowered revision (its arena and
//! module), the form store's parked units with the text and labeling it
//! relabels the next revision from, a session after its first submission, and
//! what one edit's submission adds to that session.

// Module documentation that predates the shape lint: 1 budget exceeded. Each
// allow leaves with the rewrite that clears its count.
#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    allow(
        module_doc_budget,
        reason = "module documentation that predates the shape lint"
    )
)]
extern crate alloc;

#[path = "../tests/large.rs"]
#[expect(
    dead_code,
    reason = "the measurement replays the fixed script; the property tests draw the strategy"
)]
mod large;

use alloc::collections::BTreeMap;
use alloc::sync::Arc;
use core::fmt;
use core::num::NonZeroUsize;
use core::time::Duration;
use std::io;
use std::io::Write;
use std::time::Instant;

use allocation_counter::AllocationInfo;
use anodized::spec;
use gandr_core_fork::Fork as _;
use gandr_core_incremental::BackendArtifact;
use gandr_core_incremental::MemoryCheckpointStore;
use gandr_storage_records::InMemoryBlockStore;
use gandr_surface_dispatcher::ComposeFault;
use gandr_surface_dispatcher::LoweringCount;
use gandr_surface_dispatcher::Pool;
use gandr_surface_dispatcher::SourceRoot;
use gandr_surface_dispatcher::Threads;
use gandr_surface_dispatcher::Width;
use gandr_surface_dispatcher::compose;
use gandr_surface_dispatcher::lower_source;
use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::PbgError;
use gandr_surface_grammar::built_in;
use gandr_surface_parser::FormIdentity;
use gandr_surface_parser::FormSplit;
use gandr_surface_parser::Molder;
use gandr_surface_parser::ParkedUnit;
use gandr_surface_session::FormCount;
use gandr_surface_session::Session;
use gandr_surface_syntax::SourceText;

use crate::large::module;
use crate::large::script;

/// Why the measurement stopped.
#[derive(Debug)]
enum Failure
{
    /// The built-in grammar did not build.
    Grammar(PbgError),
    /// A submission, a composition or a lowering faulted. The fault borrows
    /// the revision it is about, so it is carried rendered.
    Fault(String),
    /// A write to the output failed.
    Write(io::Error),
    /// A value the measurement records was not recorded.
    Unmeasured,
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

impl From<String> for Failure
{
    /// A pipeline fault, rendered.
    ///
    /// # Specification
    /// trivial.
    fn from(fault: String) -> Self
    {
        Self::Fault(fault)
    }
}

impl From<io::Error> for Failure
{
    /// The output's refusal.
    ///
    /// # Specification
    /// trivial.
    fn from(fault: io::Error) -> Self
    {
        Self::Write(fault)
    }
}

impl fmt::Display for Failure
{
    /// Writes why the measurement stopped.
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
            Self::Fault(ref fault) => f.write_str(fault),
            Self::Write(ref fault) => write!(f, "the output refused a row: {fault}"),
            Self::Unmeasured => f.write_str("a measured value was not recorded"),
        }
    }
}

impl core::error::Error for Failure
{
}

/// The samples behind each median.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Repeats(NonZeroUsize);

/// The session every measurement submits to.
type MeasuredSession = Session<MemoryCheckpointStore, InMemoryBlockStore>;

/// A setting the environment may override.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Setting
{
    /// `FORMS`: the generated module's top-level forms, 2000 by default.
    Forms,
    /// `REPEATS`: the samples behind each median, 9 by default.
    Repeats,
}

/// A positive number a setting configured.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Configured(NonZeroUsize);

impl Setting
{
    /// The number the setting's environment variable spells, or its default.
    ///
    /// # Specification
    /// trivial.
    fn read(self) -> Configured
    {
        let (name, default) = match self {
            Self::Forms => ("FORMS", NonZeroUsize::new(2_000)),
            Self::Repeats => ("REPEATS", NonZeroUsize::new(9)),
        };
        Configured(
            std::env::var(name)
                .ok()
                .and_then(|value| value.parse().ok())
                .or(default)
                .unwrap_or(NonZeroUsize::MIN),
        )
    }
}

/// A fresh session under `root`, parsing on `pool`.
///
/// # Specification
/// trivial.
fn fresh(
    grammar: &Pbg,
    root: SourceRoot,
    pool: &Arc<Pool>,
) -> MeasuredSession
{
    Session::new(
        grammar.clone(),
        root,
        MemoryCheckpointStore::default(),
        InMemoryBlockStore::default(),
        BackendArtifact::from(b"edit-loop".as_slice()),
    )
    .with_pool(Arc::clone(pool))
}

/// The median of `samples`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the middle sample in sorted order, the upper of the two middle
///   ones for an even count; zero for no samples.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — odd, even and empty sample sets, each asserted at the
///   sample it names. The predicate reads the middle slot of the samples the
///   body sorted.
/// - witness: `tests::the_median_is_the_middle_sample`
#[spec(ensures: |ret| if samples.is_empty() { ret == Duration::ZERO } else { samples.get(samples.len().div_euclid(2)) == Some(&ret) })]
fn median(samples: &mut [Duration]) -> Duration
{
    samples.sort_unstable();
    samples
        .get(samples.len().div_euclid(2))
        .copied()
        .unwrap_or_default()
}

/// The wall `body` takes over `state`, as the median of `repeats` runs, each
/// after `prepare` has readied `state` unmeasured.
///
/// # Specification
/// - requires: nothing.
/// - ensures: runs `prepare` then `body` on `state` `repeats` times, timing
///   only `body`, and answers the median wall; the first failure ends the
///   measurement.
/// - fails: the first failure `prepare` or `body` reports.
/// - panics: none.
/// - executable: none — the closures' effects and the clock are outside the
///   returned median.
///
/// # Errors
/// [`Failure`], as above.
///
/// # Adequacy
/// - hypothesis: L3 — a small module's matrix measures every cell at both roots
///   and both widths.
/// - witness: `tests::a_small_module_measures_every_edit_class`
fn timed<State>(
    repeats: Repeats,
    state: &mut State,
    mut prepare: impl FnMut(&mut State) -> Result<(), Failure>,
    mut body: impl FnMut(&mut State) -> Result<(), Failure>,
) -> Result<Duration, Failure>
{
    let mut samples = Vec::with_capacity(repeats.0.get());
    for _ in 0 .. repeats.0.get() {
        prepare(state)?;
        let start = Instant::now();
        body(state)?;
        samples.push(start.elapsed());
    }
    Ok(median(&mut samples))
}

/// The median wall of a fresh session's first submission of `text`, the
/// session built unmeasured.
///
/// # Specification
/// - requires: nothing.
/// - ensures: as [`timed`] states, each run submitting `text` to a session
///   [`fresh`] built before the clock started.
/// - fails: a submission's fault.
/// - panics: none.
/// - executable: none — the clock is outside the returned median.
///
/// # Errors
/// [`Failure`], as above.
///
/// # Adequacy
/// - hypothesis: L3 — a small module's matrix measures every cell at both roots
///   and both widths.
/// - witness: `tests::a_small_module_measures_every_edit_class`
fn whole(
    grammar: &Pbg,
    root: SourceRoot,
    pool: &Arc<Pool>,
    text: SourceText<'_>,
    repeats: Repeats,
) -> Result<Duration, Failure>
{
    timed(
        repeats,
        &mut None,
        |session| {
            *session = Some(fresh(grammar, root, pool));
            Ok(())
        },
        |session: &mut Option<MeasuredSession>| {
            session
                .as_mut()
                .ok_or(Failure::Unmeasured)?
                .submit(text)
                .map(drop)
                .map_err(|fault| fault.to_string().into())
        },
    )
}

/// Write one timing row per edit of the script over a module of `forms`
/// forms under `root`, submitted at `width`, after a row for the module's
/// first submission.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one Markdown row for the first submission and one per scripted
///   edit, each naming the root, the width, the edit, the forms molded of the
///   revision's forms, the judged, admitted, whole and check medians and the
///   judged median's share of the whole; the incremental session ends holding
///   the script's last revision, admitted.
/// - fails: a submission's or a composition's fault, and a refused write.
/// - panics: none.
/// - executable: none — the rows go to a writer the signature cannot read back.
///
/// # Errors
/// [`Failure`], as above.
///
/// # Adequacy
/// - hypothesis: L3 — a small module's matrix writes the row count the script
///   predicts at both roots and both widths.
/// - witness: `tests::a_small_module_measures_every_edit_class`
fn rows(
    grammar: &Pbg,
    root: SourceRoot,
    width: Width,
    forms: FormCount,
    repeats: Repeats,
    out: &mut dyn Write,
) -> Result<(), Failure>
{
    let mut generated = module(forms, root);
    let mut previous = generated.text();
    let pool = Arc::new(Pool::new(width));
    // The pool starts before any clock does, so no row times its threads
    // starting.
    pool.join(|| (), || ());
    let mut session = fresh(grammar, root, &pool);
    let threads = usize::from(NonZeroUsize::from(width.threads()));
    let first = whole(
        grammar,
        root,
        &pool,
        SourceText::from(previous.as_str()),
        repeats,
    )?;
    let census = session
        .submit(SourceText::from(previous.as_str()))
        .map_err(|fault| fault.to_string())?
        .forms();
    writeln!(
        out,
        "| {root} | {threads} | first | {}/{} | — | — | {:.2} | — | — |",
        usize::from(census.molded()),
        usize::from(census.forms()),
        first.as_secs_f64() * 1_000.0_f64,
    )?;
    for edit in script(forms) {
        generated.edit(&edit);
        let edited = generated.text();
        let mut census = None;
        let judged = timed(
            repeats,
            &mut session,
            |session| {
                session
                    .submit(SourceText::from(previous.as_str()))
                    .map(drop)
                    .map_err(|fault| fault.to_string().into())
            },
            |session| {
                let submitted = session
                    .judge(SourceText::from(edited.as_str()))
                    .map_err(|fault| fault.to_string())?;
                census = Some(submitted.forms());
                Ok(())
            },
        )?;
        let admitted = timed(
            repeats,
            &mut session,
            |session| {
                session
                    .submit(SourceText::from(previous.as_str()))
                    .map_err(|fault| fault.to_string())?;
                session
                    .judge(SourceText::from(edited.as_str()))
                    .map(drop)
                    .map_err(|fault| fault.to_string().into())
            },
            |session| {
                session
                    .admit()
                    .map(drop)
                    .map_err(|fault| ComposeFault::Readmission(fault).to_string().into())
            },
        )?;
        let whole = whole(
            grammar,
            root,
            &pool,
            SourceText::from(edited.as_str()),
            repeats,
        )?;
        let check = timed(
            repeats,
            &mut (),
            |&mut ()| Ok(()),
            |&mut ()| {
                compose(
                    grammar,
                    root.corpus_root(),
                    SourceText::from(edited.as_str()),
                    &mut LoweringCount::default(),
                )
                .map(drop)
                .map_err(|fault| fault.to_string().into())
            },
        )?;
        let census = census.ok_or(Failure::Unmeasured)?;
        writeln!(
            out,
            "| {root} | {threads} | {edit} | {}/{} | {:.2} | {:.2} | {:.2} | {:.2} | {:.1} % |",
            usize::from(census.molded()),
            usize::from(census.forms()),
            judged.as_secs_f64() * 1_000.0_f64,
            admitted.as_secs_f64() * 1_000.0_f64,
            whole.as_secs_f64() * 1_000.0_f64,
            check.as_secs_f64() * 1_000.0_f64,
            judged.as_secs_f64() / whole.as_secs_f64() * 100.0_f64,
        )?;
        previous = edited;
    }
    Ok(())
}

/// The heap `scope` leaves allocated, with what it kept.
///
/// # Specification
/// - requires: nothing.
/// - ensures: runs `scope` once under the calling thread's allocation counter
///   and answers its counts with the value it built, which still holds the
///   bytes counted as current.
/// - fails: the failure `scope` reports.
/// - panics: none.
/// - executable: none — the allocator's counts are not a function of the
///   returned value.
///
/// # Errors
/// [`Failure`], as above.
///
/// # Adequacy
/// - hypothesis: L3 — a small module's lowered revision and form store each
///   keep heap, and an edit's submission adds less than the first submission
///   kept.
/// - witness: `tests::an_edit_keeps_less_than_a_first_submission`
fn kept<Value>(
    scope: impl FnOnce() -> Result<Value, Failure>
) -> Result<(Value, AllocationInfo), Failure>
{
    let mut value = None;
    let info = allocation_counter::measure(|| value = Some(scope()));
    let value = value.ok_or(Failure::Unmeasured)??;
    Ok((value, info))
}

/// The bytes the edit loop keeps over a module of `forms` forms under the
/// strict root, one row each: the lowered revision, the form store with the
/// text and labeling it relabels from, a session after its first submission,
/// and one edit's submission to it.
///
/// # Specification
/// - requires: nothing.
/// - ensures: answers the four retained byte counts, in that order, each
///   counted at one thread's width.
/// - fails: a lowering's, a parse's or a submission's fault.
/// - panics: none.
/// - executable: none — the allocator's counts are not a function of the
///   arguments.
///
/// # Errors
/// [`Failure`], as above.
///
/// # Adequacy
/// - hypothesis: L3 — a small module's lowered revision and form store each
///   keep heap, and an edit's submission adds less than the first submission
///   kept.
/// - witness: `tests::an_edit_keeps_less_than_a_first_submission`
fn memory(
    grammar: &Pbg,
    forms: FormCount,
) -> Result<[AllocationInfo; 4], Failure>
{
    let mut generated = module(forms, SourceRoot::Strict);
    let text = generated.text();
    let source = SourceText::from(text.as_str());
    let (_lowering, lowered) = kept(|| {
        lower_source(grammar, source, &mut LoweringCount::default())
            .map_err(|fault| fault.to_string().into())
    })?;
    let (_store, store) = kept(|| {
        let mut molder = Molder::new(grammar);
        let split = FormSplit::new(&molder, source);
        let units: BTreeMap<FormIdentity, ParkedUnit> = split
            .runs()
            .iter()
            .map(|&run| (split.identity(run), split.mold(&mut molder, run).park()))
            .collect();
        Ok((units, text.clone(), split.into_labeling()))
    })?;
    let (mut session, first) = kept(|| {
        let mut session = fresh(grammar, SourceRoot::Strict, &Arc::default());
        session
            .submit(source)
            .map(drop)
            .map_err(|fault| fault.to_string())?;
        Ok(session)
    })?;
    if let Some(&edit) = script(forms).first() {
        generated.edit(&edit);
    }
    let edited = generated.text();
    let ((), edit) = kept(|| {
        session
            .submit(SourceText::from(edited.as_str()))
            .map(drop)
            .map_err(|fault| fault.to_string().into())
    })?;
    Ok([lowered, store, first, edit])
}

/// Write the memory rows, each with its share of the lowered revision.
///
/// # Specification
/// trivial.
fn memory_rows(
    counts: &[AllocationInfo; 4],
    out: &mut dyn Write,
) -> io::Result<()>
{
    let [lowered, ..] = *counts;
    let base = lowered.bytes_current.max(1);
    writeln!(out, "| kept | bytes | % of lowered |")?;
    writeln!(out, "|---|---:|---:|")?;
    for (name, info) in [
        "lowered revision (arena and module)",
        "form store (parked units by identity, text and labeling)",
        "session after its first submission",
        "one edit's submission, added",
    ]
    .into_iter()
    .zip(counts)
    {
        writeln!(
            out,
            "| {name} | {} | {} |",
            info.bytes_current,
            info.bytes_current
                .saturating_mul(100)
                .checked_div(base)
                .unwrap_or_default()
        )?;
    }
    Ok(())
}

/// Measure the edit loop and print the timing matrix and the memory rows.
///
/// # Specification
/// - requires: nothing.
/// - ensures: prints one timing row per root, width and edit, then the memory
///   rows.
/// - fails: the built-in grammar's fault, any measurement's failure, and a
///   refused write.
/// - panics: none.
/// - executable: none — the rows go to standard output.
///
/// # Errors
/// [`Failure`], as above.
///
/// # Adequacy
/// - hypothesis: L3 — a small module's matrix and memory rows are measured
///   whole.
/// - witness: `tests::a_small_module_measures_every_edit_class`
/// - witness: `tests::an_edit_keeps_less_than_a_first_submission`
fn main() -> Result<(), Failure>
{
    let Configured(forms) = Setting::Forms.read();
    let forms = FormCount::from(forms.get());
    let Configured(repeats) = Setting::Repeats.read();
    let repeats = Repeats(repeats);
    let grammar = built_in()?;
    let mut out = io::stdout().lock();
    writeln!(
        out,
        "| root | threads | edit | molded | judged ms | admitted ms | whole ms | check ms | judged/whole |"
    )?;
    writeln!(out, "|---|---:|---|---:|---:|---:|---:|---:|---:|")?;
    for root in [SourceRoot::Strict, SourceRoot::Fixture] {
        for width in [
            Width::Threads(Threads::from(NonZeroUsize::MIN)),
            Width::PerformanceCores,
        ] {
            rows(&grammar, root, width, forms, repeats, &mut out)?;
        }
    }
    writeln!(out)?;
    memory_rows(&memory(&grammar, forms)?, &mut out)?;
    Ok(())
}

#[cfg(test)]
mod tests
{
    use core::num::NonZeroUsize;
    use core::time::Duration;

    use gandr_surface_dispatcher::SourceRoot;
    use gandr_surface_dispatcher::Threads;
    use gandr_surface_dispatcher::Width;
    use gandr_surface_grammar::built_in;
    use gandr_surface_session::FormCount;

    use super::Repeats;
    use super::median;
    use super::memory;
    use super::rows;

    #[test]
    fn the_median_is_the_middle_sample()
    {
        let ms = Duration::from_millis;
        assert_eq!(median(&mut [ms(3), ms(1), ms(2)]), ms(2));
        assert_eq!(median(&mut [ms(4), ms(1), ms(3), ms(2)]), ms(3));
        assert_eq!(median(&mut []), Duration::ZERO);
    }

    #[test]
    fn a_small_module_measures_every_edit_class()
    {
        let grammar = built_in().expect("the built-in grammar builds");
        let mut out = Vec::new();
        for root in [SourceRoot::Strict, SourceRoot::Fixture] {
            for width in [
                Width::Threads(Threads::from(NonZeroUsize::MIN)),
                Width::Threads(Threads::from(NonZeroUsize::new(3).expect("three"))),
            ] {
                rows(
                    &grammar,
                    root,
                    width,
                    FormCount::from(16_usize),
                    Repeats(NonZeroUsize::MIN),
                    &mut out,
                )
                .expect("the matrix is measured");
            }
        }
        let written = String::from_utf8(out).expect("the rows are UTF-8");
        assert_eq!(
            written.lines().count(),
            4 * 9,
            "a first row and one per scripted edit, at each root and width:\n{written}"
        );
        assert!(
            written
                .lines()
                .all(|row| row.starts_with("| ") && row.ends_with(" |")),
            "{written}"
        );
    }

    #[test]
    fn an_edit_keeps_less_than_a_first_submission()
    {
        let grammar = built_in().expect("the built-in grammar builds");
        let [lowered, store, first, edit] =
            memory(&grammar, FormCount::from(64_usize)).expect("the memory is measured");
        assert!(lowered.bytes_current > 0, "{lowered:?}");
        assert!(store.bytes_current > 0, "{store:?}");
        assert!(
            edit.bytes_current < first.bytes_current,
            "an edit adds less than the first submission kept: {edit:?} against {first:?}"
        );
    }
}
