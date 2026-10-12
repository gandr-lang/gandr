//! Check a staged meta-program on the workers the driver provides.
//!
//! A [`Program`] is an arena holding every source and the context's
//! classifiers, the context its certificates replay under, and its sources in
//! order. [`check`] stages it in four steps and forks wherever the jobs are
//! independent:
//!
//! 1. **Normalize**, forked per source. Each worker clones the program's arena
//!    once and keeps the clone while its sources arrive in increasing order,
//!    starting afresh from the program's extent when a lower one arrives. Per
//!    source it normalizes, groups the certificate's equations, and takes the
//!    classifiers and terms the normalization appended.
//! 2. **Merge**, in source order. Each segment's classifiers and terms, placed
//!    in the program's coordinates, intern into the program's arena, which
//!    finds and compares a term it holds and appends only a miss. The merged
//!    arena is the one normalizing every source in order in a single arena
//!    makes, term for term, and so are the certificates.
//! 3. **Harvest**, in source order: the groupings join over the merged
//!    certificates' equations into the program's families.
//! 4. **Readmit and admit**, two halves side by side: the kernel replays every
//!    certificate, forked per certificate on per-worker clones of the merged
//!    arena, and the memo admits every family, forked per family.
//!
//! Every allowance is per job and every fold runs in source or harvest order,
//! so the result is the same at every width.
//!
//! `Checked` carries the merged arena, a certificate and a `Readmission` per
//! source, the families and a report per family, and the time each stage took.
//! Every value but the time is the serial check's, at every width and under
//! every fork: the witnesses check under forks that run jobs last first from
//! fresh state, that keep one state across half the jobs, and that meet every
//! job on one state in reverse, and compare report for report and term for
//! term. `ProgramError` names the first source, in order, whose normalization,
//! merge or harvest failed; a refused readmission or family is reported beside
//! the others, not failed.
//!
//! # Decisions
//!
//! **Each worker keeps its snapshot while its sources arrive in order.** A
//! source below one the clone holds starts afresh at the program's extent
//! through `Arena::truncate_to`, and a failed source truncates back to where it
//! began. A segment carries its worker, the extent it started at, the
//! classifiers and terms it appended, the certificate in the worker's
//! coordinates and its grouping. Keeping the clone, rather than truncating it
//! after every source, sends the merge only what its worker had not minted and
//! speeds serial normalization, because a kept clone answers a repeated term
//! from its own table. The merged arena and certificates are unchanged: the
//! reference, one arena normalizing every source in order, keeps all of its
//! syntax too. The choice reverses if a normalization's result comes to depend
//! on the syntax already in its arena, which the merged-arena witness compares
//! against, or if a worker's clone outgrows its memory.
//!
//! **The harvest groups where the certificate was made.** `template::Grouping`
//! groups one certificate's equations by family key — the rule and the shallow
//! source shape — and keeps no coordinate, so the worker that normalized the
//! certificate groups it, and the calling thread only appends each step, in
//! certificate order, to the family its key names. The families equal grouping
//! the program's concatenated equations at once, first occurrence and member
//! order kept. Grouping after the merge on the calling thread, as
//! `template::harvest` does over one arena, costs several times the joined
//! harvest. The choice reverses if a family key comes to read the merged
//! coordinates.
//!
//! **The merge interns through the program's arena.** The merge runs on the
//! calling thread in source order, so every coordinate is the one one-arena
//! normalization gives. Each worker has a placement: the merged coordinate of
//! every classifier and term its clone holds above the program's extent. A
//! classifier or term is placed — its children and classifier read through the
//! placement — and interned with `Arena::alloc_type` or `Arena::alloc`, whose
//! table finds a held descriptor by hash and confirms it by comparison, so only
//! a miss is appended and a collision never merges two terms. The certificate
//! is remapped in place and taken from its segment, and the spent segments'
//! buffers, allocated on the workers, are freed beside the readmissions rather
//! than on the merge. The alternatives were these:
//!
//! - *An exact content key: a digest per worker term and a table from digest to
//!   merged terms, a hit compared in place.* It was to be kept only if it saved
//!   5 % of the check's wall against the arena's interning on both measured
//!   hosts, and it did not: its digests cost the workers more than the merge
//!   saves, and a kept clone already sends the merge only what its worker had
//!   not minted. Reversal: a table that saves 5 % of the wall at the shipped
//!   width on both hosts.
//! - *A key of child digests, trusted without a comparison.* A 64-bit collision
//!   between child digests would merge two distinct terms, and no certificate
//!   may rest on that. Reversal: none.
//!
//! **Families fork through disjoint memo slots.** The memo plans every family
//! in harvest order — the slot its key holds and whether the controller drafts
//! it — then admits each family against its own slot on the fork, with a fresh
//! inheritance cache and allowance per family and a drafter and row buffer per
//! worker, and folds the families' time samples into the controller in harvest
//! order afterwards. Keys are unique within one harvest, so no two families
//! share a slot. The alternative was a memo per worker, merged in harvest
//! order: it clones every held template into every worker and needs a rule for
//! a key two workers both learned, for no gain while keys are unique. Every
//! draft decision reads the controller as it stood before the program, where
//! admitting the families one by one lets an earlier family's sample move a
//! later family's decision; the probe duty counts declines in plan order. Under
//! a clock that never advances the two agree exactly over the edit traces the
//! memo is measured on. The choice reverses for a program whose families share
//! a key.
//!
//! **Readmission per certificate.** Each worker clones the merged arena once,
//! replays a certificate from a fresh allowance and truncates the clone back
//! after it, so no replay sees another's syntax. The readmissions and the
//! family admissions are the two halves of one `Fork::join`.

mod merge;
mod segment;
#[cfg(test)]
mod tests;

use alloc::vec::Vec;
use core::fmt;
use core::time::Duration;

use anodized::spec;
use gandr_kernel_term::stage::Arena;
use gandr_kernel_term::stage::Budget;
use gandr_kernel_term::stage::Certificate;
use gandr_kernel_term::stage::StageError;
use gandr_kernel_term::stage::TermId;
use gandr_kernel_term::stage::TypeId;

use crate::fork::Fork;
use crate::template::Clock;
use crate::template::Family;
use crate::template::FamilyReport;
use crate::template::Harvest;
use crate::template::Memo;
use crate::template::PriceGate;
use crate::template::ProgramId;

/// A source's position in its program.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct SourceIndex(pub usize);

/// A staged meta-program, ready to check.
///
/// # Specification
/// - provides: the syntax every source names, the hypotheses its certificates
///   replay under, its sources in order, and the producer identity its families
///   are harvested under. Every source must already be in the arena.
/// - panics: none.
/// - executable: none — public fields; [`check`] refuses a source the arena
///   does not hold.
#[derive(Clone, Debug)]
pub struct Program
{
    /// Every source's syntax and the context's classifiers.
    pub arena: Arena,
    /// The hypotheses every certificate replays under.
    pub context: Vec<TypeId>,
    /// The sources, in order.
    pub sources: Vec<TermId>,
    /// The producer identity the program's families are harvested under.
    pub id: ProgramId,
}

/// The work each job of a check may spend, granted afresh to every job so no
/// job's allowance depends on how the jobs were scheduled.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Allowance
{
    /// Each source's normalization.
    pub normalizing: Budget,
    /// Each certificate's kernel replay.
    pub replaying: Budget,
    /// Each family's admission.
    pub admitting: Budget,
}

/// The kernel's verdict on one certificate.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Readmission
{
    /// The kernel replayed the certificate from its source to its target.
    Readmitted,
    /// The kernel refused the certificate, or ran out of its allowance.
    Refused(StageError),
}

/// Time spent at each stage of a check, read from the caller's clock.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct Stages
{
    /// Normalizing every source, segments and groupings included.
    pub normalizing: Duration,
    /// Joining every segment to the program's arena.
    pub merging: Duration,
    /// Joining every grouping into the program's families.
    pub harvesting: Duration,
    /// Readmitting every certificate beside admitting every family.
    pub checking: Duration,
}

/// A staged program, checked.
///
/// # Specification
/// - provides: the merged arena, one certificate and one readmission per source
///   in source order, the program's families in harvest order with one
///   admission each, and the time each stage took.
/// - panics: none.
/// - executable: none — a plain record of [`check`]'s result.
#[derive(Debug)]
pub struct Checked
{
    /// The program's arena with every normalization's syntax merged in.
    pub arena: Arena,
    /// Each source's certificate, in the merged arena's coordinates.
    pub certificates: Vec<Certificate>,
    /// The kernel's verdict on each certificate.
    pub readmissions: Vec<Readmission>,
    /// The families harvested from the certificates.
    pub families: Vec<Family>,
    /// Each family's admission through the memo.
    pub admissions: Vec<Result<FamilyReport, StageError>>,
    /// Time spent at each stage.
    pub spent: Stages,
}

/// Why a staged program could not be checked: the first failure in source
/// order, with the stage and source it belongs to.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ProgramError
{
    /// A source failed to normalize, or its certificate to be grouped.
    Normalized
    {
        /// The source.
        source: SourceIndex,
        /// The normalizer's or the grouping's error.
        error: StageError,
    },
    /// A source's syntax failed to join the program's arena.
    Merged
    {
        /// The source.
        source: SourceIndex,
        /// The arena's error.
        error: StageError,
    },
    /// A source's grouping failed to join the program's families.
    Harvested
    {
        /// The source.
        source: SourceIndex,
        /// The harvest's error.
        error: StageError,
    },
}

impl fmt::Display for ProgramError
{
    /// Name the stage, the source and the error.
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
            | Self::Normalized { source, error } => {
                write!(f, "source {} failed to normalize: {error}", source.0)
            },
            | Self::Merged { source, error } => {
                write!(f, "source {} failed to merge: {error}", source.0)
            },
            | Self::Harvested { source, error } => {
                write!(f, "source {} failed to harvest: {error}", source.0)
            },
        }
    }
}

impl core::error::Error for ProgramError
{
}

/// Check a staged program: normalize every source, merge the syntax, harvest
/// the families, then readmit every certificate beside admitting every family
/// through `memo`.
///
/// # Specification
/// - ensures: one certificate and one readmission per source, in source order,
///   each certificate in the merged arena's coordinates; the families are those
///   [`harvest`](crate::template::harvest) finds in the merged certificates,
///   each with its admission as [`Memo::admit_family`] gives it, except that
///   every draft decision reads the memo-wide controller as it stood before the
///   program. The merged arena and the certificates are those normalizing every
///   source in order in the program's own arena gives.
/// - fails: the first source, in order, that fails to normalize, merge or
///   harvest; a refused readmission or family is reported, not failed.
/// - panics: none of its own; the fork's.
/// - intension: every job's allowance is its own and every fold runs in source
///   or harvest order, so the result, the memo after and every refusal are the
///   same at every width; only the stage times differ.
///
/// # Errors
/// Returns [`ProgramError::Normalized`], [`ProgramError::Merged`] or
/// [`ProgramError::Harvested`].
///
/// # Adequacy
/// - hypothesis: L2/L3 — the power and double programs over warm and cold memos
///   are checked serially and on a fork that schedules every job last first
///   from fresh worker state, and compared report for report and term for term;
///   the merged syntax is compared with one-arena normalization; exhausted
///   allowances fail or refuse at the same source at every width.
/// - witness: `staging::tests::every_width_checks_the_serial_program`
/// - witness: `staging::tests::the_merged_arena_is_one_arena_normalization`
/// - witness: `staging::tests::exhausted_allowances_refuse_alike_at_every_width`
#[spec(captures: [sources = program.sources.len()],
    ensures: |output| output.as_ref().ok().is_none_or(|checked|
        checked.certificates.len() == sources
            && checked.readmissions.len() == sources
            && checked.admissions.len() == checked.families.len()))]
#[inline]
pub fn check<F, C>(
    program: Program,
    memo: &mut Memo,
    gate: PriceGate,
    allowance: Allowance,
    fork: &F,
    clock: &C,
) -> Result<Checked, ProgramError>
where
    F: Fork,
    C: Clock + Clone + Sync,
{
    let mut timer = clock.clone();
    let Program {
        arena,
        context,
        sources,
        id,
    } = program;
    let begun = timer.now();
    let segments = segment::normalized(&arena, &sources, allowance.normalizing, fork);
    let normalized = timer.now();
    let mut merge = merge::Merge::new(arena);
    let mut certificates = Vec::with_capacity(segments.len());
    let mut groupings = Vec::with_capacity(segments.len());
    // The spent segments' buffers were allocated on the workers; they are
    // freed beside the readmissions, off the serial merge.
    let mut spent = Vec::with_capacity(segments.len());
    for (index, segment) in segments.into_iter().enumerate() {
        let source = SourceIndex(index);
        let mut segment = segment.map_err(|error| ProgramError::Normalized { source, error })?;
        let certificate = merge
            .join(&mut segment)
            .map_err(|error| ProgramError::Merged { source, error })?;
        certificates.push(certificate);
        groupings.push(core::mem::take(&mut segment.grouping));
        spent.push(segment);
    }
    let merged = timer.now();
    let mut harvest = Harvest::new(id);
    for (index, (certificate, grouping)) in certificates.iter().zip(&groupings).enumerate() {
        harvest
            .join(grouping, &certificate.steps)
            .map_err(|error| ProgramError::Harvested {
                source: SourceIndex(index),
                error,
            })?;
    }
    let families = harvest.finish();
    let harvested = timer.now();
    let arena = merge.finish();
    let (merged_arena, merged_certificates) = (&arena, &certificates);
    let (readmissions, admissions) = fork.join(
        move || {
            let readmissions = readmitted(
                merged_arena,
                &context,
                merged_certificates,
                allowance.replaying,
                fork,
            );
            drop(spent);
            readmissions
        },
        || memo.admit_families(&arena, &families, gate, allowance.admitting, fork, clock),
    );
    let checked = timer.now();
    Ok(Checked {
        arena,
        certificates,
        readmissions,
        families,
        admissions,
        spent: Stages {
            normalizing: normalized.saturating_sub(begun),
            merging: merged.saturating_sub(normalized),
            harvesting: harvested.saturating_sub(merged),
            checking: checked.saturating_sub(harvested),
        },
    })
}

/// One certificate's readmission job.
struct Replaying<'certificate>
{
    /// The certificate offered.
    certificate: &'certificate Certificate,
    /// The kernel's verdict; `Unbalanced` until its replay runs.
    readmission: Readmission,
}

/// Replay every certificate through the kernel, forked per certificate on
/// per-worker clones of `arena`, each from a fresh `allowance`.
///
/// # Specification
/// - ensures: one verdict per certificate, in order: `Readmitted` exactly when
///   the kernel replays it from `arena` alone within `allowance`. A worker
///   truncates its clone back to `arena` after each replay, so no replay sees
///   another's syntax.
/// - panics: none of its own; the fork's.
///
/// # Adequacy
/// - hypothesis: L2/L3 — every certificate of the power and double programs is
///   readmitted at every width, and an exhausted allowance refuses each alike.
/// - witness: `staging::tests::every_width_checks_the_serial_program`
/// - witness: `staging::tests::exhausted_allowances_refuse_alike_at_every_width`
#[spec(ensures: |output| output.len() == certificates.len())]
fn readmitted<F>(
    arena: &Arena,
    context: &[TypeId],
    certificates: &[Certificate],
    allowance: Budget,
    fork: &F,
) -> Vec<Readmission>
where
    F: Fork,
{
    let floor = arena.extent();
    let mut jobs: Vec<Replaying<'_>> = certificates
        .iter()
        .map(|certificate| Replaying {
            certificate,
            readmission: Readmission::Refused(StageError::Unbalanced),
        })
        .collect();
    fork.each(
        &mut jobs,
        || arena.clone(),
        |snapshot, job| {
            let mut budget = allowance;
            job.readmission = match gandr_kernel_core::stage::replay(
                snapshot,
                context,
                job.certificate,
                &mut budget,
            ) {
                | Ok(_) => Readmission::Readmitted,
                | Err(error) => Readmission::Refused(error),
            };
            snapshot.truncate_to(floor);
        },
    );
    jobs.into_iter().map(|job| job.readmission).collect()
}
