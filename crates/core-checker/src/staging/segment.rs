//! The worker's side of a check: normalize sources on a snapshot of the
//! program's arena the worker keeps while its sources arrive in order, and
//! export what each normalization appended in a form the merge can place
//! without the worker's arena.

use alloc::vec::Vec;
use core::sync::atomic::AtomicUsize;
use core::sync::atomic::Ordering;

use anodized::spec;
use gandr_core_fork::Fork;
use gandr_kernel_term::stage::Arena;
use gandr_kernel_term::stage::Budget;
use gandr_kernel_term::stage::Certificate;
use gandr_kernel_term::stage::Extent;
use gandr_kernel_term::stage::StageError;
use gandr_kernel_term::stage::Term;
use gandr_kernel_term::stage::TermId;
use gandr_kernel_term::stage::Type;

use super::SourceIndex;
use crate::template::Grouping;

/// Which worker normalized a segment: the merge keeps one placement per
/// worker.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct WorkerIndex(pub usize);

/// What normalizing one source appended to its worker's snapshot of the
/// program's arena.
///
/// # Specification
/// - provides: the snapshot's extent before the source; the classifiers and the
///   terms appended after it, in allocation order; the certificate in the
///   snapshot's coordinates, which agree with the program's below the program's
///   extent; and the certificate's grouping.
/// - panics: none.
/// - executable: none — built only by [`Worker::normalize`].
#[derive(Debug)]
pub(super) struct Segment
{
    /// The worker whose snapshot the source was normalized on.
    pub worker: WorkerIndex,
    /// The snapshot's extent before the source: the program's, or above it
    /// by what the worker's earlier segments appended.
    pub start: Extent,
    /// The classifiers appended, in allocation order.
    pub types: Vec<Type>,
    /// The terms appended, in allocation order.
    pub terms: Vec<Term>,
    /// The certificate, in the snapshot's coordinates.
    pub certificate: Certificate,
    /// The certificate's equations grouped by decision and shape.
    pub grouping: Grouping,
}

/// A worker's snapshot of the program's arena, kept across the sources the
/// worker meets in increasing order.
///
/// # Specification
/// - provides: a snapshot holding the program's arena and the syntax of the
///   sources the worker normalized since it last started afresh.
/// - panics: none.
/// - executable: none — [`Worker::normalize`] carries the laws.
struct Worker
{
    /// The worker, as the merge knows it.
    id: WorkerIndex,
    /// The snapshot.
    snapshot: Arena,
    /// The lowest source the snapshot continues with: one past the last it
    /// holds.
    next: SourceIndex,
}

impl Worker
{
    /// Normalize `source`, the program's `index`th, on the snapshot, and
    /// export what it appended.
    ///
    /// # Specification
    /// - requires: the snapshot was cloned from the program's arena, whose
    ///   extent is `floor`.
    /// - ensures: a source below one the snapshot holds starts afresh from the
    ///   program's arena, so a segment builds only on segments of lower index;
    ///   a normalized source's syntax stays for the worker's later sources; a
    ///   failed source truncates the snapshot back to where the source started.
    /// - fails: the normalizer's error, or the grouping's.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns the normalizer's `StageError`, `StageError::UnknownTerm` or
    /// `StageError::UnknownType`.
    ///
    /// # Adequacy
    /// - hypothesis: L2/L3 — the power and double programs are normalized on
    ///   one worker in order, on two that each continue, on fresh workers per
    ///   source and on one worker that meets every source last first, and each
    ///   merges to one-arena normalization; an exhausted allowance fails the
    ///   first source at every width.
    /// - witness: `staging::tests::the_merged_arena_is_one_arena_normalization`
    /// - witness: `staging::tests::exhausted_allowances_refuse_alike_at_every_width`
    #[spec(captures: before = self.snapshot.extent(),
        ensures: |output| match output.as_ref() {
            Ok(segment) => segment.start.terms.0 >= floor.terms.0
                && segment.start.types.0 >= floor.types.0,
            Err(_) => self.snapshot.extent().terms.0 <= before.terms.0
                && self.snapshot.extent().types.0 <= before.types.0,
        })]
    fn normalize(
        &mut self,
        floor: Extent,
        index: SourceIndex,
        source: TermId,
        allowance: Budget,
    ) -> Result<Segment, StageError>
    {
        if index.0 < self.next.0 {
            self.snapshot.truncate_to(floor);
        }
        let start = self.snapshot.extent();
        let segment = self.append(start, source, allowance);
        if segment.is_ok() {
            self.next = SourceIndex(index.0.saturating_add(1));
        }
        else {
            self.snapshot.truncate_to(start);
        }
        segment
    }

    /// Normalize `source` on the snapshot from `start` and export what it
    /// appended.
    ///
    /// # Specification
    /// - requires: `start` is the snapshot's extent.
    /// - ensures: the classifiers and terms above `start`, the certificate and
    ///   its grouping.
    /// - fails: the normalizer's error, or the grouping's.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns the normalizer's `StageError`, `StageError::UnknownTerm` or
    /// `StageError::UnknownType`.
    ///
    /// # Adequacy
    /// - hypothesis: L2/L3 — as [`Worker::normalize`].
    /// - witness: `staging::tests::the_merged_arena_is_one_arena_normalization`
    #[spec(ensures: |output| output.as_ref().ok().is_none_or(|segment| segment.start == start))]
    fn append(
        &mut self,
        start: Extent,
        source: TermId,
        allowance: Budget,
    ) -> Result<Segment, StageError>
    {
        let mut budget = allowance;
        let certificate =
            gandr_core_nbe::stage::normalize(&mut self.snapshot, source, &mut budget)?;
        let grouping = Grouping::of(&self.snapshot, &certificate)?;
        Ok(Segment {
            worker: self.id,
            start,
            types: self.snapshot.types_above(start).to_vec(),
            terms: self.snapshot.terms_above(start).to_vec(),
            certificate,
            grouping,
        })
    }
}

/// One source's normalization job.
struct Normalizing
{
    /// The source's position in the program.
    index: SourceIndex,
    /// The source.
    source: TermId,
    /// Its segment; `Unbalanced` until its normalization runs.
    segment: Result<Segment, StageError>,
}

/// Normalize every source, forked per source on per-worker snapshots of
/// `arena`, each from a fresh `allowance`.
///
/// # Specification
/// - ensures: one segment or error per source, in order. A worker keeps its
///   snapshot from one source to the next while its sources arrive in
///   increasing order, so a source's segment holds only what the worker's
///   earlier sources did not already append, and starts afresh otherwise.
/// - panics: none of its own; the fork's.
///
/// # Adequacy
/// - hypothesis: L2/L3 — the power and double programs are normalized at every
///   width and under every fork shape, and merged to one-arena normalization;
///   an exhausted allowance fails the first source at every width.
/// - witness: `staging::tests::the_merged_arena_is_one_arena_normalization`
/// - witness: `staging::tests::exhausted_allowances_refuse_alike_at_every_width`
#[spec(ensures: |output| output.len() == sources.len())]
pub(super) fn normalized<F>(
    arena: &Arena,
    sources: &[TermId],
    allowance: Budget,
    fork: &F,
) -> Vec<Result<Segment, StageError>>
where
    F: Fork,
{
    let floor = arena.extent();
    let workers = AtomicUsize::new(0);
    let mut jobs: Vec<Normalizing> = sources
        .iter()
        .enumerate()
        .map(|(index, &source)| Normalizing {
            index: SourceIndex(index),
            source,
            segment: Err(StageError::Unbalanced),
        })
        .collect();
    fork.each(
        &mut jobs,
        || Worker {
            id: WorkerIndex(workers.fetch_add(1, Ordering::Relaxed)),
            snapshot: arena.clone(),
            next: SourceIndex(0),
        },
        |worker, job| {
            job.segment = worker.normalize(floor, job.index, job.source, allowance);
        },
    );
    jobs.into_iter().map(|job| job.segment).collect()
}
