//! A session: one call per revision that resumes, persists and streams.

use alloc::sync::Arc;
use core::fmt;

use anodized::spec;
use gandr_core_checker::CheckBudget;
use quenchant_shape::shape::Maybe;

use crate::checkpoint::Leading;
use crate::checkpoint::Resume;
use crate::checkpoint::ResumeCensus;
use crate::checkpoint::ResumeError;
use crate::checkpoint::check_program;
use crate::checkpoint::resume;
use crate::checkpoint::resume_after;
use crate::persistence::BackendArtifact;
use crate::persistence::CheckpointObserver;
use crate::persistence::CheckpointStore;
use crate::persistence::CheckpointStoreError;
use crate::persistence::persist;
use crate::region::Program;
use crate::stream::SynthesisStream;

quenchant_shape::reason_enum! {
    /// Why a session holds no resume.
    pub mod submitted {
        /// The reason none is held.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No resume is held, initially or after a resume failure.
            Fresh,
        }
    }
}

/// Why a submission failed.
///
/// # Specification
/// - requires: interpreted as the result of a session submission.
/// - ensures: a resume error names a failure before retaining the new pass; a
///   store error names a persistence failure after retaining the new resume.
/// - executable: none — this declaration has no call boundary and does not
///   retain the session state or the store against which it was produced.
///
/// # Adequacy
/// - hypothesis: L3 — a real file-store failure after a changed revision
///   retains the new two-item resume, which a repaired store can persist
///   without rejudging. The finite witness does not exercise order-capacity
///   failure or certify arbitrary errors constructed independently of a
///   session.
/// - witness: `session::tests::a_store_failure_retains_the_new_resume_for_the_next_submission`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum SessionError
{
    /// The resume could not complete; the session holds no resume afterwards.
    Resume(ResumeError),
    /// The checkpoints could not be persisted; the session holds the new
    /// resume, and the store what it held before.
    Store(CheckpointStoreError),
}

impl fmt::Display for SessionError
{
    /// Writes the failure's message.
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
            Self::Resume(error) => write!(f, "resume failed: {error}"),
            Self::Store(error) => write!(f, "persisting the checkpoints failed: {error}"),
        }
    }
}

impl core::error::Error for SessionError
{
}

/// An incremental session over successive revisions of one program.
///
/// # Specification
/// - requires: submissions are successive revisions; stores and observers
///   satisfy their respective trait obligations when a submission uses them.
/// - ensures: a fresh session holds no resume; a reopened session holds its
///   supplied resume. A completed checking pass replaces the retained state
///   even when persistence fails; a resume failure leaves no retained base.
/// - executable: none — this declaration has no call boundary; submit's
///   predicate checks the local transition, while persistence and observer
///   behavior belong to the supplied implementations.
///
/// # Adequacy
/// - hypothesis: L3 — first submission, independent file-store reopening and a
///   failed changed revision followed by a repaired-store submission separate
///   fresh, restored and retained-after-failure state. Order exhaustion and
///   arbitrary trait implementations remain outside these finite cases.
/// - witness: `session::tests::submit_persists_and_streams_in_order`
/// - witness: `session::tests::separately_reopened_file_session_resumes_supported_checkpoint`
/// - witness: `session::tests::a_store_failure_retains_the_new_resume_for_the_next_submission`
pub struct IncrementalSession<Store>
{
    /// Where complete checkpoint sets are persisted.
    store: Store,
    /// The identity of the checker the checkpoints were judged by.
    backend: BackendArtifact,
    /// The allowance a first submission judges under.
    budget: CheckBudget,
    /// The latest resume.
    last: Maybe<Resume, submitted::Absent>,
}

impl<Store> fmt::Debug for IncrementalSession<Store>
{
    /// Writes the latest resume; the store is opaque.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.debug_struct("IncrementalSession")
            .field("last", &self.last)
            .finish_non_exhaustive()
    }
}

impl<Store> IncrementalSession<Store>
{
    /// A session with nothing submitted.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        store: Store,
        backend: BackendArtifact,
        budget: CheckBudget,
    ) -> Self
    {
        Self {
            store,
            backend,
            budget,
            last: Maybe::Absent(submitted::Absent::Fresh),
        }
    }

    /// A session resuming from `resume`, under its checkpoints' allowance.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn reopen(
        store: Store,
        backend: BackendArtifact,
        resume: Resume,
    ) -> Self
    {
        Self {
            store,
            backend,
            budget: resume.checkpoints().budget(),
            last: Maybe::Present(resume),
        }
    }

    /// Submit a revision: resume from the latest one, or judge it whole, then
    /// persist its checkpoints.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the session holds the revision's resume and the
    ///   store its checkpoints at its address; the census of the pass is
    ///   returned.
    /// - fails: [`SessionError::Resume`] when the resume fails;
    ///   [`SessionError::Store`] when persisting fails, with the store as it
    ///   was.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — first empty submission, an independently reopened
    ///   file session and a changed revision whose real file store fails
    ///   distinguish success, persistence and retained-after-failure state. The
    ///   repaired store adopts both items from the failed submission and still
    ///   restores the earlier persisted revision. Order exhaustion is not
    ///   exercised; generic store atomicity and observer behavior remain their
    ///   implementations' obligations.
    /// - witness: `session::tests::submit_persists_and_streams_in_order`
    /// - witness: `session::tests::separately_reopened_file_session_resumes_supported_checkpoint`
    /// - witness: `session::tests::a_store_failure_retains_the_new_resume_for_the_next_submission`
    #[spec(ensures: |ret| match ret {
        | Ok(census) => {
            matches!(self.last, Maybe::Present(ref latest) if latest.census() == census && latest.checkpoints().items().len() == program.items().len())
        },
        | Err(SessionError::Resume(_)) => {
            matches!(self.last, Maybe::Absent(submitted::Absent::Fresh))
        },
        | Err(SessionError::Store(_)) => {
            matches!(self.last, Maybe::Present(ref latest) if latest.checkpoints().items().len() == program.items().len())
        },
    })]
    #[inline]
    pub fn submit<Observer>(
        &mut self,
        program: &mut Program,
        observer: &mut Observer,
    ) -> Result<ResumeCensus, SessionError>
    where
        Store: CheckpointStore,
        Observer: CheckpointObserver,
    {
        let previous = core::mem::replace(&mut self.last, Maybe::Absent(submitted::Absent::Fresh));
        let next = match previous {
            Maybe::Present(base) => resume(base, program),
            Maybe::Absent(_) => check_program(program, self.budget),
        }
        .map_err(SessionError::Resume)?;
        self.persisted(program, next, observer)
    }

    /// [`submit`](Self::submit) of a revision laid after `leading`, the state
    /// [`lead`](crate::lead) left over a program the revision lays first: only
    /// the items after that program's are judged or adopted.
    ///
    /// # Specification
    /// - requires: as [`resume_after`].
    /// - ensures: as [`submit`](Self::submit), the pass being [`resume_after`]
    ///   from the resume the session holds, if any, after `leading`.
    /// - fails: as [`submit`](Self::submit).
    /// - panics: none.
    ///
    /// # Errors
    /// As [`submit`](Self::submit).
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a session's revisions after one leading state judge
    ///   only their own items, each resumed from the one before.
    /// - witness: `session::tests::a_session_after_a_leading_state_resumes_its_own_items_776`
    #[spec(ensures: |ret| match ret {
        | Ok(census) => {
            matches!(self.last, Maybe::Present(ref latest) if latest.census() == census && latest.checkpoints().items().len() == program.items().len())
        },
        | Err(SessionError::Resume(_)) => {
            matches!(self.last, Maybe::Absent(submitted::Absent::Fresh))
        },
        | Err(SessionError::Store(_)) => {
            matches!(self.last, Maybe::Present(ref latest) if latest.checkpoints().items().len() == program.items().len())
        },
    })]
    #[inline]
    pub fn submit_after<Observer>(
        &mut self,
        program: &mut Program,
        leading: &Arc<Leading>,
        observer: &mut Observer,
    ) -> Result<ResumeCensus, SessionError>
    where
        Store: CheckpointStore,
        Observer: CheckpointObserver,
    {
        let previous = core::mem::replace(&mut self.last, Maybe::Absent(submitted::Absent::Fresh));
        let next = resume_after(previous, leading, program).map_err(SessionError::Resume)?;
        self.persisted(program, next, observer)
    }

    /// Persist `next`'s checkpoints of `program` and hold `next`, whether or
    /// not persisting succeeds.
    ///
    /// # Specification
    /// - requires: `next` is the pass over `program`.
    /// - ensures: the session holds `next`; on success its census is returned.
    /// - fails: [`SessionError::Store`] when persisting fails.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`submit`](Self::submit).
    /// - witness: `session::tests::a_store_failure_retains_the_new_resume_for_the_next_submission`
    #[spec(ensures: |ret| matches!(self.last, Maybe::Present(ref latest)
        if ret.as_ref().is_err() || ret.as_ref().is_ok_and(|census| latest.census() == *census)))]
    fn persisted<Observer>(
        &mut self,
        program: &Program,
        next: Resume,
        observer: &mut Observer,
    ) -> Result<ResumeCensus, SessionError>
    where
        Store: CheckpointStore,
        Observer: CheckpointObserver,
    {
        let census = next.census();
        let persisted = persist(
            &mut self.store,
            program,
            self.backend,
            next.checkpoints(),
            observer,
        );
        self.last = Maybe::Present(next);
        persisted.map_err(SessionError::Store)?;
        Ok(census)
    }

    /// The latest resume.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn last(&self) -> Maybe<&Resume, submitted::Absent>
    {
        match self.last {
            Maybe::Present(ref resume) => Maybe::Present(resume),
            Maybe::Absent(reason) => Maybe::Absent(reason),
        }
    }

    /// The synthesis stream of the latest resume.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn stream(&self) -> Maybe<SynthesisStream, submitted::Absent>
    {
        self.last().map(SynthesisStream::from_resume)
    }

    /// The store, once the session is done.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn into_store(self) -> Store
    {
        self.store
    }
}

#[cfg(test)]
mod tests;
