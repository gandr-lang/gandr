//! A session: one call per revision that resumes, persists and streams.

use alloc::boxed::Box;
use alloc::sync::Arc;
use core::fmt;

use anodized::spec;
use gandr_core_checker::CheckBudget;
use gandr_core_checker::Polled;
use gandr_core_checker::Retirement;
use gandr_core_checker::Unretired;
use quenchant_shape::shape::Maybe;

use crate::checkpoint::Leading;
use crate::checkpoint::Resume;
use crate::checkpoint::ResumeCensus;
use crate::checkpoint::ResumeError;
use crate::checkpoint::Resuming;
use crate::checkpoint::resume_after_retiring;
use crate::checkpoint::resume_or_check;
use crate::persistence::BackendArtifact;
use crate::persistence::CheckpointAddress;
use crate::persistence::CheckpointObserver;
use crate::persistence::CheckpointStore;
use crate::persistence::CheckpointStoreError;
use crate::persistence::Keeping;
use crate::persistence::Restorer;
use crate::persistence::persist;
use crate::persistence::persist_set;
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

quenchant_shape::reason_enum! {
    /// Why a session's next submission restores from no store.
    pub mod restoring {
        /// The reason none is consulted.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// None was given.
            Unasked,
            /// The submission after it was given consulted it.
            Spent,
        }
    }
}

/// A checkpoint observer told nothing.
struct Unobserved;

impl CheckpointObserver for Unobserved
{
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
///   even when persistence fails; a retired pass leaves it as it was; a resume
///   failure leaves no retained base.
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
    /// What the next submission restores from when no resume is held.
    restoring: Maybe<Box<dyn Restorer>, restoring::Absent>,
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
            restoring: Maybe::Absent(restoring::Absent::Unasked),
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
            restoring: Maybe::Absent(restoring::Absent::Unasked),
        }
    }

    /// Have the next submission restore from `restorer` when the session
    /// holds no resume: the set it holds for the submitted program is
    /// resumed from as a submission's own would be.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn restore_from(
        &mut self,
        restorer: Box<dyn Restorer>,
    )
    {
        self.restoring = Maybe::Present(restorer);
    }

    /// Persist the checkpoints of the latest resume to `store`, as `backend`
    /// judged them: what a save keeps for a later session to restore from.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: when a resume is held, its checkpoints stored in `store` at
    ///   the address of the program they are of, which is returned; the session
    ///   is unchanged.
    /// - provides: `submitted::Absent` when no submission completed.
    /// - fails: the address's or the store's error.
    /// - panics: propagates a panic from the store.
    ///
    /// # Errors
    /// As [`address_of`](crate::address_of) and [`CheckpointStore::store`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a set persisted from a session over a store that
    ///   keeps nothing restores a second session's first submission of the same
    ///   program, every item adopted.
    /// - witness: `session::tests::a_held_set_persists_to_another_store_and_restores_a_first_submission_1816`
    #[spec(ensures: |ret| matches!(
        (ret, &self.last),
        (Ok(Maybe::Absent(_)), Maybe::Absent(_)) | (Ok(Maybe::Present(_)) | Err(_), Maybe::Present(_))
    ))]
    #[inline]
    pub fn persist_to<To>(
        &self,
        store: &mut To,
        backend: BackendArtifact,
    ) -> Result<Maybe<CheckpointAddress, submitted::Absent>, CheckpointStoreError>
    where
        To: CheckpointStore,
    {
        match self.last {
            Maybe::Present(ref resume) => {
                persist_set(store, backend, resume.checkpoints(), &mut Unobserved)
                    .map(Maybe::Present)
            },
            Maybe::Absent(reason) => Ok(Maybe::Absent(reason)),
        }
    }

    /// The resume the next submission of `program` starts from: the one held,
    /// else the set the restorer holds for it, the restorer spent either way.
    /// A restorer that fails or holds no set leaves the submission fresh: the
    /// set is a cache of a judgement the submission makes anyway.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the held resume when one is held; otherwise the restored
    ///   set's resume when the restorer answers one, and no resume when it
    ///   answers none or fails; the restorer is spent.
    /// - panics: propagates a panic from the restorer.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`persist_to`](Self::persist_to); a program the
    ///   restorer holds no set for is judged whole.
    /// - witness: `session::tests::a_held_set_persists_to_another_store_and_restores_a_first_submission_1816`
    #[spec(ensures: matches!(self.restoring, Maybe::Absent(_)))]
    fn starting(
        &mut self,
        program: &Program,
    ) -> Maybe<Resume, submitted::Absent>
    {
        let held = core::mem::replace(&mut self.last, Maybe::Absent(submitted::Absent::Fresh));
        let mut restorer = match core::mem::replace(
            &mut self.restoring,
            Maybe::Absent(restoring::Absent::Spent),
        ) {
            Maybe::Present(restorer) => restorer,
            Maybe::Absent(reason) => {
                self.restoring = Maybe::Absent(reason);
                return held;
            },
        };
        match held {
            Maybe::Present(_) => held,
            Maybe::Absent(_) => match restorer.restored(program) {
                Ok(Maybe::Present(checkpoints)) => {
                    Resume::from_checkpoints(checkpoints).map_or(held, Maybe::Present)
                },
                Ok(Maybe::Absent(_)) | Err(_) => held,
            },
        }
    }

    /// Submit a revision: resume from the latest one, or judge it whole, then
    /// persist its checkpoints to a store that keeps them.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the session holds the revision's resume and, when
    ///   the store keeps sets ([`Keeping::Kept`]), the store its checkpoints at
    ///   its address; the census of the pass is returned.
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
        self.submit_retiring(program, observer, &Unretired)
            .map(Polled::whole)
    }

    /// [`submit`](Self::submit), polling `retirement` before each item the
    /// pass adopts or judges: retired, the pass stops before the item it
    /// polled at, nothing is persisted, and the session keeps the resume it
    /// held, or the set it restored when it held none, for the next submission
    /// to resume from.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: while every poll answers wanted, [`submit`](Self::submit)'s
    ///   census as [`Polled::Whole`]. Retired, [`Polled::Retired`] with the
    ///   retirement; the session holds the resume it held before, or, when it
    ///   held none, the set [`restore_from`](Self::restore_from)'s restorer
    ///   answered, if any, and the store is not addressed.
    /// - fails: as [`submit`](Self::submit).
    /// - panics: none.
    ///
    /// # Errors
    /// As [`submit`](Self::submit).
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a submission retired part way leaves the session the
    ///   resume it held, and the next submission resumes from it, judging and
    ///   recording what it would have with no retired one before it.
    /// - witness: `session::tests::a_retired_submission_keeps_the_resume_it_held_1547`
    #[spec(
        captures: held = self.last().map(Resume::census),
        ensures: |ret| match ret {
            | Ok(Polled::Whole(census)) => {
                matches!(self.last, Maybe::Present(ref latest) if latest.census() == census && latest.checkpoints().items().len() == program.items().len())
            },
            | Ok(Polled::Retired(..)) => {
                matches!(held, Maybe::Absent(_)) || self.last().map(Resume::census) == held
            },
            | Err(SessionError::Resume(_)) => {
                matches!(self.last, Maybe::Absent(submitted::Absent::Fresh))
            },
            | Err(SessionError::Store(_)) => {
                matches!(self.last, Maybe::Present(ref latest) if latest.checkpoints().items().len() == program.items().len())
            },
        },
    )]
    #[inline]
    pub fn submit_retiring<Observer, Poll>(
        &mut self,
        program: &mut Program,
        observer: &mut Observer,
        retirement: &Poll,
    ) -> Result<Polled<ResumeCensus, Poll::Retired, ()>, SessionError>
    where
        Store: CheckpointStore,
        Observer: CheckpointObserver,
        Poll: Retirement,
    {
        let previous = self.starting(program);
        let polled = resume_or_check(previous, program, self.budget, retirement)
            .map_err(SessionError::Resume)?;
        self.settled(program, polled, observer)
    }

    /// [`submit`](Self::submit) of a revision laid after `leading`, the state
    /// [`lead`](crate::lead) left over a program the revision lays first: only
    /// the items after that program's are judged or adopted.
    ///
    /// # Specification
    /// - requires: as [`resume_after`](crate::resume_after).
    /// - ensures: as [`submit`](Self::submit), the pass being
    ///   [`resume_after`](crate::resume_after) from the resume the session
    ///   holds, if any, after `leading`.
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
        self.submit_after_retiring(program, leading, observer, &Unretired)
            .map(Polled::whole)
    }

    /// [`submit_after`](Self::submit_after), polling `retirement` before each
    /// item the pass adopts or judges, as
    /// [`submit_retiring`](Self::submit_retiring) does.
    ///
    /// # Specification
    /// - requires: as [`resume_after`](crate::resume_after).
    /// - ensures: as [`submit_retiring`](Self::submit_retiring), the pass being
    ///   [`resume_after`](crate::resume_after)'s.
    /// - fails: as [`submit`](Self::submit).
    /// - panics: none.
    ///
    /// # Errors
    /// As [`submit`](Self::submit).
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`submit_retiring`](Self::submit_retiring).
    /// - witness: `session::tests::a_retired_submission_keeps_the_resume_it_held_1547`
    #[spec(
        captures: held = self.last().map(Resume::census),
        ensures: |ret| match ret {
            | Ok(Polled::Whole(census)) => {
                matches!(self.last, Maybe::Present(ref latest) if latest.census() == census && latest.checkpoints().items().len() == program.items().len())
            },
            | Ok(Polled::Retired(..)) => {
                matches!(held, Maybe::Absent(_)) || self.last().map(Resume::census) == held
            },
            | Err(SessionError::Resume(_)) => {
                matches!(self.last, Maybe::Absent(submitted::Absent::Fresh))
            },
            | Err(SessionError::Store(_)) => {
                matches!(self.last, Maybe::Present(ref latest) if latest.checkpoints().items().len() == program.items().len())
            },
        },
    )]
    #[inline]
    pub fn submit_after_retiring<Observer, Poll>(
        &mut self,
        program: &mut Program,
        leading: &Arc<Leading>,
        observer: &mut Observer,
        retirement: &Poll,
    ) -> Result<Polled<ResumeCensus, Poll::Retired, ()>, SessionError>
    where
        Store: CheckpointStore,
        Observer: CheckpointObserver,
        Poll: Retirement,
    {
        let previous = self.starting(program);
        let polled = resume_after_retiring(previous, leading, program, retirement)
            .map_err(SessionError::Resume)?;
        self.settled(program, polled, observer)
    }

    /// Persist and hold a whole pass's resume, or hold again the resume a
    /// retired pass handed back.
    ///
    /// # Specification
    /// - requires: `polled` is the pass over `program`.
    /// - ensures: whole, as [`persisted`](Self::persisted); retired, the
    ///   session holds what the pass handed back and the store is not
    ///   addressed.
    /// - fails: [`SessionError::Store`] when persisting a whole pass fails.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`submit_retiring`](Self::submit_retiring).
    /// - witness: `session::tests::a_retired_submission_keeps_the_resume_it_held_1547`
    #[spec(
        captures: retired = matches!(polled, Polled::Retired(..)),
        ensures: |ret| match ret {
            Ok(Polled::Retired(..)) => retired,
            Ok(Polled::Whole(ref census)) => !retired
                && matches!(self.last, Maybe::Present(ref latest) if latest.census() == *census),
            Err(_) => !retired,
        },
    )]
    fn settled<Observer, Retired>(
        &mut self,
        program: &Program,
        polled: Resuming<Retired>,
        observer: &mut Observer,
    ) -> Result<Polled<ResumeCensus, Retired, ()>, SessionError>
    where
        Store: CheckpointStore,
        Observer: CheckpointObserver,
    {
        match polled {
            Polled::Whole(next) => self.persisted(program, next, observer).map(Polled::Whole),
            Polled::Retired(retired, held) => {
                self.last = held;
                Ok(Polled::Retired(retired, ()))
            },
        }
    }

    /// Persist `next`'s checkpoints of `program` to a store that keeps them
    /// and hold `next`, whether or not persisting succeeds.
    ///
    /// # Specification
    /// - requires: `next` is the pass over `program`.
    /// - ensures: the session holds `next`; on success its census is returned.
    ///   A store that keeps nothing ([`Keeping::Discarded`]) is neither
    ///   addressed nor handed the set.
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
        if Store::KEEPING == Keeping::Discarded {
            self.last = Maybe::Present(next);
            return Ok(census);
        }
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
