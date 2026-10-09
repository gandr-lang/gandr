//! A session: one call per revision that resumes, persists and streams.

use core::fmt;

use gandr_core_checker::CheckBudget;
use quenchant_shape::shape::Maybe;

use crate::checkpoint::Resume;
use crate::checkpoint::ResumeCensus;
use crate::checkpoint::ResumeError;
use crate::checkpoint::check_program;
use crate::checkpoint::resume;
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
            /// Nothing has been submitted yet.
            Fresh,
        }
    }
}

/// Why a submission failed.
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
            | Self::Resume(error) => write!(f, "resume failed: {error}"),
            | Self::Store(error) => write!(f, "persisting the checkpoints failed: {error}"),
        }
    }
}

impl core::error::Error for SessionError
{
}

/// An incremental session over successive revisions of one program.
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
    /// - hypothesis: L3 — the surfaces are the first submission, the persisted
    ///   set and the reopened resume, separated by a first empty submission
    ///   streamed and a file session reopened in a new store over the same
    ///   directory that adopts its one item.
    /// - witness: `session::tests::submit_persists_and_streams_in_order`
    /// - witness: `session::tests::separately_reopened_file_session_resumes_supported_checkpoint`
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
            | Maybe::Present(base) => resume(base, program),
            | Maybe::Absent(_) => check_program(program, self.budget),
        }
        .map_err(SessionError::Resume)?;
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
            | Maybe::Present(ref resume) => Maybe::Present(resume),
            | Maybe::Absent(reason) => Maybe::Absent(reason),
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
mod tests
{
    use alloc::vec;
    use alloc::vec::Vec;

    use gandr_core_checker::CheckBudget;
    use gandr_core_term::CoreArena;
    use quenchant_shape::shape::Maybe;

    use super::IncrementalSession;
    use crate::boundary::ItemCount;
    use crate::checkpoint::Resume;
    use crate::fixture::Digits;
    use crate::fixture::Key;
    use crate::fixture::Label;
    use crate::fixture::Scratch;
    use crate::fixture::integers;
    use crate::persistence::BackendArtifact;
    use crate::persistence::CheckpointObserver;
    use crate::persistence::FileCheckpointStore;
    use crate::persistence::MemoryCheckpointStore;
    use crate::persistence::address_of;
    use crate::persistence::restore;
    use crate::region::Program;
    use crate::stream::SynthesisEvent;

    /// An observer that ignores what it is told.
    #[derive(Debug, Default)]
    struct Quiet;

    impl CheckpointObserver for Quiet
    {
    }

    /// The backend every fixture is judged by.
    ///
    /// # Specification
    /// trivial.
    fn backend() -> BackendArtifact
    {
        BackendArtifact::from(b"core-checker".as_slice())
    }

    #[test]
    fn submit_persists_and_streams_in_order()
    {
        let mut session = IncrementalSession::new(
            MemoryCheckpointStore::default(),
            backend(),
            CheckBudget::DEFAULT,
        );
        let mut empty = Program::new(CoreArena::new(), Vec::new()).expect("no items ascend");
        let census = session.submit(&mut empty, &mut Quiet).expect("submit");
        assert_eq!(census.adopted, ItemCount::from(0_usize), "nothing to adopt");
        let Maybe::Present(stream) = session.stream()
        else {
            panic!("a submitted session streams");
        };
        assert_eq!(
            stream.collect::<Vec<SynthesisEvent>>(),
            vec![
                SynthesisEvent::Started {
                    item_count: ItemCount::from(0_usize),
                },
                SynthesisEvent::Completed,
            ],
            "an empty program opens and closes"
        );
        let address = address_of(&empty).expect("resolved");
        let mut store = session.into_store();
        assert!(
            matches!(
                restore(&mut store, &empty, address, backend(), &mut Quiet),
                Ok(Maybe::Present(_))
            ),
            "and its checkpoints are persisted"
        );
    }

    #[test]
    fn separately_reopened_file_session_resumes_supported_checkpoint()
    {
        let scratch = Scratch::new(Label("reopened-session"));
        let program = || integers(CoreArena::new(), &[(Key("one"), Digits("1"))]);

        let mut first = IncrementalSession::new(
            FileCheckpointStore::open(scratch.path()).expect("open"),
            backend(),
            CheckBudget::DEFAULT,
        );
        let census = first.submit(&mut program(), &mut Quiet).expect("submit");
        assert_eq!(
            census.judged,
            ItemCount::from(1_usize),
            "a first submission judges"
        );
        drop(first.into_store());

        let address = address_of(&program()).expect("resolved");
        let mut loader = FileCheckpointStore::open(scratch.path()).expect("reopen");
        let Ok(Maybe::Present(checkpoints)) =
            restore(&mut loader, &program(), address, backend(), &mut Quiet)
        else {
            panic!("the first session's checkpoints are on disk");
        };
        drop(loader);

        let resume = Resume::from_checkpoints(checkpoints).expect("the order builds");
        let mut reopened = IncrementalSession::reopen(
            FileCheckpointStore::open(scratch.path()).expect("reopen"),
            backend(),
            resume,
        );
        let census = reopened.submit(&mut program(), &mut Quiet).expect("submit");
        assert_eq!(
            census.adopted,
            ItemCount::from(1_usize),
            "the restored checkpoint is adopted"
        );
    }
}
