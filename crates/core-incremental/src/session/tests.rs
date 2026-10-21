use alloc::sync::Arc;
use alloc::vec;
use alloc::vec::Vec;

use gandr_core_checker::CheckBudget;
use gandr_core_checker::signature;
use gandr_core_term::CoreArena;
use quenchant_shape::shape::Maybe;

use super::IncrementalSession;
use crate::boundary::ItemCount;
use crate::checkpoint::Resume;
use crate::checkpoint::lead;
use crate::fixture::Digits;
use crate::fixture::Key;
use crate::fixture::Label;
use crate::fixture::Position;
use crate::fixture::Scratch;
use crate::fixture::declaration;
use crate::fixture::integer;
use crate::fixture::integers;
use crate::persistence::BackendArtifact;
use crate::persistence::CheckpointObserver;
use crate::persistence::FileCheckpointStore;
use crate::persistence::MemoryCheckpointStore;
use crate::persistence::address_of;
use crate::persistence::restore;
use crate::region::Item;
use crate::region::ItemKey;
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

/// #776: a session's revisions laid after one leading state judge only their
/// own items, each resumed from the one before, and record what a whole
/// judgement records.
#[test]
fn a_session_after_a_leading_state_resumes_its_own_items_776()
{
    let fresh = || {
        IncrementalSession::new(
            MemoryCheckpointStore::default(),
            backend(),
            CheckBudget::DEFAULT,
        )
    };
    let mut leading_program = integers(CoreArena::new(), &[
        (Key("one"), Digits("1")),
        (Key("two"), Digits("2")),
    ]);
    let (_, leading) = lead(&mut leading_program, CheckBudget::DEFAULT).expect("the order builds");
    let leading = Arc::new(leading);
    let extended = || {
        let mut arena = leading_program.arena().clone();
        let three = arena.value_literal(integer(Digits("3")));
        let mut items = leading_program.items().to_vec();
        items.push(Item::new(
            ItemKey::from("three"),
            declaration(
                Position(2),
                Maybe::Absent(signature::Absent::Unsigned),
                Maybe::Present(three),
            ),
        ));
        Program::new(arena, items).expect("positions ascend")
    };
    let mut session = fresh();
    let census = session
        .submit_after(&mut extended(), &leading, &mut Quiet)
        .expect("the revision submits");
    assert_eq!(
        (census.adopted, census.judged),
        (ItemCount::from(2_usize), ItemCount::from(1_usize)),
        "the leading items are the state's and the revision's own is judged"
    );
    let again = session
        .submit_after(&mut extended(), &leading, &mut Quiet)
        .expect("the revision submits again");
    assert_eq!(
        (again.adopted, again.judged, again.recalled),
        (
            ItemCount::from(3_usize),
            ItemCount::from(0_usize),
            ItemCount::from(1_usize)
        ),
        "the next revision resumes from the one before, recalling only its own item"
    );
    let mut whole = fresh();
    let _whole = whole
        .submit(
            &mut integers(CoreArena::new(), &[
                (Key("one"), Digits("1")),
                (Key("two"), Digits("2")),
                (Key("three"), Digits("3")),
            ]),
            &mut Quiet,
        )
        .expect("the whole revision submits");
    let (Maybe::Present(after), Maybe::Present(whole_resume)) = (session.last(), whole.last())
    else {
        panic!("both sessions hold a resume");
    };
    assert_eq!(
        after.checkpoints(),
        whole_resume.checkpoints(),
        "to the checkpoints a whole judgement records"
    );
}

#[test]
fn a_store_failure_retains_the_new_resume_for_the_next_submission()
{
    let scratch = Scratch::new(Label("session-store-failure"));
    let directory = scratch.path().join("records");
    let saved = scratch.path().join("saved");
    let mut session = IncrementalSession::new(
        FileCheckpointStore::open(&directory).expect("open"),
        backend(),
        CheckBudget::DEFAULT,
    );
    let mut first = integers(CoreArena::new(), &[(Key("one"), Digits("1"))]);
    let first_census = session
        .submit(&mut first, &mut Quiet)
        .expect("first submission");
    assert_eq!(first_census.judged, ItemCount::from(1_usize));
    let first_address = address_of(&first).expect("resolved first program");
    std::fs::rename(&directory, &saved).expect("preserve the existing records");
    std::fs::write(&directory, b"not a directory").expect("block the configured root");

    let mut edited = integers(CoreArena::new(), &[
        (Key("one"), Digits("1")),
        (Key("two"), Digits("2")),
    ]);
    assert_eq!(
        session.submit(&mut edited, &mut Quiet),
        Err(super::SessionError::Store(super::CheckpointStoreError::Io))
    );
    let Maybe::Present(latest) = session.last()
    else {
        panic!("persistence failure retains the completed checking pass");
    };
    assert_eq!(latest.checkpoints().items().len(), 2_usize);
    assert_eq!(latest.census().judged, ItemCount::from(1_usize));
    assert_eq!(latest.census().adopted, ItemCount::from(1_usize));

    std::fs::remove_file(&directory).expect("remove the test obstruction");
    std::fs::rename(&saved, &directory).expect("restore the record directory");
    let next = session
        .submit(&mut edited, &mut Quiet)
        .expect("persist the retained revision");
    assert_eq!(next.adopted, ItemCount::from(2_usize));
    assert_eq!(next.judged, ItemCount::from(0_usize));
    let mut store = session.into_store();
    let Ok(Maybe::Present(earlier)) =
        restore(&mut store, &first, first_address, backend(), &mut Quiet)
    else {
        panic!("the earlier persisted revision survives the failed write");
    };
    assert_eq!(earlier.items().len(), 1_usize);
}
