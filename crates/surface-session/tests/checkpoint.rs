//! Checkpoints across sessions: written by one, restored by the next, and a
//! store's failure reported rather than raised; the kernel checkpoint read
//! back through the kernel's decoder, and refused there when its bytes are.

use std::path::Path;
use std::path::PathBuf;

use anodized::spec;
use gandr_core_incremental::BackendArtifact;
use gandr_core_incremental::CheckpointAddress;
use gandr_core_incremental::CheckpointStore;
use gandr_core_incremental::CheckpointStoreError;
use gandr_core_incremental::Checkpoints;
use gandr_core_incremental::FileCheckpointStore;
use gandr_core_incremental::ItemCount;
use gandr_core_incremental::ItemSource as _;
use gandr_core_incremental::MemoryCheckpointStore;
use gandr_core_incremental::stored;
use gandr_kernel_term::DecodeError;
use gandr_kernel_term::MalformedSite;
use gandr_kernel_term::decode;
use gandr_storage_artifact::ArtifactError;
use gandr_storage_artifact::ArtifactManifest;
use gandr_storage_artifact::ArtifactRecordSet;
use gandr_storage_artifact::ManifestImage;
use gandr_storage_artifact::SegmentBytes;
use gandr_storage_artifact::build;
use gandr_storage_records::BlockStore;
use gandr_storage_records::FailureContext;
use gandr_storage_records::InMemoryBlockStore;
use gandr_storage_records::NodeHash;
use gandr_storage_records::RecordTreeError;
use gandr_storage_records::StoredNode;
use gandr_storage_records::TreeParams;
use gandr_surface_dispatcher::Composed;
use gandr_surface_dispatcher::SourceRoot;
use gandr_surface_lowering::namespace::DottedName;
use gandr_surface_lowering::namespace::NamePath;
use gandr_surface_session::KernelCheckpoint;
use gandr_surface_session::Persistence;
use gandr_surface_session::Revision;
use gandr_surface_session::Session;
use gandr_surface_session::SurfaceItems;
use gandr_surface_session::reopened;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use crate::common::backend;
use crate::common::batch;
use crate::common::grammar;
use crate::common::resumed;

/// The revision the first session writes checkpoints for.
const WRITTEN: &str = r#"import "file:///lib/parse.gandr" as parse ;
def a = 1 ;
def b : Integer ;
def b = a ;"#;

/// That revision with one definition appended.
const APPENDED: &str = r#"import "file:///lib/parse.gandr" as parse ;
def a = 1 ;
def b : Integer ;
def b = a ;
def c = b ;"#;

/// A scratch directory's label, unique among the tests.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Label(&'static str);

/// A process-and-label directory under the system temporary directory.
/// Construction and drop attempt removal; neither promises that IO succeeds.
///
/// # Specification
/// - requires: the consuming fixture’s context.
/// - ensures: Owns the fixture directory’s path for best-effort cleanup.
/// - executable: none — The declaration has no runtime invocation; its methods
///   state the path or store relations at the boundary where their inputs and
///   outcomes exist.
///
/// # Adequacy
/// - hypothesis: L3 — the cited storage lifecycle fixture, observed through the
///   externally retained checkpoint or filesystem state; this does not claim
///   universal IO success.
/// - witness: `tests::checkpoint::a_reopened_session_resumes_from_the_checkpoints_a_dropped_one_wrote`
#[repr(transparent)]
#[derive(Debug)]
struct Scratch(PathBuf);

impl Scratch
{
    /// The scratch directory of `label` for this process.
    ///
    /// # Specification
    /// - requires: the label is exclusive to this test in the current process
    ///   and contains neither a path separator nor a NUL byte.
    /// - ensures: names a directory under the platform’s temporary directory
    ///   using the process ID and label. Attempts to remove a prior directory;
    ///   it neither creates the directory nor guarantees successful removal.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the real file-checkpoint reopen fixture, observed
    ///   through restore/adoption and the absence of its directory after drop.
    ///   The predicate checks the exact process-and-label namespace without
    ///   repeating filesystem IO; cleanup failure remains best effort.
    /// - witness: `tests::checkpoint::a_reopened_session_resumes_from_the_checkpoints_a_dropped_one_wrote`
    #[spec(
        requires: !label.0.contains(std::path::is_separator)
    && !label.0.as_bytes().contains(&0_u8),
        ensures: |ret| {
    ret
        .0
        .file_name()
        .and_then(|name| name.to_str())
        .and_then(|name| name.strip_prefix("gandr-surface-session-tests-"))
        .and_then(|name| name.split_once('-'))
        .is_some_and(|(process, name)| {
            process.parse::<u32>() == Ok(std::process::id()) && name == label.0
        })
},
    )]
    fn new(label: Label) -> Self
    {
        let path = std::env::temp_dir().join(format!(
            "gandr-surface-session-tests-{}-{}",
            std::process::id(),
            label.0
        ));
        drop(std::fs::remove_dir_all(&path));
        Self(path)
    }

    /// The directory's path.
    ///
    /// # Specification
    /// trivial.
    fn path(&self) -> &Path
    {
        &self.0
    }
}

impl Drop for Scratch
{
    /// Remove the directory.
    ///
    /// # Specification
    /// - requires: the directory is still owned exclusively by this fixture.
    /// - ensures: attempts recursive removal and ignores an IO refusal.
    /// - panics: none.
    /// - executable: none — Drop returns neither a removal status nor an owned
    ///   path. A postcondition could only repeat filesystem IO and still could
    ///   not guarantee cleanup after an ignored refusal; the fixture observes
    ///   successful cleanup from a separately retained path.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the real file-checkpoint fixture after its session
    ///   closes, with `try_exists` as the external observer. This catches
    ///   skipped cleanup on the successful IO path, not every possible
    ///   filesystem refusal.
    /// - witness: `tests::checkpoint::a_reopened_session_resumes_from_the_checkpoints_a_dropped_one_wrote`
    fn drop(&mut self)
    {
        drop(std::fs::remove_dir_all(&self.0));
    }
}

/// A store that holds nothing and refuses every set.
///
/// # Specification
/// - requires: the consuming fixture’s context.
/// - ensures: Implements a checkpoint store that holds nothing and refuses all
///   writes.
/// - executable: none — The declaration has no runtime invocation; its methods
///   state the path or store relations at the boundary where their inputs and
///   outcomes exist.
///
/// # Adequacy
/// - hypothesis: L3 — the cited storage lifecycle fixture, observed through the
///   externally retained checkpoint or filesystem state; this does not claim
///   universal IO success.
/// - witness: `tests::checkpoint::a_store_failure_is_reported_and_the_session_still_resumes`
#[derive(Debug, Default)]
struct Refusing;

impl CheckpointStore for Refusing
{
    /// Nothing is stored.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: reports `NotStored` for every checkpoint address and backend.
    /// - fails: never.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — reopening after the store refused two submissions,
    ///   observed as a fresh session rather than a restored checkpoint set. The
    ///   predicate fixes the absence reason for every invocation.
    /// - witness: `tests::checkpoint::a_store_failure_is_reported_and_the_session_still_resumes`
    #[spec(
        ensures: |ret| matches!(ret, Ok(Maybe::Absent(stored::Absent::NotStored))),
    )]
    fn load(
        &mut self,
        _address: CheckpointAddress,
        _backend: BackendArtifact,
    ) -> Result<Maybe<Checkpoints, stored::Absent>, CheckpointStoreError>
    {
        Ok(Maybe::Absent(stored::Absent::NotStored))
    }

    /// The file system failed.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: retains no checkpoint set.
    /// - fails: always returns Io.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two submissions followed by reopening, observed
    ///   through failure status, adoption from retained in-memory state and
    ///   absence from storage. This catches swallowing the refusal or
    ///   discarding the accepted resume.
    /// - witness: `tests::checkpoint::a_store_failure_is_reported_and_the_session_still_resumes`
    #[spec(
        ensures: |ret| matches!(ret, Err(CheckpointStoreError::Io)),
    )]
    fn store(
        &mut self,
        _address: CheckpointAddress,
        _backend: BackendArtifact,
        _checkpoints: &Checkpoints,
    ) -> Result<(), CheckpointStoreError>
    {
        Err(CheckpointStoreError::Io)
    }
}

#[test]
fn a_reopened_session_resumes_from_the_checkpoints_a_dropped_one_wrote()
{
    let scratch = Scratch::new(Label("reopen"));
    {
        let store = FileCheckpointStore::open(scratch.path()).expect("the directory opens");
        let mut writer = Session::new(
            grammar(),
            SourceRoot::Strict,
            store,
            InMemoryBlockStore::default(),
            backend(),
        );
        let written = writer.submit(SourceText::from(WRITTEN)).expect("submits");
        assert!(
            matches!(written.resumed(), Maybe::Present(resumed) if resumed.persistence() == Persistence::Stored),
            "the file store holds the written checkpoints"
        );
    }

    let store = FileCheckpointStore::open(scratch.path()).expect("the directory reopens");
    let reopened = Session::reopen(
        grammar(),
        SourceRoot::Strict,
        store,
        InMemoryBlockStore::default(),
        backend(),
        SourceText::from(WRITTEN),
    )
    .expect("reopens");
    assert_eq!(
        reopened.restored(),
        Maybe::Present(ItemCount::from(2_usize)),
        "both items' checkpoints are restored"
    );
    let mut session = reopened.into_session();
    assert_eq!(
        session
            .resolve_import(&NamePath::from(DottedName::from("parse")))
            .map(|row| row.uri().to_string()),
        Maybe::Present("file:///lib/parse.gandr".to_owned()),
        "the reopened session resolves the revision's imports"
    );
    let appended = session.submit(SourceText::from(APPENDED)).expect("submits");
    let Maybe::Present(resumed_pass) = appended.resumed()
    else {
        panic!("the appended revision is resumed");
    };
    assert_eq!(
        resumed_pass.census().adopted,
        ItemCount::from(2_usize),
        "the next submission adopts both restored checkpoints"
    );
    let program = SurfaceItems::new(grammar())
        .items(&Revision::from(APPENDED))
        .expect("the appended revision is offered");
    assert_eq!(
        resumed(&session),
        batch(&program),
        "the resume over restored checkpoints agrees with batch"
    );
    let path = scratch.path().to_owned();
    assert_eq!(path.parent(), Some(std::env::temp_dir().as_path()));
    drop(session);
    drop(scratch);
    assert!(
        !path
            .try_exists()
            .expect("the scratch path can be inspected")
    );
}

#[test]
fn a_store_holding_nothing_reopens_fresh()
{
    let empty = Session::reopen(
        grammar(),
        SourceRoot::Strict,
        MemoryCheckpointStore::default(),
        InMemoryBlockStore::default(),
        backend(),
        SourceText::from(WRITTEN),
    )
    .expect("reopens");
    assert_eq!(
        empty.restored(),
        Maybe::Absent(reopened::Absent::NotStored),
        "an empty store restores nothing"
    );
    let mut session = empty.into_session();
    let submission = session.submit(SourceText::from(WRITTEN)).expect("submits");
    assert!(
        matches!(submission.resumed(), Maybe::Present(resumed) if resumed.census().adopted == ItemCount::from(0_usize)),
        "a fresh session judges every item"
    );

    let other = Session::reopen(
        grammar(),
        SourceRoot::Strict,
        session.into_store(),
        InMemoryBlockStore::default(),
        BackendArtifact::from(b"another checker".as_slice()),
        SourceText::from(WRITTEN),
    )
    .expect("reopens");
    assert_eq!(
        other.restored(),
        Maybe::Absent(reopened::Absent::OtherBackend),
        "checkpoints another backend judged are not restored"
    );

    let refused = Session::reopen(
        grammar(),
        SourceRoot::Strict,
        other.into_session().into_store(),
        InMemoryBlockStore::default(),
        backend(),
        SourceText::from("def a = 1 ;\nret a"),
    )
    .expect("reopens");
    assert_eq!(
        refused.restored(),
        Maybe::Absent(reopened::Absent::RefusedWhole),
        "a revision refused whole has no program to restore for"
    );
}

#[test]
fn a_store_failure_is_reported_and_the_session_still_resumes()
{
    let mut session = Session::new(
        grammar(),
        SourceRoot::Strict,
        Refusing,
        InMemoryBlockStore::default(),
        backend(),
    );
    let first = session.submit(SourceText::from(WRITTEN)).expect("submits");
    assert!(
        matches!(first.resumed(), Maybe::Present(resumed) if resumed.persistence() == Persistence::Failed(CheckpointStoreError::Io)),
        "the store's failure is the submission's to report, not an error"
    );
    let second = session.submit(SourceText::from(APPENDED)).expect("submits");
    assert!(
        matches!(second.resumed(), Maybe::Present(resumed) if resumed.census().adopted == ItemCount::from(2_usize)),
        "the session resumes from the revision whose checkpoints were not stored"
    );
    assert_eq!(
        usize::from(session.lowerings()),
        2_usize,
        "one lowering per submission"
    );
    let reopened = Session::reopen(
        grammar(),
        SourceRoot::Strict,
        session.into_store(),
        InMemoryBlockStore::default(),
        backend(),
        SourceText::from(APPENDED),
    )
    .expect("a store with failed writes reopens fresh");
    assert_eq!(
        reopened.restored(),
        Maybe::Absent(reopened::Absent::NotStored)
    );
}

#[test]
fn a_reopened_session_reads_its_kernel_checkpoint_through_the_decoder()
{
    let mut writer = Session::new(
        grammar(),
        SourceRoot::Strict,
        MemoryCheckpointStore::default(),
        InMemoryBlockStore::default(),
        backend(),
    );
    let written = writer.submit(SourceText::from(WRITTEN)).expect("submits");
    let Composed::Settled { ref kernel, .. } = *written.composed()
    else {
        panic!("the revision settles");
    };
    let Maybe::Present(checkpoint) = written.kernel()
    else {
        panic!("an accepted revision carries a kernel checkpoint");
    };
    let KernelCheckpoint::Stored(ref manifest) = *checkpoint
    else {
        panic!("the memory block store holds the kernel checkpoint: {checkpoint:?}");
    };
    let exported = decode(kernel.as_image()).expect("the kernel's own export decodes");
    let names: Vec<Vec<&str>> = exported
        .declarations()
        .iter()
        .map(|marked| {
            marked
                .declaration()
                .name()
                .segments()
                .iter()
                .map(AsRef::as_ref)
                .collect()
        })
        .collect();
    assert_eq!(
        vec![vec!["a"], vec!["b"]],
        names,
        "both definitions crossed into the kernel"
    );
    // The manifest leaves the session as bytes, as a caller persists it.
    let carried = manifest.encode();
    let blocks = writer.blocks().clone();
    let store = writer.into_store();

    let reopened = Session::reopen(
        grammar(),
        SourceRoot::Strict,
        store,
        blocks,
        backend(),
        SourceText::from(WRITTEN),
    )
    .expect("reopens")
    .into_session();
    let manifest = ArtifactManifest::decode(ManifestImage::from(carried.as_ref()))
        .expect("the manifest decodes");
    assert_eq!(
        Ok(exported),
        reopened.read_kernel(&manifest),
        "the reopened session reads the checkpoint back as the export's decoding"
    );

    let elsewhere = Session::new(
        grammar(),
        SourceRoot::Strict,
        MemoryCheckpointStore::default(),
        InMemoryBlockStore::default(),
        backend(),
    );
    assert!(
        matches!(
            elsewhere.read_kernel(&manifest),
            Err(ArtifactError::Records {
                refusal: RecordTreeError::UnknownNode { .. }
            })
        ),
        "a block store that never held the checkpoint reads nothing for it"
    );
}

#[test]
fn a_matching_identity_over_bytes_the_kernel_refuses_is_refused()
{
    let mut writer = Session::new(
        grammar(),
        SourceRoot::Strict,
        MemoryCheckpointStore::default(),
        InMemoryBlockStore::default(),
        backend(),
    );
    let written = writer.submit(SourceText::from(WRITTEN)).expect("submits");
    let Composed::Settled { ref kernel, .. } = *written.composed()
    else {
        panic!("the revision settles");
    };
    // The genuine records under a header whose magic is broken: a writer that
    // mints a manifest over bytes the kernel refuses.
    let genuine = ArtifactRecordSet::from_artifact(kernel.as_image()).expect("the export cuts");
    let mut header = genuine.header().as_ref().to_vec();
    let magic = header.first_mut().expect("the header opens with its magic");
    *magic ^= 0xFF;
    let forged = ArtifactRecordSet::from_records(
        SegmentBytes::from(header.as_slice()),
        genuine.records().to_vec(),
    )
    .expect("the keys are the genuine ones");
    let mut blocks = writer.blocks().clone();
    let minted =
        build(&forged, TreeParams::current(), &mut blocks).expect("a writer commits any set");
    let carried = ArtifactManifest::decode(ManifestImage::from(minted.encode().as_ref()))
        .expect("the manifest decodes");
    assert_eq!(
        minted.identity(),
        carried.identity(),
        "the carried manifest reproduces the minted identity"
    );

    let reader = Session::new(
        grammar(),
        SourceRoot::Strict,
        MemoryCheckpointStore::default(),
        blocks,
        backend(),
    );
    assert_eq!(
        Err(ArtifactError::Kernel {
            refusal: DecodeError::Malformed {
                site: MalformedSite::Header,
            },
        }),
        reader.read_kernel(&carried),
        "the tree is held and seals under the matching identity, and the kernel's decoder refuses \
         its bytes"
    );
}
/// A block store whose node-count width is exhausted before any admission.
///
/// # Specification
/// - requires: the fixture’s session context.
/// - ensures: admits no nodes and refuses insertion because the count width is
///   exhausted.
/// - executable: none — The type has no invocation; its `BlockStore` methods
///   specify the two failure boundaries.
///
/// # Adequacy
/// - hypothesis: L3 — an accepted two-item revision and one appended item,
///   observed through kernel failure, independently persisted incremental
///   checkpoints, retained edit image and adoption. A genuine manifest from
///   another store checks that no blocks were admitted.
/// - witness: `tests::checkpoint::a_kernel_store_failure_preserves_resume_and_edit_state`
#[derive(Debug, Default)]
struct ExhaustedBlocks;

impl BlockStore for ExhaustedBlocks
{
    /// Refuse an insertion at the exhausted count boundary.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: admits nothing.
    /// - fails: returns `ArithmeticOverflow` for the node-count boundary.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the kernel-checkpoint failure path, observed through
    ///   retained incremental state and subsequent adoption, not merely the
    ///   injected error’s spelling.
    /// - witness: `tests::checkpoint::a_kernel_store_failure_preserves_resume_and_edit_state`
    #[spec(
        ensures: |ret| matches!(ret, Err(RecordTreeError::ArithmeticOverflow { .. })),
    )]
    fn insert(
        &mut self,
        _node: StoredNode<'_>,
    ) -> Result<(), RecordTreeError>
    {
        Err(RecordTreeError::ArithmeticOverflow {
            context: FailureContext::from("fixture node count"),
        })
    }

    /// No identity was admitted.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns no bytes.
    /// - fails: reports the exact requested identity as `UnknownNode`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a genuine manifest stored elsewhere, observed through
    ///   `Session::read_kernel` refusing its root after the local checkpoint
    ///   write failed.
    /// - witness: `tests::checkpoint::a_kernel_store_failure_preserves_resume_and_edit_state`
    #[spec(
        ensures: |ret| {
    matches!(ret, Err(RecordTreeError::UnknownNode { hash : absent }) if absent == hash)
},
    )]
    fn load(
        &self,
        hash: NodeHash,
    ) -> Result<StoredNode<'_>, RecordTreeError>
    {
        Err(RecordTreeError::UnknownNode { hash })
    }
}

#[test]
fn a_kernel_store_failure_preserves_resume_and_edit_state()
{
    let mut session = Session::new(
        grammar(),
        SourceRoot::Strict,
        MemoryCheckpointStore::default(),
        ExhaustedBlocks,
        backend(),
    );
    let first = session
        .submit(SourceText::from(WRITTEN))
        .expect("the revision is accepted despite the block refusal");
    assert!(matches!(
        first.kernel(),
        Maybe::Present(KernelCheckpoint::Failed(ArtifactError::Records {
            refusal: RecordTreeError::ArithmeticOverflow { .. }
        }))
    ));
    assert!(
        matches!(first.resumed(), Maybe::Present(resumed) if resumed.persistence() == Persistence::Stored)
    );
    let Composed::Settled { ref kernel, .. } = *first.composed()
    else {
        panic!("the accepted revision settles");
    };
    let records = ArtifactRecordSet::from_artifact(kernel.as_image())
        .expect("the accepted kernel cuts into records");
    let manifest = build(
        &records,
        TreeParams::current(),
        &mut InMemoryBlockStore::default(),
    )
    .expect("another store admits the genuine records");
    assert_eq!(
        session.read_kernel(&manifest),
        Err(ArtifactError::Records {
            refusal: RecordTreeError::UnknownNode {
                hash: manifest.root_node()
            },
        })
    );
    let before = session.snapshot().clone();
    let second = session
        .submit(SourceText::from(APPENDED))
        .expect("a later revision can still resume");
    assert!(
        matches!(second.resumed(), Maybe::Present(resumed) if resumed.census().adopted == ItemCount::from(2_usize))
    );
    assert_eq!(session.snapshot().items().len(), 3_usize);
    let Maybe::Present(edits) = second.edits()
    else {
        panic!("an accepted revision retains its edit script");
    };
    assert_eq!(
        gandr_surface_session::apply(before.items(), edits),
        session.snapshot().items()
    );
}
