//! A keystroke's judgement takes each standing declaration from the last
//! pass, and a taken declaration keeps the entries that its judgement added
//! to the tables that the bridge reads (#7373, #7399, #7428).

use gandr_core_checker_base::CheckBudget;
use gandr_core_checker_base::CheckingContext;
use gandr_core_checker_base::check_declaration_supported;
use gandr_core_checker_base::support::OtherTables;
use gandr_core_incremental::BackendArtifact;
use gandr_core_incremental::ItemCount;
use gandr_core_incremental::MemoryCheckpointStore;
use gandr_core_incremental::decode_checkpoints;
use gandr_core_incremental::encode_checkpoints;
use gandr_storage_records::InMemoryBlockStore;
use gandr_surface_dispatcher::Lowered;
use gandr_surface_dispatcher::LoweringCount;
use gandr_surface_dispatcher::SourceRoot;
use gandr_surface_dispatcher::item_program;
use gandr_surface_dispatcher::lower_source;
use gandr_surface_grammar::built_in;
use gandr_surface_session::Reusing;
use gandr_surface_session::Session;
use gandr_surface_session::Submission;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

/// The handler fixture: a declaration at a row, and a handler of it.
const HANDLER: &str =
    include_str!("taking/fixtures/a-taken-handler-keeps-its-rows-and-handled-entries-7373.gandr");

/// The reflexivity fixture: two theories, and a reflexivity at a function
/// type.
const REFLEXIVITY: &str =
    include_str!("taking/fixtures/a-taken-reflexivity-keeps-its-dialogues-7399.gandr");

/// The payload fixture: a send and a receive over a session endpoint.
const PAYLOAD: &str = include_str!("taking/fixtures/a-taken-payload-keeps-its-type-7428.gandr");

/// The lift fixture: a type at the universe above its own.
const LIFT: &str = include_str!("taking/fixtures/a-lifted-type-is-judged-again-7428.gandr");

/// The forward fixture: a record-schema flow from a translator.
const FORWARD: &str =
    include_str!("taking/fixtures/a-taken-forward-flow-keeps-its-images-7433.gandr");

/// The reopened fixture: a law whose right endpoint unfolds under a thunk.
const REOPENED: &str =
    include_str!("taking/fixtures/a-reopened-take-replays-a-kept-dialogue-7399.gandr");

/// A fresh session over memory stores, for a fixture source.
///
/// # Specification
/// trivial.
fn session() -> Session<MemoryCheckpointStore, InMemoryBlockStore>
{
    Session::new(
        built_in().expect("the built-in grammar builds"),
        SourceRoot::Fixture,
        MemoryCheckpointStore::default(),
        InMemoryBlockStore::default(),
        BackendArtifact::from(b"gandr-surface-lsp taking tests".as_slice()),
    )
}

/// `text` submitted to `session`, which must not fault.
///
/// # Specification
/// trivial.
fn submit<'text>(
    session: &mut Session<MemoryCheckpointStore, InMemoryBlockStore>,
    text: SourceText<'text>,
) -> Submission<'text>
{
    match session.submit(text) {
        Ok(submission) => submission,
        Err(fault) => panic!("the fixture faulted: {fault}"),
    }
}

/// How many declarations a judgement of `base` with a definition appended
/// takes from the last pass, once its kernel checkpoint and its composition
/// equal a fresh session's.
///
/// # Specification
/// trivial.
fn taken_past_an_insertion(base: SourceText<'_>) -> ItemCount
{
    let mut edited = String::from(<&str>::from(base));
    edited.push('\n');
    edited.push_str("def appended = 1;");
    edited.push('\n');
    let mut taking = session();
    taking.reuse(Reusing::Standing);
    let _base = submit(&mut taking, base);
    let submission = submit(&mut taking, SourceText::from(edited.as_str()));
    let mut whole = session();
    let fresh = submit(&mut whole, SourceText::from(edited.as_str()));
    assert_eq!(
        submission.kernel(),
        fresh.kernel(),
        "a judgement that takes the standing declarations gives a fresh session's kernel checkpoint"
    );
    assert_eq!(
        submission.composed(),
        fresh.composed(),
        "a judgement that takes the standing declarations composes as a fresh session"
    );
    taking.taken()
}

/// How many declarations a session reopened over the store of `base` takes,
/// once an edit puts a definition first, beside how many checkpoints it
/// restores. The reopened session's kernel checkpoint and composition must
/// equal a fresh session's.
///
/// # Specification
/// trivial.
fn taken_past_a_reopening(base: SourceText<'_>) -> (ItemCount, ItemCount)
{
    let mut edited = String::from("def prepended = 1;");
    edited.push('\n');
    edited.push_str(<&str>::from(base));
    let mut writer = session();
    let _base = submit(&mut writer, base);
    let reopened = Session::reopen(
        built_in().expect("the built-in grammar builds"),
        SourceRoot::Fixture,
        writer.into_store(),
        InMemoryBlockStore::default(),
        BackendArtifact::from(b"gandr-surface-lsp taking tests".as_slice()),
        base,
    )
    .expect("the store reopens");
    let Maybe::Present(restored) = reopened.restored()
    else {
        panic!("the reopened store restores the checkpoints");
    };
    let mut taking = reopened.into_session();
    taking.reuse(Reusing::Standing);
    let submission = submit(&mut taking, SourceText::from(edited.as_str()));
    let mut whole = session();
    let fresh = submit(&mut whole, SourceText::from(edited.as_str()));
    assert!(
        matches!(fresh.kernel(), Maybe::Present(_)),
        "the kernel admits the edited revision"
    );
    assert_eq!(
        submission.kernel(),
        fresh.kernel(),
        "the kernel crosses each taken declaration with its kept entries, as a fresh session's"
    );
    assert_eq!(
        submission.composed(),
        fresh.composed(),
        "the reopened session that takes composes as a fresh session"
    );
    (restored, taking.taken())
}

/// A taken declaration at a row and a taken handler keep the entries that
/// their judgement added to the rows and the handlers (#7373). The bridge
/// reads `tallyHandled` as the fold of its subject's program at its recorded
/// types. Its checkpoint keeps those entries by place, and the take seats
/// them. Without the
/// entries, the kernel checkpoint of the taking session differs. The kept
/// entries read back from bytes as written.
#[test]
fn a_taken_handler_keeps_its_rows_and_handled_entries_7373()
{
    assert_eq!(
        taken_past_an_insertion(SourceText::from(HANDLER)),
        ItemCount::from(4_usize),
        "the declarations the theory lowers to, `tallied` and `tallyHandled` are taken; the appended definition is decided"
    );
    let mut kept = session();
    let _kept = submit(&mut kept, SourceText::from(HANDLER));
    let Maybe::Present(resume) = kept.last()
    else {
        panic!("the submission resumes");
    };
    let checkpoints = resume.checkpoints();
    assert!(
        checkpoints
            .items()
            .iter()
            .any(|checkpoint| matches!(checkpoint.tables(), Maybe::Present(_))),
        "a checkpoint keeps the entries of `tallyHandled`"
    );
    let bytes = encode_checkpoints(checkpoints).expect("the checkpoints encode");
    assert_eq!(
        decode_checkpoints(&bytes).expect("the checkpoints decode"),
        *checkpoints,
        "the kept entries read back as written"
    );
}

/// A taken reflexivity keeps the dialogues that its judgement recorded
/// (#7399). The reflexivity of `unreadCall` relates its point to each
/// endpoint by a dialogue that the bridge crosses with it. Its checkpoint
/// keeps the dialogues, each constant at the item that holds it, and the take
/// seats them. The kept dialogues read back from bytes as written.
#[test]
fn a_taken_reflexivity_keeps_its_dialogues_7399()
{
    assert_eq!(
        taken_past_an_insertion(SourceText::from(REFLEXIVITY)),
        ItemCount::from(5_usize),
        "the declarations the two theories lower to and `unreadCall` are taken; the appended definition is decided"
    );
    let mut kept = session();
    let _kept = submit(&mut kept, SourceText::from(REFLEXIVITY));
    let Maybe::Present(resume) = kept.last()
    else {
        panic!("the submission resumes");
    };
    let checkpoints = resume.checkpoints();
    assert!(
        checkpoints
            .items()
            .iter()
            .any(|checkpoint| matches!(checkpoint.tables(), Maybe::Present(_))),
        "a checkpoint keeps the reflexivity of `unreadCall`"
    );
    let bytes = encode_checkpoints(checkpoints).expect("the checkpoints encode");
    assert_eq!(
        decode_checkpoints(&bytes).expect("the checkpoints decode"),
        *checkpoints,
        "the kept dialogues read back as written"
    );
}

/// A taken send and receive keep the payload types that their judgement
/// recorded (#7428). A session reopened over a store crosses the taken
/// `deliver` again, and the bridge reads the type of the received payload at
/// the receive's node. The take seats the kept types at the places that an
/// edit shifts. The kept types read back from bytes as written.
#[test]
fn a_taken_payload_keeps_its_type_7428()
{
    assert_eq!(
        taken_past_an_insertion(SourceText::from(PAYLOAD)),
        ItemCount::from(1_usize),
        "`deliver` is taken; the appended definition is decided"
    );
    assert_eq!(
        taken_past_a_reopening(SourceText::from(PAYLOAD)),
        (ItemCount::from(1_usize), ItemCount::from(1_usize)),
        "the checkpoint of `deliver` is restored and taken; the definition put first is decided"
    );
    let mut kept = session();
    let _kept = submit(&mut kept, SourceText::from(PAYLOAD));
    let Maybe::Present(resume) = kept.last()
    else {
        panic!("the submission resumes");
    };
    let checkpoints = resume.checkpoints();
    assert!(
        checkpoints
            .items()
            .iter()
            .any(|checkpoint| matches!(checkpoint.tables(), Maybe::Present(_))),
        "a checkpoint keeps the payload types of `deliver`"
    );
    let bytes = encode_checkpoints(checkpoints).expect("the checkpoints encode");
    assert_eq!(
        decode_checkpoints(&bytes).expect("the checkpoints decode"),
        *checkpoints,
        "the kept payload types read back as written"
    );
}

/// A taken forward flow keeps the images and the dialogues that its
/// judgement recorded (#7433). A session reopened over a store crosses the
/// taken `upgrade` again, and the bridge reads its classifier, its images
/// and its dialogues at the flow's node. The take seats them at the places
/// that an edit shifts. The kept flow reads back from bytes as written.
#[test]
fn a_taken_forward_flow_keeps_its_images_7433()
{
    assert_eq!(
        taken_past_an_insertion(SourceText::from(FORWARD)),
        ItemCount::from(2_usize),
        "`toNew` and `upgrade` are taken; the appended definition is decided"
    );
    assert_eq!(
        taken_past_a_reopening(SourceText::from(FORWARD)),
        (ItemCount::from(2_usize), ItemCount::from(2_usize)),
        "the checkpoints are restored and taken; the definition put first is decided"
    );
    let mut kept = session();
    let _kept = submit(&mut kept, SourceText::from(FORWARD));
    let Maybe::Present(resume) = kept.last()
    else {
        panic!("the submission resumes");
    };
    let checkpoints = resume.checkpoints();
    assert!(
        checkpoints
            .items()
            .iter()
            .any(|checkpoint| matches!(checkpoint.tables(), Maybe::Present(_))),
        "a checkpoint keeps the forward flow of `upgrade`"
    );
    let bytes = encode_checkpoints(checkpoints).expect("the checkpoints encode");
    assert_eq!(
        decode_checkpoints(&bytes).expect("the checkpoints decode"),
        *checkpoints,
        "the kept flow reads back as written"
    );
}

/// A declaration whose judgement adds an entry to a table that a checkpoint
/// does not keep yet is judged again (#7399, #7428). The judgement of
/// `raised` records a lift, so its checkpoint keeps no entries, and the take
/// declines it. A take without the decline takes it.
#[test]
fn a_lifted_type_is_judged_again_7428()
{
    assert_eq!(
        taken_past_an_insertion(SourceText::from(LIFT)),
        ItemCount::from(0_usize),
        "`raised` and the appended definition are decided"
    );
}

/// A session reopened over a store holds no record of the kernel's last
/// readmission, so the kernel crosses each taken declaration again (#7399).
/// The law of the reopened fixture relates its endpoints only by the dialogue
/// that its judgement recorded, and its constants shift by one when an edit
/// puts a definition first. The take seats the kept dialogue at the shifted
/// constants, and the kernel re-derives the law. Without the seat, the kernel
/// refuses the law, a reflexivity between differing endpoints.
#[test]
fn a_reopened_take_replays_a_kept_dialogue_7399()
{
    assert_eq!(
        taken_past_a_reopening(SourceText::from(REOPENED)),
        (ItemCount::from(3_usize), ItemCount::from(3_usize)),
        "`k`, `j` and the law are restored and taken; the definition put first is decided"
    );
}

/// A supported judgement logs the entries that each declaration adds to the
/// tables (#7373, #7399, #7428). `tallyHandled` adds a handler and its rows
/// records, and it touches no other table. `tallied` stands at a row that
/// names an instance, which the rows do not record. `unreadCall` adds a
/// reflexivity, `deliver` adds payload types, and `upgrade` adds a forward
/// flow. `raised` adds a lift, a table that a checkpoint does not keep yet.
#[test]
fn a_supported_judgement_logs_the_entries_each_declaration_adds_7373()
{
    for (text, expected) in [
        (HANDLER, (1_usize, 0_usize)),
        (REFLEXIVITY, (1, 0)),
        (PAYLOAD, (1, 0)),
        (FORWARD, (1, 0)),
        (LIFT, (0, 1)),
    ] {
        let grammar = built_in().expect("the built-in grammar builds");
        let lowering = lower_source(
            &grammar,
            SourceText::from(text),
            &mut LoweringCount::default(),
        )
        .expect("the fixture lowers");
        let Lowered::Module { module, arena } = lowering.into_lowered()
        else {
            panic!("the fixture lowers to a module");
        };
        let program = item_program(&module, arena).expect("the fixture's items are ordered");
        let mut arena = program.arena().clone();
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        let (mut kept, mut unkept) = (0_usize, 0_usize);
        for declaration in program.declarations() {
            let supported = check_declaration_supported(&mut context, &declaration);
            let Maybe::Present(tabled) = supported.tabled()
            else {
                panic!("a supported judgement logs its entries");
            };
            if tabled.others() == OtherTables::Written {
                unkept = unkept.saturating_add(1);
            }
            else if tabled.rows().records().next().is_some()
                || !tabled.handled().is_empty()
                || !tabled.reflexivities().is_empty()
                || !tabled.payloads().is_empty()
                || !tabled.directed().is_empty()
            {
                kept = kept.saturating_add(1);
            }
        }
        assert_eq!(
            (kept, unkept),
            expected,
            "the declarations that keep their entries, and those that touch another table"
        );
    }
}
