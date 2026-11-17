//! A command's image over the corpus: each `runs` item that names no core
//! annotation reads back from its bytes, checks, and runs as its first
//! command runs; each other item is refused by the kind of annotation that
//! it reaches; and bytes with a fault are refused by name.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use core::convert::Infallible;
use core::ops::ControlFlow;
use std::path::Path;
use std::path::PathBuf;

use gandr_core_sequent::CommandArena;
use gandr_core_sequent::CommandId;
use gandr_core_sequent::CommandNode;
use gandr_core_sequent::ConsumerNode;
use gandr_core_sequent::Definition;
use gandr_core_sequent::Definitions;
use gandr_core_sequent::NodeAddress;
use gandr_core_sequent::ProducerId;
use gandr_core_sequent::ProducerNode;
use gandr_core_sequent::Provenance;
use gandr_core_sequent::focus_computation;
use gandr_core_sequent::reach;
use gandr_core_term::CoreArena;
use gandr_runtime_emitter::image::Annotated;
use gandr_runtime_emitter::image::ImageRefusal;
use gandr_runtime_emitter::image::Uncodable;
use gandr_runtime_emitter::image::encode;
use gandr_runtime_emitter::image::read;
use gandr_storage_values::CanonicalValue;
use gandr_storage_values::CanonicalWord;
use gandr_storage_values::ConstructorTag;
use gandr_storage_values::DecodeWork;
use gandr_storage_values::FlatBytes;
use gandr_storage_values::TokenBody;
use gandr_storage_values::TokenOffset;
use gandr_storage_values::TokenReader;
use gandr_storage_values::TokenSink;
use gandr_storage_values::ValueError;
use gandr_storage_values::encode_flat;
use gandr_surface_corpus::Stated;
use gandr_surface_dispatcher::Composed;
use gandr_surface_dispatcher::Pool;
use gandr_surface_dispatcher::Step;
use gandr_surface_dispatcher::Walk;
use gandr_surface_dispatcher::Width;
use gandr_surface_evaluate::Evaluator;

use crate::agreement::ROOTS;
use crate::support::Label;
use crate::support::agree;
use crate::support::focus;
use crate::support::named;

/// One `runs` item of the corpus, focused: its arena, its definitions and
/// its root, or nothing when its root does not focus.
struct Item
{
    /// The source and the declaration, for a failure's message.
    name: String,
    /// The program's arena with the item's root focused into it.
    arena: CommandArena,
    /// The program's definitions.
    definitions: Definitions,
    /// The root `⟨return c | ★⟩`.
    root: CommandId,
}

/// Each `runs` item under the corpus roots, outside the pathological twins,
/// focused once, in the order the walk meets them.
///
/// # Specification
/// trivial.
fn items() -> Vec<Item>
{
    let corpus = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let paths: Vec<PathBuf> = ROOTS.iter().map(|root| corpus.join(root)).collect();
    let mut found = Vec::new();
    let ControlFlow::Continue(_report) = Walk::new(paths).visit::<Evaluator, _, _>(
        &Pool::new(Width::SERIAL),
        |step| -> ControlFlow<Infallible> {
            let Step::Source {
                path,
                composed:
                    Composed::Settled {
                        report,
                        mut program,
                        ..
                    },
                ..
            } = step
            else {
                return ControlFlow::Continue(());
            };
            if path
                .components()
                .any(|component| component.as_os_str() == "pathological")
            {
                return ControlFlow::Continue(());
            }
            let parts = program.parts();
            for declaration in report.declarations() {
                let Stated::Verdict(gandr_surface_corpus::Outcome::Runs(_)) = *declaration.stated()
                else {
                    continue;
                };
                let mut arena = parts.arena.clone();
                let mut core = CoreArena::new();
                let value = core.value_constant(declaration.constant());
                let returned = core.computation_return(value);
                let root = focus_computation(
                    &core,
                    returned,
                    &mut arena,
                    &mut Provenance::new(),
                    &gandr_core_sequent::Writers::NONE,
                )
                .expect("a runs item's return focuses");
                found.push(Item {
                    name: format!("{} {}", path.display(), declaration.name()),
                    arena,
                    definitions: parts.definitions.clone(),
                    root,
                });
            }
            ControlFlow::Continue(())
        },
    );
    found
}

/// The kinds of annotation that `root` reaches, through each definition
/// that it unfolds.
///
/// # Specification
/// trivial.
fn annotated(item: &Item) -> BTreeSet<Annotated>
{
    let mut seen = BTreeSet::new();
    let mut order = Vec::new();
    let mut roots = vec![NodeAddress::Command(item.root)];
    let mut met = BTreeSet::new();
    let mut kinds = BTreeSet::new();
    while !roots.is_empty() {
        let from = order.len();
        reach(&item.arena, &roots, &mut seen, &mut order).expect("the item's nodes resolve");
        roots.clear();
        for &node in &order[from ..] {
            match node {
                NodeAddress::Producer(id) => match item.arena.producer(id) {
                    Some(&ProducerNode::Constant(constant)) if met.insert(constant) => {
                        if let Some(Definition::Transparent(body)) = item.definitions.get(constant)
                        {
                            roots.push(NodeAddress::Producer(body));
                        }
                    },
                    Some(&ProducerNode::Code(_)) => {
                        kinds.insert(Annotated::Code);
                    },
                    _ => {},
                },
                NodeAddress::Consumer(id) => {
                    if let Some(&ConsumerNode::ListFold { .. }) = item.arena.consumer(id) {
                        kinds.insert(Annotated::Fold);
                    }
                },
                NodeAddress::Command(id) => match item.arena.command(id) {
                    Some(&CommandNode::Perform { .. }) => {
                        kinds.insert(Annotated::Perform);
                    },
                    Some(&CommandNode::Handle { .. }) => {
                        kinds.insert(Annotated::Handle);
                    },
                    Some(&CommandNode::Session { .. }) => {
                        kinds.insert(Annotated::Session);
                    },
                    _ => {},
                },
            }
        }
    }
    kinds
}

/// Each `runs` item that reaches no annotation writes its image, reads it
/// back into a fresh arena that checks, and answers on both tiers what its
/// first command answers. Its image read back writes the same bytes. Each
/// other item is refused by name, and the counts of each kind are stated, so
/// a change in the corpus or in the codec shows here.
#[test]
fn each_runs_item_reads_back_and_runs_alike()
{
    let mut written = 0_usize;
    let mut refused: BTreeMap<Annotated, usize> = BTreeMap::new();
    for item in items() {
        match encode(&item.arena, &item.definitions, item.root) {
            Ok(bytes) => {
                let back = read(bytes.as_body()).unwrap_or_else(|refusal| {
                    panic!("{}: the bytes read back: {refusal}", item.name)
                });
                assert_eq!(
                    agree(Label(&item.name), &item.arena, &item.definitions, item.root),
                    agree(Label(&item.name), &back.arena, &back.definitions, back.root),
                    "{}: the read command answers as the first",
                    item.name
                );
                assert_eq!(
                    encode(&back.arena, &back.definitions, back.root).as_ref(),
                    Ok(&bytes),
                    "{}: the read command writes the same bytes",
                    item.name
                );
                written = written.saturating_add(1);
            },
            Err(ImageRefusal::Uncodable {
                form: Uncodable::Annotation(_),
                ..
            }) => {
                let kinds = annotated(&item);
                assert!(
                    !kinds.is_empty(),
                    "{}: a refused item reaches an annotation",
                    item.name
                );
                for kind in kinds {
                    let count = refused.entry(kind).or_default();
                    *count = count.saturating_add(1);
                }
            },
            Err(refusal) => panic!("{}: the image is refused: {refusal}", item.name),
        }
    }
    assert_eq!(
        (written, refused),
        (
            538,
            BTreeMap::from([
                (Annotated::Code, 184),
                (Annotated::Fold, 7),
                (Annotated::Perform, 61),
                (Annotated::Handle, 74),
                (Annotated::Session, 16),
            ])
        )
    );
}

/// Two focus runs of the corpus give each `runs` item the same bytes.
#[test]
fn two_focus_runs_give_equal_bytes()
{
    let images = || -> Vec<(String, Result<FlatBytes, ImageRefusal>)> {
        items()
            .into_iter()
            .map(|item| {
                let bytes = encode(&item.arena, &item.definitions, item.root);
                (item.name, bytes)
            })
            .collect()
    };
    let first = images();
    assert!(
        first.iter().any(|(_, bytes)| bytes.is_ok()),
        "some item writes its image"
    );
    assert_eq!(first, images());
}

/// A command with a code is refused by name, with the code's address.
#[test]
fn an_annotation_is_refused_by_name()
{
    let mut arena = CommandArena::new();
    let mut core = CoreArena::new();
    let unit = core.value_type_unit();
    let quoted = arena.annotations_mut().value_code(unit);
    let code = arena
        .mint_producer(ProducerNode::Code(quoted))
        .expect("a code mints");
    let top = arena
        .mint_consumer(ConsumerNode::Top)
        .expect("the top mints");
    let root = arena
        .mint_cut(gandr_theory_cell_complexes::Polarity::Positive, code, top)
        .expect("a cut mints");
    assert_eq!(
        encode(&arena, &Definitions::new(), root),
        Err(ImageRefusal::Uncodable {
            node: NodeAddress::Producer(code),
            form: Uncodable::Annotation(Annotated::Code),
        })
    );
}

/// One record of a hand-written image.
#[derive(Clone, Copy, Debug)]
enum Record
{
    /// A constructor opens.
    Open(u8),
    /// A word.
    Word(u64),
    /// The innermost constructor closes.
    Close,
}

/// A value that writes `records` as they stand.
struct Script(&'static [Record]);

impl CanonicalValue for Script
{
    /// Write each record.
    ///
    /// # Specification
    /// trivial.
    fn emit_tokens<Sink>(
        &self,
        sink: &mut Sink,
    ) -> Result<(), ValueError>
    where
        Sink: TokenSink + ?Sized,
    {
        self.0.iter().try_for_each(|&record| match record {
            Record::Open(tag) => sink.open(ConstructorTag::from(tag)),
            Record::Word(word) => sink.word(CanonicalWord::from(word)),
            Record::Close => sink.close(),
        })
    }

    /// A script is written, never read.
    ///
    /// # Specification
    /// trivial.
    fn decode_tokens<Store>(_reader: &mut TokenReader<'_, Store>) -> Result<Self, ValueError>
    where
        Store: gandr_storage_values::ChunkStore,
    {
        Err(ValueError::TruncatedStream {
            position: TokenOffset::ZERO,
        })
    }
}

/// The read of `records`.
///
/// # Specification
/// trivial.
fn read_script(records: &'static [Record]) -> Result<CommandId, ImageRefusal>
{
    let bytes = encode_flat(&Script(records)).expect("a script writes");
    read(bytes.as_body()).map(|back| back.root)
}

/// The image's open and counts: one producer, one consumer, one command, no
/// definition, the root at command zero.
const HEAD: [Record; 6] = [
    Record::Open(0x01),
    Record::Word(1),
    Record::Word(1),
    Record::Word(1),
    Record::Word(0),
    Record::Word(0),
];

/// A tag that no node has, a child that stands after its parent, a count
/// past the ceiling and bytes after the image are each refused by name.
#[test]
fn each_fault_of_the_bytes_is_refused_by_name()
{
    static UNKNOWN: [Record; 8] = [
        HEAD[0],
        HEAD[1],
        HEAD[2],
        HEAD[3],
        HEAD[4],
        HEAD[5],
        Record::Open(0x7f),
        Record::Close,
    ];
    assert_eq!(
        read_script(&UNKNOWN),
        Err(ImageRefusal::Plane(ValueError::UnexpectedConstructor {
            found: ConstructorTag::from(0x7f),
            position: TokenOffset::from(6_u32),
        })),
        "a tag that no node has"
    );
    // The cut stands before the unit and the top that it names.
    static FORWARD: [Record; 18] = [
        HEAD[0],
        HEAD[1],
        HEAD[2],
        HEAD[3],
        HEAD[4],
        HEAD[5],
        Record::Open(0x64),
        Record::Word(0),
        Record::Word(0),
        Record::Word(0),
        Record::Close,
        Record::Open(0x26),
        Record::Open(0x10),
        Record::Word(0),
        Record::Close,
        Record::Word(0),
        Record::Word(0),
        Record::Close,
    ];
    static ORDERED: [Record; 21] = [
        HEAD[0],
        HEAD[1],
        HEAD[2],
        HEAD[3],
        HEAD[4],
        HEAD[5],
        Record::Open(0x26),
        Record::Open(0x10),
        Record::Word(0),
        Record::Close,
        Record::Word(0),
        Record::Word(0),
        Record::Close,
        Record::Open(0x47),
        Record::Close,
        Record::Open(0x64),
        Record::Word(0),
        Record::Word(0),
        Record::Word(0),
        Record::Close,
        Record::Close,
    ];
    assert_eq!(
        read_script(&ORDERED),
        Ok(CommandId::from(0_u32)),
        "the unit sent to the top"
    );
    assert_eq!(
        read_script(&FORWARD[.. 18])
            .err()
            .map(|refusal| refusal.to_string()),
        read_script(&FORWARD)
            .err()
            .map(|refusal| refusal.to_string()),
    );
    let forward: Vec<Record> = FORWARD
        .iter()
        .copied()
        .chain([Record::Open(0x47), Record::Close, Record::Close])
        .collect();
    let forward: &'static [Record] = Vec::leak(forward);
    assert_eq!(
        read_script(forward),
        Err(ImageRefusal::Mint(
            gandr_core_sequent::MintRefusal::DanglingProducer(ProducerId::from(0_u32))
        )),
        "a child after its parent"
    );
    static PAST: [Record; 7] = [
        Record::Open(0x01),
        Record::Word((1 << 24) + 1),
        Record::Word(0),
        Record::Word(0),
        Record::Word(0),
        Record::Word(0),
        Record::Close,
    ];
    assert_eq!(
        read_script(&PAST),
        Err(ImageRefusal::Plane(ValueError::DecodeBudgetExceeded {
            spent: DecodeWork::from((1_u64 << 24) + 1),
            ceiling: DecodeWork::from(1_u64 << 24),
        })),
        "a count past the ceiling"
    );
    let (commands, root) = focus(&named().swap_remove(0).program);
    let image = encode(&commands, &Definitions::new(), root).expect("a named program writes");
    let tail = encode_flat(&Script(&[Record::Open(0x47), Record::Close])).expect("a script writes");
    let mut trailing = image.as_body().as_ref().to_vec();
    trailing.extend_from_slice(tail.as_body().as_ref());
    let records = read(TokenBody::from(trailing.as_slice()));
    assert!(
        matches!(
            records,
            Err(ImageRefusal::Plane(ValueError::TrailingTokens { .. }))
        ),
        "bytes after the image: {records:?}"
    );
}
