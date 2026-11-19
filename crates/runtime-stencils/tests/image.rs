//! A command's image over the corpus: each `runs` item reads back from its
//! bytes, checks, and runs as its first command runs. The test names each
//! head that does not cross. It compares the annotation kinds of the first
//! command and the read command. Five named items witness the kinds.

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
use gandr_core_sequent::ProducerNode;
use gandr_core_sequent::Provenance;
use gandr_core_sequent::focus_computation;
use gandr_core_sequent::reach;
use gandr_core_term::CoreArena;
use gandr_runtime_emitter::image::ImageRefusal;
use gandr_runtime_emitter::image::Uncodable;
use gandr_runtime_emitter::image::encode;
use gandr_runtime_emitter::image::read;
use gandr_storage_values::FlatBytes;
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
                    name: format!(
                        "{} {}",
                        path.strip_prefix(&corpus)
                            .expect("a corpus source is below its root")
                            .display(),
                        declaration.name()
                    ),
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

/// A kind of node that names an annotation.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Kind
{
    /// A code.
    Code,
    /// A fold over a list.
    Fold,
    /// An operation request.
    Perform,
    /// A handler.
    Handle,
    /// A session action.
    Session,
}

/// The kinds of annotation that `root` reaches, through each definition
/// that it unfolds.
///
/// # Specification
/// trivial.
fn annotated(
    arena: &CommandArena,
    definitions: &Definitions,
    root: CommandId,
) -> BTreeSet<Kind>
{
    let mut seen = BTreeSet::new();
    let mut order = Vec::new();
    let mut roots = vec![NodeAddress::Command(root)];
    let mut met = BTreeSet::new();
    let mut kinds = BTreeSet::new();
    while !roots.is_empty() {
        let from = order.len();
        reach(arena, &roots, &mut seen, &mut order).expect("the item's nodes resolve");
        roots.clear();
        for &node in &order[from ..] {
            match node {
                NodeAddress::Producer(id) => match arena.producer(id) {
                    Some(&ProducerNode::Constant(constant)) if met.insert(constant) => {
                        if let Some(Definition::Transparent(body)) = definitions.get(constant) {
                            roots.push(NodeAddress::Producer(body));
                        }
                    },
                    Some(&ProducerNode::Code(_)) => {
                        kinds.insert(Kind::Code);
                    },
                    _ => {},
                },
                NodeAddress::Consumer(id) => {
                    if let Some(&ConsumerNode::ListFold { .. }) = arena.consumer(id) {
                        kinds.insert(Kind::Fold);
                    }
                },
                NodeAddress::Command(id) => match arena.command(id) {
                    Some(&CommandNode::Perform { .. }) => {
                        kinds.insert(Kind::Perform);
                    },
                    Some(&CommandNode::Handle { .. }) => {
                        kinds.insert(Kind::Handle);
                    },
                    Some(&CommandNode::Session { .. }) => {
                        kinds.insert(Kind::Session);
                    },
                    _ => {},
                },
            }
        }
    }
    kinds
}

/// Each `runs` item writes its image, reads it back into a fresh arena that
/// checks, and answers on both tiers what its first command answers. Its
/// image read back writes the same bytes. An item whose head does not cross
/// is refused by name. The read command reaches the same annotation kinds as
/// the first command. Five named items witness the kinds.
#[test]
fn each_runs_item_reads_back_and_runs_alike()
{
    let expected_heads = BTreeSet::from([
        String::from("corpus/model/sessions/run-transport.gandr decodedRun"),
        String::from("corpus/model/sessions/seat-evolution.gandr moved"),
        String::from("corpus/model/sessions/seat-prefix-evolution.gandr upgraded"),
        String::from("corpus/model/sessions/seat-prefix.gandr shown"),
    ]);
    let expected_witnesses = BTreeMap::from([
        (
            String::from("corpus/classifier/implicit-telescope.gandr sameRun"),
            BTreeSet::from([Kind::Code]),
        ),
        (
            String::from("corpus/model/cancellation/abandoned.gandr cancelled"),
            BTreeSet::from([Kind::Perform, Kind::Handle, Kind::Session]),
        ),
        (
            String::from("corpus/model/cancellation/answered.gandr answered"),
            BTreeSet::from([Kind::Perform, Kind::Handle]),
        ),
        (
            String::from("corpus/model/cancellation/resumed.gandr resumed"),
            BTreeSet::from([Kind::Perform, Kind::Handle, Kind::Session]),
        ),
        (
            String::from("corpus/model/identity/flow-data.gandr two"),
            BTreeSet::from([Kind::Fold]),
        ),
    ]);
    let mut heads = BTreeSet::new();
    let mut found_witnesses = BTreeMap::new();
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
                let written_kinds = annotated(&item.arena, &item.definitions, item.root);
                let read_kinds = annotated(&back.arena, &back.definitions, back.root);
                assert_eq!(
                    written_kinds, read_kinds,
                    "{}: the read command reaches the first command's kinds",
                    item.name
                );
                if expected_witnesses.contains_key(&item.name) {
                    found_witnesses.insert(item.name, written_kinds);
                }
            },
            Err(ImageRefusal::Uncodable {
                form: Uncodable::Head(_),
                ..
            }) => {
                heads.insert(item.name);
            },
            Err(refusal) => panic!("{}: the image is refused: {refusal}", item.name),
        }
    }
    assert_eq!(heads, expected_heads, "the set of refused heads is stable");
    assert_eq!(
        found_witnesses, expected_witnesses,
        "the named items reach their stated kinds"
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
        first.iter().any(|entry| entry.1.is_ok()),
        "some item writes its image"
    );
    assert_eq!(first, images());
}
