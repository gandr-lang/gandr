//! A command's image over the corpus: each `runs` item that names no core
//! annotation reads back from its bytes, checks, and runs as its first
//! command runs. Each other item is refused by the kind of annotation or
//! head that it reaches, and the counts of each kind are stated.

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
use gandr_runtime_emitter::image::Annotated;
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
    let mut heads = 0_usize;
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
            Err(ImageRefusal::Uncodable {
                form: Uncodable::Head(_),
                ..
            }) => {
                heads = heads.saturating_add(1);
            },
            Err(refusal) => panic!("{}: the image is refused: {refusal}", item.name),
        }
    }
    assert_eq!(
        (written, heads, refused),
        (
            514,
            4,
            BTreeMap::from([
                (Annotated::Code, 183),
                (Annotated::Fold, 7),
                (Annotated::Perform, 60),
                (Annotated::Handle, 73),
                (Annotated::Session, 15),
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
        first.iter().any(|entry| entry.1.is_ok()),
        "some item writes its image"
    );
    assert_eq!(first, images());
}
