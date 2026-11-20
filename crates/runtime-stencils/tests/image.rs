//! A command's image over the corpus: each `runs` item reads back from its
//! bytes, checks, and runs as its first command runs. The test names each
//! head that does not cross. It compares the annotation kinds of the first
//! command and the read command. Five named items witness the kinds. The
//! sweep reads its sample and the named sources on a pull request, and the
//! corpus whole under the `sweeps` and nightly profiles.

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

/// The checkout's root, as the walk reaches it: the parent of [`ROOTS`].
///
/// # Specification
/// trivial.
fn repository() -> PathBuf
{
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .expect("the checkout's root resolves")
}

/// Each `runs` item of the sources at `paths`, outside the pathological
/// twins, focused once, in the order the walk meets them.
///
/// # Specification
/// trivial.
fn items(paths: Vec<PathBuf>) -> Vec<Item>
{
    let corpus = repository();
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

/// The image sweeps: each `runs` item of the corpus sources a sweep visits
/// writes its image and reads it back.
mod sweeps
{
    use gandr_workflow_sweep::Coverage;
    use gandr_workflow_sweep::Portion;
    use gandr_workflow_sweep::Sample;
    use gandr_workflow_sweep::SampleName;
    use gandr_workflow_sweep::SampleSize;
    use gandr_workflow_sweep::Sweep;

    use super::*;

    /// The sample: sixteen sources, ranked by their BLAKE3 digest under this
    /// name, at least one of each corpus class, and, in the companion, every
    /// source the change adds or modifies beside them
    /// (`gandr-workflow-sweep`). The fixed portion walks the sources of
    /// [`NAMED`] beside the sample. The `sweeps` and nightly profiles walk
    /// [`ROOTS`] whole.
    const IMAGES: Sample = Sample {
        name: SampleName("each_runs_item_reads_back_and_runs_alike"),
        size: SampleSize(16),
    };

    /// The sources whose items the image sweep names: four whose heads do
    /// not cross, and five whose items witness the annotation kinds.
    const NAMED: [&str; 9] = [
        "corpus/model/sessions/run-transport.gandr",
        "corpus/model/sessions/seat-evolution.gandr",
        "corpus/model/sessions/seat-prefix-evolution.gandr",
        "corpus/model/sessions/seat-prefix.gandr",
        "corpus/classifier/implicit-telescope.gandr",
        "corpus/model/cancellation/abandoned.gandr",
        "corpus/model/cancellation/answered.gandr",
        "corpus/model/cancellation/resumed.gandr",
        "corpus/model/identity/flow-data.gandr",
    ];

    /// The paths that `sweep` walks: [`ROOTS`] whole in a full run, nothing
    /// for the change's portion of a full run, the sample's sources under
    /// [`ROOTS`] and the sources of [`NAMED`] for the fixed portion of a
    /// sampled run, and the change's sources under [`ROOTS`] for its
    /// portion.
    ///
    /// # Specification
    /// trivial.
    fn walked(sweep: &Sweep) -> Vec<PathBuf>
    {
        let corpus = repository();
        let roots: Vec<PathBuf> = ROOTS.iter().map(|root| corpus.join(root)).collect();
        match (sweep.coverage(), sweep.portion()) {
            (Coverage::Full, Portion::Fixed) => roots,
            (Coverage::Full, Portion::Changed) => Vec::new(),
            (Coverage::Sampled, portion) => {
                let mut paths: BTreeSet<PathBuf> = sweep
                    .visit(
                        IMAGES,
                        &gandr_workflow_sweep::corpus::sources().expect("the corpus reads"),
                    )
                    .into_iter()
                    .filter(|source| roots.iter().any(|root| source.path.starts_with(root)))
                    .map(|source| source.path)
                    .collect();
                if portion == Portion::Fixed {
                    paths.extend(NAMED.iter().map(|named| corpus.join(named)));
                }
                paths.into_iter().collect()
            },
        }
    }

    /// Whether the item named `name` stands in a source that `sweep` walks
    /// whenever it walks any: every item under the fixed portion, which
    /// walks [`NAMED`], and an item of a walked source under the change's.
    ///
    /// # Specification
    /// trivial.
    fn walks(
        sweep: &Sweep,
        walked: &[PathBuf],
        name: &str,
    ) -> bool
    {
        let corpus = repository();
        sweep.portion() == Portion::Fixed
            || name
                .split_once(' ')
                .is_some_and(|(source, _)| walked.iter().any(|path| *path == corpus.join(source)))
    }

    /// Each `runs` item that `sweep` walks writes its image, reads it back
    /// into a fresh arena that checks, and answers on both tiers what its
    /// first command answers. Its image read back writes the same bytes. An
    /// item whose head does not cross is refused by name. The read command
    /// reaches the same annotation kinds as the first command. Five named
    /// items witness the kinds.
    ///
    /// # Specification
    /// trivial.
    fn reads_back(sweep: &Sweep)
    {
        let paths = walked(sweep);
        if paths.is_empty() {
            return;
        }
        let expected_heads: BTreeSet<String> = [
            "corpus/model/sessions/run-transport.gandr decodedRun",
            "corpus/model/sessions/seat-evolution.gandr moved",
            "corpus/model/sessions/seat-prefix-evolution.gandr upgraded",
            "corpus/model/sessions/seat-prefix.gandr shown",
        ]
        .into_iter()
        .filter(|name| walks(sweep, &paths, name))
        .map(String::from)
        .collect();
        let expected_witnesses: BTreeMap<String, BTreeSet<Kind>> = [
            (
                "corpus/classifier/implicit-telescope.gandr sameRun",
                BTreeSet::from([Kind::Code]),
            ),
            (
                "corpus/model/cancellation/abandoned.gandr cancelled",
                BTreeSet::from([Kind::Perform, Kind::Handle, Kind::Session]),
            ),
            (
                "corpus/model/cancellation/answered.gandr answered",
                BTreeSet::from([Kind::Perform, Kind::Handle]),
            ),
            (
                "corpus/model/cancellation/resumed.gandr resumed",
                BTreeSet::from([Kind::Perform, Kind::Handle, Kind::Session]),
            ),
            (
                "corpus/model/identity/flow-data.gandr two",
                BTreeSet::from([Kind::Fold]),
            ),
        ]
        .into_iter()
        .filter(|&(name, _)| walks(sweep, &paths, name))
        .map(|(name, kinds)| (String::from(name), kinds))
        .collect();
        let mut heads = BTreeSet::new();
        let mut found_witnesses = BTreeMap::new();
        for item in items(paths) {
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

    #[test]
    fn each_runs_item_reads_back_and_runs_alike()
    {
        reads_back(&Sweep::asked().expect("the run's sweep resolves"));
    }

    /// The change's sources beside the fixed set (#4654).
    #[test]
    fn each_runs_item_reads_back_and_runs_alike_changed()
    {
        reads_back(&Sweep::asked().expect("the run's sweep resolves").changed());
    }

    /// Two focus runs of the sources `sweep` walks give each `runs` item the
    /// same bytes. The fixed portion's sources write some image.
    ///
    /// # Specification
    /// trivial.
    fn focuses_alike(sweep: &Sweep)
    {
        let paths = walked(sweep);
        if paths.is_empty() {
            return;
        }
        let images = || -> Vec<(String, Result<FlatBytes, ImageRefusal>)> {
            items(paths.clone())
                .into_iter()
                .map(|item| {
                    let bytes = encode(&item.arena, &item.definitions, item.root);
                    (item.name, bytes)
                })
                .collect()
        };
        let first = images();
        assert!(
            sweep.portion() == Portion::Changed || first.iter().any(|entry| entry.1.is_ok()),
            "some item writes its image"
        );
        assert_eq!(first, images());
    }

    #[test]
    fn two_focus_runs_give_equal_bytes()
    {
        focuses_alike(&Sweep::asked().expect("the run's sweep resolves"));
    }

    /// The change's sources beside the fixed set (#4654).
    #[test]
    fn two_focus_runs_give_equal_bytes_changed()
    {
        focuses_alike(&Sweep::asked().expect("the run's sweep resolves").changed());
    }
}
