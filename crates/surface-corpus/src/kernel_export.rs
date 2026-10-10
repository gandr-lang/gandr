//! The kernel export over the whole corpus: every source of both roots
//! exported, committed as artifact records and read back through the kernel's
//! decoder, and every declaration classified by what became of it at the
//! kernel boundary.
//!
//! The sweep lists `strict/` and `fixture/` itself — `.gandr` files, links not
//! followed, as the dispatcher's walk lists them — and runs the composition a
//! driver runs: parse, lower, check, readmit, export. Nothing here pins a
//! count: each root is asserted to export a declaration, so a source added to
//! either moves a count and reddens nothing.

use alloc::vec;
use alloc::vec::Vec;
use std::fs;
use std::path::Path;
use std::path::PathBuf;

use anodized::spec;
use gandr_core_checker::CheckBudget;
use gandr_core_checker::CheckingContext;
use gandr_core_checker::Verdict;
use gandr_core_checker::bridge;
use gandr_core_checker::check_module;
use gandr_core_term::CoreArena;
use gandr_core_term::FailureClass;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::EncodedArtifact;
use gandr_kernel_term::StructuredName;
use gandr_storage_artifact::ArtifactManifest;
use gandr_storage_artifact::ArtifactRecordSet;
use gandr_storage_artifact::build;
use gandr_storage_records::InMemoryBlockStore;
use gandr_storage_records::TreeParams;
use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::built_in;
use gandr_surface_lowering::DeclarationOutcome;
use gandr_surface_lowering::LoweringBudget;
use gandr_surface_lowering::lower_module;
use gandr_surface_lowering::namespace::Recognition;
use gandr_surface_parser::parse;
use gandr_surface_syntax::SourceText;

use crate::fixture::declarations;
use crate::refusal::Refusal;
use crate::refusal::RefusalName;

/// The corpus root a source was listed under.
///
/// # Specification
/// - requires: the fixture producer preserves the source and boundary
///   correspondence represented.
/// - ensures: Identifies the strict or fixture tree from which the sweep
///   obtained a source.
/// - panics: none.
/// - executable: none — The enum has no path or filesystem observation;
///   `sources` and `corpus` supply those relationships.
///
/// # Adequacy
/// - hypothesis: L3 — the current strict and fixture sources are observed
///   through boundary classification and record-backed artifact reconstruction.
///   Exact admitted names and withheld dependencies distinguish changed
///   inclusion and lost provenance; repeated exports show determinism rather
///   than an independent oracle.
/// - witness: `kernel_export::kernel_export_gate::the_kernel_export_exit_gate_holds`
/// - witness: `kernel_export::kernel_corpus_partition::corpus_partition_matches_the_manifest`
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Root
{
    /// `strict/`.
    Strict,
    /// `fixture/`, the pending set among it.
    Fixture,
}

/// What became of one declaration at the kernel boundary.
///
/// # Specification
/// - requires: the fixture producer preserves the source and boundary
///   correspondence represented.
/// - ensures: Distinguishes definitions and assumptions that enter the artifact
///   from marked, withheld, static and never-offered declarations.
/// - panics: none.
/// - executable: none — The enum holds no checker/readmission pair or artifact;
///   `class_of`, `export` and the partition witness establish its
///   interpretation.
///
/// # Adequacy
/// - hypothesis: L3 — the current strict and fixture sources are observed
///   through boundary classification and record-backed artifact reconstruction.
///   Exact admitted names and withheld dependencies distinguish changed
///   inclusion and lost provenance; repeated exports show determinism rather
///   than an independent oracle.
/// - witness: `kernel_export::kernel_export_gate::the_kernel_export_exit_gate_holds`
/// - witness: `kernel_export::kernel_corpus_partition::corpus_partition_matches_the_manifest`
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Class
{
    /// The checker accepted it whole and the kernel admitted it as a
    /// definition.
    Defined,
    /// The checker owed its body and the kernel admitted its signature as an
    /// axiom.
    Assumed,
    /// The checker refused it, under this name, and it crossed as its mark
    /// alone.
    Marked(RefusalName),
    /// The checker accepted it, and it names a declaration that did not cross.
    Withheld,
    /// The checker accepted it as a type operator, which stays on the
    /// checker's side for the instances that name it.
    Static,
    /// The lowering refused it, under this name, and nothing was offered.
    NeverOffered(RefusalName),
}

/// One source the lowering read, exported.
///
/// # Specification
/// - requires: the fixture producer preserves the source and boundary
///   correspondence represented.
/// - ensures: Associates a source path and root with declaration classes,
///   withheld dependencies, admitted names and their canonical artifact.
/// - panics: none.
/// - executable: none — The record has no original source, module or judgement
///   sequence; `export` establishes its structural invariants and the partition
///   witness compares its admitted names to the artifact.
///
/// # Adequacy
/// - hypothesis: L3 — the current strict and fixture sources are observed
///   through boundary classification and record-backed artifact reconstruction.
///   Exact admitted names and withheld dependencies distinguish changed
///   inclusion and lost provenance; repeated exports show determinism rather
///   than an independent oracle.
/// - witness: `kernel_export::kernel_export_gate::the_kernel_export_exit_gate_holds`
/// - witness: `kernel_export::kernel_corpus_partition::corpus_partition_matches_the_manifest`
struct Exported
{
    /// Where the source sits.
    path: PathBuf,
    /// The root it was listed under.
    root: Root,
    /// Each declaration's position and class, in admission order.
    classes: Vec<(ConstantIndex, Class)>,
    /// Each withheld declaration's position beside the position it names.
    withheld: Vec<(ConstantIndex, ConstantIndex)>,
    /// The structured name of each declaration that crossed, in admission
    /// order.
    crossed_names: Vec<StructuredName>,
    /// The kernel artifact of what crossed.
    artifact: EncodedArtifact,
}

/// What one listed source came to.
///
/// # Specification
/// - requires: the fixture producer preserves the source and boundary
///   correspondence represented.
/// - ensures: Distinguishes a source exported after lowering from a source
///   refused as a whole before any declaration was offered.
/// - panics: none.
/// - executable: none — The enum carries no original lowering result; `export`
///   selects the case while the corpus consumers validate successful exports.
///
/// # Adequacy
/// - hypothesis: L3 — the current strict and fixture sources are observed
///   through boundary classification and record-backed artifact reconstruction.
///   Exact admitted names and withheld dependencies distinguish changed
///   inclusion and lost provenance; repeated exports show determinism rather
///   than an independent oracle.
/// - witness: `kernel_export::kernel_export_gate::the_kernel_export_exit_gate_holds`
/// - witness: `kernel_export::kernel_corpus_partition::corpus_partition_matches_the_manifest`
enum Swept
{
    /// The lowering read it, and it was exported.
    Exported(Exported),
    /// The lowering refused it as a whole, so it offered nothing.
    RefusedWhole,
}

/// Every `.gandr` source under `root`, sorted, symbolic links not followed.
///
/// # Specification
/// - requires: the committed corpus roots remain readable and unchanged during
///   the sweep.
/// - ensures: returns the `.gandr` paths under the selected root, uniquely in
///   lexical order, without following symbolic links.
/// - panics: when a corpus directory, entry or file type cannot be read.
///
/// # Adequacy
/// - hypothesis: L3 — the checked-in strict and fixture trees feed the export
///   and record-plane witnesses. The predicate observes root membership,
///   extension, uniqueness and ordering without a second filesystem walk. The
///   witnesses cover the current corpus; they do not model concurrent
///   filesystem mutation.
/// - witness: `kernel_export::kernel_export_gate::the_kernel_export_exit_gate_holds`
/// - witness: `kernel_export::kernel_corpus_partition::corpus_partition_matches_the_manifest`
#[spec(
    ensures: |ret| {
    let directory = match root {
        Root::Strict => concat!(env!("CARGO_MANIFEST_DIR"), "/strict"),
        Root::Fixture => concat!(env!("CARGO_MANIFEST_DIR"), "/fixture"),
    };
    ret
        .iter()
        .all(|path| {
            path.starts_with(directory)
                && path.extension().is_some_and(|extension| extension == "gandr")
        })
        && ret.iter().zip(ret.iter().skip(1_usize)).all(|(first, second)| first < second)
},
)]
fn sources(root: Root) -> Vec<PathBuf>
{
    let directory = match root {
        | Root::Strict => concat!(env!("CARGO_MANIFEST_DIR"), "/strict"),
        | Root::Fixture => concat!(env!("CARGO_MANIFEST_DIR"), "/fixture"),
    };
    let mut pending = vec![PathBuf::from(directory)];
    let mut found = Vec::new();
    while let Some(directory) = pending.pop() {
        let entries = fs::read_dir(&directory).unwrap_or_else(|error| {
            panic!(
                "{}: the corpus directory lists: {error}",
                directory.display()
            )
        });
        for entry in entries {
            let entry = entry.expect("a corpus entry reads");
            let kind = entry.file_type().expect("a corpus entry has a type");
            let path = entry.path();
            if kind.is_dir() {
                pending.push(path);
            }
            else if !kind.is_symlink()
                && path
                    .extension()
                    .is_some_and(|extension| extension == "gandr")
            {
                found.push(path);
            }
        }
    }
    found.sort();
    found
}

/// What became of the declaration whose verdict is `verdict` and whose
/// readmission is `outcome`, which must agree.
///
/// # Specification
/// - requires: the checker verdict and kernel readmission agree: accepted
///   definitions or static operators, owed assumptions, matching refusal marks,
///   or accepted/owed declarations withheld by a dependency.
/// - ensures: returns exactly the corresponding boundary class, retaining the
///   checker refusal’s canonical name for a mark.
/// - panics: when the fixture’s verdict and readmission disagree.
///
/// # Adequacy
/// - hypothesis: L3 — the current corpus supplies readmitted definitions,
///   assumptions, refusal marks, static declarations and withheld dependencies.
///   Exact partition-to-artifact membership distinguishes admitting excluded
///   declarations or losing admitted names; the predicate additionally states
///   pair compatibility and exact class selection.
/// - witness: `kernel_export::kernel_export_gate::the_kernel_export_exit_gate_holds`
/// - witness: `kernel_export::kernel_corpus_partition::corpus_partition_matches_the_manifest`
#[spec(
    requires: match (verdict, outcome) {
    (
        Verdict::Checked { .. } | Verdict::Synthesised { .. },
        &(bridge::Outcome::Defined { .. }
        | bridge::Outcome::Static
        | bridge::Outcome::Refused(bridge::Refusal::Withheld { .. })),
    )
    | (
        Verdict::Owed(_),
        &(bridge::Outcome::Assumed { .. }
        | bridge::Outcome::Refused(bridge::Refusal::Withheld { .. })),
    ) => true,
    (Verdict::Refused(refusal), &bridge::Outcome::Marked(mark)) => refusal == mark,
    _ => false,
},
    ensures: |ret| match (verdict, outcome, ret) {
    (_, &bridge::Outcome::Defined { .. }, Class::Defined)
    | (_, &bridge::Outcome::Static, Class::Static)
    | (_, &bridge::Outcome::Assumed { .. }, Class::Assumed)
    | (
        _,
        &bridge::Outcome::Refused(bridge::Refusal::Withheld { .. }),
        Class::Withheld,
    ) => true,
    (Verdict::Refused(refusal), &bridge::Outcome::Marked(mark), Class::Marked(name)) => {
        refusal == mark && name == Refusal::Checking(refusal).name()
    }
    _ => false,
},
)]
fn class_of(
    path: &Path,
    verdict: Verdict,
    outcome: &bridge::Outcome,
) -> Class
{
    match (verdict, outcome) {
        | (
            Verdict::Checked { .. } | Verdict::Synthesised { .. },
            &bridge::Outcome::Defined { .. },
        ) => Class::Defined,
        | (Verdict::Checked { .. } | Verdict::Synthesised { .. }, &bridge::Outcome::Static) => {
            Class::Static
        },
        | (Verdict::Owed(_), &bridge::Outcome::Assumed { .. }) => Class::Assumed,
        | (Verdict::Refused(refusal), &bridge::Outcome::Marked(mark)) if refusal == mark => {
            Class::Marked(Refusal::Checking(refusal).name())
        },
        | (
            Verdict::Checked { .. } | Verdict::Synthesised { .. } | Verdict::Owed(_),
            &bridge::Outcome::Refused(bridge::Refusal::Withheld { .. }),
        ) => Class::Withheld,
        | (verdict, outcome) => panic!(
            "{}: the verdict {verdict:?} and the kernel's outcome {outcome:?} disagree",
            path.display()
        ),
    }
}

/// The source at `path` under `root`, parsed, lowered, checked, readmitted and
/// exported.
///
/// # Specification
/// - requires: `path` is a readable UTF-8 corpus source and `pbg` is its
///   grammar; the caller supplies the root it was listed under.
/// - ensures: a whole-source lowering refusal offers nothing. Otherwise
///   preserves the root, declaration admission order, boundary classes,
///   withheld dependencies and exactly the names admitted as definitions or
///   assumptions alongside their artifact.
/// - panics: on unreadable source, parser failure, an engine fault, or
///   inconsistent checker/readmission positions.
///
/// # Adequacy
/// - hypothesis: L3 — every current corpus source that lowers is checked
///   against its decoded and record-backed artifact. Exact names, admission
///   order, record cardinality and withheld targets distinguish
///   inclusion/exclusion mistakes and lost dependencies. Repeat sweeps
///   establish determinism, not an independent semantic oracle; the predicate
///   does not reread source files.
/// - witness: `kernel_export::kernel_export_gate::the_kernel_export_exit_gate_holds`
/// - witness: `kernel_export::kernel_corpus_partition::corpus_partition_matches_the_manifest`
#[spec(
    ensures: |ret| match ret {
    Swept::RefusedWhole => true,
    Swept::Exported(ref exported) => {
        exported.root == root
            && exported
                .classes
                .iter()
                .zip(exported.classes.iter().skip(1_usize))
                .all(|(first, second)| first.0 < second.0)
            && exported.crossed_names.len()
                == exported
                    .classes
                    .iter()
                    .filter(|&&(_, class)| {
                        matches!(class, Class::Defined | Class::Assumed)
                    })
                    .count()
            && exported
                .withheld
                .iter()
                .all(|&(declaration, named)| {
                    exported
                        .classes
                        .iter()
                        .any(|&(constant, class)| {
                            constant == declaration && class == Class::Withheld
                        })
                        && !exported
                            .classes
                            .iter()
                            .any(|&(constant, class)| {
                                constant == named
                                    && matches!(class, Class::Defined | Class::Assumed)
                            })
                })
            && exported
                .classes
                .iter()
                .filter(|&&(_, class)| class == Class::Withheld)
                .count() == exported.withheld.len()
    }
},
)]
fn export(
    pbg: &Pbg,
    path: PathBuf,
    root: Root,
) -> Swept
{
    let text = fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("{}: the source reads: {error}", path.display()));
    let tree = parse(pbg, SourceText::from(text.as_str()))
        .unwrap_or_else(|fault| panic!("{}: the parser commits a tree: {fault}", path.display()))
        .into_tree();
    let mut arena = CoreArena::new();
    let module = match lower_module(
        pbg,
        &tree,
        &mut arena,
        LoweringBudget::DEFAULT,
        Recognition::default(),
    ) {
        | Ok(module) => module,
        | Err(refusal) => {
            assert_ne!(
                refusal.classify(),
                FailureClass::EngineFault,
                "{}: the lowering faulted: {refusal}",
                path.display()
            );
            return Swept::RefusedWhole;
        },
    };
    let verdicts = check_module(
        &mut CheckingContext::new(&mut arena, CheckBudget::DEFAULT),
        &declarations(&module),
    );
    let readmission = bridge::readmit(&mut arena, &verdicts);
    let names = module.structured_names();
    let mut judged = verdicts.judged().iter().zip(readmission.readmitted());
    let mut classes = Vec::new();
    let mut withheld = Vec::new();
    let mut crossed_names = Vec::new();
    for lowered in module.declarations() {
        let constant = lowered.constant();
        let class = if let DeclarationOutcome::Refused(refusal) = lowered.outcome() {
            Class::NeverOffered(Refusal::Lowering(refusal).name())
        }
        else {
            let Some((judgement, crossing)) = judged.next()
            else {
                panic!(
                    "{}: the declaration at {} was offered and has no verdict",
                    path.display(),
                    usize::from(constant)
                );
            };
            assert_eq!(
                (judgement.constant(), crossing.constant()),
                (constant, constant),
                "{}: the verdicts and the readmission keep admission order",
                path.display()
            );
            if let bridge::Outcome::Refused(bridge::Refusal::Withheld {
                constant: named, ..
            }) = *crossing.outcome()
            {
                withheld.push((constant, named));
            }
            class_of(&path, judgement.verdict(), crossing.outcome())
        };
        if matches!(class, Class::Defined | Class::Assumed) {
            crossed_names.push(names.get(&constant).cloned().unwrap_or_default());
        }
        classes.push((constant, class));
    }
    assert!(
        judged.next().is_none(),
        "{}: every verdict belongs to a declaration the lowering read",
        path.display()
    );
    let artifact = readmission.export(names);
    Swept::Exported(Exported {
        path,
        root,
        classes,
        withheld,
        crossed_names,
        artifact,
    })
}

/// Every source of both roots the lowering reads, exported, in root and then
/// path order.
///
/// # Specification
/// - requires: both committed corpus trees remain readable and unchanged during
///   the sweep.
/// - ensures: exports every source that lowers, omitting whole-source refusals,
///   in strict-root then fixture-root path order without duplicate paths.
/// - panics: on an invalid fixture or failed export precondition.
///
/// # Adequacy
/// - hypothesis: L3 — the checked-in roots are swept twice and each resulting
///   artifact is decoded and read through its records. Root/path order and
///   unique membership are executable invariants; byte identity across sweeps
///   is determinism evidence, while the partition witness compares admitted
///   names to the reconstructed artifact.
/// - witness: `kernel_export::kernel_export_gate::the_kernel_export_exit_gate_holds`
/// - witness: `kernel_export::kernel_corpus_partition::corpus_partition_matches_the_manifest`
#[spec(
    ensures: |ret| {
    ret
        .iter()
        .all(|exported| {
            exported
                .path
                .starts_with(
                    match exported.root {
                        Root::Strict => concat!(env!("CARGO_MANIFEST_DIR"), "/strict"),
                        Root::Fixture => concat!(env!("CARGO_MANIFEST_DIR"), "/fixture"),
                    },
                )
        })
        && ret
            .iter()
            .zip(ret.iter().skip(1_usize))
            .all(|(first, second)| {
                (first.root, &first.path) < (second.root, &second.path)
            })
},
)]
fn corpus() -> Vec<Exported>
{
    let pbg = built_in().expect("the built-in grammar builds");
    let mut exported = Vec::new();
    for root in [Root::Strict, Root::Fixture] {
        for path in sources(root) {
            if let Swept::Exported(source) = export(&pbg, path, root) {
                exported.push(source);
            }
        }
    }
    exported
}

/// `artifact` committed as records into a fresh block store, beside the
/// manifest naming them.
///
/// # Specification
/// - requires: `artifact` is a valid canonical kernel export whose record tree
///   fits the current profile.
/// - ensures: returns a fresh store containing the artifact’s record tree and
///   the manifest naming its root. Reading the manifest under the current
///   profile reconstructs the same artifact.
/// - panics: if the export cannot be segmented or the records cannot be
///   committed.
///
/// # Adequacy
/// - hypothesis: L3 — every current corpus export is committed, read through
///   the manifest and compared with the kernel-decoded artifact; its manifest
///   count also matches the independently observed admitted declarations. The
///   predicate verifies the returned manifest/store root association without
///   another whole-artifact reconstruction.
/// - witness: `kernel_export::kernel_export_gate::the_kernel_export_exit_gate_holds`
/// - witness: `kernel_export::kernel_corpus_partition::corpus_partition_matches_the_manifest`
#[spec(
    ensures: |ret| {
    gandr_storage_records::BlockStore::load(&ret.1, ret.0.root_node())
        .is_ok_and(|node| node.identity() == ret.0.root_node())
},
)]
fn commit(artifact: &EncodedArtifact) -> (ArtifactManifest, InMemoryBlockStore)
{
    let records = ArtifactRecordSet::from_artifact(artifact.as_image())
        .expect("an export cuts at its own segments");
    let mut store = InMemoryBlockStore::default();
    let manifest = build(&records, TreeParams::current(), &mut store).expect("the records commit");
    (manifest, store)
}

/// The export gate: every source's artifact is a function of its text, and
/// reads back through the record plane and the decoder as itself.
mod kernel_export_gate
{
    use alloc::collections::BTreeSet;

    use gandr_kernel_term::decode;
    use gandr_kernel_term::encode;
    use gandr_storage_records::TreeParams;

    use super::Class;
    use super::Root;
    use super::commit;
    use super::corpus;

    #[test]
    fn the_kernel_export_exit_gate_holds()
    {
        let first = corpus();
        let second = corpus();
        assert_eq!(
            first.len(),
            second.len(),
            "two sweeps read the same sources"
        );
        let mut exporting = BTreeSet::new();
        for (one, two) in first.iter().zip(&second) {
            let path = one.path.display();
            assert_eq!(
                one.artifact, two.artifact,
                "{path}: the export is a function of the source"
            );
            let (manifest, store) = commit(&one.artifact);
            let (again, _again_store) = commit(&two.artifact);
            assert_eq!(
                manifest.identity(),
                again.identity(),
                "{path}: the identity is a function of the source"
            );
            let decoded = decode(one.artifact.as_image())
                .unwrap_or_else(|refusal| panic!("{path}: the export decodes: {refusal}"));
            assert_eq!(
                one.artifact,
                encode(decoded.arena(), decoded.declarations()),
                "{path}: the decoding re-encodes byte for byte"
            );
            assert_eq!(
                Ok(decoded),
                manifest.read_under(&store, TreeParams::current()),
                "{path}: the records read back through the decoder as the export"
            );
            if one
                .classes
                .iter()
                .any(|&(_, class)| matches!(class, Class::Defined | Class::Assumed))
            {
                exporting.insert(one.root);
            }
        }
        assert_eq!(
            BTreeSet::from([Root::Strict, Root::Fixture]),
            exporting,
            "each root exports a declaration"
        );
    }
}

/// The partition: every declaration of the corpus classified once by what
/// became of it at the kernel boundary, against the artifact that holds what
/// crossed.
mod kernel_corpus_partition
{
    use alloc::collections::BTreeMap;
    use alloc::vec::Vec;

    use gandr_kernel_term::StructuredName;
    use gandr_storage_records::RecordCount;
    use gandr_storage_records::TreeParams;

    use super::Class;
    use super::commit;
    use super::corpus;

    #[test]
    fn corpus_partition_matches_the_manifest()
    {
        for exported in corpus() {
            let path = exported.path.display();
            let classes: BTreeMap<_, _> = exported.classes.iter().copied().collect();
            for &(declaration, named) in &exported.withheld {
                assert!(
                    !matches!(
                        classes.get(&named),
                        Some(&(Class::Defined | Class::Assumed))
                    ),
                    "{path}: the declaration at {} is withheld for naming {}, which crossed",
                    usize::from(declaration),
                    usize::from(named)
                );
            }
            let crossed = exported
                .classes
                .iter()
                .filter(|&&(_, class)| matches!(class, Class::Defined | Class::Assumed))
                .count();
            let (manifest, store) = commit(&exported.artifact);
            assert_eq!(
                RecordCount(
                    u64::try_from(crossed.saturating_add(1)).expect("a count fits sixty-four bits")
                ),
                manifest.record_count(),
                "{path}: the manifest counts the header and every declaration that crossed"
            );
            let read = manifest
                .read_under(&store, TreeParams::current())
                .unwrap_or_else(|refusal| panic!("{path}: the records read back: {refusal}"));
            let names: Vec<&StructuredName> = read
                .declarations()
                .iter()
                .map(|marked| marked.declaration().name())
                .collect();
            assert_eq!(
                exported.crossed_names.iter().collect::<Vec<_>>(),
                names,
                "{path}: the artifact holds exactly the declarations that crossed, in admission \
                 order, under their names"
            );
        }
    }
}
