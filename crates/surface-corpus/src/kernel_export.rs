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
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Root
{
    /// `strict/`.
    Strict,
    /// `fixture/`, the pending set among it.
    Fixture,
}

/// What became of one declaration at the kernel boundary.
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
    /// The lowering refused it, under this name, and nothing was offered.
    NeverOffered(RefusalName),
}

/// One source the lowering read, exported.
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
/// trivial.
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
/// trivial.
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
/// trivial.
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
    let readmission = bridge::readmit(&arena, &verdicts);
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
/// trivial.
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
/// trivial.
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
    use alloc::collections::BTreeSet;
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

    #[test]
    fn corpus_exercises_multiple_exclusion_classes()
    {
        let excluded: BTreeSet<Class> = corpus()
            .iter()
            .flat_map(|exported| exported.classes.iter().map(|&(_, class)| class))
            .filter(|class| !matches!(*class, Class::Defined | Class::Assumed))
            .collect();
        assert!(
            excluded.len() >= 4_usize,
            "the corpus keeps several kinds of declaration out of the kernel: {excluded:?}"
        );
    }
}
