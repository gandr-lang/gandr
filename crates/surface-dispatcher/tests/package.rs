//! A package's discovery from any path in it, the paths a verb walks, and the
//! manifest the checker writes from the package's model (#2687).
//!
//! The package cases, in a `cfg(test)` module so the crate's lint wall reads
//! them as test code rather than as shipping code.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use core::convert::Infallible;
use core::ops::ControlFlow;
use std::path::Path;
use std::path::PathBuf;

use anodized::spec;
use gandr_core_incremental::ContentKey;
use gandr_core_incremental::ItemKey;
use gandr_core_incremental::content_keys;
use gandr_kernel_term::AdmissionMark;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::DeclarationBuilder;
use gandr_kernel_term::DeclarationContent;
use gandr_kernel_term::EncodedArtifact;
use gandr_kernel_term::LevelSignature;
use gandr_kernel_term::MarkedDeclaration;
use gandr_storage_store::Store;
use gandr_storage_store::StoreError;
use gandr_storage_values::ValueError;
use gandr_surface_dispatcher::Composed;
use gandr_surface_dispatcher::Coordinate;
use gandr_surface_dispatcher::Export;
use gandr_surface_dispatcher::Exporting;
use gandr_surface_dispatcher::Field;
use gandr_surface_dispatcher::Identity;
use gandr_surface_dispatcher::LOCK;
use gandr_surface_dispatcher::Lock;
use gandr_surface_dispatcher::LockFault;
use gandr_surface_dispatcher::Lowered;
use gandr_surface_dispatcher::LoweringCount;
use gandr_surface_dispatcher::Manifest;
use gandr_surface_dispatcher::ManifestFault;
use gandr_surface_dispatcher::Package;
use gandr_surface_dispatcher::Pool;
use gandr_surface_dispatcher::Reconciled;
use gandr_surface_dispatcher::Revisions;
use gandr_surface_dispatcher::Shadows;
use gandr_surface_dispatcher::Step;
use gandr_surface_dispatcher::Unaddressed;
use gandr_surface_dispatcher::Unexported;
use gandr_surface_dispatcher::Unmanifested;
use gandr_surface_dispatcher::Unmembered;
use gandr_surface_dispatcher::Unpathed;
use gandr_surface_dispatcher::Unreadmitted;
use gandr_surface_dispatcher::Unresolved;
use gandr_surface_dispatcher::Unstated;
use gandr_surface_dispatcher::WORKSPACE_LOCK;
use gandr_surface_dispatcher::Walk;
use gandr_surface_dispatcher::Width;
use gandr_surface_dispatcher::Workspace;
use gandr_surface_dispatcher::classify;
use gandr_surface_dispatcher::exported_source;
use gandr_surface_dispatcher::item_program;
use gandr_surface_dispatcher::lay_out_shadowed;
use gandr_surface_dispatcher::lower_source;
use gandr_surface_dispatcher::lower_unit_source;
use gandr_surface_dispatcher::package_root;
use gandr_surface_dispatcher::packaged;
use gandr_surface_dispatcher::reconcile;
use gandr_surface_dispatcher::reconcile_lock;
use gandr_surface_dispatcher::relock;
use gandr_surface_dispatcher::stepped_alone;
use gandr_surface_dispatcher::workspace_root;
use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::built_in;
use gandr_surface_lowering::DeclarationCount;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

/// How many scratch directories and stores this process has made. Each takes
/// the count as its last name segment, so two tests that share a name never
/// share a directory when one process runs them on parallel threads (#5204).
static MADE: core::sync::atomic::AtomicUsize = core::sync::atomic::AtomicUsize::new(0);

/// A directory under the system's temporary directory, named for `kind`,
/// `test`, this process and this call, and so owned by this call alone.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a path no earlier call of this process returned.
/// - provides: the path, which no call has made.
/// - fails: never.
/// - panics: none.
/// - executable: none — unwitnessable provenance: the obligation concerns every
///   earlier call of the process, which one call holds nothing to check
///   against.
///
/// # Adequacy
/// - hypothesis: L3 — two calls with one name answer two paths.
/// - witness: `tests::package::two_calls_with_one_name_make_two_directories_5204`
fn owned(
    kind: &Path,
    test: &Path,
) -> PathBuf
{
    let call = MADE.fetch_add(1, core::sync::atomic::Ordering::Relaxed);
    std::env::temp_dir().join(format!(
        "gandr-dispatcher-{}-{}-{}-{call}",
        kind.display(),
        test.display(),
        std::process::id()
    ))
}

/// A fresh scratch directory named for `test`, this process and this call,
/// holding each of `files`, empty.
///
/// # Specification
/// - requires: `files` are relative paths.
/// - ensures: the canonical path of a directory that this call alone made, any
///   stale one of the same name removed first, in which each file of `files`
///   has been written empty, its parent directories made.
/// - fails: never.
/// - panics: if a directory or a file cannot be made.
///
/// # Adequacy
/// - hypothesis: L3 — every case below finds the files it lays out.
/// - witness: `tests::package::a_package_is_found_from_any_path_in_it_2687`
#[spec(ensures: |ref ret| ret.is_dir() && files.iter().all(|file| ret.join(file).is_file()))]
fn scratch(
    test: &Path,
    files: &[&Path],
) -> PathBuf
{
    let directory = owned(Path::new("package"), test);
    if directory.exists() {
        std::fs::remove_dir_all(&directory).expect("a stale scratch directory is removed");
    }
    std::fs::create_dir_all(&directory).expect("the scratch directory is made");
    for file in files {
        let path = directory.join(file);
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent).expect("the file's directory is made");
        }
        std::fs::write(&path, "").expect("the file is written");
    }
    directory
        .canonicalize()
        .expect("the scratch directory canonicalizes")
}

/// A fresh store named for `test`, this process and this call, any stale one
/// of the same name removed first.
///
/// # Specification
/// trivial.
fn stored(test: &Path) -> Store
{
    let directory = owned(Path::new("store"), test);
    if directory.exists() {
        std::fs::remove_dir_all(&directory).expect("a stale store is removed");
    }
    Store::open(&directory).expect("the store opens")
}

/// #5204: two calls with one test name make two directories, so the cases
/// that share a name never remove or fill each other's directory on parallel
/// threads.
#[test]
fn two_calls_with_one_name_make_two_directories_5204()
{
    let first = scratch(Path::new("shared"), &[Path::new("package.gandr")]);
    let second = scratch(Path::new("shared"), &[Path::new("package.gandr")]);
    assert_ne!(first, second, "each call owns its directory");
    assert!(
        first.join("package.gandr").is_file(),
        "the second call leaves the first directory in place"
    );
    for directory in [first, second] {
        std::fs::remove_dir_all(&directory).expect("the scratch directory is removed");
    }
}

/// The root, package source and sources of the package `from` sits in, or
/// none.
///
/// # Specification
/// trivial.
fn found(from: &Path) -> Option<(PathBuf, PathBuf, PathBuf)>
{
    match Package::discover(from) {
        Maybe::Present(package) => Some((
            package.root().to_path_buf(),
            package.source().to_path_buf(),
            package.sources().to_path_buf(),
        )),
        Maybe::Absent(package_root::Absent::Unpackaged) => None,
    }
}

/// A package source whose model states `sources` as `stated`, and nothing
/// else: what discovery reads.
///
/// # Specification
/// trivial.
fn sourced(stated: &Path) -> String
{
    format!(
        "pub module Package : Model(Gandr.Package) where {{\n  def sources = \"{}\";\n}}\n",
        stated.display()
    )
}

/// #2687, #4916: a package is found from any path in it — a leaf deep in its
/// sources, its sources directory, its root — at its root, the directory
/// holding its package source, with the sources its model names. A model
/// naming `.` keeps its modules at the root, and one naming none, or a
/// directory outside the root, has the root for its sources. A
/// `src/package.gandr` roots a package at `src`. An inner package source is
/// found before an outer one, and a directory with no package source above
/// it is in no package.
#[test]
fn a_package_is_found_from_any_path_in_it_2687()
{
    let directory = scratch(Path::new("found"), &[
        Path::new("hello/package.gandr"),
        Path::new("hello/src/text/greet/words.gandr"),
        Path::new("flat/package.gandr"),
        Path::new("flat/inner/package.gandr"),
        Path::new("flat/inner/deep.gandr"),
        Path::new("outside/package.gandr"),
        Path::new("nested/src/package.gandr"),
        Path::new("loose/alone.gandr"),
    ]);
    for (package, stated) in [("hello", "src"), ("flat", "."), ("outside", "../hello")] {
        std::fs::write(
            directory.join(package).join("package.gandr"),
            sourced(Path::new(stated)),
        )
        .expect("the package source is written");
    }
    let hello = (
        directory.join("hello"),
        directory.join("hello/package.gandr"),
        directory.join("hello/src"),
    );
    for from in [
        "hello/src/text/greet/words.gandr",
        "hello/src/text",
        "hello/src",
        "hello/package.gandr",
        "hello",
    ] {
        assert_eq!(
            found(&directory.join(from)),
            Some(hello.clone()),
            "`{from}` is in the package rooted at `hello`, its sources at `src`"
        );
    }
    let at_root = |package: &str| {
        Some((
            directory.join(package),
            directory.join(package).join("package.gandr"),
            directory.join(package),
        ))
    };
    assert_eq!(
        found(&directory.join("flat")),
        at_root("flat"),
        "a package whose `sources` is `.` keeps its modules at its root"
    );
    assert_eq!(
        found(&directory.join("flat/inner/deep.gandr")),
        at_root("flat/inner"),
        "the nearest library is the package's, and one stating no `sources` keeps its \
         modules at its root"
    );
    assert_eq!(
        found(&directory.join("outside")),
        at_root("outside"),
        "a `sources` leaving the root names no sources of its own"
    );
    assert_eq!(
        found(&directory.join("nested/src")),
        at_root("nested/src"),
        "a `src/package.gandr` roots a package at `src`, never above it"
    );
    assert_eq!(
        found(&directory.join("nested")),
        None,
        "the directory above a `src/package.gandr` is in no package"
    );
    assert_eq!(
        found(&directory.join("loose/alone.gandr")),
        None,
        "no library above it"
    );
    assert_eq!(
        found(&directory.join("absent.gandr")),
        None,
        "a path that does not exist is in no package"
    );
    std::fs::remove_dir_all(&directory).expect("the scratch directory is removed");
}

/// #2687, #4916: a path inside a package walks the whole package, listed
/// once: its package source at its root, then its sources. A path outside
/// its sources but under its root is walked beside them, a path in no package
/// is walked as given, and no path walks the package the working directory is
/// in, or is refused outside every package.
#[test]
fn a_path_in_a_package_walks_the_whole_package_2687()
{
    let directory = scratch(Path::new("walked"), &[
        Path::new("hello/package.gandr"),
        Path::new("hello/src/text/greet.gandr"),
        Path::new("hello/src/text/part.gandr"),
        Path::new("hello/tests/smoke.gandr"),
        Path::new("loose/alone.gandr"),
    ]);
    std::fs::write(
        directory.join("hello/package.gandr"),
        sourced(Path::new("src")),
    )
    .expect("the package source is written");
    let walked = |paths: &[&str], working: &str| {
        packaged(
            paths.iter().map(|path| directory.join(path)).collect(),
            &directory.join(working),
        )
        .map(|(walked, packages, _gathered)| {
            (
                walked,
                packages
                    .iter()
                    .map(|package| package.root().to_path_buf())
                    .collect::<Vec<_>>(),
            )
        })
    };
    let hello = directory.join("hello");
    let root_file = directory.join("hello/package.gandr");
    assert_eq!(
        walked(&[], "hello/src/text"),
        Ok((
            Vec::from([root_file.clone(), directory.join("hello/src")]),
            Vec::from([hello.clone()])
        )),
        "no path walks the package the working directory is in, whole"
    );
    assert_eq!(
        walked(&[], "hello"),
        Ok((
            Vec::from([PathBuf::from("package.gandr"), PathBuf::from("src")]),
            Vec::from([hello.clone()])
        )),
        "the package below the working directory is listed relative to it"
    );
    assert_eq!(
        walked(&[], "hello/src"),
        Ok((
            Vec::from([root_file.clone(), PathBuf::from(".")]),
            Vec::from([hello.clone()])
        )),
        "the working directory itself is `.`"
    );
    assert_eq!(
        walked(&[], "loose"),
        Err(Unpathed::Nowhere {
            working: directory.join("loose")
        }),
        "no path outside every package is refused"
    );
    assert_eq!(
        walked(
            &[
                "hello/src/text/greet.gandr",
                "loose/alone.gandr",
                "hello/package.gandr",
                "hello/src/text/part.gandr",
                "hello/tests/smoke.gandr"
            ],
            "loose"
        ),
        Ok((
            Vec::from([
                root_file,
                directory.join("hello/src"),
                directory.join("loose/alone.gandr"),
                directory.join("hello/tests/smoke.gandr"),
            ]),
            Vec::from([hello]),
        )),
        "a package once, at its first path; a path in none as given; one under the root \
         beside the sources, the package source not twice"
    );
    std::fs::remove_dir_all(&directory).expect("the scratch directory is removed");
}

/// #3889: a package's root given walks each source once. The root, kept
/// beside the sources for its entries outside them, lists the sources
/// directory no second time, answers through it, and walks a source under
/// it outside them once.
#[test]
fn a_package_root_walks_each_source_once_3889()
{
    let directory = scratch(Path::new("root-once"), &[
        Path::new("hello/package.gandr"),
        Path::new("hello/src/text/greet.gandr"),
        Path::new("hello/tests/smoke.gandr"),
    ]);
    std::fs::write(
        directory.join("hello/package.gandr"),
        sourced(Path::new("src")),
    )
    .expect("the package source is written");
    let (walked, ..) = packaged(Vec::from([directory.join("hello")]), &directory)
        .expect("the root stands in a package");
    let mut reached = Vec::new();
    let ControlFlow::Continue(_report) =
        Walk::new(walked.iter().map(|path| directory.join(path)).collect()).visit(
            &Pool::new(Width::SERIAL),
            |step| -> ControlFlow<Infallible> {
                let (Step::Source { path, .. } | Step::Fault { path, .. }) = step;
                reached.push(path.strip_prefix(&directory).unwrap_or(path).to_path_buf());
                ControlFlow::Continue(())
            },
        );
    assert_eq!(
        reached,
        Vec::from([
            PathBuf::from("hello/package.gandr"),
            PathBuf::from("hello/src/text/greet.gandr"),
            PathBuf::from("hello/tests/smoke.gandr"),
        ]),
        "each source once, the sources first, and the root faults nowhere"
    );
    std::fs::remove_dir_all(&directory).expect("the scratch directory is removed");
}

/// #2687: a workspace is found from any directory below it, names its
/// members by its `members` list in order, and a verb given no path in it
/// outside every package, or given its directory, walks its source and each
/// member's sources; a verb in a member walks that member alone. A member
/// rooting no package, a `members` that is no list of strings, and one left
/// undeclared are refused, and a directory with no workspace above it is in
/// none.
#[test]
fn a_workspace_walks_every_member_it_names_2687()
{
    let directory = scratch(Path::new("workspace"), &[
        Path::new("workspace.gandr"),
        Path::new("hello/package.gandr"),
        Path::new("hello/src/greet.gandr"),
        Path::new("tools/package.gandr"),
        Path::new("docs/notes.gandr"),
    ]);
    std::fs::write(
        directory.join("hello/package.gandr"),
        sourced(Path::new("src")),
    )
    .expect("the package source is written");
    let source = directory.join("workspace.gandr");
    let stated = |members: &str| {
        format!(
            "import std.list (List);\npub module Workspace : Model(Gandr.Workspace) where {{ def version = \"0.2.0\"; }}\n{members}\n"
        )
    };
    std::fs::write(
        &source,
        stated("pub def members : List(String) = #[\"hello\", \"tools\"];"),
    )
    .expect("the workspace is written");
    for from in ["", "docs", "hello", "tools/package.gandr"] {
        assert!(
            matches!(
                Workspace::discover(&directory.join(from)),
                Maybe::Present(ref workspace) if workspace.root() == directory
            ),
            "`{from}` is in the workspace above it"
        );
    }
    assert_eq!(
        Workspace::discover(&std::env::temp_dir()),
        Maybe::Absent(workspace_root::Absent::Unworkspaced),
        "a directory with no workspace above it is in none"
    );
    let hello = directory.join("hello");
    let tools = directory.join("tools");
    let walked = |paths: &[&Path], working: &str| {
        packaged(
            paths.iter().map(|path| path.to_path_buf()).collect(),
            &directory.join(working),
        )
        .map(|(walked, packages, _gathered)| {
            (
                walked,
                packages
                    .iter()
                    .map(|package| package.root().to_path_buf())
                    .collect::<Vec<_>>(),
            )
        })
    };
    assert_eq!(
        walked(&[], ""),
        Ok((
            Vec::from([
                PathBuf::from("workspace.gandr"),
                PathBuf::from("hello/package.gandr"),
                PathBuf::from("hello/src"),
                PathBuf::from("tools"),
            ]),
            Vec::from([hello.clone(), tools.clone()]),
        )),
        "no path at the workspace's root walks its source and each member, in order"
    );
    assert_eq!(
        walked(&[], "docs"),
        Ok((
            Vec::from([
                source.clone(),
                hello.join("package.gandr"),
                hello.join("src"),
                tools.clone(),
            ]),
            Vec::from([hello.clone(), tools.clone()]),
        )),
        "no path in the workspace outside every package walks it whole, each path not below \
         the working directory as it stands"
    );
    assert_eq!(
        walked(&[&directory], "docs"),
        Ok((
            Vec::from([
                source.clone(),
                hello.join("package.gandr"),
                hello.join("src"),
                tools.clone(),
            ]),
            Vec::from([hello.clone(), tools]),
        )),
        "the workspace's directory given walks it whole"
    );
    assert_eq!(
        walked(&[], "hello"),
        Ok((
            Vec::from([PathBuf::from("package.gandr"), PathBuf::from("src")]),
            Vec::from([hello])
        )),
        "no path in a member walks that member alone"
    );
    for (members, refused) in [
        (
            "pub def members : List(String) = #[\"hello\", \"docs\"];",
            Unmembered::Unpackaged {
                member: String::from("docs"),
            },
        ),
        (
            "pub def members : String = \"hello\";",
            Unmembered::Unlisted {
                came: String::from("\"hello\""),
            },
        ),
        ("", Unmembered::Undeclared),
    ] {
        std::fs::write(&source, stated(members)).expect("the workspace is rewritten");
        assert_eq!(
            walked(&[], ""),
            Err(Unpathed::Unmembered {
                workspace: source.clone(),
                why: refused.clone(),
            }),
            "`{members}` is refused as {refused}"
        );
    }
    std::fs::remove_dir_all(&directory).expect("the scratch directory is removed");
}

/// The manifest that `model` states as the package source at `source`, which
/// imports `std.build` before the model, composed as `gandr check` composes
/// a package source.
///
/// # Specification
/// - requires: `source` is a path a `package.gandr` may be written at, and its
///   directory roots a package once it is written.
/// - ensures: [`Manifest::of`] the program and the report of the package
///   source, laid out over the sources it imports and judged as `stepped_alone`
///   judges it, for the package `source` roots.
/// - fails: never on the admitted domain.
/// - panics: a source that does not write, roots no package, or does not settle
///   violates the precondition.
/// - executable: none — reading the manifest runs the program, which a
///   predicate could only check by running it again; the cases observe each
///   outcome.
///
/// # Adequacy
/// - hypothesis: L3 — the manifest cases below compose package sources as the
///   checker reads them, each an ascribed `Model(Gandr.Package)`.
/// - witness: `tests::package::a_manifest_reads_the_package_model_2687`
/// - witness: `tests::package::a_manifest_lists_the_modules_its_sources_make_2687`
fn manifest_at<'text>(
    source: &Path,
    model: impl Into<SourceText<'text>>,
) -> Result<Manifest, Unmanifested>
{
    let text = format!("{STD_PACKAGE}{}", model.into());
    if let Err(why) = std::fs::write(source, &text) {
        panic!("the package source is written: {why}");
    }
    let Some(Maybe::Present(package)) = source.parent().map(Package::discover)
    else {
        panic!("the package is found");
    };
    let composed = stepped_alone(source, SourceText::from(text.as_str()), |step| match step {
        Step::Source {
            composed:
                Composed::Settled {
                    mut program,
                    report,
                    ..
                },
            ..
        } => Manifest::of(&mut program, &report, &package),
        Step::Source {
            composed: Composed::Refused(refusal),
            ..
        } => panic!("the package source settles: {refusal}"),
        Step::Fault { fault, .. } => panic!("the package source composes: {fault}"),
    });
    match composed {
        Ok(manifest) => manifest,
        Err(why) => panic!("the built-in grammar builds: {why:?}"),
    }
}

/// The manifest that `model` states, for a package of its package source
/// alone.
///
/// # Specification
/// - requires: as [`manifest_at`].
/// - ensures: [`manifest_at`] the `package.gandr` of a scratch package whose
///   root holds nothing else, so discovery reads the `sources` it states.
/// - fails: never on the admitted domain.
/// - panics: as [`manifest_at`], and as [`scratch`].
/// - executable: none — as [`manifest_at`].
///
/// # Adequacy
/// - hypothesis: L3 — the manifest cases below compose real sources.
/// - witness: `tests::package::a_manifest_reads_the_package_model_2687`
fn manifest_of<'text>(model: impl Into<SourceText<'text>>) -> Result<Manifest, Unmanifested>
{
    let directory = scratch(Path::new("alone"), &[Path::new("package.gandr")]);
    manifest_at(&directory.join("package.gandr"), model)
}

/// The model fields every case below states beside its `name` and its
/// `version`, a string each.
macro_rules! rest {
    () => {
        "def authors = \"Ada, Grace\" ; def licence = \"MIT\" ; def documentation = \
         \"https://d.example\" ; def endpoint = \"https://e.example\" ; def gandr = \">= 0.1\" ; \
         def features = \"a, b\" ; def systems = \"\" ; def spelling = \"\" ; def sources = \".\" ;"
    };
}

/// The manifest body the fields [`rest`] states render to after `name` and
/// `version`, up to `modules`.
const REST: &str = "authors = \"Ada, Grace\"\nlicence = \"MIT\"\ndocumentation = \
                    \"https://d.example\"\nendpoint = \"https://e.example\"\n";

/// The toolchain table the fields [`rest`] states render to after `modules`.
const TOOLCHAIN: &str = "\n[toolchain]\ngandr = \">= 0.1\"\nfeatures = [\n  \"a\",\n  \"b\",\n]\nsystems \
                         = []\n";

/// #2687, #3030: a manifest reads each field of the `Package` model, each run
/// to its string and decoded; a model missing a field, and one whose field is
/// not a string, whether the first or a later one, are refused at that field.
/// The ascription refuses a missing field and a field that is no string, so
/// the manifest finds that field unrunnable.
#[test]
fn a_manifest_reads_the_package_model_2687()
{
    let read = manifest_of(concat!(
        "pub module Package : Model(Gandr.Package) where { def name = \"a \\\"quoted\\\" name\" ; \
         def version = \"0.1.0\" ; ",
        rest!(),
        " }"
    ))
    .expect("every field is what it states");
    assert_eq!(
        read.render(),
        manifest_of(concat!(
            "pub module Package : Model(Gandr.Package) where { def name = \"a \\\"quoted\\\" name\" \
             ; def version = \"0.1.0\" ; ",
            rest!(),
            " }"
        ))
        .expect("the same model")
        .render()
    );
    assert!(
        read.render().ends_with(&format!(
            "\n[package]\nname = \"a \\\"quoted\\\" name\"\nversion = \"0.1.0\"\n{REST}modules = \
             []\n{TOOLCHAIN}"
        )),
        "the decoded name, quoted again for TOML: {}",
        read.render()
    );
    assert!(
        matches!(
            manifest_of(concat!(
                "pub module Package : Model(Gandr.Package) where { def name = \"hello\" ; ",
                rest!(),
                " }"
            )),
            Err(Unmanifested::Unstrung {
                field: Field::Version,
                ..
            })
        ),
        "a missing version"
    );
    assert!(
        matches!(
            manifest_of(concat!(
                "pub module Package : Model(Gandr.Package) where { def name = 3 ; def version = \
                 \"0.1.0\" ; ",
                rest!(),
                " }"
            )),
            Err(Unmanifested::Unstrung {
                field: Field::Name,
                ..
            })
        ),
        "a name that is no string"
    );
    assert!(
        matches!(
            manifest_of(
                "pub module Package : Model(Gandr.Package) where { def name = \"hello\" ; def \
                 version = \"0.1.0\" ; def authors = 3 ; def licence = \"MIT\" ; def documentation \
                 = \"d\" ; def endpoint = \"e\" ; }"
            ),
            Err(Unmanifested::Unstrung {
                field: Field::Authors,
                ..
            })
        ),
        "authors that are no string"
    );
    assert_eq!(
        manifest_of(concat!(
            "def name = \"hello\" ; def version = \"0.1.0\" ; ",
            rest!()
        )),
        Err(Unmanifested::Undeclared(Field::Name)),
        "top-level fields are not the package's"
    );
}

/// #4916: a model's `sources` is the string literal discovery reads before
/// any source is checked. One computed from another declaration runs to a
/// string discovery never read, and one naming a directory above the root
/// leaves the package; the manifest refuses both. Discovery reads `src`, `.`
/// and the empty string as written, and nothing from an escaped string or a
/// module nested in the model.
#[test]
fn a_model_s_sources_is_the_literal_discovery_reads_4916()
{
    let model = |sources: &str| {
        format!(
            "pub module Package : Model(Gandr.Package) where {{ def name = \"p\" ; def version = \
             \"0.1.0\" ; def authors = \"A\" ; def licence = \"MIT\" ; def documentation = \"d\" ; \
             def endpoint = \"e\" ; def gandr = \">= 0.1\" ; def features = \"\" ; def systems = \
             \"\" ; def spelling = \"\" ; {sources} }}"
        )
    };
    let manifest = |sources: &str| manifest_of(model(sources).as_str());
    assert!(
        manifest("def sources = \"src\" ;").is_ok(),
        "a literal reads"
    );
    assert_eq!(
        manifest("def here = \".\" ; def sources = here ;"),
        Err(Unmanifested::Unstated {
            came: String::from("."),
        }),
        "a computed `sources`"
    );
    assert_eq!(
        manifest("def sources = \"../elsewhere\" ;"),
        Err(Unmanifested::Outside {
            came: String::from("../elsewhere"),
        }),
        "a `sources` above the root"
    );
    assert!(
        matches!(
            manifest(""),
            Err(Unmanifested::Unstrung {
                field: Field::Sources,
                ..
            })
        ),
        "a missing `sources`"
    );
    let directory = scratch(Path::new("stated"), &[Path::new("package.gandr")]);
    let stated = |sources: &str| {
        std::fs::write(directory.join("package.gandr"), model(sources))
            .expect("the package source is written");
        match Package::discover(&directory) {
            Maybe::Present(package) => package.stated().map(Path::to_path_buf),
            Maybe::Absent(_) => panic!("the scratch package is found"),
        }
    };
    for (sources, read) in [
        ("def sources = \"src\" ;", Some("src")),
        ("def sources = \".\" ;", Some(".")),
        ("def sources = \"\" ;", Some("")),
        ("def sources = \"s\\u{72}c\" ;", None),
        ("module Inner where { def sources = \"src\" ; }", None),
    ] {
        assert_eq!(
            stated(sources),
            read.map(PathBuf::from),
            "`{sources}` reads as {read:?}"
        );
    }
    // A laid-out model reads as a braced one: the labeler writes its block's
    // brackets as tokens that spell nothing, at depth one as `{` and `}` are.
    let laid_out = |sources: &str| {
        std::fs::write(
            directory.join("package.gandr"),
            format!(
                "pub module Package : Model(Gandr.Package) where\n  def name = \"p\";\n  {sources}\n"
            ),
        )
        .expect("the package source is written");
        match Package::discover(&directory) {
            Maybe::Present(package) => package.stated().map(Path::to_path_buf),
            Maybe::Absent(_) => panic!("the scratch package is found"),
        }
    };
    assert_eq!(
        laid_out("def sources = \"src\";"),
        Some(PathBuf::from("src")),
        "a laid-out model's `sources` reads"
    );
    assert_eq!(
        laid_out("module Inner where\n    def sources = \"src\";"),
        None,
        "a laid-out nested module's `sources` reads none"
    );
    std::fs::remove_dir_all(&directory).expect("the scratch directory is removed");
}

/// #2687: a manifest renders its header, the digest of its body and its
/// table, the same bytes each time, an empty module list as `[]` the way the
/// tree's TOML formatter writes it, and escapes what TOML's basic strings
/// escape.
#[test]
fn a_manifest_renders_its_digest_and_its_table_2687()
{
    let rendered = manifest_of(concat!(
        "pub module Package : Model(Gandr.Package) where { def name = \"hello\" ; def version = \
         \"0.1.0\" ; ",
        rest!(),
        " }"
    ))
    .expect("the model reads")
    .render();
    let body = format!(
        "\n[package]\nname = \"hello\"\nversion = \"0.1.0\"\n{REST}modules = []\n{TOOLCHAIN}"
    );
    assert_eq!(
        rendered,
        format!(
            "# Written by `gandr check` from the package's `Package` model: edit the model, not \
             this file.\n# blake3: {}\n{body}",
            blake3::hash(body.as_bytes()).to_hex()
        )
    );
    let escaped = manifest_of(concat!(
        "pub module Package : Model(Gandr.Package) where { def name = \
         \"back\\\\slash\\nline\\ttab\" ; def version = \"1\" ; ",
        rest!(),
        " }"
    ))
    .expect("the model reads")
    .render();
    assert!(
        escaped.contains("\nname = \"back\\\\slash\\nline\\ttab\"\n"),
        "a backslash, a newline and a tab escaped: {escaped}"
    );
}

/// #3135: a manifest renders what the model asks of the toolchain as its
/// `[toolchain]` table, `gandr` as written and each list one entry a line;
/// a `gandr` stating no constraint, and a model missing `features`, are
/// refused.
#[test]
fn a_manifest_renders_the_toolchain_its_model_asks_for_3135()
{
    /// The model of a package `p` stating `$toolchain` beside its other fields.
    macro_rules! model {
        ($toolchain:literal) => {
            manifest_of(concat!(
                "pub module Package : Model(Gandr.Package) where { def name = \"p\" ; def version \
                 = \"0.1.0\" ; def authors = \"A\" ; def licence = \"MIT\" ; def documentation = \
                 \"d\" ; def endpoint = \"e\" ; def spelling = \"\" ; def sources = \".\" ; ",
                $toolchain,
                " }"
            ))
        };
    }
    let read = model!(
        "def gandr = \">= 0.3.1\" ; def features = \" package-lock ,, std-build \" ; def \
         systems = \"x86_64-linux\" ;"
    )
    .expect("the constraints read");
    assert!(
        read.render().ends_with(
            "modules = []\n\n[toolchain]\ngandr = \">= 0.3.1\"\nfeatures = [\n  \
             \"package-lock\",\n  \"std-build\",\n]\nsystems = [\n  \"x86_64-linux\",\n]\n"
        ),
        "the table follows the package's, each entry trimmed: {}",
        read.render()
    );
    assert_eq!(
        model!("def gandr = \"0.3\" ; def features = \"\" ; def systems = \"\" ;"),
        Err(Unmanifested::Unconstrained {
            came: String::from("0.3"),
        }),
        "a version with no `>=`"
    );
    assert!(
        matches!(
            model!("def gandr = \"\" ; def systems = \"\" ;"),
            Err(Unmanifested::Unstrung {
                field: Field::Features,
                ..
            })
        ),
        "a missing `features`"
    );
}

/// #3135: a manifest renders the spelling its model names as its
/// `[presentation]` table, the table the user's configuration file writes,
/// and none for an empty one; a name no spelling has is refused.
#[test]
fn a_manifest_renders_the_presentation_its_model_names_3135()
{
    /// The model of a package `p` stating `$spelling` beside its other fields.
    macro_rules! model {
        ($spelling:literal) => {
            manifest_of(concat!(
                "pub module Package : Model(Gandr.Package) where { def name = \"p\" ; def version \
                 = \"0.1.0\" ; def authors = \"A\" ; def licence = \"MIT\" ; def documentation = \
                 \"d\" ; def endpoint = \"e\" ; def gandr = \">= 0.1\" ; def features = \"a, b\" ; \
                 def systems = \"\" ; def spelling = ",
                $spelling,
                " ; def sources = \".\" ; }"
            ))
        };
    }
    let ascii = model!("\"ascii\"").expect("the spelling reads").render();
    assert!(
        ascii.ends_with(&format!(
            "modules = []\n{TOOLCHAIN}\n[presentation]\nspelling = \"ascii\"\n"
        )),
        "the table follows the toolchain's: {ascii}"
    );
    let unnamed = model!("\"\"").expect("an empty spelling reads").render();
    assert!(
        !unnamed.contains("[presentation]"),
        "an empty spelling leaves the reader's own: {unnamed}"
    );
    assert_eq!(
        model!("\"latin\""),
        Err(Unmanifested::Unspelled {
            came: String::from("latin"),
        }),
        "a name no spelling has"
    );
}

/// #2687: a manifest lists every module its package's sources make, by its
/// path, in order: a module in a directory by its directory and its stem, and
/// nothing of the root module or of a package nested inside.
#[test]
fn a_manifest_lists_the_modules_its_sources_make_2687()
{
    let directory = scratch(Path::new("modules"), &[
        Path::new("hello/package.gandr"),
        Path::new("hello/util.gandr"),
        Path::new("hello/text/greet.gandr"),
        Path::new("hello/text/notes.md"),
        Path::new("hello/vendored/package.gandr"),
        Path::new("hello/vendored/inner.gandr"),
    ]);
    let rendered = manifest_at(
        &directory.join("hello/package.gandr"),
        concat!(
            "pub module Package : Model(Gandr.Package) where { def name = \"hello\" ; def version \
             = \"0.1.0\" ; ",
            rest!(),
            " }"
        ),
    )
    .expect("the model reads")
    .render();
    assert!(
        rendered.ends_with(&format!(
            "\nmodules = [\n  \"text.greet\",\n  \"util\",\n]\n{TOOLCHAIN}"
        )),
        "each module by its path, the root and the nested package's left out: {rendered}"
    );
    std::fs::remove_dir_all(&directory).expect("the scratch directory is removed");
}

/// #2687: an absent manifest is written; the checker's own is unchanged on a
/// second run and rewritten when the model changes; a hand edit, and a file
/// with no header, are each refused as drift and left byte for byte.
#[test]
fn a_manifest_is_written_rewritten_and_refused_as_drift_2687()
{
    let directory = scratch(Path::new("reconciled"), &[]);
    let path = directory.join("package.gandr.toml");
    let first = manifest_of(concat!(
        "pub module Package : Model(Gandr.Package) where { def name = \"hello\" ; def version = \
         \"0.1.0\" ; ",
        rest!(),
        " }"
    ))
    .expect("the model reads");
    let second = manifest_of(concat!(
        "pub module Package : Model(Gandr.Package) where { def name = \"hello\" ; def version = \
         \"0.2.0\" ; ",
        rest!(),
        " }"
    ))
    .expect("the model reads");
    let outcome = |manifest: &Manifest| match reconcile(&path, manifest) {
        Ok(reconciled) => Ok(reconciled),
        Err(ManifestFault::Drifted) => Err("drifted"),
        Err(ManifestFault::Io(error)) => panic!("the scratch file is readable: {error}"),
    };
    let on_disk = || std::fs::read_to_string(&path).expect("the manifest reads");
    assert_eq!(outcome(&first), Ok(Reconciled::Written));
    assert_eq!(on_disk(), first.render());
    assert_eq!(outcome(&first), Ok(Reconciled::Unchanged));
    assert_eq!(outcome(&second), Ok(Reconciled::Rewritten));
    assert_eq!(on_disk(), second.render());
    let edited = second.render().replace("0.2.0", "0.3.0");
    std::fs::write(&path, &edited).expect("the hand edit is written");
    assert_eq!(outcome(&first), Err("drifted"), "a hand edit to the body");
    assert_eq!(on_disk(), edited, "left as it stands");
    let headless = "[package]\nname = \"hello\"\nversion = \"0.1.0\"\n";
    std::fs::write(&path, headless).expect("the hand-written file is written");
    assert_eq!(outcome(&first), Err("drifted"), "a file with no header");
    assert_eq!(on_disk(), headless, "left as it stands");
    std::fs::remove_dir_all(&directory).expect("the scratch directory is removed");
}

#[test]
fn each_unrefused_declaration_is_one_item_keyed_by_its_name()
{
    let grammar = built_in().expect("the built-in grammar builds");
    let mut lowerings = LoweringCount::default();
    let lowering = lower_source(
        &grammar,
        SourceText::from(
            "def first : Integer ; def first = 1 ; def broken = missing ; def owed : String ; def last = first ;",
        ),
        &mut lowerings,
    )
    .expect("lowers");
    let Lowered::Module { module, arena } = lowering.into_lowered()
    else {
        panic!("the module is read");
    };
    let program = item_program(&module, arena).expect("positions ascend");
    let keys: Vec<&ItemKey> = program
        .items()
        .iter()
        .map(gandr_core_incremental::Item::key)
        .collect();
    assert_eq!(
        keys,
        vec![
            &ItemKey::from("first"),
            &ItemKey::from("owed"),
            &ItemKey::from("last")
        ],
        "one item per unrefused declaration, keyed by its name, in admission order"
    );
}

/// The texts a case holds for a package's sources in place of their files,
/// by the canonical path each is named by.
#[repr(transparent)]
#[derive(Debug, Default)]
struct Held(BTreeMap<PathBuf, String>);

impl Shadows for Held
{
    /// The text held at `named`, if any.
    ///
    /// # Specification
    /// trivial.
    fn shadowed(
        &self,
        named: &Path,
    ) -> Option<SourceText<'_>>
    {
        self.0
            .get(named)
            .map(|text| SourceText::from(text.as_str()))
    }
}

/// Each item of the unit the source at `source` lays out to, as `shadows`
/// holds it, by its key, with its content key when it has one.
///
/// # Specification
/// - requires: the source reads and lowers to a module under `grammar`.
/// - ensures: the unit's items in admission order, each its item key and its
///   content key, `None` for an item whose content holds an unresolved node.
/// - fails: never on the admitted domain.
/// - panics: a source that does not read or lower violates the precondition.
/// - executable: none — the keys are the lowering's, which a predicate could
///   only restate by lowering again; the cases compare two of them.
///
/// # Adequacy
/// - hypothesis: L3 — the address cases below compare the keys an edit leaves.
/// - witness: `tests::package::an_inert_edit_leaves_the_address_and_a_content_edit_moves_it_3030`
fn keyed(
    grammar: &Pbg,
    source: &Path,
    shadows: &dyn Shadows,
) -> Vec<(ItemKey, Option<ContentKey>)>
{
    let text = shadows.shadowed(source).map_or_else(
        || std::fs::read_to_string(source).expect("the source reads"),
        |held| String::from(held.as_ref()),
    );
    let laid = lay_out_shadowed(
        grammar,
        source,
        classify(source),
        SourceText::from(text.as_str()),
        shadows,
    );
    let mut lowerings = LoweringCount::default();
    let lowering = lower_unit_source(
        grammar,
        SourceText::from(laid.text.as_str()),
        &laid.unit,
        &mut lowerings,
    )
    .expect("the unit lowers");
    let Lowered::Module { module, arena } = lowering.into_lowered()
    else {
        panic!("the unit is read as a module");
    };
    let program = item_program(&module, arena).expect("positions ascend");
    program
        .items()
        .iter()
        .map(|item| item.key().clone())
        .zip(content_keys(&program).into_iter().map(|key| match key {
            Maybe::Present(key) => Some(key),
            Maybe::Absent(_) => None,
        }))
        .collect()
}

/// The import of `std.build` by the absolute path to its source.
const STD_PACKAGE: &str = concat!(
    "import \"",
    env!("CARGO_MANIFEST_DIR"),
    "/../../library/std/src/build.gandr\";\n"
);

/// #3030, #3135: in a package of a package source and one module, an edit to an
/// inert field of the model leaves the package's address and the key of every
/// item but the field's where they were; an edit to a toolchain constraint,
/// which is content, moves the address and only its own key, and so does an
/// edit to the module's item.
#[test]
fn an_inert_edit_leaves_the_address_and_a_content_edit_moves_it_3030()
{
    let directory = scratch(Path::new("address"), &[
        Path::new("hello/package.gandr"),
        Path::new("hello/src/text/greet.gandr"),
    ]);
    let library = directory.join("hello/package.gandr");
    let leaf = directory.join("hello/src/text/greet.gandr");
    let stated = |name: &str, gandr: &str| {
        format!(
            "import text.greet (greeting);\n{STD_PACKAGE}pub module Package : \
             Model(Gandr.Package) where {{\n  def name : String = \"{name}\";\n  def version = \
             \"0.1.0\";\n  def authors = \"Ada\";\n  def licence = \"MIT\";\n  def documentation \
             = \"d\";\n  def endpoint = \"e\";\n  def gandr = \"{gandr}\";\n  def features = \
             \"\";\n  def systems = \"\";\n  def spelling = \"\";\n  def sources = \"src\";\n}}\npub def \
             welcome = greeting;\n"
        )
    };
    std::fs::write(&library, stated("hello", ">= 0.0")).expect("the library is written");
    std::fs::write(&leaf, "pub def greeting = \"hello, world\";\n").expect("the leaf is written");
    let Maybe::Present(package) = Package::discover(&library)
    else {
        panic!("the package is found");
    };
    let grammar = built_in().expect("the built-in grammar builds");
    let store = stored(Path::new("inert"));
    let address = |held: &Held| {
        package
            .identity(&grammar, held, &Lock::default(), &store)
            .expect("the package addresses")
            .address
    };
    let before = address(&Held::default());
    let renamed = Held(BTreeMap::from([(
        library.clone(),
        stated("howdy", ">= 0.0"),
    )]));
    assert_eq!(
        address(&renamed),
        before,
        "an edit to `name` leaves the address"
    );
    let unrenamed = keyed(&grammar, &library, &Held::default());
    let swept = keyed(&grammar, &library, &renamed);
    let renamed_items = moved(&unrenamed, &swept);
    assert!(
        !renamed_items.is_empty() && renamed_items.iter().all(|key| key == "name"),
        "only the field's own key moves, and every other item's key stays: {renamed_items:?}"
    );
    let constrained = Held(BTreeMap::from([(
        library.clone(),
        stated("hello", ">= 0.1"),
    )]));
    assert_ne!(
        address(&constrained),
        before,
        "an edit to `gandr` moves the address"
    );
    let constrained_items = moved(&unrenamed, &keyed(&grammar, &library, &constrained));
    assert!(
        !constrained_items.is_empty() && constrained_items.iter().all(|key| key == "gandr"),
        "only the constraint's own key moves: {constrained_items:?}"
    );
    let regreeted = Held(BTreeMap::from([(
        leaf,
        String::from("pub def greeting = \"hello, there\";\n"),
    )]));
    assert_ne!(
        address(&regreeted),
        before,
        "an edit to the module's item moves the address"
    );
    std::fs::remove_dir_all(&directory).expect("the scratch directory is removed");
}

/// #6141: in a package source, an edit to a top-level definition marked
/// `@[ inert ]` leaves the package's address, and the same edit to the
/// definition unmarked moves it.
#[test]
fn an_edit_to_an_inert_definition_leaves_the_address_6141()
{
    let directory = scratch(Path::new("inert-definition"), &[Path::new(
        "hello/package.gandr",
    )]);
    let library = directory.join("hello/package.gandr");
    let stated = |mark: &str, note: &str| {
        format!(
            "{STD_PACKAGE}pub module Package : Model(Gandr.Package) where {{\n  def name : String \
             = \"hello\";\n  def version = \"0.1.0\";\n  def authors = \"Ada\";\n  def licence = \
             \"MIT\";\n  def documentation = \"d\";\n  def endpoint = \"e\";\n  def gandr = \">= \
             0.0\";\n  def features = \"\";\n  def systems = \"\";\n  def spelling = \"\";\n  def \
             sources = \"src\";\n}}\n{mark}def note = \"{note}\";\n"
        )
    };
    std::fs::write(&library, stated("@[ inert ]\n", "a")).expect("the library is written");
    let Maybe::Present(package) = Package::discover(&library)
    else {
        panic!("the package is found");
    };
    let grammar = built_in().expect("the built-in grammar builds");
    let store = stored(Path::new("inert-definition"));
    let address = |mark: &str, note: &str| {
        let held = Held(BTreeMap::from([(library.clone(), stated(mark, note))]));
        package
            .identity(&grammar, &held, &Lock::default(), &store)
            .expect("the package addresses")
            .address
    };
    assert_eq!(
        address("@[ inert ]\n", "b"),
        address("@[ inert ]\n", "a"),
        "an edit to the inert `note` leaves the address"
    );
    assert_ne!(
        address("", "b"),
        address("", "a"),
        "the same edit to a content `note` moves the address"
    );
    std::fs::remove_dir_all(&directory).expect("the scratch directory is removed");
}

/// The keys, spelled, of the items whose content key differs between
/// `before` and `after`, two keyings of one unit.
///
/// # Specification
/// - requires: `before` and `after` key the same items in the same order.
/// - ensures: each position's item key, spelled lossily as UTF-8, where the two
///   content keys differ, in order.
/// - fails: never on the admitted domain.
/// - panics: when the two key different items at a position.
/// - executable: none — the cases compare the list it gives.
///
/// # Adequacy
/// - hypothesis: L3 — the address cases below name what an edit moved.
/// - witness: `tests::package::an_inert_edit_leaves_the_address_and_a_content_edit_moves_it_3030`
fn moved(
    before: &[(ItemKey, Option<ContentKey>)],
    after: &[(ItemKey, Option<ContentKey>)],
) -> Vec<String>
{
    assert_eq!(before.len(), after.len(), "one item per declaration");
    before
        .iter()
        .zip(after)
        .filter_map(|(&(ref key, was), &(ref again, now))| {
            assert_eq!(key, again, "the same item at each position");
            (was != now).then(|| String::from_utf8_lossy(key.as_ref()).into_owned())
        })
        .collect()
}

/// Each inert operation of `Gandr.Package`, the ones it includes from
/// `Versioned` among them, as `std.build` states it, by name.
///
/// # Specification
/// - requires: `std.build` writes each operation as `oper <name> : <type>;` on
///   one line, an `@[inert]` mark on the line before it, and each theory as
///   `pub theory <name> where {` closed by a line `}`.
/// - ensures: the operations of `Versioned`, `Presentation` and `Gandr.Package`
///   marked inert, in the order the source states them.
/// - fails: never on the admitted domain.
/// - panics: a source that cannot be read.
/// - executable: none — the fields are the source's, which the sweep reads.
///
/// # Adequacy
/// - hypothesis: L3 — the sweep edits each field this names in every corpus
///   package, so a field added to the theory is swept with no edit here.
/// - witness: `tests::package::every_corpus_package_s_address_ignores_its_inert_fields_3030`
fn inert_fields() -> Vec<String>
{
    let source = std::fs::read_to_string(
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../library/std/src/build.gandr"),
    )
    .expect("`std.build` reads");
    let mut fields = Vec::new();
    let mut theory = "";
    let mut marked = false;
    for line in source.lines().map(str::trim) {
        if let Some(named) = line
            .strip_prefix("pub theory ")
            .and_then(|rest| rest.strip_suffix(" where {"))
        {
            theory = named;
        }
        else if line == "}" {
            theory = "";
        }
        else if let Some((name, _)) = line
            .strip_prefix("oper ")
            .and_then(|rest| rest.split_once(" : "))
            && marked
            && matches!(theory, "Versioned" | "Presentation" | "Gandr.Package")
        {
            fields.push(String::from(name));
        }
        marked = line == "@[inert]" || (marked && line.starts_with("///"));
    }
    fields
}

/// How many times the sweep replaced one field's body.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
struct Replaced(usize);

/// The text of the package source at `library` with the body of each of
/// `fields` in its `Package` model replaced by another string, and how many
/// times each was replaced.
///
/// # Specification
/// - requires: the package source reads; the model opens on a line starting
///   with `pub module Package : Model(Gandr.Package)` and closes on a line `}`,
///   each component on one line as `def <name> ... = <body>;`, and each field
///   is a string.
/// - ensures: the text with each named component's body `"swept"`, and every
///   other line as it stood, beside each field's count of replacements.
/// - fails: never on the admitted domain.
/// - panics: a package source that cannot be read violates the precondition.
/// - executable: none — the sweep counts each field's replacements.
///
/// # Adequacy
/// - hypothesis: L3 — every corpus package's model is swept whole.
/// - witness: `tests::package::every_corpus_package_s_address_ignores_its_inert_fields_3030`
fn swept(
    library: &Path,
    fields: &[String],
) -> (String, BTreeMap<String, Replaced>)
{
    let stated = std::fs::read_to_string(library).expect("the library reads");
    let mut text = String::new();
    let mut counts = BTreeMap::new();
    let mut within = false;
    for line in stated.lines() {
        let trimmed = line.trim();
        let field = fields.iter().find(|name| {
            trimmed
                .strip_prefix("def ")
                .and_then(|rest| rest.strip_prefix(name.as_str()))
                .is_some_and(|rest| rest.starts_with([' ', ':']))
        });
        match (within, field, line.rsplit_once(" = ")) {
            (true, Some(name), Some((head, _))) => {
                let count: &mut Replaced = counts.entry(name.clone()).or_default();
                count.0 = count.0.saturating_add(1);
                text.push_str(head);
                text.push_str(" = \"swept\";");
            },
            _ => text.push_str(line),
        }
        text.push('\n');
        if trimmed.starts_with("pub module Package : Model(Gandr.Package)") {
            within = true;
        }
        else if trimmed == "}" {
            within = false;
        }
    }
    (text, counts)
}

/// #3030: every corpus package — the witness workspace's two members and
/// `std` — keeps its address and every item key when each inert field of its
/// model is edited to another value of its type, and a declaration added to
/// its package source moves the address.
#[test]
fn every_corpus_package_s_address_ignores_its_inert_fields_3030()
{
    let grammar = built_in().expect("the built-in grammar builds");
    let fields = inert_fields();
    assert!(
        fields.len() >= 6,
        "`Gandr.Package`'s fields are read: {fields:?}"
    );
    let tree = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let store = stored(Path::new("inert-corpus"));
    for library in [
        "corpus/model/projects/hello/package.gandr",
        "corpus/model/projects/tools/package.gandr",
        "library/std/package.gandr",
    ] {
        let library = tree
            .join(library)
            .canonicalize()
            .expect("the library exists");
        let Maybe::Present(package) = Package::discover(&library)
        else {
            panic!("`{}` roots a package", library.display());
        };
        let address = |held: &Held| {
            package
                .identity(&grammar, held, &Lock::default(), &store)
                .map(|identity| identity.address)
        };
        let before = address(&Held::default()).expect("the package addresses");
        let stated = std::fs::read_to_string(&library).expect("the library reads");
        let (edited, counts) = swept(&library, &fields);
        for field in &fields {
            assert_eq!(
                counts.get(field),
                Some(&Replaced(1)),
                "`{}` states `{field}` once",
                library.display()
            );
        }
        let held = Held(BTreeMap::from([(library.clone(), edited)]));
        assert_eq!(
            address(&held),
            Ok(before),
            "`{}`'s inert fields, swept, leave its address; the items moved: {:?}",
            library.display(),
            moved(
                &keyed(&grammar, &library, &Held::default()),
                &keyed(&grammar, &library, &held)
            )
        );
        let keys = |keyed: Vec<(ItemKey, Option<ContentKey>)>| {
            keyed.into_iter().map(|(key, _)| key).collect::<Vec<_>>()
        };
        assert_eq!(
            keys(keyed(&grammar, &library, &held)),
            keys(keyed(&grammar, &library, &Held::default())),
            "`{}`'s item keys stay",
            library.display()
        );
        let added = Held(BTreeMap::from([(
            library.clone(),
            format!(
                include_str!(
                    "package/unformatted/every-corpus-package-s-address-ignores-its-inert-fields-3030-added.gandr"
                ),
                stated = stated
            ),
        )]));
        assert_ne!(
            address(&added),
            Ok(before),
            "`{}`'s address moves with its content",
            library.display()
        );
    }
}

/// A package source a case writes: what it imports before `std.build`, the
/// version its `Package` model states, and what follows the model.
#[derive(Clone, Copy, Debug)]
struct Library<'text>
{
    /// The imports before `std.build`'s.
    imports: &'text str,
    /// The model's `version`.
    version: &'text str,
    /// The declarations after the model.
    rest: &'text str,
}

impl Library<'_>
{
    /// The package source's text.
    ///
    /// # Specification
    /// trivial.
    fn source(self) -> String
    {
        let Self {
            imports,
            version,
            rest,
        } = self;
        format!(
            "{imports}{STD_PACKAGE}pub module Package : Model(Gandr.Package) where {{\n  def name : \
             String = \"p\";\n  def version = \"{version}\";\n  def authors = \"Ada\";\n  def \
             licence = \"MIT\";\n  def documentation = \"d\";\n  def endpoint = \"e\";\n  def \
             gandr = \"\";\n  def features = \"\";\n  def systems = \"\";\n  def spelling = \
             \"\";\n  def sources = \"src\";\n}}\n{rest}"
        )
    }
}

/// The package `hello` a case writes: its version and the greeting its
/// `welcome` exports.
#[derive(Clone, Copy, Debug)]
struct Hello
{
    /// The model's `version`.
    version: &'static str,
    /// What `welcome` is.
    welcome: &'static str,
}

/// A scratch directory named for `test` holding the package `hello` as
/// `written`, and the package `sibling` importing it by the coordinate
/// `path:../hello` from two sources, each reading `welcome` through its own
/// alias.
///
/// # Specification
/// trivial.
fn siblings(
    test: &Path,
    written: Hello,
) -> PathBuf
{
    let directory = scratch(test, &[
        Path::new("hello/package.gandr"),
        Path::new("sibling/package.gandr"),
        Path::new("sibling/src/again.gandr"),
    ]);
    write_hello(&directory, written);
    std::fs::write(
        directory.join("sibling/package.gandr"),
        Library {
            imports: "import \"path:../hello\" as hello;\n",
            version: "0.1.0",
            rest: "pub def greeting = hello.welcome;\n",
        }
        .source(),
    )
    .expect("the sibling is written");
    std::fs::write(
        directory.join("sibling/src/again.gandr"),
        "import \"path:../hello\" as hi;\npub def again = hi.welcome;\n",
    )
    .expect("the sibling's second source is written");
    directory
}

/// Write `hello`'s package source under `directory` as `written`.
///
/// # Specification
/// trivial.
fn write_hello(
    directory: &Path,
    written: Hello,
)
{
    let rest = format!("pub def welcome = \"{}\";\n", written.welcome);
    std::fs::write(
        directory.join("hello/package.gandr"),
        Library {
            imports: "",
            version: written.version,
            rest: &rest,
        }
        .source(),
    )
    .expect("hello is written");
}

/// The package rooted at `root`.
///
/// # Specification
/// trivial.
fn rooted(root: &Path) -> Package
{
    match Package::discover(root) {
        Maybe::Present(package) => package,
        Maybe::Absent(package_root::Absent::Unpackaged) => {
            panic!("`{}` roots a package", root.display())
        },
    }
}

/// #4921: the packages below a workspace share one lock, and each package has
/// its own table in it. A package below no workspace keeps its own lock. The
/// check writes the dependencies of a member as its table and reads them back
/// from it. A member that records no dependency writes nothing. It keeps the
/// table of the other member. A table that records a different lock is drift.
/// When a relock removes the last table, it removes the file. The model of
/// the workspace gives the manifest beside it. A model that does not define a
/// toolchain field gives no manifest.
#[test]
fn a_workspace_s_packages_share_one_lock_4921()
{
    let grammar = built_in().expect("the built-in grammar builds");
    let directory = siblings(Path::new("shared-lock"), Hello {
        version: "0.1.0",
        welcome: "hello",
    });
    let sibling = rooted(&directory.join("sibling"));
    let hello = rooted(&directory.join("hello"));
    assert_eq!(
        sibling.lock(),
        sibling.root().join(LOCK),
        "a package below no workspace keeps its own lock"
    );
    let stated = |toolchain: &str| {
        format!(
            "import std.build (Gandr);\nimport std.list (List);\npub module Workspace : \
             Model(Gandr.Workspace) where {{ def version = \"0.2.0\"; {toolchain}}}\npub def members : List(String) = #[\"hello\", \
             \"sibling\"];\n"
        )
    };
    std::fs::write(
        directory.join("workspace.gandr"),
        stated("def gandr = \">= 0.0\"; def features = \"\"; def systems = \"\"; "),
    )
    .expect("the workspace is written");
    let shared = directory
        .canonicalize()
        .expect("the scratch directory resolves")
        .join(WORKSPACE_LOCK);
    assert_eq!(
        (sibling.lock(), hello.lock()),
        (shared.clone(), shared.clone()),
        "both packages below the workspace keep their lock in its one file"
    );
    let mut store = stored(Path::new("shared-lock"));
    let lock = sibling
        .resolve(&grammar, &mut store, Revisions::Locked)
        .expect("the dependencies resolve");
    let coordinate = Coordinate::Path(String::from("../hello"));
    assert!(
        matches!(
            reconcile_lock(&hello, &Lock::default()),
            Ok(Reconciled::Unchanged)
        ) && !shared.exists(),
        "a member recording no dependency writes nothing"
    );
    assert!(
        matches!(reconcile_lock(&sibling, &lock), Ok(Reconciled::Written)),
        "the member's table is written"
    );
    let read = || std::fs::read_to_string(&shared).ok();
    let written = read().expect("the shared lock reads");
    assert!(
        written.contains("\n\n[dependencies.\"sibling\"]\n\"path:../hello\" = { pointer = \""),
        "the table is keyed by the member's path from the workspace: {written}"
    );
    assert!(
        matches!(Lock::read(&sibling), Maybe::Present(ref table) if *table == lock),
        "the member's table reads back as its lock"
    );
    assert!(
        matches!(Lock::read(&hello), Maybe::Absent(_)),
        "a member with no table reads no lock"
    );
    assert!(
        matches!(reconcile_lock(&sibling, &lock), Ok(Reconciled::Unchanged))
            && matches!(
                reconcile_lock(&hello, &Lock::default()),
                Ok(Reconciled::Unchanged)
            )
            && matches!(relock(&hello, &Lock::default()), Ok(Reconciled::Unchanged))
            && read().as_ref() == Some(&written),
        "a second run, and another member's check and relock, leave the table byte for byte"
    );
    let drifted = reconcile_lock(&sibling, &Lock::default());
    assert!(
        matches!(drifted, Err(LockFault::Drifted(ref coordinates)) if *coordinates == [coordinate])
            && read().as_ref() == Some(&written),
        "a table recording another lock is drift at `path:../hello`, left as it stands: {drifted:?}"
    );
    assert!(
        matches!(
            relock(&sibling, &Lock::default()),
            Ok(Reconciled::Rewritten)
        ) && !shared.exists(),
        "relocking the last table away removes the file"
    );
    let Maybe::Present(workspace) = Workspace::discover(&directory)
    else {
        panic!("the scratch directory is a workspace");
    };
    let (members, gathered) = workspace
        .members()
        .expect("the workspace names its members");
    assert_eq!(
        members.iter().map(Package::root).collect::<Vec<_>>(),
        [hello.root(), sibling.root()],
        "the members are read in order"
    );
    let rendered = gathered
        .manifest
        .map(|manifest| manifest.render())
        .expect("the model states a manifest");
    assert_eq!(
        rendered.split_once("\n\n").map(|(_, body)| body),
        Some(
            "[workspace]\nversion = \"0.2.0\"\nmembers = [\n  \"hello\",\n  \"sibling\",\n]\n\n[toolchain]\ngandr = \">= 0.0\"\nfeatures = []\nsystems = []\n"
        ),
        "the manifest records the model's version, its members and its toolchain"
    );
    std::fs::write(directory.join("workspace.gandr"), stated("")).expect("the model is cut");
    let (_members, gathered) = workspace.members().expect("the workspace still names them");
    assert!(
        matches!(
            gathered.manifest,
            Err(Unstated::Unstrung {
                field: "Workspace.gandr",
                ..
            })
        ),
        "a model defining no `gandr` gives no manifest, the field run to no string: {:?}",
        gathered.manifest
    );
}

/// #3072, #3157, #4527: the coordinate two sources of a package import is
/// collected once before its lock is written, the use through the alias alone
/// refused; the lock records the coordinate and the pointer its identity
/// commits to, is written once, read back equal and unchanged on a second run,
/// and is the same bytes resolved from another directory into another store;
/// with it, the use reads the dependency.
#[test]
fn a_lock_is_written_once_and_reads_alike_from_anywhere_3072()
{
    let grammar = built_in().expect("the built-in grammar builds");
    let directory = siblings(Path::new("lock"), Hello {
        version: "0.1.0",
        welcome: "hello",
    });
    let sibling = rooted(&directory.join("sibling"));
    let hello = rooted(&directory.join("hello"));
    let coordinate = Coordinate::Path(String::from("../hello"));
    assert_eq!(
        sibling.dependencies(&grammar),
        Ok(BTreeSet::from([coordinate.clone()])),
        "the coordinate both sources import is collected once, before any lock stands"
    );
    let mut store = stored(Path::new("lock"));
    let unlocked = sibling.identity(&grammar, &Held::default(), &Lock::default(), &store);
    assert!(
        matches!(unlocked, Err(Unaddressed::Refused { ref item, .. }) if item == "greeting"),
        "with no lock, the use through the alias is refused, and only it: {unlocked:?}"
    );
    let lock = sibling
        .resolve(&grammar, &mut store, Revisions::Locked)
        .expect("the dependencies resolve");
    let own = hello
        .identity(&grammar, &Held::default(), &Lock::default(), &store)
        .expect("hello addresses");
    let pointer = store.commit(&own).expect("hello's identity commits");
    assert_eq!(
        lock.coordinates().collect::<Vec<_>>(),
        [&coordinate],
        "the lock records hello's coordinate once"
    );
    assert_eq!(
        lock.locked(&coordinate),
        Some(pointer),
        "at the pointer its identity commits to"
    );
    assert_eq!(
        store.deref::<Identity>(pointer),
        Ok(own),
        "and the pointer reads back as hello's identity"
    );
    assert!(
        matches!(
            reconcile(&sibling.root().join(LOCK), &lock),
            Ok(Reconciled::Written)
        ),
        "an absent lock is written"
    );
    let written =
        std::fs::read_to_string(directory.join("sibling").join(LOCK)).expect("the lock reads");
    assert!(
        matches!(Lock::read(&sibling), Maybe::Present(ref read) if *read == lock),
        "the lock reads back as it was written"
    );
    assert_eq!(
        sibling
            .resolve(&grammar, &mut store, Revisions::Locked)
            .as_ref(),
        Ok(&lock),
        "a second resolution is the same lock"
    );
    assert!(
        matches!(
            reconcile(&sibling.root().join(LOCK), &lock),
            Ok(Reconciled::Unchanged)
        ),
        "a second run writes nothing"
    );
    assert_eq!(
        std::fs::read_to_string(directory.join("sibling").join(LOCK)).ok(),
        Some(written.clone()),
        "the lock stands byte for byte"
    );
    let locked = sibling
        .identity(&grammar, &Held::default(), &lock, &store)
        .expect("with the lock, the use reads `hello.welcome`");
    let elsewhere = siblings(Path::new("lock-elsewhere"), Hello {
        version: "0.1.0",
        welcome: "hello",
    });
    let other = rooted(&elsewhere.join("sibling"));
    let mut fresh = stored(Path::new("lock-elsewhere"));
    let relocked = other
        .resolve(&grammar, &mut fresh, Revisions::Locked)
        .expect("the copy resolves");
    assert_eq!(
        relocked.render(),
        written,
        "the lock is the same bytes resolved from another directory into another store"
    );
    assert!(
        matches!(
            reconcile(&other.root().join(LOCK), &relocked),
            Ok(Reconciled::Written)
        ),
        "the copy's lock is written"
    );
    assert_eq!(
        other
            .identity(&grammar, &Held::default(), &relocked, &fresh)
            .map(|identity| identity.address),
        Ok(locked.address),
        "the dependent's address is the same from another directory"
    );
    for scratch in [directory, elsewhere] {
        std::fs::remove_dir_all(&scratch).expect("the scratch directory is removed");
    }
    for scratch in [store.root(), fresh.root()] {
        std::fs::remove_dir_all(scratch).expect("the store is removed");
    }
}

/// #4715: a module path whose head is the alias a coordinate import binds
/// names the dependency's module, qualified and by a listed name, refused as
/// unlocked until the lock records the coordinate and read once it does; the
/// lock records the coordinate alone, and a head that is neither the alias nor
/// a source of the package stays refused.
#[test]
fn a_module_path_through_a_coordinate_s_alias_reads_the_dependency_s_module_4715()
{
    let grammar = built_in().expect("the built-in grammar builds");
    let directory = scratch(Path::new("aliased-path"), &[
        Path::new("hello/package.gandr"),
        Path::new("hello/src/text/greet.gandr"),
        Path::new("sibling/package.gandr"),
        Path::new("stray/package.gandr"),
    ]);
    write_hello(&directory, Hello {
        version: "0.1.0",
        welcome: "hello",
    });
    std::fs::write(
        directory.join("hello/src/text/greet.gandr"),
        "pub def greeting = \"hi\";\n",
    )
    .expect("hello's module is written");
    for (package, imports, rest) in [
        (
            "sibling",
            "import \"path:../hello\" as hello;\nimport hello.text.greet (greeting);\n",
            "pub def listed = greeting;\npub def qualified = hello.text.greet.greeting;\n",
        ),
        (
            "stray",
            "import \"path:../hello\" as hello;\nimport nowhere.text.greet;\n",
            "pub def stray = nowhere.text.greet.greeting;\n",
        ),
    ] {
        std::fs::write(
            directory.join(package).join("package.gandr"),
            Library {
                imports,
                version: "0.1.0",
                rest,
            }
            .source(),
        )
        .expect("the dependent is written");
    }
    let sibling = rooted(&directory.join("sibling"));
    let coordinate = Coordinate::Path(String::from("../hello"));
    let mut store = stored(Path::new("aliased-path"));
    let unlocked = sibling.identity(&grammar, &Held::default(), &Lock::default(), &store);
    assert!(
        matches!(unlocked, Err(Unaddressed::Refused { .. })),
        "with no lock, the module path through the alias is refused: {unlocked:?}"
    );
    let lock = sibling
        .resolve(&grammar, &mut store, Revisions::Locked)
        .expect("the dependencies resolve");
    assert_eq!(
        lock.coordinates().collect::<Vec<_>>(),
        [&coordinate],
        "the lock records the coordinate alone, the module path adding no entry"
    );
    assert!(
        matches!(
            reconcile(&sibling.root().join(LOCK), &lock),
            Ok(Reconciled::Written)
        ),
        "the lock is written"
    );
    let locked = sibling.identity(&grammar, &Held::default(), &lock, &store);
    assert!(
        locked.is_ok(),
        "with the lock, the listed name and the qualified path read hello's module: {locked:?}"
    );
    let stray = rooted(&directory.join("stray"));
    let lock = stray
        .resolve(&grammar, &mut store, Revisions::Locked)
        .expect("the stray's dependencies resolve");
    let _written = reconcile(&stray.root().join(LOCK), &lock).expect("the stray's lock is written");
    let refused = stray.identity(&grammar, &Held::default(), &lock, &store);
    assert!(
        matches!(refused, Err(Unaddressed::Refused { ref item, .. }) if item == "stray"),
        "a head that is neither the alias nor a source stays refused: {refused:?}"
    );
    std::fs::remove_dir_all(&directory).expect("the scratch directory is removed");
    std::fs::remove_dir_all(store.root()).expect("the store is removed");
}

/// #3072: an inert edit to a dependency leaves its dependent's lock; a
/// content edit moves the dependency's address, and the standing lock is
/// refused as `LockDrift.path:../hello`, left byte for byte, until `relock`
/// writes it again; a hand edit to the lock is refused as drift.
#[test]
fn a_dependency_s_content_edit_drifts_the_lock_until_relocked_3072()
{
    let grammar = built_in().expect("the built-in grammar builds");
    let directory = siblings(Path::new("drift"), Hello {
        version: "0.1.0",
        welcome: "hello",
    });
    let sibling = rooted(&directory.join("sibling"));
    let path = directory.join("sibling").join(LOCK);
    let mut store = stored(Path::new("drift"));
    let lock = sibling
        .resolve(&grammar, &mut store, Revisions::Locked)
        .expect("the dependencies resolve");
    assert!(
        matches!(
            reconcile(&sibling.root().join(LOCK), &lock),
            Ok(Reconciled::Written)
        ),
        "the lock is written"
    );
    let standing = std::fs::read_to_string(&path).expect("the lock reads");
    write_hello(&directory, Hello {
        version: "0.2.0",
        welcome: "hello",
    });
    assert!(
        matches!(
            reconcile(
                &sibling.root().join(LOCK),
                &sibling
                    .resolve(&grammar, &mut store, Revisions::Locked)
                    .expect("it resolves")
            ),
            Ok(Reconciled::Unchanged)
        ),
        "an inert edit to the dependency leaves the lock"
    );
    write_hello(&directory, Hello {
        version: "0.2.0",
        welcome: "howdy",
    });
    let moved = sibling
        .resolve(&grammar, &mut store, Revisions::Locked)
        .expect("it resolves");
    let coordinate = Coordinate::Path(String::from("../hello"));
    let address = |lock: &Lock| {
        lock.locked(&coordinate).map(|pointer| {
            store
                .deref::<Identity>(pointer)
                .map(|identity| identity.address)
        })
    };
    assert_ne!(
        address(&moved),
        address(&lock),
        "a content edit moves the dependency's address, and the pointer its identity commits to"
    );
    let drifted = reconcile(&sibling.root().join(LOCK), &moved);
    assert!(
        matches!(drifted, Err(LockFault::Drifted(ref coordinates)) if *coordinates == [coordinate.clone()]),
        "the standing lock is drift at `path:../hello`: {drifted:?}"
    );
    assert_eq!(
        drifted.map_err(|fault| fault.to_string()).err().as_deref(),
        Some(
            "LockDrift.path:../hello: the lock records another dependency than it resolves to, so \
             it is left as it stands; relock with `gandr lock`"
        ),
        "the drift names its coordinate"
    );
    assert_eq!(
        std::fs::read_to_string(&path).ok(),
        Some(standing),
        "a drifted lock is left byte for byte"
    );
    assert!(
        matches!(relock(&sibling, &moved), Ok(Reconciled::Rewritten)),
        "relocking rewrites it"
    );
    assert!(
        matches!(
            reconcile(&sibling.root().join(LOCK), &moved),
            Ok(Reconciled::Unchanged)
        ),
        "the relocked lock holds"
    );
    let mut edited = std::fs::read_to_string(&path).expect("the lock reads");
    edited.push_str("# by hand\n");
    std::fs::write(&path, edited).expect("the lock is edited");
    assert!(
        matches!(
            reconcile(&sibling.root().join(LOCK), &moved),
            Err(LockFault::Edited)
        ),
        "a hand edit is refused"
    );
    std::fs::remove_dir_all(&directory).expect("the scratch directory is removed");
    std::fs::remove_dir_all(store.root()).expect("the store is removed");
}

/// #3157: the lock records a pointer into the store its run committed to;
/// read against a store that never held it, the dependent's address is
/// refused by the dependency's coordinate, naming the pointer the store
/// cannot answer, and a run that commits again answers it.
#[test]
fn a_pointer_the_store_cannot_answer_leaves_the_dependent_unaddressed_3157()
{
    let grammar = built_in().expect("the built-in grammar builds");
    let directory = siblings(Path::new("unstored"), Hello {
        version: "0.1.0",
        welcome: "hello",
    });
    let sibling = rooted(&directory.join("sibling"));
    let mut committed = stored(Path::new("unstored"));
    let lock = sibling
        .resolve(&grammar, &mut committed, Revisions::Locked)
        .expect("the dependencies resolve");
    assert!(
        matches!(
            reconcile(&sibling.root().join(LOCK), &lock),
            Ok(Reconciled::Written)
        ),
        "the lock is written, so the use through the alias reads it"
    );
    let coordinate = Coordinate::Path(String::from("../hello"));
    let pointer = lock.locked(&coordinate).expect("hello is locked");
    let mut empty = stored(Path::new("unstored-empty"));
    let unaddressed = sibling.identity(&grammar, &Held::default(), &lock, &empty);
    assert_eq!(
        unaddressed,
        Err(Unaddressed::Unstored {
            coordinate,
            fault: Box::new(StoreError::Value(ValueError::UnknownChunk {
                digest: pointer.digest()
            })),
        }),
        "a store that never held the pointer leaves the dependent unaddressed by the coordinate"
    );
    assert!(
        unaddressed
            .map_err(|fault| fault.to_string())
            .err()
            .is_some_and(|said| said.starts_with(
                "the dependency `path:../hello` is locked to a pointer the store cannot read back"
            )),
        "the refusal names the dependency"
    );
    assert_eq!(
        sibling
            .resolve(&grammar, &mut empty, Revisions::Locked)
            .as_ref(),
        Ok(&lock),
        "resolving into the empty store commits the same pointer"
    );
    assert_eq!(
        sibling
            .identity(&grammar, &Held::default(), &lock, &empty)
            .map(|identity| identity.address),
        sibling
            .identity(&grammar, &Held::default(), &lock, &committed)
            .map(|identity| identity.address),
        "and the Path.step(store, answers) it alike"
    );
    std::fs::remove_dir_all(&directory).expect("the scratch directory is removed");
    for scratch in [committed.root(), empty.root()] {
        std::fs::remove_dir_all(scratch).expect("the store is removed");
    }
}

/// #3072: two packages importing each other by coordinate are refused as a
/// `DependencyCycle`, naming the chain of roots from the one resolved back to
/// it.
#[test]
fn a_dependency_cycle_is_refused_by_its_paths_3072()
{
    let grammar = built_in().expect("the built-in grammar builds");
    let directory = scratch(Path::new("cycle"), &[
        Path::new("a/package.gandr"),
        Path::new("b/package.gandr"),
    ]);
    for (from, to) in [("a", "b"), ("b", "a")] {
        std::fs::write(
            directory.join(from).join("package.gandr"),
            format!("import \"path:../{to}\" as {to};\n{STD_PACKAGE}"),
        )
        .expect("the library is written");
    }
    let resolved = rooted(&directory.join("a")).resolve(
        &grammar,
        &mut stored(Path::new("cycle")),
        Revisions::Locked,
    );
    assert_eq!(
        resolved,
        Err(Unresolved::Cycle {
            chain: Vec::from([
                directory.join("a"),
                directory.join("b"),
                directory.join("a")
            ]),
        }),
        "the cycle is refused by its paths"
    );
    assert!(
        resolved
            .err()
            .is_some_and(|unresolved| unresolved.to_string().starts_with("DependencyCycle: ")),
        "the refusal is named"
    );
    std::fs::remove_dir_all(&directory).expect("the scratch directory is removed");
}

/// The export a walk of `sources` under `root` builds, each settled source's
/// artifact passed through `alter` before the export takes it, beside the
/// artifact each source was admitted with, by its path from `root`.
///
/// # Specification
/// trivial.
fn exported_walk(
    root: &Path,
    sources: &Path,
    alter: &dyn Fn(&Path, EncodedArtifact) -> EncodedArtifact,
) -> (
    Result<Export, Unexported>,
    BTreeMap<PathBuf, EncodedArtifact>,
)
{
    let mut exporting = Exporting::default();
    let mut admitted = BTreeMap::new();
    let ControlFlow::Continue(_report) = Walk::new(vec![sources.to_path_buf()]).visit(
        &Pool::new(Width::SERIAL),
        |mut step| -> ControlFlow<Infallible> {
            let (Step::Source { path, .. } | Step::Fault { path, .. }) = step;
            let from = path
                .canonicalize()
                .expect("the source canonicalizes")
                .strip_prefix(root)
                .expect("the source is under the root")
                .to_path_buf();
            if let Step::Source {
                composed:
                    Composed::Settled {
                        kernel: Maybe::Present(ref mut kernel),
                        ..
                    },
                ..
            } = step
            {
                let _first = admitted.insert(from.clone(), kernel.clone());
                *kernel = alter(&from, core::mem::take(kernel));
            }
            exporting.take(&from, &step);
            ControlFlow::Continue(())
        },
    );
    (exporting.finish(), admitted)
}

/// `kernel`, unaltered.
///
/// # Specification
/// trivial.
fn kept(
    _source: &Path,
    kernel: EncodedArtifact,
) -> EncodedArtifact
{
    kernel
}

/// `kernel` with its last declaration, a definition, rewritten after
/// admission to a definition at the same type whose body is a variable no
/// binder holds.
///
/// # Specification
/// trivial.
fn unbound(kernel: &EncodedArtifact) -> EncodedArtifact
{
    let (mut arena, mut declarations) = gandr_kernel_term::decode(kernel.as_image())
        .expect("the artifact decodes")
        .into_parts();
    let Some(&DeclarationContent::Def { declared, .. }) =
        declarations.last().map(|last| last.declaration().content())
    else {
        panic!("the artifact ends with a definition");
    };
    let body = arena.value_variable(DeBruijnIndex::from(0_u32));
    let rewritten =
        DeclarationBuilder::new(&mut arena).def(LevelSignature::monomorphic(), declared, body);
    if let Some(last) = declarations.last_mut() {
        *last = MarkedDeclaration::new(AdmissionMark::Checked, rewritten);
    }
    gandr_kernel_term::encode(&arena, &declarations)
}

/// #3225: a package's export holds each artifact its walk admitted, filed
/// under each source it was admitted for, and committed under the package's
/// address its root names it, the same pointer a second commit names, and
/// reads back byte for byte: two sources one import joins read back one
/// artifact, which the kernel decodes, and a third reads back its own; a path
/// the package does not hold reads back none; and a package with an unsettled
/// source has no export, naming the source.
#[test]
fn a_package_s_export_holds_what_its_check_admitted_3225()
{
    let directory = scratch(Path::new("export"), &[]);
    for (source, text) in [
        (
            "src/package.gandr",
            "def answer : Integer ;\ndef answer = 42 ;\n",
        ),
        (
            "src/shapes/point.gandr",
            "pub data Point : Type where {\n  | Here : Point\n}\n",
        ),
        (
            "src/shapes/here.gandr",
            "import \"./point.gandr\" ;\n\ndef here : Point ;\ndef here = Here ;\n",
        ),
    ] {
        let path = directory.join(source);
        std::fs::create_dir_all(path.parent().expect("a source has a directory"))
            .expect("the source's directory is made");
        std::fs::write(&path, text).expect("the source is written");
    }
    let (export, admitted) = exported_walk(&directory, &directory.join("src"), &kept);
    let export = export.expect("every source settles");
    let mut store = stored(Path::new("export"));
    let grammar = built_in().expect("the built-in grammar builds");
    let address = rooted(&directory.join("src"))
        .identity(&grammar, &Held::default(), &Lock::default(), &store)
        .expect("the package addresses")
        .address;
    let pointer = export
        .commit(&mut store, &address)
        .expect("the export commits");
    assert_eq!(
        store.roots().root(&Export::root(&address)),
        Maybe::Present(pointer),
        "the package's address names the export"
    );
    assert_eq!(
        export.commit(&mut store, &address),
        Ok(pointer),
        "a second commit names the same pointer"
    );
    let back: Export = store.deref(pointer).expect("the export reads back");
    assert_eq!(back, export, "the export reads back whole");
    assert_eq!(admitted.len(), 3_usize, "each source was admitted");
    for (source, image) in &admitted {
        let Maybe::Present(read) = back.artifact(source)
        else {
            panic!("{} is exported", source.display());
        };
        assert_eq!(
            read.as_ref(),
            image.as_ref(),
            "{} reads back the artifact it was admitted with",
            source.display()
        );
        assert!(
            gandr_kernel_term::decode(read.as_image()).is_ok(),
            "the kernel decodes {}'s artifact",
            source.display()
        );
    }
    let artifact = |source: &str| match back.artifact(Path::new(source)) {
        Maybe::Present(read) => read.as_ref().to_vec(),
        Maybe::Absent(absent) => panic!("{source}: {absent:?}"),
    };
    assert_eq!(
        artifact("src/shapes/point.gandr"),
        artifact("src/shapes/here.gandr"),
        "the sources an import joins share one artifact"
    );
    assert_ne!(
        artifact("src/package.gandr"),
        artifact("src/shapes/here.gandr"),
        "a source joined to none has its own"
    );
    assert_eq!(
        back.artifact(Path::new("src/shapes/absent.gandr")),
        Maybe::Absent(exported_source::Absent::Unexported),
        "a path the package does not hold reads back none"
    );
    std::fs::write(
        directory.join("src/shapes/here.gandr"),
        "def here = missing ;\n",
    )
    .expect("the source is rewritten");
    assert_eq!(
        exported_walk(&directory, &directory.join("src"), &kept).0,
        Err(Unexported::Unsettled {
            source: PathBuf::from("src/shapes/here.gandr")
        }),
        "a package with an unsettled source has no export"
    );
    std::fs::remove_dir_all(&directory).expect("the scratch directory is removed");
}

/// #3285: a package's export, read back by its address's root, re-admits
/// through the kernel every declaration its walk admitted, each artifact once
/// and alone; an export holding an artifact whose last declaration was
/// rewritten after admission is refused at that declaration, by the source the
/// artifact was admitted for.
#[test]
fn a_dependency_s_export_is_re_admitted_through_the_kernel_3285()
{
    let directory = scratch(Path::new("readmit"), &[]);
    for (source, text) in [
        (
            "src/package.gandr",
            "def answer : Integer ;\ndef answer = 42 ;\n",
        ),
        (
            "src/shapes/point.gandr",
            "pub data Point : Type where {\n  | Here : Point\n}\n",
        ),
        (
            "src/shapes/here.gandr",
            "import \"./point.gandr\" ;\n\ndef here : Point ;\ndef here = Here ;\n",
        ),
    ] {
        let path = directory.join(source);
        std::fs::create_dir_all(path.parent().expect("a source has a directory"))
            .expect("the source's directory is made");
        std::fs::write(&path, text).expect("the source is written");
    }
    let (export, admitted) = exported_walk(&directory, &directory.join("src"), &kept);
    let export = export.expect("every source settles");
    let mut store = stored(Path::new("readmit"));
    let grammar = built_in().expect("the built-in grammar builds");
    let address = rooted(&directory.join("src"))
        .identity(&grammar, &Held::default(), &Lock::default(), &store)
        .expect("the package addresses")
        .address;
    let _pointer = export
        .commit(&mut store, &address)
        .expect("the export commits");
    let Maybe::Present(pointer) = store.roots().root(&Export::root(&address))
    else {
        panic!("the address's root names the export");
    };
    let back: Export = store.deref(pointer).expect("the export reads back");
    let mut seen = BTreeSet::new();
    let declarations = admitted
        .values()
        .filter(|image| seen.insert(image.as_ref().to_vec()))
        .fold(0_usize, |count, image| {
            count.saturating_add(
                gandr_kernel_term::decode(image.as_image())
                    .expect("the admitted artifact decodes")
                    .declarations()
                    .len(),
            )
        });
    assert_eq!(
        seen.len(),
        2_usize,
        "two artifacts: one alone, one an import joins"
    );
    assert_eq!(
        back.readmit(),
        Ok(DeclarationCount::from(declarations)),
        "the kernel re-admits every declaration of each artifact, once"
    );
    let library = Path::new("src/package.gandr");
    let (tampered, _admitted) =
        exported_walk(&directory, &directory.join("src"), &|source, kernel| {
            if source == library {
                unbound(&kernel)
            }
            else {
                kernel
            }
        });
    let rewritten = gandr_kernel_term::decode(
        admitted
            .get(library)
            .expect("the library was admitted")
            .as_image(),
    )
    .expect("the library's artifact decodes")
    .declarations()
    .len()
    .checked_sub(1_usize)
    .expect("the library's artifact holds a declaration");
    let Err(Unreadmitted::Refused {
        ref source,
        ref refusal,
    }) = tampered
        .expect("the rewritten artifact still cuts")
        .readmit()
    else {
        panic!("the rewritten declaration is refused by the kernel's replay");
    };
    assert_eq!(source, "src/package.gandr", "the refusal names the source");
    assert_eq!(
        usize::from(refusal.position()),
        rewritten,
        "the replay stops at the rewritten declaration"
    );
    std::fs::remove_dir_all(&directory).expect("the scratch directory is removed");
}

/// What `git` writes to standard output run with `arguments` in `directory`,
/// as a test's own commits are made: unsigned, by a fixed author.
///
/// # Specification
/// trivial.
fn git<Argument>(
    directory: &Path,
    arguments: &[Argument],
) -> String
where
    Argument: AsRef<std::ffi::OsStr> + core::fmt::Debug,
{
    let output = std::process::Command::new("git")
        .arg("-C")
        .arg(directory)
        .args([
            "-c",
            "commit.gpgsign=false",
            "-c",
            "user.name=gandr",
            "-c",
            "user.email=gandr@invalid",
        ])
        .args(arguments)
        .output()
        .expect("git runs");
    assert!(
        output.status.success(),
        "git {arguments:?}: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8_lossy(&output.stdout).trim().to_owned()
}

/// Commit `hello` as `written` in its working repository under `directory`,
/// push it to the remote's `acme-org/hello` and answer the revision.
///
/// # Specification
/// trivial.
fn published(
    directory: &Path,
    written: Hello,
) -> String
{
    write_hello(directory, written);
    let hello = directory.join("hello");
    let _added = git(&hello, &["add", "--all"]);
    let _committed = git(&hello, &["commit", "--quiet", "--message", written.welcome]);
    let _pushed = git(&hello, &["push", "--quiet", "remote", "HEAD:main"]);
    git(&hello, &["rev-parse", "HEAD"])
}

/// #4714: a `gh:` coordinate reads back as it is written, and a name that
/// would climb out of its checkout, a third segment or a short revision reads
/// as none.
#[test]
fn a_gh_coordinate_reads_back_and_refuses_a_climbing_name_4714()
{
    use gandr_surface_dispatcher::Repository;
    use gandr_surface_dispatcher::Revision;
    use gandr_surface_dispatcher::Written;

    let read = |written: &str| Repository::written(Written(written)).map(|read| read.to_string());
    assert_eq!(
        read("acme-org/rope.gandr"),
        Some(String::from("acme-org/rope.gandr")),
        "an owner and a name read back"
    );
    for climbing in [
        "acme-org/..",
        "acme-org/.",
        "../rope",
        "acme-org/rope/src",
        "acme/",
        "",
    ] {
        assert_eq!(read(climbing), None, "`{climbing}` names no repository");
    }
    let spelled = "0123456789abcdef0123456789abcdef01234567";
    assert_eq!(
        Revision::opening(Written(spelled)).map(|(revision, rest)| (revision.to_string(), rest.0)),
        Some((String::from(spelled), "")),
        "a revision reads back as its 40 digits"
    );
    assert!(
        Revision::opening(Written(&spelled.to_uppercase())).is_none(),
        "an uppercase revision reads as none"
    );
    assert!(
        Revision::opening(Written("0123456789abcdef0123456789abcdef0123456")).is_none(),
        "a short revision reads as none"
    );
}

/// #4714: a `gh:` coordinate no lock records is refused unrevisioned by a
/// check, and locked at the remote's `HEAD` by `gandr lock`'s resolution,
/// which fetches its checkout; the lock records the revision beside the
/// pointer and reads back. A later resolution keeps the revision as the
/// remote moves, reads the checkout standing, fetches it again once it is
/// removed, and the import reads the dependency.
#[test]
fn a_gh_coordinate_is_fetched_at_the_revision_its_lock_records_4714()
{
    use gandr_surface_dispatcher::Hydration;
    use gandr_surface_dispatcher::install_hydration;

    let grammar = built_in().expect("the built-in grammar builds");
    let directory = scratch(Path::new("gh"), &[
        Path::new("hello/package.gandr"),
        Path::new("sibling/package.gandr"),
        Path::new("remote/acme-org/hello/HEAD"),
    ]);
    let remote = directory.join("remote");
    std::fs::remove_file(remote.join("acme-org/hello/HEAD")).expect("the placeholder goes");
    let _bare = git(&remote.join("acme-org/hello"), &[
        "init",
        "--quiet",
        "--bare",
        "--initial-branch",
        "main",
    ]);
    let _working = git(&directory.join("hello"), &["init", "--quiet"]);
    let _remoted = git(&directory.join("hello"), &[
        "remote",
        "add",
        "remote",
        &remote.join("acme-org/hello").display().to_string(),
    ]);
    let first = published(&directory, Hello {
        version: "0.1.0",
        welcome: "hello",
    });
    std::fs::write(
        directory.join("sibling/package.gandr"),
        Library {
            imports: "import \"gh:acme-org/hello\" as hello;\n",
            version: "0.1.0",
            rest: "pub def greeting = hello.welcome;\n",
        }
        .source(),
    )
    .expect("the sibling is written");
    let checkouts = directory.join("checkouts");
    install_hydration(Hydration::new(
        checkouts.clone(),
        format!("file://{}", remote.display()),
    ))
    .expect("no other hydration is installed");
    let sibling = rooted(&directory.join("sibling"));
    let coordinate = Coordinate::GitHub(
        gandr_surface_dispatcher::Repository::written(gandr_surface_dispatcher::Written(
            "acme-org/hello",
        ))
        .expect("the repository reads"),
    );
    let mut store = stored(Path::new("gh"));
    assert_eq!(
        sibling.resolve(&grammar, &mut store, Revisions::Locked),
        Err(Unresolved::Unrevisioned {
            coordinate: coordinate.clone(),
            root: sibling.root().to_path_buf(),
        }),
        "a check with no lock fetches nothing"
    );
    let lock = sibling
        .resolve(&grammar, &mut store, Revisions::Asked)
        .expect("locking asks the remote's `HEAD` and fetches it");
    assert_eq!(
        lock.revision(&coordinate)
            .map(|revision| revision.to_string()),
        Some(first.clone()),
        "the lock records the revision `HEAD` named"
    );
    let checkout = checkouts.join("acme-org/hello").join(&first);
    assert!(
        checkout.join("package.gandr").is_file() && !checkout.join(".git").exists(),
        "the checkout is the tree at the revision, with no repository"
    );
    assert!(
        lock.render().contains(&format!(
            "\"gh:acme-org/hello\" = {{ revision = \"{first}\", pointer = "
        )),
        "the lock writes the revision before the pointer: {}",
        lock.render()
    );
    assert!(
        matches!(relock(&sibling, &lock), Ok(Reconciled::Written)),
        "the lock is written"
    );
    assert!(
        matches!(Lock::read(&sibling), Maybe::Present(ref read) if *read == lock),
        "the lock reads back with its revision"
    );
    let _second = published(&directory, Hello {
        version: "0.1.0",
        welcome: "hello again",
    });
    assert_eq!(
        sibling
            .resolve(&grammar, &mut store, Revisions::Asked)
            .as_ref(),
        Ok(&lock),
        "locking keeps the revision the lock records as the remote moves"
    );
    std::fs::remove_dir_all(&checkout).expect("the checkout is removed");
    assert_eq!(
        sibling
            .resolve(&grammar, &mut store, Revisions::Locked)
            .as_ref(),
        Ok(&lock),
        "a check fetches the recorded revision again"
    );
    assert!(
        checkout.join("package.gandr").is_file(),
        "the checkout stands again"
    );
    assert!(
        sibling
            .identity(&grammar, &Held::default(), &lock, &store)
            .is_ok(),
        "with the lock, the use reads `hello.welcome` from the checkout"
    );
    std::fs::remove_dir_all(&directory).expect("the scratch directory is removed");
}
