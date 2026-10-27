//! A package's discovery from any path in it, the paths a verb walks, and the
//! manifest the checker writes from the package's model (#2687).
//!
//! The package cases, in a `cfg(test)` module so the crate's lint wall reads
//! them as test code rather than as shipping code.

use std::path::Path;
use std::path::PathBuf;

use anodized::spec;
use gandr_surface_corpus::CorpusRoot;
use gandr_surface_corpus::SettleReport;
use gandr_surface_dispatcher::Composed;
use gandr_surface_dispatcher::Field;
use gandr_surface_dispatcher::LoweringCount;
use gandr_surface_dispatcher::Manifest;
use gandr_surface_dispatcher::ManifestFault;
use gandr_surface_dispatcher::Package;
use gandr_surface_dispatcher::Program;
use gandr_surface_dispatcher::Reconciled;
use gandr_surface_dispatcher::Unmanifested;
use gandr_surface_dispatcher::Unmembered;
use gandr_surface_dispatcher::Unpathed;
use gandr_surface_dispatcher::Workspace;
use gandr_surface_dispatcher::compose;
use gandr_surface_dispatcher::package_root;
use gandr_surface_dispatcher::packaged;
use gandr_surface_dispatcher::reconcile;
use gandr_surface_dispatcher::workspace_root;
use gandr_surface_grammar::built_in;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

/// A fresh scratch directory named for `test` and this process, holding each
/// of `files`, empty.
///
/// # Specification
/// - requires: `files` are relative paths; the derived directory belongs only
///   to this test for its lifetime.
/// - ensures: the canonical path of a directory, any stale one of the same name
///   removed first, in which each file of `files` has been written empty, its
///   parent directories made.
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
    let directory = std::env::temp_dir().join(format!(
        "gandr-dispatcher-package-{}-{}",
        test.display(),
        std::process::id()
    ));
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

/// The root and library of the package `from` sits in, or none.
///
/// # Specification
/// trivial.
fn found(from: &Path) -> Option<(PathBuf, PathBuf)>
{
    match Package::discover(from) {
        Maybe::Present(package) => Some((
            package.root().to_path_buf(),
            package.library().to_path_buf(),
        )),
        Maybe::Absent(package_root::Absent::Unpackaged) => None,
    }
}

/// #2687: a package is found from any path in it — a leaf deep in its
/// sources, its `src` directory, its root — at its root, the directory above
/// a library in `src`, or the library's own directory when the library is
/// not in one. An inner library is found before an outer one, and a
/// directory with no library above it is in no package.
#[test]
fn a_package_is_found_from_any_path_in_it_2687()
{
    let directory = scratch(Path::new("found"), &[
        Path::new("hello/src/lib.gandr"),
        Path::new("hello/src/text/greet/words.gandr"),
        Path::new("flat/lib.gandr"),
        Path::new("flat/inner/lib.gandr"),
        Path::new("flat/inner/deep.gandr"),
        Path::new("loose/alone.gandr"),
    ]);
    let hello = (
        directory.join("hello"),
        directory.join("hello/src/lib.gandr"),
    );
    for from in [
        "hello/src/text/greet/words.gandr",
        "hello/src/text",
        "hello/src",
        "hello/src/lib.gandr",
        "hello",
    ] {
        assert_eq!(
            found(&directory.join(from)),
            Some(hello.clone()),
            "`{from}` is in the package rooted above its `src`"
        );
    }
    assert_eq!(
        found(&directory.join("flat")),
        Some((directory.join("flat"), directory.join("flat/lib.gandr"))),
        "a library outside `src` roots its own directory"
    );
    assert_eq!(
        found(&directory.join("flat/inner/deep.gandr")),
        Some((
            directory.join("flat/inner"),
            directory.join("flat/inner/lib.gandr")
        )),
        "the nearest library is the package's"
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

/// #2687: a path inside a package walks the whole package, listed once, a
/// path outside its sources but under its root is walked beside them, a path
/// in no package is walked as given, and no path walks the package the
/// working directory is in, or is refused outside every package.
#[test]
fn a_path_in_a_package_walks_the_whole_package_2687()
{
    let directory = scratch(Path::new("walked"), &[
        Path::new("hello/src/lib.gandr"),
        Path::new("hello/src/text/greet.gandr"),
        Path::new("hello/src/text/part.gandr"),
        Path::new("hello/tests/smoke.gandr"),
        Path::new("loose/alone.gandr"),
    ]);
    let walked = |paths: &[&str], working: &str| {
        packaged(
            paths.iter().map(|path| directory.join(path)).collect(),
            &directory.join(working),
        )
        .map(|(walked, packages)| {
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
    assert_eq!(
        walked(&[], "hello/src/text"),
        Ok((
            Vec::from([directory.join("hello/src")]),
            Vec::from([hello.clone()])
        )),
        "no path walks the package the working directory is in, whole"
    );
    assert_eq!(
        walked(&[], "hello"),
        Ok((
            Vec::from([PathBuf::from("src")]),
            Vec::from([hello.clone()])
        )),
        "the sources below the working directory are listed relative to it"
    );
    assert_eq!(
        walked(&[], "hello/src"),
        Ok((Vec::from([PathBuf::from(".")]), Vec::from([hello.clone()]))),
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
                "hello/src/text/part.gandr",
                "hello/tests/smoke.gandr"
            ],
            "loose"
        ),
        Ok((
            Vec::from([
                directory.join("hello/src"),
                directory.join("loose/alone.gandr"),
                directory.join("hello/tests/smoke.gandr"),
            ]),
            Vec::from([hello]),
        )),
        "a package once, at its first path; a path in none as given; one under the root \
         beside the sources"
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
        Path::new("hello/src/lib.gandr"),
        Path::new("tools/lib.gandr"),
        Path::new("docs/notes.gandr"),
    ]);
    let source = directory.join("workspace.gandr");
    let stated = |members: &str| {
        format!(
            "pub module Workspace : Model(Gandr.Workspace) {{ def version = \"0.2.0\"; }}\n{members}\n"
        )
    };
    std::fs::write(
        &source,
        stated("pub def members : List(String) = [\"hello\", \"tools\"];"),
    )
    .expect("the workspace is written");
    for from in ["", "docs", "hello/src", "tools/lib.gandr"] {
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
        .map(|(walked, packages)| {
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
            Vec::from([source.clone(), hello.join("src"), tools.clone()]),
            Vec::from([hello.clone(), tools.clone()]),
        )),
        "no path in the workspace outside every package walks it whole, each path not below \
         the working directory as it stands"
    );
    assert_eq!(
        walked(&[&directory], "docs"),
        Ok((
            Vec::from([source.clone(), hello.join("src"), tools.clone()]),
            Vec::from([hello.clone(), tools]),
        )),
        "the workspace's directory given walks it whole"
    );
    assert_eq!(
        walked(&[], "hello"),
        Ok((Vec::from([PathBuf::from("src")]), Vec::from([hello]))),
        "no path in a member walks that member alone"
    );
    for (members, refused) in [
        (
            "pub def members : List(String) = [\"hello\", \"docs\"];",
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

/// The program `source` composes to, and the report of its declarations.
///
/// # Specification
/// - requires: `source` composes under the strict root and settles.
/// - ensures: the program and the report of the settled composition.
/// - fails: never on the admitted domain.
/// - panics: a source that does not compose, or composes refused, violates the
///   precondition.
/// - executable: none — a program is opaque to a predicate; the cases observe
///   it by running its declarations.
///
/// # Adequacy
/// - hypothesis: L3 — the manifest cases below compose real sources.
/// - witness: `tests::package::a_manifest_reads_the_package_model_2687`
fn settled_of(source: SourceText<'static>) -> (Program<'static>, SettleReport<'static>)
{
    let grammar = built_in().expect("the built-in grammar builds");
    let mut lowerings = LoweringCount::default();
    match compose(&grammar, CorpusRoot::Strict, source, &mut lowerings)
        .expect("the source composes")
    {
        Composed::Settled {
            program, report, ..
        } => (program, report),
        refused @ Composed::Refused(_) => panic!("the source settles: {refused:?}"),
    }
}

/// The manifest the `Package` model of `source` states, for a package of
/// its library alone.
///
/// # Specification
/// - requires: as [`settled_of`].
/// - ensures: [`Manifest::of`] the program `source` composes to and its report,
///   for a scratch package whose sources hold nothing but its `lib.gandr`.
/// - fails: never on the admitted domain.
/// - panics: as [`settled_of`], and as [`scratch`].
/// - executable: none — reading the manifest runs the program, which a
///   predicate could only check by running it again; the cases observe each
///   outcome.
///
/// # Adequacy
/// - hypothesis: L3 — the manifest cases below compose real sources.
/// - witness: `tests::package::a_manifest_reads_the_package_model_2687`
fn manifest_of(source: SourceText<'static>) -> Result<Manifest, Unmanifested>
{
    let directory = scratch(Path::new("alone"), &[Path::new("lib.gandr")]);
    let Maybe::Present(package) = Package::discover(&directory)
    else {
        panic!("the scratch package is found");
    };
    let (mut program, report) = settled_of(source);
    Manifest::of(&mut program, &report, &package)
}

/// #2687: a manifest reads the `Package` model's `name` and `version`, each
/// run to its string and decoded; a model missing a field, and one whose
/// field is not a string, are refused at that field.
#[test]
fn a_manifest_reads_the_package_model_2687()
{
    let read = manifest_of(SourceText::from(
        "module Package { def name = \"a \\\"quoted\\\" name\" ; def version = \"0.1.0\" ; }",
    ))
    .expect("both fields are strings");
    assert_eq!(
        read.render(),
        manifest_of(SourceText::from(
            "module Package { def name = \"a \\\"quoted\\\" name\" ; def version = \"0.1.0\" ; }"
        ))
        .expect("the same model")
        .render()
    );
    assert!(
        read.render().ends_with(
            "\n[package]\nname = \"a \\\"quoted\\\" name\"\nversion = \"0.1.0\"\nmodules = []\n"
        ),
        "the decoded name, quoted again for TOML: {}",
        read.render()
    );
    assert_eq!(
        manifest_of(SourceText::from(
            "module Package { def name = \"hello\" ; }"
        )),
        Err(Unmanifested::Undeclared(Field::Version)),
        "a missing version"
    );
    assert_eq!(
        manifest_of(SourceText::from(
            "module Package { def name = 3 ; def version = \"0.1.0\" ; }"
        )),
        Err(Unmanifested::Unstrung {
            field: Field::Name,
            came: String::from("3"),
        }),
        "a name that is no string"
    );
    assert_eq!(
        manifest_of(SourceText::from(
            "def name = \"hello\" ; def version = \"0.1.0\" ;"
        )),
        Err(Unmanifested::Undeclared(Field::Name)),
        "top-level fields are not the package's"
    );
}

/// #2687: a manifest renders its header, the digest of its body and its
/// table, the same bytes each time, an empty module list as `[]` the way the
/// tree's TOML formatter writes it, and escapes what TOML's basic strings
/// escape.
#[test]
fn a_manifest_renders_its_digest_and_its_table_2687()
{
    let rendered = manifest_of(SourceText::from(
        "module Package { def name = \"hello\" ; def version = \"0.1.0\" ; }",
    ))
    .expect("the model reads")
    .render();
    let body = "\n[package]\nname = \"hello\"\nversion = \"0.1.0\"\nmodules = []\n";
    assert_eq!(
        rendered,
        format!(
            "# Written by `gandr check` from the package's `Package` model: edit the model, not \
             this file.\n# blake3: {}\n{body}",
            blake3::hash(body.as_bytes()).to_hex()
        )
    );
    let escaped = manifest_of(SourceText::from(
        "module Package { def name = \"back\\\\slash\\nline\\ttab\" ; def version = \"1\" ; }",
    ))
    .expect("the model reads")
    .render();
    assert!(
        escaped.contains("\nname = \"back\\\\slash\\nline\\ttab\"\n"),
        "a backslash, a newline and a tab escaped: {escaped}"
    );
}

/// #2687: a manifest lists every module its package's sources make, by its
/// path, in order: a module in a directory by its directory and its stem, and
/// nothing of the root module or of a package nested inside.
#[test]
fn a_manifest_lists_the_modules_its_sources_make_2687()
{
    let directory = scratch(Path::new("modules"), &[
        Path::new("hello/src/lib.gandr"),
        Path::new("hello/src/util.gandr"),
        Path::new("hello/src/text/greet.gandr"),
        Path::new("hello/src/text/notes.md"),
        Path::new("hello/src/vendored/lib.gandr"),
        Path::new("hello/src/vendored/inner.gandr"),
    ]);
    let Maybe::Present(package) = Package::discover(&directory.join("hello"))
    else {
        panic!("the package is found");
    };
    let (mut program, report) = settled_of(SourceText::from(
        "module Package { def name = \"hello\" ; def version = \"0.1.0\" ; }",
    ));
    let rendered = Manifest::of(&mut program, &report, &package)
        .expect("the model reads")
        .render();
    assert!(
        rendered.ends_with("\nmodules = [\n  \"text.greet\",\n  \"util\",\n]\n"),
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
    let path = directory.join("gandr.toml");
    let first = manifest_of(SourceText::from(
        "module Package { def name = \"hello\" ; def version = \"0.1.0\" ; }",
    ))
    .expect("the model reads");
    let second = manifest_of(SourceText::from(
        "module Package { def name = \"hello\" ; def version = \"0.2.0\" ; }",
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
