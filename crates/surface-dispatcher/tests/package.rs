//! A package's discovery from any path in it, the paths a verb walks, and the
//! manifest the checker writes from the package's model (#2687).
//!
//! The package cases, in a `cfg(test)` module so the crate's lint wall reads
//! them as test code rather than as shipping code.

use alloc::collections::BTreeMap;
use std::path::Path;
use std::path::PathBuf;

use anodized::spec;
use gandr_core_incremental::ContentKey;
use gandr_core_incremental::ItemKey;
use gandr_core_incremental::content_keys;
use gandr_surface_corpus::CorpusRoot;
use gandr_surface_corpus::SettleReport;
use gandr_surface_dispatcher::Alias;
use gandr_surface_dispatcher::Composed;
use gandr_surface_dispatcher::Coordinate;
use gandr_surface_dispatcher::Dependency;
use gandr_surface_dispatcher::Field;
use gandr_surface_dispatcher::LOCK;
use gandr_surface_dispatcher::Lock;
use gandr_surface_dispatcher::LockFault;
use gandr_surface_dispatcher::Locked;
use gandr_surface_dispatcher::Lowered;
use gandr_surface_dispatcher::LoweringCount;
use gandr_surface_dispatcher::Manifest;
use gandr_surface_dispatcher::ManifestFault;
use gandr_surface_dispatcher::Package;
use gandr_surface_dispatcher::Program;
use gandr_surface_dispatcher::Reconciled;
use gandr_surface_dispatcher::Shadows;
use gandr_surface_dispatcher::Unaddressed;
use gandr_surface_dispatcher::Unmanifested;
use gandr_surface_dispatcher::Unmembered;
use gandr_surface_dispatcher::Unpathed;
use gandr_surface_dispatcher::Unresolved;
use gandr_surface_dispatcher::Workspace;
use gandr_surface_dispatcher::classify;
use gandr_surface_dispatcher::compose;
use gandr_surface_dispatcher::item_program;
use gandr_surface_dispatcher::lay_out_shadowed;
use gandr_surface_dispatcher::lower_source;
use gandr_surface_dispatcher::lower_unit_source;
use gandr_surface_dispatcher::package_root;
use gandr_surface_dispatcher::packaged;
use gandr_surface_dispatcher::reconcile;
use gandr_surface_dispatcher::reconcile_lock;
use gandr_surface_dispatcher::relock;
use gandr_surface_dispatcher::workspace_root;
use gandr_surface_grammar::Pbg;
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

/// The model fields every case below states beside its `name` and its
/// `version`, a string each.
macro_rules! rest {
    () => {
        "def authors = \"Ada, Grace\" ; def licence = \"MIT\" ; def documentation = \
         \"https://d.example\" ; def endpoint = \"https://e.example\" ; def gandr = \">= 0.1\" ; \
         def features = \"a, b\" ; def systems = \"\" ; def spelling = \"\" ;"
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
#[test]
fn a_manifest_reads_the_package_model_2687()
{
    let read = manifest_of(SourceText::from(concat!(
        "module Package { def name = \"a \\\"quoted\\\" name\" ; def version = \"0.1.0\" ; ",
        rest!(),
        " }"
    )))
    .expect("every field is what it states");
    assert_eq!(
        read.render(),
        manifest_of(SourceText::from(concat!(
            "module Package { def name = \"a \\\"quoted\\\" name\" ; def version = \"0.1.0\" ; ",
            rest!(),
            " }"
        )))
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
    assert_eq!(
        manifest_of(SourceText::from(concat!(
            "module Package { def name = \"hello\" ; ",
            rest!(),
            " }"
        ))),
        Err(Unmanifested::Undeclared(Field::Version)),
        "a missing version"
    );
    assert_eq!(
        manifest_of(SourceText::from(concat!(
            "module Package { def name = 3 ; def version = \"0.1.0\" ; ",
            rest!(),
            " }"
        ))),
        Err(Unmanifested::Unstrung {
            field: Field::Name,
            came: String::from("3"),
        }),
        "a name that is no string"
    );
    assert_eq!(
        manifest_of(SourceText::from(
            "module Package { def name = \"hello\" ; def version = \"0.1.0\" ; def authors = 3 ; \
             def licence = \"MIT\" ; def documentation = \"d\" ; def endpoint = \"e\" ; }"
        )),
        Err(Unmanifested::Unstrung {
            field: Field::Authors,
            came: String::from("3"),
        }),
        "authors that are no string"
    );
    assert_eq!(
        manifest_of(SourceText::from(concat!(
            "def name = \"hello\" ; def version = \"0.1.0\" ; ",
            rest!()
        ))),
        Err(Unmanifested::Undeclared(Field::Name)),
        "top-level fields are not the package's"
    );
}

/// #3072: a library's `dependencies` renders the manifest's dependency table,
/// each alias with its path, and one that runs to no list of dependencies is
/// refused with what it came to.
#[test]
fn a_manifest_renders_the_dependencies_its_library_lists_3072()
{
    let read = manifest_of(SourceText::from(concat!(
        "data Coordinate : Type { Path : (path : String) --> Coordinate; } ",
        "type Dependency = #{ alias : String, coordinate : Coordinate }; ",
        "module Package { def name = \"tools\" ; def version = \"0.1.0\" ; ",
        rest!(),
        " } def dependencies : List(Dependency) = [ #{ alias = \"hello\", coordinate = \
         Path(\"../hello\") } ] ;"
    )))
    .expect("the model and its dependencies read");
    assert!(
        read.render().ends_with(&format!(
            "modules = []\n{TOOLCHAIN}\n[dependencies]\nhello = {{ path = \"../hello\" }}\n"
        )),
        "the table follows the package's: {}",
        read.render()
    );
    assert_eq!(
        manifest_of(SourceText::from(concat!(
            "module Package { def name = \"tools\" ; def version = \"0.1.0\" ; ",
            rest!(),
            " } def dependencies = 3 ;"
        ))),
        Err(Unmanifested::Undepended {
            came: String::from("3"),
        }),
        "dependencies that are no list"
    );
}

/// #2687: a manifest renders its header, the digest of its body and its
/// table, the same bytes each time, an empty module list as `[]` the way the
/// tree's TOML formatter writes it, and escapes what TOML's basic strings
/// escape.
#[test]
fn a_manifest_renders_its_digest_and_its_table_2687()
{
    let rendered = manifest_of(SourceText::from(concat!(
        "module Package { def name = \"hello\" ; def version = \"0.1.0\" ; ",
        rest!(),
        " }"
    )))
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
    let escaped = manifest_of(SourceText::from(concat!(
        "module Package { def name = \"back\\\\slash\\nline\\ttab\" ; def version = \"1\" ; ",
        rest!(),
        " }"
    )))
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
            manifest_of(SourceText::from(concat!(
                "module Package { def name = \"p\" ; def version = \"0.1.0\" ; def authors = \
                 \"A\" ; def licence = \"MIT\" ; def documentation = \"d\" ; def endpoint = \"e\" \
                 ; def spelling = \"\" ; ",
                $toolchain,
                " }"
            )))
        };
    }
    let read = model!(
        "def gandr = \">= 0.3.1\" ; def features = \" package-lock ,, std-package \" ; def \
         systems = \"x86_64-linux\" ;"
    )
    .expect("the constraints read");
    assert!(
        read.render().ends_with(
            "modules = []\n\n[toolchain]\ngandr = \">= 0.3.1\"\nfeatures = [\n  \
             \"package-lock\",\n  \"std-package\",\n]\nsystems = [\n  \"x86_64-linux\",\n]\n"
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
    assert_eq!(
        model!("def gandr = \"\" ; def systems = \"\" ;"),
        Err(Unmanifested::Undeclared(Field::Features)),
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
            manifest_of(SourceText::from(concat!(
                "module Package { def name = \"p\" ; def version = \"0.1.0\" ; def authors = \
                 \"A\" ; def licence = \"MIT\" ; def documentation = \"d\" ; def endpoint = \"e\" \
                 ; def gandr = \">= 0.1\" ; def features = \"a, b\" ; def systems = \"\" ; def \
                 spelling = ",
                $spelling,
                " ; }"
            )))
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
    let (mut program, report) = settled_of(SourceText::from(concat!(
        "module Package { def name = \"hello\" ; def version = \"0.1.0\" ; ",
        rest!(),
        " }"
    )));
    let rendered = Manifest::of(&mut program, &report, &package)
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
    let path = directory.join("gandr.toml");
    let first = manifest_of(SourceText::from(concat!(
        "module Package { def name = \"hello\" ; def version = \"0.1.0\" ; ",
        rest!(),
        " }"
    )))
    .expect("the model reads");
    let second = manifest_of(SourceText::from(concat!(
        "module Package { def name = \"hello\" ; def version = \"0.2.0\" ; ",
        rest!(),
        " }"
    )))
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

/// The import of `std.package` by the absolute path to its source.
const STD_PACKAGE: &str = concat!(
    "import \"",
    env!("CARGO_MANIFEST_DIR"),
    "/../../library/std/src/package.gandr\";\n"
);

/// #3030, #3135: in a package of a library and one module, an edit to an
/// inert field of the model leaves the package's address and the key of every
/// item but the field's where they were; an edit to a toolchain constraint,
/// which is content, moves the address and only its own key, and so does an
/// edit to the module's item.
#[test]
fn an_inert_edit_leaves_the_address_and_a_content_edit_moves_it_3030()
{
    let directory = scratch(Path::new("address"), &[
        Path::new("hello/src/lib.gandr"),
        Path::new("hello/src/text/greet.gandr"),
    ]);
    let library = directory.join("hello/src/lib.gandr");
    let leaf = directory.join("hello/src/text/greet.gandr");
    let stated = |name: &str, gandr: &str| {
        format!(
            "import text.greet (greeting);\n{STD_PACKAGE}pub module Package : \
             Model(Gandr.Package) {{\n  def name : String = \"{name}\";\n  def version = \
             \"0.1.0\";\n  def authors = \"Ada\";\n  def licence = \"MIT\";\n  def documentation \
             = \"d\";\n  def endpoint = \"e\";\n  def gandr = \"{gandr}\";\n  def features = \
             \"\";\n  def systems = \"\";\n  def spelling = \"\";\n}}\npub def welcome = greeting;\n"
        )
    };
    std::fs::write(&library, stated("hello", ">= 0.0")).expect("the library is written");
    std::fs::write(&leaf, "pub def greeting = \"hello, world\";\n").expect("the leaf is written");
    let Maybe::Present(package) = Package::discover(&library)
    else {
        panic!("the package is found");
    };
    let grammar = built_in().expect("the built-in grammar builds");
    let address = |held: &Held| {
        package
            .identity(&grammar, held, &Lock::default())
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
/// `Versioned` among them, as `std.package` states it, by name.
///
/// # Specification
/// - requires: `std.package` writes each operation as `oper <name> : <type>;`
///   on one line, an `@[ inert ]` mark on the line before it, and each theory
///   as `pub theory <name> {` closed by a line `}`.
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
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../library/std/src/package.gandr"),
    )
    .expect("`std.package` reads");
    let mut fields = Vec::new();
    let mut theory = "";
    let mut marked = false;
    for line in source.lines().map(str::trim) {
        if let Some(named) = line
            .strip_prefix("pub theory ")
            .and_then(|rest| rest.strip_suffix(" {"))
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
        marked = line == "@[ inert ]" || (marked && line.starts_with("///"));
    }
    fields
}

/// How many times the sweep replaced one field's body.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
struct Replaced(usize);

/// The text of the library at `library` with the body of each of `fields` in
/// its `Package` model replaced by another string, and how many times each
/// was replaced.
///
/// # Specification
/// - requires: the library reads; the model opens on a line starting with `pub
///   module Package : Model(Gandr.Package)` and closes on a line `}`, each
///   component on one line as `def <name> ... = <body>;`, and each field is a
///   string.
/// - ensures: the text with each named component's body `"swept"`, and every
///   other line as it stood, beside each field's count of replacements.
/// - fails: never on the admitted domain.
/// - panics: a library that cannot be read violates the precondition.
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
/// its library moves the address.
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
    for library in [
        "corpus/model/projects/hello/src/lib.gandr",
        "corpus/model/projects/tools/lib.gandr",
        "library/std/src/lib.gandr",
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
                .identity(&grammar, held, &Lock::default())
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
            format!("{stated}\n/// A declaration the sweep adds.\npub def swept = 1;\n"),
        )]));
        assert_ne!(
            address(&added),
            Ok(before),
            "`{}`'s address moves with its content",
            library.display()
        );
    }
}

/// A library a case writes: what it imports before `std.package`, the
/// version its `Package` model states, and what follows the model.
#[derive(Clone, Copy, Debug)]
struct Library<'text>
{
    /// The imports before `std.package`'s.
    imports: &'text str,
    /// The model's `version`.
    version: &'text str,
    /// The declarations after the model.
    rest: &'text str,
}

impl Library<'_>
{
    /// The library's source.
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
            "{imports}{STD_PACKAGE}pub module Package : Model(Gandr.Package) {{\n  def name : \
             String = \"p\";\n  def version = \"{version}\";\n  def authors = \"Ada\";\n  def \
             licence = \"MIT\";\n  def documentation = \"d\";\n  def endpoint = \"e\";\n  def \
             gandr = \"\";\n  def features = \"\";\n  def systems = \"\";\n  def spelling = \
             \"\";\n}}\n{rest}"
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
/// `written`, and the package `sibling` depending on it by the path
/// `../hello` and reading `hello.welcome`.
///
/// # Specification
/// trivial.
fn siblings(
    test: &Path,
    written: Hello,
) -> PathBuf
{
    let directory = scratch(test, &[
        Path::new("hello/src/lib.gandr"),
        Path::new("sibling/src/lib.gandr"),
    ]);
    write_hello(&directory, written);
    std::fs::write(
        directory.join("sibling/src/lib.gandr"),
        Library {
            imports: "import hello;\n",
            version: "0.1.0",
            rest: "pub def dependencies : List(Dependency) = [#{ alias = \"hello\", coordinate = \
                   Path(\"../hello\") }];\npub def greeting = hello.welcome;\n",
        }
        .source(),
    )
    .expect("the sibling is written");
    directory
}

/// Write `hello`'s library under `directory` as `written`.
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
        directory.join("hello/src/lib.gandr"),
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

/// #3072: a library's `dependencies` runs before its lock is written, the
/// use through the alias alone refused; the lock records the dependency's
/// coordinate, address and signature key, is written once, read back equal
/// and unchanged on a second run, and is the same bytes resolved from another
/// directory; with it, the use reads the dependency.
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
    assert_eq!(
        sibling.dependencies(),
        Ok(Vec::from([Dependency {
            alias: Alias::new(String::from("hello")),
            coordinate: Coordinate::Path(String::from("../hello")),
        }])),
        "the dependencies run before any lock stands"
    );
    let unlocked = sibling.identity(&grammar, &Held::default(), &Lock::default());
    assert!(
        matches!(unlocked, Err(Unaddressed::Refused { ref item, .. }) if item == "greeting"),
        "with no lock, the use through the alias is refused, and only it: {unlocked:?}"
    );
    let lock = sibling.resolve(&grammar).expect("the dependencies resolve");
    let own = hello
        .identity(&grammar, &Held::default(), &Lock::default())
        .expect("hello addresses");
    assert_eq!(
        lock.locked(&Alias::new(String::from("hello"))),
        Some(&Locked {
            coordinate: Coordinate::Path(String::from("../hello")),
            address: own.address,
            signature: own.signature,
        }),
        "the lock records hello's coordinate and identity"
    );
    assert!(
        matches!(reconcile_lock(&sibling, &lock), Ok(Reconciled::Written)),
        "an absent lock is written"
    );
    let written =
        std::fs::read_to_string(directory.join("sibling").join(LOCK)).expect("the lock reads");
    assert!(
        matches!(Lock::read(&sibling), Maybe::Present(ref read) if *read == lock),
        "the lock reads back as it was written"
    );
    assert_eq!(
        sibling.resolve(&grammar).as_ref(),
        Ok(&lock),
        "a second resolution is the same lock"
    );
    assert!(
        matches!(reconcile_lock(&sibling, &lock), Ok(Reconciled::Unchanged)),
        "a second run writes nothing"
    );
    assert_eq!(
        std::fs::read_to_string(directory.join("sibling").join(LOCK)).ok(),
        Some(written.clone()),
        "the lock stands byte for byte"
    );
    let locked = sibling
        .identity(&grammar, &Held::default(), &lock)
        .expect("with the lock, the use reads `hello.welcome`");
    let elsewhere = siblings(Path::new("lock-elsewhere"), Hello {
        version: "0.1.0",
        welcome: "hello",
    });
    let other = rooted(&elsewhere.join("sibling"));
    let relocked = other.resolve(&grammar).expect("the copy resolves");
    assert_eq!(
        relocked.render(),
        written,
        "the lock is the same bytes resolved from another directory"
    );
    assert!(
        matches!(reconcile_lock(&other, &relocked), Ok(Reconciled::Written)),
        "the copy's lock is written"
    );
    assert_eq!(
        other
            .identity(&grammar, &Held::default(), &relocked)
            .map(|identity| identity.address),
        Ok(locked.address),
        "the dependent's address is the same from another directory"
    );
    for scratch in [directory, elsewhere] {
        std::fs::remove_dir_all(&scratch).expect("the scratch directory is removed");
    }
}

/// #3072: an inert edit to a dependency leaves its dependent's lock; a
/// content edit moves the dependency's address, and the standing lock is
/// refused as `LockDrift.hello`, left byte for byte, until `relock` writes
/// it again; a hand edit to the lock is refused as drift.
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
    let lock = sibling.resolve(&grammar).expect("the dependencies resolve");
    assert!(
        matches!(reconcile_lock(&sibling, &lock), Ok(Reconciled::Written)),
        "the lock is written"
    );
    let standing = std::fs::read_to_string(&path).expect("the lock reads");
    write_hello(&directory, Hello {
        version: "0.2.0",
        welcome: "hello",
    });
    assert!(
        matches!(
            reconcile_lock(&sibling, &sibling.resolve(&grammar).expect("it resolves")),
            Ok(Reconciled::Unchanged)
        ),
        "an inert edit to the dependency leaves the lock"
    );
    write_hello(&directory, Hello {
        version: "0.2.0",
        welcome: "howdy",
    });
    let moved = sibling.resolve(&grammar).expect("it resolves");
    assert_ne!(
        moved
            .locked(&Alias::new(String::from("hello")))
            .map(|locked| locked.address),
        lock.locked(&Alias::new(String::from("hello")))
            .map(|locked| locked.address),
        "a content edit moves the dependency's address"
    );
    let drifted = reconcile_lock(&sibling, &moved);
    assert!(
        matches!(drifted, Err(LockFault::Drifted(ref aliases)) if *aliases == [Alias::new(String::from("hello"))]),
        "the standing lock is drift at `hello`: {drifted:?}"
    );
    assert_eq!(
        drifted.map_err(|fault| fault.to_string()).err().as_deref(),
        Some(
            "LockDrift.hello: the lock records another dependency than it resolves to, so it is \
             left as it stands; relock with `gandr lock`"
        ),
        "the drift names its alias"
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
        matches!(reconcile_lock(&sibling, &moved), Ok(Reconciled::Unchanged)),
        "the relocked lock holds"
    );
    let mut edited = std::fs::read_to_string(&path).expect("the lock reads");
    edited.push_str("# by hand\n");
    std::fs::write(&path, edited).expect("the lock is edited");
    assert!(
        matches!(reconcile_lock(&sibling, &moved), Err(LockFault::Edited)),
        "a hand edit is refused"
    );
    std::fs::remove_dir_all(&directory).expect("the scratch directory is removed");
}

/// #3072: two packages depending on each other by path are refused as a
/// `DependencyCycle`, naming the chain of roots from the one resolved back to
/// it.
#[test]
fn a_dependency_cycle_is_refused_by_its_paths_3072()
{
    let grammar = built_in().expect("the built-in grammar builds");
    let directory = scratch(Path::new("cycle"), &[
        Path::new("a/src/lib.gandr"),
        Path::new("b/src/lib.gandr"),
    ]);
    for (from, to) in [("a", "b"), ("b", "a")] {
        std::fs::write(
            directory.join(from).join("src/lib.gandr"),
            format!(
                "{STD_PACKAGE}pub def dependencies : List(Dependency) = [#{{ alias = \"{to}\", \
                 coordinate = Path(\"../{to}\") }}];\n"
            ),
        )
        .expect("the library is written");
    }
    let resolved = rooted(&directory.join("a")).resolve(&grammar);
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
