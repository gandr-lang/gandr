//! A package: the sources beside a `lib.gandr`, and the `gandr.toml` the
//! checker writes at its root from the package's own model.
//!
//! # A package is found by its library
//!
//! [`Package::discover`] walks up from a path to the first directory that
//! holds `lib.gandr`, or holds it in a `src` directory of its own. The package
//! is every source under the library's directory. Its root, where the manifest
//! lives, is that directory, or the directory above it when the library sits
//! in a directory named `src`. So a package laid out as `hello/src/lib.gandr`
//! is rooted at `hello`, and one laid out as `hello/lib.gandr` at `hello`
//! too. The search is Cargo's upward search for `Cargo.toml` and Go's for
//! `go.mod`, keyed by the library a gandr package always has rather than by
//! the manifest, since the manifest is the checker's output. A layout that
//! roots a package elsewhere reverses the convention, by a root the
//! package's model states.
//!
//! # The manifest is written, never read
//!
//! `gandr check` evaluates `Package.name` and `Package.version` of the
//! library and renders them as [`Manifest::render`] does. The file opens
//! with a header naming the model it was written from and a BLAKE3 digest
//! of the rest of the file, so [`reconcile`] tells the checker's own file
//! from one edited by hand: the first is rewritten when the model changes,
//! and the second is refused as drift, so a hand edit is never overwritten
//! and never read.
//!
//! # References
//!
//! - `vault:01a178aa-d585-7822-9cf0-40459729a925` — background: a package's
//!   metadata is written in gandr rather than in a manifest language, so the
//!   manifest is the checker's output and is never read back.

use alloc::collections::BTreeSet;
use core::fmt::Write as _;
use std::io;
use std::path::Path;
use std::path::PathBuf;

use anodized::spec;
use gandr_surface_corpus::DeclarationReport;
use gandr_surface_corpus::SettleReport;
use gandr_surface_lowering::SurfaceName;
use gandr_surface_lowering::decode_escapes;
use gandr_surface_syntax::SourceFragment;
use quenchant_shape::shape::Maybe;

use crate::evaluate::Evaluation;
use crate::evaluate::Program;
use crate::evaluate::declaration_name;
use crate::workspace::Unmembered;
use crate::workspace::WORKSPACE;
use crate::workspace::Workspace;
use crate::workspace::workspace_root;

/// The file name of a package's library, the source that declares the
/// package's model.
pub const LIBRARY: &str = "lib.gandr";

/// The file name of the manifest the checker writes at a package's root.
pub const MANIFEST: &str = "gandr.toml";

/// The directory name that roots a package one directory above its library.
const SOURCES: &str = "src";

/// The line that opens a manifest the checker wrote.
const WRITTEN: &str = "# Written by `gandr check` from the package's `Package` model: edit the \
                       model, not this file.";

/// The prefix of the header line that carries the digest of the body.
const DIGEST: &str = "# blake3: ";

/// A package: its library and the root its manifest is written at.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Package
{
    /// The directory the manifest is written in.
    root: PathBuf,
    /// The library, `lib.gandr`.
    library: PathBuf,
}

impl Package
{
    /// The package `from` sits in, found by walking up from it to the first
    /// directory holding a library.
    ///
    /// # Specification
    /// - requires: nothing; a relative path is read against the working
    ///   directory.
    /// - ensures: the first directory from `from` up — `from` itself when it is
    ///   a directory, else the directory holding it — that holds [`LIBRARY`],
    ///   or holds it in a [`SOURCES`] directory, names the package; its library
    ///   is that file, and its root the directory above the library's when that
    ///   is named [`SOURCES`], else the library's own. Each path is canonical.
    ///   `Unpackaged` when no directory up to the filesystem's root holds one,
    ///   or `from` cannot be canonicalized.
    /// - provides: the root search every verb run without a path reads.
    /// - fails: an unpackaged path is the typed absence.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a leaf two directories below `src/lib.gandr`, the
    ///   package's root, its `src` directory and a flat `lib.gandr` each find
    ///   their package at its root, an inner library is found before an outer
    ///   one, and a directory with no library above it is unpackaged.
    /// - witness: `tests::package::a_package_is_found_from_any_path_in_it_2687`
    #[spec(ensures: |ret| match ret {
        Maybe::Present(ref package) => package.library.ends_with(LIBRARY)
            && package.library.starts_with(&package.root),
        Maybe::Absent(package_root::Absent::Unpackaged) => true,
    })]
    #[inline]
    pub fn discover(from: &Path) -> Maybe<Self, package_root::Absent>
    {
        let unpackaged = Maybe::Absent(package_root::Absent::Unpackaged);
        let Ok(canonical) = from.canonicalize()
        else {
            return unpackaged;
        };
        let start = if canonical.is_dir() {
            canonical.as_path()
        }
        else {
            match canonical.parent() {
                Some(parent) => parent,
                None => return unpackaged,
            }
        };
        for directory in start.ancestors() {
            let library = [
                directory.join(LIBRARY),
                directory.join(SOURCES).join(LIBRARY),
            ]
            .into_iter()
            .find(|library| library.is_file());
            if let Some(library) = library {
                let sources = library.parent().unwrap_or(directory);
                let root = if sources.file_name().is_some_and(|name| name == SOURCES) {
                    sources.parent().unwrap_or(sources)
                }
                else {
                    sources
                };
                return Maybe::Present(Self {
                    root: root.to_path_buf(),
                    library,
                });
            }
        }
        unpackaged
    }

    /// The directory the manifest is written in.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn root(&self) -> &Path
    {
        &self.root
    }

    /// The package's library, `lib.gandr`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn library(&self) -> &Path
    {
        &self.library
    }

    /// The directory every source of the package sits under: the library's.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn sources(&self) -> &Path
    {
        self.library.parent().unwrap_or(&self.root)
    }

    /// The path of the package's manifest, [`MANIFEST`] at its root.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn manifest(&self) -> PathBuf
    {
        self.root.join(MANIFEST)
    }
}

quenchant_shape::reason_enum! {
    /// Why a path stands in no package.
    pub mod package_root {
        /// No directory from the path up holds a library.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No `lib.gandr` stands in, or in a `src` directory of, any
            /// directory from the path up.
            Unpackaged,
        }
    }
}

/// The paths a verb walks and the packages they reach, each path inside a
/// package or naming a workspace widened to what it stands for.
///
/// # Specification
/// - requires: `working` is the process's working directory, against which a
///   relative path given is read, or every path given is absolute.
/// - ensures: with no path, the package [`Package::discover`] finds from
///   `working`, its [`Package::sources`] the one path walked; when it finds
///   none, the workspace [`Workspace::discover`] finds from `working`: its
///   [`Workspace::source`], then each member's sources in the order
///   [`Workspace::members`] reads them; and [`Unpathed::Nowhere`] naming
///   `working` canonically when neither stands. Otherwise each path in order:
///   one in a package is replaced by the package's sources, and also kept when
///   it lies outside them, under the package's root; a workspace's directory,
///   in no package, is replaced by the workspace's source and its members'
///   sources; any other path in no package is kept as given. A package's
///   sources are listed once, at the first path reaching it, and each package
///   once, in that order. Paths below `working` are listed relative to it, `.`
///   for `working` itself, as a path a caller gives would be.
/// - provides: the paths `check`, `test` and `fmt` walk, and the packages whose
///   manifests `check` reconciles.
/// - fails: [`Unpathed::Nowhere`] when no path is given and `working` is in no
///   package and no workspace; [`Unpathed::Unmembered`] when a workspace the
///   verb works on names no packages.
/// - panics: none.
///
/// # Errors
/// [`Unpathed`], as above.
///
/// # Adequacy
/// - hypothesis: L3 — no path in a package, no path outside one, a leaf of a
///   package beside a path in no package, two leaves of one package, and a
///   source under the root outside the sources directory each walk their exact
///   paths and packages; no path in a workspace and its directory given each
///   walk its members.
/// - witness: `tests::package::a_path_in_a_package_walks_the_whole_package_2687`
/// - witness: `tests::package::a_workspace_walks_every_member_it_names_2687`
#[spec(
    captures: [given = paths.len()],
    ensures: |ret| match ret {
        Ok((ref walked, ref packages)) => packages.iter().all(|package|
                walked.iter().any(|path| working.join(path).canonicalize()
                    .is_ok_and(|canonical| canonical == package.sources()))),
        Err(Unpathed::Nowhere { .. }) => given == 0,
        Err(Unpathed::Unmembered { .. }) => true,
    },
)]
#[inline]
pub fn packaged(
    paths: Vec<PathBuf>,
    working: &Path,
) -> Result<(Vec<PathBuf>, Vec<Package>), Unpathed>
{
    let base = working
        .canonicalize()
        .unwrap_or_else(|_| working.to_path_buf());
    // A path as the walk prints it: below the working directory when it is,
    // as the paths a caller gives would be.
    let shown = |path: &Path| match path.strip_prefix(&base) {
        Ok(below) if below.as_os_str().is_empty() => PathBuf::from("."),
        Ok(below) => below.to_path_buf(),
        Err(_) => path.to_path_buf(),
    };
    let members = |workspace: &Workspace| {
        workspace.members().map_err(|why| Unpathed::Unmembered {
            workspace: workspace.source(),
            why,
        })
    };
    let mut walked: Vec<PathBuf> = Vec::new();
    let mut packages: Vec<Package> = Vec::new();
    let mut seen: BTreeSet<PathBuf> = BTreeSet::new();
    let mut reach = |package: Package, walked: &mut Vec<PathBuf>| {
        if seen.insert(package.library.clone()) {
            walked.push(shown(package.sources()));
            packages.push(package);
        }
    };
    if paths.is_empty() {
        if let Maybe::Present(package) = Package::discover(working) {
            reach(package, &mut walked);
        }
        else if let Maybe::Present(workspace) = Workspace::discover(working) {
            walked.push(shown(&workspace.source()));
            for package in members(&workspace)? {
                reach(package, &mut walked);
            }
        }
        else {
            return Err(Unpathed::Nowhere { working: base });
        }
        return Ok((walked, packages));
    }
    for path in paths {
        let Maybe::Present(package) = Package::discover(&path)
        else {
            let canonical = path.canonicalize().ok();
            match Workspace::discover(&path) {
                Maybe::Present(workspace) if canonical.as_deref() == Some(workspace.root()) => {
                    walked.push(shown(&workspace.source()));
                    for package in members(&workspace)? {
                        reach(package, &mut walked);
                    }
                },
                Maybe::Present(_) | Maybe::Absent(workspace_root::Absent::Unworkspaced) => {
                    walked.push(path);
                },
            }
            continue;
        };
        let inside = path
            .canonicalize()
            .is_ok_and(|canonical| canonical.starts_with(package.sources()));
        reach(package, &mut walked);
        if !inside {
            walked.push(path);
        }
    }
    Ok((walked, packages))
}

/// Why a verb has no paths to walk.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Unpathed
{
    /// No path was given, and the working directory stands in no package and
    /// no workspace.
    Nowhere
    {
        /// The directory the search started from.
        working: PathBuf,
    },
    /// A workspace the verb works on names no packages.
    Unmembered
    {
        /// The workspace's source.
        workspace: PathBuf,
        /// Why it names none.
        why: Unmembered,
    },
}

impl core::fmt::Display for Unpathed
{
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        match *self {
            Self::Nowhere { ref working } => write!(
                f,
                "no path given, and no `{LIBRARY}` stands in `{}` or a directory above it, or in \
                 a `{SOURCES}` directory of one, and no `{WORKSPACE}` above it",
                working.display()
            ),
            Self::Unmembered {
                ref workspace,
                ref why,
            } => {
                write!(f, "{}: {why}", workspace.display())
            },
        }
    }
}

impl core::error::Error for Unpathed
{
}

/// What a package's model states for its manifest, and the modules its
/// sources make.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Manifest
{
    /// `Package.name`.
    name: String,
    /// `Package.version`.
    version: String,
    /// Each module of the package but its root, by its path.
    modules: BTreeSet<String>,
}

impl Manifest
{
    /// The manifest `program`'s `Package` model states: its `name` and its
    /// `version`, each run to its string; and the modules of `package`.
    ///
    /// # Specification
    /// - requires: `program` is the program of the package's library, and `own`
    ///   the report of the library's own declarations.
    /// - ensures: each field read by its path among the declarations `own`
    ///   reports, `Package.name` then `Package.version`, run once, and its
    ///   string decoded from the value's spelling; the first field none of them
    ///   declares is [`Unmanifested::Undeclared`], and the first whose run is
    ///   no string [`Unmanifested::Unstrung`] with what it came to. The modules
    ///   are [`modules`] of `package`'s sources.
    /// - provides: the manifest `gandr check` writes.
    /// - fails: a field undeclared, or run to no string.
    /// - panics: none.
    /// - executable: none — each field is run on the program's machine, which a
    ///   predicate could only check by running it again; the witness observes
    ///   each outcome.
    ///
    /// # Errors
    /// The first field that is undeclared, or does not run to a string.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a model holding both fields, one of them escaped,
    ///   reads both; one missing `version` and one whose name is an integer are
    ///   refused at that field.
    /// - witness: `tests::package::a_manifest_reads_the_package_model_2687`
    #[inline]
    pub fn of(
        program: &mut Program<'_>,
        own: &SettleReport<'_>,
        package: &Package,
    ) -> Result<Self, Unmanifested>
    {
        let mut field = |field: Field| {
            let path = field.path();
            let constant = match program.named_among(
                path,
                own.declarations().iter().map(DeclarationReport::constant),
            ) {
                Maybe::Present(constant) => constant,
                Maybe::Absent(declaration_name::Absent::Undeclared) => {
                    return Err(Unmanifested::Undeclared(field));
                },
            };
            match program.evaluate(constant) {
                Evaluation::Value(value) => {
                    let spelled = value.to_string();
                    let decoded = spelled
                        .strip_prefix('"')
                        .and_then(|rest| rest.strip_suffix('"'))
                        .map(|content| decode_escapes(SourceFragment::from(content)));
                    decoded.ok_or(Unmanifested::Unstrung {
                        field,
                        came: spelled,
                    })
                },
                ref other @ (Evaluation::Sealed(_)
                | Evaluation::Blamed(_)
                | Evaluation::Holed { .. }
                | Evaluation::Stuck(_)
                | Evaluation::Unfinished(_)
                | Evaluation::Unrunnable(_)) => Err(Unmanifested::Unstrung {
                    field,
                    came: other.to_string(),
                }),
            }
        };
        let name = field(Field::Name)?;
        let version = field(Field::Version)?;
        Ok(Self {
            name,
            version,
            modules: modules(package.sources()),
        })
    }

    /// The manifest as the checker writes it: the header, then the body.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the [`WRITTEN`] line, the digest line carrying the BLAKE3
    ///   digest of the body in lowercase hexadecimal, then the body: a
    ///   `[package]` table with `name` and `version` as TOML basic strings,
    ///   each `"`, `\` and control character escaped, and `modules` an array of
    ///   the modules' paths, one per line, in order, or `[]` when there are
    ///   none, as the tree's TOML formatter writes it. The same manifest
    ///   renders the same bytes.
    /// - provides: the file [`reconcile`] writes.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a manifest renders its pinned bytes, and one whose
    ///   name holds a quote, a backslash and a newline escapes each.
    /// - witness: `tests::package::a_manifest_renders_its_digest_and_its_table_2687`
    #[spec(ensures: |ref ret| ret.starts_with(WRITTEN)
        && matches!(Split::of(Manifested(ret)).authorship(), Authorship::Checker))]
    #[inline]
    #[must_use]
    pub fn render(&self) -> String
    {
        let body = format!(
            "\n[package]\nname = {}\nversion = {}\nmodules = {}\n",
            Basic(&self.name),
            Basic(&self.version),
            Listed(&self.modules)
        );
        format!(
            "{WRITTEN}\n{DIGEST}{}\n{body}",
            blake3::hash(body.as_bytes()).to_hex()
        )
    }
}

/// Every module the sources under `sources` make but the root, each named by
/// its path from `sources`: `text/greet.gandr` is `text.greet`.
///
/// # Specification
/// - requires: `sources` is a package's sources directory.
/// - ensures: one name per `.gandr` file under `sources`, its directories and
///   its file stem joined by `.`, the root module `lib.gandr` beside `sources`
///   left out; a directory holding a `lib.gandr` of its own is another
///   package's, and nothing under it is named. A directory that does not list
///   names nothing.
/// - provides: the membership the manifest records: a module is a file, and
///   nothing declares it.
/// - fails: never.
/// - panics: none.
/// - executable: none — the clause reads the file system again.
///
/// # Adequacy
/// - hypothesis: L3 — a package with a nested module and a nested package lists
///   the module alone.
/// - witness: `tests::package::a_manifest_lists_the_modules_its_sources_make_2687`
fn modules(sources: &Path) -> BTreeSet<String>
{
    let mut named = BTreeSet::new();
    let mut pending = Vec::from([sources.to_path_buf()]);
    while let Some(directory) = pending.pop() {
        listed(sources, &directory, &mut pending, &mut named);
    }
    named
}

/// File the entries of `directory`, under the package's `sources`: each
/// directory that holds no library onto `pending`, and each source but the
/// root's into `named`, by its module path.
///
/// # Specification
/// trivial.
fn listed(
    sources: &Path,
    directory: &Path,
    pending: &mut Vec<PathBuf>,
    named: &mut BTreeSet<String>,
)
{
    let Ok(entries) = std::fs::read_dir(directory)
    else {
        return;
    };
    for path in entries.filter_map(Result::ok).map(|entry| entry.path()) {
        if path.is_dir() {
            if !path.join(LIBRARY).is_file() {
                pending.push(path);
            }
        }
        else if path
            .extension()
            .is_some_and(|extension| extension == "gandr")
            && path != sources.join(LIBRARY)
            && let Some(module) = module_path(sources, &path)
        {
            let _fresh = named.insert(module);
        }
    }
}

/// The module path of the source at `path` under `sources`: its directories
/// and its file stem, joined by `.`.
///
/// # Specification
/// trivial.
fn module_path(
    sources: &Path,
    path: &Path,
) -> Option<String>
{
    let relative = path.strip_prefix(sources).ok()?.with_extension("");
    let names: Option<Vec<&str>> = relative
        .components()
        .map(|component| component.as_os_str().to_str())
        .collect();
    Some(names?.join("."))
}

/// A field of the `Package` model the manifest records.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Field
{
    /// `Package.name`.
    Name,
    /// `Package.version`.
    Version,
}

impl Field
{
    /// The field's path from the library's top level.
    ///
    /// # Specification
    /// trivial.
    fn path(self) -> SurfaceName<'static>
    {
        SurfaceName::from(match self {
            Self::Name => "Package.name",
            Self::Version => "Package.version",
        })
    }
}

/// Why a library's model gives no manifest.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Unmanifested
{
    /// The library declares no such field.
    Undeclared(Field),
    /// The field does not run to a string.
    Unstrung
    {
        /// The field.
        field: Field,
        /// What its run came to, spelled.
        came: String,
    },
}

impl core::fmt::Display for Unmanifested
{
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        match *self {
            Self::Undeclared(field) => write!(
                f,
                "the library declares no `{}`, so no `{MANIFEST}` is written: import `std.package` \
                 and declare `module Package : Model(Gandr.Package)` in it",
                field.path()
            ),
            Self::Unstrung { field, ref came } => write!(
                f,
                "`{}` runs to `{came}`, not to a string, so no `{MANIFEST}` is written",
                field.path()
            ),
        }
    }
}

/// What [`reconcile`] did to a manifest.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Reconciled
{
    /// No manifest stood there; it was written.
    Written,
    /// The checker's manifest stated another model; it was rewritten.
    Rewritten,
    /// The manifest is the one the model renders; nothing was written.
    Unchanged,
}

impl core::fmt::Display for Reconciled
{
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        f.write_str(match *self {
            Self::Written => "written",
            Self::Rewritten => "rewritten",
            Self::Unchanged => "unchanged",
        })
    }
}

/// Why a manifest was not reconciled.
#[derive(Debug)]
pub enum ManifestFault
{
    /// The file is not the checker's: its body does not match the digest its
    /// header carries, or it carries none. It was left as it stands.
    Drifted,
    /// The file could not be read or written.
    Io(io::Error),
}

impl core::fmt::Display for ManifestFault
{
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        match *self {
            Self::Drifted => write!(
                f,
                "drifted: edited since the checker wrote it, so it is left as it stands; state the \
                 change in the `Package` model and delete the file to have it written again"
            ),
            Self::Io(ref error) => write!(f, "{error}"),
        }
    }
}

impl core::error::Error for ManifestFault
{
}

/// Bring the manifest at `path` to `manifest`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: an absent file is written with [`Manifest::render`] and is
///   [`Reconciled::Written`]. A file whose header carries the digest of its
///   body is the checker's: when it is the render, nothing is written and it is
///   [`Reconciled::Unchanged`]; otherwise it is overwritten with the render and
///   is [`Reconciled::Rewritten`]. Any other file is left unchanged and is
///   [`ManifestFault::Drifted`].
/// - provides: the manifest step of `gandr check`.
/// - fails: a drifted file, or one that cannot be read or written.
/// - panics: none.
/// - executable: none — the clause is about the file, which a predicate could
///   only check by reading it again after the write; the witness observes each
///   case on disk.
///
/// # Errors
/// [`ManifestFault::Drifted`] for a file the checker did not write as it
/// stands, and [`ManifestFault::Io`] for one that cannot be read or written.
///
/// # Adequacy
/// - hypothesis: L3 — an absent file is written; the written file is unchanged
///   on a second run; a model change rewrites it; a hand edit to its body, and
///   a file with no header, are each refused as drift and left byte for byte.
/// - witness: `tests::package::a_manifest_is_written_rewritten_and_refused_as_drift_2687`
#[inline]
pub fn reconcile(
    path: &Path,
    manifest: &Manifest,
) -> Result<Reconciled, ManifestFault>
{
    let rendered = manifest.render();
    let standing = match std::fs::read_to_string(path) {
        Ok(standing) => standing,
        Err(error) if error.kind() == io::ErrorKind::NotFound => {
            return std::fs::write(path, rendered)
                .map(|()| Reconciled::Written)
                .map_err(ManifestFault::Io);
        },
        Err(error) => return Err(ManifestFault::Io(error)),
    };
    if matches!(
        Split::of(Manifested(&standing)).authorship(),
        Authorship::Hand
    ) {
        return Err(ManifestFault::Drifted);
    }
    if standing == rendered {
        return Ok(Reconciled::Unchanged);
    }
    std::fs::write(path, rendered)
        .map(|()| Reconciled::Rewritten)
        .map_err(ManifestFault::Io)
}

/// The text of a manifest file as it stands.
#[repr(transparent)]
#[derive(Clone, Copy)]
struct Manifested<'file>(&'file str);

/// Who wrote a manifest file as it stands.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Authorship
{
    /// The checker: its header carries its body's digest.
    Checker,
    /// Anyone else: the file has no header, or its body is not the one the
    /// header's digest names.
    Hand,
}

/// A manifest file read as its header's digest and its body.
struct Split<'file>
{
    /// The digest the header carries, when the file opens with the header.
    digest: Option<&'file str>,
    /// Everything below the header, or the whole file when it has none.
    body: &'file str,
}

impl<'file> Split<'file>
{
    /// `file` split at its header.
    ///
    /// # Specification
    /// trivial.
    fn of(file: Manifested<'file>) -> Self
    {
        let Manifested(text) = file;
        let headed = text
            .strip_prefix(WRITTEN)
            .and_then(|rest| rest.strip_prefix('\n'))
            .and_then(|rest| {
                let (line, body) = rest.split_once('\n')?;
                Some((line.strip_prefix(DIGEST)?, body))
            });
        match headed {
            Some((digest, body)) => Self {
                digest: Some(digest),
                body,
            },
            None => Self {
                digest: None,
                body: text,
            },
        }
    }

    /// Who wrote the file as it stands: the checker when its header carries
    /// its body's digest.
    ///
    /// # Specification
    /// trivial.
    fn authorship(&self) -> Authorship
    {
        let digest = blake3::hash(self.body.as_bytes());
        if self.digest == Some(digest.to_hex().as_str()) {
            Authorship::Checker
        }
        else {
            Authorship::Hand
        }
    }
}

/// A string written as a TOML basic string, `"` and `\` and each control
/// character escaped.
#[repr(transparent)]
struct Basic<'text>(&'text str);

impl core::fmt::Display for Basic<'_>
{
    /// # Specification
    /// trivial.
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        f.write_char('"')?;
        for character in self.0.chars() {
            match character {
                '"' => f.write_str("\\\"")?,
                '\\' => f.write_str("\\\\")?,
                '\n' => f.write_str("\\n")?,
                '\t' => f.write_str("\\t")?,
                '\r' => f.write_str("\\r")?,
                control if control.is_control() => write!(f, "\\u{:04X}", u32::from(control))?,
                other => f.write_char(other)?,
            }
        }
        f.write_char('"')
    }
}

/// Module paths written as a TOML array: `[]` when there are none, else
/// one line per path, each a basic string indented two spaces and followed
/// by a comma, between `[` and `]` on lines of their own.
#[repr(transparent)]
struct Listed<'modules>(&'modules BTreeSet<String>);

impl core::fmt::Display for Listed<'_>
{
    /// # Specification
    /// trivial.
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        if self.0.is_empty() {
            return f.write_str("[]");
        }
        f.write_str("[\n")?;
        for module in self.0 {
            writeln!(f, "  {},", Basic(module))?;
        }
        f.write_char(']')
    }
}
