//! A package: a `package.gandr` at its root, the modules under the directory
//! its model's `sources` names, and the `package.gandr.toml` the checker writes
//! beside it from the package's own model.
//!
//! # A package is found by its package source
//!
//! [`Package::discover`] walks up from a path to the first directory that holds
//! `package.gandr`. That directory is the package's root, where the manifest
//! lives. The package's modules are the sources under the directory its
//! `Package` model's `sources` names from the root, `src` for a package laid
//! out as `hello/package.gandr` and `hello/src/text/greet.gandr`. The search is
//! Cargo's upward search for `Cargo.toml` and Go's for `go.mod`, keyed by the
//! package source a gandr package always has rather than by the manifest,
//! since the manifest is the checker's output.
//!
//! **Choice.** Discovery reads `sources` off the package source's tokens, as
//! the string literal the model's `def sources` writes: an import resolves
//! through it before any source is checked, so it cannot wait for the model
//! to run. [`Manifest::of`] runs the field with the others, and refuses a
//! package whose `sources` runs to another string than the one discovery
//! read, or leaves the root. **Reversal.** A default for `sources` (#4915)
//! reads `src` for a model that states none.
//!
//! # The manifest is written, never read
//!
//! `gandr check` evaluates `Package.name` and `Package.version` of the
//! package source and renders them as [`Manifest::render`] does. The file opens
//! with a header naming the model it was written from and a BLAKE3 digest
//! of the rest of the file, so [`reconcile`] tells the checker's own file
//! from one edited by hand: the first is rewritten when the model changes,
//! and the second is refused as drift, so a hand edit is never overwritten
//! and never read.
//!
//! # A package's dependencies are locked by address
//!
//! [`lock`] resolves the coordinates that the sources of a package import. It
//! writes the lock that these imports read them through (#533 p3). A package
//! in no workspace keeps `package.gandr.lock` beside its package source. A
//! package below a workspace keeps its own table in `workspace.gandr.lock`.
//!
//! # A workspace has a manifest too
//!
//! [`WorkspaceManifest`] holds what the `Workspace` model of a workspace
//! states, and the members that `members` names. `gandr check` writes it as
//! `workspace.gandr.toml` beside `workspace.gandr` when it works on the
//! workspace. The header and the drift rule are the same as for the manifest
//! of a package.
//!
//! # A package's toolchain constraints are checked
//!
//! [`toolchain`] reads what the package's model asks of the toolchain, and
//! `gandr check` refuses a package whose constraints the running toolchain
//! does not meet (#533 p5).
//!
//! # A manifest's fields have identity roles
//!
//! A package's metadata is its package source's `Package` model, a model of
//! `std.build`'s `Gandr.Package`, not a manifest language, and each field
//! has one role in the package's address:
//!
//! | Role | Fields | Address |
//! | --- | --- | --- |
//! | inert | `name`, `version`, `authors`, `licence`, `documentation`, `endpoint`, `spelling`, `sources` | left out: an edit leaves it |
//! | resolution | an import's coordinate, `import "path:…" as name ;` | written in the importer's source; each dependency's address enters through the lock, never its alias or its coordinate |
//! | syntax | an import's signature, `import <address> : S ;` | written in the importer's source, not in the model |
//! | toolchain | `gandr`, `features`, `systems` | content: an edit moves it |
//!
//! The manifest's own bytes enter no address: `package.gandr.toml` is the
//! checker's output, so identity enters through the items, the lock and the
//! constraints, never through the file. Where the sources sit enters none
//! either: the address digests their content. A reference is an address and a
//! coordinate kept apart: the address says what the package is, and a resolve
//! that finds another is refused `LockDrift.<coordinate>`; the coordinate says
//! where it is found and is never part of identity. The capabilities a package
//! requires join the syntax role with #533 p6.
//!
//! # References
//!
//! - `vault:01a178aa-d585-7822-9cf0-40459729a925` — background: a package's
//!   metadata is written in gandr rather than in a manifest language, so the
//!   manifest is the checker's output and is never read back.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::sync::Arc;
use core::fmt::Write as _;
use std::io;
use std::path::Component;
use std::path::Path;
use std::path::PathBuf;

use anodized::spec;
use gandr_core_fork::Fork;
use gandr_core_incremental::ContentKey;
use gandr_core_incremental::ItemOrdinal;
use gandr_core_incremental::content_key;
use gandr_core_term::CoreArena;
use gandr_surface_corpus::DeclarationReport;
use gandr_surface_corpus::SettleReport;
use gandr_surface_grammar::Pbg;
use gandr_surface_lowering::ClosureLowering;
use gandr_surface_lowering::DeclarationOutcome;
use gandr_surface_lowering::Inertness;
use gandr_surface_lowering::LoweredModule;
use gandr_surface_lowering::SurfaceName;
use gandr_surface_lowering::Visibility;
use gandr_surface_lowering::coincide::Decisions;
use gandr_surface_lowering::decode_escapes;
use gandr_surface_parser::Lexeme;
use gandr_surface_parser::label;
use gandr_surface_parser::parse;
use gandr_surface_syntax::SourceFragment;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use crate::component;
use crate::component::Given;
use crate::component::Shadows;
use crate::component::named_path;
use crate::compose::Lowered;
use crate::compose::LoweringCount;
use crate::compose::item_program;
use crate::compose::lower_prelude;
use crate::compose::lower_unit_source;
use crate::evaluate::Evaluation;
use crate::evaluate::Program;
use crate::evaluate::declaration_name;
use crate::root::classify;
use crate::workspace::Gathered;
use crate::workspace::Unmembered;
use crate::workspace::WORKSPACE;
use crate::workspace::Workspace;
use crate::workspace::workspace_root;

pub mod export;
pub mod fetch;
pub mod lock;
pub mod toolchain;

use self::lock::Lock;
use self::lock::SignatureKey;
use self::toolchain::Separated;
use self::toolchain::Toolchain;

/// The file name of a package's source, the source that declares the
/// package's model.
pub const PACKAGE: &str = "package.gandr";

/// The file name of the manifest that the checker writes beside the source of
/// a package, at its root.
pub const MANIFEST: &str = "package.gandr.toml";

/// The `Package` model's field naming the directory a package's modules sit
/// under, as a model writes it.
const SOURCES: &str = "sources";

/// The line that opens a manifest the checker wrote.
const WRITTEN: &str = "# Written by `gandr check` from the package's `Package` model: edit the \
                       model, not this file.";

/// The first line of a workspace manifest that the checker wrote.
const WORKSPACE_WRITTEN: &str = "# Written by `gandr check` from the workspace's `Workspace` \
                                 model: edit the model, not this file.";

/// The prefix of the header line that carries the digest of the body.
const DIGEST: &str = "# blake3: ";

/// A package: its package source, the root its manifest is written at, and
/// the directory its modules sit under.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Package
{
    /// The directory the manifest is written in, which holds the package
    /// source.
    root: PathBuf,
    /// The package source, `package.gandr`.
    source: PathBuf,
    /// The directory the modules sit under: the one `stated` names below the
    /// root, else the root.
    sources: PathBuf,
    /// The string literal the model's `sources` writes, as discovery read it
    /// off the package source's tokens; none when it writes none.
    stated: Option<PathBuf>,
}

impl Package
{
    /// The package `from` sits in, found by walking up from it to the first
    /// directory holding a package source.
    ///
    /// # Specification
    /// - requires: nothing; a relative path is read against the working
    ///   directory.
    /// - ensures: the first directory from `from` up — `from` itself when it is
    ///   a directory, else the directory holding it — that holds [`PACKAGE`]
    ///   names the package: that directory is its root and that file its
    ///   package source. Its sources are the directory the string literal its
    ///   model's `sources` writes names below the root, read as
    ///   [`stated_sources`] reads it, when that path stays inside the root; the
    ///   root itself otherwise. Each path is canonical. `Unpackaged` when no
    ///   directory up to the filesystem's root holds one, or `from` cannot be
    ///   canonicalized.
    /// - provides: the root search every verb run without a path reads.
    /// - fails: an unpackaged path is the typed absence.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a leaf two directories below a package's `src`, the
    ///   package's root and its `src` directory each find their package at its
    ///   root with its sources at `src`, a package whose `sources` is `.` has
    ///   its root for its sources, an inner package source is found before an
    ///   outer one, and a directory with no package source above it is
    ///   unpackaged.
    /// - witness: `tests::package::a_package_is_found_from_any_path_in_it_2687`
    #[spec(ensures: |ret| match ret {
        Maybe::Present(ref package) => package.source.ends_with(PACKAGE)
            && package.source.parent() == Some(package.root.as_path())
            && package.sources.starts_with(&package.root),
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
            let source = directory.join(PACKAGE);
            if source.is_file() {
                let stated = std::fs::read_to_string(&source)
                    .ok()
                    .and_then(|text| stated_sources(SourceFragment::from(text.as_str())));
                let sources = stated
                    .as_deref()
                    .and_then(|stated| inside(directory, stated))
                    .unwrap_or_else(|| directory.to_path_buf());
                return Maybe::Present(Self {
                    root: directory.to_path_buf(),
                    source,
                    sources,
                    stated,
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

    /// The package's source, `package.gandr`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn source(&self) -> &Path
    {
        &self.source
    }

    /// The directory every module of the package sits under: the one its
    /// model's `sources` names, or the root when that names none inside it.
    /// A directory that does not stand holds no modules, as a checkout of a
    /// package with none carries no empty directory.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn sources(&self) -> &Path
    {
        &self.sources
    }

    /// The directory the model's `sources` writes, its string literal as
    /// discovery read it; none when the model writes none.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn stated(&self) -> Option<&Path>
    {
        self.stated.as_deref()
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

    /// The paths where a walk of the package starts. The package source comes
    /// first when it is outside the sources. The sources come next when that
    /// directory exists.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Package::source`] first when it is not under
    ///   [`Package::sources`]. Then [`Package::sources`] when that directory
    ///   exists. A walk of these paths reaches each source of the package once.
    /// - provides: the paths that `packaged` lists for a package. The language
    ///   server walks the same paths for the package that a folder roots.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a package with the sources `src` walks its package
    ///   source and `src`. A package with its root as its sources walks the
    ///   root alone. A package with sources that do not exist walks its package
    ///   source alone.
    /// - witness: `tests::package::a_path_in_a_package_walks_the_whole_package_2687`
    #[spec(ensures: |ret| ret.len() <= 2 && ret.iter().all(|path| path.starts_with(&self.root)))]
    #[inline]
    #[must_use]
    pub fn walked(&self) -> Vec<&Path>
    {
        let mut walked = Vec::with_capacity(2);
        if !self.source.starts_with(&self.sources) {
            walked.push(self.source.as_path());
        }
        if self.sources.is_dir() {
            walked.push(self.sources.as_path());
        }
        walked
    }
}

quenchant_shape::reason_enum! {
    /// Why a path stands in no package.
    pub mod package_root {
        /// No directory from the path up holds a package source.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No `package.gandr` stands in any directory from the path up.
            Unpackaged,
        }
    }
}

/// The string literal `source`, a package source, writes for its `Package`
/// model's `sources`, as a path: the string after `def sources =` directly in
/// the block of the module named `Package`, the module [`Manifest::of`]
/// reads each field of. The block is braced or laid out: the labeler writes a
/// laid-out block's brackets as tokens of their own, which spell nothing.
/// None when that module writes none, or writes an escape.
///
/// # Specification
/// - requires: nothing.
/// - ensures: read off the labeler's tokens, the spaces and comments skipped,
///   the first `def sources = "<text>"` at depth one of the block after the
///   first `module Package`, braced or laid out; its `<text>` as written, empty
///   for `""`; none when the string holds an escape or the form is another.
/// - provides: the directory discovery reads before any source is checked.
/// - fails: never; an unread field is none.
/// - panics: none.
/// - executable: none — the clause restates the scan.
///
/// # Adequacy
/// - hypothesis: L3 — `src`, `.` and the empty string read as written, in a
///   braced block and in a laid-out one; a computed `sources`, an escaped one
///   and one in a nested module read none.
/// - witness: `tests::package::a_model_s_sources_is_the_literal_discovery_reads_4916`
fn stated_sources(source: SourceFragment<'_>) -> Option<PathBuf>
{
    let tokens: Vec<(Lexeme, &str)> = label(source)
        .iter()
        .filter(|token| token.lexeme != Lexeme::Space)
        .map(|token| (token.lexeme, <&str>::from(token.text(&source))))
        .collect();
    let spelled = |at: usize| tokens.get(at).map(|&(_, spelled)| spelled);
    let opens = |at: usize| {
        tokens
            .get(at)
            .is_some_and(|&(lexeme, spelled)| lexeme == Lexeme::LayoutOpen || spelled == "{")
    };
    let closes = |at: usize| {
        tokens
            .get(at)
            .is_some_and(|&(lexeme, spelled)| lexeme == Lexeme::LayoutClose || spelled == "}")
    };
    let named = (0 .. tokens.len()).find(|&at| {
        spelled(at) == Some("module") && spelled(at.saturating_add(1)) == Some("Package")
    })?;
    let open = (named .. tokens.len()).find(|&at| opens(at))?;
    let mut depth = 0_usize;
    for at in open .. tokens.len() {
        if opens(at) {
            depth = depth.saturating_add(1);
            continue;
        }
        if closes(at) {
            depth = depth.saturating_sub(1);
            if depth == 0 {
                return None;
            }
            continue;
        }
        if spelled(at) == Some("def")
            && depth == 1
            && spelled(at.saturating_add(1)) == Some(SOURCES)
            && spelled(at.saturating_add(2)) == Some("=")
        {
            let quoted = at.saturating_add(3);
            return match (
                tokens.get(quoted),
                tokens.get(quoted.saturating_add(1)),
                tokens.get(quoted.saturating_add(2)),
            ) {
                (Some(&(Lexeme::Quote, _)), Some(&(Lexeme::Quote, _)), _) => Some(PathBuf::new()),
                (
                    Some(&(Lexeme::Quote, _)),
                    Some(&(Lexeme::StringFragment, written)),
                    Some(&(Lexeme::Quote, _)),
                ) => Some(PathBuf::from(written)),
                _ => None,
            };
        }
    }
    None
}

/// The directory `stated`, a relative path, names below `root`; none when it
/// is empty or leaves `root`: a parent, a root or a prefix among its
/// components.
///
/// # Specification
/// trivial.
fn inside(
    root: &Path,
    stated: &Path,
) -> Option<PathBuf>
{
    let mut below = root.to_path_buf();
    for component in stated.components() {
        match component {
            Component::Normal(name) => below.push(name),
            Component::CurDir => {},
            Component::ParentDir | Component::RootDir | Component::Prefix(_) => return None,
        }
    }
    (!stated.as_os_str().is_empty()).then_some(below)
}

/// The paths that a verb walks, the packages that they reach and the
/// workspaces that they gather.
///
/// The function widens each path in a package to the package, and each path
/// that names a workspace to its members.
///
/// # Specification
/// - requires: `working` is the process's working directory, against which a
///   relative path given is read, or every path given is absolute.
/// - ensures: with no path, the package [`Package::discover`] finds from
///   `working`: its package source when it lies outside its
///   [`Package::sources`], then its sources when they stand; when it finds
///   none, the workspace [`Workspace::discover`] finds from `working`: its
///   [`Workspace::source`], then each member as a package is listed, in the
///   order [`Workspace::members`] reads them; and [`Unpathed::Nowhere`] naming
///   `working` canonically when neither stands. Otherwise each path in order:
///   one in a package is replaced by the package as it is listed, and also kept
///   when it lies outside the sources and is not the package source, under the
///   package's root; a workspace's directory, in no package, is replaced by the
///   workspace's source and its members; any other path in no package is kept
///   as given. A package is listed once, at the first path reaching it, and
///   each package once, in that order. Paths below `working` are listed
///   relative to it, `.` for `working` itself, as a path a caller gives would
///   be.
/// - provides: the paths `check`, `test` and `fmt` walk, and the packages whose
///   locks and manifests `check` reconciles. Also the workspaces whose
///   manifests `check` reconciles. Each workspace that the verb works on is in
///   the list one time, as [`Workspace::members`] gathers it. The order is the
///   order in which the paths reach them.
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
        Ok((ref walked, ref packages, _)) => packages.iter().all(|package|
                !package.sources().is_dir()
                || walked.iter().any(|path| working.join(path).canonicalize()
                    .is_ok_and(|canonical| canonical == package.sources()))),
        Err(Unpathed::Nowhere { .. }) => given == 0,
        Err(Unpathed::Unmembered { .. }) => true,
    },
)]
#[inline]
pub fn packaged(
    paths: Vec<PathBuf>,
    working: &Path,
) -> Result<Walked, Unpathed>
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
    let mut gathered: Vec<Gathered> = Vec::new();
    let mut members = |workspace: &Workspace| {
        let (members, read) = workspace.members().map_err(|why| Unpathed::Unmembered {
            workspace: workspace.source(),
            why,
        })?;
        if gathered
            .iter()
            .all(|standing| standing.workspace != *workspace)
        {
            gathered.push(read);
        }
        Ok(members)
    };
    let mut walked: Vec<PathBuf> = Vec::new();
    let mut packages: Vec<Package> = Vec::new();
    let mut seen: BTreeSet<PathBuf> = BTreeSet::new();
    let mut reach = |package: Package, walked: &mut Vec<PathBuf>| {
        if seen.insert(package.source.clone()) {
            walked.extend(package.walked().into_iter().map(&shown));
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
        return Ok((walked, packages, gathered));
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
        let inside = path.canonicalize().is_ok_and(|canonical| {
            canonical.starts_with(package.sources()) || canonical == package.source
        });
        reach(package, &mut walked);
        if !inside {
            walked.push(path);
        }
    }
    Ok((walked, packages, gathered))
}

/// The paths that [`packaged`] gives a verb to walk, the packages that they
/// reach and the workspaces that they gather.
pub type Walked = (Vec<PathBuf>, Vec<Package>, Vec<Gathered>);

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
                "no path given, and no `{PACKAGE}` stands in `{}` or a directory above it, and \
                 no `{WORKSPACE}` above it",
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
    /// `Package.authors`.
    authors: String,
    /// `Package.licence`.
    licence: String,
    /// `Package.documentation`.
    documentation: String,
    /// `Package.endpoint`.
    endpoint: String,
    /// Each module of the package but its root, by its path, in order.
    modules: Vec<String>,
    /// `Package.gandr`, `Package.features` and `Package.systems`.
    toolchain: Toolchain,
    /// `Package.spelling`: a spelling's name, or empty for the reader's own.
    spelling: String,
}

impl Manifest
{
    /// The manifest `program`'s `Package` model states, each of its fields run
    /// to its string, and the modules of `package`.
    ///
    /// # Specification
    /// - requires: `program` is the program of the package's source, and `own`
    ///   the report of the package source's own declarations.
    /// - ensures: each field read by its path among the declarations `own`
    ///   reports, in [`Field`] order, run once, and its string decoded from the
    ///   value's spelling; the first field none of them declares is
    ///   [`Unmanifested::Undeclared`], and the first whose run is no string
    ///   [`Unmanifested::Unstrung`] with what it came to. The toolchain is
    ///   [`Toolchain::read`] of `gandr`, `features` and `systems`, and a
    ///   `gandr` it cannot read is [`Unmanifested::Unconstrained`]. `spelling`
    ///   is empty or a name [`gandr_surface_grammar::Spelling`] reads, and any
    ///   other is [`Unmanifested::Unspelled`]. `sources` is the literal
    ///   [`Package::stated`] holds, else [`Unmanifested::Unstated`], and names
    ///   a directory inside the root, else [`Unmanifested::Outside`]. The
    ///   modules are [`modules`] of `package`'s sources, in order.
    /// - provides: the manifest `gandr check` writes.
    /// - fails: a field undeclared, or run to no string; a `gandr` stating no
    ///   constraint; a `spelling` naming none; a `sources` discovery did not
    ///   read, or naming a directory outside the root.
    /// - panics: none.
    /// - executable: none — each field is run on the program's machine, which a
    ///   predicate could only check by running it again; the witness observes
    ///   each outcome.
    ///
    /// # Errors
    /// The first field that is undeclared, or does not run to a string; a
    /// `gandr` stating no constraint; a `spelling` naming none; a `sources`
    /// discovery did not read, or outside the root.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a model holding every field, one of them escaped,
    ///   reads each; one missing `version` and one whose name is an integer are
    ///   refused at that field; a `gandr` with no `>=` and a `spelling` naming
    ///   no spelling are refused; a computed `sources` and one leaving the root
    ///   are refused.
    /// - witness: `tests::package::a_manifest_reads_the_package_model_2687`
    /// - witness: `tests::package::a_manifest_renders_the_toolchain_its_model_asks_for_3135`
    /// - witness: `tests::package::a_manifest_renders_the_presentation_its_model_names_3135`
    #[inline]
    pub fn of(
        program: &mut Program<'_>,
        own: &SettleReport<'_>,
        package: &Package,
    ) -> Result<Self, Unmanifested>
    {
        let name = strung(program, own, Field::Name)?;
        let version = strung(program, own, Field::Version)?;
        let authors = strung(program, own, Field::Authors)?;
        let licence = strung(program, own, Field::Licence)?;
        let documentation = strung(program, own, Field::Documentation)?;
        let endpoint = strung(program, own, Field::Endpoint)?;
        let gandr = strung(program, own, Field::Gandr)?;
        let features = strung(program, own, Field::Features)?;
        let systems = strung(program, own, Field::Systems)?;
        let toolchain = Toolchain::read(gandr.clone(), Separated(&features), Separated(&systems))
            .map_err(|_unconstrained| Unmanifested::Unconstrained { came: gandr })?;
        let spelling = strung(program, own, Field::Spelling)?;
        if !spelling.is_empty() && spelling.parse::<gandr_surface_grammar::Spelling>().is_err() {
            return Err(Unmanifested::Unspelled { came: spelling });
        }
        let sources = strung(program, own, Field::Sources)?;
        if package.stated().map(Path::as_os_str) != Some(std::ffi::OsStr::new(&sources)) {
            return Err(Unmanifested::Unstated { came: sources });
        }
        if inside(package.root(), Path::new(&sources)).is_none() {
            return Err(Unmanifested::Outside { came: sources });
        }
        Ok(Self {
            name,
            version,
            authors,
            licence,
            documentation,
            endpoint,
            modules: modules(package.sources()).into_keys().collect(),
            toolchain,
            spelling,
        })
    }

    /// What the package's model asks of the toolchain.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn toolchain(&self) -> &Toolchain
    {
        &self.toolchain
    }

    /// The manifest as the checker writes it: the header, then the body.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the [`WRITTEN`] line, the digest line carrying the BLAKE3
    ///   digest of the body in lowercase hexadecimal, then the body: a
    ///   `[package]` table with `name`, `version`, `authors`, `licence`,
    ///   `documentation` and `endpoint` as TOML basic strings, each `"`, `\`
    ///   and control character escaped, and `modules` an array of the modules'
    ///   paths, one per line, in order, or `[]` when there are none, as the
    ///   tree's TOML formatter writes it; then a `[toolchain]` table with
    ///   `gandr` as written and `features` and `systems` arrays of their
    ///   entries, written as `modules` is; then, when `spelling` names one, a
    ///   `[presentation]` table with `spelling`, the table the user's
    ///   configuration file writes. The same manifest renders the same bytes.
    /// - provides: the file [`reconcile`] writes.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a manifest renders its pinned bytes, and one whose
    ///   name holds a quote, a backslash and a newline escapes each.
    /// - witness: `tests::package::a_manifest_renders_its_digest_and_its_table_2687`
    #[spec(ensures: |ref ret| ret.starts_with(WRITTEN)
        && matches!(Split::of(Manifested(ret), Opening(WRITTEN)).authorship(), Authorship::Checker))]
    #[inline]
    #[must_use]
    pub fn render(&self) -> String
    {
        let mut body = format!(
            "\n[package]\nname = {}\nversion = {}\nauthors = {}\nlicence = {}\ndocumentation = \
             {}\nendpoint = {}\nmodules = {}\n",
            Basic(&self.name),
            Basic(&self.version),
            Basic(&self.authors),
            Basic(&self.licence),
            Basic(&self.documentation),
            Basic(&self.endpoint),
            Listed(&self.modules)
        );
        let _written = write!(body, "{}", self.toolchain);
        if !self.spelling.is_empty() {
            let _written = write!(
                body,
                "\n[presentation]\nspelling = {}\n",
                Basic(&self.spelling)
            );
        }
        format!(
            "{WRITTEN}\n{DIGEST}{}\n{body}",
            blake3::hash(body.as_bytes()).to_hex()
        )
    }
}

/// What the model of a workspace states for its manifest, and the members
/// that the workspace names.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct WorkspaceManifest
{
    /// `Workspace.version`.
    version: String,
    /// Each member, as `members` names it, in order.
    members: Vec<String>,
    /// `Workspace.gandr`, `Workspace.features` and `Workspace.systems`.
    toolchain: Toolchain,
}

impl WorkspaceManifest
{
    /// The manifest of a workspace. Its model states `version` and
    /// `toolchain`, and the workspace names `members`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        version: String,
        members: Vec<String>,
        toolchain: Toolchain,
    ) -> Self
    {
        Self {
            version,
            members,
            toolchain,
        }
    }

    /// The manifest as the checker writes it: the header, then the body.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the [`WORKSPACE_WRITTEN`] line comes first. The digest line
    ///   follows. It holds the BLAKE3 digest of the body in lowercase
    ///   hexadecimal. The body follows. It starts with a `[workspace]` table.
    ///   In this table, `version` is a TOML basic string. `members` is an array
    ///   of the members in order, one on each line, as in the `modules` of a
    ///   package manifest. The `[toolchain]` table of a package manifest comes
    ///   last. The same manifest always gives the same bytes.
    /// - provides: the file [`reconcile`] writes beside `workspace.gandr`.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a workspace's model renders its version, its members
    ///   and its toolchain.
    /// - witness: `tests::package::a_workspace_s_packages_share_one_lock_4921`
    #[spec(ensures: |ref ret| ret.starts_with(WORKSPACE_WRITTEN)
        && matches!(Split::of(Manifested(ret), Opening(WORKSPACE_WRITTEN)).authorship(), Authorship::Checker))]
    #[inline]
    #[must_use]
    pub fn render(&self) -> String
    {
        let mut body = format!(
            "\n[workspace]\nversion = {}\nmembers = {}\n",
            Basic(&self.version),
            Listed(&self.members)
        );
        let _written = write!(body, "{}", self.toolchain);
        format!(
            "{WORKSPACE_WRITTEN}\n{DIGEST}{}\n{body}",
            blake3::hash(body.as_bytes()).to_hex()
        )
    }
}

/// The string `field` runs to on `program`, decoded from its spelling.
///
/// # Specification
/// - requires: as [`Manifest::of`].
/// - ensures: the field read by its path among the declarations `own` reports
///   and run once: its value's spelling, a quoted string, its escapes decoded;
///   [`Unmanifested::Undeclared`] when none declares it, and
///   [`Unmanifested::Unstrung`] with what it came to when it runs to anything
///   else.
/// - fails: an undeclared field, or one run to no string.
/// - panics: none.
/// - executable: none — as [`Manifest::of`].
///
/// # Errors
/// [`Unmanifested::Undeclared`] and [`Unmanifested::Unstrung`].
///
/// # Adequacy
/// - hypothesis: L3 — as [`Manifest::of`].
/// - witness: `tests::package::a_manifest_reads_the_package_model_2687`
fn strung(
    program: &mut Program<'_>,
    own: &SettleReport<'_>,
    field: Field,
) -> Result<String, Unmanifested>
{
    let constant = match program.named_among(
        field.path(),
        own.declarations().iter().map(DeclarationReport::constant),
    ) {
        Maybe::Present(constant) => constant,
        Maybe::Absent(declaration_name::Absent::Undeclared) => {
            return Err(Unmanifested::Undeclared(field));
        },
    };
    let came = match program.evaluate(constant) {
        Evaluation::Value(value) => value.to_string(),
        ref other @ (Evaluation::Sealed(_)
        | Evaluation::Blamed(_)
        | Evaluation::Holed { .. }
        | Evaluation::Stuck(_)
        | Evaluation::Unfinished(_)
        | Evaluation::Unrunnable(_)) => {
            return Err(Unmanifested::Unstrung {
                field,
                came: other.to_string(),
            });
        },
    };
    came.strip_prefix('"')
        .and_then(|rest| rest.strip_suffix('"'))
        .map(|content| decode_escapes(SourceFragment::from(content)))
        .ok_or(Unmanifested::Unstrung { field, came })
}

/// A package's address: the BLAKE3 digest of what the package is.
///
/// It digests its items' content keys, every inert component of its models
/// left out (#533 § p2), and its dependencies' addresses (§ p3). It says what
/// the package is, never where it is or what its dependents call it, and no
/// manifest carries it.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct PackageAddress([u8; 32]);

impl core::fmt::Display for PackageAddress
{
    /// The digest in lowercase hexadecimal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        self.0.iter().try_for_each(|byte| write!(f, "{byte:02x}"))
    }
}

/// What a package is: its address, and the key of the interface its root
/// exports.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Identity
{
    /// The package's address.
    pub address: PackageAddress,
    /// The package's signature key.
    pub signature: SignatureKey,
}

impl Package
{
    /// The package's identity: each of its sources, its package source then its
    /// modules in [`modules`] order, read as `shadows` holds it and grouped
    /// into the import-connected components that [`component::group`] lays
    /// out; each component lowered once, its sources' own items keyed on
    /// `fork`; each source's own items digested in admission order as its
    /// path and its content key, a model's inert component left out; then
    /// the addresses `lock`'s pointers read back through `store`; and the
    /// paths the package source exports, keyed.
    ///
    /// # Specification
    /// - requires: `grammar` is the grammar the package's sources are read
    ///   under, `lock` the lock its dependencies resolve to, and `store` the
    ///   store that lock's pointers were committed to.
    /// - ensures: the address is the BLAKE3 digest, over the sources in that
    ///   order and each one's own items in its unit's admission order, of each
    ///   item that is no [`Inertness::Inert`] declaration, as its path's dotted
    ///   spelling prefixed by its length and then its content key's bytes,
    ///   followed by each address of [`Lock::addresses`] read back through
    ///   `store` in order, prefixed by `u64::MAX`. A source's own items are the
    ///   items its component's lowering gives the bytes the source writes. An
    ///   item of an import is the importer's to leave out, so each item enters
    ///   once. The sources are grouped under [`component::Reading::Whole`],
    ///   each import read as [`component::lay_out_shadowed`] reads it. Each
    ///   component is lowered after the prelude's closure
    ///   ([`ClosureLowering::resume`]) when its text lays after the prelude's,
    ///   and whole otherwise, both answering what the whole lowering answers.
    ///   The components are keyed on `fork`, and the calling thread digests
    ///   their items in source order, so the address is the same at every
    ///   width. Equal content at equal paths over equal dependencies is one
    ///   address, whatever the inert fields state and wherever and under
    ///   whatever alias each dependency is found. The signature key is the
    ///   BLAKE3 digest of each dotted path of a [`Visibility::Public`] item the
    ///   package source digests, ascending, prefixed by its length.
    /// - provides: the identity a dependent's lock commits to the store.
    /// - fails: [`Unaddressed`] at the first source, in that order, that does
    ///   not read, whose component does not lower, or one of whose items has no
    ///   key; or at the first dependency whose pointer `store` cannot read
    ///   back.
    /// - panics: none.
    /// - executable: none — the address is a digest of the lowering's content,
    ///   which a predicate could only restate by lowering again; the witnesses
    ///   observe it moving and staying.
    ///
    /// # Errors
    /// [`Unaddressed`]: a source that does not read, a source whose component
    /// does not lower, a declaration of the package the lowering refused, an
    /// item whose content holds an unresolved node, or a dependency whose
    /// pointer `store` cannot read back.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — in a two-source package, an edit to an inert field
    ///   leaves the address and every other item's key where they were, and an
    ///   edit to a content item moves the address; every corpus package's inert
    ///   fields, each edited, leave its address unchanged; every corpus
    ///   package's address, at one thread and at every thread the host gives
    ///   the process, is the digest of each source's own items lowered over the
    ///   source's own closure; a dependency's content edit moves its
    ///   dependent's address, and its inert edit does not; a lock whose pointer
    ///   the store never held leaves the dependent unaddressed by the
    ///   coordinate.
    /// - witness: `tests::package::an_inert_edit_leaves_the_address_and_a_content_edit_moves_it_3030`
    /// - witness: `tests::package::every_corpus_package_s_address_ignores_its_inert_fields_3030`
    /// - witness: `tests::package::every_corpus_package_s_address_digests_each_source_s_closure_at_every_width_6406`
    /// - witness: `tests::package::a_dependency_s_content_edit_drifts_the_lock_until_relocked_3072`
    /// - witness: `tests::package::a_pointer_the_store_cannot_answer_leaves_the_dependent_unaddressed_3157`
    #[inline]
    pub fn identity<F>(
        &self,
        grammar: &Arc<Pbg>,
        shadows: &dyn Shadows,
        lock: &Lock,
        store: &gandr_storage_store::Store,
        fork: &F,
    ) -> Result<Identity, Unaddressed>
    where
        F: Fork,
    {
        let sources: Vec<PathBuf> = core::iter::once(self.source.clone())
            .chain(modules(self.sources()).into_values())
            .collect();
        let mut given = Vec::with_capacity(sources.len());
        // Each source's place among the sources read, or why it does not read.
        let read: Vec<Result<usize, Unaddressed>> = sources
            .iter()
            .map(|source| {
                let text = match shadows.shadowed(source) {
                    Some(text) => String::from(text.as_ref()),
                    None => {
                        std::fs::read_to_string(source).map_err(|error| Unaddressed::Unread {
                            source: source.clone(),
                            message: error.to_string(),
                        })?
                    },
                };
                given.push(Given {
                    path: named_path(source),
                    root: classify(source),
                    text,
                });
                Ok(given.len().saturating_sub(1))
            })
            .collect();
        let grouped = component::group(
            grammar,
            given,
            component::Reading::Whole,
            &BTreeSet::new(),
            shadows,
        );
        let mut keyings: Vec<Keying<'_>> = grouped
            .components
            .iter()
            .map(|laid| Keying {
                component: laid,
                members: laid.members.iter().map(|_| None).collect(),
                fault: None,
            })
            .collect();
        // Only a member that some source is placed at is keyed.
        for placed in &grouped.placed {
            if let Some(slot) = keyings
                .get_mut(placed.component)
                .and_then(|keying| keying.members.get_mut(placed.member))
            {
                *slot = Some(Vec::new());
            }
        }
        let prelude = lower_prelude(grammar);
        fork.each(
            &mut keyings,
            || (),
            |&mut (), keying| keying.key(grammar, prelude.as_ref()),
        );
        let mut hasher = blake3::Hasher::new();
        let mut exported = BTreeSet::new();
        for (position, (source, read)) in sources.iter().zip(read).enumerate() {
            // `group` places every source it is given, at a member of a
            // component it makes.
            let Some(placed) = grouped.placed.get(read?)
            else {
                continue;
            };
            let Some(keying) = keyings.get(placed.component)
            else {
                continue;
            };
            if let Some(ref why) = keying.fault {
                return Err(Unaddressed::Unlowered {
                    source: source.clone(),
                    why: why.clone(),
                });
            }
            let own = keying
                .members
                .get(placed.member)
                .and_then(Option::as_ref)
                .into_iter()
                .flatten();
            for written in own {
                let key = match written.key {
                    Keyed::Present(key) => key,
                    Keyed::Refused => {
                        return Err(Unaddressed::Refused {
                            source: source.clone(),
                            item: written.path.clone(),
                        });
                    },
                    Keyed::Opaque => {
                        return Err(Unaddressed::Opaque {
                            source: source.clone(),
                            item: written.path.clone(),
                        });
                    },
                };
                let length = u64::try_from(written.path.len()).unwrap_or(u64::MAX);
                let _digested = hasher
                    .update(&length.to_le_bytes())
                    .update(written.path.as_bytes());
                key.digest_into(&mut hasher);
                if position == 0 && written.visibility == Visibility::Public {
                    let _fresh = exported.insert(written.path.clone());
                }
            }
        }
        for address in lock.addresses(store)? {
            let _digested = hasher.update(&u64::MAX.to_le_bytes()).update(&address.0);
        }
        let mut signed = blake3::Hasher::new();
        for path in &exported {
            let length = u64::try_from(path.len()).unwrap_or(u64::MAX);
            let _signed = signed.update(&length.to_le_bytes()).update(path.as_bytes());
        }
        Ok(Identity {
            address: PackageAddress(*hasher.finalize().as_bytes()),
            signature: SignatureKey::new(signed.finalize()),
        })
    }
}

/// One component of a package's sources, lowered and keyed for its identity:
/// the items each member that a source is placed at writes, or why the
/// component does not lower.
///
/// # Specification
/// - requires: `members` holds one slot per member of `component`, `Some` at
///   each member a source of the package is placed at.
/// - ensures: after [`Self::key`], `fault` holds why the component does not
///   lower, or each `Some` slot holds its member's own items in admission
///   order.
/// - executable: none — a data type; [`Self::key`] carries the clauses.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Package::identity`].
/// - witness: `tests::package::every_corpus_package_s_address_digests_each_source_s_closure_at_every_width_6406`
#[derive(Debug)]
struct Keying<'grouped>
{
    /// The component.
    component: &'grouped component::Component,
    /// Each member's own items, by the member's place; `None` for a member no
    /// source is placed at.
    members: Vec<Option<Vec<Written>>>,
    /// Why the component does not lower.
    fault: Option<String>,
}

/// One item a source writes, as its component's lowering keys it.
///
/// # Specification
/// trivial.
#[derive(Debug)]
struct Written
{
    /// Its dotted path.
    path: String,
    /// Its content key, or why it has none.
    key: Keyed,
    /// Whether it is public.
    visibility: Visibility,
}

/// An item's content key, or why it has none.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug)]
enum Keyed
{
    /// The key.
    Present(ContentKey),
    /// The lowering refused the declaration.
    Refused,
    /// Its content holds an unresolved node.
    Opaque,
}

impl Keying<'_>
{
    /// Lower the component once under `grammar`, after `prelude` when its text
    /// lays after the prelude's and whole otherwise, and key each item that a
    /// member wanted writes.
    ///
    /// # Specification
    /// - requires: `prelude` is the prelude's closure under `grammar`.
    /// - ensures: what [`lower_unit_source`] makes of the component: a refusal
    ///   or a fault sets `fault` to its text; a module fills each wanted
    ///   member's slot with each declaration whose bytes start in the member
    ///   and that is no [`Inertness::Inert`] one unless refused, in admission
    ///   order, keyed by [`content_key`] or marked refused or opaque.
    /// - fails: never; a fault is held in `fault`.
    /// - panics: none.
    /// - executable: none — the lowering's answer is the clause, which a
    ///   predicate could only restate by lowering again.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Package::identity`].
    /// - witness: `tests::package::every_corpus_package_s_address_digests_each_source_s_closure_at_every_width_6406`
    fn key(
        &mut self,
        grammar: &Pbg,
        prelude: Option<&ClosureLowering>,
    )
    {
        let laid = self.component;
        if let Some(closure) = prelude
            && let Some(own) = laid.text.strip_prefix(<&str>::from(closure.text()))
            && let Ok(alone) = parse(grammar, SourceText::from(own))
            && let Ok(after) = alone.after(closure.tree(), SourceText::from(laid.text.as_str()))
        {
            let tree = after.into_tree();
            let mut arena = CoreArena::new();
            match closure.resume(&tree, &laid.unit, &mut arena, &mut Decisions::none()) {
                Ok(module) => self.file(&module, arena),
                Err(refusal) => self.fault = Some(refusal.to_string()),
            }
            return;
        }
        match lower_unit_source(
            grammar,
            SourceText::from(laid.text.as_str()),
            &laid.unit,
            &mut LoweringCount::default(),
        ) {
            Ok(lowering) => match lowering.into_lowered() {
                Lowered::Module { module, arena } => self.file(&module, arena),
                Lowered::Refused(refusal) => self.fault = Some(refusal.to_string()),
            },
            Err(fault) => self.fault = Some(fault.to_string()),
        }
    }

    /// Key each item of `module` over `arena` that a wanted member writes.
    ///
    /// # Specification
    /// - requires: `module` and `arena` are the component's lowering.
    /// - ensures: as [`Self::key`] for a module; a module whose positions do
    ///   not ascend sets `fault` instead.
    /// - fails: never; a fault is held in `fault`.
    /// - panics: none.
    /// - executable: none — as [`Self::key`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Package::identity`].
    /// - witness: `tests::package::every_corpus_package_s_address_digests_each_source_s_closure_at_every_width_6406`
    fn file(
        &mut self,
        module: &LoweredModule<'_>,
        arena: CoreArena,
    )
    {
        let program = match item_program(module, arena) {
            Ok(program) => program,
            Err(fault) => {
                self.fault = Some(fault.to_string());
                return;
            },
        };
        let laid = self.component;
        let items = program.items().len();
        // Each declaration the lowering did not refuse is the next item.
        let mut ordinal = 0_usize;
        for declaration in module.declarations() {
            let refused = matches!(declaration.outcome(), DeclarationOutcome::Refused(_));
            let item = ordinal;
            if !refused {
                ordinal = ordinal.saturating_add(1);
            }
            let start = declaration.span().start();
            let Some(&mut Some(ref mut written)) = laid
                .members
                .partition_point(|member| member.start <= start)
                .checked_sub(1)
                .filter(|&own| {
                    laid.members
                        .get(own)
                        .is_some_and(|member| start < member.end)
                })
                .and_then(|own| self.members.get_mut(own))
            else {
                continue;
            };
            if !refused && declaration.inertness() == Inertness::Inert {
                continue;
            }
            let key = if refused {
                Keyed::Refused
            }
            else if item < items
                && let Maybe::Present(key) = content_key(&program, ItemOrdinal::from(item))
            {
                Keyed::Present(key)
            }
            else {
                Keyed::Opaque
            };
            let mut path = String::new();
            for (index, segment) in module.path_of(declaration).iter().enumerate() {
                if index > 0 {
                    path.push('.');
                }
                let segment: &str = segment.as_ref();
                path.push_str(segment);
            }
            written.push(Written {
                path,
                key,
                visibility: declaration.visibility(),
            });
        }
    }
}

/// Why a package has no address.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Unaddressed
{
    /// A source of the package could not be read.
    Unread
    {
        /// The source.
        source: PathBuf,
        /// Why it could not be read.
        message: String,
    },
    /// A source of the package does not lower to a module.
    Unlowered
    {
        /// The source.
        source: PathBuf,
        /// Why it does not.
        why: String,
    },
    /// A declaration of the package the lowering refused, which no content
    /// key names.
    Refused
    {
        /// The source declaring it.
        source: PathBuf,
        /// Its path.
        item: String,
    },
    /// An item whose content holds an unresolved node, which no content key
    /// names.
    Opaque
    {
        /// The source declaring it.
        source: PathBuf,
        /// Its path.
        item: String,
    },
    /// A dependency whose locked pointer the store cannot read back as an
    /// identity.
    Unstored
    {
        /// The dependency.
        coordinate: lock::Coordinate,
        /// Why the store cannot.
        fault: Box<gandr_storage_store::StoreError>,
    },
}

impl core::fmt::Display for Unaddressed
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
            Self::Unread {
                ref source,
                ref message,
            } => write!(
                f,
                "`{}` cannot be read, so the package has no address: {message}",
                source.display()
            ),
            Self::Unlowered {
                ref source,
                ref why,
            } => write!(
                f,
                "`{}` does not lower, so the package has no address: {why}",
                source.display()
            ),
            Self::Refused {
                ref source,
                ref item,
            } => write!(
                f,
                "`{item}` in `{}` is refused, so no content key names it and the package has no \
                 address",
                source.display()
            ),
            Self::Opaque {
                ref source,
                ref item,
            } => write!(
                f,
                "`{item}` in `{}` holds an unresolved node, so no content key names it and the \
                 package has no address",
                source.display()
            ),
            Self::Unstored {
                ref coordinate,
                ref fault,
            } => write!(
                f,
                "the dependency `{coordinate}` is locked to a pointer the store cannot read back, so \
                 the package has no address: {fault}; run `gandr lock` to lock it again"
            ),
        }
    }
}

/// Every module the sources under `sources` make but the root, each named by
/// its path from `sources`, `text/greet.gandr` as `text.greet`, beside the
/// source that makes it.
///
/// # Specification
/// - requires: `sources` is a package's sources directory.
/// - ensures: one entry per `.gandr` file under `sources`, its directories and
///   its file stem joined by `.`, the root module `package.gandr` left out when
///   the sources are the root; a directory holding a `package.gandr` of its own
///   is another package's, and nothing under it is named. A directory that does
///   not list names nothing.
/// - provides: the membership the manifest records, a module being a file that
///   nothing declares, and the sources a package's address reads after its
///   package source.
/// - fails: never.
/// - panics: none.
/// - executable: none — the clause reads the file system again.
///
/// # Adequacy
/// - hypothesis: L3 — a package with a nested module and a nested package lists
///   the module alone.
/// - witness: `tests::package::a_manifest_lists_the_modules_its_sources_make_2687`
fn modules(sources: &Path) -> BTreeMap<String, PathBuf>
{
    let mut named = BTreeMap::new();
    let mut pending = Vec::from([sources.to_path_buf()]);
    while let Some(directory) = pending.pop() {
        listed(sources, &directory, &mut pending, &mut named);
    }
    named
}

/// File the entries of `directory`, under the package's `sources`: each
/// directory that holds no package source onto `pending`, and each source but
/// the root's into `named`, by its module path.
///
/// # Specification
/// trivial.
fn listed(
    sources: &Path,
    directory: &Path,
    pending: &mut Vec<PathBuf>,
    named: &mut BTreeMap<String, PathBuf>,
)
{
    let Ok(entries) = std::fs::read_dir(directory)
    else {
        return;
    };
    for path in entries.filter_map(Result::ok).map(|entry| entry.path()) {
        if path.is_dir() {
            if !path.join(PACKAGE).is_file() {
                pending.push(path);
            }
        }
        else if path
            .extension()
            .is_some_and(|extension| extension == "gandr")
            && path != sources.join(PACKAGE)
            && let Some(module) = module_path(sources, &path)
        {
            let _fresh = named.insert(module, path);
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

/// A field of the `Package` model the manifest records, in the order it
/// records them.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Field
{
    /// `Package.name`.
    Name,
    /// `Package.version`.
    Version,
    /// `Package.authors`.
    Authors,
    /// `Package.licence`.
    Licence,
    /// `Package.documentation`.
    Documentation,
    /// `Package.endpoint`.
    Endpoint,
    /// `Package.gandr`.
    Gandr,
    /// `Package.features`.
    Features,
    /// `Package.systems`.
    Systems,
    /// `Package.spelling`.
    Spelling,
    /// `Package.sources`.
    Sources,
}

impl Field
{
    /// The field's path from the package source's top level.
    ///
    /// # Specification
    /// trivial.
    fn path(self) -> SurfaceName<'static>
    {
        SurfaceName::from(match self {
            Self::Name => "Package.name",
            Self::Version => "Package.version",
            Self::Authors => "Package.authors",
            Self::Licence => "Package.licence",
            Self::Documentation => "Package.documentation",
            Self::Endpoint => "Package.endpoint",
            Self::Gandr => "Package.gandr",
            Self::Features => "Package.features",
            Self::Systems => "Package.systems",
            Self::Spelling => "Package.spelling",
            Self::Sources => "Package.sources",
        })
    }
}

/// Why a package source's model gives no manifest.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Unmanifested
{
    /// The package source declares no such field.
    Undeclared(Field),
    /// The field does not run to a string.
    Unstrung
    {
        /// The field.
        field: Field,
        /// What its run came to, spelled.
        came: String,
    },
    /// The package source's `Package.gandr` states no constraint the check
    /// reads.
    Unconstrained
    {
        /// What it runs to.
        came: String,
    },
    /// The package source's `Package.spelling` names no spelling.
    Unspelled
    {
        /// What it runs to.
        came: String,
    },
    /// The package source's `Package.sources` runs to another string than the
    /// literal discovery read off its tokens, or the model writes it as no
    /// string literal: discovery resolves imports through it before any source
    /// is checked.
    Unstated
    {
        /// What it runs to.
        came: String,
    },
    /// The package source's `Package.sources` names no directory inside the
    /// package's root.
    Outside
    {
        /// What it runs to.
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
                "the package source declares no `{}`, so no `{MANIFEST}` is written: import `std.build` \
                 and declare `module Package : Model(Gandr.Package)` in it",
                field.path()
            ),
            Self::Unstrung { field, ref came } => write!(
                f,
                "`{}` runs to `{came}`, not to a string, so no `{MANIFEST}` is written",
                field.path()
            ),
            Self::Unconstrained { ref came } => write!(
                f,
                "`{}` is `{came}`, which states no constraint, so no `{MANIFEST}` is written: \
                 write `>= <major>.<minor>`, or nothing for any version",
                Field::Gandr.path()
            ),
            Self::Unspelled { ref came } => write!(
                f,
                "`{}` is `{came}`, which names no spelling, so no `{MANIFEST}` is written: \
                 write `unicode` or `ascii`, or nothing for the reader's own",
                Field::Spelling.path()
            ),
            Self::Unstated { ref came } => write!(
                f,
                "`{}` runs to `{came}`, which no string literal states, so no `{MANIFEST}` is \
                 written: write it as `def {SOURCES} = \"<directory>\";`",
                Field::Sources.path()
            ),
            Self::Outside { ref came } => write!(
                f,
                "`{}` is `{came}`, which names no directory inside the package's root, so no \
                 `{MANIFEST}` is written: write a path below the root, `src`, or `.` for the \
                 root",
                Field::Sources.path()
            ),
        }
    }
}

/// What [`reconcile`] did to a file the checker writes.
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

/// A file the checker writes from a model: the line it opens with, its
/// render, and how [`reconcile`] answers each way the file may stand.
pub trait Held
{
    /// Why the file was left as it stands.
    type Fault;

    /// The line the file opens with when the checker wrote it.
    const OPENING: &'static str;

    /// The file as the checker writes it.
    ///
    /// # Specification
    /// trivial.
    fn rendered(&self) -> String;

    /// Whether an absent file is written.
    ///
    /// # Specification
    /// trivial.
    fn absent(&self) -> Absence;

    /// The fault for a file whose header does not carry its body's digest.
    ///
    /// # Specification
    /// trivial.
    fn edited(&self) -> Self::Fault;

    /// What a file the checker wrote, whose text is not the render, is, from
    /// its `body` below the header.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// The file's fault, when it is left as it stands.
    fn differing(
        &self,
        body: Body<'_>,
    ) -> Result<Differing, Self::Fault>;

    /// The fault for a file that cannot be read or written.
    ///
    /// # Specification
    /// trivial.
    fn unreadable(error: io::Error) -> Self::Fault;
}

/// The body of a file the checker wrote: everything below its header.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct Body<'file>(&'file str);

/// Whether [`reconcile`] writes a held file where none stands.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Absence
{
    /// The render is written.
    Written,
    /// Nothing is written: the model states nothing the file would record.
    Left,
}

/// What [`reconcile`] does with a file the checker wrote whose text is not
/// the render.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Differing
{
    /// The file reads as the model: it is kept.
    Kept,
    /// The file states another model: the render overwrites it.
    Rewritten,
}

/// Bring the file at `path` to `held`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: an absent file is written with [`Held::rendered`] and is
///   [`Reconciled::Written`], or is [`Reconciled::Unchanged`] where
///   [`Held::absent`] leaves it. A file whose header, opening with
///   [`Held::OPENING`], does not carry its body's digest is left as it stands,
///   [`Held::edited`]. A file that is the render is [`Reconciled::Unchanged`].
///   Any other is as [`Held::differing`] answers from its body: kept and
///   [`Reconciled::Unchanged`], overwritten with the render and
///   [`Reconciled::Rewritten`], or left as it stands with its fault.
/// - provides: the step of `gandr check` that holds the manifest and the lock
///   to their models.
/// - fails: an edited file, a fault [`Held::differing`] answers, or a file that
///   cannot be read or written ([`Held::unreadable`]).
/// - panics: none.
/// - executable: none — the clause is about the file, which a predicate could
///   only check by reading it again after the write; the witnesses observe each
///   case on disk.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — an absent manifest is written; the written file is
///   unchanged on a second run; a model change rewrites it; a hand edit to its
///   body, and a file with no header, are each refused and left byte for byte;
///   an absent lock is written and unchanged on a second run; a content edit to
///   a dependency is drift until relocked.
/// - witness: `tests::package::a_manifest_is_written_rewritten_and_refused_as_drift_2687`
/// - witness: `tests::package::a_lock_is_written_once_and_reads_alike_from_anywhere_3072`
/// - witness: `tests::package::a_dependency_s_content_edit_drifts_the_lock_until_relocked_3072`
#[inline]
pub fn reconcile<H>(
    path: &Path,
    held: &H,
) -> Result<Reconciled, H::Fault>
where
    H: Held + ?Sized,
{
    let standing = match std::fs::read_to_string(path) {
        Ok(standing) => standing,
        Err(error) if error.kind() == io::ErrorKind::NotFound => {
            return match held.absent() {
                Absence::Left => Ok(Reconciled::Unchanged),
                Absence::Written => std::fs::write(path, held.rendered())
                    .map(|()| Reconciled::Written)
                    .map_err(H::unreadable),
            };
        },
        Err(error) => return Err(H::unreadable(error)),
    };
    let split = Split::of(Manifested(&standing), Opening(H::OPENING));
    if matches!(split.authorship(), Authorship::Hand) {
        return Err(held.edited());
    }
    let rendered = held.rendered();
    if standing == rendered {
        return Ok(Reconciled::Unchanged);
    }
    match held.differing(Body(split.body))? {
        Differing::Kept => Ok(Reconciled::Unchanged),
        Differing::Rewritten => std::fs::write(path, rendered)
            .map(|()| Reconciled::Rewritten)
            .map_err(H::unreadable),
    }
}

/// The manifest: a file the checker writes from the `Package` model, which a
/// model change rewrites.
impl Held for Manifest
{
    type Fault = ManifestFault;

    const OPENING: &'static str = WRITTEN;

    /// # Specification
    /// trivial.
    #[inline]
    fn rendered(&self) -> String
    {
        self.render()
    }

    /// # Specification
    /// trivial.
    #[inline]
    fn absent(&self) -> Absence
    {
        Absence::Written
    }

    /// # Specification
    /// trivial.
    #[inline]
    fn edited(&self) -> ManifestFault
    {
        ManifestFault::Drifted
    }

    /// # Specification
    /// trivial.
    #[inline]
    fn differing(
        &self,
        _body: Body<'_>,
    ) -> Result<Differing, ManifestFault>
    {
        Ok(Differing::Rewritten)
    }

    /// # Specification
    /// trivial.
    #[inline]
    fn unreadable(error: io::Error) -> ManifestFault
    {
        ManifestFault::Io(error)
    }
}

/// The manifest of a workspace: a file that the checker writes from the
/// `Workspace` model. A change to the model rewrites the file, as for the
/// manifest of a package.
impl Held for WorkspaceManifest
{
    type Fault = ManifestFault;

    const OPENING: &'static str = WORKSPACE_WRITTEN;

    /// # Specification
    /// trivial.
    #[inline]
    fn rendered(&self) -> String
    {
        self.render()
    }

    /// # Specification
    /// trivial.
    #[inline]
    fn absent(&self) -> Absence
    {
        Absence::Written
    }

    /// # Specification
    /// trivial.
    #[inline]
    fn edited(&self) -> ManifestFault
    {
        ManifestFault::Drifted
    }

    /// # Specification
    /// trivial.
    #[inline]
    fn differing(
        &self,
        _body: Body<'_>,
    ) -> Result<Differing, ManifestFault>
    {
        Ok(Differing::Rewritten)
    }

    /// # Specification
    /// trivial.
    #[inline]
    fn unreadable(error: io::Error) -> ManifestFault
    {
        ManifestFault::Io(error)
    }
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

/// The line a file the checker wrote opens with.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Opening(&'static str);

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
    /// `file` split at its header, which opens with `opening`.
    ///
    /// # Specification
    /// trivial.
    fn of(
        file: Manifested<'file>,
        opening: Opening,
    ) -> Self
    {
        let Manifested(text) = file;
        let headed = text
            .strip_prefix(opening.0)
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

/// Strings written as a TOML array, in order: `[]` when there are none, else
/// one line per string, each a basic string indented two spaces and followed
/// by a comma, between `[` and `]` on lines of their own.
#[repr(transparent)]
struct Listed<'strings, Item>(&'strings [Item])
where
    Item: AsRef<str>;

impl<Item> core::fmt::Display for Listed<'_, Item>
where
    Item: AsRef<str>,
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
        for string in self.0 {
            writeln!(f, "  {},", Basic(string.as_ref()))?;
        }
        f.write_char(']')
    }
}
