//! The path table holds every source of the projects that the workspace's
//! folders root. The table gives each path one stable id. For each source, the
//! table keeps the files that the source imports and the names that it
//! declares. Thus the sources that import a file are one lookup. The names that
//! no closure of an open document reaches are one lookup too.
//!
//! A root is a folder that a client opens. The table resolves a root once, when
//! the client adds it. The table keeps the root while a connection holds it
//! open. Each root contributes the project that it roots:
//!
//! - A folder that holds `package.gandr` contributes that package.
//! - Else, a folder that holds `workspace.gandr` contributes that workspace and
//!   each member that it names.
//! - Any other folder contributes nothing. The server judges a file in it only
//!   while an editor holds the file.
//!
//! The table reaches the sources only when an answer needs them. Thus a session
//! that asks nothing pays nothing. [`Files::importers`] and [`Files::declared`]
//! are the answers that need the sources. The table reaches a source as
//! `gandr check` does, with the dispatcher's [`Traversal`]. The traversal goes
//! depth-first through a directory in byte order, takes its `.gandr` entries
//! and follows no link.
//!
//! For each source, the table keeps the files that its imports name. The table
//! reads them from the import forms with [`imports_named`]. It does not judge
//! the source. After an answer asks for names, the table also keeps the names
//! that the outline of each source declares. It reads them with [`declared`],
//! from one parse and no lowering. With them, it keeps a stamp: the length and
//! the modification time of the file at that read.
//!
//! An answer reads a source again only when its file differs from its stamp.
//! Thus the table is current, whether or not a watcher reports changes. A
//! source that the last walk did not reach keeps its id. It imports nothing and
//! declares nothing.
//!
//! The table reads the disk. An importer an editor holds imports what its
//! editor's copy writes, which the server passes where it asks, so an unsaved
//! import is followed and an import an editor deleted is not.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::collections::VecDeque;
use alloc::vec::Vec;
use std::path::Path;
use std::path::PathBuf;
use std::time::SystemTime;

use anodized::spec;
use gandr_surface_dispatcher::PACKAGE;
use gandr_surface_dispatcher::Package;
use gandr_surface_dispatcher::Reached;
use gandr_surface_dispatcher::Traversal;
use gandr_surface_dispatcher::WORKSPACE;
use gandr_surface_dispatcher::Workspace;
use gandr_surface_dispatcher::imports_named;
use gandr_surface_dispatcher::named_path;
use gandr_surface_dispatcher::package_root;
use gandr_surface_dispatcher::workspace_root;
use gandr_surface_grammar::Pbg;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use crate::relocate::Moves;
use crate::search::Declared;
use crate::search::declared;
use crate::server::Peer;

/// A source's place in the table, stable while the table lives.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct FileId(usize);

/// What a source's file was when its imports were read: its length and its
/// modification time, where the platform keeps one.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Stamp
{
    /// The file's length in bytes.
    length: u64,
    /// When the file was last modified.
    modified: Option<SystemTime>,
}

/// The [`Stamp`] of the file at `path` now. None when the metadata of the file
/// is not readable.
///
/// # Specification
/// trivial.
fn stamped(path: &Path) -> Option<Stamp>
{
    std::fs::metadata(path).ok().map(|metadata| Stamp {
        length: metadata.len(),
        modified: metadata.modified().ok(),
    })
}

/// A path in the table: a source of the project of a root, or a file that a
/// source imports.
#[derive(Debug)]
struct Named
{
    /// The path.
    path: PathBuf,
    /// What its file was when its imports were read; none for a path the last
    /// walk did not reach as a source.
    stamp: Option<Stamp>,
    /// The files its imports name, as last read.
    imports: Vec<FileId>,
    /// The names its file declared when its imports were read; none until an
    /// answer has asked for names, and for a path the last walk did not
    /// reach.
    declared: Option<Vec<Declared>>,
}

/// The table of every source of the projects that the workspace's folders
/// root, with the files that each source imports.
///
/// # Specification
/// - requires: nothing.
/// - ensures: each path in the table has one id for the life of the table. Each
///   source that the project of a root reaches holds the files that its file
///   imported at its stamp.
/// - panics: none.
/// - executable: none — this state carrier has no call boundary; its methods
///   carry the executable clauses.
///
/// # Adequacy
/// - hypothesis: L3 — a source importing a file, one importing that importer,
///   an editor's copy, a source rewritten to import nothing and one removed
///   each answer as a file's importers do.
/// - witness: `files::tests::a_file_s_importers_are_every_source_reaching_it`
#[derive(Debug, Default)]
pub struct Files
{
    /// The roots, each resolved once, with the connections holding it open.
    roots: BTreeMap<PathBuf, BTreeSet<Peer>>,
    /// For each root that holds a workspace source, the members that the
    /// source names and the stamp of the source at that read. A read of the
    /// members runs the source. Thus the table reads them again only when the
    /// source changes.
    workspaces: BTreeMap<PathBuf, (Option<Stamp>, Vec<Package>)>,
    /// Each path the table names, by its id.
    named: Vec<Named>,
    /// The id of each path the table names.
    ids: BTreeMap<PathBuf, FileId>,
    /// Whether an answer has asked for the names the sources declare, after
    /// which every source read is read for its names too.
    naming: bool,
}

impl Files
{
    /// Add `root`, resolved now, as a folder `peer` opened.
    ///
    /// # Specification
    /// trivial.
    pub fn root(
        &mut self,
        peer: Peer,
        root: &Path,
    )
    {
        let _opened = self.roots.entry(named_path(root)).or_default().insert(peer);
    }

    /// Withdraw `root`, resolved now, as a folder `peer` opened; the root goes
    /// once no connection holds it open.
    ///
    /// # Specification
    /// trivial.
    pub fn unroot(
        &mut self,
        peer: Peer,
        root: &Path,
    )
    {
        let root = named_path(root);
        if let Some(openers) = self.roots.get_mut(&root) {
            let _closed = openers.remove(&peer);
            if openers.is_empty() {
                let _gone = self.roots.remove(&root);
            }
        }
    }

    /// Withdraw every root `peer` opened, as its connection ends.
    ///
    /// # Specification
    /// trivial.
    pub fn depart(
        &mut self,
        peer: Peer,
    )
    {
        self.roots.retain(|_, openers| {
            let _closed = openers.remove(&peer);
            !openers.is_empty()
        });
    }

    /// The paths where a walk starts. These are the paths of the project of
    /// each root, in ascending order of the roots. Each path occurs once.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: for each root in ascending order, the paths that its project
    ///   walks. A path that an earlier root gave does not occur again.
    /// - fails: never.
    /// - panics: none.
    /// - intension: one discovery for each root. The table reads the members of
    ///   a workspace again only when the stamp of its source changes.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a package folder walks its package source and its
    ///   sources and no sibling directory. A workspace folder walks its source
    ///   and its members. A folder that holds neither walks nothing. A
    ///   withdrawn root walks nothing more.
    /// - witness: `files::tests::a_folder_walks_the_project_it_roots_and_nothing_beside_it`
    /// - witness: `files::tests::a_root_is_walked_while_a_connection_holds_it_open`
    #[spec(ensures: |ret| ret.iter().enumerate().all(|(at, path)| !ret.iter().take(at).any(|before| before == path)))]
    fn walked(&mut self) -> Vec<PathBuf>
    {
        let roots: Vec<PathBuf> = self.roots.keys().cloned().collect();
        let mut seen: BTreeSet<PathBuf> = BTreeSet::new();
        let mut walked: Vec<PathBuf> = Vec::new();
        for root in roots {
            for path in self.project(&root) {
                if seen.insert(path.clone()) {
                    walked.push(path);
                }
            }
        }
        walked
    }

    /// The paths that the project at `root` walks. A folder that holds
    /// `package.gandr` gives the paths of that package. Else, a folder that
    /// holds `workspace.gandr` gives that source, then each member package in
    /// the order of its `members`. Any other folder gives nothing.
    ///
    /// # Specification
    /// - requires: `root` is canonical.
    /// - ensures: when `root` holds [`PACKAGE`], [`Package::walked`] of the
    ///   package at `root`. Else, when `root` holds [`WORKSPACE`], that source,
    ///   then [`Package::walked`] of each package that [`Workspace::members`]
    ///   names and that still roots at its directory. The table reads the
    ///   members again only when the stamp of the source changes. When the
    ///   members are not readable, the source alone. Else nothing, and the
    ///   table keeps no members for `root`.
    /// - fails: never. A workspace with members that are not readable walks its
    ///   source alone.
    /// - panics: none.
    /// - intension: one metadata read for each root file. The members run once
    ///   for each change of the workspace source.
    /// - executable: none — the clauses read the disk, and a predicate would
    ///   read it again.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as for [`Files::walked`].
    /// - witness: `files::tests::a_folder_walks_the_project_it_roots_and_nothing_beside_it`
    fn project(
        &mut self,
        root: &Path,
    ) -> Vec<PathBuf>
    {
        let walked = |package: &Package| {
            package
                .walked()
                .into_iter()
                .map(Path::to_path_buf)
                .collect::<Vec<_>>()
        };
        if root.join(PACKAGE).is_file() {
            let _gone = self.workspaces.remove(root);
            return match Package::discover(root) {
                Maybe::Present(package) => walked(&package),
                Maybe::Absent(package_root::Absent::Unpackaged) => Vec::new(),
            };
        }
        let source = root.join(WORKSPACE);
        let stamp = stamped(&source);
        if stamp.is_none() {
            let _gone = self.workspaces.remove(root);
            return Vec::new();
        }
        if self.workspaces.get(root).is_none_or(|held| held.0 != stamp) {
            let members = match Workspace::discover(root) {
                Maybe::Present(workspace) if workspace.root() == root => {
                    workspace.members().unwrap_or_default()
                },
                Maybe::Present(_) | Maybe::Absent(workspace_root::Absent::Unworkspaced) => {
                    Vec::new()
                },
            };
            let _read = self.workspaces.insert(root.to_path_buf(), (stamp, members));
        }
        let mut paths = Vec::from([source]);
        for member in self
            .workspaces
            .get(root)
            .into_iter()
            .flat_map(|held| &held.1)
        {
            if let Maybe::Present(package) = Package::discover(member.root())
                && package.root() == member.root()
            {
                paths.extend(walked(&package));
            }
        }
        paths
    }

    /// The root holding `path`, if one does.
    ///
    /// # Specification
    /// trivial.
    pub fn root_of(
        &self,
        path: &Path,
    ) -> Option<&Path>
    {
        self.roots
            .keys()
            .find(|root| path.starts_with(root))
            .map(PathBuf::as_path)
    }

    /// The folder `peer` opened that holds `path`, if one does.
    ///
    /// # Specification
    /// trivial.
    pub fn opened_by(
        &self,
        peer: Peer,
        path: &Path,
    ) -> Option<&Path>
    {
        self.roots
            .iter()
            .find(|&(root, openers)| openers.contains(&peer) && path.starts_with(root))
            .map(|(root, _)| root.as_path())
    }

    /// The id of `path`, named now when the table names it not yet.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the id the table already gives `path`, else a fresh one, one
    ///   past the last, naming `path` with no stamp and no imports.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a source and the files it imports are each named once
    ///   across answers, so an importer found twice is listed once.
    /// - witness: `files::tests::a_file_s_importers_are_every_source_reaching_it`
    #[spec(ensures: |ret| self.named.get(ret.0).is_some_and(|named| named.path == path))]
    fn id(
        &mut self,
        path: &Path,
    ) -> FileId
    {
        if let Some(&id) = self.ids.get(path) {
            return id;
        }
        let id = FileId(self.named.len());
        self.named.push(Named {
            path: path.to_path_buf(),
            stamp: None,
            imports: Vec::new(),
            declared: None,
        });
        let _named = self.ids.insert(path.to_path_buf(), id);
        id
    }

    /// Reach every source of the projects of the roots. For each source with a
    /// file that differs from its stamp, read the imports again. After an
    /// answer asks for names, read the names again too.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the dispatcher's traversal starts from the paths that
    ///   [`Files::walked`] gives. Each `.gandr` source that it reaches holds
    ///   what its file imports and the stamp of that file. The table reads them
    ///   again only when the stamp differs. When the table is naming, the
    ///   source also holds what its file declares. The table reads the names
    ///   when the stamp differs or when it has no names yet. A source that is
    ///   not readable imports nothing and declares nothing. A source that the
    ///   last walk reached and this walk does not reach has no stamp. It
    ///   imports nothing and declares nothing.
    /// - fails: never. A source that is not readable imports nothing.
    /// - panics: none.
    /// - intension: one listing per directory and one metadata read per source;
    ///   a source's text is read only when its stamp moved or its names are
    ///   owed.
    /// - executable: none — the clause would walk the roots again.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a source rewritten, one added in a new folder and one
    ///   removed between answers each answer as their file now reads.
    /// - witness: `files::tests::a_file_s_importers_are_every_source_reaching_it`
    /// - witness: `files::tests::the_names_a_source_declares_follow_its_file`
    fn refreshed(
        &mut self,
        grammar: &Pbg,
    )
    {
        let naming = self.naming;
        let mut reached = BTreeSet::new();
        let mut traversal = Traversal::new(self.walked());
        let mut text = String::new();
        while let Maybe::Present(found) = traversal.reach() {
            if !matches!(found, Reached::Source) {
                continue;
            }
            let path = traversal.take_path();
            let id = self.id(&path);
            let _reached = reached.insert(id);
            let stamp = stamped(&path);
            if self
                .named
                .get(id.0)
                .is_some_and(|named| named.stamp == stamp && (!naming || named.declared.is_some()))
            {
                continue;
            }
            text.clear();
            let read = stamp.is_some()
                && std::fs::File::open(&path)
                    .and_then(|mut file| std::io::Read::read_to_string(&mut file, &mut text))
                    .is_ok();
            let named = if read {
                imports_named(grammar, &path, SourceText::from(text.as_str()))
            }
            else {
                Vec::new()
            };
            let mut imports = Vec::with_capacity(named.len());
            for imported in &named {
                imports.push(self.id(imported));
            }
            let names = naming.then(|| {
                if read {
                    declared(SourceText::from(text.as_str()))
                }
                else {
                    Vec::new()
                }
            });
            if let Some(held) = self.named.get_mut(id.0) {
                held.stamp = stamp.filter(|_| read);
                held.imports = imports;
                held.declared = names;
            }
        }
        for (index, named) in self.named.iter_mut().enumerate() {
            if named.stamp.is_some() && !reached.contains(&FileId(index)) {
                named.stamp = None;
                named.imports.clear();
                named.declared = None;
            }
        }
    }

    /// Every source under the roots with the names its file declares, the
    /// roots reached first.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: each source that the walk reaches in the projects of the
    ///   roots, once, with the names that [`declared`] reads from its file now.
    ///   A source that is not readable declares nothing. After this call, the
    ///   table is naming. Each later walk reads the names of a changed source
    ///   with its imports.
    /// - provides: the names a workspace-symbol request finds beyond the open
    ///   documents' closures.
    /// - fails: never.
    /// - panics: none.
    /// - intension: one walk of the roots; a source's text is read only when
    ///   its stamp moved since its names were read, or never was.
    /// - executable: none — the clause would walk the roots again.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a source's names, its names after it is rewritten,
    ///   and a removed source's absence each answer as the disk now reads.
    /// - witness: `files::tests::the_names_a_source_declares_follow_its_file`
    pub fn declared(
        &mut self,
        grammar: &Pbg,
    ) -> impl Iterator<Item = (&Path, &[Declared])>
    {
        self.naming = true;
        self.refreshed(grammar);
        self.named.iter().filter_map(|named| {
            named
                .stamp
                .and(named.declared.as_deref())
                .map(|names| (named.path.as_path(), names))
        })
    }

    /// Every source whose imports reach the file at `path`, directly or
    /// through another source, the roots reached first; each source `held`
    /// lists, one an editor holds, imports the files listed beside it in
    /// place of what its file imports.
    ///
    /// # Specification
    /// - requires: `path`, and every path `held` lists, is named as
    ///   [`named_path`] names it.
    /// - ensures: each source whose imports, as `held` lists them for a source
    ///   it lists and as its file holds them otherwise, lead to `path` through
    ///   one import or more, ascending; `path` itself only when a cycle leads
    ///   back to it.
    /// - fails: never.
    /// - panics: none.
    /// - intension: one pass over the imports to invert them, then one
    ///   breadth-first walk; recursion-free.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a direct and a transitive importer, an editor's copy
    ///   importing the file and a source importing nothing each answer as
    ///   stated.
    /// - witness: `files::tests::a_file_s_importers_are_every_source_reaching_it`
    #[spec(ensures: |ret| ret.windows(2).all(|pair| pair.first() < pair.get(1)))]
    pub fn importers(
        &mut self,
        grammar: &Pbg,
        path: &Path,
        held: &[(PathBuf, Vec<PathBuf>)],
    ) -> Vec<PathBuf>
    {
        self.refreshed(grammar);
        let target = self.id(path);
        let mut overrides: BTreeMap<FileId, Vec<FileId>> = BTreeMap::new();
        for &(ref copy, ref imported) in held {
            let ids = imported.iter().map(|imported| self.id(imported)).collect();
            let _held = overrides.insert(self.id(copy), ids);
        }
        let mut importers: Vec<Vec<FileId>> = alloc::vec![Vec::new(); self.named.len()];
        for (index, named) in self.named.iter().enumerate() {
            let importer = FileId(index);
            for imported in overrides.get(&importer).unwrap_or(&named.imports) {
                if let Some(list) = importers.get_mut(imported.0) {
                    list.push(importer);
                }
            }
        }
        let mut found = BTreeSet::new();
        let mut queue = VecDeque::from([target]);
        while let Some(next) = queue.pop_front() {
            for &importer in importers.get(next.0).into_iter().flatten() {
                if found.insert(importer) {
                    queue.push_back(importer);
                }
            }
        }
        let mut paths: Vec<PathBuf> = found
            .into_iter()
            .filter_map(|id| self.named.get(id.0).map(|named| named.path.clone()))
            .collect();
        paths.sort_unstable();
        paths
    }

    /// Every source under the roots that `moves` moves, or whose file imports
    /// a file `moves` moves, the roots reached first, ascending.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: each source the last walk reached whose path, or a path its
    ///   file imports, [`Moves::moved`] moves, ascending and once each; a
    ///   source reaching a moved file only through another source is not
    ///   listed.
    /// - fails: never.
    /// - panics: none.
    /// - intension: one walk of the roots, then one pass over the table.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a source importing a moved file, the moved file
    ///   itself and a source importing it only through another are each
    ///   answered as stated.
    /// - witness: `files::tests::a_move_touches_its_file_and_the_files_importing_it`
    #[spec(ensures: |ret| ret.windows(2).all(|pair| pair.first() < pair.get(1)))]
    pub fn touching(
        &mut self,
        grammar: &Pbg,
        moves: &Moves,
    ) -> Vec<PathBuf>
    {
        self.refreshed(grammar);
        let moved = |id: &FileId| {
            self.named
                .get(id.0)
                .is_some_and(|named| moves.moved(&named.path).is_some())
        };
        let mut paths: Vec<PathBuf> = self
            .named
            .iter()
            .enumerate()
            .filter(|&(index, named)| {
                named.stamp.is_some() && (moved(&FileId(index)) || named.imports.iter().any(&moved))
            })
            .map(|(_, named)| named.path.clone())
            .collect();
        paths.sort_unstable();
        paths
    }

    /// Every source the walk reaches under the roots, the roots reached first,
    /// ascending.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: each `.gandr` source the dispatcher's traversal reaches under
    ///   a root whose file could be read, once, ascending.
    /// - provides: the sources a workspace's diagnostics report.
    /// - fails: never.
    /// - panics: none.
    /// - intension: one walk of the roots, then one pass over the table.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the list holds a source of the project of a root and
    ///   a source in a new folder of that project. It does not hold a removed
    ///   source.
    /// - witness: `server::tests::a_workspace_pull_reports_each_source_no_editor_holds_1824`
    #[spec(ensures: |ret| ret.windows(2).all(|pair| pair.first() < pair.get(1)))]
    pub fn sources(
        &mut self,
        grammar: &Pbg,
    ) -> Vec<PathBuf>
    {
        self.refreshed(grammar);
        let mut paths: Vec<PathBuf> = self
            .named
            .iter()
            .filter(|named| named.stamp.is_some())
            .map(|named| named.path.clone())
            .collect();
        paths.sort_unstable();
        paths
    }
}

#[cfg(test)]
mod tests
{
    use alloc::string::String;
    use alloc::vec::Vec;
    use std::path::Path;
    use std::path::PathBuf;

    use gandr_surface_grammar::built_in;

    use super::Files;
    use crate::protocol::DocumentUri;
    use crate::protocol::FileRename;
    use crate::relocate::Moves;
    use crate::server::Peer;

    /// A package source. Its sources are in its own directory.
    const ROOTED: &str = "// The scratch package. Its sources are in its directory.\n";

    #[test]
    fn a_file_s_importers_are_every_source_reaching_it()
    {
        let grammar = built_in().expect("the grammar builds");
        let directory = std::env::temp_dir().join(format!("gandr-files-{}", std::process::id()));
        let _cleared = std::fs::remove_dir_all(&directory);
        std::fs::create_dir_all(directory.join("deeper")).expect("the scratch tree is created");
        let directory =
            std::fs::canonicalize(&directory).expect("the scratch directory canonicalises");
        let base = "def one : Integer ;\ndef one = 1 ;\n";
        let mid = "import \"../base.gandr\" ;\ndef two : Integer ;\ndef two = one ;\n";
        let top = "import \"./deeper/mid.gandr\" ;\ndef three : Integer ;\ndef three = two ;\n";
        let lone = "def four : Integer ;\ndef four = 4 ;\n";
        let at = |file: &str| directory.join(file);
        for (file, text) in [
            ("base.gandr", base),
            ("deeper/mid.gandr", mid),
            ("top.gandr", top),
            ("lone.gandr", lone),
            ("package.gandr", ROOTED),
        ] {
            std::fs::write(at(file), text).expect("the source is written");
        }
        let mut files = Files::default();
        files.root(Peer::from(1_u64), &directory);
        assert_eq!(
            files.importers(&grammar, &at("base.gandr"), &[]),
            [at("deeper/mid.gandr"), at("top.gandr")],
            "the importer and its own importer reach the base"
        );
        let edited = [(at("lone.gandr"), Vec::from([at("base.gandr")]))];
        assert_eq!(
            files.importers(&grammar, &at("base.gandr"), &edited),
            [at("deeper/mid.gandr"), at("lone.gandr"), at("top.gandr")],
            "an editor's copy importing the base reaches it, its file not"
        );
        std::fs::write(
            at("deeper/mid.gandr"),
            "def two : Integer ;\ndef two = 2 ;\n",
        )
        .expect("the source is rewritten");
        assert_eq!(
            files.importers(&grammar, &at("base.gandr"), &[]),
            Vec::<PathBuf>::new(),
            "a source rewritten to import nothing reaches nothing, nor does its importer"
        );
        std::fs::write(at("deeper/mid.gandr"), mid).expect("the source is restored");
        std::fs::create_dir_all(at("added")).expect("a folder is added");
        std::fs::write(
            at("added/later.gandr"),
            "import \"../deeper/mid.gandr\" ;\ndef five : Integer ;\ndef five = two ;\n",
        )
        .expect("a source is added");
        assert_eq!(
            files.importers(&grammar, &at("base.gandr"), &[]),
            [
                at("added/later.gandr"),
                at("deeper/mid.gandr"),
                at("top.gandr")
            ],
            "a source added since the last answer is reached"
        );
        std::fs::remove_file(at("deeper/mid.gandr")).expect("the source is removed");
        assert_eq!(
            files.importers(&grammar, &at("base.gandr"), &[]),
            Vec::<PathBuf>::new(),
            "a source removed imports nothing"
        );
        let _removed = std::fs::remove_dir_all(&directory);
    }

    #[test]
    fn the_names_a_source_declares_follow_its_file()
    {
        let grammar = built_in().expect("the grammar builds");
        let directory = std::env::temp_dir().join(format!("gandr-declared-{}", std::process::id()));
        let _cleared = std::fs::remove_dir_all(&directory);
        std::fs::create_dir_all(directory.join("deeper")).expect("the scratch tree is created");
        let directory =
            std::fs::canonicalize(&directory).expect("the scratch directory canonicalises");
        let at = |file: &str| directory.join(file);
        for (file, text) in [
            (
                "base.gandr",
                "data Nat : Type where {\n  | Zero : Nat\n  | Succ : (n : Nat) --> Nat\n}\n",
            ),
            (
                "deeper/mid.gandr",
                "import \"../base.gandr\" ;\ndef two : Nat ;\ndef two = Succ(Succ(Zero)) ;\n",
            ),
            ("lone.gandr", "def four : Integer ;\ndef four = 4 ;\n"),
            ("package.gandr", ROOTED),
        ] {
            std::fs::write(at(file), text).expect("the source is written");
        }
        let mut files = Files::default();
        files.root(Peer::from(1_u64), &directory);
        let _importers = files.importers(&grammar, &at("base.gandr"), &[]);
        let names = |files: &mut Files| -> Vec<(PathBuf, Vec<String>)> {
            let mut names: Vec<(PathBuf, Vec<String>)> = files
                .declared(&grammar)
                .map(|(path, declared)| {
                    (
                        path.to_path_buf(),
                        declared.iter().map(|name| name.name.clone()).collect(),
                    )
                })
                .collect();
            names.sort_unstable();
            names
        };
        let named = |file: &str, declared: &[&str]| {
            (
                at(file),
                declared
                    .iter()
                    .copied()
                    .map(String::from)
                    .collect::<Vec<_>>(),
            )
        };
        assert_eq!(
            names(&mut files),
            [
                named("base.gandr", &["Nat", "Zero", "Succ"]),
                named("deeper/mid.gandr", &["two"]),
                named("lone.gandr", &["four"]),
                named("package.gandr", &[])
            ],
            "each source's names, a family's constructors among them, read though its imports \
             were read before any names were asked for"
        );
        std::fs::write(
            at("lone.gandr"),
            "def five : Integer ;\ndef five = 5 ;\ndef six : Integer ;\ndef six = 6 ;\n",
        )
        .expect("the source is rewritten");
        std::fs::remove_file(at("deeper/mid.gandr")).expect("the source is removed");
        assert_eq!(
            names(&mut files),
            [
                named("base.gandr", &["Nat", "Zero", "Succ"]),
                named("lone.gandr", &["five", "six"]),
                named("package.gandr", &[])
            ],
            "a rewritten source declares what its file now does, a removed one nothing"
        );
        let _removed = std::fs::remove_dir_all(&directory);
    }

    #[test]
    fn a_move_touches_its_file_and_the_files_importing_it()
    {
        let grammar = built_in().expect("the grammar builds");
        let directory = std::env::temp_dir().join(format!("gandr-touching-{}", std::process::id()));
        let _cleared = std::fs::remove_dir_all(&directory);
        std::fs::create_dir_all(directory.join("deeper")).expect("the scratch tree is created");
        let directory =
            std::fs::canonicalize(&directory).expect("the scratch directory canonicalises");
        let at = |file: &str| directory.join(file);
        for (file, text) in [
            ("base.gandr", "def one : Integer ;\ndef one = 1 ;\n"),
            (
                "deeper/mid.gandr",
                "import \"../base.gandr\" ;\ndef two : Integer ;\ndef two = one ;\n",
            ),
            (
                "top.gandr",
                "import \"./deeper/mid.gandr\" ;\ndef three : Integer ;\ndef three = two ;\n",
            ),
            ("lone.gandr", "def four : Integer ;\ndef four = 4 ;\n"),
            ("package.gandr", ROOTED),
        ] {
            std::fs::write(at(file), text).expect("the source is written");
        }
        let renamed = |from: &str, to: &str| {
            let uri = |file: &str| DocumentUri::of_path(&at(file)).expect("the path is a URI");
            Moves::of(&[FileRename {
                old_uri: uri(from),
                new_uri: uri(to),
            }])
        };
        let mut files = Files::default();
        files.root(Peer::from(1_u64), &directory);
        assert_eq!(
            files.touching(&grammar, &renamed("base.gandr", "moved.gandr")),
            [at("base.gandr"), at("deeper/mid.gandr")],
            "the moved file and its importer are touched, its importer's importer not"
        );
        assert_eq!(
            files.touching(&grammar, &renamed("deeper", "renamed")),
            [at("deeper/mid.gandr"), at("top.gandr")],
            "a file under a moved folder and its importer are touched"
        );
        assert_eq!(
            files.touching(&grammar, &renamed("lone.gandr", "alone.gandr")),
            [at("lone.gandr")],
            "a moved file nothing imports touches itself alone"
        );
        let _cleared = std::fs::remove_dir_all(&directory);
    }

    #[test]
    fn a_root_is_walked_while_a_connection_holds_it_open()
    {
        let grammar = built_in().expect("the grammar builds");
        let directory = std::env::temp_dir().join(format!("gandr-roots-{}", std::process::id()));
        let _cleared = std::fs::remove_dir_all(&directory);
        std::fs::create_dir_all(directory.join("deeper")).expect("the scratch tree is created");
        let directory =
            std::fs::canonicalize(&directory).expect("the scratch directory canonicalises");
        let at = |file: &str| directory.join(file);
        for (file, text) in [
            ("base.gandr", "def one : Integer ;\ndef one = 1 ;\n"),
            (
                "deeper/mid.gandr",
                "import \"../base.gandr\" ;\ndef two : Integer ;\ndef two = one ;\n",
            ),
            (
                "top.gandr",
                "import \"./base.gandr\" ;\ndef three : Integer ;\ndef three = one ;\n",
            ),
            ("package.gandr", ROOTED),
            ("deeper/package.gandr", ROOTED),
        ] {
            std::fs::write(at(file), text).expect("the source is written");
        }
        let (first, second) = (Peer::from(1_u64), Peer::from(2_u64));
        let mut files = Files::default();
        files.root(first, &directory);
        files.root(second, &directory);
        files.root(first, &at("deeper"));
        assert_eq!(
            files.importers(&grammar, &at("base.gandr"), &[]),
            [at("deeper/mid.gandr"), at("top.gandr")],
            "a package folder in an open folder adds no source that the outer walk holds"
        );
        files.unroot(first, &directory);
        assert_eq!(
            files.importers(&grammar, &at("base.gandr"), &[]),
            [at("deeper/mid.gandr"), at("top.gandr")],
            "a folder another connection holds open stays a root"
        );
        files.depart(second);
        assert_eq!(
            files.importers(&grammar, &at("base.gandr"), &[]),
            [at("deeper/mid.gandr")],
            "when no connection holds the outer folder open, the walk covers the inner package only"
        );
        files.depart(first);
        assert_eq!(
            files.importers(&grammar, &at("base.gandr"), &[]),
            Vec::<PathBuf>::new(),
            "with no root left, nothing is walked"
        );
        let _removed = std::fs::remove_dir_all(&directory);
    }

    #[test]
    fn a_folder_walks_the_project_it_roots_and_nothing_beside_it()
    {
        let grammar = built_in().expect("the grammar builds");
        let directory = std::env::temp_dir().join(format!("gandr-projects-{}", std::process::id()));
        let _cleared = std::fs::remove_dir_all(&directory);
        for folder in ["package/src", "package/corpus", "loose"] {
            std::fs::create_dir_all(directory.join(folder)).expect("the scratch tree is created");
        }
        let directory =
            std::fs::canonicalize(&directory).expect("the scratch directory canonicalises");
        let at = |file: &str| directory.join(file);
        for (file, text) in [
            (
                "package/package.gandr",
                "pub module Package where {\n  def sources = \"src\";\n}\n",
            ),
            (
                "package/src/one.gandr",
                "def one : Integer ;\ndef one = 1 ;\n",
            ),
            (
                "package/corpus/beside.gandr",
                "def two : Integer ;\ndef two = 2 ;\n",
            ),
            (
                "loose/three.gandr",
                "def three : Integer ;\ndef three = 3 ;\n",
            ),
        ] {
            std::fs::write(at(file), text).expect("the source is written");
        }
        let peer = Peer::from(1_u64);
        let mut files = Files::default();
        files.root(peer, &at("package"));
        files.root(peer, &at("loose"));
        assert_eq!(
            files.walked(),
            [at("package/package.gandr"), at("package/src")],
            "a package folder walks its package source and its sources. A folder with no root \
             file walks nothing."
        );
        assert_eq!(
            files.sources(&grammar),
            [at("package/package.gandr"), at("package/src/one.gandr")],
            "the walk reaches no source outside the package's sources and no source in a folder \
             with no root file"
        );
        files.depart(peer);
        let projects = std::fs::canonicalize(
            Path::new(env!("CARGO_MANIFEST_DIR")).join("../../corpus/model/projects"),
        )
        .expect("the corpus's workspace canonicalises");
        files.root(peer, &projects);
        assert_eq!(
            files.walked(),
            [
                projects.join("workspace.gandr"),
                projects.join("hello/package.gandr"),
                projects.join("hello/src"),
                projects.join("tools"),
            ],
            "a workspace folder walks its source, then each member that it names, in order"
        );
        files.depart(peer);
        assert_eq!(
            files.walked(),
            Vec::<PathBuf>::new(),
            "a withdrawn root walks nothing"
        );
        let _removed = std::fs::remove_dir_all(&directory);
    }
}
