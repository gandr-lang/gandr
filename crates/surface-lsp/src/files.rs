//! The path table: every source under the workspace's roots, each named once
//! by a stable id, with the files it imports and the names it declares, so the
//! sources that import a file, and the names no open document's closure
//! reaches, are lookups.
//!
//! A root is a folder a client opened, resolved once, when it is added, and
//! held while any connection holds it open; a folder inside another root is
//! walked from the outer. The sources under the roots are reached when an
//! answer needs them ([`Files::importers`], [`Files::declared`]), not at the
//! connection's start, so a session that never asks pays nothing; a source is
//! reached as `gandr check` reaches one, by the dispatcher's [`Traversal`]: a
//! directory depth-first in byte order, its `.gandr` entries, no link in a
//! listing followed. Each source keeps the files its imports name
//! ([`imports_named`]), read from its import forms without judging it, and,
//! once an answer has asked for names, the names its outline declares
//! ([`declared`]), read from one parse and no lowering; with them the length
//! and modification time its file had when they were read: an answer reads
//! again only a source whose file differs from its stamp, so the table is
//! current whether or not anything watches the roots. A source the last walk
//! did not reach keeps its id and imports and declares nothing.
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
use gandr_surface_dispatcher::Reached;
use gandr_surface_dispatcher::Traversal;
use gandr_surface_dispatcher::imports_named;
use gandr_surface_dispatcher::named_path;
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

/// A path the table names: a source under a root, or a file one imports.
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

/// Every source under the workspace's roots, with the files each imports.
///
/// # Specification
/// - requires: nothing.
/// - ensures: each path the table names has one id, and the id names that path
///   for the table's life; each source reached under a root holds the files its
///   file imported when its stamp was taken.
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

    /// The roots a walk starts from: each root no other root holds, ascending.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: every root is under exactly one root answered, and no root
    ///   answered is under another.
    /// - fails: never.
    /// - panics: none.
    /// - intension: one pass over the roots in path order, which places every
    ///   root directly after the root holding it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a folder opened inside another is walked once, from
    ///   the outer, and from itself once the outer is withdrawn.
    /// - witness: `files::tests::a_root_is_walked_while_a_connection_holds_it_open`
    #[spec(ensures: |ret| ret.windows(2).all(|pair| matches!(pair, [first, second] if !second.starts_with(first))))]
    fn outermost(&self) -> Vec<PathBuf>
    {
        let mut outermost: Vec<PathBuf> = Vec::new();
        for root in self.roots.keys() {
            if outermost.last().is_some_and(|held| root.starts_with(held)) {
                continue;
            }
            outermost.push(root.clone());
        }
        outermost
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

    /// Reach every source under the roots, reading again the imports, and
    /// once an answer has asked for them the names, of each whose file differs
    /// from its stamp.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: each `.gandr` source the dispatcher's traversal reaches under
    ///   a root holds what its file imports and that file's stamp, read again
    ///   only when the stamp differs; once the table is naming, what its file
    ///   declares too, read when the stamp differs or its names were not yet
    ///   read; one that cannot be read imports and declares nothing; a source
    ///   reached before and not now has no stamp and imports and declares
    ///   nothing.
    /// - fails: never; a source that cannot be read imports nothing.
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
        let mut traversal = Traversal::new(self.outermost());
        let mut text = String::new();
        while let Maybe::Present(found) = traversal.reach() {
            if !matches!(found, Reached::Source) {
                continue;
            }
            let path = traversal.take_path();
            let id = self.id(&path);
            let _reached = reached.insert(id);
            let stamp = std::fs::metadata(&path).ok().map(|metadata| Stamp {
                length: metadata.len(),
                modified: metadata.modified().ok(),
            });
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
    /// - ensures: each source the walk reaches under a root, once, with the
    ///   names [`declared`] reads off its file as it now reads; a source that
    ///   cannot be read declares nothing. The table names from now on: every
    ///   later walk reads a changed source's names with its imports.
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
}

#[cfg(test)]
mod tests
{
    use alloc::string::String;
    use alloc::vec::Vec;
    use std::path::PathBuf;

    use gandr_surface_grammar::built_in;

    use super::Files;
    use crate::protocol::DocumentUri;
    use crate::protocol::FileRename;
    use crate::relocate::Moves;
    use crate::server::Peer;

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
                "data Nat : Type {\n  Zero : Nat;\n  Succ : (n : Nat) --> Nat;\n}\n",
            ),
            (
                "deeper/mid.gandr",
                "import \"../base.gandr\" ;\ndef two : Nat ;\ndef two = Succ(Succ(Zero)) ;\n",
            ),
            ("lone.gandr", "def four : Integer ;\ndef four = 4 ;\n"),
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
                named("lone.gandr", &["four"])
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
                named("lone.gandr", &["five", "six"])
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
            "a folder inside an open one is walked once, from the outer"
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
            "once no connection holds the outer folder open, only the inner is walked"
        );
        files.depart(first);
        assert_eq!(
            files.importers(&grammar, &at("base.gandr"), &[]),
            Vec::<PathBuf>::new(),
            "with no root left, nothing is walked"
        );
        let _removed = std::fs::remove_dir_all(&directory);
    }
}
