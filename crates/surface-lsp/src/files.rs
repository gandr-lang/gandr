//! The path table: every source under the workspace's roots, each named once
//! by a stable id, with the files it imports, so the sources that import a
//! file are a lookup.
//!
//! A root is a folder the client opened, resolved once, when it is added. The
//! sources under it are reached when an answer needs them
//! ([`Files::importers`]), not at the connection's start, so a session that
//! never asks pays nothing; a source is reached as `gandr check` reaches one,
//! by the dispatcher's [`Traversal`]: a directory depth-first in byte order,
//! its `.gandr` entries, no link in a listing followed. Each source keeps the
//! files its imports name ([`imports_named`]), read from its import forms
//! without judging it, and the length and modification time its file had when
//! they were read: an answer reads again only a source whose file differs from
//! its stamp, so the table is current whether or not anything watches the
//! roots. A source the last walk did not reach keeps its id and imports
//! nothing.
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
    /// The roots, each resolved once.
    roots: Vec<PathBuf>,
    /// Each path the table names, by its id.
    named: Vec<Named>,
    /// The id of each path the table names.
    ids: BTreeMap<PathBuf, FileId>,
}

impl Files
{
    /// Add `root`, resolved now, unless a root held already holds it.
    ///
    /// # Specification
    /// trivial.
    pub fn root(
        &mut self,
        root: &Path,
    )
    {
        let root = named_path(root);
        if self.roots.iter().any(|held| root.starts_with(held)) {
            return;
        }
        self.roots.push(root);
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
            .iter()
            .find(|root| path.starts_with(root))
            .map(PathBuf::as_path)
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
        });
        let _named = self.ids.insert(path.to_path_buf(), id);
        id
    }

    /// Reach every source under the roots, reading again the imports of each
    /// whose file differs from its stamp.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: each `.gandr` source the dispatcher's traversal reaches under
    ///   a root holds what its file imports and that file's stamp, read again
    ///   only when the stamp differs; one that cannot be read imports nothing;
    ///   a source reached before and not now has no stamp and imports nothing.
    /// - fails: never; a source that cannot be read imports nothing.
    /// - panics: none.
    /// - intension: one listing per directory and one metadata read per source;
    ///   a source's text is read only when its stamp moved.
    /// - executable: none — the clause would walk the roots again.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a source rewritten, one added in a new folder and one
    ///   removed between answers each answer as their file now reads.
    /// - witness: `files::tests::a_file_s_importers_are_every_source_reaching_it`
    fn refreshed(
        &mut self,
        grammar: &Pbg,
    )
    {
        let mut reached = BTreeSet::new();
        let mut traversal = Traversal::new(self.roots.clone());
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
                .is_some_and(|named| named.stamp == stamp)
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
            if let Some(held) = self.named.get_mut(id.0) {
                held.stamp = stamp.filter(|_| read);
                held.imports = imports;
            }
        }
        for (index, named) in self.named.iter_mut().enumerate() {
            if named.stamp.is_some() && !reached.contains(&FileId(index)) {
                named.stamp = None;
                named.imports.clear();
            }
        }
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
}

#[cfg(test)]
mod tests
{
    use alloc::vec::Vec;
    use std::path::PathBuf;

    use gandr_surface_grammar::built_in;

    use super::Files;

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
        files.root(&directory);
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
}
