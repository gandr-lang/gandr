//! A tree of the repository as git holds it: the tool of a kind and the
//! sources that its values read.
//!
//! A tree is a commit, or the work tree with its changes, which a run writes
//! as a tree object through an index of its own. Each read of a tree is one
//! `git ls-tree`, and the contents of the sources that a run computes come
//! from one `git cat-file --batch`.

use core::fmt;
use std::io::BufRead as _;
use std::io::BufReader;
use std::io::Read as _;
use std::io::Write as _;
use std::path::Path;
use std::path::PathBuf;
use std::process::Command;
use std::process::Stdio;

use anodized::spec;
use gandr_workflow_output_store::Digest;

/// Why a tree could not be read.
///
/// # Specification
/// - provides: one variant for each refusal; each names the command.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TreeError
{
    /// A `git` command could not run, failed, or wrote what is not UTF-8.
    Git
    {
        /// The arguments of the command.
        command: String,
        /// The refusal.
        detail: String,
    },
}

impl fmt::Display for TreeError
{
    /// Writes one line that names the command and the refusal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::Git {
                ref command,
                ref detail,
            } => write!(f, "git {command}: {detail}"),
        }
    }
}

/// A refusal is an error value, so a caller can return it.
impl core::error::Error for TreeError
{
}

/// A source that a value reads: its name in the corpus and the git object
/// identifier of its content.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Source
{
    /// The name: `strict/` and the path below the strict root, or `fixture/`
    /// and the path below the fixture root.
    pub name: String,
    /// The git object identifier of the content, in hexadecimal.
    pub object: String,
}

/// A tree of the repository: the git tree identifier of its root.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Tree
{
    /// The repository that holds the tree.
    repository: PathBuf,
    /// The git tree identifier.
    id: String,
}

/// The root of the strict sources, and the prefix of their names.
const STRICT: (&str, &str) = ("crates/surface-corpus/strict/", "strict/");

/// The root of the fixture sources, and the prefix of their names.
const FIXTURE: (&str, &str) = ("corpus/", "fixture/");

/// The directories below the fixture root that hold no source that a value
/// reads: the ledgers and the sketch set.
const FIXTURE_HELD_OUT: [&str; 2] = ["corpus/ledger/", "corpus/sketch/"];

/// The roots of the sources that state refusals: the pathological twins,
/// and one exemplar for each refusal name.
const REFUSING: [&str; 2] = ["corpus/pathological/", "corpus/ledger/diagnostics/"];

/// The paths at the root that a refusal reads: the corpus, the library, and
/// the workspace of the library with its lock.
const REFUSAL_INPUTS: [&str; 5] = [
    "corpus",
    "library",
    "workspace.gandr",
    "workspace.gandr.lock",
    "workspace.gandr.toml",
];

impl Tree
{
    /// The git tree identifier of the tree, in hexadecimal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn id(&self) -> &str
    {
        &self.id
    }

    /// The tree of the commit `revision` in `repository`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`TreeError::Git`] when `revision` names no commit.
    #[inline]
    pub fn of_revision(
        repository: &Path,
        revision: &str,
    ) -> Result<Self, TreeError>
    {
        let id = git(repository, &[], &[
            "rev-parse",
            &format!("{revision}^{{tree}}"),
        ])?;
        Ok(Self {
            repository: repository.to_path_buf(),
            id: id.trim().to_owned(),
        })
    }

    /// The tree of the work tree of `repository`, its changes included: each
    /// file that git does not ignore, written through an index below
    /// `scratch`. The index starts as a copy of the index of the repository,
    /// so git hashes only the files that changed.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`TreeError::Git`] when git cannot read the work tree.
    #[inline]
    pub fn of_work_tree(
        repository: &Path,
        scratch: &Path,
    ) -> Result<Self, TreeError>
    {
        let index = scratch.join(format!("outputs-index.{}", std::process::id()));
        let index_text = index.display().to_string();
        let environment = [("GIT_INDEX_FILE", index_text.as_str())];
        let own = git(repository, &[], &["rev-parse", "--git-path", "index"])?;
        let copied = std::fs::create_dir_all(scratch)
            .and_then(|()| std::fs::copy(repository.join(own.trim()), &index));
        let started = match copied {
            Ok(_) => Ok(String::new()),
            Err(_) => git(repository, &environment, &["read-tree", "HEAD"]),
        };
        let written = started
            .and_then(|_| git(repository, &environment, &["add", "--all", "--", "."]))
            .and_then(|_| git(repository, &environment, &["write-tree"]));
        let _removed = std::fs::remove_file(&index);
        Ok(Self {
            repository: repository.to_path_buf(),
            id: written?.trim().to_owned(),
        })
    }

    /// The digest of the tool of a kind in this tree.
    ///
    /// The parts are the git tree identifier of each directory of
    /// `packages`, in the order given, the manifest of each directory of
    /// `manifests`, then the root manifest, the lock and the toolchain file.
    /// The packages are those that compute the kind. The manifests are those
    /// of each package that builds the binary: a manifest can turn a feature
    /// of a package of the kind on.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`TreeError::Git`] when git cannot list the tree.
    #[inline]
    pub fn tool(
        &self,
        packages: &[&str],
        manifests: &[&str],
    ) -> Result<Digest, TreeError>
    {
        let listed = git(&self.repository, &[], &[
            "ls-tree",
            "-z",
            &self.id,
            "--",
            "crates/",
            "Cargo.toml",
            "Cargo.lock",
            "rust-toolchain.toml",
        ])?;
        let paths: Vec<String> = manifests
            .iter()
            .map(|package| format!("crates/{package}/Cargo.toml"))
            .collect();
        let mut arguments = vec!["ls-tree", "-z", self.id.as_str(), "--"];
        arguments.extend(paths.iter().map(String::as_str));
        let features = if paths.is_empty() {
            String::new()
        }
        else {
            git(&self.repository, &[], &arguments)?
        };
        let entries: Vec<(&str, &str)> = listed
            .split('\0')
            .filter_map(|entry| {
                let (head, path) = entry.split_once('\t')?;
                Some((path, head.rsplit(' ').next()?))
            })
            .collect();
        let object = |path: &str| {
            entries
                .iter()
                .find(|&&(listed, _)| listed == path)
                .map_or(b"".as_slice(), |&(_, object)| object.as_bytes())
        };
        let directories: Vec<String> = packages
            .iter()
            .map(|package| format!("crates/{package}"))
            .collect();
        let parts = directories
            .iter()
            .map(|directory| object(directory))
            .chain(["Cargo.toml", "Cargo.lock", "rust-toolchain.toml"].map(object))
            .chain([features.as_bytes()]);
        Ok(Digest::of_parts(parts))
    }

    /// The corpus sources of this tree, in name order: each `.gandr` file
    /// below the strict root and below the fixture root, outside the ledgers
    /// and the sketch set, and not a symbolic link.
    ///
    /// # Specification
    /// - ensures: the sources are in name order.
    ///
    /// # Errors
    /// [`TreeError::Git`] when git cannot list the tree.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a strict source, a fixture source, a source of the
    ///   ledgers and a file that is not a source give the first two, and the
    ///   work tree gives a source that no commit holds.
    /// - witness: `tree::tests::the_sources_are_the_gandr_files_outside_the_held_out_directories`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |sources| sources.is_sorted()))]
    #[inline]
    pub fn sources(&self) -> Result<Vec<Source>, TreeError>
    {
        self.below(&[STRICT.0, FIXTURE.0], &FIXTURE_HELD_OUT)
    }

    /// The sources of this tree that state refusals, in name order: each
    /// `.gandr` file below the pathological twins and below the exemplars of
    /// the refusal names, and not a symbolic link.
    ///
    /// # Specification
    /// - ensures: the sources are in name order.
    ///
    /// # Errors
    /// [`TreeError::Git`] when git cannot list the tree.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a pathological source and an exemplar of a refusal
    ///   name are refusing sources, and a model source and a source of another
    ///   ledger are not.
    /// - witness: `tree::tests::the_refusing_sources_are_the_twins_and_the_exemplars`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |sources| sources.is_sorted()))]
    #[inline]
    pub fn refusing(&self) -> Result<Vec<Source>, TreeError>
    {
        self.below(&REFUSING, &[])
    }

    /// The git objects that a refusal of this tree reads, as git lists them.
    ///
    /// They are the corpus, the library, and the workspace of the library
    /// with its lock. Two trees with one such text give each refusing source
    /// one refusal.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`TreeError::Git`] when git cannot list the tree.
    #[inline]
    pub fn refusal_inputs(&self) -> Result<String, TreeError>
    {
        let mut arguments = vec!["ls-tree", "-z", self.id.as_str(), "--"];
        arguments.extend(REFUSAL_INPUTS);
        git(&self.repository, &[], &arguments)
    }

    /// Each `.gandr` file below `roots` and outside `held_out` that is not a
    /// symbolic link, in name order.
    ///
    /// The name of a file below the strict root starts with `strict/`, and
    /// of a file below the corpus with `fixture/`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`TreeError::Git`] when git cannot list the tree.
    fn below(
        &self,
        roots: &[&str],
        held_out: &[&str],
    ) -> Result<Vec<Source>, TreeError>
    {
        let mut arguments = vec!["ls-tree", "-r", "-z", self.id.as_str(), "--"];
        arguments.extend(roots);
        let listed = git(&self.repository, &[], &arguments)?;
        let mut sources: Vec<Source> = listed
            .split('\0')
            .filter_map(|entry| {
                let (head, path) = entry.split_once('\t')?;
                let mut fields = head.split(' ');
                let mode = fields.next()?;
                let object = fields.nth(1)?;
                if mode == "120000"
                    || Path::new(path)
                        .extension()
                        .is_none_or(|extension| extension != "gandr")
                    || held_out.iter().any(|held| path.starts_with(held))
                {
                    return None;
                }
                let name = [STRICT, FIXTURE].iter().find_map(|&(root, prefix)| {
                    path.strip_prefix(root)
                        .map(|below| format!("{prefix}{below}"))
                })?;
                Some(Source {
                    name,
                    object: object.to_owned(),
                })
            })
            .collect();
        sources.sort();
        Ok(sources)
    }

    /// The contents of the objects `objects`, in their order, from one
    /// `git cat-file --batch`.
    ///
    /// # Specification
    /// - ensures: one content for each object.
    ///
    /// # Errors
    /// [`TreeError::Git`] when git cannot read an object.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the content of each source equals the text that the
    ///   tree holds.
    /// - witness: `tree::tests::the_sources_are_the_gandr_files_outside_the_held_out_directories`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |contents| contents.len() == objects.len()))]
    #[inline]
    pub fn contents(
        &self,
        objects: &[&str],
    ) -> Result<Vec<Vec<u8>>, TreeError>
    {
        let refused = |detail: String| TreeError::Git {
            command: String::from("cat-file --batch"),
            detail,
        };
        let mut child = Command::new("git")
            .arg("-C")
            .arg(&self.repository)
            .args(["cat-file", "--batch"])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()
            .map_err(|error| refused(error.to_string()))?;
        let mut asked = String::new();
        for object in objects {
            asked.push_str(object);
            asked.push('\n');
        }
        let stdin = child.stdin.take();
        let writer =
            std::thread::spawn(move || stdin.map(|mut stdin| stdin.write_all(asked.as_bytes())));
        let mut reader = BufReader::new(
            child
                .stdout
                .take()
                .ok_or_else(|| refused(String::from("no output")))?,
        );
        let mut contents = Vec::with_capacity(objects.len());
        let mut header = String::new();
        for _ in objects {
            header.clear();
            let _read = reader
                .read_line(&mut header)
                .map_err(|error| refused(error.to_string()))?;
            let size: usize = header
                .trim_end()
                .rsplit(' ')
                .next()
                .and_then(|size| size.parse().ok())
                .ok_or_else(|| {
                    refused(format!("the header `{}` names no size", header.trim_end()))
                })?;
            let mut content = vec![0; size];
            reader
                .read_exact(&mut content)
                .map_err(|error| refused(error.to_string()))?;
            let mut newline = [0_u8; 1];
            reader
                .read_exact(&mut newline)
                .map_err(|error| refused(error.to_string()))?;
            contents.push(content);
        }
        let _written = writer.join();
        let _status = child.wait();
        Ok(contents)
    }
}

/// The output of `git` with `arguments` in `repository`, under the variables
/// `environment`.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`TreeError::Git`] when git cannot run, fails, or writes what is not
/// UTF-8.
fn git(
    repository: &Path,
    environment: &[(&str, &str)],
    arguments: &[&str],
) -> Result<String, TreeError>
{
    let refused = |detail: String| TreeError::Git {
        command: arguments.join(" "),
        detail,
    };
    let output = Command::new("git")
        .arg("-C")
        .arg(repository)
        .args(arguments)
        .envs(environment.iter().copied())
        .stdin(Stdio::null())
        .output()
        .map_err(|error| refused(error.to_string()))?;
    if !output.status.success() {
        return Err(refused(
            String::from_utf8_lossy(&output.stderr).trim().to_owned(),
        ));
    }
    String::from_utf8(output.stdout).map_err(|error| refused(error.to_string()))
}

/// A repository below the temporary directory, named by `name` and the
/// process, that holds `files` in one commit.
///
/// # Specification
/// trivial.
///
/// # Panics
/// When git cannot make the repository.
#[cfg(test)]
pub(crate) fn scratch_repository(
    name: &str,
    files: &[(&str, &str)],
) -> PathBuf
{
    let root = std::env::temp_dir().join(format!("gandr-outputs-{name}-{}", std::process::id()));
    let _removed = std::fs::remove_dir_all(&root);
    for &(path, text) in files {
        let file = root.join(path);
        std::fs::create_dir_all(file.parent().expect("a file has a directory"))
            .expect("the directory is made");
        std::fs::write(file, text).expect("the file is written");
    }
    let commit = [
        "-c",
        "user.name=outputs",
        "-c",
        "user.email=outputs@example.invalid",
        "-c",
        "commit.gpgsign=false",
        "commit",
        "-q",
        "-m",
        "sources",
    ];
    for arguments in [&["init", "-q"][..], &["add", "--all"][..], &commit[..]] {
        let status = Command::new("git")
            .arg("-C")
            .arg(&root)
            .args(arguments)
            .status()
            .expect("git runs");
        assert!(status.success(), "git {arguments:?} makes the repository");
    }
    root
}

#[cfg(test)]
mod tests
{
    use super::Tree;
    use super::scratch_repository;

    /// A source that parses whole.
    const WHOLE: &str = include_str!("compute/fixtures/a-definition-of-one.gandr");

    /// A source that stops in an open parenthesis.
    const CUT: &str =
        include_str!("compute/unformatted/a-definition-that-stops-in-a-parenthesis.gandr");

    /// A strict source, a fixture source, a source of the ledgers and a file
    /// that is not a source give the first two, in name order, and the work
    /// tree gives a source that no commit holds.
    #[test]
    fn the_sources_are_the_gandr_files_outside_the_held_out_directories()
    {
        let root = scratch_repository("tree", &[
            ("crates/surface-corpus/strict/values.gandr", WHOLE),
            ("corpus/model/circle.gandr", CUT),
            ("corpus/ledger/syntax/rule.gandr", WHOLE),
            ("corpus/model/notes.md", "notes\n"),
        ]);
        let tree = Tree::of_revision(&root, "HEAD").expect("the commit has a tree");
        let sources = tree.sources().expect("the tree lists");
        let names: Vec<&str> = sources.iter().map(|source| source.name.as_str()).collect();
        assert_eq!(names, ["fixture/model/circle.gandr", "strict/values.gandr"]);
        let objects: Vec<&str> = sources
            .iter()
            .map(|source| source.object.as_str())
            .collect();
        let contents = tree.contents(&objects).expect("the objects read");
        assert_eq!(contents, [
            CUT.as_bytes().to_vec(),
            WHOLE.as_bytes().to_vec()
        ]);
        std::fs::write(root.join("corpus/model/new.gandr"), WHOLE).expect("the file is written");
        let scratch = root.join(".git");
        let work = Tree::of_work_tree(&root, &scratch).expect("the work tree has a tree");
        assert_eq!(work.sources().expect("the tree lists").len(), 3);
        std::fs::remove_dir_all(root).expect("the repository is removed");
    }

    /// A pathological source and an exemplar of a refusal name are refusing
    /// sources. A model source and a source of another ledger are not. The
    /// inputs of a refusal change with a file of the library.
    #[test]
    fn the_refusing_sources_are_the_twins_and_the_exemplars()
    {
        let root = scratch_repository("refusing", &[
            ("corpus/pathological/circuit/cyclic.gandr", CUT),
            ("corpus/ledger/diagnostics/unclosed.gandr", CUT),
            ("corpus/ledger/syntax/rule.gandr", WHOLE),
            ("corpus/model/circle.gandr", WHOLE),
            ("library/std/one.gandr", WHOLE),
        ]);
        let tree = Tree::of_revision(&root, "HEAD").expect("the commit has a tree");
        let sources = tree.refusing().expect("the tree lists");
        let names: Vec<&str> = sources.iter().map(|source| source.name.as_str()).collect();
        assert_eq!(names, [
            "fixture/ledger/diagnostics/unclosed.gandr",
            "fixture/pathological/circuit/cyclic.gandr"
        ]);
        let inputs = tree.refusal_inputs().expect("the tree lists");
        std::fs::write(root.join("library/std/one.gandr"), CUT).expect("the file is written");
        let work = Tree::of_work_tree(&root, &root.join(".git")).expect("the work tree has a tree");
        assert_ne!(inputs, work.refusal_inputs().expect("the tree lists"));
        assert_eq!(sources, work.refusing().expect("the tree lists"));
        std::fs::remove_dir_all(root).expect("the repository is removed");
    }
}
