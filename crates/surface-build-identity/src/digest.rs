//! The digest of what one library of the workspace compiles.
//!
//! The build script reads this module, and the tests of the crate read it
//! too. The library compiles it only for its tests, so the driver carries none
//! of it.
//!
//! A library compiles each file of each member of the workspace that it
//! reaches by a normal or a build dependency, and each package of the lock
//! that it reaches so. The digest reads exactly those: for a member its
//! manifest, its build script and each file under `src`, and for another
//! package its locked name, version and source. It reads no test, bench,
//! example or README, no member that a dev dependency alone reaches, and no
//! other entry of the lock.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use core::fmt;
use std::io;
use std::path::Path;
use std::path::PathBuf;

/// The tables of a manifest that name a dependency the library compiles
/// with: the normal and the build dependencies.
const COMPILED: [&str; 2] = ["dependencies", "build-dependencies"];

/// One package of the lock: its name, version and source.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Locked
{
    /// The name.
    name: String,
    /// The version.
    version: String,
    /// The source; empty for a member of the workspace.
    source: String,
}

/// How a library reaches a dependency.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Reach
{
    /// By a path: a member of the workspace.
    Member,
    /// By the lock: a package from a registry or a repository.
    Locked,
}

/// The name of a package, as a manifest and the lock spell it.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct PackageName(String);

impl From<&str> for PackageName
{
    /// The package named `name`.
    ///
    /// # Specification
    /// trivial.
    fn from(name: &str) -> Self
    {
        Self(name.to_owned())
    }
}

impl fmt::Display for PackageName
{
    /// The name as written.
    ///
    /// # Specification
    /// trivial.
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(&self.0)
    }
}

/// The context a digest derives under, which sets one identity apart from
/// another.
#[derive(Clone, Copy, Debug)]
#[repr(transparent)]
pub struct Context(&'static str);

impl From<&'static str> for Context
{
    /// The context `context`.
    ///
    /// # Specification
    /// trivial.
    fn from(context: &'static str) -> Self
    {
        Self(context)
    }
}

/// One dependency as the lock spells it: `name`, `name version` or `name
/// version (source)`.
#[derive(Clone, Debug)]
#[repr(transparent)]
struct Spelling(String);

impl Spelling
{
    /// The name of the package that the spelling names.
    ///
    /// # Specification
    /// trivial.
    fn name(&self) -> PackageName
    {
        PackageName::from(self.0.split(' ').next().unwrap_or_default())
    }
}

impl fmt::Display for Spelling
{
    /// The spelling as the lock writes it.
    ///
    /// # Specification
    /// trivial.
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(&self.0)
    }
}

/// A workspace as the digest reads it: its members by package name, and its
/// lock.
#[derive(Debug)]
pub struct Workspace
{
    /// The root of the workspace.
    root: PathBuf,
    /// The table of each dependency that a member takes from the workspace.
    shared: toml::Table,
    /// The directory and the manifest of each member, by package name.
    members: BTreeMap<PackageName, (PathBuf, toml::Table)>,
    /// Each package of the lock, with the dependencies that it names.
    lock: Vec<(Locked, Vec<Spelling>)>,
}

/// The digest of one library, and the paths whose change can change it.
#[derive(Debug)]
pub struct Digested
{
    /// The digest.
    pub digest: [u8; 32],
    /// The root manifest, the lock, and the manifest, the build script and the
    /// `src` directory of each member of the closure.
    pub watched: BTreeSet<PathBuf>,
}

impl Workspace
{
    /// The workspace at `root`: its root manifest, each member's manifest and
    /// the lock.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// A file that cannot be read or does not parse.
    pub fn read(root: PathBuf) -> io::Result<Self>
    {
        let manifest = table(&root.join("Cargo.toml"))?;
        let workspace = manifest
            .get("workspace")
            .and_then(toml::Value::as_table)
            .ok_or_else(|| io::Error::other("the root manifest holds `[workspace]`"))?;
        let shared = workspace
            .get("dependencies")
            .and_then(toml::Value::as_table)
            .cloned()
            .unwrap_or_default();
        let mut members = BTreeMap::new();
        for member in workspace
            .get("members")
            .and_then(toml::Value::as_array)
            .ok_or_else(|| io::Error::other("the root manifest lists its members"))?
        {
            let directory = root.join(
                member
                    .as_str()
                    .ok_or_else(|| io::Error::other("a member is a path"))?,
            );
            let manifest = table(&directory.join("Cargo.toml"))?;
            let name = PackageName::from(
                manifest
                    .get("package")
                    .and_then(|package| package.get("name"))
                    .and_then(toml::Value::as_str)
                    .ok_or_else(|| {
                        io::Error::other(format!("{} names no package", directory.display()))
                    })?,
            );
            let _member = members.insert(name, (directory, manifest));
        }
        let lock = table(&root.join("Cargo.lock"))?;
        let mut packages = Vec::new();
        for package in lock
            .get("package")
            .and_then(toml::Value::as_array)
            .ok_or_else(|| io::Error::other("the lock lists its packages"))?
        {
            let text = |key: &str| {
                package
                    .get(key)
                    .and_then(toml::Value::as_str)
                    .map_or_else(String::new, String::from)
            };
            let named = package
                .get("dependencies")
                .and_then(toml::Value::as_array)
                .map_or_else(Vec::new, |dependencies| {
                    dependencies
                        .iter()
                        .filter_map(toml::Value::as_str)
                        .map(|spelling| Spelling(String::from(spelling)))
                        .collect()
                });
            packages.push((
                Locked {
                    name: text("name"),
                    version: text("version"),
                    source: text("source"),
                },
                named,
            ));
        }
        Ok(Self {
            root,
            shared,
            members,
            lock: packages,
        })
    }

    /// The digest of what the member `library` compiles, derived under
    /// `context`.
    ///
    /// # Specification
    /// - ensures: the digest reads each file of each member of the closure of
    ///   `library` that the library compiles, in path order: the manifest, the
    ///   build script and each file under `src`, each as its path relative to
    ///   the workspace, its length and its bytes. It then reads the name, the
    ///   version and the source of each locked package of the closure, in
    ///   order. Two workspaces give one digest exactly when, up to a BLAKE3
    ///   collision, those inputs agree. `watched` holds the root manifest, the
    ///   lock, and each manifest, build script and `src` directory read.
    /// - fails: as [`Self::closure`], or a file of the closure that cannot be
    ///   read.
    /// - panics: none.
    /// - executable: none — the digest's agreement is a property of the files
    ///   it reads.
    ///
    /// # Errors
    /// An I/O error, as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — over a workspace of three members and two locked
    ///   packages, an edit of a test, of a README, of a member that a dev
    ///   dependency alone reaches and of a package outside the closure keeps
    ///   the digest; an edit of a reached member's source and a new locked
    ///   version of a reached package change it.
    /// - witness: `digest::tests::what_the_library_does_not_compile_keeps_the_digest`
    /// - witness: `digest::tests::what_the_library_compiles_changes_the_digest`
    /// - witness: `digest::tests::the_script_watches_the_closure_alone`
    pub fn digest(
        &self,
        library: &PackageName,
        context: Context,
    ) -> io::Result<Digested>
    {
        let (members, packages) = self.closure(library)?;
        let mut watched =
            BTreeSet::from([self.root.join("Cargo.toml"), self.root.join("Cargo.lock")]);
        let mut files = Vec::new();
        for member in &members {
            let &(ref directory, _) = self.member(member)?;
            let manifest = directory.join("Cargo.toml");
            let _manifest = watched.insert(manifest.clone());
            files.push(manifest);
            let script = directory.join("build.rs");
            if script.is_file() {
                let _script = watched.insert(script.clone());
                files.push(script);
            }
            let sources = directory.join("src");
            gather(&sources, &mut files)?;
            let _sources = watched.insert(sources);
        }
        files.sort();
        let mut hasher = blake3::Hasher::new_derive_key(context.0);
        for path in &files {
            let relative = path.strip_prefix(&self.root).unwrap_or(path);
            let bytes = std::fs::read(path)?;
            let _hashed = hasher
                .update(relative.as_os_str().as_encoded_bytes())
                .update(&u64::try_from(bytes.len()).unwrap_or(u64::MAX).to_le_bytes())
                .update(&bytes);
        }
        for package in &packages {
            for field in [&package.name, &package.version, &package.source] {
                let _field = hasher
                    .update(&u64::try_from(field.len()).unwrap_or(u64::MAX).to_le_bytes())
                    .update(field.as_bytes());
            }
        }
        Ok(Digested {
            digest: *hasher.finalize().as_bytes(),
            watched,
        })
    }

    /// The directory and the manifest of the member named `name`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// No member of the workspace is named `name`.
    fn member(
        &self,
        name: &PackageName,
    ) -> io::Result<&(PathBuf, toml::Table)>
    {
        self.members
            .get(name)
            .ok_or_else(|| io::Error::other(format!("no member of the workspace is `{name}`")))
    }

    /// The closure of the member `library` over its normal and build
    /// dependencies: its members by name, and its other packages as the lock
    /// holds them.
    ///
    /// # Specification
    /// - ensures: a member is in the closure when `library` reaches it by a
    ///   path dependency of a `[dependencies]` or `[build-dependencies]` table,
    ///   of the manifest or of a `[target]` table. A locked package is in it
    ///   when a member of the closure names it in such a table and in the lock,
    ///   or when a locked package of the closure names it in the lock. A dev
    ///   dependency reaches nothing.
    /// - fails: a member that the walk reaches and the workspace does not hold,
    ///   or a dependency that no one package of the lock answers.
    /// - panics: none.
    /// - executable: none — a walk of the manifests and the lock.
    ///
    /// # Errors
    /// An I/O error, as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::digest`]: a member that a dev dependency
    ///   alone reaches and a package that only it locks stay outside the
    ///   closure, and a package that a reached package locks is inside it.
    /// - witness: `digest::tests::what_the_library_does_not_compile_keeps_the_digest`
    /// - witness: `digest::tests::what_the_library_compiles_changes_the_digest`
    fn closure(
        &self,
        library: &PackageName,
    ) -> io::Result<(BTreeSet<PackageName>, BTreeSet<Locked>)>
    {
        let mut members = BTreeSet::from([library.clone()]);
        let mut pending = vec![library.clone()];
        let mut locked = Vec::new();
        while let Some(member) = pending.pop() {
            let &(_, ref manifest) = self.member(&member)?;
            let mut external = BTreeSet::new();
            for (package, reach) in self.compiled(manifest) {
                match reach {
                    Reach::Member => {
                        if members.insert(package.clone()) {
                            pending.push(package);
                        }
                    },
                    Reach::Locked => {
                        let _external = external.insert(package);
                    },
                }
            }
            let &(_, ref named) = self
                .lock
                .iter()
                .find(|&&(ref entry, _)| entry.name == member.0 && entry.source.is_empty())
                .ok_or_else(|| io::Error::other(format!("the lock holds no member `{member}`")))?;
            for dependency in named {
                if external.contains(&dependency.name()) {
                    locked.push(self.locked(dependency)?);
                }
            }
        }
        let mut packages = BTreeSet::new();
        while let Some((package, named)) = locked.pop() {
            if packages.insert(package) {
                for dependency in named {
                    locked.push(self.locked(dependency)?);
                }
            }
        }
        Ok((members, packages))
    }

    /// Each dependency that `manifest` compiles with, as its package name and
    /// how the library reaches it.
    ///
    /// # Specification
    /// trivial.
    fn compiled(
        &self,
        manifest: &toml::Table,
    ) -> Vec<(PackageName, Reach)>
    {
        let mut tables: Vec<&toml::Table> = COMPILED
            .iter()
            .filter_map(|kind| manifest.get(*kind).and_then(toml::Value::as_table))
            .collect();
        if let Some(targets) = manifest.get("target").and_then(toml::Value::as_table) {
            for target in targets.values().filter_map(toml::Value::as_table) {
                tables.extend(
                    COMPILED
                        .iter()
                        .filter_map(|kind| target.get(*kind).and_then(toml::Value::as_table)),
                );
            }
        }
        let mut compiled = Vec::new();
        for (key, specification) in tables.into_iter().flatten() {
            let inherited = specification
                .get("workspace")
                .and_then(toml::Value::as_bool)
                .unwrap_or(false);
            let declared = if inherited {
                self.shared.get(key).unwrap_or(specification)
            }
            else {
                specification
            };
            let package = PackageName::from(
                specification
                    .get("package")
                    .or_else(|| declared.get("package"))
                    .and_then(toml::Value::as_str)
                    .unwrap_or(key),
            );
            let reach = if declared.get("path").is_some() {
                Reach::Member
            }
            else {
                Reach::Locked
            };
            compiled.push((package, reach));
        }
        compiled
    }

    /// The package of the lock that `dependency` names, as a dependency of the
    /// lock spells it: `name`, `name version` or `name version (source)`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// No package of the lock answers the spelling, or more than one does.
    fn locked(
        &self,
        dependency: &Spelling,
    ) -> io::Result<(Locked, &[Spelling])>
    {
        let mut words = dependency.0.splitn(3, ' ');
        let name = words.next().unwrap_or_default();
        let version = words.next();
        let source = words
            .next()
            .map(|source| source.trim_start_matches('(').trim_end_matches(')'));
        let mut found = self.lock.iter().filter(|&&(ref entry, _)| {
            entry.name == name
                && version.is_none_or(|version| entry.version == version)
                && source.is_none_or(|source| entry.source == source)
        });
        match (found.next(), found.next()) {
            (Some(&(ref package, ref named)), None) => Ok((package.clone(), named.as_slice())),
            _ => Err(io::Error::other(format!(
                "no one package of the lock is `{dependency}`"
            ))),
        }
    }
}

/// The TOML table at `path`.
///
/// # Specification
/// trivial.
///
/// # Errors
/// The file cannot be read or does not parse.
fn table(path: &Path) -> io::Result<toml::Table>
{
    std::fs::read_to_string(path)?
        .parse::<toml::Table>()
        .map_err(|error| io::Error::other(format!("{}: {error}", path.display())))
}

/// Every file under `directory` except build output, appended to `files`.
///
/// # Specification
/// - ensures: `files` gains each regular file below `directory`, skipping any
///   `target` directory, walked from a worklist of directories still to read.
/// - executable: none — a walk of the file system.
///
/// # Errors
/// An I/O error reading a directory.
///
/// # Adequacy
/// - hypothesis: L3 — a new file under `src` of a reached member changes the
///   digest, so the walk reads it.
/// - witness: `digest::tests::what_the_library_compiles_changes_the_digest`
fn gather(
    directory: &Path,
    files: &mut Vec<PathBuf>,
) -> std::io::Result<()>
{
    let mut pending = vec![directory.to_path_buf()];
    while let Some(directory) = pending.pop() {
        for entry in std::fs::read_dir(&directory)? {
            let path = entry?.path();
            if path.is_dir() {
                if path.file_name().is_some_and(|name| name != "target") {
                    pending.push(path);
                }
            }
            else {
                files.push(path);
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests
{
    use alloc::collections::BTreeSet;
    use std::path::Path;
    use std::path::PathBuf;

    use super::Context;
    use super::Digested;
    use super::PackageName;
    use super::Workspace;

    /// The context the tests derive under.
    const CONTEXT: &str = "gandr build identity test";

    /// The lock of the fixture: the members `a`, `b` and `c`, the package `x`
    /// that `a` uses, the package `y` that `x` uses, and the package `z` that
    /// `c` uses.
    const LOCK: &str = r#"version = 4

[[package]]
name = "a"
version = "0.0.0"
dependencies = ["b", "c", "x"]

[[package]]
name = "b"
version = "0.0.0"

[[package]]
name = "c"
version = "0.0.0"
dependencies = ["z"]

[[package]]
name = "x"
version = "1.0.0"
source = "registry+https://example.org"
dependencies = ["y"]

[[package]]
name = "y"
version = "2.0.0"
source = "registry+https://example.org"

[[package]]
name = "z"
version = "3.0.0"
source = "registry+https://example.org"
"#;

    /// The files of the fixture: `a` reaches `b` from the workspace and `x`
    /// from the lock, and `c` by a dev dependency alone.
    const FILES: [(&str, &str); 10] = [
        (
            "Cargo.toml",
            "[workspace]\nmembers = [\"crates/a\", \"crates/b\", \"crates/c\"]\n\n[workspace.dependencies]\nb = { path = \"crates/b\" }\n",
        ),
        ("Cargo.lock", LOCK),
        (
            "crates/a/Cargo.toml",
            "[package]\nname = \"a\"\n\n[dependencies]\nb.workspace = true\nx = \"1\"\n\n[dev-dependencies]\nc = { path = \"../c\" }\n",
        ),
        ("crates/a/src/lib.rs", "pub fn a() {}\n"),
        ("crates/a/tests/lib.rs", "#[test]\nfn a() {}\n"),
        ("crates/a/README.md", "# a\n"),
        ("crates/b/Cargo.toml", "[package]\nname = \"b\"\n"),
        ("crates/b/src/lib.rs", "pub fn b() {}\n"),
        (
            "crates/c/Cargo.toml",
            "[package]\nname = \"c\"\n\n[dependencies]\nz = \"3\"\n",
        ),
        ("crates/c/src/lib.rs", "pub fn c() {}\n"),
    ];

    /// The name of a fixture's directory, one for each test.
    #[repr(transparent)]
    #[derive(Clone, Copy)]
    struct Fixture(&'static str);

    /// One file to write: its path under the root, and its text.
    struct File<'text>
    {
        /// The path under the root.
        path: &'static str,
        /// The text.
        text: &'text str,
    }

    /// A fresh fixture under a directory of its own, named for `test`.
    ///
    /// # Specification
    /// trivial.
    fn fixture(test: Fixture) -> PathBuf
    {
        let root = std::env::temp_dir().join(format!(
            "gandr-build-identity-{}-{}",
            std::process::id(),
            test.0
        ));
        drop(std::fs::remove_dir_all(&root));
        for (path, text) in FILES {
            write(&root, &File { path, text });
        }
        root
    }

    /// Write `file` under `root`.
    ///
    /// # Specification
    /// trivial.
    fn write(
        root: &Path,
        file: &File<'_>,
    )
    {
        let path = root.join(file.path);
        std::fs::create_dir_all(path.parent().expect("a file sits in a directory"))
            .expect("the directory is made");
        std::fs::write(path, file.text).expect("the file is written");
    }

    /// The digest of `a` in the workspace at `root`, with what it watches.
    ///
    /// # Specification
    /// trivial.
    fn digested(root: &Path) -> Digested
    {
        Workspace::read(root.to_path_buf())
            .expect("the fixture reads")
            .digest(&PackageName::from("a"), Context::from(CONTEXT))
            .expect("the closure of `a` digests")
    }

    #[test]
    fn what_the_library_does_not_compile_keeps_the_digest()
    {
        let root = fixture(Fixture("keeps"));
        let before = digested(&root).digest;
        for (path, text) in [
            (
                "crates/a/tests/lib.rs",
                "#[test]\nfn a() {}\n// a comment\n",
            ),
            ("crates/a/README.md", "# a\n\nA line.\n"),
            ("crates/c/src/lib.rs", "pub fn c() {}\n// a comment\n"),
            ("Cargo.lock", LOCK.replace("3.0.0", "3.0.1").as_str()),
        ] {
            write(&root, &File { path, text });
            assert_eq!(
                digested(&root).digest,
                before,
                "an edit of `{path}` keeps the digest"
            );
        }
        drop(std::fs::remove_dir_all(&root));
    }

    #[test]
    fn what_the_library_compiles_changes_the_digest()
    {
        let root = fixture(Fixture("changes"));
        let mut seen = BTreeSet::from([digested(&root).digest]);
        for (path, text) in [
            ("crates/a/src/lib.rs", "pub fn a() {}\n// a comment\n"),
            ("crates/b/src/lib.rs", "pub fn b() {}\n// a comment\n"),
            ("crates/b/build.rs", "fn main() {}\n"),
            ("crates/b/src/more.rs", "pub fn more() {}\n"),
            ("Cargo.lock", LOCK.replace("2.0.0", "2.0.1").as_str()),
        ] {
            write(&root, &File { path, text });
            assert!(
                seen.insert(digested(&root).digest),
                "an edit of `{path}` gives a new digest"
            );
        }
        drop(std::fs::remove_dir_all(&root));
    }

    #[test]
    fn the_script_watches_the_closure_alone()
    {
        let root = fixture(Fixture("watches"));
        write(&root, &File {
            path: "crates/b/build.rs",
            text: "fn main() {}\n",
        });
        let watched = digested(&root).watched;
        assert_eq!(
            watched,
            BTreeSet::from(
                [
                    "Cargo.lock",
                    "Cargo.toml",
                    "crates/a/Cargo.toml",
                    "crates/a/src",
                    "crates/b/Cargo.toml",
                    "crates/b/build.rs",
                    "crates/b/src",
                ]
                .map(|path| root.join(path))
            ),
        );
        drop(std::fs::remove_dir_all(&root));
    }
}
