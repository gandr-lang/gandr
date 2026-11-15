//! A package's lock: each coordinate its sources import, at the address it
//! was resolved to.
//!
//! # A dependency is found by the coordinate an import writes
//!
//! A source imports a package by its coordinate, `import "path:../hello" as
//! hello ;`, and binds its root module under the alias it writes. A path
//! coordinate is a directory, read from the dependent's root, that roots a
//! package. A `gh:` coordinate is a repository on GitHub whose checkout, at
//! the revision the dependent's lock records, roots one ([`super::fetch`]).
//! [`Package::dependencies`] collects the coordinates every source of the
//! package imports, each once, and [`Package::resolve`] reads each one and
//! checks it as the package it roots, recursively, so a dependency's own
//! dependencies are resolved before it is. A root met twice on one chain is a
//! cycle, refused with the chain.
//!
//! # The lock records pointers, and the address never records a coordinate
//!
//! The lock maps each coordinate to a content pointer into the store, the one
//! store of the storage tier a run opens: resolving a dependency commits its
//! address and its signature key there, and the lock records the pointer the
//! value plane returns, as `<digest>:<offset>`. The checker writes the lock
//! once, and every import of the coordinate reads it back, so two sources
//! importing one coordinate read one address. A lock that says another thing
//! than what the coordinates resolve to is refused as drift, coordinate by
//! coordinate, until `gandr lock` writes it again, so a dependency never
//! changes under its dependent unseen. The package's own address digests the
//! addresses its lock's pointers name, read back through the store, and never
//! their coordinates or the aliases its imports bind: where a dependency is
//! found and what it is called are not what the package is.
//!
//! # A workspace's packages share one lock
//!
//! A package in no workspace keeps its lock as `package.gandr.lock` beside its
//! package source. A package below a workspace keeps its lock as a table in
//! `workspace.gandr.lock`, beside `workspace.gandr`. The key of the table is
//! the path from the root of the workspace to the root of the package. A
//! `path:` coordinate reads from the root of its dependent. Thus two members
//! can write one coordinate for two different packages, and each member needs
//! its own table. Each package reconciles its own table. It does not change
//! the other tables.
//!
//! **Choice.** A package below the directory of a workspace shares the lock of
//! the workspace. This is also true when `members` does not name the package.
//! Cargo also keeps one `Cargo.lock` for all the packages below the root of
//! its workspace. To read membership, the checker must run the source of the
//! workspace. Each import of a coordinate reads the lock. Thus the checker
//! finds the file from the location of the package, and never from a run.
//!
//! # References
//!
//! - `vault:01a178aa-d585-7822-9cf0-40459729a925` — background: a package
//!   reference is a content address and a separate coordinate never part of
//!   identity, and resolution produces a lock mapping coordinates to verified
//!   addresses.
//! - `vault:01a17cb3-d471-72b2-9bd2-70a46f74c3de` — background: the storage
//!   tier is the one store the lock, the build layer and the verdict cache
//!   share.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::sync::Arc;
use core::fmt::Write as _;
use std::io;
use std::path::Path;
use std::path::PathBuf;

use anodized::spec;
use gandr_core_fork::Fork;
use gandr_storage_store::ContentPtr;
use gandr_storage_store::Store;
use gandr_storage_store::StoreError;
use gandr_storage_store::Stored;
use gandr_storage_values::CanonicalValue;
use gandr_storage_values::CanonicalWord;
use gandr_storage_values::ChunkDigest;
use gandr_storage_values::CodecId;
use gandr_storage_values::CodecIdentity;
use gandr_storage_values::CodecVersion;
use gandr_storage_values::ConstructorTag;
use gandr_storage_values::TokenOffset;
use gandr_storage_values::TokenReader;
use gandr_storage_values::TokenSink;
use gandr_storage_values::ValueError;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use super::Absence;
use super::Authorship;
use super::Basic;
use super::Body;
use super::DIGEST;
use super::Differing;
use super::Held;
use super::Identity;
use super::Manifested;
use super::Opening;
use super::Package;
use super::PackageAddress;
use super::Reconciled;
use super::Split;
use super::Unaddressed;
use super::fetch;
use super::fetch::Repository;
use super::fetch::Revision;
use super::fetch::Unfetched;
use super::fetch::Written;
use super::package_root;
use crate::component::ImportBase;
use crate::component::ImportPath;
use crate::component::Unshadowed;
use crate::component::path_imports;
use crate::workspace::Workspace;

/// The file name of the lock that the checker writes beside the source of a
/// package in no workspace.
pub const LOCK: &str = "package.gandr.lock";

/// The file name of the lock that the checker writes beside the source of a
/// workspace. The lock has one table for each package below the workspace.
pub const WORKSPACE_LOCK: &str = "workspace.gandr.lock";

/// The line that opens a lock the checker wrote.
const WRITTEN: &str = "# Written by `gandr check` from the coordinates the package's sources \
                       import: relock with `gandr lock`, never by hand.";

/// The first line of a workspace lock that the checker wrote.
const SHARED: &str = "# Written by `gandr check` from the coordinates the workspace's packages' \
                      sources import: relock with `gandr lock`, never by hand.";

/// The line that opens the lock's table.
const TABLE: &str = "[dependencies]";

/// The start of the line that opens the table of a package in a workspace
/// lock. The key of the package follows it.
const MEMBER: &str = "[dependencies.";

/// The head every module path names the standard library by.
pub const STANDARD: &str = "std";

/// The standard library's package root in the tree this build was built
/// from.
const STANDARD_ROOT: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/../../library/std");

/// Where a dependency is found, as an import writes it: never part of what
/// it is.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Coordinate
{
    /// `path:<directory>`: a directory rooting the dependency, read from the
    /// dependent's root, as the import writes it.
    Path(String),
    /// `gh:<owner>/<name>`: a repository on GitHub whose top directory, at the
    /// revision the dependent's lock records, roots the dependency.
    GitHub(Repository),
}

impl Coordinate
{
    /// The coordinate `import` writes, `path:../hello`; none for an import
    /// of no coordinate.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn of(import: &ImportPath) -> Option<Self>
    {
        if import.base() != ImportBase::Coordinate {
            return None;
        }
        written(Text(import.as_ref()))
    }

    /// The path an import of the coordinate names from `root` while the
    /// coordinate stands unlocked: a `path:` coordinate's directory, and a
    /// `gh:` coordinate as it is written, under `root`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn named(
        &self,
        root: &Path,
    ) -> PathBuf
    {
        match *self {
            Self::Path(ref directory) => root.join(directory),
            Self::GitHub(_) => root.join(alloc::format!("{self}")),
        }
    }
}

/// The coordinate `address` writes, `path:../hello` or `gh:acme-org/rope`;
/// none for an address of another scheme or none.
///
/// # Specification
/// trivial.
fn written(address: Text<'_>) -> Option<Coordinate>
{
    let (scheme, rest) = address.0.split_once(':')?;
    if scheme == gandr_surface_lowering::PATH_SCHEME {
        Some(Coordinate::Path(String::from(rest)))
    }
    else if scheme == gandr_surface_lowering::GITHUB_SCHEME {
        Repository::written(Written(rest)).map(Coordinate::GitHub)
    }
    else {
        None
    }
}

impl core::fmt::Display for Coordinate
{
    /// The coordinate as an import writes it, `path:../hello` or
    /// `gh:acme-org/rope`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        match *self {
            Self::Path(ref directory) => {
                write!(f, "{}:{directory}", gandr_surface_lowering::PATH_SCHEME)
            },
            Self::GitHub(ref repository) => {
                write!(f, "{}:{repository}", gandr_surface_lowering::GITHUB_SCHEME)
            },
        }
    }
}

/// A package's signature key: the BLAKE3 digest of the dotted paths its root
/// exports, in order. It names the interface a dependent reads, not its
/// types; matching one is #533 p4's.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct SignatureKey([u8; 32]);

impl SignatureKey
{
    /// The key a digest of a root's exported paths is.
    ///
    /// # Specification
    /// trivial.
    pub(super) const fn new(digest: blake3::Hash) -> Self
    {
        Self(*digest.as_bytes())
    }
}

impl core::fmt::Display for SignatureKey
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

/// The tag a package's identity opens with in the store.
const IDENTITY: u8 = 0x1D_u8;

impl CanonicalValue for Identity
{
    /// The identity as one constructor of eight words: the address, then the
    /// signature key, each as four little-endian words.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn emit_tokens<Sink>(
        &self,
        sink: &mut Sink,
    ) -> Result<(), ValueError>
    where
        Sink: TokenSink + ?Sized,
    {
        sink.open(ConstructorTag::from(IDENTITY))?;
        for digest in [&self.address.0, &self.signature.0] {
            for word in digest.as_chunks::<8>().0 {
                sink.word(CanonicalWord::from(u64::from_le_bytes(*word)))?;
            }
        }
        sink.close()
    }

    /// The identity [`Identity::emit_tokens`] wrote.
    ///
    /// # Specification
    /// - requires: `reader` stands at an identity's constructor.
    /// - ensures: the address and the signature key its eight words spell.
    /// - provides: the read [`Lock::addresses`] makes through the store.
    /// - fails: [`ValueError::UnexpectedConstructor`] for another constructor,
    ///   and the reader's refusals.
    /// - panics: none.
    /// - executable: none — the reader's stream is the store's.
    ///
    /// # Errors
    /// [`ValueError`], as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a dependency's address read back through the store
    ///   digests into its dependent's, which moves with the dependency's
    ///   content.
    /// - witness: `tests::package::a_dependency_s_content_edit_drifts_the_lock_until_relocked_3072`
    #[inline]
    fn decode_tokens(reader: &mut TokenReader<'_>) -> Result<Self, ValueError>
    {
        let position = reader.position();
        let found = reader.read_tag()?;
        if found != ConstructorTag::from(IDENTITY) {
            return Err(ValueError::UnexpectedConstructor { found, position });
        }
        let mut address = [0_u8; 32];
        let mut signature = [0_u8; 32];
        for digest in [&mut address, &mut signature] {
            for word in digest.as_chunks_mut::<8>().0 {
                *word = u64::from(reader.read_word()?).to_le_bytes();
            }
        }
        reader.read_close()?;
        Ok(Self {
            address: PackageAddress(address),
            signature: SignatureKey(signature),
        })
    }
}

impl Stored for Identity
{
    /// # Specification
    /// trivial.
    #[inline]
    fn codec() -> CodecIdentity
    {
        CodecIdentity::new(
            CodecId::from(u16::from(IDENTITY)),
            CodecVersion::from(1_u16),
        )
    }
}

/// A package's lock: each dependency by its coordinate, at the pointer its
/// identity stands at in the store, and a `gh:` dependency at the revision
/// it was fetched at.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Lock(BTreeMap<Coordinate, Locked>);

/// What a lock records of one dependency.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Locked
{
    /// Where its identity stands in the store.
    pointer: ContentPtr,
    /// The revision a `gh:` dependency was fetched at; none for a `path:` one.
    revision: Option<Revision>,
}

/// Which revisions a resolution may fetch a `gh:` dependency at.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Revisions
{
    /// Only the ones the standing locks record, as `gandr check` resolves.
    Locked,
    /// The ones the standing locks record, and the remote's `HEAD` for a
    /// coordinate the resolved package's own lock does not record, as `gandr
    /// lock` resolves.
    Asked,
}

impl Lock
{
    /// The pointer the lock records for `coordinate`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn locked(
        &self,
        coordinate: &Coordinate,
    ) -> Option<ContentPtr>
    {
        self.0.get(coordinate).map(|locked| locked.pointer)
    }

    /// The revision the lock records for `coordinate`: a `gh:` dependency's;
    /// none for a `path:` one or a coordinate the lock does not record.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn revision(
        &self,
        coordinate: &Coordinate,
    ) -> Option<Revision>
    {
        self.0.get(coordinate)?.revision
    }

    /// Each coordinate the lock records, in order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn coordinates(&self) -> impl Iterator<Item = &Coordinate>
    {
        self.0.keys()
    }

    /// The pointer of each identity the lock records, in the order of the
    /// coordinates.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn pointers(&self) -> impl Iterator<Item = ContentPtr>
    {
        self.0.values().map(|locked| locked.pointer)
    }

    /// Each coordinate the lock records, in order, with the address of the
    /// identity its pointer names, read back through `store`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one entry per coordinate, in order: the coordinate and the
    ///   address of the identity its pointer names, or
    ///   [`Unaddressed::Unstored`] where the store cannot read the pointer back
    ///   as an identity.
    /// - provides: the one reading of the lock's pointers that
    ///   [`Lock::addresses`] and a dependent's re-admission of its
    ///   dependencies' exports share.
    /// - fails: never; a pointer the store cannot read back is its entry's
    ///   [`Unaddressed`].
    /// - panics: none.
    /// - executable: none — the identities are the store's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Lock::addresses`], which reads each entry.
    /// - witness: `tests::package::a_dependency_s_content_edit_drifts_the_lock_until_relocked_3072`
    /// - witness: `tests::package::a_pointer_the_store_cannot_answer_leaves_the_dependent_unaddressed_3157`
    #[inline]
    pub fn resolved<'lock>(
        &'lock self,
        store: &'lock Store,
    ) -> impl Iterator<Item = (&'lock Coordinate, Result<PackageAddress, Unaddressed>)> + 'lock
    {
        self.0.iter().map(|(coordinate, &Locked { pointer, .. })| {
            let address = store
                .deref::<Identity>(pointer)
                .map(|identity| identity.address)
                .map_err(|fault| Unaddressed::Unstored {
                    coordinate: coordinate.clone(),
                    fault: Box::new(fault),
                });
            (coordinate, address)
        })
    }

    /// The addresses the lock records, once each, read back through `store`:
    /// what the package's own address digests of its dependencies.
    ///
    /// # Specification
    /// - requires: `store` holds what the lock's pointers name.
    /// - ensures: the address of the identity each pointer names, once each, in
    ///   order, as [`Lock::resolved`] reads them.
    /// - provides: the dependencies' part of [`Package::identity`].
    /// - fails: [`Unaddressed::Unstored`] at the first coordinate whose pointer
    ///   the store cannot read back as an identity.
    /// - panics: none.
    /// - executable: none — the identities are the store's.
    ///
    /// # Errors
    /// [`Unaddressed::Unstored`], as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a dependency's content edit moves its dependent's
    ///   address, and a pointer the store cannot answer leaves the dependent
    ///   unaddressed by the coordinate.
    /// - witness: `tests::package::a_dependency_s_content_edit_drifts_the_lock_until_relocked_3072`
    /// - witness: `tests::package::a_pointer_the_store_cannot_answer_leaves_the_dependent_unaddressed_3157`
    #[inline]
    pub fn addresses(
        &self,
        store: &Store,
    ) -> Result<BTreeSet<PackageAddress>, Unaddressed>
    {
        self.resolved(store).map(|(_, address)| address).collect()
    }

    /// The lock as the checker writes it: the header, then the body.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the [`WRITTEN`] line, the digest line carrying the BLAKE3
    ///   digest of the body in lowercase hexadecimal, then the body: a
    ///   `[dependencies]` table holding one line per coordinate in order,
    ///   `"path:…" = { pointer = "<digest>:<offset>" }`, and `"gh:…" = {
    ///   revision = "<revision>", pointer = "<digest>:<offset>" }` for a
    ///   coordinate the lock records a revision of: the coordinate a basic
    ///   string as an import writes it, the revision and the digest lowercase
    ///   hexadecimal and the offset decimal. The same lock renders the same
    ///   bytes wherever it is rendered, and [`Lock::read`] reads the render
    ///   back as the lock.
    /// - provides: the file [`reconcile`](super::reconcile) and [`relock`]
    ///   write.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a lock is written, read back equal and written again
    ///   byte for byte from another working directory, and one recording a
    ///   revision reads back with it.
    /// - witness: `tests::package::a_lock_is_written_once_and_reads_alike_from_anywhere_3072`
    /// - witness: `tests::package::a_gh_coordinate_reads_back_and_refuses_a_climbing_name_4714`
    #[spec(ensures: |ref ret| ret.starts_with(WRITTEN)
        && matches!(Split::of(Manifested(ret), Opening(WRITTEN)).authorship(), Authorship::Checker))]
    #[inline]
    #[must_use]
    pub fn render(&self) -> String
    {
        let mut body = format!("\n{TABLE}\n");
        self.entries(&mut body);
        format!(
            "{WRITTEN}\n{DIGEST}{}\n{body}",
            blake3::hash(body.as_bytes()).to_hex()
        )
    }

    /// Write one line for each coordinate of the lock to `body`. The lines are
    /// the lines of the table that [`Lock::render`] writes.
    ///
    /// # Specification
    /// trivial.
    fn entries(
        &self,
        body: &mut String,
    )
    {
        let mut key = String::new();
        for (coordinate, &Locked { pointer, revision }) in &self.0 {
            key.clear();
            let _keyed = write!(key, "{coordinate}");
            let _opened = write!(body, "{} = {{ ", Basic(&key));
            if let Some(revision) = revision {
                let _revised = write!(body, "revision = \"{revision}\", ");
            }
            let _written = writeln!(
                body,
                "pointer = \"{}:{}\" }}",
                pointer.digest(),
                pointer.offset()
            );
        }
    }

    /// The lock that stands for `package`, as the checker wrote it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the lock [`Lock::render`] would write as the file at the
    ///   package's [`Package::lock`] stands. For a package below a workspace,
    ///   the lock is its table in the workspace lock. `Unwritten` if no file
    ///   stands there, if the file cannot be read, or if the file has no table
    ///   for the package. `Edited` if the header does not hold the digest of
    ///   the body. `Unread` if the body is not a render.
    /// - provides: the lock every import of a coordinate, and every check of a
    ///   dependency's own lock, reads.
    /// - fails: never; a missing or foreign file is the typed absence.
    /// - panics: none.
    /// - executable: none — the clause reads the file system again.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a written lock reads back equal, and one edited by
    ///   hand reads as edited.
    /// - witness: `tests::package::a_lock_is_written_once_and_reads_alike_from_anywhere_3072`
    #[inline]
    pub fn read(package: &Package) -> Maybe<Self, lock_file::Absent>
    {
        let (path, member) = match shared(package) {
            Some((path, member)) => (path, Some(member)),
            None => (package.root().join(LOCK), None),
        };
        let Ok(text) = std::fs::read_to_string(path)
        else {
            return Maybe::Absent(lock_file::Absent::Unwritten);
        };
        let opening = if member.is_some() { SHARED } else { WRITTEN };
        let split = Split::of(Manifested(&text), Opening(opening));
        if matches!(split.authorship(), Authorship::Hand) {
            return Maybe::Absent(lock_file::Absent::Edited);
        }
        let read = match member {
            None => parsed(Text(split.body)),
            Some(member) => match tables(Text(split.body)) {
                Some(mut tables) => match tables.remove(&member) {
                    Some(lock) => Some(lock),
                    None => return Maybe::Absent(lock_file::Absent::Unwritten),
                },
                None => None,
            },
        };
        read.map_or(Maybe::Absent(lock_file::Absent::Unread), Maybe::Present)
    }
}

/// The lock a body [`Lock::render`] wrote states, or none for any other
/// body.
///
/// # Specification
/// trivial.
fn parsed(body: Text<'_>) -> Option<Lock>
{
    let mut lines = body.0.strip_prefix('\n')?.lines();
    if lines.next()? != TABLE {
        return None;
    }
    let mut lock = BTreeMap::new();
    for line in lines {
        let (coordinate, locked) = entry(Text(line))?;
        let _first = lock.insert(coordinate, locked);
    }
    Some(Lock(lock))
}

/// The tables of a body that [`shared_render`] wrote: the lock of each package
/// by its key. None for a different body.
///
/// # Specification
/// trivial.
fn tables(body: Text<'_>) -> Option<BTreeMap<String, Lock>>
{
    let mut tables = BTreeMap::new();
    let mut lines = body.0.lines().peekable();
    while let Some(blank) = lines.next() {
        let (member, Text(rest)) = Text(lines.next()?.strip_prefix(MEMBER)?).basic()?;
        if !blank.is_empty() || rest != "]" {
            return None;
        }
        let mut lock = BTreeMap::new();
        while let Some(line) = lines.next_if(|line| !line.is_empty()) {
            let (coordinate, locked) = entry(Text(line))?;
            let _first = lock.insert(coordinate, locked);
        }
        if lock.is_empty() || tables.insert(member, Lock(lock)).is_some() {
            return None;
        }
    }
    Some(tables)
}

/// One coordinate and what the lock records for it, from a line of a table
/// that [`Lock::render`] wrote. None for a different line.
///
/// # Specification
/// trivial.
fn entry(line: Text<'_>) -> Option<(Coordinate, Locked)>
{
    let (coordinate, Text(rest)) = line.basic()?;
    let coordinate = written(Text(&coordinate))?;
    let rest = rest.strip_prefix(" = { ")?;
    let (revision, rest) = match coordinate {
        Coordinate::Path(_) => (None, rest),
        Coordinate::GitHub(_) => {
            let (revision, Written(rest)) =
                Revision::opening(Written(rest.strip_prefix("revision = \"")?))?;
            (Some(revision), rest.strip_prefix("\", ")?)
        },
    };
    let (digest, Text(rest)) = Text(rest.strip_prefix("pointer = \"")?).digest()?;
    let (offset, rest) = rest.strip_prefix(':')?.split_once('"')?;
    let parsed: u32 = offset.parse().ok()?;
    let canonical = offset.bytes().all(|digit| digit.is_ascii_digit())
        && (offset == "0" || !offset.starts_with('0'));
    if rest != " }" || !canonical {
        return None;
    }
    Some((coordinate, Locked {
        pointer: ContentPtr::new(ChunkDigest::from(digest.0), TokenOffset::from(parsed)),
        revision,
    }))
}

/// A workspace lock as the checker writes it. The header comes first. One table
/// follows for each package that records a dependency, in the order of the
/// keys.
///
/// # Specification
/// - requires: each lock of `tables` records a coordinate.
/// - ensures: the [`SHARED`] line comes first. The digest line follows. It
///   holds the BLAKE3 digest of the body in lowercase hexadecimal. The body has
///   a part for each package. Each part is a blank line, then
///   `[dependencies."<key>"]` with the key as a basic string, then the lines
///   that [`Lock::render`] writes in its table. [`tables`] reads the body back
///   as `tables`.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a member's table is written, keyed by its path, and read
///   back as its lock.
/// - witness: `tests::package::a_workspace_s_packages_share_one_lock_4921`
#[spec(ensures: |ref ret| ret.starts_with(SHARED)
    && matches!(Split::of(Manifested(ret), Opening(SHARED)).authorship(), Authorship::Checker))]
fn shared_render(tables: &BTreeMap<String, Lock>) -> String
{
    let mut body = String::new();
    for (member, lock) in tables {
        let _opened = write!(body, "\n{MEMBER}{}]\n", Basic(member));
        lock.entries(&mut body);
    }
    format!(
        "{SHARED}\n{DIGEST}{}\n{body}",
        blake3::hash(body.as_bytes()).to_hex()
    )
}

/// The workspace lock that holds the table of `package`, and the key of the
/// table. The function finds the workspace from the directory above the root
/// of the package. The lock is [`WORKSPACE_LOCK`] beside the source of the
/// workspace. The key is the path from the directory of the workspace to the
/// root of the package, with `/` between its components. None for a package
/// below no workspace, or for a path that is not Unicode.
///
/// # Specification
/// trivial.
fn shared(package: &Package) -> Option<(PathBuf, String)>
{
    let Maybe::Present(workspace) = Workspace::discover(package.root().parent()?)
    else {
        return None;
    };
    let below = package.root().strip_prefix(workspace.root()).ok()?;
    let key = below
        .components()
        .map(|component| component.as_os_str().to_str())
        .collect::<Option<Vec<&str>>>()?
        .join("/");
    Some((workspace.root().join(WORKSPACE_LOCK), key))
}

/// Text of a lock file, read from its start.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Text<'text>(&'text str);

/// The 32 bytes 64 hexadecimal digits spell.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Digest([u8; 32]);

impl Text<'_>
{
    /// The TOML basic string the text opens with, decoded as [`Basic`]
    /// encodes it, and what follows it.
    ///
    /// # Specification
    /// trivial.
    fn basic(self) -> Option<(String, Self)>
    {
        let mut characters = self.0.strip_prefix('"')?.char_indices();
        let mut decoded = String::new();
        while let Some((at, character)) = characters.next() {
            match character {
                '"' => return Some((decoded, Self(self.0.get(at.saturating_add(2) ..)?))),
                '\\' => decoded.push(match characters.next()?.1 {
                    '"' => '"',
                    '\\' => '\\',
                    'n' => '\n',
                    't' => '\t',
                    'r' => '\r',
                    'u' => {
                        let mut code = 0_u32;
                        for _ in 0_u8 .. 4_u8 {
                            let digit = characters.next()?.1.to_digit(16)?;
                            code = code.checked_mul(16)?.checked_add(digit)?;
                        }
                        char::from_u32(code)?
                    },
                    _ => return None,
                }),
                other => decoded.push(other),
            }
        }
        None
    }

    /// The 32 bytes the 64 lowercase hexadecimal digits the text opens with
    /// spell, and what follows them.
    ///
    /// # Specification
    /// trivial.
    fn digest(self) -> Option<(Digest, Self)>
    {
        let mut bytes = [0_u8; 32];
        for (index, byte) in bytes.iter_mut().enumerate() {
            let at = index.saturating_mul(2);
            let pair = self.0.get(at .. at.saturating_add(2))?;
            if !pair
                .bytes()
                .all(|digit| matches!(digit, b'0' ..= b'9' | b'a' ..= b'f'))
            {
                return None;
            }
            *byte = u8::from_str_radix(pair, 16).ok()?;
        }
        Some((Digest(bytes), Self(self.0.get(64 ..)?)))
    }
}

quenchant_shape::reason_enum! {
    /// Why a package's root holds no lock the checker wrote.
    pub mod lock_file {
        /// The lock file is missing, foreign or not a render.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No lock stands at the root, or it cannot be read.
            Unwritten,
            /// The lock's header does not carry its body's digest: it was
            /// edited since the checker wrote it.
            Edited,
            /// The lock's body is no lock the checker renders.
            Unread,
        }
    }
}

impl Package
{
    /// The path of the file that holds the lock of the package. For a package
    /// below a workspace, this is [`WORKSPACE_LOCK`] beside the source of the
    /// workspace. The file holds the table of the package and the tables of
    /// the other packages. For a package below no workspace, this is [`LOCK`]
    /// at its root.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn lock(&self) -> PathBuf
    {
        shared(self).map_or_else(|| self.root().join(LOCK), |(path, _member)| path)
    }

    /// The coordinates the package's sources import, each once.
    ///
    /// # Specification
    /// - requires: `grammar` is the grammar the package's sources are read
    ///   under.
    /// - ensures: the [`Coordinate`] of each import whose address is one, read
    ///   off the package source and every module under the package's sources,
    ///   each once, in the coordinates' order. A source that does not parse
    ///   writes none, its own check refusing it.
    /// - provides: the dependencies [`Package::resolve`] resolves.
    /// - fails: [`Unresolved::Unread`] for a source that cannot be read.
    /// - panics: none.
    /// - executable: none — the clause reads the file system.
    ///
    /// # Errors
    /// [`Unresolved::Unread`], as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two sources importing one coordinate collect it once,
    ///   and a package importing none collects none.
    /// - witness: `tests::package::a_lock_is_written_once_and_reads_alike_from_anywhere_3072`
    #[inline]
    pub fn dependencies(
        &self,
        grammar: &gandr_surface_grammar::Pbg,
    ) -> Result<BTreeSet<Coordinate>, Unresolved>
    {
        let mut sources = BTreeSet::from([self.source.clone()]);
        sources.extend(super::modules(self.sources()).into_values());
        let mut coordinates = BTreeSet::new();
        for source in sources {
            let text = std::fs::read_to_string(&source).map_err(|error| Unresolved::Unread {
                source: source.clone(),
                why: error.to_string(),
            })?;
            let Ok(read) = gandr_surface_parser::parse(grammar, SourceText::from(text.as_str()))
            else {
                continue;
            };
            coordinates.extend(
                path_imports(grammar, read.tree())
                    .iter()
                    .filter_map(Coordinate::of),
            );
        }
        Ok(coordinates)
    }

    /// The lock the package's dependencies resolve to: each one found at its
    /// coordinate, its own dependencies resolved and locked first, and
    /// addressed.
    ///
    /// # Specification
    /// - requires: `grammar` is the grammar the packages' sources are read
    ///   under.
    /// - ensures: for each of [`Package::dependencies`], the package it roots:
    ///   a `path:` coordinate's directory, read from this package's root, and a
    ///   `gh:` coordinate's checkout ([`fetch::fetched`]) at the revision the
    ///   lock standing at this package's root records. Under
    ///   [`Revisions::Asked`], a `gh:` coordinate that lock of the package
    ///   resolution started at does not record is fetched at the remote's
    ///   `HEAD` ([`fetch::head`]). Its own dependencies are resolved the same
    ///   way first, depth first with an explicit stack of the packages being
    ///   resolved, and the lock standing at its root must be the one they
    ///   resolve to — none at all when it has none; then its address over its
    ///   own items and that lock's addresses, read back through `store`, and
    ///   its signature key, as [`Package::identity`] gives them on `fork`, are
    ///   committed to `store` together. Each dependency is locked under its
    ///   coordinate by the pointer the commit returns, and a `gh:` one by its
    ///   revision. The lock is a function of the packages' contents,
    ///   coordinates and revisions alone, whatever directory the process runs
    ///   in and whatever the store held.
    /// - provides: the lock `gandr check` reconciles and `gandr lock` writes.
    /// - fails: [`Unresolved`], at the first dependency that does not resolve.
    /// - panics: none.
    /// - executable: none — the clause reads the file system and lowers every
    ///   package again; the witnesses observe each outcome.
    ///
    /// # Errors
    /// [`Unresolved::Unpackaged`] for a coordinate rooting no package,
    /// [`Unresolved::Unrevisioned`] for a `gh:` coordinate no lock gives a
    /// revision, [`Unresolved::Unfetched`] for one whose tree is not fetched,
    /// [`Unresolved::Cycle`] for a root met twice on one chain,
    /// [`Unresolved::Unlocked`] for a dependency whose own lock is missing or
    /// stale, [`Unresolved::Unaddressed`] for a dependency with no address,
    /// [`Unresolved::Unstored`] for an identity the store cannot commit, and
    /// [`Unresolved::Unread`] as [`Package::dependencies`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one dependency resolves alike from two working
    ///   directories; a content edit to it moves its address and an inert edit
    ///   does not; two packages depending on each other are refused with their
    ///   chain; a `gh:` dependency is fetched at `HEAD` when locking, at the
    ///   recorded revision when checking, and refused unrevisioned when no lock
    ///   records one.
    /// - witness: `tests::package::a_lock_is_written_once_and_reads_alike_from_anywhere_3072`
    /// - witness: `tests::package::a_dependency_s_content_edit_drifts_the_lock_until_relocked_3072`
    /// - witness: `tests::package::a_dependency_cycle_is_refused_by_its_paths_3072`
    /// - witness: `tests::package::a_gh_coordinate_is_fetched_at_the_revision_its_lock_records_4714`
    #[inline]
    pub fn resolve<F>(
        &self,
        grammar: &Arc<gandr_surface_grammar::Pbg>,
        store: &mut Store,
        revisions: Revisions,
        fork: &F,
    ) -> Result<Lock, Unresolved>
    where
        F: Fork,
    {
        let mut open = BTreeSet::from([self.root.clone()]);
        let mut frames = Vec::from([Frame::of(self.clone(), None, grammar)?]);
        loop {
            let asking = revisions == Revisions::Asked && frames.len() == 1;
            let Some(frame) = frames.last_mut()
            else {
                return Ok(Lock::default());
            };
            if let Some(coordinate) = frame.pending.next() {
                let (directory, revision) = match coordinate {
                    Coordinate::Path(ref directory) => (frame.package.root.join(directory), None),
                    Coordinate::GitHub(ref repository) => {
                        let revision = match (frame.standing.revision(&coordinate), asking) {
                            (Some(revision), _) => revision,
                            (None, true) => {
                                fetch::head(repository).map_err(|fault| Unresolved::Unfetched {
                                    coordinate: coordinate.clone(),
                                    fault,
                                })?
                            },
                            (None, false) => {
                                return Err(Unresolved::Unrevisioned {
                                    root: frame.package.root.clone(),
                                    coordinate,
                                });
                            },
                        };
                        let fetched = fetch::fetched(repository, revision).map_err(|fault| {
                            Unresolved::Unfetched {
                                coordinate: coordinate.clone(),
                                fault,
                            }
                        })?;
                        (fetched, Some(revision))
                    },
                };
                let rooted = directory.canonicalize().ok();
                let dependency = match Self::discover(&directory) {
                    Maybe::Present(found) if rooted.as_deref() == Some(found.root()) => found,
                    Maybe::Present(_) | Maybe::Absent(package_root::Absent::Unpackaged) => {
                        return Err(Unresolved::Unpackaged {
                            coordinate,
                            path: directory,
                        });
                    },
                };
                if !open.insert(dependency.root.clone()) {
                    return Err(cycle(&frames, dependency.root));
                }
                frames.push(Frame::of(
                    dependency,
                    Some((coordinate, revision)),
                    grammar,
                )?);
                continue;
            }
            let Some(Frame {
                package,
                via,
                standing,
                entries,
                ..
            }) = frames.pop()
            else {
                return Ok(Lock::default());
            };
            let _closed = open.remove(&package.root);
            let own = Lock(entries);
            let (Some(parent), Some((coordinate, revision))) = (frames.last_mut(), via)
            else {
                return Ok(own);
            };
            if standing != own {
                return Err(Unresolved::Unlocked {
                    coordinate,
                    root: package.root,
                });
            }
            let identity = package
                .identity(grammar, &Unshadowed, &own, store, fork)
                .map_err(|fault| Unresolved::Unaddressed {
                    coordinate: coordinate.clone(),
                    fault,
                })?;
            let pointer = store
                .commit(&identity)
                .map_err(|fault| Unresolved::Unstored {
                    coordinate: coordinate.clone(),
                    fault: Box::new(fault),
                })?;
            let _first = parent
                .entries
                .insert(coordinate, Locked { pointer, revision });
        }
    }
}

/// One package being resolved: the dependencies of it left to resolve, the
/// lock standing at its root, and the entries of its lock so far.
struct Frame
{
    /// The package.
    package: Package,
    /// The coordinate its dependent imports it by, and the revision a `gh:`
    /// one was fetched at; none for the package resolution started at.
    via: Option<(Coordinate, Option<Revision>)>,
    /// Its dependencies not yet resolved, in the coordinates' order.
    pending: alloc::collections::btree_set::IntoIter<Coordinate>,
    /// The lock standing at its root, or none when it holds no lock the
    /// checker wrote.
    standing: Lock,
    /// Its dependencies resolved so far, by coordinate.
    entries: BTreeMap<Coordinate, Locked>,
}

impl Frame
{
    /// `package`, imported by `via`, its dependencies all left to resolve.
    ///
    /// # Specification
    /// trivial.
    fn of(
        package: Package,
        via: Option<(Coordinate, Option<Revision>)>,
        grammar: &gandr_surface_grammar::Pbg,
    ) -> Result<Self, Unresolved>
    {
        let pending = package.dependencies(grammar)?.into_iter();
        let standing = match Lock::read(&package) {
            Maybe::Present(standing) => standing,
            Maybe::Absent(_) => Lock::default(),
        };
        Ok(Self {
            package,
            via,
            pending,
            standing,
            entries: BTreeMap::new(),
        })
    }
}

/// The cycle `root` closes over the packages `frames` is resolving: their
/// roots from `root`'s own on, outermost first, then `root` again.
///
/// # Specification
/// trivial.
fn cycle(
    frames: &[Frame],
    root: PathBuf,
) -> Unresolved
{
    let mut chain: Vec<PathBuf> = frames
        .iter()
        .map(|frame| &frame.package.root)
        .skip_while(|open| **open != root)
        .cloned()
        .collect();
    chain.push(root);
    Unresolved::Cycle { chain }
}

/// Why a package's dependencies resolve to no lock.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Unresolved
{
    /// A source of a package cannot be read for the coordinates it imports.
    Unread
    {
        /// The source.
        source: PathBuf,
        /// Why, spelled.
        why: String,
    },
    /// A dependency's coordinate roots no package.
    Unpackaged
    {
        /// The dependency.
        coordinate: Coordinate,
        /// The directory its coordinate names.
        path: PathBuf,
    },
    /// A `gh:` dependency whose revision the lock standing at its dependent's
    /// root does not record, met where no revision may be asked.
    Unrevisioned
    {
        /// The dependency.
        coordinate: Coordinate,
        /// Its dependent's root, where `gandr lock` writes the revision.
        root: PathBuf,
    },
    /// A `gh:` dependency's tree, or its revision, was not fetched.
    Unfetched
    {
        /// The dependency.
        coordinate: Coordinate,
        /// Why.
        fault: Unfetched,
    },
    /// A package depends on itself through the chain of roots given,
    /// outermost first and ending where it began.
    Cycle
    {
        /// The roots, in dependency order.
        chain: Vec<PathBuf>,
    },
    /// A dependency's own lock is missing or does not record what its
    /// dependencies resolve to.
    Unlocked
    {
        /// The dependency.
        coordinate: Coordinate,
        /// Its root, where `gandr lock` writes its lock.
        root: PathBuf,
    },
    /// A dependency has no address.
    Unaddressed
    {
        /// The dependency.
        coordinate: Coordinate,
        /// Why it has none.
        fault: Unaddressed,
    },
    /// A dependency's identity cannot be committed to the store.
    Unstored
    {
        /// The dependency.
        coordinate: Coordinate,
        /// Why the store refused it.
        fault: Box<StoreError>,
    },
}

impl core::fmt::Display for Unresolved
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
                ref why,
            } => write!(
                f,
                "the imports of `{}` cannot be read: {why}",
                source.display()
            ),
            Self::Unpackaged {
                ref coordinate,
                ref path,
            } => write!(
                f,
                "the coordinate `{coordinate}` names `{}`, which roots no package: point it at a \
                 directory holding `package.gandr`",
                path.display()
            ),
            Self::Cycle { ref chain } => {
                f.write_str("DependencyCycle: ")?;
                for (index, root) in chain.iter().enumerate() {
                    if index > 0 {
                        f.write_str(" -> ")?;
                    }
                    write!(f, "`{}`", root.display())?;
                }
                f.write_str(" depend on each other: remove one of the dependencies")
            },
            Self::Unrevisioned {
                ref coordinate,
                ref root,
            } => write!(
                f,
                "the lock at `{}` records no revision of `{coordinate}`: run `gandr lock {}`",
                root.display(),
                root.display()
            ),
            Self::Unfetched {
                ref coordinate,
                ref fault,
            } => write!(f, "the dependency `{coordinate}` is not fetched: {fault}"),
            Self::Unlocked {
                ref coordinate,
                ref root,
            } => write!(
                f,
                "the dependency `{coordinate}` at `{}` is not locked to what its own \
                 dependencies resolve to: run `gandr lock {}`",
                root.display(),
                root.display()
            ),
            Self::Unaddressed {
                ref coordinate,
                ref fault,
            } => write!(f, "the dependency `{coordinate}` has no address: {fault}"),
            Self::Unstored {
                ref coordinate,
                ref fault,
            } => write!(f, "the dependency `{coordinate}` cannot be locked: {fault}"),
        }
    }
}

impl core::error::Error for Unresolved
{
}

/// Why a lock was not reconciled.
#[derive(Debug)]
pub enum LockFault
{
    /// The lock standing records the coordinates given otherwise than they
    /// resolve to, each `LockDrift.<coordinate>`. It was left as it stands.
    Drifted(Vec<Coordinate>),
    /// The lock was edited since the checker wrote it. It was left as it
    /// stands.
    Edited,
    /// The file could not be read or written.
    Io(io::Error),
}

impl core::fmt::Display for LockFault
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
            Self::Drifted(ref coordinates) => {
                for (index, coordinate) in coordinates.iter().enumerate() {
                    if index > 0 {
                        f.write_str(", ")?;
                    }
                    write!(f, "LockDrift.{coordinate}")?;
                }
                f.write_str(
                    ": the lock records another dependency than it resolves to, so it is left as \
                     it stands; relock with `gandr lock`",
                )
            },
            Self::Edited => f.write_str(
                "LockDrift: edited since the checker wrote it, so it is left as it stands; relock \
                 with `gandr lock`",
            ),
            Self::Io(ref error) => write!(f, "{error}"),
        }
    }
}

impl core::error::Error for LockFault
{
}

/// The lock: a file the checker writes from the package's dependencies,
/// written only where none stands. A lock standing otherwise is left as it
/// stands until `gandr lock` relocks it ([`relock`]): [`LockFault::Edited`]
/// for a file edited by hand or no render, and [`LockFault::Drifted`] naming,
/// in order, each coordinate whose entry the standing lock and this one record
/// differently or only one records. A lock recording no dependency leaves no
/// file where none stands.
impl Held for Lock
{
    type Fault = LockFault;

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
        if self.0.is_empty() {
            Absence::Left
        }
        else {
            Absence::Written
        }
    }

    /// # Specification
    /// trivial.
    #[inline]
    fn edited(&self) -> LockFault
    {
        LockFault::Edited
    }

    /// # Specification
    /// trivial.
    #[inline]
    fn differing(
        &self,
        body: Body<'_>,
    ) -> Result<Differing, LockFault>
    {
        let Body(text) = body;
        let standing = parsed(Text(text)).ok_or(LockFault::Edited)?;
        if standing == *self {
            return Ok(Differing::Kept);
        }
        Err(LockFault::Drifted(drifted(&standing, self)))
    }

    /// # Specification
    /// trivial.
    #[inline]
    fn unreadable(error: io::Error) -> LockFault
    {
        LockFault::Io(error)
    }
}

/// Each coordinate that `standing` and `held` record differently, in order.
/// This includes each coordinate that only one of them records.
///
/// # Specification
/// trivial.
fn drifted(
    standing: &Lock,
    held: &Lock,
) -> Vec<Coordinate>
{
    let coordinates: BTreeSet<&Coordinate> = standing.0.keys().chain(held.0.keys()).collect();
    coordinates
        .into_iter()
        .filter(|coordinate| standing.0.get(*coordinate) != held.0.get(*coordinate))
        .cloned()
        .collect()
}

/// Make the lock of `package` agree with `lock`, as `gandr check` does.
///
/// # Specification
/// - requires: nothing.
/// - ensures: for a package below no workspace, the function does
///   [`reconcile`](super::reconcile) of the file at its [`Package::lock`] with
///   `lock`. For a package below a workspace, it works on the table of the
///   package in the workspace lock. If the file or the table is absent and
///   `lock` records a dependency, it adds the table and writes the file. The
///   result is [`Reconciled::Written`]. If `lock` records no dependency, it
///   writes nothing, and the result is [`Reconciled::Unchanged`]. A table that
///   records `lock` is [`Reconciled::Unchanged`]. A different table is
///   [`LockFault::Drifted`]. This fault names each coordinate that the table
///   and `lock` record differently, in order. A file whose header does not hold
///   the digest of its body, or whose body is not a render, is
///   [`LockFault::Edited`]. The function does not change a file that has a
///   fault. It never changes the table of a different package.
/// - provides: the lock step of `gandr check`.
/// - fails: drift, an edited file, or a file that cannot be read or written.
/// - panics: none.
/// - executable: none — the clause is about the file, which the witnesses
///   observe on disk.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — a member's table is written once and kept, another
///   member's run leaves it, and a table recording another lock is drift.
/// - witness: `tests::package::a_workspace_s_packages_share_one_lock_4921`
#[inline]
pub fn reconcile_lock(
    package: &Package,
    lock: &Lock,
) -> Result<Reconciled, LockFault>
{
    let Some((path, member)) = shared(package)
    else {
        return super::reconcile(&package.root().join(LOCK), lock);
    };
    let mut tables = match std::fs::read_to_string(&path) {
        Ok(text) => {
            let split = Split::of(Manifested(&text), Opening(SHARED));
            if matches!(split.authorship(), Authorship::Hand) {
                return Err(LockFault::Edited);
            }
            tables(Text(split.body)).ok_or(LockFault::Edited)?
        },
        Err(error) if error.kind() == io::ErrorKind::NotFound => BTreeMap::new(),
        Err(error) => return Err(LockFault::Io(error)),
    };
    match tables.get(&member) {
        Some(standing) if standing == lock => Ok(Reconciled::Unchanged),
        Some(standing) => Err(LockFault::Drifted(drifted(standing, lock))),
        None if lock.0.is_empty() => Ok(Reconciled::Unchanged),
        None => {
            let _absent = tables.insert(member, lock.clone());
            std::fs::write(&path, shared_render(&tables))
                .map(|()| Reconciled::Written)
                .map_err(LockFault::Io)
        },
    }
}

/// Write `package`'s lock as `lock`, whatever stands there.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the file at the package's [`Package::lock`] holds `lock`'s
///   render: written and [`Reconciled::Written`] where none stood, overwritten
///   and [`Reconciled::Rewritten`] where another stood, and
///   [`Reconciled::Unchanged`] where it already was. A `lock` recording no
///   dependency leaves no file: one standing is removed and is
///   [`Reconciled::Rewritten`]. For a package below a workspace, the render is
///   the workspace lock. In it, the table of the package is `lock`, or the
///   function removes the table if `lock` records nothing. The other tables
///   stay as they are. If the checker did not write the file, the function
///   keeps no other table. It removes a file that has no table.
/// - provides: `gandr lock`.
/// - fails: a file that cannot be read, written or removed.
/// - panics: none.
/// - executable: none — the clause is about the file; the witness observes each
///   case on disk.
///
/// # Errors
/// [`LockFault::Io`].
///
/// # Adequacy
/// - hypothesis: L3 — a drifted lock is rewritten, and `gandr check` then finds
///   it unchanged; relocking a member of a workspace leaves the other's table,
///   and relocking the last table away removes the file.
/// - witness: `tests::package::a_dependency_s_content_edit_drifts_the_lock_until_relocked_3072`
/// - witness: `tests::package::a_workspace_s_packages_share_one_lock_4921`
#[inline]
pub fn relock(
    package: &Package,
    lock: &Lock,
) -> Result<Reconciled, LockFault>
{
    let (path, member) = match shared(package) {
        Some((path, member)) => (path, Some(member)),
        None => (package.root().join(LOCK), None),
    };
    let standing = match std::fs::read_to_string(&path) {
        Ok(standing) => Some(standing),
        Err(error) if error.kind() == io::ErrorKind::NotFound => None,
        Err(error) => return Err(LockFault::Io(error)),
    };
    let rendered = member.map_or_else(
        || (!lock.0.is_empty()).then(|| lock.render()),
        |member| {
            let mut tables = standing
                .as_deref()
                .and_then(|text| {
                    let split = Split::of(Manifested(text), Opening(SHARED));
                    match split.authorship() {
                        Authorship::Checker => tables(Text(split.body)),
                        Authorship::Hand => None,
                    }
                })
                .unwrap_or_default();
            if lock.0.is_empty() {
                let _removed = tables.remove(&member);
            }
            else {
                let _replaced = tables.insert(member, lock.clone());
            }
            (!tables.is_empty()).then(|| shared_render(&tables))
        },
    );
    let Some(rendered) = rendered
    else {
        return match standing {
            Some(_) => std::fs::remove_file(&path)
                .map(|()| Reconciled::Rewritten)
                .map_err(LockFault::Io),
            None => Ok(Reconciled::Unchanged),
        };
    };
    let reconciled = match standing {
        Some(ref standing) if *standing == rendered => return Ok(Reconciled::Unchanged),
        Some(_) => Reconciled::Rewritten,
        None => Reconciled::Written,
    };
    std::fs::write(&path, rendered)
        .map(|()| reconciled)
        .map_err(LockFault::Io)
}

/// The package source of the dependency `coordinate` names from `package`'s
/// root, as its lock records it.
///
/// None when the lock standing for `package` does not record the
/// coordinate, or the directory roots no package: a `path:` coordinate's,
/// and a `gh:` coordinate's checkout at the revision the lock records, which
/// only a resolution fetches.
///
/// # Specification
/// trivial.
#[inline]
#[must_use]
pub fn locked_source(
    package: &Package,
    coordinate: &Coordinate,
) -> Option<PathBuf>
{
    let Maybe::Present(lock) = Lock::read(package)
    else {
        return None;
    };
    let &Locked { revision, .. } = lock.0.get(coordinate)?;
    match *coordinate {
        Coordinate::Path(_) => unpackaged(package.root(), coordinate),
        Coordinate::GitHub(ref repository) => source_of(&fetch::checkout(repository, revision?)?),
    }
}

/// The package source of the dependency `coordinate` names from `directory`,
/// where a source in no package reads it with no lock; none when its
/// directory roots no package, and for a `gh:` coordinate, which only a lock
/// gives a revision.
///
/// # Specification
/// trivial.
#[inline]
#[must_use]
pub fn unpackaged(
    directory: &Path,
    coordinate: &Coordinate,
) -> Option<PathBuf>
{
    match *coordinate {
        Coordinate::Path(ref path) => source_of(&directory.join(path)),
        Coordinate::GitHub(_) => None,
    }
}

/// The package source of the package `directory` roots; none when it roots
/// none.
///
/// # Specification
/// trivial.
fn source_of(directory: &Path) -> Option<PathBuf>
{
    let Maybe::Present(dependency) = Package::discover(directory)
    else {
        return None;
    };
    Some(dependency.source().to_path_buf())
}

/// The file an import through [`STANDARD`] names when no lock records it, the
/// path below it `rest`: the standard library's package source for `std`
/// alone, and the file under its sources otherwise; none when the tree this
/// build was built from holds no standard library.
///
/// **Choice.** The standard library is `library/std` of the tree the driver
/// was built from, the one every toolchain links today. **Reversal.** A
/// toolchain that ships its standard library beside its `gandr` names it
/// there.
///
/// # Specification
/// trivial.
#[inline]
#[must_use]
pub fn standard(rest: Option<&Path>) -> Option<PathBuf>
{
    let Maybe::Present(library) = Package::discover(Path::new(STANDARD_ROOT))
    else {
        return None;
    };
    Some(within(&library, rest))
}

/// The module path of the standard library's source at `path`, `std.io` for
/// its `src/io.gandr` and `std` for its package source: the module whose
/// host interfaces the source names without importing it (#4523).
///
/// # Specification
/// - requires: nothing.
/// - ensures: [`STANDARD`] for the standard library's package source, else
///   [`STANDARD`], a dot and the path's module path under the standard
///   library's sources, as the package walk names it; none for a path outside
///   them, or when the tree this build was built from holds no standard
///   library.
/// - fails: never.
/// - panics: none.
/// - executable: none — the clause reads the file system again.
///
/// # Adequacy
/// - hypothesis: L3 — `std.io`'s file is `std.io`, the package source is `std`,
///   and a source beside the importer is none.
/// - witness: `component::tests::a_std_module_path_names_the_standard_library_from_any_root_4517`
#[must_use]
pub fn standard_module(path: &Path) -> Option<String>
{
    static LIBRARY: std::sync::OnceLock<Option<(PathBuf, PathBuf)>> = std::sync::OnceLock::new();
    let &(ref source, ref sources) = LIBRARY
        .get_or_init(|| match Package::discover(Path::new(STANDARD_ROOT)) {
            Maybe::Present(library) => Some((
                library.source().to_path_buf(),
                std::fs::canonicalize(library.sources()).ok()?,
            )),
            Maybe::Absent(_) => None,
        })
        .as_ref()?;
    let canonical = || std::fs::canonicalize(path).ok();
    if path == source.as_path() || canonical().as_deref() == Some(source.as_path()) {
        return Some(alloc::string::String::from(STANDARD));
    }
    let module = super::module_path(sources, path).or_else(|| {
        let canonical = canonical()?;
        super::module_path(sources, &canonical)
    })?;
    Some(alloc::format!("{STANDARD}.{module}"))
}

/// The file `rest` names in `dependency`: its package source for none, and
/// the file under its sources otherwise.
///
/// # Specification
/// trivial.
fn within(
    dependency: &Package,
    rest: Option<&Path>,
) -> PathBuf
{
    rest.map_or_else(
        || dependency.source().to_path_buf(),
        |rest| dependency.sources().join(rest),
    )
}
