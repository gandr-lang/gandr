//! A package's lock: each dependency its library declares, at the address it
//! was resolved to.
//!
//! # A dependency is named by an alias and found by a coordinate
//!
//! A library declares `pub def dependencies : List(Dependency)`, each an alias
//! a source imports the dependency by and a coordinate saying where it is
//! found. A path coordinate is a directory, read from the dependent's root,
//! that roots a package. [`Package::resolve`] reads each one and checks it as
//! the package it roots, recursively, so a dependency's own dependencies are
//! resolved before it is. A path met twice on one chain is a cycle, refused
//! with the chain.
//!
//! # The lock records pointers, and the address never records a coordinate
//!
//! `gandr.lock` at the package's root maps each alias to its coordinate and a
//! content pointer into the store, the one store of the storage tier a run
//! opens: resolving a dependency commits its address and its signature key
//! there, and the lock records the pointer the value plane returns, as
//! `<digest>:<offset>`. The checker writes the lock once, and every import
//! through the alias reads it back. A lock that says another thing than what
//! the dependencies resolve to is refused as drift, alias by alias, until
//! `gandr lock` writes it again, so a dependency never changes under its
//! dependent unseen. The package's own address digests the addresses its
//! lock's pointers name, read back through the store, and never their
//! coordinates or aliases: where a dependency is found and what it is called
//! are not what the package is.
//!
//! # References
//!
//! - `vault:01a178aa-d585-7822-9cf0-40459729a925` — background: a package
//!   reference is a content address and a separate coordinate never part of
//!   identity, and resolution produces a lock mapping aliases to verified
//!   addresses.
//! - `vault:01a17cb3-d471-72b2-9bd2-70a46f74c3de` — background: the storage
//!   tier is the one store the lock, the build layer and the verdict cache
//!   share.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use core::fmt::Write as _;
use std::io;
use std::path::Path;
use std::path::PathBuf;

use anodized::spec;
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
use gandr_surface_lowering::SurfaceName;
use quenchant_shape::shape::Maybe;

use super::Absence;
use super::Authorship;
use super::Basic;
use super::Body;
use super::DIGEST;
use super::Differing;
use super::Held;
use super::Identity;
use super::Key;
use super::Manifested;
use super::Opening;
use super::Package;
use super::PackageAddress;
use super::Reconciled;
use super::Split;
use super::Unaddressed;
use super::package_root;
use crate::component::Unshadowed;
use crate::evaluate::declaration_name;
use crate::workspace::Spelling;
use crate::workspace::Unran;
use crate::workspace::ran_alone;

/// The file name of the lock the checker writes at a package's root.
pub const LOCK: &str = "gandr.lock";

/// The declaration of a library that names its dependencies.
pub(super) const DEPENDENCIES: &str = "dependencies";

/// The line that opens a lock the checker wrote.
const WRITTEN: &str = "# Written by `gandr check` from the package's `dependencies`: relock with \
                       `gandr lock`, never by hand.";

/// The line that opens the lock's table.
const TABLE: &str = "[dependencies]";

/// The name a source imports a dependency by.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Alias(String);

impl Alias
{
    /// The alias `name`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(name: String) -> Self
    {
        Self(name)
    }
}

impl AsRef<str> for Alias
{
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &str
    {
        &self.0
    }
}

impl core::fmt::Display for Alias
{
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        f.write_str(&self.0)
    }
}

/// Where a dependency is found: never part of what it is.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Coordinate
{
    /// A directory rooting the dependency, read from the dependent's root, as
    /// the library writes it.
    Path(String),
}

/// A dependency as a library declares it.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Dependency
{
    /// The name its dependent imports it by.
    pub alias: Alias,
    /// Where it is found.
    pub coordinate: Coordinate,
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

/// A dependency as its dependent's lock records it.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Locked
{
    /// Where it is found.
    pub coordinate: Coordinate,
    /// Where what it resolved to, its address and its signature key, stands
    /// in the store.
    pub pointer: ContentPtr,
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

/// A package's lock: each dependency by its alias.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Lock(BTreeMap<Alias, Locked>);

impl Lock
{
    /// The dependency the lock records under `alias`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn locked(
        &self,
        alias: &Alias,
    ) -> Option<&Locked>
    {
        self.0.get(alias)
    }

    /// Each alias the lock records, in order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn aliases(&self) -> impl Iterator<Item = &Alias>
    {
        self.0.keys()
    }

    /// Each alias the lock records, in order, with the dependency it locks and
    /// the address of the identity its pointer names, read back through
    /// `store`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one entry per alias, in order: the alias, its locked
    ///   dependency, and the address of the identity its pointer names, or
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
    ) -> impl Iterator<
        Item = (
            &'lock Alias,
            &'lock Locked,
            Result<PackageAddress, Unaddressed>,
        ),
    > + 'lock
    {
        self.0.iter().map(|(alias, locked)| {
            let address = store
                .deref::<Identity>(locked.pointer)
                .map(|identity| identity.address)
                .map_err(|fault| Unaddressed::Unstored {
                    alias: alias.clone(),
                    fault: Box::new(fault),
                });
            (alias, locked, address)
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
    /// - fails: [`Unaddressed::Unstored`] at the first alias whose pointer the
    ///   store cannot read back as an identity.
    /// - panics: none.
    /// - executable: none — the identities are the store's.
    ///
    /// # Errors
    /// [`Unaddressed::Unstored`], as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a dependency's content edit moves its dependent's
    ///   address, and a pointer the store cannot answer leaves the dependent
    ///   unaddressed by the alias.
    /// - witness: `tests::package::a_dependency_s_content_edit_drifts_the_lock_until_relocked_3072`
    /// - witness: `tests::package::a_pointer_the_store_cannot_answer_leaves_the_dependent_unaddressed_3157`
    #[inline]
    pub fn addresses(
        &self,
        store: &Store,
    ) -> Result<BTreeSet<PackageAddress>, Unaddressed>
    {
        self.resolved(store)
            .map(|(_, _, address)| address)
            .collect()
    }

    /// The lock as the checker writes it: the header, then the body.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the [`WRITTEN`] line, the digest line carrying the BLAKE3
    ///   digest of the body in lowercase hexadecimal, then the body: a
    ///   `[dependencies]` table holding one line per alias in order, `alias = {
    ///   path = "…", pointer = "<digest>:<offset>" }`, the alias bare when it
    ///   is a TOML bare key and a basic string otherwise, the path a basic
    ///   string, the digest lowercase hexadecimal and the offset decimal. The
    ///   same lock renders the same bytes wherever it is rendered, and
    ///   [`Lock::read`] reads the render back as the lock.
    /// - provides: the file [`reconcile`](super::reconcile) and [`relock`]
    ///   write.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a lock is written, read back equal and written again
    ///   byte for byte from another working directory.
    /// - witness: `tests::package::a_lock_is_written_once_and_reads_alike_from_anywhere_3072`
    #[spec(ensures: |ref ret| ret.starts_with(WRITTEN)
        && matches!(Split::of(Manifested(ret), Opening(WRITTEN)).authorship(), Authorship::Checker))]
    #[inline]
    #[must_use]
    pub fn render(&self) -> String
    {
        let mut body = format!("\n{TABLE}\n");
        for (alias, locked) in &self.0 {
            let Coordinate::Path(ref path) = locked.coordinate;
            let _written = writeln!(
                body,
                "{} = {{ path = {}, pointer = \"{}:{}\" }}",
                Key(&alias.0),
                Basic(path),
                locked.pointer.digest(),
                locked.pointer.offset()
            );
        }
        format!(
            "{WRITTEN}\n{DIGEST}{}\n{body}",
            blake3::hash(body.as_bytes()).to_hex()
        )
    }

    /// The lock standing at `package`'s root, as the checker wrote it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the lock [`Lock::render`] would write as the file at the
    ///   package's [`LOCK`] stands; `Unwritten` when no file stands there or it
    ///   cannot be read, `Edited` when its header does not carry its body's
    ///   digest, and `Unread` when its body is not a render.
    /// - provides: the lock every import through an alias, and every check of a
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
        let Ok(text) = std::fs::read_to_string(package.root().join(LOCK))
        else {
            return Maybe::Absent(lock_file::Absent::Unwritten);
        };
        let split = Split::of(Manifested(&text), Opening(WRITTEN));
        if matches!(split.authorship(), Authorship::Hand) {
            return Maybe::Absent(lock_file::Absent::Edited);
        }
        parsed(Text(split.body)).map_or(Maybe::Absent(lock_file::Absent::Unread), Maybe::Present)
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
        let (alias, Text(rest)) = if line.starts_with('"') {
            Text(line).basic()?
        }
        else {
            let (alias, _) = line.split_once(' ')?;
            (String::from(alias), Text(line.get(alias.len() ..)?))
        };
        let (path, Text(rest)) = Text(rest.strip_prefix(" = { path = ")?).basic()?;
        let (digest, Text(rest)) = Text(rest.strip_prefix(", pointer = \"")?).digest()?;
        let (offset, rest) = rest.strip_prefix(':')?.split_once('"')?;
        let parsed: u32 = offset.parse().ok()?;
        let canonical = offset.bytes().all(|digit| digit.is_ascii_digit())
            && (offset == "0" || !offset.starts_with('0'));
        if rest != " }" || !canonical {
            return None;
        }
        let _first = lock.insert(Alias(alias), Locked {
            coordinate: Coordinate::Path(path),
            pointer: ContentPtr::new(ChunkDigest::from(digest.0), TokenOffset::from(parsed)),
        });
    }
    Some(Lock(lock))
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
    /// The dependencies the package's library declares, in the order it lists
    /// them.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the library checked alone over the sources it imports and its
    ///   `dependencies` run, as [`ran_alone`] does; each element of the list
    ///   its alias and its path coordinate. None when the library declares no
    ///   `dependencies`.
    /// - provides: the dependencies [`Package::resolve`] resolves.
    /// - fails: [`Unresolved::Undeclared`] for a library that cannot be read or
    ///   is refused as a whole, or whose `dependencies` runs to no list of
    ///   dependencies.
    /// - panics: none.
    /// - executable: none — as [`ran_alone`].
    ///
    /// # Errors
    /// [`Unresolved::Undeclared`], as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a library naming one dependency reads it, and one
    ///   naming none reads none.
    /// - witness: `tests::package::a_lock_is_written_once_and_reads_alike_from_anywhere_3072`
    #[inline]
    pub fn dependencies(&self) -> Result<Vec<Dependency>, Unresolved>
    {
        let undeclared = |why: String| Unresolved::Undeclared {
            package: self.root.clone(),
            why,
        };
        let came = match ran_alone(&self.library, [SurfaceName::from(DEPENDENCIES)]) {
            Ok([Maybe::Present(came)]) => came,
            Ok([Maybe::Absent(declaration_name::Absent::Undeclared)]) => return Ok(Vec::new()),
            Err(Unran::Unread { message }) => return Err(undeclared(message)),
            Err(Unran::Refused { why }) => return Err(undeclared(why)),
        };
        let listed = Spelling::from(came.as_str())
            .dependencies()
            .ok_or_else(|| undeclared(format!("`{DEPENDENCIES}` runs to `{came}`")))?;
        Ok(listed
            .into_iter()
            .map(|(alias, path)| Dependency {
                alias: Alias(alias),
                coordinate: Coordinate::Path(path),
            })
            .collect())
    }

    /// The lock the package's dependencies resolve to: each one found at its
    /// coordinate, its own dependencies resolved and locked first, and
    /// addressed.
    ///
    /// # Specification
    /// - requires: `grammar` is the grammar the packages' sources are read
    ///   under.
    /// - ensures: for each of [`Package::dependencies`], the package its path,
    ///   read from this package's root, roots; its own dependencies resolved
    ///   the same way first, depth first with an explicit stack of the packages
    ///   being resolved, and the lock standing at its root, which must be the
    ///   one they resolve to — none at all when it has none; then its address
    ///   over its own items and that lock's addresses, read back through
    ///   `store`, and its signature key, as [`Package::identity`] gives them,
    ///   committed to `store` together. Each dependency is locked under its
    ///   alias at its coordinate by the pointer the commit returns. The lock is
    ///   a function of the packages' contents and coordinates alone, whatever
    ///   directory the process runs in and whatever the store held.
    /// - provides: the lock `gandr check` reconciles and `gandr lock` writes.
    /// - fails: [`Unresolved`], at the first dependency that does not resolve.
    /// - panics: none.
    /// - executable: none — the clause reads the file system and lowers every
    ///   package again; the witnesses observe each outcome.
    ///
    /// # Errors
    /// [`Unresolved::Unpackaged`] for a coordinate rooting no package,
    /// [`Unresolved::Cycle`] for a root met twice on one chain,
    /// [`Unresolved::Unlocked`] for a dependency whose own lock is missing or
    /// stale, [`Unresolved::Twice`] for an alias declared twice,
    /// [`Unresolved::Unaddressed`] for a dependency with no address,
    /// [`Unresolved::Unstored`] for an identity the store cannot commit, and
    /// [`Unresolved::Undeclared`] as [`Package::dependencies`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one dependency resolves alike from two working
    ///   directories; a content edit to it moves its address and an inert edit
    ///   does not; two packages depending on each other are refused with their
    ///   chain.
    /// - witness: `tests::package::a_lock_is_written_once_and_reads_alike_from_anywhere_3072`
    /// - witness: `tests::package::a_dependency_s_content_edit_drifts_the_lock_until_relocked_3072`
    /// - witness: `tests::package::a_dependency_cycle_is_refused_by_its_paths_3072`
    #[inline]
    pub fn resolve(
        &self,
        grammar: &gandr_surface_grammar::Pbg,
        store: &mut Store,
    ) -> Result<Lock, Unresolved>
    {
        let mut open = BTreeSet::from([self.root.clone()]);
        let mut frames = Vec::from([Frame::of(self.clone(), None)?]);
        loop {
            let Some(frame) = frames.last_mut()
            else {
                return Ok(Lock::default());
            };
            if let Some(Dependency { alias, coordinate }) = frame.pending.next() {
                let Coordinate::Path(ref path) = coordinate;
                let directory = frame.package.root.join(path);
                let rooted = directory.canonicalize().ok();
                let dependency = match Self::discover(&directory) {
                    Maybe::Present(found) if rooted.as_deref() == Some(found.root()) => found,
                    Maybe::Present(_) | Maybe::Absent(package_root::Absent::Unpackaged) => {
                        return Err(Unresolved::Unpackaged {
                            alias,
                            path: directory,
                        });
                    },
                };
                if !open.insert(dependency.root.clone()) {
                    return Err(cycle(&frames, dependency.root));
                }
                frames.push(Frame::of(dependency, Some((alias, coordinate)))?);
                continue;
            }
            let Some(Frame {
                package,
                via,
                entries,
                ..
            }) = frames.pop()
            else {
                return Ok(Lock::default());
            };
            let _closed = open.remove(&package.root);
            let own = Lock(entries);
            let (Some(parent), Some((alias, coordinate))) = (frames.last_mut(), via)
            else {
                return Ok(own);
            };
            let standing = match Lock::read(&package) {
                Maybe::Present(standing) => standing,
                Maybe::Absent(_) => Lock::default(),
            };
            if standing != own {
                return Err(Unresolved::Unlocked {
                    alias,
                    root: package.root,
                });
            }
            let identity = package
                .identity(grammar, &Unshadowed, &own, store)
                .map_err(|fault| Unresolved::Unaddressed {
                    alias: alias.clone(),
                    fault,
                })?;
            let pointer = store
                .commit(&identity)
                .map_err(|fault| Unresolved::Unstored {
                    alias: alias.clone(),
                    fault: Box::new(fault),
                })?;
            let twice = Unresolved::Twice {
                alias: alias.clone(),
            };
            if parent
                .entries
                .insert(alias, Locked {
                    coordinate,
                    pointer,
                })
                .is_some()
            {
                return Err(twice);
            }
        }
    }
}

/// One package being resolved: the dependencies of it left to resolve, and
/// the entries of its lock so far.
struct Frame
{
    /// The package.
    package: Package,
    /// The alias and coordinate its dependent names it by; none for the
    /// package resolution started at.
    via: Option<(Alias, Coordinate)>,
    /// Its dependencies not yet resolved, in the order its library lists
    /// them.
    pending: alloc::vec::IntoIter<Dependency>,
    /// Its dependencies resolved so far, by alias.
    entries: BTreeMap<Alias, Locked>,
}

impl Frame
{
    /// `package`, named by `via`, its dependencies all left to resolve.
    ///
    /// # Specification
    /// trivial.
    fn of(
        package: Package,
        via: Option<(Alias, Coordinate)>,
    ) -> Result<Self, Unresolved>
    {
        let pending = package.dependencies()?.into_iter();
        Ok(Self {
            package,
            via,
            pending,
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
    /// A library's `dependencies` cannot be read, or runs to no list of
    /// dependencies.
    Undeclared
    {
        /// The root of the package declaring it.
        package: PathBuf,
        /// Why, spelled.
        why: String,
    },
    /// A dependency's coordinate roots no package.
    Unpackaged
    {
        /// The dependency.
        alias: Alias,
        /// The directory its coordinate names.
        path: PathBuf,
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
        alias: Alias,
        /// Its root, where `gandr lock` writes its lock.
        root: PathBuf,
    },
    /// An alias is declared twice.
    Twice
    {
        /// The alias.
        alias: Alias,
    },
    /// A dependency has no address.
    Unaddressed
    {
        /// The dependency.
        alias: Alias,
        /// Why it has none.
        fault: Unaddressed,
    },
    /// A dependency's identity cannot be committed to the store.
    Unstored
    {
        /// The dependency.
        alias: Alias,
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
            Self::Undeclared {
                ref package,
                ref why,
            } => write!(
                f,
                "the dependencies of `{}` cannot be read: {why}; declare `pub def {DEPENDENCIES} \
                 : List(Dependency)` in its library",
                package.display()
            ),
            Self::Unpackaged {
                ref alias,
                ref path,
            } => write!(
                f,
                "the dependency `{alias}` names `{}`, which roots no package: point its \
                 coordinate at a directory holding `lib.gandr` or `src/lib.gandr`",
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
            Self::Unlocked {
                ref alias,
                ref root,
            } => write!(
                f,
                "the dependency `{alias}` at `{}` is not locked to what its own dependencies \
                 resolve to: run `gandr lock {}`",
                root.display(),
                root.display()
            ),
            Self::Twice { ref alias } => write!(
                f,
                "the dependency `{alias}` is declared twice: give each dependency its own alias"
            ),
            Self::Unaddressed {
                ref alias,
                ref fault,
            } => write!(f, "the dependency `{alias}` has no address: {fault}"),
            Self::Unstored {
                ref alias,
                ref fault,
            } => write!(f, "the dependency `{alias}` cannot be locked: {fault}"),
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
    /// The lock standing records the aliases given otherwise than the
    /// dependencies resolve to, each `LockDrift.<alias>`. It was left as it
    /// stands.
    Drifted(Vec<Alias>),
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
            Self::Drifted(ref aliases) => {
                for (index, alias) in aliases.iter().enumerate() {
                    if index > 0 {
                        f.write_str(", ")?;
                    }
                    write!(f, "LockDrift.{alias}")?;
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
/// in order, each alias whose entry the standing lock and this one record
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
        let aliases: BTreeSet<&Alias> = standing.0.keys().chain(self.0.keys()).collect();
        Err(LockFault::Drifted(
            aliases
                .into_iter()
                .filter(|alias| standing.0.get(*alias) != self.0.get(*alias))
                .cloned()
                .collect(),
        ))
    }

    /// # Specification
    /// trivial.
    #[inline]
    fn unreadable(error: io::Error) -> LockFault
    {
        LockFault::Io(error)
    }
}

/// Write the lock at `package`'s root as `lock`, whatever stands there.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the file at the package's [`LOCK`] is `lock`'s render: written
///   and [`Reconciled::Written`] where none stood, overwritten and
///   [`Reconciled::Rewritten`] where another stood, and
///   [`Reconciled::Unchanged`] where it already was. A `lock` recording no
///   dependency leaves no file: one standing is removed and is
///   [`Reconciled::Rewritten`].
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
///   it unchanged.
/// - witness: `tests::package::a_dependency_s_content_edit_drifts_the_lock_until_relocked_3072`
#[inline]
pub fn relock(
    package: &Package,
    lock: &Lock,
) -> Result<Reconciled, LockFault>
{
    let path = package.root().join(LOCK);
    let standing = match std::fs::read_to_string(&path) {
        Ok(standing) => Some(standing),
        Err(error) if error.kind() == io::ErrorKind::NotFound => None,
        Err(error) => return Err(LockFault::Io(error)),
    };
    if lock.0.is_empty() {
        return match standing {
            Some(_) => std::fs::remove_file(&path)
                .map(|()| Reconciled::Rewritten)
                .map_err(LockFault::Io),
            None => Ok(Reconciled::Unchanged),
        };
    }
    let rendered = lock.render();
    let reconciled = match standing {
        Some(ref standing) if *standing == rendered => return Ok(Reconciled::Unchanged),
        Some(_) => Reconciled::Rewritten,
        None => Reconciled::Written,
    };
    std::fs::write(&path, rendered)
        .map(|()| reconciled)
        .map_err(LockFault::Io)
}

/// The file an import through the alias `head` of a module path names in
/// `package`, the path below it `rest`: the dependency's library for the alias
/// alone, and the file under its sources otherwise; none when the lock
/// standing at `package`'s root records no such alias, or the dependency it
/// records roots no package.
///
/// # Specification
/// trivial.
#[inline]
pub fn through(
    package: &Package,
    head: &Alias,
    rest: Option<&Path>,
) -> Option<PathBuf>
{
    let Maybe::Present(lock) = Lock::read(package)
    else {
        return None;
    };
    let Coordinate::Path(ref path) = lock.locked(head)?.coordinate;
    let Maybe::Present(dependency) = Package::discover(&package.root().join(path))
    else {
        return None;
    };
    Some(rest.map_or_else(
        || dependency.library().to_path_buf(),
        |rest| dependency.sources().join(rest),
    ))
}
