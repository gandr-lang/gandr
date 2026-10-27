//! A package's export: each kernel artifact a `check` of the package admitted,
//! once, under the paths of the sources it was admitted for, committed through
//! the store's value plane and named by the root `export/<package address>`.
//!
//! # The export is what the walk admitted
//!
//! A walk admits each import-connected component of the sources it is given
//! once, and every source of the component carries the one artifact
//! (`crate::component`). [`Exporting`] takes the walk's steps for one package
//! as they come, keeps each artifact the first time a source carries it, and
//! files each later source under the artifact it carries; a source that does
//! not settle, or that the walk could not carry through, leaves the package
//! with no export. So the export costs the walk no second judgement, and a
//! package checked whole exports the same value however often it is checked.
//!
//! **Choice.** Every artifact the walk admitted for the package's sources,
//! each under its sources' paths, read from the package's root.
//! **Alternatives.** The library's artifact alone, which holds what an import
//! of the library reads but leaves out every source no import reaches, and
//! which the walk admits apart from the library only when nothing else joins
//! its component. **Reversal.** A dependent that admits a dependency's export
//! whole reads the library's own unit, and the export narrows to it.
//!
//! # A pointer names bytes, never an admission
//!
//! An artifact commits as its declaration records, in
//! `gandr_storage_artifact`'s value-plane codec, so artifacts that share a run
//! of leading declarations, the prelude's among them, share its chunks.
//! [`Export::artifact`] reassembles one artifact's bytes. Whether they are an
//! artifact is the kernel's decoder's to say, and admitting them is the
//! consumer's: [`Export::readmit`] decodes each artifact and replays it into
//! an environment of its own, the admission a dependent's `check` runs over
//! each dependency's export. One environment per artifact, since the atoms an
//! artifact mints are fresh only within it.
//!
//! # References
//!
//! - `vault:01a178aa-ce14-7610-bcad-5aab5f9c0b0f` — background: a content
//!   pointer is integrity, never validity; the kernel's decoder and admission
//!   stay the wall.
//! - `vault:01a17cb3-d471-72b2-9bd2-70a46f74c3de` — background: the storage
//!   tier is the one store the lock, the build layer and the verdict cache
//!   share.
//! - `vault:01a178aa-d585-7822-9cf0-40459729a925` — background: a dependency
//!   hydrates from the persistent store, and a minted atom is fresh only within
//!   the artifact that mints it.

use alloc::collections::BTreeMap;
use alloc::string::String;
use std::path::Path;
use std::path::PathBuf;

use anodized::spec;
use gandr_kernel_core::ArtifactRefusal;
use gandr_kernel_core::Environment;
use gandr_kernel_term::DecodeError;
use gandr_kernel_term::decode;
use gandr_storage_artifact::ArtifactError;
use gandr_storage_artifact::ArtifactRecordSet;
use gandr_storage_artifact::ReassembledArtifact;
use gandr_storage_store::ContentPtr;
use gandr_storage_store::RootName;
use gandr_storage_store::Store;
use gandr_storage_store::StoreError;
use gandr_storage_store::Stored;
use gandr_storage_values::CanonicalValue;
use gandr_storage_values::CanonicalWord;
use gandr_storage_values::CodecId;
use gandr_storage_values::CodecIdentity;
use gandr_storage_values::CodecVersion;
use gandr_storage_values::ConstructorTag;
use gandr_storage_values::TokenBytes;
use gandr_storage_values::TokenReader;
use gandr_storage_values::TokenSink;
use gandr_storage_values::ValueError;
use gandr_surface_lowering::DeclarationCount;
use quenchant_shape::shape::Maybe;

use super::PackageAddress;
use crate::compose::Composed;
use crate::walk::Standing;
use crate::walk::Step;

/// The tag an export opens with, and its codec's identifier.
const EXPORT: u8 = 0x1E_u8;

/// The tag each admitted artifact opens with inside an export.
const ADMITTED: u8 = 0x1F_u8;

/// A source's path from the package's root, its components joined by `/`.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
struct Spelling(Box<[u8]>);

/// One artifact the walk admitted, and the sources it was admitted for.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Admitted
{
    /// The artifact's declaration records.
    artifact: ArtifactRecordSet,
    /// Each source's spelling, in walk order.
    sources: Vec<Spelling>,
}

/// A package's export: each artifact a walk of it admitted, in the order its
/// first source came, under its sources' paths.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Export(Vec<Admitted>);

quenchant_shape::reason_enum! {
    /// Why an export holds no artifact for a source.
    pub mod exported_source {
        /// The reason none is held.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No artifact of the export was admitted for the source.
            Unexported,
        }
    }
}

/// `source`'s components joined by `/`, or nothing when one is not UTF-8.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the bytes of each component of `source` in order, `/` between
///   two; nothing when a component does not spell as UTF-8.
/// - provides: the one spelling an export files a source under and looks it up
///   by, alike on every host.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a source in a directory of the package is found by the
///   path it was filed under.
/// - witness: `tests::package::a_package_s_export_holds_what_its_check_admitted_3225`
#[spec(ensures: |ret| ret.as_ref().is_none_or(|spelled| !spelled.0.ends_with(b"/")))]
fn spelled(source: &Path) -> Option<Spelling>
{
    let mut spelling = Vec::new();
    for component in source {
        if !spelling.is_empty() {
            spelling.push(b'/');
        }
        spelling.extend_from_slice(component.to_str()?.as_bytes());
    }
    Some(Spelling(spelling.into_boxed_slice()))
}

impl Export
{
    /// The root the export of the package at `address` is named by.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn root(address: &PackageAddress) -> RootName
    {
        RootName::new(format!("export/{address}"))
    }

    /// Commit the export into `store` and name it by the root of the package
    /// at `address`.
    ///
    /// # Specification
    /// - requires: `address` is the address of the package the export is of.
    /// - ensures: on success the pointer [`Store::commit`] returns for the
    ///   export, which [`Export::root`] of `address` then names, whatever it
    ///   named before.
    /// - provides: the one write of a package's export.
    /// - fails: the store's faults, committing or naming.
    /// - panics: none.
    /// - executable: none — the outcome is the store's on disk.
    ///
    /// # Errors
    /// [`StoreError`], as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a package's export committed under its address is
    ///   named by the address's root and reads back equal, and committing it
    ///   again names the same pointer.
    /// - witness: `tests::package::a_package_s_export_holds_what_its_check_admitted_3225`
    #[inline]
    pub fn commit(
        &self,
        store: &mut Store,
        address: &PackageAddress,
    ) -> Result<ContentPtr, StoreError>
    {
        let pointer = store.commit(self)?;
        store.set_root(Self::root(address), pointer)?;
        Ok(pointer)
    }

    /// The bytes of the artifact admitted for `source`, read from the
    /// package's root, for the kernel's decoder.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the reassembled artifact filed under `source`'s spelling;
    ///   [`exported_source::Absent::Unexported`] when none is.
    /// - provides: a consumer's read of one source's artifact.
    /// - fails: never; an absent source is the answer's absence.
    /// - panics: none.
    /// - executable: none — the answer is the body's one search of the export,
    ///   which a predicate could only repeat; the witness reads each source's
    ///   bytes against the walk's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each source of a package reads back the artifact its
    ///   walk admitted it with, byte for byte, and a path the package does not
    ///   hold reads back none.
    /// - witness: `tests::package::a_package_s_export_holds_what_its_check_admitted_3225`
    #[inline]
    pub fn artifact(
        &self,
        source: &Path,
    ) -> Maybe<ReassembledArtifact, exported_source::Absent>
    {
        spelled(source)
            .and_then(|spelling| {
                self.0
                    .iter()
                    .find(|admitted| admitted.sources.contains(&spelling))
            })
            .map_or(
                Maybe::Absent(exported_source::Absent::Unexported),
                |admitted| Maybe::Present(admitted.artifact.reassemble()),
            )
    }

    /// Re-admit each artifact of the export through the kernel: decoded by
    /// its bounded decoder, then replayed into a fresh environment of its own.
    ///
    /// # Specification
    /// - requires: nothing; the export may hold any bytes.
    /// - ensures: the count of declarations the kernel re-admitted across the
    ///   artifacts, when every one decodes and replays. Otherwise
    ///   [`Unreadmitted::Undecoded`] for the first artifact the decoder refuses
    ///   and [`Unreadmitted::Refused`] for the first one whose replay rejects a
    ///   declaration, each naming the first source the artifact was admitted
    ///   for. No environment outlives its artifact's replay, so the atoms one
    ///   artifact mints never meet another's.
    /// - provides: the admission of a stored export by its consumer, the inner
    ///   wall a pointer to it never stands for.
    /// - fails: [`Unreadmitted`], as above.
    /// - panics: none.
    /// - executable: none — the answer is the kernel's replay, which a
    ///   predicate could only run again.
    ///
    /// # Errors
    /// [`Unreadmitted`], as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a committed export, read back by its root, re-admits
    ///   every declaration of each artifact its walk admitted, each artifact
    ///   once; one whose last declaration was rewritten after admission to a
    ///   body no binder holds is refused at that declaration, naming its
    ///   source. The decoder's refusal is excluded: an export's records were
    ///   cut by the decoder, so within one format version they reassemble to
    ///   bytes it reads.
    /// - witness: `tests::package::a_dependency_s_export_is_re_admitted_through_the_kernel_3285`
    #[inline]
    pub fn readmit(&self) -> Result<DeclarationCount, Unreadmitted>
    {
        let mut declarations = 0_usize;
        for admitted in &self.0 {
            let source = || {
                admitted
                    .sources
                    .first()
                    .map_or_else(String::new, |spelling| {
                        String::from_utf8_lossy(&spelling.0).into_owned()
                    })
            };
            let image = admitted.artifact.reassemble();
            let (arena, marked) = decode(image.as_image())
                .map_err(|refusal| Unreadmitted::Undecoded {
                    source: source(),
                    refusal,
                })?
                .into_parts();
            let _replayed =
                Environment::replay(arena, &marked).map_err(|refusal| Unreadmitted::Refused {
                    source: source(),
                    refusal,
                })?;
            declarations = declarations.saturating_add(marked.len());
        }
        Ok(DeclarationCount::from(declarations))
    }
}

impl CanonicalValue for Export
{
    /// The export as one constructor: the count of artifacts, then each as a
    /// constructor holding its records, its count of sources and each
    /// source's path.
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
        // A count widens to the word whole on every host whose addresses are
        // sixty-four bits or fewer; past that, the word's ceiling.
        sink.open(ConstructorTag::from(EXPORT))?;
        sink.word(CanonicalWord::from(
            u64::try_from(self.0.len()).unwrap_or(u64::MAX),
        ))?;
        for admitted in &self.0 {
            sink.open(ConstructorTag::from(ADMITTED))?;
            admitted.artifact.emit_tokens(sink)?;
            sink.word(CanonicalWord::from(
                u64::try_from(admitted.sources.len()).unwrap_or(u64::MAX),
            ))?;
            for source in &admitted.sources {
                sink.bytes(TokenBytes::from(&*source.0))?;
            }
            sink.close()?;
        }
        sink.close()
    }

    /// The export [`Export::emit_tokens`] wrote.
    ///
    /// # Specification
    /// - requires: `reader` stands at an export's constructor.
    /// - ensures: on success the artifacts and their sources the stream spells,
    ///   in its order.
    /// - provides: the read [`Store::deref`] makes of an export's root.
    /// - fails: [`ValueError::UnexpectedConstructor`] for a constructor other
    ///   than an export's or an artifact's where one stands, an artifact's own
    ///   refusals, and the reader's.
    /// - panics: none.
    /// - executable: none — the reader's stream is the store's.
    ///
    /// # Errors
    /// [`ValueError`], as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an export committed into a store reads back from it,
    ///   each source's artifact intact.
    /// - witness: `tests::package::a_package_s_export_holds_what_its_check_admitted_3225`
    #[inline]
    fn decode_tokens(reader: &mut TokenReader<'_>) -> Result<Self, ValueError>
    {
        let opened = |reader: &mut TokenReader<'_>, expected: u8| {
            let position = reader.position();
            let found = reader.read_tag()?;
            if found == ConstructorTag::from(expected) {
                Ok(())
            }
            else {
                Err(ValueError::UnexpectedConstructor { found, position })
            }
        };
        opened(reader, EXPORT)?;
        // Each count is the stream's claim, so it bounds a loop and never
        // reserves memory: a short stream is refused when it runs out.
        let mut export = Vec::new();
        for _admitted in 0_u64 .. u64::from(reader.read_word()?) {
            opened(reader, ADMITTED)?;
            let artifact = ArtifactRecordSet::decode_tokens(reader)?;
            let mut sources = Vec::new();
            for _source in 0_u64 .. u64::from(reader.read_word()?) {
                sources.push(Spelling(Box::from(<&[u8]>::from(reader.read_bytes()?))));
            }
            reader.read_close()?;
            export.push(Admitted { artifact, sources });
        }
        reader.read_close()?;
        Ok(Self(export))
    }
}

impl Stored for Export
{
    /// # Specification
    /// trivial.
    #[inline]
    fn codec() -> CodecIdentity
    {
        CodecIdentity::new(CodecId::from(u16::from(EXPORT)), CodecVersion::from(1_u16))
    }
}

/// A package's export as a walk's steps build it.
#[derive(Debug, Default)]
pub struct Exporting
{
    /// The artifacts kept so far.
    admitted: Vec<Admitted>,
    /// Each kept artifact's place, by the BLAKE3 digest of its bytes.
    seen: BTreeMap<[u8; 32], usize>,
    /// Why the package has no export, once a step says so.
    broken: Option<Unexported>,
}

impl Exporting
{
    /// Take `step`, a step of the walk for the source at `source`, read from
    /// the package's root.
    ///
    /// # Specification
    /// - requires: `step` is of a source of the package, and `source` its path
    ///   from the package's root.
    /// - ensures: a settled source carrying an artifact is filed under the
    ///   artifact, which is kept the first time a source carries it; any other
    ///   step leaves the package with no export, naming the first source that
    ///   did, and so does a source whose path does not spell as UTF-8 or whose
    ///   artifact does not cut into declaration records. Once the package has
    ///   no export, no step changes anything.
    /// - provides: the one way an export is built.
    /// - fails: never; a step that breaks the export is recorded.
    /// - panics: none.
    /// - executable: none — the steps are the walk's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a package of three sources, two joined by an import,
    ///   exports two artifacts, the joined sources under one; a package with an
    ///   unsettled source exports nothing, naming it.
    /// - witness: `tests::package::a_package_s_export_holds_what_its_check_admitted_3225`
    #[inline]
    pub fn take(
        &mut self,
        source: &Path,
        step: &Step<'_>,
    )
    {
        if self.broken.is_some() {
            return;
        }
        let kernel = match *step {
            Step::Source {
                standing: Standing::Settled,
                composed:
                    Composed::Settled {
                        kernel: Maybe::Present(ref kernel),
                        ..
                    },
                ..
            } => kernel,
            Step::Source { .. } => {
                self.broken = Some(Unexported::Unsettled {
                    source: source.to_path_buf(),
                });
                return;
            },
            Step::Fault { .. } => {
                self.broken = Some(Unexported::Faulted {
                    source: source.to_path_buf(),
                });
                return;
            },
        };
        let Some(spelling) = spelled(source)
        else {
            self.broken = Some(Unexported::Unspelled {
                source: source.to_path_buf(),
            });
            return;
        };
        let digest = *blake3::hash(kernel.as_ref()).as_bytes();
        if let Some(admitted) = self
            .seen
            .get(&digest)
            .and_then(|&place| self.admitted.get_mut(place))
        {
            admitted.sources.push(spelling);
            return;
        }
        match ArtifactRecordSet::from_artifact(kernel.as_image()) {
            Ok(artifact) => {
                let _fresh = self.seen.insert(digest, self.admitted.len());
                self.admitted.push(Admitted {
                    artifact,
                    sources: vec![spelling],
                });
            },
            Err(fault) => {
                self.broken = Some(Unexported::Uncut {
                    source: source.to_path_buf(),
                    fault,
                });
            },
        }
    }

    /// The export the steps taken build, or why there is none.
    ///
    /// # Specification
    /// - requires: every step of the package's sources was taken.
    /// - ensures: the artifacts kept, in the order their first sources came,
    ///   each under its sources' paths; or the first reason a step gave.
    /// - provides: what `gandr check` commits for a package.
    /// - fails: [`Unexported`], as [`Exporting::take`] recorded it.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Unexported`], as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Exporting::take`].
    /// - witness: `tests::package::a_package_s_export_holds_what_its_check_admitted_3225`
    #[inline]
    #[spec(
        captures: [whole = self.broken.is_none(), kept = self.admitted.len()],
        ensures: |ret| ret.as_ref().map_or(!whole, |export| whole && export.0.len() == kept),
    )]
    pub fn finish(self) -> Result<Export, Unexported>
    {
        match self.broken {
            Some(unexported) => Err(unexported),
            None => Ok(Export(self.admitted)),
        }
    }
}

/// Why a package has no export.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Unexported
{
    /// A source of the package did not settle.
    Unsettled
    {
        /// The source, from the package's root.
        source: PathBuf,
    },
    /// The walk could not carry a source of the package through.
    Faulted
    {
        /// The source, from the package's root.
        source: PathBuf,
    },
    /// A source's path does not spell as UTF-8, so no export can file it.
    Unspelled
    {
        /// The source, from the package's root.
        source: PathBuf,
    },
    /// The artifact a source was admitted with does not cut into declaration
    /// records.
    Uncut
    {
        /// The source, from the package's root.
        source: PathBuf,
        /// Why.
        fault: ArtifactError,
    },
}

impl core::fmt::Display for Unexported
{
    /// The source, then why the package has no export.
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
            Self::Unsettled { ref source } => {
                write!(
                    f,
                    "{}: no export: the source does not settle",
                    source.display()
                )
            },
            Self::Faulted { ref source } => {
                write!(
                    f,
                    "{}: no export: the source was not checked",
                    source.display()
                )
            },
            Self::Unspelled { ref source } => write!(
                f,
                "{}: no export: the path does not spell as UTF-8",
                source.display()
            ),
            Self::Uncut {
                ref source,
                ref fault,
            } => write!(
                f,
                "{}: no export: its artifact does not cut: {fault}",
                source.display()
            ),
        }
    }
}

/// Why a stored export does not re-admit: the first artifact refused, by the
/// first source it was admitted for.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Unreadmitted
{
    /// The kernel's decoder refused the artifact's bytes.
    Undecoded
    {
        /// The source, from the package's root.
        source: String,
        /// Why.
        refusal: DecodeError,
    },
    /// The kernel's replay rejected a declaration of the artifact.
    Refused
    {
        /// The source, from the package's root.
        source: String,
        /// The declaration rejected, and why.
        refusal: ArtifactRefusal,
    },
}

impl core::fmt::Display for Unreadmitted
{
    /// The source, then why its artifact does not re-admit.
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
            Self::Undecoded {
                ref source,
                ref refusal,
            } => write!(f, "{source}: the artifact does not decode: {refusal}"),
            Self::Refused {
                ref source,
                ref refusal,
            } => write!(
                f,
                "{source}: the kernel refuses declaration {}: {}",
                usize::from(refusal.position()),
                refusal.error()
            ),
        }
    }
}
