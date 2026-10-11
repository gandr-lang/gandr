//! Every refusal the artifact layer raises, and the manifest field one names.

use core::error::Error;
use core::fmt;

use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DecodeError;
use gandr_kernel_term::FormatVersion;
use gandr_storage_records::RecordIndex;
use gandr_storage_records::RecordTreeError;

/// The field of a manifest image a refusal names, in image order.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ManifestField
{
    /// The domain the image opens with.
    Domain,
    /// The manifest layout version.
    ManifestVersion,
    /// The kernel format version the records carry.
    KernelFormat,
    /// The length prefix of the boundary commitment.
    CommitmentLength,
    /// The boundary commitment the length prefix counts.
    Commitment,
    /// The record count.
    RecordCount,
    /// The root node's identity.
    RootNode,
}

impl fmt::Display for ManifestField
{
    /// Writes the refused field.
    ///
    /// # Specification
    /// - requires: nothing; every variant renders.
    /// - ensures: writes one fixed phrase per variant, no two alike.
    /// - provides: the field a manifest refusal names.
    /// - fails: propagates the formatter's own write failure unchanged.
    /// - panics: none.
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Errors
    /// Propagates the formatter's write failure.
    ///
    /// # Adequacy
    /// - hypothesis: L3 on all seven fields observes pairwise distinct names
    ///   and exact first-write refusal. It distinguishes collapsed fields and
    ///   swallowed errors without pinning diagnostic wording or exercising
    ///   alternate formatter modes.
    /// - witness: `error::tests::every_manifest_field_renders_apart`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match *self {
            | Self::Domain => "the domain",
            | Self::ManifestVersion => "the manifest version",
            | Self::KernelFormat => "the kernel format version",
            | Self::CommitmentLength => "the boundary commitment's length",
            | Self::Commitment => "the boundary commitment",
            | Self::RecordCount => "the record count",
            | Self::RootNode => "the root node identity",
        })
    }
}

/// Every way the artifact layer refuses an input.
///
/// Refusal is the crate's only failure mode: no operation panics, and no
/// operation repairs a record set, a manifest or a stored tree it was handed.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ArtifactError
{
    /// The kernel's decoder refused the artifact bytes.
    Kernel
    {
        /// The decoder's refusal.
        refusal: DecodeError,
    },

    /// The record plane refused: a tree it would not build, parameters it
    /// does not implement, or a node a store could not authenticate.
    Records
    {
        /// The record plane's refusal.
        refusal: RecordTreeError,
    },

    /// Two records of one set carry one admission key.
    DuplicateAdmissionKey
    {
        /// The repeated admission index.
        key: ConstantIndex,
        /// The input position of the first record carrying it.
        first: RecordIndex,
        /// The input position of the second.
        second: RecordIndex,
    },

    /// A manifest image's field holds a value this build does not read: a
    /// foreign domain or an unknown manifest version.
    MalformedManifest
    {
        /// The field refused.
        field: ManifestField,
    },

    /// A manifest image ended inside a field.
    TruncatedManifest
    {
        /// The field the image ended inside.
        field: ManifestField,
    },

    /// A manifest image continued past its last field.
    TrailingManifestBytes,

    /// A manifest names a kernel format version this build's decoder does not
    /// read.
    UnsupportedKernelFormat
    {
        /// The version the manifest names.
        found: FormatVersion,
    },

    /// A manifest's boundary commitment differs from the one its reader's
    /// tree parameters commit to.
    IncompatibleProfile,

    /// The records a stored root reaches do not rebuild the tree the manifest
    /// names.
    TreeMismatch,

    /// A stored record sits under a key other than the one its position
    /// requires: the header first, under the empty key, then the declarations
    /// at their admission indices, contiguous from zero.
    MisplacedRecord
    {
        /// The record's position in key order.
        position: RecordIndex,
    },

    /// A stored record ends where the decoded artifact has no segment
    /// boundary.
    SegmentBoundary
    {
        /// The record's position in key order.
        position: RecordIndex,
    },
}

impl From<DecodeError> for ArtifactError
{
    /// Carries the kernel decoder's refusal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(refusal: DecodeError) -> Self
    {
        Self::Kernel { refusal }
    }
}

impl From<RecordTreeError> for ArtifactError
{
    /// Carries the record plane's refusal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(refusal: RecordTreeError) -> Self
    {
        Self::Records { refusal }
    }
}

impl fmt::Display for ArtifactError
{
    /// Writes the refusal and the values it names.
    ///
    /// # Specification
    /// - requires: nothing; every variant renders.
    /// - ensures: writes one message per variant, each naming the refusal, key,
    ///   positions, field or version its payload carries, so no two variants
    ///   render alike.
    /// - provides: the operator-facing sentence a caller prints, and the
    ///   [`Error`] rendering the implementation below inherits.
    /// - fails: propagates the formatter's own write failure unchanged.
    /// - panics: none.
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Errors
    /// Propagates the formatter's write failure.
    ///
    /// # Adequacy
    /// - hypothesis: L3 on one representative of all eleven variants observes
    ///   complete payload renderings, distinct messages and first-write sink
    ///   refusal. Indices reach the usize ceiling; the matrix distinguishes
    ///   lost or narrowed payloads, collapsed variants and swallowed errors. It
    ///   does not pin prose, exhaust payloads or sample later-write failure.
    /// - witness: `error::tests::every_refusal_renders_apart`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            | Self::Kernel { refusal } => write!(f, "the kernel refuses the artifact: {refusal}"),
            | Self::Records { ref refusal } => write!(f, "the record plane refuses: {refusal}"),
            | Self::DuplicateAdmissionKey { key, first, second } => {
                write!(
                    f,
                    "records {first} and {second} both carry admission index {}",
                    usize::from(key)
                )
            },
            | Self::MalformedManifest { field } => {
                write!(f, "a manifest image holds {field} this build does not read")
            },
            | Self::TruncatedManifest { field } => {
                write!(f, "a manifest image ends inside {field}")
            },
            | Self::TrailingManifestBytes => {
                f.write_str("a manifest image continues past its root node identity")
            },
            | Self::UnsupportedKernelFormat { found } => {
                write!(
                    f,
                    "the manifest names kernel format {found}, which this build does not decode"
                )
            },
            | Self::IncompatibleProfile => {
                f.write_str("the manifest's boundary commitment differs from the reader's")
            },
            | Self::TreeMismatch => {
                f.write_str("the stored records do not rebuild the tree the manifest names")
            },
            | Self::MisplacedRecord { position } => {
                write!(
                    f,
                    "stored record {position} is not under the key its position requires"
                )
            },
            | Self::SegmentBoundary { position } => {
                write!(
                    f,
                    "stored record {position} ends where the artifact has no segment boundary"
                )
            },
        }
    }
}

impl Error for ArtifactError
{
}

#[cfg(test)]
mod tests
{
    use alloc::string::ToString as _;

    use anodized::spec;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::DecodeError;
    use gandr_kernel_term::FormatVersion;
    use gandr_storage_records::NodeHash;
    use gandr_storage_records::RecordIndex;
    use gandr_storage_records::RecordTreeError;

    use super::ArtifactError;
    use super::ManifestField;

    /// A sink that refuses the first formatted write.
    #[derive(Debug)]
    struct RefusingSink;

    impl core::fmt::Write for RefusingSink
    {
        /// Refuses any offered text.
        ///
        /// # Specification
        /// - requires: nothing.
        /// - ensures: returns the formatting error.
        /// - provides: the refusal observer for every display branch.
        /// - fails: always returns the formatting error.
        /// - panics: none.
        ///
        /// # Errors
        /// Always returns the formatting error.
        ///
        /// # Adequacy
        /// - hypothesis: L3 on every artifact-error variant and manifest field
        ///   observes exact first-write refusal, distinguishing a sink that
        ///   accepts text. Later writes are not sampled by this observer.
        /// - witness: `error::tests::every_refusal_renders_apart`
        /// - witness: `error::tests::every_manifest_field_renders_apart`
        #[spec(ensures: |ret| ret == Err(core::fmt::Error))]
        fn write_str(
            &mut self,
            _s: &str,
        ) -> core::fmt::Result
        {
            Err(core::fmt::Error)
        }
    }

    /// Every refusal retains its diagnostic payload and remains
    /// distinguishable.
    #[test]
    fn every_refusal_renders_apart()
    {
        let kernel = DecodeError::Truncated;
        let records = RecordTreeError::UnknownNode {
            hash: NodeHash::from([0xa7; 32]),
        };
        let key = ConstantIndex::from(usize::MAX);
        let first = RecordIndex::from(usize::MAX - 1);
        let second = RecordIndex::from(usize::MAX - 2);
        let found = FormatVersion(0x1234);
        let kernel_text = kernel.to_string();
        let records_text = records.to_string();
        let key_text = usize::from(key).to_string();
        let first_text = first.to_string();
        let second_text = second.to_string();
        let format_text = found.to_string();
        let malformed_field = ManifestField::Commitment.to_string();
        let truncated_field = ManifestField::RootNode.to_string();
        let cases: [(ArtifactError, &[&str]); 11] = [
            (ArtifactError::Kernel { refusal: kernel }, &[&kernel_text]),
            (ArtifactError::Records { refusal: records }, &[
                &records_text,
            ]),
            (
                ArtifactError::DuplicateAdmissionKey { key, first, second },
                &[&key_text, &first_text, &second_text],
            ),
            (
                ArtifactError::MalformedManifest {
                    field: ManifestField::Commitment,
                },
                &[&malformed_field],
            ),
            (
                ArtifactError::TruncatedManifest {
                    field: ManifestField::RootNode,
                },
                &[&truncated_field],
            ),
            (ArtifactError::TrailingManifestBytes, &[]),
            (ArtifactError::UnsupportedKernelFormat { found }, &[
                &format_text,
            ]),
            (ArtifactError::IncompatibleProfile, &[]),
            (ArtifactError::TreeMismatch, &[]),
            (ArtifactError::MisplacedRecord { position: first }, &[
                &first_text,
            ]),
            (ArtifactError::SegmentBoundary { position: second }, &[
                &second_text,
            ]),
        ];
        let rendered = cases.each_ref().map(|case| case.0.to_string());
        for (index, (error, payloads)) in cases.into_iter().enumerate() {
            for payload in payloads {
                assert!(
                    rendered[index].contains(payload),
                    "{error:?} omitted {payload}"
                );
            }
            assert!(!rendered[.. index].contains(&rendered[index]));
            assert_eq!(
                core::fmt::write(&mut RefusingSink, format_args!("{error}")),
                Err(core::fmt::Error)
            );
        }
    }

    /// Every manifest field retains its identity without fixing its prose.
    #[test]
    fn every_manifest_field_renders_apart()
    {
        let fields = [
            ManifestField::Domain,
            ManifestField::ManifestVersion,
            ManifestField::KernelFormat,
            ManifestField::CommitmentLength,
            ManifestField::Commitment,
            ManifestField::RecordCount,
            ManifestField::RootNode,
        ];
        let rendered = fields.map(|field| field.to_string());
        for (index, field) in fields.into_iter().enumerate() {
            assert!(!rendered[.. index].contains(&rendered[index]));
            assert_eq!(
                core::fmt::write(&mut RefusingSink, format_args!("{field}")),
                Err(core::fmt::Error)
            );
        }
    }
}
