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
    use alloc::collections::BTreeSet;
    use alloc::string::String;
    use alloc::string::ToString;

    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::DecodeError;
    use gandr_kernel_term::FormatVersion;
    use gandr_storage_records::NodeHash;
    use gandr_storage_records::RecordIndex;
    use gandr_storage_records::RecordTreeError;

    use super::ArtifactError;
    use super::ManifestField;

    /// Every refusal renders its own sentence, so an operator can tell any two
    /// apart from the text alone.
    #[test]
    fn every_refusal_renders_apart()
    {
        let refusals = [
            ArtifactError::Kernel {
                refusal: DecodeError::Truncated,
            },
            ArtifactError::Records {
                refusal: RecordTreeError::UnknownNode {
                    hash: NodeHash::from([0_u8; 32]),
                },
            },
            ArtifactError::DuplicateAdmissionKey {
                key: ConstantIndex::from(3_usize),
                first: RecordIndex::from(0_usize),
                second: RecordIndex::from(1_usize),
            },
            ArtifactError::MalformedManifest {
                field: ManifestField::Domain,
            },
            ArtifactError::TruncatedManifest {
                field: ManifestField::Domain,
            },
            ArtifactError::TrailingManifestBytes,
            ArtifactError::UnsupportedKernelFormat {
                found: FormatVersion(1),
            },
            ArtifactError::IncompatibleProfile,
            ArtifactError::TreeMismatch,
            ArtifactError::MisplacedRecord {
                position: RecordIndex::from(1_usize),
            },
            ArtifactError::SegmentBoundary {
                position: RecordIndex::from(1_usize),
            },
        ];
        let rendered: BTreeSet<String> = refusals.iter().map(ToString::to_string).collect();
        assert_eq!(
            refusals.len(),
            rendered.len(),
            "each refusal renders a sentence no other one does"
        );
    }

    /// Every manifest field renders its own phrase.
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
        let rendered: BTreeSet<String> = fields.iter().map(ToString::to_string).collect();
        assert_eq!(
            fields.len(),
            rendered.len(),
            "each field renders a phrase no other one does"
        );
    }
}
