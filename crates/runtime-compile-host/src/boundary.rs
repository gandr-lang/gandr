//! Versioned C layout and status vocabulary, independent of any linked host.

use anodized::spec;

use crate::render::RenderedValue;

/// A C boundary version.
#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct AbiVersion(u32);
impl From<u32> for AbiVersion
{
    /// Wrap the boundary field.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: u32) -> Self
    {
        Self(value)
    }
}
impl From<AbiVersion> for u32
{
    /// Expose the C field's representation.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: AbiVersion) -> Self
    {
        value.0
    }
}

/// A C boundary result code.
#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct BoundaryStatus(i32);
impl From<i32> for BoundaryStatus
{
    /// Wrap the boundary field.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: i32) -> Self
    {
        Self(value)
    }
}
impl From<BoundaryStatus> for i32
{
    /// Expose the C field's representation.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: BoundaryStatus) -> Self
    {
        value.0
    }
}

/// An executed operation count.
#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct LedgerCount(i64);
impl From<i64> for LedgerCount
{
    /// Wrap the boundary field.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: i64) -> Self
    {
        Self(value)
    }
}
impl From<LedgerCount> for i64
{
    /// Expose the C field's representation.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: LedgerCount) -> Self
    {
        value.0
    }
}

/// Consumed arena words.
#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct ArenaWords(u64);
impl From<u64> for ArenaWords
{
    /// Wrap the boundary field.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: u64) -> Self
    {
        Self(value)
    }
}
impl From<ArenaWords> for u64
{
    /// Expose the C field's representation.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: ArenaWords) -> Self
    {
        value.0
    }
}

/// Offered heap words.
#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct HeapWords(u64);
impl From<u64> for HeapWords
{
    /// Wrap the boundary field.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: u64) -> Self
    {
        Self(value)
    }
}
impl From<HeapWords> for u64
{
    /// Expose the C field's representation.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: HeapWords) -> Self
    {
        value.0
    }
}

/// The supported boundary version.
pub const ABI_VERSION: AbiVersion = AbiVersion(1);
/// The successful status code.
pub const STATUS_OK: BoundaryStatus = BoundaryStatus(0);
/// The C outcome record. The host owns text until its release entry is called.
///
/// # Specification
/// - provides: C field order status, duplications, discards, `allocated_words`,
///   text, with i32, i64, i64, u64 and pointer representations respectively.
///   Constructing or copying the record neither dereferences nor frees text.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 offset and width goldens distinguish ABI field drift.
/// - witness: `tests::contract::the_boundary_struct_layout_is_unchanged`
#[derive(Clone, Copy, Debug)]
#[repr(C)]
pub struct RawOutcome
{
    /// Zero on success, otherwise the refusing stage's code.
    pub status: i32,
    /// Executed duplications.
    pub duplications: i64,
    /// Executed discards.
    pub discards: i64,
    /// Consumed arena words.
    pub allocated_words: u64,
    /// Host-owned NUL-terminated message, or null before a call fills it.
    pub text: *const core::ffi::c_char,
}
impl Default for RawOutcome
{
    /// A zeroed record with no message allocation.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn default() -> Self
    {
        Self {
            status: 0,
            duplications: 0,
            discards: 0,
            allocated_words: 0,
            text: core::ptr::null(),
        }
    }
}
/// A host answer after its message has been copied into Rust ownership.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct HostAnswer
{
    /// Canonical result text.
    pub value: RenderedValue,
    /// Executed duplication count.
    pub duplications: LedgerCount,
    /// Executed discard count.
    pub discards: LedgerCount,
    /// Consumed arena words.
    pub allocated: ArenaWords,
}
/// A failed host stage.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RefusalStage
{
    /// Byte image did not decode.
    MalformedImage,
    /// Module failed verification.
    VerifierRejected,
    /// An operation could not be lowered.
    LoweringFailed,
    /// Conversion to LLVM failed.
    ConversionFailed,
    /// Execution engine failed.
    ExecutionFailed,
    /// Result heap was unreadable.
    ResultUnreadable,
    /// Resource bound was reached.
    LimitExceeded,
    /// Input fixture was unreadable.
    FixtureUnreadable,
    /// The call violated the C entry's requirements.
    BadCall,
    /// An unrecognized status, preserved exactly.
    Unknown(BoundaryStatus),
}
impl core::fmt::Display for RefusalStage
{
    /// Render the refusing stage, retaining unknown status numbers.
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
            | Self::Unknown(status) => write!(f, "unknown host status {}", status.0),
            | Self::MalformedImage => f.write_str("image decoder"),
            | Self::VerifierRejected => f.write_str("module verifier"),
            | Self::LoweringFailed => f.write_str("operation lowering"),
            | Self::ConversionFailed => f.write_str("LLVM conversion"),
            | Self::ExecutionFailed => f.write_str("execution engine"),
            | Self::ResultUnreadable => f.write_str("value renderer"),
            | Self::LimitExceeded => f.write_str("resource limit"),
            | Self::FixtureUnreadable => f.write_str("fixture reader"),
            | Self::BadCall => f.write_str("C boundary"),
        }
    }
}
/// Decoded status, separating success from every refusal.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum BoundaryResult
{
    /// A successful run.
    Success,
    /// The named stage refused.
    Refused(RefusalStage),
}
impl From<BoundaryStatus> for BoundaryResult
{
    /// Decode the version-one status vocabulary, retaining unknown codes.
    ///
    /// # Specification
    /// - ensures: zero succeeds; codes 1 through 8 and 100 name their stage;
    ///   every other code survives in Unknown unchanged.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 all named codes and nearby unknowns distinguish
    ///   remapping and accidental success.
    /// - witness: `tests::boundary::every_boundary_status_names_its_own_stage`
    #[spec(ensures: |ret| (ret == Self::Success) == (status == STATUS_OK))]
    #[inline]
    fn from(status: BoundaryStatus) -> Self
    {
        let stage = match status.0 {
            | 0_i32 => return Self::Success,
            | 1_i32 => RefusalStage::MalformedImage,
            | 2_i32 => RefusalStage::VerifierRejected,
            | 3_i32 => RefusalStage::LoweringFailed,
            | 4_i32 => RefusalStage::ConversionFailed,
            | 5_i32 => RefusalStage::ExecutionFailed,
            | 6_i32 => RefusalStage::ResultUnreadable,
            | 7_i32 => RefusalStage::LimitExceeded,
            | 8_i32 => RefusalStage::FixtureUnreadable,
            | 100_i32 => RefusalStage::BadCall,
            | _ => RefusalStage::Unknown(status),
        };
        Self::Refused(stage)
    }
}
/// An owned host failure message.
#[derive(Clone, Debug, Eq, PartialEq)]
#[repr(transparent)]
pub struct RefusalDetail(pub String);
/// A boundary version or execution refusal.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum HostError
{
    /// The host speaks another boundary version.
    VersionMismatch
    {
        /// Version advertised by the host.
        found: AbiVersion,
        /// Version required by this Rust boundary.
        expected: AbiVersion,
    },
    /// A host stage refused a program.
    Refused
    {
        /// Refusing stage.
        stage: RefusalStage,
        /// Owned detail supplied by the host.
        detail: RefusalDetail,
    },
}
impl core::fmt::Display for HostError
{
    /// Name the version mismatch or original host refusal.
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
            | Self::VersionMismatch { found, expected } => {
                write!(f, "host ABI version {}, expected {}", found.0, expected.0)
            },
            | Self::Refused { stage, ref detail } => write!(f, "{stage}: {}", detail.0),
        }
    }
}
impl core::error::Error for HostError
{
}
/// Require the supported C boundary version before entering a host.
///
/// # Specification
/// - ensures: succeeds exactly at `ABI_VERSION`.
/// - fails: `VersionMismatch` retains both versions.
/// - panics: none.
///
/// # Errors
/// Returns `VersionMismatch` for every other version.
///
/// # Adequacy
/// - hypothesis: L3 current, older and newer versions separate equality from
///   permissive version comparisons.
/// - witness: `tests::contract::the_boundary_version_and_statuses_are_unchanged`
#[spec(ensures: |ret| ret.is_ok() == (found == ABI_VERSION))]
#[inline]
pub fn require_version(found: AbiVersion) -> Result<(), HostError>
{
    if found == ABI_VERSION {
        Ok(())
    }
    else {
        Err(HostError::VersionMismatch {
            found,
            expected: ABI_VERSION,
        })
    }
}
