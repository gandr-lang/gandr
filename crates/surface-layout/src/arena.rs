//! The sealed document arena and the node algebra it stores.
//!
//! A document is a directed acyclic graph of nodes held in flat, grow-only
//! stores. Every stored edge points at an earlier node in the same builder, so
//! the graph is acyclic by construction rather than by a check. Identities are
//! dense insertion ordinals: they never move, never recycle, and are not
//! content identities.
//!
//! Sharing is the point of the arena. A subdocument referenced twice is stored
//! once and resolved once per distinct layout context, which is what keeps a
//! large printed term from re-walking its own shape.
//!
//! # The node semantics
//!
//! | node       | semantics                                                                                                          |
//! | ---------- | ------------------------------------------------------------------------------------------------------------------ |
//! | `Empty`    | Emits nothing and changes neither column nor indentation.                                                           |
//! | `Text`     | Emits its newline-free string at the current column.                                                                |
//! | `Verbatim` | Emits its exact stored bytes; later physical lines begin at column zero with whatever indentation the bytes carry.  |
//! | `Line`     | Emits the configured physical ending and the current indentation; under flattening it emits one space.              |
//! | `HardLine` | Emits the ending and the indentation even under flattening, which is what protects a line comment.                  |
//! | `Concat`   | Unaligned concatenation: resolve the left, then the right at the left's ending column, keeping the indentation.     |
//! | `Nest`     | Resolves its child with the indentation raised by a checked amount.                                                 |
//! | `Align`    | Resolves its child with the indentation set to the current column.                                                  |
//! | `Choice`   | Admits every layout of either child and merges their measure sets.                                                  |
//! | `Flatten`  | Uses the memoized flattened image of its child, turning `Line` into one space and leaving `HardLine` and verbatim.  |
//!
//! Unaligned concatenation is the feature that makes the resolver's second cost
//! dimension necessary: a locally more expensive left layout can leave a column
//! that makes everything after it cheaper.
//!
//! # Physical text
//!
//! Text is newline-free and rejects a carriage return, a line feed, and a tab;
//! a client expands its own tabs before construction. Verbatim text is the
//! separate opaque carrier for content that must survive byte-identical. Its
//! scan produces one record per physical fragment — including the empty final
//! fragment after a trailing ending — and each record stores that fragment's
//! checked scalar width and the exact ending that follows it, so the stored
//! bytes and the stored metrics cannot disagree. Verbatim text is inert to
//! flattening: neither a `Flatten` node nor a surrounding group may rewrite its
//! newlines or its internal indentation.
//!
//! The first fragment extends the incoming column. After a stored ending, every
//! later fragment starts at absolute column zero, so middle widths are absolute
//! line widths and the ending column is the final fragment's width.
//!
//! # Handles
//!
//! A client names a node only through a [`DocId`], which carries the key of
//! the arena that minted it; [`DocArena::contains`] answers with the two-valued
//! [`DocHandleStatus`] rather than a `bool`. Identity minting, verbatim
//! scanning, and the flatten interner are private to [`crate::build`]; nothing
//! here hands out a raw ordinal.

use alloc::string::String;
use alloc::vec::Vec;
use core::num::NonZeroU32;

use quenchant_shape::shape::Maybe;

use crate::error::BuildAllocationSite;
use crate::error::BuildArithmetic;
use crate::error::BuildError;
use crate::units::DocNodesUsed;
use crate::units::ScalarWidth;
use crate::units::TextBytesUsed;
use crate::units::VerbatimLinesUsed;

quenchant_shape::reason_enum! {
    /// Why a verbatim fragment carries no ending.
    pub mod ending {
        /// The reason none follows.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The fragment is the text's last, which no ending follows.
            Final,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a store identity names no entry.
    pub(crate) mod stored {
        /// The reason none is named.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub(crate) enum Absent {
            /// The identity lies past the end of its store.
            OutOfRange,
        }
    }
}

/// A stable dense document-arena identity.
///
/// # Specification
/// - requires: the value was minted by the builder that owns the node.
/// - ensures: the identity never moves and is never recycled.
/// - provides: the identity stored in every document edge.
/// - panics: none.
/// - executable: none — this data declaration has no executable invocation;
///   ingestion, construction and checked projections carry the relevant
///   predicates.
///
/// # Adequacy
/// - hypothesis: L3 — first and last identities, the next ordinal, maximal
///   ordinals, foreign arenas and wrong node kinds are observed through exact
///   payloads or typed absence. Dropping the arena check, shifting a bound,
///   reading a different store and returning a different payload change these
///   observations; borrowed private projections also expose storage identity.
/// - witness: `arena::tests::arena_projections_separate_namespaces_kinds_and_store_bounds`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub(crate) struct NodeId
{
    /// The dense insertion ordinal.
    index: u32,
}

/// A stable dense text-arena identity.
///
/// # Specification
/// - requires: the value was minted by the builder that owns the text.
/// - ensures: the identity never moves and is never recycled.
/// - provides: the payload of a text node.
/// - panics: none.
/// - executable: none — this data declaration has no executable invocation;
///   ingestion, construction and checked projections carry the relevant
///   predicates.
///
/// # Adequacy
/// - hypothesis: L3 — first and last identities, the next ordinal, maximal
///   ordinals, foreign arenas and wrong node kinds are observed through exact
///   payloads or typed absence. Dropping the arena check, shifting a bound,
///   reading a different store and returning a different payload change these
///   observations; borrowed private projections also expose storage identity.
/// - witness: `arena::tests::arena_projections_separate_namespaces_kinds_and_store_bounds`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub(crate) struct TextId
{
    /// The dense insertion ordinal.
    index: u32,
}

/// A stable dense verbatim-arena identity.
///
/// # Specification
/// - requires: the value was minted by the builder that owns the text.
/// - ensures: the identity never moves and is never recycled.
/// - provides: the payload of a verbatim node.
/// - panics: none.
/// - executable: none — this data declaration has no executable invocation;
///   ingestion, construction and checked projections carry the relevant
///   predicates.
///
/// # Adequacy
/// - hypothesis: L3 — first and last identities, the next ordinal, maximal
///   ordinals, foreign arenas and wrong node kinds are observed through exact
///   payloads or typed absence. Dropping the arena check, shifting a bound,
///   reading a different store and returning a different payload change these
///   observations; borrowed private projections also expose storage identity.
/// - witness: `arena::tests::arena_projections_separate_namespaces_kinds_and_store_bounds`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub(crate) struct VerbatimId
{
    /// The dense insertion ordinal.
    index: u32,
}

/// A process-local token distinguishing one arena from every other.
///
/// The key is what makes a handle checkable. Without it a dense ordinal from
/// one document would silently name a different node in another, and the
/// mistake would surface as wrong output rather than as an error.
///
/// # Specification
/// - requires: the value was minted by the crate's checked monotonic counter.
/// - ensures: two live arenas never share a key.
/// - provides: the arena half of a client-facing document handle.
/// - fails: minting reports `BuildError::ArenaKeyExhausted` when the counter
///   has no value left.
/// - panics: none.
/// - executable: none — this data declaration has no executable invocation;
///   ingestion, construction and checked projections carry the relevant
///   predicates.
///
/// # Adequacy
/// - hypothesis: L3 — distinct builder arenas reject each other's handles,
///   while the final nonzero counter value is minted once and exhaustion never
///   reuses it. Key omission, reuse and wraparound change handle validation or
///   the typed exhaustion result.
/// - witness: `algebra::tests::a_handle_from_another_arena_is_refused_before_lookup`
/// - witness: `build::tests::an_exhausted_arena_key_counter_is_reported_rather_than_reused`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub(crate) struct ArenaKey
{
    /// The non-zero process-local token.
    token: NonZeroU32,
}

/// A checked client handle to a document node.
///
/// The fields are private on purpose: a handle is presented to the arena that
/// minted it and validated there, and a client never constructs one from parts.
///
/// # Specification
/// - requires: the handle is presented to the arena whose key it carries.
/// - ensures: a foreign or out-of-range handle is rejected before any lookup.
/// - provides: the only way a client names a node.
/// - fails: a mismatch surfaces as `BuildError::UnknownDoc` during
///   construction, and as the render-phase unknown-handle error afterwards.
/// - panics: none.
/// - executable: none — this data declaration has no executable invocation;
///   ingestion, construction and checked projections carry the relevant
///   predicates.
///
/// # Adequacy
/// - hypothesis: L3 — first and last identities, the next ordinal, maximal
///   ordinals, foreign arenas and wrong node kinds are observed through exact
///   payloads or typed absence. Dropping the arena check, shifting a bound,
///   reading a different store and returning a different payload change these
///   observations; borrowed private projections also expose storage identity.
/// - witness: `arena::tests::arena_projections_separate_namespaces_kinds_and_store_bounds`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct DocId
{
    /// The arena this identity belongs to.
    arena: ArenaKey,
    /// The node named within that arena.
    node: NodeId,
}

/// The result of checking a client document handle against an arena.
///
/// # Specification
/// - requires: the status came from [`DocArena::contains`].
/// - ensures: `Present` means the arena key and dense node ordinal are valid;
///   `Absent` means at least one check failed.
/// - provides: a nominal two-valued handle status without exposing `bool`.
/// - panics: none.
/// - executable: none — this data declaration has no executable invocation;
///   ingestion, construction and checked projections carry the relevant
///   predicates.
///
/// # Adequacy
/// - hypothesis: L3 — first and last identities, the next ordinal, maximal
///   ordinals, foreign arenas and wrong node kinds are observed through exact
///   payloads or typed absence. Dropping the arena check, shifting a bound,
///   reading a different store and returning a different payload change these
///   observations; borrowed private projections also expose storage identity.
/// - witness: `arena::tests::arena_projections_separate_namespaces_kinds_and_store_bounds`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum DocHandleStatus
{
    /// The handle belongs to this arena and names a stored node.
    Present,
    /// The handle is foreign or outside this arena's node store.
    Absent,
}

/// Borrowed newline-free text destined for a `Text` node.
///
/// The wrapper is owned by this module because this module validates and stores
/// its bytes; the raw borrow never crosses the arena boundary.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct TextSource<'source>
{
    /// The borrowed text.
    text: &'source str,
}

/// Owned newline-free text destined for a `Text` node.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct TextOwned
{
    /// The owned text.
    text: String,
}

/// Borrowed opaque multiline text destined for a `Verbatim` node.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct VerbatimSource<'source>
{
    /// The borrowed opaque bytes.
    text: &'source str,
}

/// Owned opaque multiline text destined for a `Verbatim` node.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct VerbatimOwned
{
    /// The owned opaque bytes.
    text: String,
}

/// A validated, owned newline-free text identity.
///
/// # Specification
/// - requires: construction validates the complete UTF-8 input.
/// - ensures: the bytes contain no CR, LF or tab and the width counts scalars.
/// - provides: one owned text payload with coherent storage metrics.
/// - panics: none.
/// - executable: none — this stored record has no invocation boundary; both
///   ingestion paths validate its bytes and width.
///
/// # Adequacy
/// - hypothesis: L3 — empty text, multibyte scalars, NUL and each forbidden
///   scalar at distinct positions expose exact bytes, scalar width, byte charge
///   and typed rejection. Owned inputs also expose allocation identity.
///   Byte-counted widths, normalization, skipped forbidden scalars and cloning
///   the adopted buffer change these observations; allocation failure is not
///   deterministically injected.
/// - witness: `arena::tests::text_ingestion_preserves_unicode_counts_and_owned_allocations`
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(crate) struct CheckedText
{
    /// The owned newline-free bytes.
    text: String,
    /// The checked scalar width.
    width: ScalarWidth,
}

impl CheckedText
{
    /// Returns the nominal byte charge for this text identity.
    ///
    /// # Specification
    /// - requires: the text was accepted as newline-free checked input.
    /// - ensures: the byte count is converted without changing the stored text.
    /// - provides: the text-byte usage consumed by build accounting.
    /// - fails: returns `ArithmeticOverflow` when the byte length is not
    ///   representable by the nominal usage type.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `ArithmeticOverflow` when the byte length cannot be represented.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty text, multibyte scalars, NUL and each forbidden
    ///   scalar at distinct positions expose exact bytes, scalar width, byte
    ///   charge and typed rejection. Owned inputs also expose allocation
    ///   identity. Byte-counted widths, normalization, skipped forbidden
    ///   scalars and cloning the adopted buffer change these observations;
    ///   allocation failure is not deterministically injected.
    /// - witness: `arena::tests::text_ingestion_preserves_unicode_counts_and_owned_allocations`
    #[anodized::spec(
        ensures: |ret| ret.as_ref().map_or_else(|error| u64::try_from(self.text.len()).is_err()
                && *error == BuildError::ArithmeticOverflow { operation: BuildArithmetic::TextBytes },
            |used| u64::try_from(self.text.len()) == Ok(u64::from(*used)))
    )]
    #[inline]
    pub(crate) fn bytes_used(&self) -> Result<TextBytesUsed, BuildError>
    {
        TextBytesUsed::try_from(self.text.len())
    }

    /// Returns the checked scalar width carried by this identity.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) const fn width(&self) -> ScalarWidth
    {
        self.width
    }
}

impl AsRef<str> for CheckedText
{
    /// The stored newline-free bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &str
    {
        &self.text
    }
}

/// A physical line ending recorded inside verbatim text.
///
/// # Specification
/// - requires: the value is what the verbatim scan actually found.
/// - ensures: the recorded ending reproduces the original bytes exactly.
/// - provides: the ending half of a verbatim fragment record.
/// - panics: none.
/// - executable: none — this data declaration has no executable invocation;
///   ingestion, construction and checked projections carry the relevant
///   predicates.
///
/// # Adequacy
/// - hypothesis: L3 — all strings of up to four symbols over ASCII, a multibyte
///   scalar, CR, LF and tab are checked against a split-based physical-fragment
///   oracle. Exact bytes, widths, ending variants and final fragments
///   distinguish normalization, byte-counted widths, missing trailing fragments
///   and acceptance of bare CR. Allocation failure and widths beyond u32 are
///   outside this bounded witness domain.
/// - witness: `arena::tests::short_verbatim_inputs_match_an_independent_fragment_oracle`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
#[repr(u8)]
pub enum StoredLineEnding
{
    /// A single line feed.
    Lf,
    /// A carriage return followed by a line feed.
    CrLf,
}

/// One physical fragment of verbatim text, with its width and its ending.
///
/// # Specification
/// - requires: the record comes from the scan of the bytes it describes.
/// - ensures: the width is a checked scalar count and the ending is exactly
///   what follows the fragment, or none at the end of the text.
/// - provides: the metrics the cost and taint rules read without re-scanning
///   the bytes.
/// - panics: none.
/// - executable: none — this data declaration has no executable invocation;
///   ingestion, construction and checked projections carry the relevant
///   predicates.
///
/// # Adequacy
/// - hypothesis: L3 — all strings of up to four symbols over ASCII, a multibyte
///   scalar, CR, LF and tab are checked against a split-based physical-fragment
///   oracle. Exact bytes, widths, ending variants and final fragments
///   distinguish normalization, byte-counted widths, missing trailing fragments
///   and acceptance of bare CR. Allocation failure and widths beyond u32 are
///   outside this bounded witness domain.
/// - witness: `arena::tests::short_verbatim_inputs_match_an_independent_fragment_oracle`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct VerbatimLine
{
    /// The fragment's checked scalar width.
    scalar_width: ScalarWidth,
    /// The ending that follows the fragment, or why none does.
    ending: Maybe<StoredLineEnding, ending::Absent>,
}

/// Verbatim bytes stored once, beside the fragment records describing them.
///
/// # Specification
/// - requires: the records were produced by scanning exactly these bytes.
/// - ensures: bytes and metrics cannot disagree, because neither is derived a
///   second time.
/// - provides: the byte-identical carrier for comments and other protected
///   content.
/// - panics: none.
/// - executable: none — this data declaration has no executable invocation;
///   ingestion, construction and checked projections carry the relevant
///   predicates.
///
/// # Adequacy
/// - hypothesis: L3 — all strings of up to four symbols over ASCII, a multibyte
///   scalar, CR, LF and tab are checked against a split-based physical-fragment
///   oracle. Exact bytes, widths, ending variants and final fragments
///   distinguish normalization, byte-counted widths, missing trailing fragments
///   and acceptance of bare CR. Allocation failure and widths beyond u32 are
///   outside this bounded witness domain.
/// - witness: `arena::tests::short_verbatim_inputs_match_an_independent_fragment_oracle`
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct VerbatimText
{
    /// The original bytes, stored exactly once.
    bytes: String,
    /// One record per physical fragment.
    lines: Vec<VerbatimLine>,
}

impl VerbatimLine
{
    /// Returns this fragment's nominal scalar width.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn scalar_width(&self) -> ScalarWidth
    {
        self.scalar_width
    }

    /// Returns the exact ending following this fragment.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the ending the scan found after the fragment.
    /// - provides: [`ending::Absent::Final`] for the text's last fragment,
    ///   which no ending follows.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — all strings of up to four symbols over ASCII, a
    ///   multibyte scalar, CR, LF and tab are checked against a split-based
    ///   physical-fragment oracle. Exact bytes, widths, ending variants and
    ///   final fragments distinguish normalization, byte-counted widths,
    ///   missing trailing fragments and acceptance of bare CR. Allocation
    ///   failure and widths beyond u32 are outside this bounded witness domain.
    /// - witness: `arena::tests::short_verbatim_inputs_match_an_independent_fragment_oracle`
    #[anodized::spec(
        ensures: |ret| matches!((self.ending, ret), (Maybe::Present(StoredLineEnding::Lf), Maybe::Present(StoredLineEnding::Lf)) | (Maybe::Present(StoredLineEnding::CrLf), Maybe::Present(StoredLineEnding::CrLf)) | (Maybe::Absent(ending::Absent::Final), Maybe::Absent(ending::Absent::Final)))
    )]
    #[inline]
    pub const fn ending(&self) -> Maybe<StoredLineEnding, ending::Absent>
    {
        self.ending
    }
}

impl VerbatimText
{
    /// Returns the nominal byte charge for this identity.
    ///
    /// # Specification
    /// - requires: the bytes were accepted by the verbatim scanner.
    /// - ensures: the byte count reflects the exact stored opaque bytes.
    /// - provides: the text-byte usage consumed by build accounting.
    /// - fails: returns `ArithmeticOverflow` when the byte length is not
    ///   representable by the nominal usage type.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `ArithmeticOverflow` when the byte length cannot be represented.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — all strings of up to four symbols over ASCII, a
    ///   multibyte scalar, CR, LF and tab are checked against a split-based
    ///   physical-fragment oracle. Exact bytes, widths, ending variants and
    ///   final fragments distinguish normalization, byte-counted widths,
    ///   missing trailing fragments and acceptance of bare CR. Allocation
    ///   failure and widths beyond u32 are outside this bounded witness domain.
    /// - witness: `arena::tests::short_verbatim_inputs_match_an_independent_fragment_oracle`
    #[anodized::spec(
        ensures: |ret| ret.as_ref().map_or_else(|error| u64::try_from(self.bytes.len()).is_err()
                && *error == BuildError::ArithmeticOverflow { operation: BuildArithmetic::TextBytes },
            |used| u64::try_from(self.bytes.len()) == Ok(u64::from(*used)))
    )]
    #[inline]
    pub(crate) fn bytes_used(&self) -> Result<TextBytesUsed, BuildError>
    {
        TextBytesUsed::try_from(self.bytes.len())
    }

    /// Returns the nominal physical-fragment charge for this identity.
    ///
    /// # Specification
    /// - requires: the fragment records were produced by the verbatim scanner.
    /// - ensures: the count includes the final fragment, even when it is empty.
    /// - provides: the verbatim-line usage consumed by build accounting.
    /// - fails: returns `ArithmeticOverflow` when the fragment count is not
    ///   representable by the nominal usage type.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `ArithmeticOverflow` when the fragment count cannot be
    /// represented.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — all strings of up to four symbols over ASCII, a
    ///   multibyte scalar, CR, LF and tab are checked against a split-based
    ///   physical-fragment oracle. Exact bytes, widths, ending variants and
    ///   final fragments distinguish normalization, byte-counted widths,
    ///   missing trailing fragments and acceptance of bare CR. Allocation
    ///   failure and widths beyond u32 are outside this bounded witness domain.
    /// - witness: `arena::tests::short_verbatim_inputs_match_an_independent_fragment_oracle`
    #[anodized::spec(
        ensures: |ret| ret.as_ref().map_or_else(|error| u64::try_from(self.lines.len()).is_err()
                && *error == BuildError::ArithmeticOverflow { operation: BuildArithmetic::VerbatimLines },
            |used| u64::try_from(self.lines.len()) == Ok(u64::from(*used)))
    )]
    #[inline]
    pub(crate) fn lines_used(&self) -> Result<VerbatimLinesUsed, BuildError>
    {
        VerbatimLinesUsed::try_from(self.lines.len())
    }

    /// Returns all physical fragment records in source order.
    ///
    /// # Specification
    /// - requires: the records came from the same scan as [`Self::bytes`].
    /// - ensures: the final empty fragment, when present, is retained.
    /// - provides: exact widths and endings for cost computation.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — all strings of up to four symbols over ASCII, a
    ///   multibyte scalar, CR, LF and tab are checked against a split-based
    ///   physical-fragment oracle. Exact bytes, widths, ending variants and
    ///   final fragments distinguish normalization, byte-counted widths,
    ///   missing trailing fragments and acceptance of bare CR. Allocation
    ///   failure and widths beyond u32 are outside this bounded witness domain.
    /// - witness: `arena::tests::short_verbatim_inputs_match_an_independent_fragment_oracle`
    #[anodized::spec(
        ensures: |ret| core::ptr::eq(&raw const *ret, &raw const *self.lines.as_slice())
    )]
    #[inline]
    pub(crate) fn lines(&self) -> &[VerbatimLine]
    {
        &self.lines
    }
}

impl AsRef<str> for VerbatimText
{
    /// The stored bytes, line endings included, exactly as ingested.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &str
    {
        &self.bytes
    }
}

impl<'source> From<&'source str> for TextSource<'source>
{
    /// Wraps borrowed text for validation at ingestion.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(text: &'source str) -> Self
    {
        Self { text }
    }
}

impl From<String> for TextOwned
{
    /// Wraps owned text for validation at ingestion.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(text: String) -> Self
    {
        Self { text }
    }
}

impl<'source> From<&'source str> for VerbatimSource<'source>
{
    /// Wraps borrowed verbatim text for splitting at ingestion.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(text: &'source str) -> Self
    {
        Self { text }
    }
}

impl From<String> for VerbatimOwned
{
    /// Wraps owned verbatim text for splitting at ingestion.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(text: String) -> Self
    {
        Self { text }
    }
}

impl<'source> TryFrom<TextSource<'source>> for CheckedText
{
    type Error = BuildError;

    /// Validates and owns one borrowed newline-free text identity.
    ///
    /// # Specification
    /// - requires: `source` is UTF-8 text supplied by the caller.
    /// - ensures: success stores the exact bytes and checked scalar width.
    /// - provides: the borrowed text ingestion path.
    /// - fails: returns `InvalidText`, `ArithmeticOverflow`, or
    ///   `AllocationFailed` without returning partial text.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `InvalidText` for forbidden scalars, `ArithmeticOverflow` for
    /// unrepresentable widths, or `AllocationFailed` for storage reservation.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty text, multibyte scalars, NUL and each forbidden
    ///   scalar at distinct positions expose exact bytes, scalar width, byte
    ///   charge and typed rejection. Owned inputs also expose allocation
    ///   identity. Byte-counted widths, normalization, skipped forbidden
    ///   scalars and cloning the adopted buffer change these observations;
    ///   allocation failure is not deterministically injected.
    /// - witness: `arena::tests::text_ingestion_preserves_unicode_counts_and_owned_allocations`
    #[anodized::spec(
        ensures: |ret| ret.as_ref().map_or_else(|error| match *error { BuildError::InvalidText => source.text.contains(['\r', '\n', '\t']), BuildError::ArithmeticOverflow { operation: BuildArithmetic::ScalarWidth } => !source.text.contains(['\r', '\n', '\t'])
                && u32::try_from(source.text.chars().count()).is_err(), BuildError::AllocationFailed { site: BuildAllocationSite::TextArena } => !source.text.contains(['\r', '\n', '\t'])
                && u32::try_from(source.text.chars().count()).is_ok(), _ => false },
            |text| text.text == source.text
                && !source.text.contains(['\r', '\n', '\t'])
                && usize::try_from(u32::from(text.width)) == Ok(source.text.chars().count()))
    )]
    #[inline]
    fn try_from(source: TextSource<'source>) -> Result<Self, Self::Error>
    {
        let width = checked_text_width(source)?;
        let mut text = String::new();
        text.try_reserve(source.text.len())
            .map_err(|_error| BuildError::AllocationFailed {
                site: BuildAllocationSite::TextArena,
            })?;
        text.push_str(source.text);
        Ok(Self { text, width })
    }
}

impl TryFrom<TextOwned> for CheckedText
{
    type Error = BuildError;

    /// Validates and adopts one owned newline-free text identity.
    ///
    /// # Specification
    /// - requires: `source` owns UTF-8 text supplied by the caller.
    /// - ensures: success preserves ownership, exact bytes, and scalar width.
    /// - provides: the owned text ingestion path.
    /// - fails: returns `InvalidText` or `ArithmeticOverflow` without returning
    ///   a partial identity.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `InvalidText` for forbidden scalars or `ArithmeticOverflow` for
    /// an unrepresentable width.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty text, multibyte scalars, NUL and each forbidden
    ///   scalar at distinct positions expose exact bytes, scalar width, byte
    ///   charge and typed rejection. Owned inputs also expose allocation
    ///   identity. Byte-counted widths, normalization, skipped forbidden
    ///   scalars and cloning the adopted buffer change these observations;
    ///   allocation failure is not deterministically injected.
    /// - witness: `arena::tests::text_ingestion_preserves_unicode_counts_and_owned_allocations`
    #[anodized::spec(
        captures: before = (source.text.as_ptr(), source.text.len(), source.text.chars().count(), source.text.contains(['\r', '\n', '\t'])),
        ensures: |ret| ret.as_ref().map_or_else(|error| if before.3 { *error == BuildError::InvalidText }
            else { u32::try_from(before.2).is_err()
                && *error == BuildError::ArithmeticOverflow { operation: BuildArithmetic::ScalarWidth } },
            |text| !before.3
                && text.text.as_ptr() == before.0
                && text.text.len() == before.1
                && usize::try_from(u32::from(text.width)) == Ok(before.2))
    )]
    #[inline]
    fn try_from(source: TextOwned) -> Result<Self, Self::Error>
    {
        let TextOwned { text } = source;
        let width = checked_text_width(TextSource::from(text.as_str()))?;
        Ok(Self { text, width })
    }
}

impl<'source> TryFrom<VerbatimSource<'source>> for VerbatimText
{
    type Error = BuildError;

    /// Scans and owns one borrowed opaque multiline text identity.
    ///
    /// # Specification
    /// - requires: `source` is complete UTF-8 text; bare CR remains in the
    ///   domain.
    /// - ensures: success preserves bytes and one record per physical fragment.
    /// - provides: the borrowed verbatim ingestion path.
    /// - fails: returns `InvalidVerbatimLineEnding`, `ArithmeticOverflow`, or
    ///   `AllocationFailed` without returning partial text.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns the typed scan or storage error that prevents ingestion.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — all strings of up to four symbols over ASCII, a
    ///   multibyte scalar, CR, LF and tab are checked against a split-based
    ///   physical-fragment oracle. Exact bytes, widths, ending variants and
    ///   final fragments distinguish normalization, byte-counted widths,
    ///   missing trailing fragments and acceptance of bare CR. Allocation
    ///   failure and widths beyond u32 are outside this bounded witness domain.
    /// - witness: `arena::tests::short_verbatim_inputs_match_an_independent_fragment_oracle`
    #[anodized::spec(
        ensures: |ret| ret.as_ref().map_or_else(|error| match *error { BuildError::InvalidVerbatimLineEnding => source.text.match_indices('\r').any(|(offset, _)| source.text.as_bytes().get(offset.saturating_add(1)) != Some(&b'\n')), BuildError::ArithmeticOverflow { operation: BuildArithmetic::ScalarWidth } => source.text.split('\n').any(|fragment| u32::try_from(fragment.strip_suffix('\r').unwrap_or(fragment).chars().count()).is_err()), BuildError::AllocationFailed { site: BuildAllocationSite::VerbatimArena | BuildAllocationSite::TextArena } => true, _ => false },
            |verbatim| verbatim.bytes == source.text
                && !(source.text.match_indices('\r').any(|(offset, _)| source.text.as_bytes().get(offset.saturating_add(1)) != Some(&b'\n')))
                && verbatim.lines.len() == source.text.bytes().filter(|byte| *byte == b'\n').count().saturating_add(1)
                && verbatim.lines.iter().zip(source.text.split('\n')).enumerate().all(|(index, (line, fragment))| { let last = index.saturating_add(1) == verbatim.lines.len();
            let crlf = !last
                && fragment.ends_with('\r');
            let content = if crlf { fragment.strip_suffix('\r').unwrap_or(fragment) }
            else { fragment };
            u32::try_from(content.chars().count()).is_ok_and(|width| u32::from(line.scalar_width) == width)
                && line.ending == if last { Maybe::Absent(ending::Absent::Final) }
            else if crlf { Maybe::Present(StoredLineEnding::CrLf) }
            else { Maybe::Present(StoredLineEnding::Lf) } }))
    )]
    #[inline]
    fn try_from(source: VerbatimSource<'source>) -> Result<Self, Self::Error>
    {
        let lines = scan_verbatim(source)?;
        let mut bytes = String::new();
        bytes
            .try_reserve(source.text.len())
            .map_err(|_error| BuildError::AllocationFailed {
                site: BuildAllocationSite::TextArena,
            })?;
        bytes.push_str(source.text);
        Ok(Self { bytes, lines })
    }
}

impl TryFrom<VerbatimOwned> for VerbatimText
{
    type Error = BuildError;

    /// Scans and adopts one owned opaque multiline text identity.
    ///
    /// # Specification
    /// - requires: `source` owns complete UTF-8 text; bare CR remains in the
    ///   domain.
    /// - ensures: success preserves ownership, bytes, and physical fragments.
    /// - provides: the owned verbatim ingestion path.
    /// - fails: returns `InvalidVerbatimLineEnding`, `ArithmeticOverflow` or
    ///   `AllocationFailed` without returning a partial identity.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns the typed scan error that prevents ingestion.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — all strings of up to four symbols over ASCII, a
    ///   multibyte scalar, CR, LF and tab are checked against a split-based
    ///   physical-fragment oracle. Exact bytes, widths, ending variants and
    ///   final fragments distinguish normalization, byte-counted widths,
    ///   missing trailing fragments and acceptance of bare CR. Allocation
    ///   failure and widths beyond u32 are outside this bounded witness domain.
    /// - witness: `arena::tests::short_verbatim_inputs_match_an_independent_fragment_oracle`
    #[anodized::spec(
        captures: before = (source.text.as_ptr(), source.text.len(), source.text.match_indices('\r').any(|(offset, _)| source.text.as_bytes().get(offset.saturating_add(1)) != Some(&b'\n')), source.text.split('\n').any(|fragment| u32::try_from(fragment.strip_suffix('\r').unwrap_or(fragment).chars().count()).is_err())),
        ensures: |ret| ret.as_ref().map_or_else(|error| match *error { BuildError::InvalidVerbatimLineEnding => before.2, BuildError::ArithmeticOverflow { operation: BuildArithmetic::ScalarWidth } => before.3, BuildError::AllocationFailed { site: BuildAllocationSite::VerbatimArena } => true, _ => false },
            |verbatim| verbatim.bytes.as_ptr() == before.0
                && verbatim.bytes.len() == before.1
                && !(verbatim.bytes.match_indices('\r').any(|(offset, _)| verbatim.bytes.as_bytes().get(offset.saturating_add(1)) != Some(&b'\n')))
                && verbatim.lines.len() == verbatim.bytes.bytes().filter(|byte| *byte == b'\n').count().saturating_add(1)
                && verbatim.lines.iter().zip(verbatim.bytes.split('\n')).enumerate().all(|(index, (line, fragment))| { let last = index.saturating_add(1) == verbatim.lines.len();
            let crlf = !last
                && fragment.ends_with('\r');
            let content = if crlf { fragment.strip_suffix('\r').unwrap_or(fragment) }
            else { fragment };
            u32::try_from(content.chars().count()).is_ok_and(|width| u32::from(line.scalar_width) == width)
                && line.ending == if last { Maybe::Absent(ending::Absent::Final) }
            else if crlf { Maybe::Present(StoredLineEnding::CrLf) }
            else { Maybe::Present(StoredLineEnding::Lf) } }))
    )]
    #[inline]
    fn try_from(source: VerbatimOwned) -> Result<Self, Self::Error>
    {
        let VerbatimOwned { text } = source;
        let lines = scan_verbatim(VerbatimSource::from(text.as_str()))?;
        Ok(Self { bytes: text, lines })
    }
}
/// Validates newline-free text and returns its checked scalar width.
///
/// # Specification
/// - requires: `source` is the complete candidate text.
/// - ensures: success returns the exact scalar count and rejects forbidden
///   carriage returns, line feeds, and tabs.
/// - provides: the validation boundary shared by borrowed and owned text.
/// - fails: returns `InvalidText` for forbidden scalars or `ArithmeticOverflow`
///   for an unrepresentable scalar count.
/// - panics: none.
///
/// # Errors
/// Returns `InvalidText` or `ArithmeticOverflow`.
///
/// # Adequacy
/// - hypothesis: L3 — empty text, multibyte scalars, NUL and each forbidden
///   scalar at distinct positions expose exact bytes, scalar width, byte charge
///   and typed rejection. Owned inputs also expose allocation identity.
///   Byte-counted widths, normalization, skipped forbidden scalars and cloning
///   the adopted buffer change these observations; allocation failure is not
///   deterministically injected.
/// - witness: `arena::tests::text_ingestion_preserves_unicode_counts_and_owned_allocations`
#[anodized::spec(
    ensures: |ret| ret.as_ref().map_or_else(|error| if source.text.contains(['\r', '\n', '\t']) { *error == BuildError::InvalidText }
        else { u32::try_from(source.text.chars().count()).is_err()
            && *error == BuildError::ArithmeticOverflow { operation: BuildArithmetic::ScalarWidth } },
        |width| !source.text.contains(['\r', '\n', '\t'])
            && usize::try_from(u32::from(*width)) == Ok(source.text.chars().count()))
)]
fn checked_text_width(source: TextSource<'_>) -> Result<ScalarWidth, BuildError>
{
    if source
        .text
        .chars()
        .any(|character| matches!(character, '\r' | '\n' | '\t'))
    {
        return Err(BuildError::InvalidText);
    }
    ScalarWidth::try_from(source.text.chars().count())
}

/// Scans LF and CRLF text into nominal physical-fragment records.
///
/// # Specification
/// - requires: `source` is the complete candidate verbatim text.
/// - ensures: success returns one record per physical fragment, including the
///   empty fragment after a trailing line ending.
/// - provides: the byte-preserving line metrics used by the arena.
/// - fails: returns `InvalidVerbatimLineEnding`, `ArithmeticOverflow`, or
///   `AllocationFailed` without returning partial scan output.
/// - panics: none.
///
/// # Errors
/// Returns the typed scan or allocation error that prevents a complete scan.
///
/// # Adequacy
/// - hypothesis: L3 — all strings of up to four symbols over ASCII, a multibyte
///   scalar, CR, LF and tab are checked against a split-based physical-fragment
///   oracle. Exact bytes, widths, ending variants and final fragments
///   distinguish normalization, byte-counted widths, missing trailing fragments
///   and acceptance of bare CR. Allocation failure and widths beyond u32 are
///   outside this bounded witness domain.
/// - witness: `arena::tests::short_verbatim_inputs_match_an_independent_fragment_oracle`
#[anodized::spec(
    ensures: |ret| ret.as_ref().map_or_else(|error| match *error { BuildError::InvalidVerbatimLineEnding => source.text.match_indices('\r').any(|(offset, _)| source.text.as_bytes().get(offset.saturating_add(1)) != Some(&b'\n')), BuildError::ArithmeticOverflow { operation: BuildArithmetic::ScalarWidth } => source.text.split('\n').any(|fragment| u32::try_from(fragment.strip_suffix('\r').unwrap_or(fragment).chars().count()).is_err()), BuildError::AllocationFailed { site: BuildAllocationSite::VerbatimArena } => true, _ => false },
        |lines| !(source.text.match_indices('\r').any(|(offset, _)| source.text.as_bytes().get(offset.saturating_add(1)) != Some(&b'\n')))
            && lines.len() == source.text.bytes().filter(|byte| *byte == b'\n').count().saturating_add(1)
            && lines.iter().zip(source.text.split('\n')).enumerate().all(|(index, (line, fragment))| { let last = index.saturating_add(1) == lines.len();
        let crlf = !last
            && fragment.ends_with('\r');
        let content = if crlf { fragment.strip_suffix('\r').unwrap_or(fragment) }
        else { fragment };
        u32::try_from(content.chars().count()).is_ok_and(|width| u32::from(line.scalar_width) == width)
            && line.ending == if last { Maybe::Absent(ending::Absent::Final) }
        else if crlf { Maybe::Present(StoredLineEnding::CrLf) }
        else { Maybe::Present(StoredLineEnding::Lf) } }))
)]
fn scan_verbatim(source: VerbatimSource<'_>) -> Result<Vec<VerbatimLine>, BuildError>
{
    let mut lines = Vec::new();
    let mut chars = source.text.chars();
    let mut width = 0u32;
    while let Some(character) = chars.next() {
        let ending = match character {
            | '\n' => Some(StoredLineEnding::Lf),
            | '\r' => match chars.next() {
                | Some('\n') => Some(StoredLineEnding::CrLf),
                | Some(_) | None => return Err(BuildError::InvalidVerbatimLineEnding),
            },
            | _ => {
                width = width
                    .checked_add(1u32)
                    .ok_or(BuildError::ArithmeticOverflow {
                        operation: BuildArithmetic::ScalarWidth,
                    })?;
                None
            },
        };
        if let Some(ending) = ending {
            lines
                .try_reserve(1usize)
                .map_err(|_error| BuildError::AllocationFailed {
                    site: BuildAllocationSite::VerbatimArena,
                })?;
            lines.push(VerbatimLine {
                scalar_width: ScalarWidth::from(width),
                ending: Maybe::Present(ending),
            });
            width = 0u32;
        }
    }
    lines
        .try_reserve(1usize)
        .map_err(|_error| BuildError::AllocationFailed {
            site: BuildAllocationSite::VerbatimArena,
        })?;
    lines.push(VerbatimLine {
        scalar_width: ScalarWidth::from(width),
        ending: Maybe::Absent(ending::Absent::Final),
    });
    Ok(lines)
}

/// A stored document node.
///
/// # Specification
/// - requires: every identity a variant carries names an earlier node in the
///   same arena.
/// - ensures: the store is a directed acyclic graph by construction.
/// - provides: the complete document algebra, including arbitrary choice and
///   unaligned concatenation.
/// - panics: none.
/// - executable: none — this data declaration has no executable invocation;
///   ingestion, construction and checked projections carry the relevant
///   predicates.
///
/// # Adequacy
/// - hypothesis: L3 — exhaustive small documents compare concatenation, choice,
///   nesting, alignment, flattening and line behavior with a direct oracle.
///   Reversing child order, changing flat images or mixing incoming column with
///   indentation changes the selected cost or output.
/// - witness: `algebra::tests::exhaustive_small_documents_match_the_direct_oracle`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(crate) enum DocNode
{
    /// Emits nothing.
    Empty,
    /// Emits newline-free text.
    Text(TextId),
    /// Emits opaque multiline bytes.
    Verbatim(VerbatimId),
    /// A layout-owned line break, softened to a space by flattening.
    Line,
    /// A line break that survives flattening.
    HardLine,
    /// Unaligned concatenation.
    Concat
    {
        /// Resolved first.
        left: NodeId,
        /// Resolved at the left's ending column.
        right: NodeId,
    },
    /// Raised indentation over a child.
    Nest
    {
        /// The checked amount added to the current indentation.
        amount: u32,
        /// The child resolved under the raised indentation.
        doc: NodeId,
    },
    /// Indentation set to the current column over a child.
    Align
    {
        /// The child resolved under the aligned indentation.
        doc: NodeId,
    },
    /// Arbitrary choice between two children.
    Choice
    {
        /// The left alternative, which wins a tie.
        left: NodeId,
        /// The right alternative.
        right: NodeId,
    },
    /// The flattened image of a child.
    Flatten
    {
        /// The child whose memoized flattened image is used.
        doc: NodeId,
    },
}

/// A finished, immutable, shareable document.
///
/// Finalization has already computed each node's flattened image, so the
/// resolver never needs flattening as a second memo dimension.
///
/// # Specification
/// - requires: the arena came from a builder that finished without refusing.
/// - ensures: identities are stable, the graph is acyclic, and every node has
///   an entry in the flattened image table.
/// - provides: the immutable input the resolver and the renderer read.
/// - panics: none.
/// - executable: none — this data declaration has no executable invocation;
///   ingestion, construction and checked projections carry the relevant
///   predicates.
///
/// # Adequacy
/// - hypothesis: L3 — first and last identities, the next ordinal, maximal
///   ordinals, foreign arenas and wrong node kinds are observed through exact
///   payloads or typed absence. Dropping the arena check, shifting a bound,
///   reading a different store and returning a different payload change these
///   observations; borrowed private projections also expose storage identity.
/// - witness: `arena::tests::arena_projections_separate_namespaces_kinds_and_store_bounds`
#[derive(Clone, Debug)]
pub struct DocArena
{
    /// The arena this identity belongs to.
    arena: ArenaKey,
    /// The document node store.
    nodes: Vec<DocNode>,
    /// The text store.
    texts: Vec<CheckedText>,
    /// The verbatim store.
    verbatim: Vec<VerbatimText>,
    /// Each node's flattened image, computed at finalization.
    flattened: Vec<NodeId>,
}

impl DocArena
{
    /// Returns the number of stored document nodes, including flattened images.
    ///
    /// # Specification
    /// - requires: the arena was sealed by a successful builder finalization.
    /// - ensures: the result equals the arena's dense node-store length.
    /// - provides: the public storage observation used by build accounting.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — shared handles and finalized images expose exact node
    ///   cardinality without charging each reference as a new identity.
    ///   Counting edges, omitting appended images and changing dense insertion
    ///   order alter the count or stored identities.
    /// - witness: `algebra::tests::finalization_appends_at_most_one_image_per_node`
    /// - witness: `algebra::tests::identities_are_dense_insertion_ordinals_that_never_move`
    #[anodized::spec(
        ensures: |ret| u64::try_from(self.nodes.len()).map_or_else(|_error| u64::from(ret) == u64::MAX,
            |count| u64::from(ret) == count)
    )]
    #[inline]
    #[must_use]
    pub fn node_count(&self) -> DocNodesUsed
    {
        let nodes = u64::try_from(self.nodes.len()).unwrap_or(u64::MAX);
        DocNodesUsed::from(nodes)
    }

    /// Returns the stored newline-free text for a text handle.
    ///
    /// # Specification
    /// - requires: `doc` is any client handle, including a foreign,
    ///   out-of-range or wrong-kind handle.
    /// - ensures: the returned nominal value contains the exact stored bytes.
    /// - provides: a read-only semantic projection for tests and renderers.
    /// - fails: returns `UnknownDoc` for foreign, invalid, or non-text handles,
    ///   and `ArithmeticOverflow` for an unrepresentable internal index.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `UnknownDoc` for a foreign, invalid, or non-text handle, or
    /// `ArithmeticOverflow` for an unrepresentable index conversion.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — first and last identities, the next ordinal, maximal
    ///   ordinals, foreign arenas and wrong node kinds are observed through
    ///   exact payloads or typed absence. Dropping the arena check, shifting a
    ///   bound, reading a different store and returning a different payload
    ///   change these observations; borrowed private projections also expose
    ///   storage identity.
    /// - witness: `arena::tests::arena_projections_separate_namespaces_kinds_and_store_bounds`
    #[anodized::spec(
        ensures: |ret| { let expected = (self.arena == doc.arena
                && u32::try_from(self.nodes.len()).is_ok_and(|count| doc.node.index < count)).then_some(doc.node.index).and_then(|index| usize::try_from(index).ok()).and_then(|index| self.nodes.get(index)).and_then(|node| match *node { DocNode::Text(identity) => self.texts.get(usize::try_from(identity.index).ok()?), _ => None });
            ret.as_ref().map_or_else(|error| expected.is_none()
                && matches!(*error, BuildError::UnknownDoc | BuildError::ArithmeticOverflow { operation: BuildArithmetic::IdConversion }),
            |actual| expected.is_some_and(|expected| actual.text == expected.text)) }
    )]
    #[inline]
    pub fn stored_text(
        &self,
        doc: DocId,
    ) -> Result<TextOwned, BuildError>
    {
        let node = self.node_id_for(doc)?;
        let index =
            usize::try_from(u32::from(node)).map_err(|_error| BuildError::ArithmeticOverflow {
                operation: BuildArithmetic::IdConversion,
            })?;
        let Some(DocNode::Text(text)) = self.nodes.get(index).copied()
        else {
            return Err(BuildError::UnknownDoc);
        };
        let index =
            usize::try_from(u32::from(text)).map_err(|_error| BuildError::ArithmeticOverflow {
                operation: BuildArithmetic::IdConversion,
            })?;
        self.texts
            .get(index)
            .map(|text| TextOwned::from(text.text.clone()))
            .ok_or(BuildError::UnknownDoc)
    }

    /// Returns the checked scalar width stored beside a text identity.
    ///
    /// # Specification
    /// - requires: `doc` is any client handle, including a foreign,
    ///   out-of-range or wrong-kind handle.
    /// - ensures: the result is the width computed during ingestion.
    /// - provides: a nominal width projection without exposing raw bytes.
    /// - fails: returns `UnknownDoc` for foreign, invalid, or non-text handles,
    ///   and `ArithmeticOverflow` for an unrepresentable internal index.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `UnknownDoc` for an invalid handle, or `ArithmeticOverflow` for
    /// an unrepresentable index conversion.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — first and last identities, the next ordinal, maximal
    ///   ordinals, foreign arenas and wrong node kinds are observed through
    ///   exact payloads or typed absence. Dropping the arena check, shifting a
    ///   bound, reading a different store and returning a different payload
    ///   change these observations; borrowed private projections also expose
    ///   storage identity.
    /// - witness: `arena::tests::arena_projections_separate_namespaces_kinds_and_store_bounds`
    #[anodized::spec(
        ensures: |ret| { let expected = (self.arena == doc.arena
                && u32::try_from(self.nodes.len()).is_ok_and(|count| doc.node.index < count)).then_some(doc.node.index).and_then(|index| usize::try_from(index).ok()).and_then(|index| self.nodes.get(index)).and_then(|node| match *node { DocNode::Text(identity) => self.texts.get(usize::try_from(identity.index).ok()?), _ => None });
            ret.as_ref().map_or_else(|error| expected.is_none()
                && matches!(*error, BuildError::UnknownDoc | BuildError::ArithmeticOverflow { operation: BuildArithmetic::IdConversion }),
            |actual| expected.is_some_and(|expected| *actual == expected.width)) }
    )]
    #[inline]
    pub fn stored_text_width(
        &self,
        doc: DocId,
    ) -> Result<ScalarWidth, BuildError>
    {
        let node = self.node_id_for(doc)?;
        let index =
            usize::try_from(u32::from(node)).map_err(|_error| BuildError::ArithmeticOverflow {
                operation: BuildArithmetic::IdConversion,
            })?;
        let Some(DocNode::Text(text)) = self.nodes.get(index).copied()
        else {
            return Err(BuildError::UnknownDoc);
        };
        let index =
            usize::try_from(u32::from(text)).map_err(|_error| BuildError::ArithmeticOverflow {
                operation: BuildArithmetic::IdConversion,
            })?;
        self.texts
            .get(index)
            .map(CheckedText::width)
            .ok_or(BuildError::UnknownDoc)
    }

    /// Returns the stored verbatim bytes for a verbatim handle.
    ///
    /// # Specification
    /// - requires: `doc` is any client handle, including a foreign,
    ///   out-of-range or wrong-kind handle.
    /// - ensures: the returned nominal value contains the exact stored bytes.
    /// - provides: a read-only byte-identity projection.
    /// - fails: returns `UnknownDoc` for foreign, invalid, or non-verbatim
    ///   handles, and `ArithmeticOverflow` for an unrepresentable index.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `UnknownDoc` for an invalid handle, or `ArithmeticOverflow` for
    /// an unrepresentable index conversion.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — first and last identities, the next ordinal, maximal
    ///   ordinals, foreign arenas and wrong node kinds are observed through
    ///   exact payloads or typed absence. Dropping the arena check, shifting a
    ///   bound, reading a different store and returning a different payload
    ///   change these observations; borrowed private projections also expose
    ///   storage identity.
    /// - witness: `arena::tests::arena_projections_separate_namespaces_kinds_and_store_bounds`
    #[anodized::spec(
        ensures: |ret| { let expected = (self.arena == doc.arena
                && u32::try_from(self.nodes.len()).is_ok_and(|count| doc.node.index < count)).then_some(doc.node.index).and_then(|index| usize::try_from(index).ok()).and_then(|index| self.nodes.get(index)).and_then(|node| match *node { DocNode::Verbatim(identity) => self.verbatim.get(usize::try_from(identity.index).ok()?), _ => None });
            ret.as_ref().map_or_else(|error| expected.is_none()
                && matches!(*error, BuildError::UnknownDoc | BuildError::ArithmeticOverflow { operation: BuildArithmetic::IdConversion }),
            |actual| expected.is_some_and(|expected| actual.text == expected.bytes)) }
    )]
    #[inline]
    pub fn stored_verbatim(
        &self,
        doc: DocId,
    ) -> Result<VerbatimOwned, BuildError>
    {
        let node = self.node_id_for(doc)?;
        let index =
            usize::try_from(u32::from(node)).map_err(|_error| BuildError::ArithmeticOverflow {
                operation: BuildArithmetic::IdConversion,
            })?;
        let Some(DocNode::Verbatim(verbatim)) = self.nodes.get(index).copied()
        else {
            return Err(BuildError::UnknownDoc);
        };
        let index = usize::try_from(u32::from(verbatim)).map_err(|_error| {
            BuildError::ArithmeticOverflow {
                operation: BuildArithmetic::IdConversion,
            }
        })?;
        self.verbatim
            .get(index)
            .map(|verbatim| VerbatimOwned::from(verbatim.bytes.clone()))
            .ok_or(BuildError::UnknownDoc)
    }

    /// Returns the stored fragment records for a verbatim handle.
    ///
    /// # Specification
    /// - requires: `doc` is any client handle, including a foreign,
    ///   out-of-range or wrong-kind handle.
    /// - ensures: widths and endings are the records produced by ingestion.
    /// - provides: a read-only nominal metric projection.
    /// - fails: returns `UnknownDoc` for foreign, invalid, or non-verbatim
    ///   handles, and `ArithmeticOverflow` for an unrepresentable index.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `UnknownDoc` for an invalid handle, or `ArithmeticOverflow` for
    /// an unrepresentable index conversion.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — first and last identities, the next ordinal, maximal
    ///   ordinals, foreign arenas and wrong node kinds are observed through
    ///   exact payloads or typed absence. Dropping the arena check, shifting a
    ///   bound, reading a different store and returning a different payload
    ///   change these observations; borrowed private projections also expose
    ///   storage identity.
    /// - witness: `arena::tests::arena_projections_separate_namespaces_kinds_and_store_bounds`
    #[anodized::spec(
        ensures: |ret| { let expected = (self.arena == doc.arena
                && u32::try_from(self.nodes.len()).is_ok_and(|count| doc.node.index < count)).then_some(doc.node.index).and_then(|index| usize::try_from(index).ok()).and_then(|index| self.nodes.get(index)).and_then(|node| match *node { DocNode::Verbatim(identity) => self.verbatim.get(usize::try_from(identity.index).ok()?), _ => None });
            ret.as_ref().map_or_else(|error| expected.is_none()
                && matches!(*error, BuildError::UnknownDoc | BuildError::ArithmeticOverflow { operation: BuildArithmetic::IdConversion }),
            |actual| expected.is_some_and(|expected| actual.as_slice() == expected.lines.as_slice())) }
    )]
    #[inline]
    pub fn verbatim_lines(
        &self,
        doc: DocId,
    ) -> Result<Vec<VerbatimLine>, BuildError>
    {
        let node = self.node_id_for(doc)?;
        let index =
            usize::try_from(u32::from(node)).map_err(|_error| BuildError::ArithmeticOverflow {
                operation: BuildArithmetic::IdConversion,
            })?;
        let Some(DocNode::Verbatim(verbatim)) = self.nodes.get(index).copied()
        else {
            return Err(BuildError::UnknownDoc);
        };
        let index = usize::try_from(u32::from(verbatim)).map_err(|_error| {
            BuildError::ArithmeticOverflow {
                operation: BuildArithmetic::IdConversion,
            }
        })?;
        self.verbatim
            .get(index)
            .map(|verbatim| verbatim.lines.clone())
            .ok_or(BuildError::UnknownDoc)
    }

    /// Returns the finalized flattened image of a document handle.
    ///
    /// # Specification
    /// - requires: `doc` names any stored node in this arena.
    /// - ensures: the returned handle names the memoized flattened image.
    /// - provides: a read-only finalization projection for identity checks.
    /// - fails: returns `UnknownDoc` for foreign or invalid handles, and
    ///   `ArithmeticOverflow` for an unrepresentable internal index.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `UnknownDoc` for an invalid handle, or `ArithmeticOverflow` for
    /// an unrepresentable index conversion.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — first and last identities, the next ordinal, maximal
    ///   ordinals, foreign arenas and wrong node kinds are observed through
    ///   exact payloads or typed absence. Dropping the arena check, shifting a
    ///   bound, reading a different store and returning a different payload
    ///   change these observations; borrowed private projections also expose
    ///   storage identity.
    /// - witness: `arena::tests::arena_projections_separate_namespaces_kinds_and_store_bounds`
    #[anodized::spec(
        ensures: |ret| { let expected = (self.arena == doc.arena
                && u32::try_from(self.nodes.len()).is_ok_and(|count| doc.node.index < count)).then_some(doc.node.index).and_then(|index| usize::try_from(index).ok()).and_then(|index| self.flattened.get(index));
            ret.as_ref().map_or_else(|error| expected.is_none()
                && matches!(*error, BuildError::UnknownDoc | BuildError::ArithmeticOverflow { operation: BuildArithmetic::IdConversion }),
            |actual| actual.arena == self.arena
                && expected == Some(&actual.node)) }
    )]
    #[inline]
    pub fn flattened_image(
        &self,
        doc: DocId,
    ) -> Result<DocId, BuildError>
    {
        let node = self.node_id_for(doc)?;
        let index =
            usize::try_from(u32::from(node)).map_err(|_error| BuildError::ArithmeticOverflow {
                operation: BuildArithmetic::IdConversion,
            })?;
        self.flattened
            .get(index)
            .copied()
            .map(|flattened| DocId::from_parts(self.arena, flattened))
            .ok_or(BuildError::UnknownDoc)
    }

    /// Validates a handle and returns its internal node identity.
    ///
    /// # Specification
    /// - requires: `doc` may be foreign, out of range, or valid.
    /// - ensures: success returns only an identity present in this arena.
    /// - provides: the shared validation boundary for every projection.
    /// - fails: returns `UnknownDoc` before any store lookup for foreign or
    ///   out-of-range handles.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `UnknownDoc` when the handle is foreign or out of range.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — first and last identities, the next ordinal, maximal
    ///   ordinals, foreign arenas and wrong node kinds are observed through
    ///   exact payloads or typed absence. Dropping the arena check, shifting a
    ///   bound, reading a different store and returning a different payload
    ///   change these observations; borrowed private projections also expose
    ///   storage identity.
    /// - witness: `arena::tests::arena_projections_separate_namespaces_kinds_and_store_bounds`
    #[anodized::spec(
        ensures: |ret| ret == if self.arena == doc.arena
                && u32::try_from(self.nodes.len()).is_ok_and(|count| doc.node.index < count) { Ok(doc.node) }
            else { Err(BuildError::UnknownDoc) }
    )]
    fn node_id_for(
        &self,
        doc: DocId,
    ) -> Result<NodeId, BuildError>
    {
        let DocHandleStatus::Present = self.contains(doc)
        else {
            return Err(BuildError::UnknownDoc);
        };
        Ok(doc.node_id())
    }

    /// Checks whether `doc` is a valid handle for this arena.
    ///
    /// # Specification
    /// - requires: `doc` is any client handle, including one from another
    ///   arena.
    /// - ensures: foreign and out-of-range handles return `Absent` before
    ///   lookup.
    /// - provides: a non-panicking identity check for every caller.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — first and last identities, the next ordinal, maximal
    ///   ordinals, foreign arenas and wrong node kinds are observed through
    ///   exact payloads or typed absence. Dropping the arena check, shifting a
    ///   bound, reading a different store and returning a different payload
    ///   change these observations; borrowed private projections also expose
    ///   storage identity.
    /// - witness: `arena::tests::arena_projections_separate_namespaces_kinds_and_store_bounds`
    #[anodized::spec(
        ensures: |ret| matches!(ret, DocHandleStatus::Present) == (self.arena == doc.arena
                && u32::try_from(self.nodes.len()).is_ok_and(|count| doc.node.index < count))
    )]
    #[inline]
    #[must_use]
    pub fn contains(
        &self,
        doc: DocId,
    ) -> DocHandleStatus
    {
        let Ok(node_count) = u32::try_from(self.nodes.len())
        else {
            return DocHandleStatus::Absent;
        };
        if self.arena == doc.arena_key() && u32::from(doc.node_id()) < node_count {
            DocHandleStatus::Present
        }
        else {
            DocHandleStatus::Absent
        }
    }

    /// Returns a stored node for resolver lookup.
    ///
    /// # Specification
    /// - requires: `node` may be out of range.
    /// - ensures: lookup answers by store bounds rather than indexing.
    /// - provides: the resolver's checked node projection;
    ///   [`stored::Absent::OutOfRange`] past the node store.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — first and last identities, the next ordinal, maximal
    ///   ordinals, foreign arenas and wrong node kinds are observed through
    ///   exact payloads or typed absence. Dropping the arena check, shifting a
    ///   bound, reading a different store and returning a different payload
    ///   change these observations; borrowed private projections also expose
    ///   storage identity.
    /// - witness: `arena::tests::arena_projections_separate_namespaces_kinds_and_store_bounds`
    #[anodized::spec(
        ensures: |ret| { let expected = usize::try_from(node.index).ok().and_then(|index| self.nodes.get(index));
            match (ret, expected) { (Maybe::Present(actual), Some(expected)) => actual == *expected, (Maybe::Absent(stored::Absent::OutOfRange), None) => true, _ => false } }
    )]
    #[inline]
    pub(crate) fn node(
        &self,
        node: NodeId,
    ) -> Maybe<DocNode, stored::Absent>
    {
        match usize::try_from(u32::from(node))
            .ok()
            .and_then(|index| self.nodes.get(index))
        {
            | Some(&stored) => Maybe::Present(stored),
            | None => Maybe::Absent(stored::Absent::OutOfRange),
        }
    }

    /// Returns the finalized flattened image for a node.
    ///
    /// # Specification
    /// - requires: `node` is an arena identity.
    /// - ensures: every finalized identity has one image entry.
    /// - provides: flatten resolution without a second memo dimension;
    ///   [`stored::Absent::OutOfRange`] past the image table.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — first and last identities, the next ordinal, maximal
    ///   ordinals, foreign arenas and wrong node kinds are observed through
    ///   exact payloads or typed absence. Dropping the arena check, shifting a
    ///   bound, reading a different store and returning a different payload
    ///   change these observations; borrowed private projections also expose
    ///   storage identity.
    /// - witness: `arena::tests::arena_projections_separate_namespaces_kinds_and_store_bounds`
    #[anodized::spec(
        ensures: |ret| { let expected = usize::try_from(node.index).ok().and_then(|index| self.flattened.get(index));
            match (ret, expected) { (Maybe::Present(actual), Some(expected)) => actual == *expected, (Maybe::Absent(stored::Absent::OutOfRange), None) => true, _ => false } }
    )]
    #[inline]
    pub(crate) fn flattened_node(
        &self,
        node: NodeId,
    ) -> Maybe<NodeId, stored::Absent>
    {
        match usize::try_from(u32::from(node))
            .ok()
            .and_then(|index| self.flattened.get(index))
        {
            | Some(&image) => Maybe::Present(image),
            | None => Maybe::Absent(stored::Absent::OutOfRange),
        }
    }

    /// Returns a checked text identity by its private store id.
    ///
    /// # Specification
    /// - requires: `text` was minted by this arena.
    /// - ensures: lookup answers by store bounds rather than indexing.
    /// - provides: byte and width metrics for resolution;
    ///   [`stored::Absent::OutOfRange`] past the text store.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — first and last identities, the next ordinal, maximal
    ///   ordinals, foreign arenas and wrong node kinds are observed through
    ///   exact payloads or typed absence. Dropping the arena check, shifting a
    ///   bound, reading a different store and returning a different payload
    ///   change these observations; borrowed private projections also expose
    ///   storage identity.
    /// - witness: `arena::tests::arena_projections_separate_namespaces_kinds_and_store_bounds`
    #[anodized::spec(
        ensures: |ret| { let expected = usize::try_from(text.index).ok().and_then(|index| self.texts.get(index));
            match (ret, expected) { (Maybe::Present(actual), Some(expected)) => core::ptr::eq(&raw const *actual, &raw const *expected), (Maybe::Absent(stored::Absent::OutOfRange), None) => true, _ => false } }
    )]
    #[inline]
    pub(crate) fn text_identity(
        &self,
        text: TextId,
    ) -> Maybe<&CheckedText, stored::Absent>
    {
        match usize::try_from(u32::from(text))
            .ok()
            .and_then(|index| self.texts.get(index))
        {
            | Some(identity) => Maybe::Present(identity),
            | None => Maybe::Absent(stored::Absent::OutOfRange),
        }
    }

    /// Returns a verbatim identity by its private store id.
    ///
    /// # Specification
    /// - requires: `verbatim` was minted by this arena.
    /// - ensures: lookup answers by store bounds rather than indexing.
    /// - provides: exact bytes and physical fragment metrics;
    ///   [`stored::Absent::OutOfRange`] past the verbatim store.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — first and last identities, the next ordinal, maximal
    ///   ordinals, foreign arenas and wrong node kinds are observed through
    ///   exact payloads or typed absence. Dropping the arena check, shifting a
    ///   bound, reading a different store and returning a different payload
    ///   change these observations; borrowed private projections also expose
    ///   storage identity.
    /// - witness: `arena::tests::arena_projections_separate_namespaces_kinds_and_store_bounds`
    #[anodized::spec(
        ensures: |ret| { let expected = usize::try_from(verbatim.index).ok().and_then(|index| self.verbatim.get(index));
            match (ret, expected) { (Maybe::Present(actual), Some(expected)) => core::ptr::eq(&raw const *actual, &raw const *expected), (Maybe::Absent(stored::Absent::OutOfRange), None) => true, _ => false } }
    )]
    #[inline]
    pub(crate) fn verbatim_identity(
        &self,
        verbatim: VerbatimId,
    ) -> Maybe<&VerbatimText, stored::Absent>
    {
        match usize::try_from(u32::from(verbatim))
            .ok()
            .and_then(|index| self.verbatim.get(index))
        {
            | Some(identity) => Maybe::Present(identity),
            | None => Maybe::Absent(stored::Absent::OutOfRange),
        }
    }
}

impl From<u32> for NodeId
{
    /// The node at dense insertion ordinal `index`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: u32) -> Self
    {
        Self { index }
    }
}

impl From<NodeId> for u32
{
    /// The node's dense insertion ordinal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(node: NodeId) -> Self
    {
        node.index
    }
}

impl From<u32> for TextId
{
    /// The text at dense insertion ordinal `index`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: u32) -> Self
    {
        Self { index }
    }
}

impl From<TextId> for u32
{
    /// The text's dense insertion ordinal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(text: TextId) -> Self
    {
        text.index
    }
}

impl From<u32> for VerbatimId
{
    /// The verbatim text at dense insertion ordinal `index`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: u32) -> Self
    {
        Self { index }
    }
}

impl From<VerbatimId> for u32
{
    /// The verbatim text's dense insertion ordinal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(verbatim: VerbatimId) -> Self
    {
        verbatim.index
    }
}

impl From<NonZeroU32> for ArenaKey
{
    /// The arena key carrying `token`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(token: NonZeroU32) -> Self
    {
        Self { token }
    }
}

impl DocId
{
    /// Creates a crate-internal handle from its checked arena and node parts.
    ///
    /// # Specification
    /// - requires: `arena` and `node` were minted by the same builder.
    /// - ensures: the resulting public handle carries both identity components.
    /// - provides: the builder's only internal handle assembly operation.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — first, last, foreign and out-of-range handles are
    ///   observed through exact payloads and typed refusal. Changing the
    ///   namespace or insertion identity changes those observations; assembling
    ///   a handle does not validate its store bounds.
    /// - witness: `arena::tests::arena_projections_separate_namespaces_kinds_and_store_bounds`
    #[anodized::spec(
        ensures: |ret| ret.arena == arena
                && ret.node == node
    )]
    #[inline]
    pub(crate) fn from_parts(
        arena: ArenaKey,
        node: NodeId,
    ) -> Self
    {
        Self { arena, node }
    }

    /// Returns the crate-internal arena component of this handle.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) const fn arena_key(self) -> ArenaKey
    {
        self.arena
    }

    /// Returns the crate-internal dense node component of this handle.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) const fn node_id(self) -> NodeId
    {
        self.node
    }
}

impl DocArena
{
    /// Creates a sealed arena from crate-internal finalized stores.
    ///
    /// # Specification
    /// - requires: `flattened` contains one image entry for every stored node.
    /// - ensures: all finalized stores move into one immutable arena.
    /// - provides: the builder-to-arena ownership boundary.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — sealed arenas expose preserved payloads, namespace
    ///   checks and idempotent flattened images. Substituting a store, changing
    ///   a namespace or losing an image changes these observations. The
    ///   predicate observes allocation identity and lengths without cloning
    ///   owned stores; the builder owns structural validation.
    /// - witness: `arena::tests::arena_projections_separate_namespaces_kinds_and_store_bounds`
    /// - witness: `algebra::tests::flattening_is_idempotent`
    /// - witness: `algebra::tests::finalization_reuses_the_original_identity_when_nothing_changes`
    #[anodized::spec(
        captures: before = (nodes.as_ptr(), nodes.len(), texts.as_ptr(), texts.len(), verbatim.as_ptr(), verbatim.len(), flattened.as_ptr(), flattened.len()),
        ensures: |ret| ret.arena == arena
                && ret.nodes.as_ptr() == before.0
                && ret.nodes.len() == before.1
                && ret.texts.as_ptr() == before.2
                && ret.texts.len() == before.3
                && ret.verbatim.as_ptr() == before.4
                && ret.verbatim.len() == before.5
                && ret.flattened.as_ptr() == before.6
                && ret.flattened.len() == before.7
    )]
    #[inline]
    pub(crate) fn from_parts(
        arena: ArenaKey,
        nodes: Vec<DocNode>,
        texts: Vec<CheckedText>,
        verbatim: Vec<VerbatimText>,
        flattened: Vec<NodeId>,
    ) -> Self
    {
        Self {
            arena,
            nodes,
            texts,
            verbatim,
            flattened,
        }
    }
}

#[cfg(test)]
mod tests
{
    use super::*;
    use crate::build::DocBuilder;
    use crate::limits::BuildLimits;
    use crate::limits::BuildMeter;

    /// Scalar widths, exact bytes and ownership remain distinct observations.
    #[test]
    fn text_ingestion_preserves_unicode_counts_and_owned_allocations() -> Result<(), BuildError>
    {
        for source in ["", "a\0β𐐀", "e\u{301}"] {
            let borrowed = CheckedText::try_from(TextSource::from(source))?;
            assert_eq!(borrowed.as_ref(), source);
            assert_eq!(
                usize::try_from(u32::from(borrowed.width())),
                Ok(source.chars().count())
            );
            assert_eq!(
                borrowed.bytes_used().map(u64::from),
                u64::try_from(source.len()).map_err(|_error| BuildError::ArithmeticOverflow {
                    operation: BuildArithmetic::TextBytes
                })
            );
            let mut owned = String::with_capacity(64);
            owned.push_str(source);
            let pointer = owned.as_ptr();
            let adopted = CheckedText::try_from(TextOwned::from(owned))?;
            assert_eq!(adopted, borrowed);
            assert_eq!(adopted.text.as_ptr(), pointer);
        }
        // workflow-gates: allow-escaped-newline
        for source in ["\r", "\n", "\t", "prefix\r𐐀", "𐐀\nend", "\tend"] {
            assert_eq!(
                CheckedText::try_from(TextSource::from(source)),
                Err(BuildError::InvalidText)
            );
            assert_eq!(
                CheckedText::try_from(TextOwned::from(String::from(source))),
                Err(BuildError::InvalidText)
            );
        }
        Ok(())
    }

    /// Exhaustive short inputs distinguish physical endings from scalar width
    /// and final fragments.
    #[test]
    fn short_verbatim_inputs_match_an_independent_fragment_oracle()
    {
        let alphabet = ['a', '𐐀', '\r', '\n', '\t'];
        for length in 0_u32 ..= 4 {
            for encoded in 0_u32 .. 5_u32.saturating_pow(length) {
                let mut source = String::new();
                let mut rest = encoded;
                for _ in 0 .. length {
                    let digit = rest.checked_rem(5).expect("nonzero radix");
                    source.push(
                        *alphabet
                            .get(usize::try_from(digit).expect("small digit"))
                            .expect("digit in alphabet"),
                    );
                    rest = rest.checked_div(5).expect("nonzero radix");
                }
                let expected = (|| {
                    let mut fragments = source.split('\n').peekable();
                    let mut lines = Vec::new();
                    while let Some(fragment) = fragments.next() {
                        let (content, ending) = if fragments.peek().is_none() {
                            (fragment, Maybe::Absent(ending::Absent::Final))
                        }
                        else if let Some(content) = fragment.strip_suffix('\r') {
                            (content, Maybe::Present(StoredLineEnding::CrLf))
                        }
                        else {
                            (fragment, Maybe::Present(StoredLineEnding::Lf))
                        };
                        if content.contains('\r') {
                            return Err(BuildError::InvalidVerbatimLineEnding);
                        }
                        lines.push(VerbatimLine {
                            scalar_width: ScalarWidth::from(
                                u32::try_from(content.chars().count()).expect("bounded fragment"),
                            ),
                            ending,
                        });
                    }
                    Ok(lines)
                })();
                assert_eq!(
                    scan_verbatim(VerbatimSource::from(source.as_str())),
                    expected
                );
                let borrowed = VerbatimText::try_from(VerbatimSource::from(source.as_str()));
                assert_eq!(
                    borrowed.as_ref().map(VerbatimText::lines),
                    expected.as_ref().map(Vec::as_slice)
                );
                if let Ok(value) = borrowed.as_ref() {
                    assert_eq!(value.as_ref(), source);
                    assert_eq!(
                        value.bytes_used().map(u64::from),
                        Ok(u64::try_from(source.len()).expect("bounded source"))
                    );
                    assert_eq!(
                        value.lines_used().map(u64::from),
                        Ok(
                            u64::try_from(expected.as_ref().expect("successful scan").len())
                                .expect("bounded lines")
                        )
                    );
                    for (line, expected_line) in value
                        .lines()
                        .iter()
                        .zip(expected.as_ref().expect("successful scan"))
                    {
                        assert_eq!(line.scalar_width(), expected_line.scalar_width);
                        assert_eq!(line.ending(), expected_line.ending);
                    }
                }
                let pointer = source.as_ptr();
                let owned = VerbatimText::try_from(VerbatimOwned::from(source));
                assert_eq!(owned, borrowed);
                if let Ok(value) = owned {
                    assert_eq!(value.bytes.as_ptr(), pointer);
                }
            }
        }
    }

    /// Arena namespaces, node kinds and dense store boundaries reject distinct
    /// invalid handles.
    #[test]
    fn arena_projections_separate_namespaces_kinds_and_store_bounds() -> Result<(), BuildError>
    {
        let mut meter = BuildMeter::new(BuildLimits::default());
        let mut builder = DocBuilder::try_new(&mut meter)?;
        let text_doc = builder.text(TextSource::from("β𐐀"))?;
        // workflow-gates: allow-escaped-newline
        let verbatim_doc = builder.verbatim(VerbatimSource::from("a\r\n𐐀\n"))?;
        let arena = builder.finish()?;
        let mut foreign_meter = BuildMeter::new(BuildLimits::default());
        let mut foreign_builder = DocBuilder::try_new(&mut foreign_meter)?;
        let foreign_doc = foreign_builder.text(TextSource::from("different"))?;
        let _foreign_arena = foreign_builder.finish()?;
        let count =
            u32::try_from(arena.nodes.len()).map_err(|_error| BuildError::ArithmeticOverflow {
                operation: BuildArithmetic::IdConversion,
            })?;
        for index in [0_u32, count.saturating_sub(1)] {
            let doc = DocId::from_parts(arena.arena, NodeId::from(index));
            assert_eq!(arena.contains(doc), DocHandleStatus::Present);
            assert_eq!(arena.node_id_for(doc), Ok(NodeId::from(index)));
        }
        for doc in [
            foreign_doc,
            DocId::from_parts(arena.arena, NodeId::from(count)),
            DocId::from_parts(arena.arena, NodeId::from(u32::MAX)),
        ] {
            assert_eq!(arena.contains(doc), DocHandleStatus::Absent);
            assert_eq!(arena.node_id_for(doc), Err(BuildError::UnknownDoc));
            assert_eq!(arena.stored_text(doc), Err(BuildError::UnknownDoc));
            assert_eq!(arena.stored_text_width(doc), Err(BuildError::UnknownDoc));
            assert_eq!(arena.stored_verbatim(doc), Err(BuildError::UnknownDoc));
            assert_eq!(arena.verbatim_lines(doc), Err(BuildError::UnknownDoc));
            assert_eq!(arena.flattened_image(doc), Err(BuildError::UnknownDoc));
        }
        assert_eq!(arena.stored_text(verbatim_doc), Err(BuildError::UnknownDoc));
        assert_eq!(
            arena.stored_text_width(verbatim_doc),
            Err(BuildError::UnknownDoc)
        );
        assert_eq!(arena.stored_verbatim(text_doc), Err(BuildError::UnknownDoc));
        assert_eq!(arena.verbatim_lines(text_doc), Err(BuildError::UnknownDoc));
        assert_eq!(
            arena.stored_text(text_doc)?,
            TextOwned::from(String::from("β𐐀"))
        );
        assert_eq!(arena.stored_text_width(text_doc)?, ScalarWidth::from(2_u32));
        assert_eq!(arena.flattened_image(text_doc)?, text_doc);
        let Maybe::Present(DocNode::Text(text_id)) = arena.node(text_doc.node)
        else {
            panic!("text node retained")
        };
        let Maybe::Present(text) = arena.text_identity(text_id)
        else {
            panic!("text identity retained")
        };
        assert_eq!(text.as_ref(), "β𐐀");
        let Maybe::Present(DocNode::Verbatim(verbatim_id)) = arena.node(verbatim_doc.node)
        else {
            panic!("verbatim node retained")
        };
        let Maybe::Present(verbatim) = arena.verbatim_identity(verbatim_id)
        else {
            panic!("verbatim identity retained")
        };
        // workflow-gates: allow-escaped-newline
        assert_eq!(verbatim.as_ref(), "a\r\n𐐀\n");
        assert_eq!(
            arena.verbatim_lines(verbatim_doc)?.as_slice(),
            verbatim.lines()
        );
        assert_eq!(
            arena.stored_verbatim(verbatim_doc)?,
            VerbatimOwned::from(String::from(verbatim.as_ref()))
        );
        assert_eq!(
            arena.flattened_node(text_doc.node),
            Maybe::Present(text_doc.node)
        );
        for index in [count, u32::MAX] {
            assert_eq!(
                arena.node(NodeId::from(index)),
                Maybe::Absent(stored::Absent::OutOfRange)
            );
            assert_eq!(
                arena.flattened_node(NodeId::from(index)),
                Maybe::Absent(stored::Absent::OutOfRange)
            );
        }
        for index in [
            u32::try_from(arena.texts.len()).map_err(|_error| BuildError::ArithmeticOverflow {
                operation: BuildArithmetic::IdConversion,
            })?,
            u32::MAX,
        ] {
            assert_eq!(
                arena.text_identity(TextId::from(index)),
                Maybe::Absent(stored::Absent::OutOfRange)
            );
        }
        for index in [
            u32::try_from(arena.verbatim.len()).map_err(|_error| {
                BuildError::ArithmeticOverflow {
                    operation: BuildArithmetic::IdConversion,
                }
            })?,
            u32::MAX,
        ] {
            assert_eq!(
                arena.verbatim_identity(VerbatimId::from(index)),
                Maybe::Absent(stored::Absent::OutOfRange)
            );
        }
        Ok(())
    }
}
