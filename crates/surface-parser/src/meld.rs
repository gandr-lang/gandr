//! The melder: a resumable, first-order push machine over the checked PBG.
//!
//! `push` is the primary API and is **total**: every molded tile drives exactly
//! one of the three push rules of Moon et al., "Syntactic Completions with
//! Material Obligations" (PACMPL 9, OOPSLA2, 2025), Fig. 29 —
//!
//! * **Shift** (head `⋖`/`≐` τ): push τ; it enters the exposed slot.
//! * **Reduce** (head `⋗` τ): reduce the handle into a meld, propagate up,
//!   retry.
//! * **Degrout** (incomparable): complete-and-reduce the head level with grout,
//!   deferring the comparison down the slope; guaranteed to conclude at Shift
//!   because grout sits at `⊥`, comparable to everything.
//!
//! Incomparable precedences **within one sort** classify as
//! [`Oblig::AmbiguousPrec`] at maximum severity
//! (ambiguity is an error, but the tree stays total — parse totally,
//! classify, let lowering decide). Cross-sort transitions route through grout.
//!
//! The stack is a single `Vec`-backed slope of terraces with O(1) access at
//! both ends (`Vec::first`/`Vec::last`/`push`/`pop`) and no ambient state — the
//! edit-state readiness constraint. Emission is an **append-only log**
//! replayed into the `gandr-surface-syntax` [`TreeBuilder`] at `commit`; a
//! [`Checkpoint`] records the log length and the (small, first-order) slope, so
//! rollback is log truncation and checkpoints are cheap and serializable.

use alloc::boxed::Box;
use alloc::string::String;
use alloc::vec::Vec;
use core::error::Error;
use core::fmt;

use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::Sort;
use gandr_surface_grammar::StepSym;
use gandr_surface_grammar::TileLabel;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::ClosingClass;
use gandr_surface_syntax::GrammarFingerprint;
use gandr_surface_syntax::GroutShape;
use gandr_surface_syntax::GroutSort;
use gandr_surface_syntax::MoldId;
use gandr_surface_syntax::NodeLabel;
use gandr_surface_syntax::SourceText;
use gandr_surface_syntax::StagedId;
use gandr_surface_syntax::SyntaxError;
use gandr_surface_syntax::SyntaxTree;
use gandr_surface_syntax::TreeBuilder;
use gandr_theory_graphs::Assoc;
use gandr_theory_graphs::Bound;
use gandr_theory_graphs::Dir;
use gandr_theory_graphs::Prec;
use gandr_theory_graphs::PrecIndex;

use crate::oblig::Delta;
use crate::oblig::Oblig;
use crate::oblig::ObligationInstance;

/// Define a transparent copyable newtype over a primitive payload.
///
/// The generated struct derives the standard value-semantics traits and
/// converts freely both ways with the payload, plus `Not` for boolean-shaped
/// flags; construction stays literal so constant tables can name the wrapper.
macro_rules! primitive_copy_wrapper {
    ($(#[$meta:meta])* $vis:vis struct $name:ident($inner:ty);) => {
        $(#[$meta])*
        #[repr(transparent)]
        #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
        $vis struct $name($inner);

        impl From<$inner> for $name
        {
            /// Wrap the payload.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            fn from(value: $inner) -> Self
            {
                Self(value)
            }
        }

        impl From<$name> for $inner
        {
            /// Read the payload back.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            fn from(value: $name) -> Self
            {
                value.0
            }
        }

        impl core::ops::Not for $name
        {
            type Output = Self;

            /// Negate the payload.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            fn not(self) -> Self::Output
            {
                Self(!self.0)
            }
        }
    };
}
pub(crate) use primitive_copy_wrapper;

/// Define a transparent newtype over borrowed source text.
///
/// The generated struct carries a `&'text str`, derives the standard
/// value-semantics traits, and converts freely both ways with the borrowed
/// text so lexing code can pass either shape without re-slicing.
macro_rules! borrowed_str_wrapper {
    ($(#[$meta:meta])* $vis:vis struct $name:ident;) => {
        $(#[$meta])*
        #[repr(transparent)]
        #[derive(Clone, Copy, Debug, Eq, PartialEq)]
        $vis struct $name<'text>(&'text str);

        impl<'text> From<&'text str> for $name<'text>
        {
            /// Adopt borrowed text.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            fn from(value: &'text str) -> Self
            {
                Self(value)
            }
        }

        impl<'text> From<$name<'text>> for &'text str
        {
            /// Read the borrowed text back.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            fn from(value: $name<'text>) -> Self
            {
                value.0
            }
        }

        impl AsRef<str> for $name<'_>
        {
            /// Borrow the text.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            fn as_ref(&self) -> &str
            {
                self.0
            }
        }
    };
}

borrowed_str_wrapper!(
    /// Borrowed surface text for a molded tile.
    pub struct TileText;
);
borrowed_str_wrapper!(
    /// Borrowed layout text recorded as lossless space.
    pub struct SpaceText;
);
borrowed_str_wrapper!(
    /// Borrowed text appended to the assembled source buffer.
    struct SourceFragment;
);

impl<'text> From<TileText<'text>> for SourceFragment<'text>
{
    /// View a tile's text as text the source buffer appends.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: TileText<'text>) -> Self
    {
        Self(<&str>::from(value))
    }
}

impl<'text> From<SpaceText<'text>> for SourceFragment<'text>
{
    /// View layout text as text the source buffer appends.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: SpaceText<'text>) -> Self
    {
        Self(<&str>::from(value))
    }
}

/// Borrowed candidate-label set for the next lexical token.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CandidateLabels<'labels>(&'labels [&'static str]);

impl<'labels> From<&'labels [&'static str]> for CandidateLabels<'labels>
{
    /// Adopt a borrowed slice of label names as a candidate set.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: &'labels [&'static str]) -> Self
    {
        Self(value)
    }
}

impl<'labels> From<CandidateLabels<'labels>> for &'labels [&'static str]
{
    /// Read the slice of label names back.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: CandidateLabels<'labels>) -> Self
    {
        value.0
    }
}

primitive_copy_wrapper!(
    /// Source-buffer byte offset.
    struct SourceOffset(u32);
);

impl SourceOffset
{
    /// The same offset in the tree's byte frame.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the offset's value, widened; a host whose pointer is narrower
    ///   than 32 bits saturates rather than wraps.
    /// - panics: none.
    #[inline]
    fn byte_offset(self) -> ByteOffset
    {
        ByteOffset::from(usize::try_from(self.0).unwrap_or(usize::MAX))
    }
}

/// Source-buffer span with an inclusive start and exclusive end.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct SourceSpan
{
    /// First byte of the span.
    start: SourceOffset,
    /// One past the last byte of the span.
    end: SourceOffset,
}

impl SourceSpan
{
    /// Build the half-open span `[start, end)`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    const fn new(
        start: SourceOffset,
        end: SourceOffset,
    ) -> Self
    {
        Self { start, end }
    }

    /// Build the empty span at `offset`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    const fn point(offset: SourceOffset) -> Self
    {
        Self {
            start: offset,
            end: offset,
        }
    }

    /// The same span in the tree's byte frame.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the span with the same endpoints.
    /// - fails: an inverted span, which the melder never builds.
    /// - panics: none.
    ///
    /// # Errors
    /// [`SyntaxError::InvertedSpan`] when `start` lies past `end`.
    #[inline]
    fn byte_span(self) -> Result<ByteSpan, SyntaxError>
    {
        ByteSpan::new(self.start.byte_offset(), self.end.byte_offset())
    }
}

primitive_copy_wrapper!(
    /// Index into the melder slope stack.
    struct StackIndex(usize);
);
primitive_copy_wrapper!(
    /// Lowest stack index a collapse pass may reduce.
    struct StackFloor(usize);
);
primitive_copy_wrapper!(
    /// Index of an open form frontier.
    struct FrontierIndex(usize);
);
primitive_copy_wrapper!(
    /// Index of an operator cell.
    struct OperatorIndex(usize);
);

impl From<StackIndex> for StackFloor
{
    /// Take a slope index as a collapse floor.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: StackIndex) -> Self
    {
        Self(usize::from(value))
    }
}

impl From<FrontierIndex> for StackIndex
{
    /// View a frontier position as a slope index.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: FrontierIndex) -> Self
    {
        Self(usize::from(value))
    }
}

impl From<StackIndex> for FrontierIndex
{
    /// Name a slope index as a form frontier.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: StackIndex) -> Self
    {
        Self(usize::from(value))
    }
}

impl From<OperatorIndex> for StackIndex
{
    /// View an operator position as a slope index.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: OperatorIndex) -> Self
    {
        Self(usize::from(value))
    }
}

impl From<StackIndex> for OperatorIndex
{
    /// Name a slope index as an operator position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: StackIndex) -> Self
    {
        Self(usize::from(value))
    }
}

impl StackIndex
{
    /// Return the index above this one, or `None` at the `usize` ceiling.
    ///
    /// # Specification
    /// - ensures: returns the successor index when it is representable.
    /// - fails: returns `None` on `usize::MAX` overflow rather than panicking.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the successor is taken on every form continuation;
    ///   the ceiling arm is unreachable because slope indices stay far below
    ///   `usize::MAX`.
    /// - witness: `tests::acceptance::corpus_parses_totally`
    #[inline]
    fn next(self) -> Option<Self>
    {
        usize::from(self).checked_add(1).map(Self::from)
    }

    /// Return the collapse floor above this index, or `None` at the ceiling.
    ///
    /// # Specification
    /// - ensures: returns the [`StackFloor`] above this index when the
    ///   successor is representable.
    /// - fails: returns `None` on `usize::MAX` overflow rather than panicking.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the floor is consumed by form continuation collapse;
    ///   the ceiling arm is unreachable because slope indices stay far below
    ///   `usize::MAX`.
    /// - witness: `tests::acceptance::corpus_parses_totally`
    #[inline]
    fn floor_after(self) -> Option<StackFloor>
    {
        self.next().map(StackFloor::from)
    }
}

/// Half-open stack range `[low, high_exclusive)`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct StackRange
{
    /// First stack index in the range.
    low: StackIndex,
    /// One past the last stack index in the range.
    high_exclusive: StackIndex,
}

impl StackRange
{
    /// Build the half-open stack range `[low, high_exclusive)`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    const fn new(
        low: StackIndex,
        high_exclusive: StackIndex,
    ) -> Self
    {
        Self {
            low,
            high_exclusive,
        }
    }
}

primitive_copy_wrapper!(
    /// Whether a form tile is open.
    struct FormOpen(bool);
);
primitive_copy_wrapper!(
    /// Whether a form-start absorbs the operand to its left.
    struct AbsorbsLeft(bool);
);
primitive_copy_wrapper!(
    /// Whether a form continuation tile is a form end.
    struct FormEndTile(bool);
);
primitive_copy_wrapper!(
    /// Whether a mold has a same-form predecessor.
    struct MoldHasPredecessor(bool);
);
primitive_copy_wrapper!(
    /// Whether a mold has a same-form successor.
    struct MoldHasSuccessor(bool);
);
primitive_copy_wrapper!(
    /// Whether a mold can start a form.
    struct FormFirstMembership(bool);
);
primitive_copy_wrapper!(
    /// Whether a mold can finish a nullable-tail form.
    struct FormLastMembership(bool);
);
primitive_copy_wrapper!(
    /// Whether a required-tail frontier's tail is one form already under way.
    struct TailUnderWay(bool);
);
primitive_copy_wrapper!(
    /// Whether an incoming tile continues a required-tail form's tail.
    struct TailExtension(bool);
);
primitive_copy_wrapper!(
    /// Whether a required-tail frontier's tail is a whole operand run.
    struct TailWhole(bool);
);
primitive_copy_wrapper!(
    /// Whether a mold would continue the nearest open form.
    pub struct FormContinuation(bool);
);
primitive_copy_wrapper!(
    /// Whether a mold is admissible at the current frontier.
    pub struct MoldAdmissibility(bool);
);
primitive_copy_wrapper!(
    /// Whether the slope has an open form.
    pub struct OpenFormPresence(bool);
);
primitive_copy_wrapper!(
    /// Whether a mold extends the head operand.
    pub struct OperandContinuation(bool);
);
primitive_copy_wrapper!(
    /// Whether the stack head is an operand.
    pub struct HeadOperandPresence(bool);
);
primitive_copy_wrapper!(
    /// Whether a mold's sort fits the expected slot.
    struct SortAdmissibility(bool);
);
primitive_copy_wrapper!(
    /// Whether two molds are same-form adjacent.
    struct SameFormAdjacency(bool);
);
primitive_copy_wrapper!(
    /// Whether a successor mold has one of the candidate token labels.
    struct SuccessorLabelPresence(bool);
);
primitive_copy_wrapper!(
    /// Whether a grammar sort is an item position.
    struct ItemPosition(bool);
);
primitive_copy_wrapper!(
    /// Whether a mold can open an item-position declaration at a fresh slot.
    struct DeclarationStart(bool);
);
primitive_copy_wrapper!(
    /// Whether a stack cell is an operand.
    struct OperandPresence(bool);
);
primitive_copy_wrapper!(
    /// Whether a completion is empty.
    pub struct CompletionStatus(bool);
);

/// One reducible head action selected by the collapse worklist.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum CollapseStep
{
    /// Reduce an unsaturated operator cell.
    ReduceOperator(OperatorIndex),
    /// Force-close an open form frontier.
    ForceCloseForm(FrontierIndex),
}

/// What arrives after a required-tail form's tail: the tile being pushed,
/// or a token whose mold the molder has yet to choose.
#[derive(Clone, Copy, Debug)]
enum Incoming<'labels>
{
    /// The molded tile `push` is about to place.
    Tile(MoldId),
    /// The labels of the token the molder is about to gather.
    Token(CandidateLabels<'labels>),
}
primitive_copy_wrapper!(
    /// One checkpoint wire byte.
    struct WireByte(u8);
);
primitive_copy_wrapper!(
    /// Checkpoint wire `u16`.
    struct WireU16(u16);
);
primitive_copy_wrapper!(
    /// Checkpoint wire `u32`.
    struct WireU32(u32);
);
primitive_copy_wrapper!(
    /// Checkpoint wire `u64`.
    struct WireU64(u64);
);
primitive_copy_wrapper!(
    /// Count encoded in a checkpoint.
    struct CheckpointCount(usize);
);
primitive_copy_wrapper!(
    /// Count of bytes read from a checkpoint.
    struct ByteCount(usize);
);

/// Owned checkpoint byte stream.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct CheckpointBytes
{
    /// Encoded checkpoint payload, laid out per the checkpoint wire format.
    bytes: Vec<u8>,
}

impl From<Vec<u8>> for CheckpointBytes
{
    /// Adopt a serialized checkpoint buffer.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: Vec<u8>) -> Self
    {
        Self { bytes: value }
    }
}

impl From<CheckpointBytes> for Vec<u8>
{
    /// Release the serialized buffer.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: CheckpointBytes) -> Self
    {
        value.bytes
    }
}

impl AsRef<[u8]> for CheckpointBytes
{
    /// Borrow the serialized bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &[u8]
    {
        &self.bytes
    }
}

/// Borrowed checkpoint byte stream.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CheckpointBytesRef<'bytes>(&'bytes [u8]);

impl<'bytes> From<&'bytes [u8]> for CheckpointBytesRef<'bytes>
{
    /// Borrow serialized bytes for decoding.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: &'bytes [u8]) -> Self
    {
        Self(value)
    }
}

impl<'bytes> From<&'bytes CheckpointBytes> for CheckpointBytesRef<'bytes>
{
    /// Borrow an owned checkpoint buffer for decoding.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: &'bytes CheckpointBytes) -> Self
    {
        Self(value.as_ref())
    }
}

impl AsRef<[u8]> for CheckpointBytesRef<'_>
{
    /// Borrow the serialized bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &[u8]
    {
        self.0
    }
}

/// Borrowed bytes returned by the checkpoint reader.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ByteChunk<'bytes>(&'bytes [u8]);

impl<'bytes> From<&'bytes [u8]> for ByteChunk<'bytes>
{
    /// Wrap a borrowed wire chunk.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: &'bytes [u8]) -> Self
    {
        Self(value)
    }
}

impl<'bytes> From<ByteChunk<'bytes>> for &'bytes [u8]
{
    /// Read the borrowed chunk back.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: ByteChunk<'bytes>) -> Self
    {
        value.0
    }
}

impl AsRef<[u8]> for ByteChunk<'_>
{
    /// Borrow the chunk's bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &[u8]
    {
        self.0
    }
}
/// A tile that has already been assigned a mold, ready to push.
///
/// The molder produces these from labeled tokens; a caller driving the melder
/// directly synthesizes them from the real PBG mold table. The tile carries
/// its interned
/// [`MoldId`] and its surface text; the melder appends the text to its
/// assembled source buffer and records the span.
///
/// # Specification
/// - requires: `mold` indexes the mold table of the grammar the [`MeldState`]
///   was built over; `text` is the tile's exact surface bytes.
/// - ensures: preserves `mold` and `text` exactly.
/// - provides: the unit of input to [`MeldState::push`].
/// - fails: never; an out-of-range `mold` is handled totally by `push` as an
///   [`Oblig::UnmoldedTok`].
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L1 — a two-field record; retention is witnessed at the push
///   seam.
/// - witness: `meld::tests::single_atom_commits_to_one_token`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MoldedTile
{
    /// The interned mold assigned to the tile.
    mold: MoldId,
    /// The tile's exact surface text.
    text: Box<str>,
}

impl MoldedTile
{
    /// Construct a molded tile from its mold and surface text.
    ///
    /// # Specification
    /// - requires: `mold` indexes the melder's grammar; `text` is the surface.
    /// - ensures: preserves both exactly.
    /// - provides: the caller's tile constructor.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — direct field initialization.
    /// - witness: `meld::tests::single_atom_commits_to_one_token`
    #[inline]
    #[must_use]
    pub fn new(
        mold: MoldId,
        text: TileText<'_>,
    ) -> Self
    {
        Self {
            mold,
            text: Box::from(<&str>::from(text)),
        }
    }

    /// Return the tile's mold.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn mold(&self) -> MoldId
    {
        self.mold
    }

    /// Return the tile's surface text.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn text(&self) -> TileText<'_>
    {
        TileText::from(self.text.as_ref())
    }
}

/// A dense id into the melder's append-only emission log.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct EmitId(u32);

/// One append-only emission-log entry (replayed into the tree at commit).
#[derive(Clone, Debug, Eq, PartialEq)]
enum EmitOp
{
    /// A leaf: a tile, a grout, a minted close, or layout space.
    Token
    {
        /// What the leaf is.
        label: NodeLabel,
        /// Inclusive source start.
        start: u32,
        /// Exclusive source end.
        end: u32,
    },
    /// An interior node owning already-emitted children: a meld or the root.
    Interior
    {
        /// What the interior is.
        label: NodeLabel,
        /// Inclusive source start.
        start: u32,
        /// Exclusive source end.
        end: u32,
        /// The interior's children, in source order.
        children: Vec<EmitId>,
    },
}

/// The operator shape of a shifted tile, derived from its precedence bounds.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum OpShape
{
    /// Faces a sort hole on the right only (e.g. unary `-`, `if`).
    Prefix,
    /// Faces a sort hole on both sides (an infix operator).
    Infix,
    /// Faces a sort hole on the left only (e.g. a projection tail).
    Postfix,
}

/// The role of a stack cell in the slope.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Role
{
    /// A completed subtree filling a slot (a "kid").
    Operand,
    /// A shifted tile of a multi-tile form, joined to its neighbours by the
    /// same-form `≐` adjacency (paper Fig. 15's equal face). Brackets are the
    /// special case where the opener and closer are directly `≐`-adjacent.
    FormTile
    {
        /// The tile's mold, for `≐`-successor lookup.
        mold: MoldId,
        /// The producing form's sort.
        sort: Sort,
        /// Whether this is the form's open frontier (awaiting a continuation).
        open: bool,
        /// Whether this tile opened the form (a form-start).
        start: bool,
        /// Whether a form-start absorbs the preceding operand (a left-bounded
        /// start such as a call `(` or a projection `.`).
        absorb_left: bool,
    },
    /// A shifted operator awaiting completion.
    Operator
    {
        /// The operator's mold.
        mold: MoldId,
        /// The operator's form-group precedence.
        prec: Prec,
        /// The producing form's sort.
        sort: Sort,
        /// The operator's shape.
        shape: OpShape,
    },
}

/// One terrace of the slope: an emitted subtree plus its role.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Cell
{
    /// The emission-log id of this cell's subtree or tile.
    emit: EmitId,
    /// Inclusive source start.
    start: u32,
    /// Exclusive source end.
    end: u32,
    /// The subtree's sort.
    sort: Sort,
    /// The cell's slope role.
    role: Role,
}

/// The classification of an incoming molded tile.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Kind
{
    /// A complete operand (no holes on either side, no `≐` neighbours).
    Operand,
    /// An operator of the given shape (single-tile form, no `≐` neighbours).
    Operator(OpShape),
    /// The opening tile of a multi-tile form (`≐`-successor, no predecessor).
    FormStart
    {
        /// Whether the start absorbs the preceding operand (left-bounded).
        absorb_left: bool,
    },
    /// A middle tile of a multi-tile form (`≐`-predecessor and successor).
    FormMid,
    /// The closing tile of a multi-tile form (`≐`-predecessor, no successor).
    FormEnd,
}

/// The operator-precedence relation between the stack head and an incoming
/// tile.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Rel
{
    /// `head ⋖ τ`: shift (τ enters the head's open slot).
    Yields,
    /// `head ≐ τ`: shift (same-form continuation).
    Match,
    /// `head ⋗ τ`: reduce the head handle.
    Takes,
    /// Same-sort, precedence-incomparable: `AmbiguousPrec` at maximum severity.
    Ambiguous,
    /// Different sorts: route through grout (Degrout).
    CrossSort,
}

/// The precomputed same-form `≐`-membership table, derived from `Pbg`
/// The form-membership queries over the checked PBG's `≐` relation.
///
/// A tile mold participates in a multi-tile form when it has a `≐`-predecessor,
/// a `≐`-successor, or both (paper Fig. 15's equal face; `Pbg::adjacencies`).
/// The four roles fall out of the pair of flags: a **start** has a successor
/// but no predecessor (`def`, `(`, an opening `"`); an **end** has a
/// predecessor but no successor (`;`, `)`, a closing `"`); a **middle** has
/// both (`=`, `else`, a repeated `,`); and everything else is a single-tile
/// operator or a bare operand. The actual `≐` between two molds is checked
/// against the sorted adjacency relation directly ([`MeldState::adjacent`]).
///
/// Membership itself lives in the grammar: [`Pbg::mold_has_predecessor`] and
/// [`Pbg::mold_has_successor`] read dense flags derived at table build, and
/// the form-first/form-last tests binary-search the stored sorted lists. This
/// facade carries no state — the per-parse (and per-restore) rebuild of four
/// `BTreeSet<MoldId>` membership sets it replaced cost O(adjacencies) tree
/// inserts on every parse.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
struct FormTable;

impl FormTable
{
    /// Return whether `mold` has a same-form `≐`-predecessor.
    ///
    /// # Specification
    /// trivial.
    fn has_pred(
        pbg: &Pbg,
        mold: MoldId,
    ) -> MoldHasPredecessor
    {
        MoldHasPredecessor::from(bool::from(pbg.mold_has_predecessor(mold)))
    }

    /// Return whether `mold` has a same-form `≐`-successor.
    ///
    /// # Specification
    /// trivial.
    fn has_succ(
        pbg: &Pbg,
        mold: MoldId,
    ) -> MoldHasSuccessor
    {
        MoldHasSuccessor::from(bool::from(pbg.mold_has_successor(mold)))
    }

    /// Return whether `mold` can be a form's first tile (its FIRST set).
    ///
    /// # Specification
    /// trivial.
    fn is_form_first(
        pbg: &Pbg,
        mold: MoldId,
    ) -> FormFirstMembership
    {
        FormFirstMembership::from(bool::from(pbg.mold_is_form_first(mold)))
    }

    /// Return whether `mold` can be a form's last tile (its LAST set) — a
    /// completable frontier whose remaining form tail is nullable.
    ///
    /// # Specification
    /// trivial.
    fn is_form_last(
        pbg: &Pbg,
        mold: MoldId,
    ) -> FormLastMembership
    {
        FormLastMembership::from(bool::from(pbg.mold_is_form_last(mold)))
    }
}

/// Return whether `sort` is an **item position** — a slot whose residents are
/// declarations rather than values.
///
/// Two sorts qualify, and the second is why this is a function rather than an
/// equality. [`Sort::Item`] is the file's own top level. [`Sort::ModuleMember`]
/// is a module body, which holds its members *by reference* so that nesting
/// costs one rule instead of one copy per admitted level — members are forms in
/// their own right there, not tiles of the enclosing declaration.
///
/// Both are positions where an open form legitimately reaches past a fresh
/// declaration head and takes it as a member, which is exactly the case a
/// boundary repair must not fire on.
///
/// # Specification
/// trivial.
#[inline]
#[must_use]
const fn is_item_position(sort: Sort) -> ItemPosition
{
    ItemPosition(matches!(sort, Sort::Item | Sort::ModuleMember))
}

/// A resumable, first-order push machine over a checked PBG.
///
/// See the module docs for the three push rules and the append-only emission
/// model. `MeldState` holds no ambient state: the slope, the emission log, the
/// obligation buffer, and the assembled source are the whole state (P2), so a
/// [`Checkpoint`] is a faithful, serializable snapshot.
///
/// # Specification
/// - requires: `pbg` outlives the state; all pushed [`MoldedTile`] molds index
///   `pbg`'s table (out-of-range molds are handled totally).
/// - ensures: [`push`](MeldState::push) is total and never panics; the slope
///   stays well-formed; [`commit`](MeldState::commit) yields a well-formed
///   [`SyntaxTree`] recording `pbg`'s fingerprint.
/// - provides: the streaming push surface plus non-destructive
///   [`finalize`](MeldState::finalize) and
///   [`obligations`](MeldState::obligations) queries and
///   [`checkpoint`](MeldState::checkpoint)/[`resume`](MeldState::resume).
/// - fails: only [`commit`](MeldState::commit) is fallible, returning
///   [`MeldError`] for an arena-construction failure.
/// - panics: none.
/// - intension: the slope is a `Vec` processed with checked arithmetic;
///   emission is append-only; obligations accumulate in buffer order.
///
/// # Adequacy
/// - hypothesis: L3 — totality over arbitrary molds, the three-rule traces,
///   resume-equivalence, and finalize non-destructiveness each exercise a
///   distinct behavior.
/// - witness: `meld::tests::single_atom_commits_to_one_token`
/// - witness: `meld::tests::degrout_flags_one_ambiguous_prec_at_the_smallest_span`
pub struct MeldState<'pbg>
{
    /// The grammar this state melds against.
    pbg: &'pbg Pbg,
    /// The assembled source buffer (grows as tiles are pushed).
    source: String,
    /// The append-only emission log, replayed at commit.
    emit: Vec<EmitOp>,
    /// The slope: a `Vec`-backed sequence of terraces, base at index zero.
    stack: Vec<Cell>,
    /// Ascending indices of the OPEN form-frontier cells on the slope
    /// (`Role::FormTile { open: true }`), the top of a monotone index cache.
    ///
    /// The three index caches (`frontiers` / `operators` / `barriers`) keep the
    /// per-token head queries O(1) instead of O(content-region): a shell block
    /// accumulates its whole interior as juxtaposed operand cells above the
    /// open `#!{` frontier, so the former top-down role scans cost O(atoms) per
    /// token — O(atoms²) per block (the shell-juxtaposition hazard). Every
    /// slope mutation is a top push, a top-reaching splice, or a
    /// frontier-flag flip, so each cache maintains itself with amortized
    /// O(1) pushes/pops and no rescans.
    frontiers: Vec<usize>,
    /// Ascending indices of the operator cells (`Role::Operator`) on the slope.
    operators: Vec<usize>,
    /// Ascending indices of ALL form-tile cells (`Role::FormTile`, open or
    /// closed) on the slope — the scan barriers the operator query stops at.
    barriers: Vec<usize>,
    /// The obligation buffer, in accumulation order.
    obligations: Vec<ObligationInstance>,
    /// Floating layout-space tokens, included as root children at commit for
    /// losslessness (space is skipped by the merkle hash, so tree position is
    /// not identity-bearing).
    spaces: Vec<EmitId>,
}

impl<'pbg> MeldState<'pbg>
{
    /// Create an empty melder at the base boundary `⊣` over `pbg`.
    ///
    /// # Specification
    /// - requires: `pbg` is a checked PBG.
    /// - ensures: returns a state with an empty slope, empty log, empty source,
    ///   and no obligations; the bracket table is precomputed from `pbg`.
    /// - provides: the streaming entry point (`⊣` at the base).
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — direct initialization; the empty commit is witnessed.
    /// - witness: `meld::tests::empty_state_commits_to_a_root`
    #[inline]
    #[must_use]
    pub fn new(pbg: &'pbg Pbg) -> Self
    {
        Self {
            pbg,
            source: String::new(),
            emit: Vec::new(),
            stack: Vec::new(),
            frontiers: Vec::new(),
            operators: Vec::new(),
            barriers: Vec::new(),
            obligations: Vec::new(),
            spaces: Vec::new(),
        }
    }

    /// Push one molded tile through the machine (Shift / Reduce / Degrout).
    ///
    /// This is the unit of totality and of cost accounting: the Shift happy
    /// path performs no per-push heap allocation beyond amortized log/slope
    /// growth, uses interned `u32`
    /// ids throughout, and never compares strings. Reduce and Degrout
    /// amortize buffer reuse.
    ///
    /// # Specification
    /// - requires: none; `tile.mold` may be arbitrary.
    /// - ensures: exactly one push rule fires per tile; the slope stays
    ///   well-formed; any inserted grout records an [`ObligationInstance`]; an
    ///   out-of-range mold is buffered as [`Oblig::UnmoldedTok`].
    /// - provides: the primary streaming input operation; batch parse is the
    ///   derived fold of `push` followed by [`commit`](MeldState::commit).
    /// - fails: never; totally defined on every input.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — Shift, Reduce, Degrout, and the unmolded path are
    ///   each exercised, and totality holds over arbitrary mold sequences.
    /// - witness: `meld::tests::degrout_flags_one_ambiguous_prec_at_the_smallest_span`
    #[inline]
    pub fn push(
        &mut self,
        tile: &MoldedTile,
    )
    {
        let def = match self.pbg.mold(tile.mold) {
            | Ok(def) => *def,
            | Err(_error) => {
                self.push_unmolded(SourceFragment::from(tile.text()));
                return;
            },
        };
        // Settle any completable open frontier (a bare `?` hole) the incoming
        // tile does not continue, so it stands as a complete operand and the
        // incoming tile is a flat sibling, not absorbed into the hole meld.
        self.settle_completable(tile.mold);
        // A prefix form may have an optional tile-bearing branch followed by a
        // required sort hole. It cannot close before that operand arrives, but
        // once its tail is whole it is a complete form even without a terminal
        // tile, unless this tile continues the tail.
        self.settle_filled_required_tail(Incoming::Tile(tile.mold));
        let span = self.append_source(SourceFragment::from(tile.text()));
        let tile_emit = self.emit_token(NodeLabel::Tile(tile.mold), span);
        let cell = Cell {
            emit: tile_emit,
            start: u32::from(span.start),
            end: u32::from(span.end),
            sort: def.sort,
            role: Role::Operand,
        };

        match self.classify(tile.mold) {
            | Kind::FormStart { absorb_left } => {
                self.open_form(tile.mold, def.sort, cell, AbsorbsLeft::from(absorb_left));
            },
            | Kind::FormMid => {
                self.continue_form(tile.mold, def.sort, cell, FormEndTile::from(false));
            },
            | Kind::FormEnd => {
                self.continue_form(tile.mold, def.sort, cell, FormEndTile::from(true));
            },
            | Kind::Operand => {
                self.reduce_toward(def.sort, def.prec, tile.mold, span);
                self.push_cell(cell);
            },
            | Kind::Operator(shape) => {
                self.reduce_toward(def.sort, def.prec, tile.mold, span);
                self.push_cell(Cell {
                    role: Role::Operator {
                        mold: tile.mold,
                        prec: def.prec,
                        sort: def.sort,
                        shape,
                    },
                    ..cell
                });
            },
        }
    }

    /// Return whether `mold` would `≐`-continue the topmost open form frontier.
    ///
    /// The molder prefers a continuing tile over a fresh atom/form when their
    /// obligation deltas tie: continuation keeps the open form progressing
    /// toward its end, which a bare atom in the same slot does not
    /// (minimization). A pure query — it never mutates the slope.
    ///
    /// # Specification
    /// - requires: none.
    /// - ensures: returns `true` exactly when a top open frontier exists and
    ///   `(frontier_mold, mold)` is a `≐` adjacency; leaves `self` unchanged.
    /// - provides: the molder's continuation-preference key.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a continuing tile and a non-continuing atom over the
    ///   same open form distinguish the query.
    /// - witness: `tests::acceptance::corpus_molds_to_zero_obligations`
    #[inline]
    #[must_use]
    pub fn would_continue_form(
        &self,
        mold: MoldId,
    ) -> FormContinuation
    {
        let Some(frontier) = self.nearest_open_form()
        else {
            return FormContinuation::from(false);
        };
        let Some(Role::FormTile {
            mold: head_mold, ..
        }) = self
            .stack
            .get(usize::from(StackIndex::from(frontier)))
            .map(|cell| cell.role)
        else {
            return FormContinuation::from(false);
        };
        FormContinuation::from(bool::from(self.adjacent(head_mold, mold)))
    }

    /// Return whether pushing `mold` is structurally admissible at the head.
    ///
    /// This is the candidate pre-filter: the molder discards inadmissible
    /// candidates **before** any dry-run, so the wide identifier / quote menus
    /// collapse to a handful and
    /// the greedy molder never commits a form-continuation tile (a closing `"`,
    /// a stray `=`/`;`/`)`) that has no matching open frontier. Admissibility
    /// mirrors what [`push`](MeldState::push) would do:
    ///
    /// * A form-end (`≐`-closing tile) is admissible only when it `≐`-continues
    ///   the nearest open form frontier — otherwise `push` would flag a
    ///   [`Oblig::MissingTile`] (a stray end with no opener).
    /// * A form-mid is admissible when it `≐`-continues the nearest open
    ///   frontier **or** it can be a form's first tile ([`Pbg::form_first`])
    ///   and no form is open at all — a form-mid whose only predecessor is a
    ///   nullable prefix (a `def` behind an optional `@[…]` attribute block) is
    ///   a legitimate form-start at a fresh position, which `push`'s stray-mid
    ///   path opens without an obligation; a genuine mid (`=`, `,`) — or a
    ///   deep-nested tile like an `extern` body's `def`, which is not in any
    ///   form's FIRST set — stays rejected where it cannot continue an open
    ///   frontier.
    /// * A left-bounded form-start (a call `(`, a projection `.`) and an infix
    ///   / postfix operator are admissible only with a left operand at the head
    ///   — otherwise `push` would flag a [`Oblig::MissingMeld`].
    /// * A fresh atom, a non-absorbing form-start, and a prefix operator are
    ///   always admissible; sort disagreement is a ranking, not an
    ///   admissibility, concern (see
    ///   [`expected_operand_sort`](MeldState::expected_operand_sort)).
    ///
    /// A pure query — it never mutates the slope. An out-of-range mold is
    /// admissible (it takes `push`'s total unmolded path), so the pre-filter
    /// never removes the last resort.
    ///
    /// # Specification
    /// - requires: none.
    /// - ensures: returns whether `push`ing `mold` avoids an immediately-forced
    ///   structural obligation; leaves `self` unchanged.
    /// - provides: the molder's per-candidate admissibility gate.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a closing `"` with no open string, a wide-menu
    ///   identifier at operand position, and a continuing form-mid distinguish
    ///   the gate.
    /// - witness: `meld::tests::admits_rejects_a_stray_closer`
    /// - witness: `tests::acceptance::corpus_molds_to_zero_obligations`
    #[inline]
    #[must_use]
    pub fn admits(
        &self,
        mold: MoldId,
    ) -> MoldAdmissibility
    {
        self.admits_at(mold, &self.admissibility_frontier())
    }

    /// Return the nearest open form frontier's mold, if any.
    ///
    /// The molder gathers the open form's `≐`-successors alongside the
    /// fresh-slot menu, so an identifier filling a hole inside an open
    /// block still gathers its two atoms (not the ~130-mold full menu)
    /// while the form's own next tile stays reachable.
    ///
    /// # Specification
    /// - requires: none.
    /// - ensures: returns the nearest open form frontier's mold; leaves `self`
    ///   unchanged.
    /// - provides: the molder's open-form successor source.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a fresh slot (no open mold) and an open bracket
    ///   interior distinguish the result.
    /// - witness: `tests::acceptance::corpus_parses_totally`
    #[inline]
    #[must_use]
    pub fn open_form_mold(&self) -> Option<MoldId>
    {
        let index = self.nearest_open_form()?;
        match self.stack.get(usize::from(index)).map(|cell| cell.role) {
            | Some(Role::FormTile { mold, .. }) => Some(mold),
            | _ => None,
        }
    }

    /// The head context the pre-filter reads: the nearest open form frontier's
    /// mold and whether the slope head is an operand.
    ///
    /// Both are `O(slope depth)` to compute but constant across a whole token's
    /// candidate menu, so the molder computes this **once** and reuses it for
    /// every candidate ([`admits_at`](MeldState::admits_at)) — the difference
    /// between an `O(menu × depth)` and an `O(menu + depth)` per-token cost
    /// that keeps a wide (125-candidate `identifier`) menu inside the batch
    /// budget.
    ///
    /// # Specification
    /// - requires: none.
    /// - ensures: returns the nearest open frontier mold (if any), the
    ///   head-is-operand flag, the head operand sort, and the expected slot
    ///   sort; leaves `self` unchanged.
    /// - provides: the hoisted admissibility context.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — a projection of the slope head; witnessed through
    ///   [`admits`](MeldState::admits) which consumes it.
    /// - witness: `meld::tests::admits_a_form_first_mid_at_a_fresh_slot`
    #[inline]
    #[must_use]
    pub fn admissibility_frontier(&self) -> Frontier
    {
        let open = self.open_form_mold();
        Frontier {
            open,
            head_operand: self.head_is_operand(),
            head_sort: self.head_operand_sort(),
            expected: self.expected_operand_sort(),
        }
    }

    /// Return whether any form is open on the slope (a form frontier awaiting a
    /// continuation).
    ///
    /// The molder gathers only the fresh-slot candidate menu
    /// ([`Pbg::fresh_candidates`](gandr_surface_grammar::Pbg::fresh_candidates)) when
    /// no form is open — the overwhelmingly common case — collapsing the
    /// wide `identifier` menu to its atoms before the admissibility loop
    /// even runs.
    ///
    /// # Specification
    /// - requires: none.
    /// - ensures: returns whether the slope has an open form frontier; leaves
    ///   `self` unchanged.
    /// - provides: the molder's fresh-menu gate.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a fresh top-level slot and an open bracket interior
    ///   distinguish the flag.
    /// - witness: `tests::acceptance::corpus_parses_totally`
    #[inline]
    #[must_use]
    pub fn has_open_form(&self) -> OpenFormPresence
    {
        OpenFormPresence::from(self.nearest_open_form().is_some())
    }
    /// Close an unfinished declaration before a fresh declaration head is
    /// pushed.
    ///
    /// The damage this settles is an **unclosed value or type delimiter** — the
    /// `def bad = ( 1 ;` shape — whose ghost end would otherwise be appended
    /// wherever the form finally closes, at end of input, swallowing every
    /// later declaration into the one that opened the delimiter. Collapsing at
    /// the boundary puts the ghost inside the damaged declaration instead, so
    /// the next declaration is a distinct item and the obligation stays local.
    ///
    /// The trigger is a **declaration head**, not the `def` keyword: any mold
    /// that can open an item-position form at a fresh slot
    /// ([`Self::opens_declaration`]) marks the boundary, so `data`, `codata`,
    /// `module`, `sign`, `import`, `op`, `rec`, `extern`, the `@` attribute
    /// block, and the keyword-led statement heads all bound a repair exactly as
    /// `def` does. The damaged declaration and the surviving one need not be
    /// the same family.
    ///
    /// Two guards keep the widened trigger from firing on well-formed source,
    /// and both are load-bearing:
    ///
    /// - **No candidate may continue the open frontier.** The molder gathers
    ///   every mold sharing the token's label, across every rule context, and
    ///   only one of them will be chosen — so a decision taken per candidate
    ///   acts on readings that lose. A `sign` block's `rule c : ( … data x :
    ///   Nat … )` member holds a `data` tile inside an open `(`, where the
    ///   *declaration* `data` mold continues nothing and the *member* `data`
    ///   mold continues the `(` frontier. Sixteen corpus files depend on the
    ///   member reading, so the whole candidate set has to agree that nothing
    ///   continues before anything is force-closed.
    /// - **The innermost open form must not be [`Sort::Item`].** An open item
    ///   form legitimately reaches past this point: a container (`module`,
    ///   `data`, `sign`) holds the next head as a **member** of its own rule,
    ///   and a declaration whose own frontier is innermost has no interior
    ///   damage to bound. Only a non-item frontier is unfinished value syntax.
    ///
    /// The floor is the nearest open frontier whose form **starts** at a
    /// declaration head, so a declaration opened inside an enclosing form's
    /// content region closes without closing that form; with no such frontier
    /// the floor is the slope base.
    ///
    /// Known bound: a container whose own member carries the damage — the
    /// `module M { def bad = ( 1 ; def good = 2; }` shape — force-closes the
    /// container too, so `good` is emitted as a sibling of `M` rather than a
    /// member of it. The member is tiles of the container's rule rather than a
    /// form of its own, so there is no member-level ghost to close it with,
    /// and telling a container apart from a declaration needs the rule a mold
    /// was numbered for — which the grammar reads back
    /// ([`Pbg::rule_of`](gandr_surface_grammar::Pbg::rule_of)) but this repair
    /// does not yet consult. Both declarations survive as distinct items; what
    /// the repair does not preserve is which one owns the later declaration.
    ///
    /// # Specification
    /// - requires: `candidates` are molds of this state's PBG.
    /// - ensures: when some candidate opens a declaration, no candidate
    ///   continues the open frontier, and the innermost open form is non-item,
    ///   force-closes every form at or above the nearest declaration-started
    ///   frontier (the slope base when there is none); the state is untouched
    ///   otherwise, and at most one collapse runs per token.
    /// - provides: declaration-bounded ghost repair.
    /// - fails: never; invalid molds are ignored.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an unclosed value delimiter before a fresh
    ///   declaration head distinguishes bounded repair from sibling absorption,
    ///   across the delimiter's sort and the surviving head's family.
    /// - witness: `tests::acceptance::unclosed_definition_delimiter_does_not_absorb_following_definition`
    /// - witness: `tests::acceptance::an_unclosed_delimiter_yields_to_every_declaration_family`
    /// - witness: `tests::contracts::declaration_boundary_stays_stable_under_layout`
    #[inline]
    pub fn settle_declaration_boundary(
        &mut self,
        candidates: &[MoldId],
    )
    {
        // Every candidate is consulted before anything is force-closed: one
        // that continues the open frontier is a live reading of this token, and
        // acting on a losing candidate would close a form the winner needs.
        let mut saw_declaration_head = false;
        for &mold in candidates {
            if bool::from(self.would_continue_form(mold)) {
                return;
            }
            saw_declaration_head = saw_declaration_head || bool::from(self.opens_declaration(mold));
        }
        if !saw_declaration_head {
            return;
        }
        let innermost_is_value_form = self
            .nearest_open_form()
            .and_then(|index| self.stack.get(usize::from(index)))
            .is_some_and(
                |cell| matches!(cell.role, Role::FormTile { sort, .. } if !bool::from(is_item_position(sort))),
            );
        if !innermost_is_value_form {
            return;
        }
        let floor = self
            .open_declaration_frontier()
            .map_or_else(|| StackIndex::from(0), StackIndex::from);
        self.collapse(StackFloor::from(floor));
    }

    /// Return whether `mold` can open an item-position declaration at a fresh
    /// slot.
    ///
    /// Three conditions, each excluding a distinct near-miss. [`Sort::Item`]
    /// is the item position itself. Membership in the grammar's FIRST set is
    /// what `admits_at` already means by "opens at a fresh slot", and it
    /// excludes a head inlined as a container's member tile — a module body's
    /// `def` is a tile of `module_declaration`, never a form of its own.
    /// Having a `≐`-successor excludes the bare `;` of `expression_statement`:
    /// holes are tile-transparent when the FIRST set is computed, so that `;`
    /// is the rule's first tile and is item-sorted, yet it terminates a
    /// statement rather than opening one.
    ///
    /// # Specification
    /// trivial.
    fn opens_declaration(
        &self,
        mold: MoldId,
    ) -> DeclarationStart
    {
        let Ok(def) = self.pbg.mold(mold)
        else {
            return DeclarationStart::from(false);
        };
        DeclarationStart::from(
            bool::from(is_item_position(def.sort))
                && bool::from(FormTable::is_form_first(self.pbg, mold))
                && bool::from(FormTable::has_succ(self.pbg, mold)),
        )
    }

    /// Return the nearest open frontier whose form starts at a declaration
    /// head.
    ///
    /// A frontier cell carries the mold of its form's **most recent** tile, not
    /// its first: `continue_form` advances the frontier onto each continuing
    /// tile, so an open `def id = …` sits on the `=` tile. The search therefore
    /// resolves every frontier down to its form-start before testing it, and
    /// testing the frontier's own mold would find a declaration-started form
    /// only in the degenerate `def def` case.
    ///
    /// # Specification
    /// trivial.
    fn open_declaration_frontier(&self) -> Option<FrontierIndex>
    {
        self.frontiers.iter().rev().find_map(|&index| {
            let start = self.form_start_index(StackIndex::from(index))?;
            let role = self.stack.get(usize::from(start)).map(|cell| cell.role)?;
            let Role::FormTile { mold, .. } = role
            else {
                return None;
            };
            bool::from(self.opens_declaration(mold)).then_some(FrontierIndex::from(index))
        })
    }

    /// Return whether pushing `mold` is admissible given a precomputed
    /// [`Frontier`] — the per-candidate hot path of
    /// [`admits`](MeldState::admits).
    ///
    /// # Specification
    /// - requires: `frontier` came from [`MeldState::admissibility_frontier`]
    ///   on this state, with no intervening mutation.
    /// - ensures: equals [`admits`](MeldState::admits) for `mold`; leaves
    ///   `self` unchanged.
    /// - provides: the constant-context admissibility check.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a form-end closer, a form-first mid, and an infix
    ///   operator at a fresh slot each distinguish the gate.
    /// - witness: `meld::tests::admits_rejects_a_stray_closer`
    #[inline]
    #[must_use]
    pub fn admits_at(
        &self,
        mold: MoldId,
        frontier: &Frontier,
    ) -> MoldAdmissibility
    {
        if self.pbg.mold(mold).is_err() {
            // An out-of-range mold takes push's total unmolded path; never
            // filtered, so the molder always has a last resort.
            return MoldAdmissibility::from(true);
        }
        // An item-form `(` is a declaration/telescope opener, never a
        // continuation of an expression operand. Keeping Item forms exempt
        // from sort filtering at a fresh slot is necessary for top-level
        // declarations, but that exemption must not steal a call's argument
        // opener after an expression head.
        if bool::from(frontier.head_operand)
            && frontier.expected == Sort::Expression
            && self
                .pbg
                .mold(mold)
                .is_ok_and(|def| def.sort == Sort::Item && def.label == "(")
        {
            return MoldAdmissibility::from(false);
        }
        let admissible = match self.classify(mold) {
            | Kind::FormEnd => frontier
                .open
                .is_some_and(|open| bool::from(self.adjacent(open, mold))),
            | Kind::FormMid => {
                frontier
                    .open
                    .is_some_and(|open| bool::from(self.adjacent(open, mold)))
                    || (frontier.open.is_none()
                        && bool::from(FormTable::is_form_first(self.pbg, mold)))
            },
            // A left-absorbing form-start (a call `(`, an instantiation `[`)
            // continues the head operand and is gated on it; the operand-
            // continuation tiebreak, not the sort, settles it. A fresh form-start
            // (a list `[`, a `#{` record, a parenthesised `(`) fills the open slot
            // directly, so the hole-sort check discards a wrong-sort one — a
            // Pattern `[` at an expression slot, an Expression `#{` at a type slot
            // — before any dry-run, collapsing the `[` / `(` / `#{` sort families
            // to their context-correct reading (Item form-starts stay exempt, so a
            // top-level `def` survives the Expression-defaulted slot).
            | Kind::FormStart { absorb_left } => {
                if absorb_left {
                    // The absorbing start applies only to a head operand of its
                    // own sort — never a top-level `def` item's Item-sorted head.
                    bool::from(frontier.head_operand)
                        && self.pbg.mold(mold).is_ok_and(|def| {
                            frontier.head_sort == Some(def.sort) || def.sort == Sort::Item
                        })
                }
                else {
                    bool::from(self.sort_admits(mold, frontier.expected))
                }
            },
            | Kind::Operator(OpShape::Infix | OpShape::Postfix) => {
                bool::from(frontier.head_operand)
            },
            // An operand fills the open slot directly: the hole-sort check
            // discards one whose sort mismatches the expected slot, so a
            // lowercase word's expression-atom and pattern-atom molds
            // no longer both survive at every position — the matching-sort one is
            // usually the lone admissible candidate, taken with no dry-run.
            | Kind::Operand => bool::from(self.sort_admits(mold, frontier.expected)),
            | Kind::Operator(OpShape::Prefix) => true,
        };
        MoldAdmissibility::from(admissible)
    }

    /// Return whether an operand `mold`'s sort fills the expected slot sort.
    ///
    /// Item-sort operands are never sort-filtered: the top-level slot defaults
    /// to [`Sort::Expression`] yet legitimately admits a bare-expression
    /// item, so an Item operand there must not be discarded (the filter is
    /// a soundness-safe narrowing, never a rejection of a real reading).
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    fn sort_admits(
        &self,
        mold: MoldId,
        expected: Sort,
    ) -> SortAdmissibility
    {
        let sort = self.pbg.mold(mold).map_or(Sort::Item, |def| def.sort);
        SortAdmissibility::from(sort == expected || sort == Sort::Item)
    }

    /// Return whether `mold` extends the head operand rather than starting a
    /// fresh juxtaposed one: a left-absorbing form-start (a call `(`, a
    /// projection `.`, an instantiation `[`) or an infix / postfix operator.
    ///
    /// With the head an operand, such a mold and a competing fresh atom /
    /// non-absorbing form-start over the same lexeme (a call `(` versus a
    /// parenthesised `(`, the comparison `>` versus a shell redirection atom)
    /// tie on the local `(Delta, continuation, sort)` key. Extending the
    /// operand is the reading gandr's expression grammar always intends
    /// after an operand (there is no bare expression juxtaposition outside
    /// a shell block, and the shell corpus never puts these lexemes after a
    /// command word), so the molder prefers it — settling the tie with no
    /// lookahead window.
    ///
    /// # Specification
    /// - requires: none.
    /// - ensures: returns whether `mold` continues the head operand; leaves
    ///   `self` unchanged.
    /// - provides: the molder's operand-continuation tiebreak key.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a call `(` after an operand, a fresh paren `(`, and
    ///   an infix operator distinguish the classification.
    /// - witness: `tests::acceptance::corpus_parses_totally`
    #[inline]
    #[must_use]
    pub fn continues_operand(
        &self,
        mold: MoldId,
    ) -> OperandContinuation
    {
        OperandContinuation::from(matches!(
            self.classify(mold),
            Kind::FormStart { absorb_left: true }
                | Kind::Operator(OpShape::Infix | OpShape::Postfix)
        ))
    }

    /// Return whether the topmost slope cell is a completed operand.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn head_is_operand(&self) -> HeadOperandPresence
    {
        HeadOperandPresence::from(matches!(
            self.stack.last().map(|cell| cell.role),
            Some(Role::Operand)
        ))
    }

    /// Return the sort of the head operand cell, if the head is an operand.
    ///
    /// A left-absorbing form-start (a call `(`, an instantiation `[`) only
    /// applies to an operand of its own sort: instantiating a top-level `def`
    /// item, whose head cell is [`Sort::Item`], is unsound, so the pre-filter
    /// requires the head operand's sort to match before admitting the absorbing
    /// start (and before the operand-continuation tiebreak can prefer it).
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn head_operand_sort(&self) -> Option<Sort>
    {
        let cell = self.stack.last()?;
        match cell.role {
            | Role::Operand => Some(cell.sort),
            | _ => None,
        }
    }

    /// Return the sort of the operand slot the slope head expects next.
    ///
    /// The molder ranks a fresh atom / form-start candidate by whether its sort
    /// matches this expectation, so `"hi"` reads as the expression string at an
    /// expression slot and the pattern string in a `val`/`case` pattern slot,
    /// without a completion traversal. The expectation is the nearest
    /// unsaturated operator's right-hole sort, or
    /// the nearest open form frontier's right-hole sort, defaulting to
    /// [`Sort::Expression`] at the top level.
    ///
    /// # Specification
    /// - requires: none.
    /// - ensures: returns the head's expected operand sort; leaves `self`
    ///   unchanged; defaults to [`Sort::Expression`] when no slot is open.
    /// - provides: the molder's sort-compatibility ranking key.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an expression slot, a pattern slot, and the top level
    ///   distinguish the returned sort.
    /// - witness: `meld::tests::expected_sort_reads_the_open_slot`
    #[inline]
    #[must_use]
    pub fn expected_operand_sort(&self) -> Sort
    {
        // The scan's Operand arm is a no-op, so it starts at the topmost
        // non-operand cell (the higher of the operator / form-tile cache tops)
        // rather than walking the whole top operand run — a shell block's run
        // holds every juxtaposed command atom (the sibling scan).
        let top_non_operand = match (self.operators.last(), self.barriers.last()) {
            | (Some(&op), Some(&tile)) => op.max(tile),
            | (Some(&op), None) => op,
            | (None, Some(&tile)) => tile,
            | (None, None) => return Sort::Expression,
        };
        let Some(limit) = top_non_operand.checked_add(1)
        else {
            return Sort::Expression;
        };
        let mut index = limit.min(self.stack.len());
        while let Some(next_index) = index.checked_sub(1) {
            index = next_index;
            match self.stack.get(index).map(|cell| cell.role) {
                | Some(Role::Operator { sort, shape, .. }) => {
                    let wants_right = matches!(shape, OpShape::Infix | OpShape::Prefix);
                    let right_filled = index
                        .checked_add(1)
                        .is_some_and(|next| bool::from(self.is_operand_at(StackIndex::from(next))));
                    if wants_right && !right_filled {
                        return sort;
                    }
                },
                | Some(Role::FormTile {
                    mold, open: true, ..
                }) => {
                    if let Some(sort) = self.frontier_hole_sort(mold) {
                        return sort;
                    }
                    return Sort::Expression;
                },
                | Some(Role::FormTile { open: false, .. } | Role::Operand) => {},
                | None => break,
            }
        }
        Sort::Expression
    }

    /// Return the sort of the recursive hole an open form frontier faces on its
    /// right, if any (the first `≐`-successor step that crosses a sort).
    ///
    /// # Specification
    /// trivial.
    fn frontier_hole_sort(
        &self,
        mold: MoldId,
    ) -> Option<Sort>
    {
        let def = self.pbg.mold(mold).ok()?;
        for step in self.pbg.step(def.rctx, Dir::Right).ok()? {
            if let StepSym::Sort(sort) = step.crossed {
                return Some(sort);
            }
        }
        None
    }

    /// Clean-close every topmost completable open frontier the incoming tile
    /// does not `≐`-continue.
    ///
    /// A **completable** frontier is a form-start / mid whose remaining form
    /// tail is nullable — its mold is in the grammar's LAST set
    /// ([`FormTable::is_form_last`]) — so the form is already a complete shape
    /// at that tile (a bare `?` hole before its optional `hole_name`). When
    /// the incoming tile continues the frontier (`?`'s `hole_name`), it
    /// stays open for the successor; otherwise the frontier is reduced into
    /// its meld **cleanly** — no ghost end, no obligation — before the
    /// incoming tile is classified. That keeps a bare hole a complete
    /// operand and leaves the following terminator / closer / operator a
    /// flat sibling, rather than the hole's open frontier shadowing an
    /// enclosing form (so a `}` closes the block, not the hole) or
    /// force-closing with a spurious [`Oblig::MissingTile`].
    ///
    /// A genuinely incomplete form (a `{` with no `}`, mold not in the LAST
    /// set) is left open, to force-close with its obligation at commit —
    /// the repair path for real incompleteness is unchanged.
    ///
    /// # Specification
    /// trivial.
    fn settle_completable(
        &mut self,
        incoming: MoldId,
    )
    {
        // Each iteration reduces one frontier into an operand, strictly
        // shrinking the open-frontier count, so the loop terminates.
        while let Some(frontier) = self.nearest_open_form() {
            let Some(Role::FormTile {
                mold: head_mold, ..
            }) = self.stack.get(usize::from(frontier)).map(|cell| cell.role)
            else {
                break;
            };
            // The incoming tile continues this form: keep it open for the
            // successor (a `?` awaiting its `hole_name`).
            if bool::from(self.adjacent(head_mold, incoming)) {
                break;
            }
            // A regex-LAST prefix with a required recursive-sort tail is not
            // complete until its operand arrives.
            if bool::from(self.pbg.mold_has_required_tail(head_mold)) {
                break;
            }
            // Only a completable frontier closes here; a form still awaiting a
            // required tile stays open for the force-close repair path.
            if !bool::from(FormTable::is_form_last(self.pbg, head_mold)) {
                break;
            }
            self.close_form(StackIndex::from(frontier));
        }
    }
    /// Clean-close each required-tail form whose tail is whole and which the
    /// incoming tile does not continue.
    ///
    /// A form ending in a required sort hole — `forall a . T`, `\A. T`, `+U[r]
    /// C` — has no tile to end it. It closes once its tail is whole, every
    /// operator above the frontier holding the operands it wants, and the
    /// incoming tile does not continue that tail: an infix or postfix
    /// operator, or a left-absorbing form start, of the hole's sort continues
    /// it exactly when the form's own group yields to the tile, the precedence
    /// a prefix operator at that group would give it. So `forall a . a * b`
    /// keeps the product inside the quantifier and `\A. -F A` keeps the
    /// returner inside the abstraction, while `+U[r] C * D` closes the bridge
    /// before the product. Unlike
    /// [`settle_completable`](Self::settle_completable), this path is
    /// stateful: the form's LAST tile is not completable while its required
    /// operand is absent.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: closes, innermost first, every open required-tail frontier
    ///   whose tail is whole and which `incoming` does not continue, reducing
    ///   the tail's operators into one operand first; stops at the first
    ///   frontier that is not; flags no obligation.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a tail ending in a prefix operator's operand, a tail
    ///   an operator tighter than the form continues, and a tail a looser
    ///   operator follows separate the settlement, each observed through the
    ///   form the commit builds.
    /// - witness: `meld::tests::a_required_tail_runs_as_far_as_its_group_yields`
    /// - witness: `tests::grammar::every_type_operator_spelling_reads_cleanly`
    ///
    /// # Termination
    /// Each pass closes the nearest open frontier, which drops it from the
    /// frontier cache, or stops; the inner loop reduces one operator above
    /// the frontier per step.
    fn settle_filled_required_tail(
        &mut self,
        incoming: Incoming<'_>,
    )
    {
        while let Some(frontier) = self.nearest_open_form() {
            if !bool::from(self.tail_is_whole(frontier))
                || bool::from(self.extends_tail(frontier, incoming))
            {
                break;
            }
            // The frontier tile is a barrier, so only the tail's operators are
            // reduced, topmost first.
            while let Some(operator) = self.topmost_operator_index() {
                self.reduce_operator(operator);
            }
            let Some(end) = self.required_tail_operand(frontier)
            else {
                break;
            };
            self.close_form(end);
        }
    }

    /// Whether the open frontier at `frontier` carries a required tail that
    /// is whole: a run of its hole's sort of prefix operators, operands,
    /// postfix and infix operators, each operator holding the operands it
    /// wants, ending in an operand.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: true exactly when the frontier's mold carries a required tail
    ///   with a known hole sort, every cell above the frontier is an operand or
    ///   an operator of that sort, no operand stands beside another and no
    ///   operator lacks an operand it wants, and the run is non-empty.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — through
    ///   [`settle_filled_required_tail`](Self::settle_filled_required_tail): a
    ///   prefix operator with its operand is whole, one without it is not.
    /// - witness: `meld::tests::a_required_tail_runs_as_far_as_its_group_yields`
    ///
    /// # Termination
    /// One step per cell above the frontier.
    fn tail_is_whole(
        &self,
        frontier: FrontierIndex,
    ) -> TailWhole
    {
        let frontier_index = usize::from(frontier);
        let Some(Role::FormTile { mold, .. }) =
            self.stack.get(frontier_index).map(|cell| cell.role)
        else {
            return TailWhole::from(false);
        };
        let Some(expected) = self
            .frontier_hole_sort(mold)
            .filter(|_sort| bool::from(self.pbg.mold_has_required_tail(mold)))
        else {
            return TailWhole::from(false);
        };
        let tail = frontier_index
            .checked_add(1)
            .and_then(|start| self.stack.get(start ..))
            .unwrap_or(&[]);
        let mut wants_operand = true;
        for cell in tail {
            if cell.sort != expected {
                return TailWhole::from(false);
            }
            let fits = match cell.role {
                | Role::Operand
                | Role::Operator {
                    shape: OpShape::Prefix,
                    ..
                } => wants_operand,
                | Role::Operator {
                    shape: OpShape::Infix | OpShape::Postfix,
                    ..
                } => !wants_operand,
                | Role::FormTile { .. } => false,
            };
            if !fits {
                return TailWhole::from(false);
            }
            wants_operand = matches!(cell.role, Role::Operator {
                shape: OpShape::Prefix | OpShape::Infix,
                ..
            });
        }
        TailWhole::from(!tail.is_empty() && !wants_operand)
    }

    /// Whether `incoming` continues the tail of the required-tail form whose
    /// frontier is at `frontier`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: true exactly when the frontier's hole sort is known and
    ///   `incoming` — the tile, or any mold a label of the token may take — is
    ///   an infix or postfix operator or a left-absorbing form start of that
    ///   sort whose group the form's group yields to.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — through
    ///   [`settle_filled_required_tail`](Self::settle_filled_required_tail): an
    ///   operator tighter than the form and one looser separate the answer.
    /// - witness: `meld::tests::a_required_tail_runs_as_far_as_its_group_yields`
    ///
    /// # Termination
    /// One step per mold a label of the token may take.
    fn extends_tail(
        &self,
        frontier: FrontierIndex,
        incoming: Incoming<'_>,
    ) -> TailExtension
    {
        let Some((form, hole)) = self
            .stack
            .get(usize::from(frontier))
            .and_then(|cell| match cell.role {
                | Role::FormTile { mold, .. } => Some(mold),
                | Role::Operand | Role::Operator { .. } => None,
            })
            .and_then(|mold| {
                Some((
                    self.pbg.mold(mold).ok()?.prec,
                    self.frontier_hole_sort(mold)?,
                ))
            })
        else {
            return TailExtension::from(false);
        };
        let continues = |tile: MoldId| {
            self.pbg.mold(tile).is_ok_and(|def| {
                def.sort == hole
                    && matches!(
                        self.classify(tile),
                        Kind::Operator(OpShape::Infix | OpShape::Postfix)
                            | Kind::FormStart { absorb_left: true }
                    )
                    && bool::from(self.pbg.dag().lt(form, def.prec, Assoc::Right))
            })
        };
        TailExtension::from(match incoming {
            | Incoming::Tile(tile) => continues(tile),
            | Incoming::Token(labels) => <&[&str]>::from(labels).iter().any(|&label| {
                self.pbg
                    .candidates(TileLabel(label))
                    .iter()
                    .any(|&tile| continues(tile))
            }),
        })
    }

    /// Return the trailing operand index when an open required-tail form has
    /// exactly one matching operand above its frontier.
    ///
    /// # Specification
    /// trivial.
    fn required_tail_operand(
        &self,
        frontier: FrontierIndex,
    ) -> Option<StackIndex>
    {
        let frontier_index = usize::from(frontier);
        let Some(Role::FormTile { mold, .. }) =
            self.stack.get(frontier_index).map(|cell| cell.role)
        else {
            return None;
        };
        if !bool::from(self.pbg.mold_has_required_tail(mold)) {
            return None;
        }
        let expected = self.frontier_hole_sort(mold)?;
        let content_index = frontier_index.checked_add(1)?;
        let content = self.stack.get(content_index)?;
        (self.stack.len() == content_index.saturating_add(1)
            && matches!(content.role, Role::Operand)
            && content.sort == expected)
            .then_some(StackIndex::from(content_index))
    }

    /// Whether the open required-tail frontier at `frontier`, of mold `mold`,
    /// has its tail under way as one form of the hole's sort: a single operand
    /// above it, or an inner form starting right above it, whose whole run a
    /// commit collapses into that one operand before closing the frontier.
    ///
    /// # Specification
    /// - requires: `mold` is the mold of the frontier cell at `frontier`.
    /// - ensures: true exactly when `mold` carries a required tail, the hole's
    ///   sort is known, and the cell above the frontier is either the last cell
    ///   and an operand of that sort or the start tile of a form of that sort;
    ///   false otherwise.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a tail that is one operand, a tail that is an open
    ///   inner form and an absent tail separate the query, each observed
    ///   through the obligations `finalize` reports.
    /// - witness: `meld::tests::finalize_charges_a_required_tail_only_when_it_is_absent`
    fn tail_is_under_way(
        &self,
        frontier: FrontierIndex,
        mold: MoldId,
    ) -> TailUnderWay
    {
        let frontier_index = usize::from(frontier);
        let under_way = bool::from(self.pbg.mold_has_required_tail(mold))
            && self.frontier_hole_sort(mold).is_some_and(|expected| {
                let content_index = frontier_index.saturating_add(1);
                self.stack
                    .get(content_index)
                    .is_some_and(|content| match content.role {
                        | Role::Operand => {
                            self.stack.len() == content_index.saturating_add(1)
                                && content.sort == expected
                        },
                        | Role::FormTile {
                            start: true, sort, ..
                        } => sort == expected,
                        | Role::FormTile { start: false, .. } | Role::Operator { .. } => false,
                    })
            });
        TailUnderWay::from(under_way)
    }

    /// Clean-close every topmost completable frontier the **upcoming** token —
    /// with candidate labels `labels` — cannot `≐`-continue, before that token
    /// is molded.
    ///
    /// This is the molder's eager companion of
    /// [`settle_completable`](Self::settle_completable): where the latter runs
    /// inside [`push`](Self::push) on the tile actually chosen, this runs on
    /// the **real** state *before* gather/choose so a bare `?` hole never
    /// shadows an enclosing form in the molder's frontier queries —
    /// admissibility, the gathered candidate menu, the expected operand
    /// sort, the continuation rank. With the hole settled, the enclosing
    /// form's closer (the `;` closing a `def` whose value is a bare hole)
    /// molds against the correct frontier. A completable frontier whose
    /// `≐`-successor shares a label with the upcoming token (a `?` before a
    /// `hole_name` word) stays open so the name still attaches.
    ///
    /// # Specification
    /// - requires: `labels` are the upcoming token's candidate labels.
    /// - ensures: reduces to a clean operand meld every topmost completable
    ///   frontier none of whose successors carries a label in `labels`; stops
    ///   at the first non-completable or token-continuable frontier; introduces
    ///   no obligation.
    /// - provides: the molder's pre-gather hole-settling pass.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a bare hole before a form closer (settled) and a hole
    ///   before a name word (kept open) distinguish the pass.
    /// - witness: `tests::acceptance::hole_positions_mold_zero_obligation`
    #[inline]
    pub fn settle_shadowing_frontiers(
        &mut self,
        labels: CandidateLabels<'_>,
    )
    {
        self.settle_filled_required_tail(Incoming::Token(labels));
        while let Some(frontier) = self.nearest_open_form() {
            let Some(Role::FormTile {
                mold: head_mold, ..
            }) = self.stack.get(usize::from(frontier)).map(|cell| cell.role)
            else {
                break;
            };
            if bool::from(self.pbg.mold_has_required_tail(head_mold)) {
                break;
            }
            if !bool::from(FormTable::is_form_last(self.pbg, head_mold)) {
                break;
            }
            // Keep the frontier open when the upcoming token could be its
            // `≐`-successor (a `?` before a `hole_name` word), so the name
            // still attaches to the hole.
            if bool::from(self.successor_label_in(head_mold, labels)) {
                break;
            }
            self.close_form(StackIndex::from(frontier));
        }
    }

    /// Return whether any `≐`-successor of `mold` carries a label in `labels`.
    ///
    /// # Specification
    /// trivial.
    fn successor_label_in(
        &self,
        mold: MoldId,
        labels: CandidateLabels<'_>,
    ) -> SuccessorLabelPresence
    {
        let labels = <&[&'static str]>::from(labels);
        let adjacencies = self.pbg.adjacencies();
        let start = adjacencies.partition_point(|&(left, _)| left < mold);
        SuccessorLabelPresence::from(
            adjacencies
                .get(start ..)
                .unwrap_or(&[])
                .iter()
                .take_while(|&&(left, _)| left == mold)
                .any(|&(_, right)| {
                    self.pbg
                        .mold(right)
                        .is_ok_and(|def| labels.contains(&def.label))
                }),
        )
    }

    /// Open a new multi-tile form with `mold` as its start frontier.
    ///
    /// The form-start becomes the open frontier; its `≐`-successors extend it,
    /// its interior sort-holes fill with operands, and its form-end reduces it
    /// (`close_form`). A left-bounded start (`absorb_left`) absorbs the operand
    /// below it at close (a call `(`, a projection `.`).
    ///
    /// # Specification
    /// trivial.
    fn open_form(
        &mut self,
        mold: MoldId,
        sort: Sort,
        cell: Cell,
        absorb_left: AbsorbsLeft,
    )
    {
        self.push_cell(Cell {
            role: Role::FormTile {
                mold,
                sort,
                open: bool::from(FormTable::has_succ(self.pbg, mold)),
                start: true,
                absorb_left: bool::from(absorb_left),
            },
            ..cell
        });
    }

    /// Continue (or, on `is_end`, close) the topmost open form with `mold`.
    ///
    /// When `mold` is the `≐`-successor of the open frontier, the intervening
    /// content is collapsed to operands (its hole-fills), the frontier advances
    /// to `mold`, and a form-end reduces the whole run into a meld. When no
    /// open frontier accepts `mold`, a stray end flags a ghost opener
    /// ([`Oblig::MissingTile`]) and a stray mid opens a fresh partial form.
    ///
    /// # Specification
    /// trivial.
    fn continue_form(
        &mut self,
        mold: MoldId,
        sort: Sort,
        cell: Cell,
        is_end: FormEndTile,
    )
    {
        if let Some(frontier) = self.nearest_open_form()
            && let Some(Role::FormTile {
                mold: head_mold, ..
            }) = self.stack.get(usize::from(frontier)).map(|c| c.role)
            && bool::from(self.adjacent(head_mold, mold))
        {
            // The tile continues this form. Collapse the content region above
            // the frontier into operand hole-fills, then advance the frontier.
            let Some(content_floor) = StackIndex::from(frontier).floor_after()
            else {
                return;
            };
            self.collapse(content_floor);
            self.set_form_open(StackIndex::from(frontier), FormOpen::from(false));
            self.push_cell(Cell {
                role: Role::FormTile {
                    mold,
                    sort,
                    open: !bool::from(is_end),
                    start: false,
                    absorb_left: false,
                },
                ..cell
            });
            if bool::from(is_end)
                && let Some(top) = self.stack.len().checked_sub(1)
            {
                self.close_form(StackIndex::from(top));
            }
            return;
        }

        if bool::from(is_end) {
            // A form-end with no matching open frontier: an absent opener.
            self.flag(
                Oblig::MissingTile,
                SourceSpan::new(SourceOffset::from(cell.start), SourceOffset::from(cell.end)),
            );
            self.push_cell(cell);
        }
        else {
            // A form-mid with no matching frontier: open a fresh partial form.
            self.push_cell(Cell {
                role: Role::FormTile {
                    mold,
                    sort,
                    open: bool::from(FormTable::has_succ(self.pbg, mold)),
                    start: true,
                    absorb_left: false,
                },
                ..cell
            });
        }
    }

    /// Return the index of the topmost open form frontier, or `None` if none
    /// is open above the base.
    ///
    /// The topmost `open` frontier is the innermost active form; its content is
    /// collapsed to hole-fills by the caller before the frontier advances.
    /// O(1): the `frontiers` cache top — never a scan of the content region
    /// (which for a shell block holds every juxtaposed command atom).
    ///
    /// # Specification
    /// trivial.
    fn nearest_open_form(&self) -> Option<FrontierIndex>
    {
        self.frontiers.last().copied().map(FrontierIndex::from)
    }

    /// Clear or set the open frontier flag of the form tile at `index`.
    ///
    /// # Specification
    /// trivial.
    fn set_form_open(
        &mut self,
        index: StackIndex,
        open: FormOpen,
    )
    {
        let index = usize::from(index);
        let open = bool::from(open);
        if let Some(cell) = self.stack.get_mut(index)
            && let Role::FormTile {
                open: ref mut flag, ..
            } = cell.role
        {
            let was_open = *flag;
            *flag = open;
            // Maintain the open-frontier cache. Both callers flip the NEAREST
            // open frontier (`continue_form` / `force_close_form` act on
            // `nearest_open_form`), so closing pops the cache top; the sorted
            // fallbacks keep the cache exact on any other flip.
            if was_open && !open {
                if self.frontiers.last() == Some(&index) {
                    self.frontiers.pop();
                }
                else {
                    self.frontiers.retain(|&frontier| frontier != index);
                }
            }
            else if !was_open && open {
                if self.frontiers.last().is_none_or(|&last| last < index) {
                    self.frontiers.push(index);
                }
                else if let Err(slot) = self.frontiers.binary_search(&index) {
                    self.frontiers.insert(slot, index);
                }
            }
        }
    }

    /// Reduce the multi-tile form whose closing frontier is at `end_index`.
    ///
    /// Collects the form run from its start (absorbing the preceding operand
    /// for a left-bounded start) up to and including `end_index`, reducing
    /// any interior operators first, and wraps the run in a meld operand.
    ///
    /// # Specification
    /// trivial.
    fn close_form(
        &mut self,
        end_index: StackIndex,
    )
    {
        let end_index = usize::from(end_index);
        let Some(start_index) = self.form_start_index(StackIndex::from(end_index))
        else {
            return;
        };
        let start_index = usize::from(start_index);
        let Some(start_cell) = self.stack.get(start_index).copied()
        else {
            return;
        };
        // A left-bounded start absorbs the operand immediately below it.
        let low = match start_cell.role {
            | Role::FormTile {
                absorb_left: true, ..
            } => start_index
                .checked_sub(1)
                .filter(|&below| bool::from(self.is_operand_at(StackIndex::from(below))))
                .unwrap_or(start_index),
            | _ => start_index,
        };
        let Some(high_exclusive) = end_index.checked_add(1)
        else {
            return;
        };

        let mut children: Vec<EmitId> = Vec::new();
        let mut span_start = start_cell.start;
        let mut span_end = start_cell.end;
        for slot in low .. high_exclusive {
            if let Some(cell) = self.stack.get(slot) {
                children.push(cell.emit);
                span_start = span_start.min(cell.start);
                span_end = span_end.max(cell.end);
            }
        }

        // The form is named by the mold of the tile that opened it; the
        // grammar resolves that mold to the form's rule and named kind.
        let Role::FormTile { mold, .. } = start_cell.role
        else {
            return;
        };
        let span = SourceSpan::new(SourceOffset::from(span_start), SourceOffset::from(span_end));
        let meld = self.emit_interior(NodeLabel::Meld(mold), span, children);
        self.replace_range(
            StackRange::new(StackIndex::from(low), StackIndex::from(high_exclusive)),
            Cell {
                emit: meld,
                start: span_start,
                end: span_end,
                sort: start_cell.sort,
                role: Role::Operand,
            },
        );
    }

    /// Return the start index of the form whose frontier is at `end_index`,
    /// scanning down to the nearest form-start tile.
    ///
    /// The scan walks the `barriers` cache (form tiles only) instead of every
    /// slope cell, so interleaved operand content costs nothing.
    ///
    /// # Specification
    /// trivial.
    fn form_start_index(
        &self,
        end_index: StackIndex,
    ) -> Option<StackIndex>
    {
        let end_index = usize::from(end_index);
        for &index in self.barriers.iter().rev() {
            if index > end_index {
                continue;
            }
            if matches!(
                self.stack.get(index).map(|cell| cell.role),
                Some(Role::FormTile { start: true, .. })
            ) {
                return Some(StackIndex::from(index));
            }
        }
        None
    }

    /// The reduce/degrout loop: reduce the head handle while it takes
    /// precedence.
    ///
    /// # Specification
    /// trivial.
    fn reduce_toward(
        &mut self,
        tau_sort: Sort,
        tau_prec: Prec,
        tau_mold: MoldId,
        tau_span: SourceSpan,
    )
    {
        // Bounded by the operator count, which strictly decreases each reducing
        // iteration, so the loop always terminates.
        while let Some(head_index) = self.topmost_operator_index() {
            let Some((head_mold, head_prec, head_sort)) = self.operator_at(head_index)
            else {
                break;
            };
            match self.compare(
                head_mold, head_prec, head_sort, tau_mold, tau_prec, tau_sort,
            ) {
                | Rel::Yields | Rel::Match => break,
                | Rel::Takes => self.reduce_operator(head_index),
                | Rel::Ambiguous => {
                    // Route through the completion path: flag the ambiguity at
                    // the smallest responsible span (the incoming tile) and
                    // reduce the head level so the parse stays total.
                    self.flag(Oblig::AmbiguousPrec, tau_span);
                    self.reduce_operator(head_index);
                },
                | Rel::CrossSort => {
                    self.flag(Oblig::InconMeld, tau_span);
                    self.reduce_operator(head_index);
                },
            }
        }
    }

    /// Return the operator-precedence relation between a head operator and τ.
    ///
    /// # Specification
    /// trivial.
    fn compare(
        &self,
        head_mold: MoldId,
        head_prec: Prec,
        head_sort: Sort,
        tau_mold: MoldId,
        tau_prec: Prec,
        tau_sort: Sort,
    ) -> Rel
    {
        if bool::from(self.adjacent(head_mold, tau_mold)) {
            return Rel::Match;
        }
        if head_sort != tau_sort {
            return Rel::CrossSort;
        }
        let dag = self.pbg.dag();
        if bool::from(dag.gt(head_prec, tau_prec, Assoc::Left)) {
            return Rel::Takes;
        }
        if bool::from(dag.lt(head_prec, tau_prec, Assoc::Right)) {
            return Rel::Yields;
        }
        Rel::Ambiguous
    }

    /// Return whether `(left, right)` is a same-form `≐` adjacency.
    ///
    /// # Specification
    /// trivial.
    fn adjacent(
        &self,
        left: MoldId,
        right: MoldId,
    ) -> SameFormAdjacency
    {
        SameFormAdjacency::from(self.pbg.adjacencies().binary_search(&(left, right)).is_ok())
    }

    /// Return the first `≐`-successor mold of `mold`, if any (the completion
    /// query's expected next tile).
    ///
    /// # Specification
    /// trivial.
    fn first_successor(
        &self,
        mold: MoldId,
    ) -> Option<MoldId>
    {
        let adjacencies = self.pbg.adjacencies();
        let start = adjacencies.partition_point(|&(left, _)| left < mold);
        adjacencies
            .get(start)
            .filter(|&&(left, _)| left == mold)
            .map(|&(_, right)| right)
    }

    /// Classify an incoming tile by its `≐`-membership and precedence bounds.
    ///
    /// A tile that participates in the same-form `≐` relation is a form tile
    /// (start / mid / end); otherwise its precedence bounds give a bare operand
    /// or a single-tile prefix / infix / postfix operator. A tile with a
    /// `≐`-predecessor and no `≐`-successor ends its form only when nothing
    /// is required after it: one followed by a required sort hole — the `]`
    /// of `+U[r] C` — is a mid tile, and the form closes once its trailing
    /// operand arrives.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a form tile with a successor is a start or a mid by whether
    ///   it has a predecessor; a form tile with a predecessor and no successor
    ///   is a mid when its mold carries a required tail and an end otherwise;
    ///   any other tile is an operand or an operator by its bounds.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a closing bracket followed by a required operand is
    ///   separated from one that ends its form, each observed through the form
    ///   its trailing operand lands in.
    /// - witness: `meld::tests::a_bracket_before_a_required_tail_keeps_its_form_open`
    fn classify(
        &self,
        mold: MoldId,
    ) -> Kind
    {
        let (left, right) = self.pbg.bounds(mold).unwrap_or((Bound::Root, Bound::Root));
        let left_hole = matches!(left, Bound::Value(_));
        let has_pred = FormTable::has_pred(self.pbg, mold);
        let has_succ = FormTable::has_succ(self.pbg, mold);
        match (bool::from(has_pred), bool::from(has_succ)) {
            | (false, true) => Kind::FormStart {
                absorb_left: left_hole,
            },
            | (true, false) if bool::from(self.pbg.mold_has_required_tail(mold)) => Kind::FormMid,
            | (true, false) => Kind::FormEnd,
            | (true, true) => Kind::FormMid,
            | (false, false) => {
                let right_hole = matches!(right, Bound::Value(_));
                match (left_hole, right_hole) {
                    | (false, false) => Kind::Operand,
                    | (false, true) => Kind::Operator(OpShape::Prefix),
                    | (true, false) => Kind::Operator(OpShape::Postfix),
                    | (true, true) => Kind::Operator(OpShape::Infix),
                }
            },
        }
    }

    /// Return the index of the topmost reducible operator, or `None` if the top
    /// region reaches a form tile (a precedence floor) or the base.
    ///
    /// O(1): the topmost non-operand cell is the higher of the `operators` and
    /// `barriers` cache tops; an operator there is reducible, a form tile is
    /// the floor — never a scan of the operand run above it.
    ///
    /// # Specification
    /// trivial.
    fn topmost_operator_index(&self) -> Option<OperatorIndex>
    {
        let operator = self.operators.last().copied()?;
        match self.barriers.last() {
            | Some(&barrier) if barrier > operator => None,
            | _ => Some(OperatorIndex::from(operator)),
        }
    }

    /// Return the `(mold, prec, sort)` of the operator at `index`, if any.
    ///
    /// # Specification
    /// trivial.
    fn operator_at(
        &self,
        index: OperatorIndex,
    ) -> Option<(MoldId, Prec, Sort)>
    {
        match self.stack.get(usize::from(index)).map(|cell| cell.role) {
            | Some(Role::Operator {
                mold, prec, sort, ..
            }) => Some((mold, prec, sort)),
            | _ => None,
        }
    }

    /// Reduce the operator at `index` into a meld, filling its slots.
    ///
    /// This is `fill` (paper Fig. 27): the operator's grammatically required
    /// operands are drawn from the adjacent operand cells; a missing required
    /// operand inserts a convex grout child ([`Oblig::MissingMeld`]).
    ///
    /// # Specification
    /// trivial.
    fn reduce_operator(
        &mut self,
        index: OperatorIndex,
    )
    {
        let index = usize::from(index);
        let Some(cell) = self.stack.get(index).copied()
        else {
            return;
        };
        let Role::Operator {
            mold, sort, shape, ..
        } = cell.role
        else {
            return;
        };
        let wants_left = matches!(shape, OpShape::Infix | OpShape::Postfix);
        let wants_right = matches!(shape, OpShape::Infix | OpShape::Prefix);

        // Gate operand capture on the operator's shape: a captured cell is
        // removed from the slope and must appear as a child of the meld, so a
        // non-captured neighbour (e.g. a postfix's right operand) is left in
        // place rather than dropped (which would orphan its emitted node).
        let right_index = if wants_right {
            index
                .checked_add(1)
                .filter(|&next| bool::from(self.is_operand_at(StackIndex::from(next))))
        }
        else {
            None
        };
        let left_index = if wants_left {
            index
                .checked_sub(1)
                .filter(|&prev| bool::from(self.is_operand_at(StackIndex::from(prev))))
        }
        else {
            None
        };

        let low = left_index.unwrap_or(index);
        let high = right_index.unwrap_or(index);
        let Some(high_exclusive) = high.checked_add(1)
        else {
            return;
        };

        let mut children: Vec<EmitId> = Vec::new();
        let mut span_start = cell.start;
        let mut span_end = cell.end;

        if wants_left {
            match left_index.and_then(|left| self.stack.get(left)) {
                | Some(left_cell) => {
                    children.push(left_cell.emit);
                    span_start = left_cell.start;
                },
                | None => {
                    let span = SourceSpan::point(SourceOffset::from(cell.start));
                    let grout = self.emit_token(
                        NodeLabel::Grout {
                            sort: sort.grout_sort(),
                            shape: GroutShape::Convex,
                        },
                        span,
                    );
                    children.push(grout);
                    self.flag(Oblig::MissingMeld, span);
                },
            }
        }

        children.push(cell.emit);

        if wants_right {
            match right_index.and_then(|right| self.stack.get(right)) {
                | Some(right_cell) => {
                    children.push(right_cell.emit);
                    span_end = right_cell.end;
                },
                | None => {
                    let span = SourceSpan::point(SourceOffset::from(cell.end));
                    let grout = self.emit_token(
                        NodeLabel::Grout {
                            sort: sort.grout_sort(),
                            shape: GroutShape::Convex,
                        },
                        span,
                    );
                    children.push(grout);
                    self.flag(Oblig::MissingMeld, span);
                },
            }
        }

        let span = SourceSpan::new(SourceOffset::from(span_start), SourceOffset::from(span_end));
        let meld = self.emit_interior(NodeLabel::Meld(mold), span, children);
        self.replace_range(
            StackRange::new(StackIndex::from(low), StackIndex::from(high_exclusive)),
            Cell {
                emit: meld,
                start: span_start,
                end: span_end,
                sort,
                role: Role::Operand,
            },
        );
    }

    /// Reduce every operator and force-close every open form at or above
    /// `floor`, leaving only operand cells there.
    ///
    /// Each step removes one operator or open frontier, the highest first, so a
    /// form's content is reduced before the form is force-closed and the loop
    /// ends.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: no operator and no open form frontier remains at or above
    ///   `floor`.
    /// - panics: none.
    fn collapse(
        &mut self,
        floor: StackFloor,
    )
    {
        // Each iteration removes one operator or open form frontier. The
        // highest-index selector makes nested form content reduce before the
        // enclosing frontier is force-closed, so no recursive caller-input path
        // is needed.
        while let Some(step) = self.highest_reducible(floor) {
            match step {
                | CollapseStep::ForceCloseForm(frontier) => self.force_close_form(frontier),
                | CollapseStep::ReduceOperator(operator) => self.reduce_operator(operator),
            }
        }
    }

    /// Return the highest index at or above `floor` holding an operator or an
    /// open form frontier, with a flag marking which (form when `true`).
    ///
    /// O(1): the higher of the `operators` and `frontiers` cache tops at or
    /// above `floor` — never a scan of the content region.
    ///
    /// # Specification
    /// trivial.
    fn highest_reducible(
        &self,
        floor: StackFloor,
    ) -> Option<CollapseStep>
    {
        let floor = usize::from(floor);
        let operator = self
            .operators
            .last()
            .copied()
            .filter(|&index| index >= floor);
        let frontier = self
            .frontiers
            .last()
            .copied()
            .filter(|&index| index >= floor);
        match (operator, frontier) {
            | (Some(op), Some(fr)) => {
                if fr > op {
                    Some(CollapseStep::ForceCloseForm(FrontierIndex::from(fr)))
                }
                else {
                    Some(CollapseStep::ReduceOperator(OperatorIndex::from(op)))
                }
            },
            | (None, Some(fr)) => Some(CollapseStep::ForceCloseForm(FrontierIndex::from(fr))),
            | (Some(op), None) => Some(CollapseStep::ReduceOperator(OperatorIndex::from(op))),
            | (None, None) => None,
        }
    }

    /// Force-close an incomplete open form whose frontier is at `frontier`.
    ///
    /// The form never reached its end tile, so its absent closer is a ghost:
    /// the content above the frontier is collapsed to operands, a ghost end
    /// grout is appended, the run from the form-start is reduced into a meld,
    /// and the missing delimiter is flagged ([`Oblig::MissingTile`]).
    ///
    /// # Specification
    /// - requires: every cell above `frontier` is an operand, which
    ///   [`collapse`](Self::collapse)'s highest-first order guarantees.
    /// - ensures: the form at `frontier` is no longer open; a form that never
    ///   reached a last tile gains a ghost end and one [`Oblig::MissingTile`]
    ///   over the frontier tile's span.
    /// - panics: none.
    fn force_close_form(
        &mut self,
        frontier: FrontierIndex,
    )
    {
        let frontier_index = usize::from(frontier);
        // A required-tail form is complete once its trailing operand has
        // arrived, even though no terminal tile advances the frontier.
        if let Some(end) = self.required_tail_operand(frontier) {
            self.close_form(end);
            return;
        }
        // A regex-LAST prefix with a missing required tail must force-close,
        // not take the ordinary clean LAST path below.
        let required_tail = self
            .stack
            .get(frontier_index)
            .and_then(|cell| match cell.role {
                | Role::FormTile { mold, .. } => {
                    Some(bool::from(self.pbg.mold_has_required_tail(mold)))
                },
                | Role::Operand | Role::Operator { .. } => None,
            })
            .unwrap_or(false);
        // A completable frontier (its mold in the grammar's LAST set) is already
        // a complete form: close it cleanly with no ghost end and no obligation
        // — a bare `?` hole at end of input is a whole hole, not an incomplete
        // form. Content above it stays a sibling.
        if !required_tail
            && let Some(Role::FormTile { mold, .. }) =
                self.stack.get(frontier_index).map(|cell| cell.role)
            && bool::from(FormTable::is_form_last(self.pbg, mold))
        {
            self.close_form(StackIndex::from(frontier));
            return;
        }

        let Some(frontier_cell) = self.stack.get(frontier_index).copied()
        else {
            return;
        };
        let sort = frontier_cell.sort;
        let frontier_mold = match frontier_cell.role {
            | Role::FormTile { mold, .. } => mold,
            | Role::Operand | Role::Operator { .. } => MoldId::from(u32::MAX),
        };

        // Append a ghost end tile so the form reads as a completed shape.
        //
        // When the grammar says every completion of this frontier ends at a
        // paired closer of one class, the ghost carries that class and becomes
        // a minted close a later consumer can pair against the closer the
        // author actually wrote. When it says nothing — the completions
        // disagree, or end at something that closes nothing, as `def x = E ;`
        // does at its `;` — the ghost stays ordinary grout, byte-identical to
        // what it has always been. That asymmetry is deliberate: an unclassed
        // ghost pairs with nothing, so the failure mode is a suppression not
        // applied rather than one applied to the wrong declaration.
        let ghost_span = SourceSpan::point(SourceOffset::from(frontier_cell.end));
        let label = self.pbg.closing_class(frontier_mold).map_or_else(
            || NodeLabel::Grout {
                sort: sort.grout_sort(),
                shape: GroutShape::Postfix,
            },
            |class| NodeLabel::GhostClose {
                sort: sort.grout_sort(),
                class,
            },
        );
        let ghost = self.emit_token(label, ghost_span);
        self.push_cell(Cell {
            emit: ghost,
            start: frontier_cell.end,
            end: frontier_cell.end,
            sort,
            role: Role::FormTile {
                mold: frontier_mold,
                sort,
                open: false,
                start: false,
                absorb_left: false,
            },
        });
        self.set_form_open(StackIndex::from(frontier), FormOpen::from(false));
        self.flag(
            Oblig::MissingTile,
            SourceSpan::new(
                SourceOffset::from(frontier_cell.start),
                SourceOffset::from(frontier_cell.end),
            ),
        );
        if let Some(top) = self.stack.len().checked_sub(1) {
            self.close_form(StackIndex::from(top));
        }
    }

    /// Return whether the cell at `index` is an operand.
    ///
    /// # Specification
    /// trivial.
    fn is_operand_at(
        &self,
        index: StackIndex,
    ) -> OperandPresence
    {
        OperandPresence::from(matches!(
            self.stack.get(usize::from(index)).map(|cell| cell.role),
            Some(Role::Operand)
        ))
    }

    /// Push a cell onto the top of the slope, maintaining the head caches.
    ///
    /// # Specification
    /// trivial.
    fn push_cell(
        &mut self,
        cell: Cell,
    )
    {
        self.index_cell(StackIndex::from(self.stack.len()), &cell);
        self.stack.push(cell);
    }

    /// Record `cell`'s role in the monotone index caches at slope index
    /// `index` (which must be the current top — pushes only).
    ///
    /// # Specification
    /// trivial.
    fn index_cell(
        &mut self,
        index: StackIndex,
        cell: &Cell,
    )
    {
        let index = usize::from(index);
        match cell.role {
            | Role::FormTile { open, .. } => {
                self.barriers.push(index);
                if open {
                    self.frontiers.push(index);
                }
            },
            | Role::Operator { .. } => self.operators.push(index),
            | Role::Operand => {},
        }
    }

    /// Drop every cached index at or above `floor` (the cells a top-reaching
    /// splice removes). Amortized O(1): each index is pushed once and popped
    /// at most once.
    ///
    /// # Specification
    /// trivial.
    fn unindex_from(
        &mut self,
        floor: StackFloor,
    )
    {
        let floor = usize::from(floor);
        while self.frontiers.last().is_some_and(|&index| index >= floor) {
            self.frontiers.pop();
        }
        while self.operators.last().is_some_and(|&index| index >= floor) {
            self.operators.pop();
        }
        while self.barriers.last().is_some_and(|&index| index >= floor) {
            self.barriers.pop();
        }
    }

    /// Rebuild the head caches from the slope (checkpoint resume only — every
    /// streaming mutation maintains them incrementally).
    ///
    /// # Specification
    /// trivial.
    fn rebuild_head_caches(&mut self)
    {
        self.frontiers.clear();
        self.operators.clear();
        self.barriers.clear();
        for index in 0 .. self.stack.len() {
            if let Some(cell) = self.stack.get(index).copied() {
                self.index_cell(StackIndex::from(index), &cell);
            }
        }
    }

    /// TEST ONLY: assert the incremental head caches equal a fresh role scan
    /// of the slope (the caches' exactness invariant).
    ///
    /// # Specification
    /// - requires: none.
    /// - ensures: panics unless `frontiers` / `operators` / `barriers` are
    ///   exactly the ascending indices of the open-frontier / operator /
    ///   form-tile cells; leaves `self` unchanged.
    /// - provides: the head-cache adequacy witness hook.
    /// - fails: never (test-only assertion).
    /// - panics: on any cache/scan divergence (the test failure signal).
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every mutation class (push, splice-reduce, form
    ///   open/close flips, rollback, checkpoint resume) is crossed with the
    ///   validator over real corpus-shaped token streams.
    /// - witness: `meld::tests::head_caches_match_a_fresh_scan_across_streams`
    #[cfg(test)]
    fn assert_head_caches_exact(&self)
    {
        let mut frontiers = Vec::new();
        let mut operators = Vec::new();
        let mut barriers = Vec::new();
        for (index, cell) in self.stack.iter().enumerate() {
            match cell.role {
                | Role::FormTile { open, .. } => {
                    barriers.push(index);
                    if open {
                        frontiers.push(index);
                    }
                },
                | Role::Operator { .. } => operators.push(index),
                | Role::Operand => {},
            }
        }
        assert_eq!(self.frontiers, frontiers, "open-frontier cache is exact");
        assert_eq!(self.operators, operators, "operator cache is exact");
        assert_eq!(self.barriers, barriers, "form-tile cache is exact");
    }

    /// Replace the slope range `[low, high)` with a single cell.
    ///
    /// Every caller reduces a top region (`high == stack.len()`), so the head
    /// caches are maintained by dropping the removed range's indices and
    /// re-indexing the replacement at `low`.
    ///
    /// # Specification
    /// trivial.
    fn replace_range(
        &mut self,
        range: StackRange,
        cell: Cell,
    )
    {
        let low = usize::from(range.low);
        let high = usize::from(range.high_exclusive);
        if low >= high || high > self.stack.len() {
            // Defensive: never touched on the well-formed path; keep total.
            self.push_cell(cell);
            return;
        }
        self.unindex_from(StackFloor::from(range.low));
        let _drained: Vec<Cell> = self
            .stack
            .splice(low .. high, core::iter::once(cell))
            .collect();
        // The replacement landed at `low`; cells above `high` shifted down,
        // but every caller splices a top region, so none exist. Defensive:
        // if any survived, rebuild rather than corrupt the caches.
        if low.checked_add(1) == Some(self.stack.len()) {
            if let Some(replacement) = self.stack.get(low).copied() {
                self.index_cell(StackIndex::from(low), &replacement);
            }
        }
        else {
            self.rebuild_head_caches();
        }
    }

    /// Push an unmolded token: a total fallback for an out-of-range mold.
    ///
    /// # Specification
    /// trivial.
    fn push_unmolded(
        &mut self,
        text: SourceFragment<'_>,
    )
    {
        let span = self.append_source(text);
        let emit = self.emit_token(
            NodeLabel::Grout {
                sort: Sort::Item.grout_sort(),
                shape: GroutShape::Convex,
            },
            span,
        );
        self.flag(Oblig::UnmoldedTok, span);
        self.push_cell(Cell {
            emit,
            start: u32::from(span.start),
            end: u32::from(span.end),
            sort: Sort::Item,
            role: Role::Operand,
        });
    }

    /// Convert a parser buffer count to its `u32` wire offset.
    ///
    /// # Specification
    /// - ensures: returns `count` exactly when it fits the `u32` wire ceiling;
    ///   saturates at `u32::MAX` beyond it (parser buffers never approach 4
    ///   GiB; a `debug_assert` records the invariant).
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every source append and emission routes through the
    ///   conversion on ordinary inputs; the saturating arm is unreachable in
    ///   practice.
    /// - witness: `tests::acceptance::corpus_parses_totally`
    fn wire_len<T>(count: CheckpointCount) -> T
    where
        T: From<u32>,
    {
        let len = usize::from(count);
        debug_assert!(
            u32::try_from(len).is_ok(),
            "parser buffer length exceeds the u32 wire ceiling"
        );
        T::from(u32::try_from(len).unwrap_or(u32::MAX))
    }

    /// Append `text` to the source buffer and return its span.
    ///
    /// # Specification
    /// trivial.
    fn append_source(
        &mut self,
        text: SourceFragment<'_>,
    ) -> SourceSpan
    {
        let start = Self::wire_len(CheckpointCount::from(self.source.len()));
        self.source.push_str(<&str>::from(text));
        let end = Self::wire_len(CheckpointCount::from(self.source.len()));
        SourceSpan::new(start, end)
    }

    /// Append a leaf to the emission log and return its id.
    ///
    /// # Specification
    /// trivial.
    fn emit_token(
        &mut self,
        label: NodeLabel,
        span: SourceSpan,
    ) -> EmitId
    {
        let id = EmitId(Self::wire_len(CheckpointCount::from(self.emit.len())));
        self.emit.push(EmitOp::Token {
            label,
            start: u32::from(span.start),
            end: u32::from(span.end),
        });
        id
    }

    /// Append an interior node to the emission log and return its id.
    ///
    /// # Specification
    /// trivial.
    fn emit_interior(
        &mut self,
        label: NodeLabel,
        span: SourceSpan,
        children: Vec<EmitId>,
    ) -> EmitId
    {
        let id = EmitId(Self::wire_len(CheckpointCount::from(self.emit.len())));
        self.emit.push(EmitOp::Interior {
            label,
            start: u32::from(span.start),
            end: u32::from(span.end),
            children,
        });
        id
    }

    /// Record an obligation instance at a source span.
    ///
    /// # Specification
    /// trivial.
    fn flag(
        &mut self,
        class: Oblig,
        span: SourceSpan,
    )
    {
        if let Ok(span) = span.byte_span() {
            self.obligations.push(ObligationInstance::new(class, span));
        }
    }

    /// Return the buffered obligations, in accumulation order.
    ///
    /// # Specification
    /// - requires: none.
    /// - ensures: returns every obligation the melder has buffered so far, in
    ///   the order flagged.
    /// - provides: the query-surface data.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — a projection over the buffer; contents are witnessed
    ///   by the obligation tests.
    /// - witness: `meld::tests::degrout_flags_one_ambiguous_prec_at_the_smallest_span`
    #[inline]
    #[must_use]
    pub fn obligations(&self) -> &[ObligationInstance]
    {
        &self.obligations
    }

    /// Return the cumulative obligation [`Delta`] of the buffered obligations.
    ///
    /// # Specification
    /// - requires: none.
    /// - ensures: returns a delta whose per-class inserted counts equal the
    ///   buffered obligation counts (the melder only inserts obligations).
    /// - provides: the minimization key over the committed prefix.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a buffer with and without an `AmbiguousPrec` shifts
    ///   the delta at the maximum class.
    /// - witness: `meld::tests::delta_reflects_the_buffered_obligations`
    #[inline]
    #[must_use]
    pub fn delta(&self) -> Delta
    {
        let mut delta = Delta::empty();
        for obligation in &self.obligations {
            delta.insert(obligation.class);
        }
        delta
    }

    /// Return the completion to `⊢` the melder would insert if input ended
    /// here.
    ///
    /// This is `finalize` as a **query**: it computes the expected material
    /// (closers for open delimiters, holes for operators missing an operand)
    /// and the obligations closing would introduce, **without mutating** the
    /// committed parse. The scan reads each cell of the slope head as it
    /// stands, so it is a bound rather than a replay: an operator whose
    /// operand is a form still open counts a missing operand, which the
    /// commit's force-close then supplies by closing that form into the
    /// operand.
    ///
    /// # Specification
    /// - requires: none.
    /// - ensures: returns the expected material and would-introduce obligations
    ///   for the current slope; every obligation a commit from this state
    ///   inserts beyond the buffered ones is among them, and their only excess
    ///   is [`Oblig::MissingMeld`]; leaves `self` unchanged.
    /// - provides: the REPL/TUI "expected next" surface and the molder's
    ///   per-candidate completion cost.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a state with an open bracket and one with a saturated
    ///   operator distinguish expected closers from expected holes, querying at
    ///   every prefix leaves the commit unchanged, and every token prefix of
    ///   the witnessed sources bounds its commit with a missing-operand excess
    ///   observed.
    /// - witness: `meld::tests::finalize_is_non_destructive`
    /// - witness: `tests::acceptance::expected_agrees_with_committed_finalize`
    #[inline]
    #[must_use]
    pub fn finalize(&self) -> Completion
    {
        let mut expected: Vec<Expected> = Vec::new();
        let mut obligations: Vec<ObligationInstance> = Vec::new();
        let mut index = self.stack.len();
        while let Some(next_index) = index.checked_sub(1) {
            index = next_index;
            let Some(cell) = self.stack.get(index).copied()
            else {
                break;
            };
            match cell.role {
                | Role::FormTile {
                    mold, open: true, ..
                } => {
                    // A completable frontier (a `?` hole before its optional
                    // `hole_name`, mold in the grammar's LAST set) is already a
                    // complete form: commit closes it cleanly, so `finalize`
                    // reports neither an expected tile nor an obligation for it
                    // — mirroring `force_close_form`.
                    if bool::from(FormTable::is_form_last(self.pbg, mold)) {
                        continue;
                    }
                    // A required-tail frontier whose tail is one form already
                    // under way — a single operand, or an inner form starting
                    // right above it — closes cleanly once commit has collapsed
                    // that form: no tile is expected and no obligation is its
                    // own, mirroring `force_close_form`.
                    if bool::from(self.tail_is_under_way(FrontierIndex::from(index), mold)) {
                        continue;
                    }
                    // An open form frontier expects its `≐`-continuation; commit
                    // force-closes it with a ghost end and a MissingTile.
                    if let Some(succ) = self.first_successor(mold)
                        && let Ok(def) = self.pbg.mold(succ)
                    {
                        expected.push(Expected::Tile(def.label));
                    }
                    let frontier = SourceSpan::new(
                        SourceOffset::from(cell.start),
                        SourceOffset::from(cell.end),
                    );
                    if let Ok(span) = frontier.byte_span() {
                        obligations.push(ObligationInstance::new(Oblig::MissingTile, span));
                    }
                },
                | Role::Operator { sort, shape, .. } => {
                    let wants_right = matches!(shape, OpShape::Infix | OpShape::Prefix);
                    let right_filled = index
                        .checked_add(1)
                        .is_some_and(|next| bool::from(self.is_operand_at(StackIndex::from(next))));
                    if wants_right && !right_filled {
                        expected.push(Expected::Hole(sort));
                        if let Ok(span) =
                            SourceSpan::point(SourceOffset::from(cell.end)).byte_span()
                        {
                            obligations.push(ObligationInstance::new(Oblig::MissingMeld, span));
                        }
                    }
                    // An infix / postfix operator with no left operand is a
                    // completion obligation too — this is the signal that lets
                    // the molder read `-` at expression start as prefix (which
                    // needs no left) rather than infix (which does).
                    let wants_left = matches!(shape, OpShape::Infix | OpShape::Postfix);
                    let left_filled = index
                        .checked_sub(1)
                        .is_some_and(|prev| bool::from(self.is_operand_at(StackIndex::from(prev))));
                    if wants_left
                        && !left_filled
                        && let Ok(span) =
                            SourceSpan::point(SourceOffset::from(cell.start)).byte_span()
                    {
                        obligations.push(ObligationInstance::new(Oblig::MissingMeld, span));
                    }
                },
                | Role::FormTile { open: false, .. } | Role::Operand => {},
            }
        }
        Completion {
            expected,
            obligations,
        }
    }

    /// Return the ordered completion to `⊢` — "what is expected here".
    ///
    /// This is the interaction-surface name for
    /// [`finalize`](MeldState::finalize): the ordered material (tiles / holes
    /// with sorts) that would close the input at this prefix, with the
    /// obligations that closing would introduce. It is a non-destructive query
    /// over the slope — the open frontiers and unsaturated operators — never
    /// the emission log, so its cost does not grow with the text already
    /// closed: the REPL/TUI/LSP "expected next" surface.
    ///
    /// # Specification
    /// - requires: none.
    /// - ensures: returns exactly [`finalize`](MeldState::finalize)'s
    ///   completion; leaves `self` unchanged.
    /// - provides: the completion query, bounding what a commit inserts as
    ///   [`finalize`](MeldState::finalize) states.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every token prefix of the witnessed sources bounds
    ///   its commit, with the missing-operand excess observed.
    /// - witness: `tests::acceptance::expected_agrees_with_committed_finalize`
    #[inline]
    #[must_use]
    pub fn expected(&self) -> Completion
    {
        self.finalize()
    }

    /// Commit the parse: close the input and build the molded
    /// [`SyntaxTree`] over `source`.
    ///
    /// `commit` is the destructive companion of
    /// [`finalize`](MeldState::finalize): it collapses the slope to `⊢`
    /// (reducing every operator, force-closing every open delimiter with
    /// grout) and wraps the top-level operands in a single root, then
    /// replays the append-only emission log into a [`TreeBuilder`] recording
    /// the grammar fingerprint.
    ///
    /// # Specification
    /// - requires: none.
    /// - ensures: returns a well-formed [`SyntaxTree`] over `source` whose root
    ///   spans it and whose grammar is the melder's grammar fingerprint.
    /// - provides: the batch tree — the derived fold's final step.
    /// - fails: when `source` is not the text the melder assembled from its
    ///   pushes, or for an arena-construction failure.
    /// - panics: none.
    ///
    /// # Errors
    /// [`MeldError::SourceMismatch`] when `source` differs from the assembled
    /// text; [`MeldError::Build`] when the flat arena cannot be assembled.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty input, a single atom, a nested bracket, and an
    ///   infix chain each build a distinct well-formed root; a source that is
    ///   not the assembled text is refused.
    /// - witness: `meld::tests::single_atom_commits_to_one_token`
    /// - witness: `meld::tests::empty_state_commits_to_a_root`
    #[inline]
    pub fn commit(
        self,
        source: SourceText<'_>,
    ) -> Result<SyntaxTree<'_>, MeldError>
    {
        let (tree, _obligations) = self.commit_with_obligations(source)?;
        Ok(tree)
    }

    /// Commit the parse and return the tree alongside the final obligations.
    ///
    /// Closing the input flags the completion's repairs — force-closing an
    /// unfinished form ([`Oblig::MissingTile`]), filling a saturated operator's
    /// missing operand ([`Oblig::MissingMeld`]) — so those obligations exist
    /// only after `collapse`. [`commit`](MeldState::commit) alone drops them
    /// (it consumes `self`); the batch driver reads them here so the
    /// [`crate::ParseResult`] carries the whole obligation set, streaming plus
    /// completion.
    ///
    /// # Specification
    /// - requires: none.
    /// - ensures: returns the well-formed [`SyntaxTree`] over `source` and the
    ///   obligation buffer after closing the input (streaming obligations plus
    ///   the completion's).
    /// - provides: the obligation-complete batch commit.
    /// - fails: as [`commit`](MeldState::commit).
    /// - panics: none.
    ///
    /// # Errors
    /// As [`commit`](MeldState::commit).
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a clean parse (empty completion) and an incomplete
    ///   one (force-close obligations) distinguish the returned obligation set.
    /// - witness: `tests::acceptance::incomplete_input_flags_statement_local_obligations`
    /// - witness: `meld::tests::a_foreign_source_is_refused_at_commit`
    #[inline]
    pub fn commit_with_obligations(
        mut self,
        source: SourceText<'_>,
    ) -> Result<(SyntaxTree<'_>, Vec<ObligationInstance>), MeldError>
    {
        if <&str>::from(source) != self.source.as_str() {
            return Err(MeldError::SourceMismatch);
        }
        self.collapse(StackFloor::from(StackIndex::from(0)));
        let obligations = self.obligations.clone();
        let root = self.wrap_root();
        let tree = self.build_tree(source, root)?;
        Ok((tree, obligations))
    }

    /// Wrap the fully collapsed slope's operands into a single root interior.
    ///
    /// # Specification
    /// trivial.
    fn wrap_root(&mut self) -> EmitId
    {
        // Collect the top-level operands and the floating layout-space tokens,
        // ordered by source start so the root children reconstruct the source
        // in order (layout is digest-skipped, so ordering is a losslessness,
        // not an identity, concern).
        let mut ordered: Vec<(SourceOffset, EmitId)> = Vec::with_capacity(self.stack.len());
        let mut span_end = SourceOffset::from(0);
        for cell in &self.stack {
            let start = SourceOffset::from(cell.start);
            ordered.push((start, cell.emit));
            span_end = span_end.max(SourceOffset::from(cell.end));
        }
        for &space in &self.spaces {
            let start = self.emit_start(space);
            ordered.push((start, space));
        }
        ordered.sort_by_key(|&(start, _)| start);
        let children: Vec<EmitId> = ordered.into_iter().map(|(_, emit)| emit).collect();
        let source_end: SourceOffset = Self::wire_len(CheckpointCount::from(self.source.len()));
        self.emit_interior(
            NodeLabel::Wald,
            SourceSpan::new(SourceOffset::from(0), source_end.max(span_end)),
            children,
        )
    }

    /// Return the source start of an emission-log entry (0 if out of range).
    ///
    /// # Specification
    /// trivial.
    fn emit_start(
        &self,
        id: EmitId,
    ) -> SourceOffset
    {
        let Ok(index) = usize::try_from(id.0)
        else {
            return SourceOffset::from(0);
        };
        match self.emit.get(index) {
            | Some(&EmitOp::Token { start, .. } | &EmitOp::Interior { start, .. }) => {
                SourceOffset::from(start)
            },
            | None => SourceOffset::from(0),
        }
    }

    /// Replay the emission log into a checked [`TreeBuilder`] over `source`
    /// and finish at `root`.
    ///
    /// # Specification
    /// - requires: `source` is the assembled text, which
    ///   [`commit`](Self::commit) checks first.
    /// - ensures: the tree's root is `root`'s node, and every log entry
    ///   reachable from it is a node of the tree.
    /// - fails: the builder refuses a node, or the log names an id outside
    ///   itself.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`MeldError::Build`] when the tree builder refuses a node.
    /// - [`MeldError::Corrupt`] when the log names an id outside itself.
    fn build_tree<'source>(
        &self,
        source: SourceText<'source>,
        root: EmitId,
    ) -> Result<SyntaxTree<'source>, MeldError>
    {
        let mut builder = TreeBuilder::new(source, self.pbg.fingerprint())?;
        let mut mapping: Vec<StagedId> = Vec::with_capacity(self.emit.len());
        let mut child_nodes: Vec<StagedId> = Vec::new();
        for op in &self.emit {
            let node = match *op {
                | EmitOp::Token { label, start, end } => {
                    let span = SourceSpan::new(SourceOffset::from(start), SourceOffset::from(end))
                        .byte_span()?;
                    builder.node(label, span, &[])?
                },
                | EmitOp::Interior {
                    label,
                    start,
                    end,
                    ref children,
                } => {
                    child_nodes.clear();
                    for child in children {
                        let index =
                            usize::try_from(child.0).map_err(|_error| MeldError::Corrupt)?;
                        let mapped = mapping.get(index).copied().ok_or(MeldError::Corrupt)?;
                        child_nodes.push(mapped);
                    }
                    let span = SourceSpan::new(SourceOffset::from(start), SourceOffset::from(end))
                        .byte_span()?;
                    builder.node(label, span, &child_nodes)?
                },
            };
            mapping.push(node);
        }
        let root_index = usize::try_from(root.0).map_err(|_error| MeldError::Corrupt)?;
        let root_node = mapping.get(root_index).copied().ok_or(MeldError::Corrupt)?;
        let tree = builder.finish(root_node)?;
        Ok(tree)
    }

    /// Capture a serializable snapshot of the current state.
    ///
    /// # Specification
    /// - requires: none.
    /// - ensures: returns a first-order snapshot of the slope, emission log,
    ///   source, obligations, and grammar fingerprint; leaves `self` unchanged.
    /// - provides: the REPL/streaming continuation and prefix-acceptance probe
    ///   state; the append-only log makes it cheap.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — checkpoint then resume reproduces the exact
    ///   continuation, byte-round-trip included.
    /// - witness: `meld::tests::checkpoint_resume_is_equivalent`
    #[inline]
    #[must_use]
    pub fn checkpoint(&self) -> Checkpoint
    {
        Checkpoint {
            fingerprint: self.pbg.fingerprint(),
            source: self.source.clone(),
            emit: self.emit.clone(),
            stack: self.stack.clone(),
            obligations: self.obligations.clone(),
            spaces: self.spaces.clone(),
        }
    }

    /// Resume a melder from a checkpoint over `pbg`, an identical continuation.
    ///
    /// # Specification
    /// - requires: `cp` was captured over a grammar with `pbg`'s fingerprint.
    /// - ensures: returns a state whose subsequent pushes are identical to the
    ///   run the checkpoint was taken from; the bracket table is rebuilt from
    ///   `pbg`.
    /// - provides: the resume side of the streaming continuation.
    /// - fails: never; a fingerprint mismatch yields a state over `pbg`'s table
    ///   (the caller's responsibility to pair correctly — see
    ///   [`Checkpoint::fingerprint`]).
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — resume plus remaining pushes equals the uninterrupted
    ///   run.
    /// - witness: `meld::tests::checkpoint_resume_is_equivalent`
    #[inline]
    #[must_use]
    pub fn resume(
        pbg: &'pbg Pbg,
        cp: &Checkpoint,
    ) -> Self
    {
        let mut state = Self {
            pbg,
            source: cp.source.clone(),
            emit: cp.emit.clone(),
            stack: cp.stack.clone(),
            frontiers: Vec::new(),
            operators: Vec::new(),
            barriers: Vec::new(),
            obligations: cp.obligations.clone(),
            spaces: cp.spaces.clone(),
        };
        state.rebuild_head_caches();
        state
    }

    /// Record a layout-space token for losslessness.
    ///
    /// Trivia (whitespace, comments, shebangs) carry no syntactic weight — the
    /// content digest skips [`NodeLabel::Space`] — but the batch driver records
    /// them so the committed [`SyntaxTree`] reconstructs the source
    /// byte-for-byte. Space tokens float free of the slope and become root
    /// children at [`commit`](MeldState::commit).
    ///
    /// # Specification
    /// - requires: `text` is the trivia's exact surface bytes, in source order.
    /// - ensures: appends a space token to the emission log; the slope,
    ///   obligations, and digest are unchanged.
    /// - provides: the losslessness seam for the labeler's
    ///   [`Lexeme::Space`](crate::Lexeme::Space) tokens.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a parse with interleaved trivia reconstructs the
    ///   exact source and digests identically to the trivia-free parse.
    /// - witness: `parse::tests::parse_is_lossless_and_hash_stable`
    #[inline]
    pub fn space(
        &mut self,
        text: SpaceText<'_>,
    )
    {
        let span = self.append_source(SourceFragment::from(text));
        let emit = self.emit_token(NodeLabel::Space, span);
        self.spaces.push(emit);
    }

    /// Open a lightweight in-place transaction over the current state.
    ///
    /// A [`Mark`] snapshots the append-only log lengths (source, emission,
    /// obligations) and the small first-order slope, so
    /// [`rollback_to`](MeldState::rollback_to) restores the state by truncating
    /// the appended tails and reinstating the slope — **without** cloning the
    /// (arbitrarily long) emission log the way
    /// [`checkpoint`](MeldState::checkpoint) does. This is the molder's
    /// per-candidate transaction: the molder marks once, dry-runs a candidate
    /// push, reads the candidate's
    /// obligation [`delta_since`](MeldState::delta_since), and rolls back —
    /// reusing buffers across candidates rather than paying a full
    /// checkpoint clone per candidate.
    ///
    /// # Specification
    /// - requires: none.
    /// - ensures: returns a snapshot of the log lengths and slope; leaves
    ///   `self` unchanged.
    /// - provides: the open side of the candidate dry-run transaction.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a mark, a candidate push, and a rollback restore the
    ///   pre-push state exactly (byte, slope, and obligation identical).
    /// - witness: `meld::tests::mark_rollback_restores_state_exactly`
    #[inline]
    #[must_use]
    pub fn mark(&self) -> Mark
    {
        Mark {
            source_len: self.source.len(),
            emit_len: self.emit.len(),
            oblig_len: self.obligations.len(),
            spaces_len: self.spaces.len(),
            stack: self.stack.clone(),
            frontiers: self.frontiers.clone(),
            operators: self.operators.clone(),
            barriers: self.barriers.clone(),
        }
    }

    /// Fill `mark` with the current state, reusing its buffers.
    ///
    /// The allocation-free twin of [`mark`](MeldState::mark): `clone_from`
    /// reuses the mark's existing slope / cache capacity, so a caller that
    /// pools marks (the molder's per-candidate dry-run loop) reaches a
    /// zero-allocation steady state instead of four fresh vector allocations
    /// per candidate.
    ///
    /// # Specification
    /// - requires: none.
    /// - ensures: `mark` compares equal to what [`mark`](MeldState::mark) would
    ///   return; `self` is unchanged.
    /// - provides: the pooled-mark fast path for dry-run transactions.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a rollback through a pooled mark restores the exact
    ///   pre-push state, byte-for-byte with the allocating path.
    /// - witness: `meld::tests::mark_rollback_restores_state_exactly`
    /// - witness: `meld::tests::head_caches_match_a_fresh_scan_across_streams`
    #[inline]
    pub fn mark_into(
        &self,
        mark: &mut Mark,
    )
    {
        mark.source_len = self.source.len();
        mark.emit_len = self.emit.len();
        mark.oblig_len = self.obligations.len();
        mark.spaces_len = self.spaces.len();
        mark.stack.clone_from(&self.stack);
        mark.frontiers.clone_from(&self.frontiers);
        mark.operators.clone_from(&self.operators);
        mark.barriers.clone_from(&self.barriers);
    }

    /// Roll the state back to `mark`, discarding everything appended since.
    ///
    /// # Specification
    /// - requires: `mark` was taken from this same state, and only append-only
    ///   growth (pushes) happened since — the molder's marked candidate loop.
    /// - ensures: truncates the source, emission log, and obligation buffer to
    ///   their marked lengths and restores the marked slope, so the state is
    ///   bytewise identical to the mark.
    /// - provides: the close side of the candidate dry-run transaction.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — rollback after a push reproduces the marked state and
    ///   a fresh push over it is identical to one without the dry-run.
    /// - witness: `meld::tests::mark_rollback_restores_state_exactly`
    #[inline]
    pub fn rollback_to(
        &mut self,
        mark: &Mark,
    )
    {
        self.source.truncate(mark.source_len);
        self.emit.truncate(mark.emit_len);
        self.obligations.truncate(mark.oblig_len);
        self.spaces.truncate(mark.spaces_len);
        self.stack.clone_from(&mark.stack);
        self.frontiers.clone_from(&mark.frontiers);
        self.operators.clone_from(&mark.operators);
        self.barriers.clone_from(&mark.barriers);
    }

    /// Return the obligation [`Delta`] accumulated since `mark`.
    ///
    /// This is the candidate's own obligation change — the minimization key the
    /// molder compares across candidates — read from the obligation buffer tail
    /// appended since the mark, never a whole-buffer traversal.
    ///
    /// # Specification
    /// - requires: `mark` was taken from this state and no rollback has
    ///   occurred since (the read happens between the dry-run push and its
    ///   rollback).
    /// - ensures: returns a delta whose per-class inserted counts equal the
    ///   obligations flagged since `mark`.
    /// - provides: the molder's per-candidate minimization key.
    /// - fails: never; a stale mark (buffer already shorter) yields the empty
    ///   delta.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a candidate that flags an obligation and one that
    ///   does not separate the delta.
    /// - witness: `meld::tests::delta_since_reads_only_the_candidate_tail`
    #[inline]
    #[must_use]
    pub fn delta_since(
        &self,
        mark: &Mark,
    ) -> Delta
    {
        let mut delta = Delta::empty();
        if let Some(tail) = self.obligations.get(mark.oblig_len ..) {
            for obligation in tail {
                delta.insert(obligation.class);
            }
        }
        delta
    }
}

/// The head context the candidate pre-filter reads, hoisted out of the
/// per-candidate loop.
///
/// Computed once per token by
/// [`admissibility_frontier`](MeldState::admissibility_frontier) and consumed
/// by [`admits_at`](MeldState::admits_at) for every candidate, so the wide
/// identifier menu costs `O(menu + depth)` rather than `O(menu × depth)`.
///
/// # Specification
/// - requires: paired with the [`MeldState`] it was computed from, before any
///   mutation.
/// - ensures: carries the nearest open form frontier mold and the
///   head-is-operand flag exactly.
/// - provides: the constant admissibility context.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L1 — a two-field snapshot; witnessed through `admits_at`.
/// - witness: `meld::tests::admits_rejects_a_stray_closer`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Frontier
{
    /// The nearest open form frontier's mold, if any.
    pub open: Option<MoldId>,
    /// Whether the slope head is a completed operand.
    pub head_operand: HeadOperandPresence,
    /// The sort of the head operand cell, if the head is an operand — the sort
    /// a left-absorbing form-start (a call, an instantiation) must match to
    /// apply.
    pub head_sort: Option<Sort>,
    /// The sort the head's open operand slot expects (the hole-sort check): an
    /// operand candidate of a different sort would fill a hole of the wrong
    /// sort (a local `InconMeld`), so the pre-filter discards it before any
    /// dry-run.
    pub expected: Sort,
}

/// A lightweight in-place transaction snapshot of a [`MeldState`].
///
/// A `Mark` records the append-only log lengths and the small first-order slope
/// at [`mark`](MeldState::mark) time; [`rollback_to`](MeldState::rollback_to)
/// restores them. Unlike a [`Checkpoint`], it does not clone the emission log,
/// so the molder's candidate loop pays only a slope clone per mark.
///
/// # Specification
/// - requires: used only against the state it was marked from, before any
///   non-append mutation.
/// - ensures: carries exactly the marked source, emission, and obligation
///   lengths and the marked slope.
/// - provides: the candidate dry-run transaction token.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L1 — a snapshot record; behavior is witnessed by the
///   mark/rollback test.
/// - witness: `meld::tests::mark_rollback_restores_state_exactly`
///
/// The `Default` mark is an empty pool slot for
/// [`mark_into`](MeldState::mark_into) — never a valid rollback target until
/// filled.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Mark
{
    /// Assembled source length at mark time.
    source_len: usize,
    /// Emission-log length at mark time.
    emit_len: usize,
    /// Obligation-buffer length at mark time.
    oblig_len: usize,
    /// Floating-space-list length at mark time.
    spaces_len: usize,
    /// The slope of terraces at mark time.
    stack: Vec<Cell>,
    /// The open-frontier index cache at mark time.
    frontiers: Vec<usize>,
    /// The operator index cache at mark time.
    operators: Vec<usize>,
    /// The form-tile index cache at mark time.
    barriers: Vec<usize>,
}

/// One expected item in a completion to `⊢`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Expected
{
    /// An expected literal tile, named by its label.
    Tile(&'static str),
    /// An expected recursive-sort hole.
    Hole(Sort),
    /// An expected grout of the given shape.
    Grout(GroutShape),
}

/// The completion the melder would insert to close the input at a prefix.
///
/// # Specification
/// - requires: none.
/// - ensures: preserves the expected material and would-introduce obligations
///   computed by [`MeldState::finalize`].
/// - provides: the "expected next" query result; it is non-empty exactly when
///   the input is not yet complete.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a complete and an incomplete prefix distinguish an empty
///   completion from a non-empty one.
/// - witness: `meld::tests::finalize_is_non_destructive`
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Completion
{
    /// The expected material to reach `⊢`, from the head down.
    expected: Vec<Expected>,
    /// The obligations closing the input would introduce.
    obligations: Vec<ObligationInstance>,
}

impl Completion
{
    /// Return the expected material to close the input.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn expected(&self) -> &[Expected]
    {
        &self.expected
    }

    /// Return the obligations closing the input would introduce.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn obligations(&self) -> &[ObligationInstance]
    {
        &self.obligations
    }

    /// Return whether the input is already complete (no expected material).
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn is_complete(&self) -> CompletionStatus
    {
        CompletionStatus::from(self.expected.is_empty())
    }
}

/// A failure while committing the melder to a [`SyntaxTree`].
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum MeldError
{
    /// The flat arena could not be assembled.
    Build(SyntaxError),
    /// The source offered at commit is not the text the melder assembled
    /// from its pushes.
    SourceMismatch,
    /// The emission log referenced an id outside itself (never on the
    /// well-formed path).
    Corrupt,
}

impl fmt::Display for MeldError
{
    /// Describe the commit failure in prose.
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
            | Self::Build(ref error) => fmt::Display::fmt(error, f),
            | Self::SourceMismatch => {
                f.write_str("the source offered at commit is not the text the melder assembled")
            },
            | Self::Corrupt => f.write_str("emission log referenced an out-of-range id"),
        }
    }
}

impl Error for MeldError
{
    /// Return the tree builder's error when it caused the failure.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn source(&self) -> Option<&(dyn Error + 'static)>
    {
        match *self {
            | Self::Build(ref error) => Some(error),
            | Self::SourceMismatch | Self::Corrupt => None,
        }
    }
}

impl From<SyntaxError> for MeldError
{
    /// Wrap a tree builder refusal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: SyntaxError) -> Self
    {
        Self::Build(value)
    }
}

/// A failure while decoding a serialized [`Checkpoint`].
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CheckpointError
{
    /// The byte stream ended before a field was fully read.
    Truncated,
    /// A discriminant tag was outside its closed vocabulary.
    BadTag
    {
        /// The offending tag byte.
        tag: u8,
    },
    /// A decoded value violated a structural invariant (e.g. a text range).
    Malformed,
}

impl fmt::Display for CheckpointError
{
    /// Describe the decoding failure in prose.
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
            | Self::Truncated => f.write_str("checkpoint byte stream is truncated"),
            | Self::BadTag { tag } => write!(f, "checkpoint has an unknown discriminant tag {tag}"),
            | Self::Malformed => f.write_str("checkpoint content is malformed"),
        }
    }
}

impl Error for CheckpointError
{
}

/// A serializable, first-order snapshot of a [`MeldState`].
///
/// The snapshot holds the assembled source, the append-only emission log, the
/// slope, the buffered obligations, and the grammar fingerprint — everything
/// except the borrowed `Pbg`. [`Checkpoint::to_bytes`] /
/// [`Checkpoint::from_bytes`] give a self-contained binary encoding without a
/// serialization dependency, so a REPL can persist and restore session state.
///
/// # Specification
/// - requires: [`from_bytes`](Checkpoint::from_bytes) input came from
///   [`to_bytes`](Checkpoint::to_bytes).
/// - ensures: `from_bytes(to_bytes(c)) == c`; the fingerprint identifies the
///   grammar the snapshot is valid against.
/// - provides: the persistable continuation state.
/// - fails: [`from_bytes`](Checkpoint::from_bytes) returns [`CheckpointError`]
///   for truncated, mis-tagged, or malformed input.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a non-trivial parse round-trips through bytes and resumes
///   equivalently; truncated input fails closed.
/// - witness: `meld::tests::checkpoint_resume_is_equivalent`
/// - witness: `meld::tests::checkpoint_bytes_round_trip`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Checkpoint
{
    /// The grammar fingerprint the snapshot is valid against.
    fingerprint: GrammarFingerprint,
    /// The assembled source buffer.
    source: String,
    /// The append-only emission log.
    emit: Vec<EmitOp>,
    /// The slope of terraces.
    stack: Vec<Cell>,
    /// The buffered obligations.
    obligations: Vec<ObligationInstance>,
    /// The floating layout-space tokens (root children at commit).
    spaces: Vec<EmitId>,
}

impl Checkpoint
{
    /// Return the grammar fingerprint this snapshot is valid against.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn fingerprint(&self) -> GrammarFingerprint
    {
        self.fingerprint
    }

    /// Encode the checkpoint as a self-contained little-endian byte stream.
    ///
    /// # Specification
    /// - requires: none.
    /// - ensures: returns a byte stream that
    ///   [`from_bytes`](Checkpoint::from_bytes) decodes back to an equal
    ///   checkpoint.
    /// - provides: the serialization side of the round trip (no serde
    ///   dependency).
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — a deterministic encoder; the round trip is witnessed.
    /// - witness: `meld::tests::checkpoint_bytes_round_trip`
    #[inline]
    #[must_use]
    pub fn to_bytes(&self) -> CheckpointBytes
    {
        let mut writer = Writer { bytes: Vec::new() };
        writer.u64(WireU64::from(u64::from(self.fingerprint)));
        writer.blob(ByteChunk::from(self.source.as_bytes()));
        writer.len(CheckpointCount::from(self.emit.len()));
        for op in &self.emit {
            write_emit_op(&mut writer, op);
        }
        writer.len(CheckpointCount::from(self.stack.len()));
        for cell in &self.stack {
            write_cell(&mut writer, *cell);
        }
        writer.len(CheckpointCount::from(self.obligations.len()));
        for obligation in &self.obligations {
            write_obligation(&mut writer, *obligation);
        }
        writer.len(CheckpointCount::from(self.spaces.len()));
        for space in &self.spaces {
            writer.u32(WireU32::from(space.0));
        }
        CheckpointBytes::from(writer.bytes)
    }

    /// Decode a checkpoint from a byte stream produced by
    /// [`to_bytes`](Checkpoint::to_bytes).
    ///
    /// # Specification
    /// - requires: `bytes` came from [`to_bytes`](Checkpoint::to_bytes) for the
    ///   same crate revision.
    /// - ensures: returns the encoded checkpoint on well-formed input.
    /// - provides: the deserialization side of the round trip.
    /// - fails: returns [`CheckpointError`] for truncated, mis-tagged, or
    ///   malformed input.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`CheckpointError::Truncated`], [`CheckpointError::BadTag`], or
    /// [`CheckpointError::Malformed`] for an ill-formed stream.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the round trip and truncated/mis-tagged inputs are
    ///   distinguished.
    /// - witness: `meld::tests::checkpoint_bytes_round_trip`
    #[inline]
    pub fn from_bytes(bytes: CheckpointBytesRef<'_>) -> Result<Self, CheckpointError>
    {
        let mut reader = Reader { bytes, pos: 0 };
        let wire_fingerprint = reader.u64()?;
        let fingerprint = GrammarFingerprint::from(u64::from(wire_fingerprint));
        let source_bytes = reader.blob()?;
        let source = String::from_utf8(source_bytes.as_ref().to_vec())
            .map_err(|_error| CheckpointError::Malformed)?;
        let wire_emit_len = reader.len()?;
        let emit_len = usize::from(wire_emit_len);
        let mut emit = Vec::with_capacity(emit_len);
        for _ in 0 .. emit_len {
            let op = read_emit_op(&mut reader)?;
            emit.push(op);
        }
        let wire_stack_len = reader.len()?;
        let stack_len = usize::from(wire_stack_len);
        let mut stack = Vec::with_capacity(stack_len);
        for _ in 0 .. stack_len {
            let cell = read_cell(&mut reader)?;
            stack.push(cell);
        }
        let wire_oblig_len = reader.len()?;
        let oblig_len = usize::from(wire_oblig_len);
        let mut obligations = Vec::with_capacity(oblig_len);
        for _ in 0 .. oblig_len {
            let obligation = read_obligation(&mut reader)?;
            obligations.push(obligation);
        }
        let wire_spaces_len = reader.len()?;
        let spaces_len = usize::from(wire_spaces_len);
        let mut spaces = Vec::with_capacity(spaces_len);
        for _ in 0 .. spaces_len {
            let space = reader.u32()?;
            spaces.push(EmitId(u32::from(space)));
        }
        Ok(Self {
            fingerprint,
            source,
            emit,
            stack,
            obligations,
            spaces,
        })
    }
}

/// A little-endian byte-stream writer for checkpoint serialization.
#[repr(transparent)]
struct Writer
{
    /// The accumulated bytes.
    bytes: Vec<u8>,
}

impl Writer
{
    /// Write one byte.
    ///
    /// # Specification
    /// trivial.
    fn u8(
        &mut self,
        value: WireByte,
    )
    {
        self.bytes.push(u8::from(value));
    }

    /// Write a little-endian `u16`.
    ///
    /// # Specification
    /// trivial.
    fn u16(
        &mut self,
        value: WireU16,
    )
    {
        self.bytes
            .extend_from_slice(&u16::from(value).to_le_bytes());
    }

    /// Write a little-endian `u32`.
    ///
    /// # Specification
    /// trivial.
    fn u32(
        &mut self,
        value: WireU32,
    )
    {
        self.bytes
            .extend_from_slice(&u32::from(value).to_le_bytes());
    }

    /// Write a little-endian `u64`.
    ///
    /// # Specification
    /// trivial.
    fn u64(
        &mut self,
        value: WireU64,
    )
    {
        self.bytes
            .extend_from_slice(&u64::from(value).to_le_bytes());
    }

    /// Write a length as a `u64`.
    ///
    /// # Specification
    /// trivial.
    fn len(
        &mut self,
        value: CheckpointCount,
    )
    {
        let value = u64::try_from(usize::from(value)).unwrap_or(u64::MAX);
        self.u64(WireU64::from(value));
    }

    /// Write a length-prefixed byte blob.
    ///
    /// # Specification
    /// trivial.
    fn blob(
        &mut self,
        value: ByteChunk<'_>,
    )
    {
        let bytes = value.as_ref();
        self.len(CheckpointCount::from(bytes.len()));
        self.bytes.extend_from_slice(bytes);
    }
}

/// A little-endian byte-stream reader for checkpoint deserialization.
struct Reader<'bytes>
{
    /// The underlying byte stream.
    bytes: CheckpointBytesRef<'bytes>,
    /// The current read cursor.
    pos: usize,
}

impl Reader<'_>
{
    /// Read `count` bytes, advancing the cursor.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the cursor sits past exactly `count` bytes on success and is
    ///   unmoved on failure.
    /// - fails: fewer than `count` bytes remain.
    /// - panics: none.
    ///
    /// # Errors
    /// [`CheckpointError::Truncated`] when the stream ends early.
    fn take(
        &mut self,
        count: ByteCount,
    ) -> Result<ByteChunk<'_>, CheckpointError>
    {
        let count = usize::from(count);
        let end = self
            .pos
            .checked_add(count)
            .ok_or(CheckpointError::Truncated)?;
        let slice = self
            .bytes
            .as_ref()
            .get(self.pos .. end)
            .ok_or(CheckpointError::Truncated)?;
        self.pos = end;
        Ok(ByteChunk::from(slice))
    }

    /// Read one byte.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the cursor sits past the value on success and is unmoved on
    ///   failure.
    /// - fails: the stream ends before the value does.
    /// - panics: none.
    ///
    /// # Errors
    /// [`CheckpointError::Truncated`] when the stream ends early.
    fn u8(&mut self) -> Result<WireByte, CheckpointError>
    {
        let bytes = self.take(ByteCount::from(1))?;
        bytes
            .as_ref()
            .first()
            .copied()
            .map(WireByte::from)
            .ok_or(CheckpointError::Truncated)
    }

    /// Read a little-endian `u16`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the cursor sits past the value on success and is unmoved on
    ///   failure.
    /// - fails: the stream ends before the value does.
    /// - panics: none.
    ///
    /// # Errors
    /// [`CheckpointError::Truncated`] when the stream ends early.
    fn u16(&mut self) -> Result<WireU16, CheckpointError>
    {
        let slice = self.take(ByteCount::from(2))?;
        let array: [u8; 2] = slice
            .as_ref()
            .try_into()
            .map_err(|_error| CheckpointError::Truncated)?;
        Ok(WireU16::from(u16::from_le_bytes(array)))
    }

    /// Read a little-endian `u32`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the cursor sits past the value on success and is unmoved on
    ///   failure.
    /// - fails: the stream ends before the value does.
    /// - panics: none.
    ///
    /// # Errors
    /// [`CheckpointError::Truncated`] when the stream ends early.
    fn u32(&mut self) -> Result<WireU32, CheckpointError>
    {
        let slice = self.take(ByteCount::from(4))?;
        let array: [u8; 4] = slice
            .as_ref()
            .try_into()
            .map_err(|_error| CheckpointError::Truncated)?;
        Ok(WireU32::from(u32::from_le_bytes(array)))
    }

    /// Read a little-endian `u64`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the cursor sits past the value on success and is unmoved on
    ///   failure.
    /// - fails: the stream ends before the value does.
    /// - panics: none.
    ///
    /// # Errors
    /// [`CheckpointError::Truncated`] when the stream ends early.
    fn u64(&mut self) -> Result<WireU64, CheckpointError>
    {
        let slice = self.take(ByteCount::from(8))?;
        let array: [u8; 8] = slice
            .as_ref()
            .try_into()
            .map_err(|_error| CheckpointError::Truncated)?;
        Ok(WireU64::from(u64::from_le_bytes(array)))
    }

    /// Read a length previously written as a `u64`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the cursor sits past the decoded value.
    /// - fails: the stream ends early or carries a tag or length no well-formed
    ///   checkpoint holds.
    /// - panics: none.
    ///
    /// # Errors
    /// [`CheckpointError`] for a truncated or ill-formed stream.
    fn len(&mut self) -> Result<CheckpointCount, CheckpointError>
    {
        let wire_value = self.u64()?;
        let value = u64::from(wire_value);
        usize::try_from(value)
            .map(CheckpointCount::from)
            .map_err(|_error| CheckpointError::Malformed)
    }

    /// Read a length-prefixed byte blob.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the cursor sits past the decoded value.
    /// - fails: the stream ends early or carries a tag or length no well-formed
    ///   checkpoint holds.
    /// - panics: none.
    ///
    /// # Errors
    /// [`CheckpointError`] for a truncated or ill-formed stream.
    fn blob(&mut self) -> Result<ByteChunk<'_>, CheckpointError>
    {
        let count = self.len()?;
        self.take(ByteCount::from(usize::from(count)))
    }
}

/// Read an emission-log entry.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the cursor sits past the decoded value.
/// - fails: the stream ends early or carries a tag or length no well-formed
///   checkpoint holds.
/// - panics: none.
///
/// # Errors
/// [`CheckpointError`] for a truncated or ill-formed stream.
fn read_emit_op(reader: &mut Reader<'_>) -> Result<EmitOp, CheckpointError>
{
    let wire_tag = reader.u8()?;
    match u8::from(wire_tag) {
        | 0 => {
            let label = read_label(reader)?;
            let wire_start = reader.u32()?;
            let start = u32::from(wire_start);
            let wire_end = reader.u32()?;
            let end = u32::from(wire_end);
            Ok(EmitOp::Token { label, start, end })
        },
        | 1 => {
            let label = read_label(reader)?;
            let wire_start = reader.u32()?;
            let start = u32::from(wire_start);
            let wire_end = reader.u32()?;
            let end = u32::from(wire_end);
            let wire_count = reader.len()?;
            let count = usize::from(wire_count);
            let mut children = Vec::with_capacity(count);
            for _ in 0 .. count {
                let wire_child = reader.u32()?;
                let child = u32::from(wire_child);
                children.push(EmitId(child));
            }
            Ok(EmitOp::Interior {
                label,
                start,
                end,
                children,
            })
        },
        | tag => Err(CheckpointError::BadTag { tag }),
    }
}

/// Write an emission-log entry.
///
/// # Specification
/// trivial.
fn write_emit_op(
    writer: &mut Writer,
    op: &EmitOp,
)
{
    match *op {
        | EmitOp::Token { label, start, end } => {
            writer.u8(WireByte::from(0));
            write_label(writer, label);
            writer.u32(WireU32::from(start));
            writer.u32(WireU32::from(end));
        },
        | EmitOp::Interior {
            label,
            start,
            end,
            ref children,
        } => {
            writer.u8(WireByte::from(1));
            write_label(writer, label);
            writer.u32(WireU32::from(start));
            writer.u32(WireU32::from(end));
            writer.len(CheckpointCount::from(children.len()));
            for child in children {
                writer.u32(WireU32::from(child.0));
            }
        },
    }
}

/// Read a node label: the label's pinned digest tag, then its payload.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the cursor sits past the decoded value.
/// - fails: the stream ends early or carries a tag or length no well-formed
///   checkpoint holds.
/// - panics: none.
///
/// # Errors
/// [`CheckpointError`] for a truncated or ill-formed stream.
fn read_label(reader: &mut Reader<'_>) -> Result<NodeLabel, CheckpointError>
{
    let wire_tag = reader.u8()?;
    match u8::from(wire_tag) {
        | 0x01 => Ok(NodeLabel::Wald),
        | 0x02 => {
            let wire_mold = reader.u32()?;
            Ok(NodeLabel::Meld(MoldId::from(u32::from(wire_mold))))
        },
        | 0x03 => {
            let wire_mold = reader.u32()?;
            Ok(NodeLabel::Tile(MoldId::from(u32::from(wire_mold))))
        },
        | 0x04 => {
            let wire_sort = reader.u16()?;
            let sort = GroutSort::from(u16::from(wire_sort));
            let shape = read_shape(reader)?;
            Ok(NodeLabel::Grout { sort, shape })
        },
        | 0x05 => {
            let wire_sort = reader.u16()?;
            let sort = GroutSort::from(u16::from(wire_sort));
            let class = read_class(reader)?;
            Ok(NodeLabel::GhostClose { sort, class })
        },
        | 0x06 => Ok(NodeLabel::Space),
        | tag => Err(CheckpointError::BadTag { tag }),
    }
}

/// Write a node label: its pinned digest tag, then its payload.
///
/// # Specification
/// trivial.
fn write_label(
    writer: &mut Writer,
    label: NodeLabel,
)
{
    writer.u8(WireByte::from(u8::from(label.tag())));
    match label {
        | NodeLabel::Wald | NodeLabel::Space => {},
        | NodeLabel::Meld(mold) | NodeLabel::Tile(mold) => {
            writer.u32(WireU32::from(u32::from(mold)));
        },
        | NodeLabel::Grout { sort, shape } => {
            writer.u16(WireU16::from(u16::from(sort)));
            write_shape(writer, shape);
        },
        | NodeLabel::GhostClose { sort, class } => {
            writer.u16(WireU16::from(u16::from(sort)));
            write_class(writer, class);
        },
    }
}

/// Write a grout-shape tag.
///
/// # Specification
/// trivial.
fn write_shape(
    writer: &mut Writer,
    shape: GroutShape,
)
{
    writer.u8(WireByte::from(match shape {
        | GroutShape::Convex => 0,
        | GroutShape::Prefix => 1,
        | GroutShape::Postfix => 2,
        | GroutShape::Infix => 3,
    }));
}

/// Read a grout-shape tag.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the cursor sits past the decoded value.
/// - fails: the stream ends early or carries a tag or length no well-formed
///   checkpoint holds.
/// - panics: none.
///
/// # Errors
/// [`CheckpointError`] for a truncated or ill-formed stream.
fn read_shape(reader: &mut Reader<'_>) -> Result<GroutShape, CheckpointError>
{
    let wire_tag = reader.u8()?;
    match u8::from(wire_tag) {
        | 0 => Ok(GroutShape::Convex),
        | 1 => Ok(GroutShape::Prefix),
        | 2 => Ok(GroutShape::Postfix),
        | 3 => Ok(GroutShape::Infix),
        | tag => Err(CheckpointError::BadTag { tag }),
    }
}

/// Write a closing-class tag.
///
/// # Specification
/// trivial.
fn write_class(
    writer: &mut Writer,
    class: ClosingClass,
)
{
    writer.u8(WireByte::from(match class {
        | ClosingClass::Paren => 0,
        | ClosingClass::Bracket => 1,
        | ClosingClass::Brace => 2,
    }));
}

/// Read a closing-class tag.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the cursor sits past the decoded value.
/// - fails: the stream ends early or carries a tag or length no well-formed
///   checkpoint holds.
/// - panics: none.
///
/// # Errors
/// [`CheckpointError`] for a truncated or ill-formed stream.
fn read_class(reader: &mut Reader<'_>) -> Result<ClosingClass, CheckpointError>
{
    let wire_tag = reader.u8()?;
    match u8::from(wire_tag) {
        | 0 => Ok(ClosingClass::Paren),
        | 1 => Ok(ClosingClass::Bracket),
        | 2 => Ok(ClosingClass::Brace),
        | tag => Err(CheckpointError::BadTag { tag }),
    }
}

/// Read a slope cell.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the cursor sits past the decoded value.
/// - fails: the stream ends early or carries a tag or length no well-formed
///   checkpoint holds.
/// - panics: none.
///
/// # Errors
/// [`CheckpointError`] for a truncated or ill-formed stream.
fn read_cell(reader: &mut Reader<'_>) -> Result<Cell, CheckpointError>
{
    let wire_emit_id = reader.u32()?;
    let emit_id = u32::from(wire_emit_id);
    let emit = EmitId(emit_id);
    let wire_start = reader.u32()?;
    let start = u32::from(wire_start);
    let wire_end = reader.u32()?;
    let end = u32::from(wire_end);
    let sort = read_sort(reader)?;
    let wire_role = reader.u8()?;
    let role = match u8::from(wire_role) {
        | 0 => Role::Operand,
        | 1 => {
            let wire_mold_id = reader.u32()?;
            let mold_id = u32::from(wire_mold_id);
            let mold = MoldId::from(mold_id);
            let form_sort = read_sort(reader)?;
            let wire_open = reader.u8()?;
            let open = u8::from(wire_open) != 0;
            let wire_is_start = reader.u8()?;
            let is_start = u8::from(wire_is_start) != 0;
            let wire_absorb_left = reader.u8()?;
            let absorb_left = u8::from(wire_absorb_left) != 0;
            Role::FormTile {
                mold,
                sort: form_sort,
                open,
                start: is_start,
                absorb_left,
            }
        },
        | 2 => {
            let wire_mold_id = reader.u32()?;
            let mold_id = u32::from(wire_mold_id);
            let mold = MoldId::from(mold_id);
            let wire_prec_index = reader.u16()?;
            let prec_index = PrecIndex::from(u16::from(wire_prec_index));
            let prec = Prec::new(prec_index);
            let operator_sort = read_sort(reader)?;
            let shape = read_shape_op(reader)?;
            Role::Operator {
                mold,
                prec,
                sort: operator_sort,
                shape,
            }
        },
        | tag => return Err(CheckpointError::BadTag { tag }),
    };
    Ok(Cell {
        emit,
        start,
        end,
        sort,
        role,
    })
}
/// Read a grammar sort tag.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the cursor sits past the decoded value.
/// - fails: the stream ends early or carries a tag or length no well-formed
///   checkpoint holds.
/// - panics: none.
///
/// # Errors
/// [`CheckpointError`] for a truncated or ill-formed stream.
fn read_sort(reader: &mut Reader<'_>) -> Result<Sort, CheckpointError>
{
    let wire_tag = reader.u16()?;
    let tag = GroutSort::from(u16::from(wire_tag));
    Sort::try_from_tag(tag).map_err(|_error| CheckpointError::Malformed)
}

/// Write an obligation instance.
///
/// # Specification
/// trivial.
fn write_obligation(
    writer: &mut Writer,
    obligation: ObligationInstance,
)
{
    write_oblig(writer, obligation.class);
    let start = u32::try_from(usize::from(obligation.span.start())).unwrap_or(u32::MAX);
    let end = u32::try_from(usize::from(obligation.span.end())).unwrap_or(u32::MAX);
    writer.u32(WireU32::from(start));
    writer.u32(WireU32::from(end));
}
/// Write an obligation class tag.
///
/// # Specification
/// trivial.
fn write_oblig(
    writer: &mut Writer,
    class: Oblig,
)
{
    writer.u8(WireByte::from(u8::from(class.index())));
}

/// Read an obligation instance.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the cursor sits past the decoded value.
/// - fails: the stream ends early or carries a tag or length no well-formed
///   checkpoint holds.
/// - panics: none.
///
/// # Errors
/// [`CheckpointError`] for a truncated or ill-formed stream.
fn read_obligation(reader: &mut Reader<'_>) -> Result<ObligationInstance, CheckpointError>
{
    let class = read_oblig(reader)?;
    let wire_start = reader.u32()?;
    let start = u32::from(wire_start);
    let wire_end = reader.u32()?;
    let end = u32::from(wire_end);
    let span = SourceSpan::new(SourceOffset::from(start), SourceOffset::from(end))
        .byte_span()
        .map_err(|_error| CheckpointError::Malformed)?;
    Ok(ObligationInstance::new(class, span))
}
/// Read an obligation class tag.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the cursor sits past the decoded value.
/// - fails: the stream ends early or carries a tag or length no well-formed
///   checkpoint holds.
/// - panics: none.
///
/// # Errors
/// [`CheckpointError`] for a truncated or ill-formed stream.
fn read_oblig(reader: &mut Reader<'_>) -> Result<Oblig, CheckpointError>
{
    let wire_tag = reader.u8()?;
    match u8::from(wire_tag) {
        | 0 => Ok(Oblig::MissingMeld),
        | 1 => Ok(Oblig::MissingTile),
        | 2 => Ok(Oblig::IncompleteTile),
        | 3 => Ok(Oblig::UnmoldedTok),
        | 4 => Ok(Oblig::InconMeld),
        | 5 => Ok(Oblig::ExtraMeld),
        | 6 => Ok(Oblig::ReservedKeyword),
        | 7 => Ok(Oblig::AmbiguousPrec),
        | tag => Err(CheckpointError::BadTag { tag }),
    }
}

/// Write a slope cell.
///
/// # Specification
/// trivial.
fn write_cell(
    writer: &mut Writer,
    cell: Cell,
)
{
    writer.u32(WireU32::from(cell.emit.0));
    writer.u32(WireU32::from(cell.start));
    writer.u32(WireU32::from(cell.end));
    write_sort(writer, cell.sort);
    match cell.role {
        | Role::Operand => writer.u8(WireByte::from(0)),
        | Role::FormTile {
            mold,
            sort,
            open,
            start,
            absorb_left,
        } => {
            writer.u8(WireByte::from(1));
            writer.u32(WireU32::from(u32::from(mold)));
            write_sort(writer, sort);
            writer.u8(WireByte::from(u8::from(open)));
            writer.u8(WireByte::from(u8::from(start)));
            writer.u8(WireByte::from(u8::from(absorb_left)));
        },
        | Role::Operator {
            mold,
            prec,
            sort,
            shape,
        } => {
            writer.u8(WireByte::from(2));
            writer.u32(WireU32::from(u32::from(mold)));
            writer.u16(WireU16::from(u16::from(prec.index())));
            write_sort(writer, sort);
            write_shape_op(writer, shape);
        },
    }
}

/// Write a grammar sort tag.
///
/// # Specification
/// trivial.
fn write_sort(
    writer: &mut Writer,
    sort: Sort,
)
{
    writer.u16(WireU16::from(u16::from(sort.grout_sort())));
}
/// Write an operator shape tag.
///
/// # Specification
/// trivial.
fn write_shape_op(
    writer: &mut Writer,
    shape: OpShape,
)
{
    writer.u8(WireByte::from(match shape {
        | OpShape::Prefix => 0,
        | OpShape::Infix => 1,
        | OpShape::Postfix => 2,
    }));
}

/// Read an operator shape tag.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the cursor sits past the decoded value.
/// - fails: the stream ends early or carries a tag or length no well-formed
///   checkpoint holds.
/// - panics: none.
///
/// # Errors
/// [`CheckpointError`] for a truncated or ill-formed stream.
fn read_shape_op(reader: &mut Reader<'_>) -> Result<OpShape, CheckpointError>
{
    let wire_tag = reader.u8()?;
    match u8::from(wire_tag) {
        | 0 => Ok(OpShape::Prefix),
        | 1 => Ok(OpShape::Infix),
        | 2 => Ok(OpShape::Postfix),
        | tag => Err(CheckpointError::BadTag { tag }),
    }
}

#[cfg(test)]
mod tests
{
    use alloc::borrow::ToOwned as _;
    use alloc::boxed::Box;
    use alloc::format;
    use alloc::string::String;
    use alloc::vec;
    use alloc::vec::Vec;
    use core::error::Error;

    use gandr_surface_grammar::Pbg;
    use gandr_surface_grammar::Regex;
    use gandr_surface_grammar::Rule;
    use gandr_surface_grammar::RuleName;
    use gandr_surface_grammar::Sort;
    use gandr_surface_grammar::TileLabel;
    use gandr_surface_grammar::built_in;
    use gandr_surface_syntax::ByteOffset;
    use gandr_surface_syntax::ClosingClass;
    use gandr_surface_syntax::GroutShape;
    use gandr_surface_syntax::GroutSort;
    use gandr_surface_syntax::MoldId;
    use gandr_surface_syntax::NodeLabel;
    use gandr_surface_syntax::SourceFragment;
    use gandr_surface_syntax::SourceText;
    use gandr_theory_graphs::Assoc;
    use gandr_theory_graphs::PrecDag;
    use gandr_theory_graphs::PrecSpec;

    use super::Checkpoint;
    use super::CheckpointBytesRef;
    use super::CheckpointError;
    use super::Expected;
    use super::Kind;
    use super::MeldError;
    use super::MeldState;
    use super::MoldedTile;
    use super::SpaceText;
    use super::TileText;
    use crate::label::Lexeme;
    use crate::oblig::Oblig;
    use crate::testing::children;
    use crate::testing::label;
    use crate::testing::root_digest;
    use crate::testing::tile_texts;

    #[test]
    fn empty_state_commits_to_a_root() -> Result<(), Box<dyn Error>>
    {
        let pbg = infix_pbg()?;
        let state = MeldState::new(&pbg);
        let tree = state.commit(SourceText::from(""))?;
        assert_eq!(Some(NodeLabel::Wald), label(&tree, tree.root()));
        assert_eq!(tree.grammar(), pbg.fingerprint());
        Ok(())
    }
    #[test]
    fn infix_reduces_after_precedence() -> Result<(), Box<dyn Error>>
    {
        let pbg = infix_pbg()?;
        let x = only(&pbg, TileLabel("x"));
        let plus = only(&pbg, TileLabel("+"));
        let mut state = MeldState::new(&pbg);
        for tile in [
            MoldedTile::new(x, TileText::from("x")),
            MoldedTile::new(plus, TileText::from("+")),
            MoldedTile::new(x, TileText::from("x")),
        ] {
            state.push(&tile);
        }
        assert!(state.obligations().is_empty(), "`x + x` is complete");
        let tree = state.commit(SourceText::from("x+x"))?;
        // Root Wald -> one Meld named by its operator -> [x, +, x].
        let root_children = children(&tree, tree.root());
        assert_eq!(1, root_children.len());
        assert_eq!(
            Some(NodeLabel::Meld(plus)),
            label(&tree, root_children[0]),
            "an operator form is named by its operator's mold"
        );
        assert_eq!(3, children(&tree, root_children[0]).len());
        Ok(())
    }

    #[test]
    fn checkpoint_bytes_round_trip() -> Result<(), Box<dyn Error>>
    {
        let pbg = paren_pbg()?;
        let open = only(&pbg, TileLabel("("));
        let x = only(&pbg, TileLabel("x"));
        let mut state = MeldState::new(&pbg);
        // Leave an open bracket so the checkpoint carries slope + obligations.
        state.push(&MoldedTile::new(open, TileText::from("(")));
        state.push(&MoldedTile::new(x, TileText::from("x")));
        let checkpoint = state.checkpoint();
        let bytes = checkpoint.to_bytes();
        let restored = Checkpoint::from_bytes(CheckpointBytesRef::from(&bytes))?;
        assert_eq!(restored, checkpoint);

        // Truncated input (short of the 8-byte fingerprint) fails closed.
        let truncated = bytes.as_ref().get(.. 3).unwrap_or(&[]);
        assert!(matches!(
            Checkpoint::from_bytes(CheckpointBytesRef::from(truncated)),
            Err(CheckpointError::Truncated | CheckpointError::Malformed)
        ));
        Ok(())
    }

    /// A minted close survives the checkpoint wire, and every way of getting it
    /// wrong fails closed.
    ///
    /// A label carrying a class round-trips canonically. A stream truncated
    /// inside its payload is refused rather than half-read — the class is the
    /// last field written, so a stream that stops after the sort is exactly the
    /// dangerous case. And a class byte the reader does not know is refused
    /// rather than defaulted: guessing a class would pair a ghost against a
    /// closer that never answered it, which is the one error worse than not
    /// pairing at all.
    #[test]
    fn minted_close_round_trips_and_refuses_unknown_class() -> Result<(), Box<dyn Error>>
    {
        for class in [
            ClosingClass::Paren,
            ClosingClass::Bracket,
            ClosingClass::Brace,
        ] {
            let ghost = NodeLabel::GhostClose {
                sort: GroutSort::from(7),
                class,
            };
            let mut writer = super::Writer { bytes: Vec::new() };
            super::write_label(&mut writer, ghost);
            let encoded = writer.bytes;

            let mut reader = super::Reader {
                bytes: CheckpointBytesRef::from(encoded.as_slice()),
                pos: 0,
            };
            assert_eq!(
                ghost,
                super::read_label(&mut reader)?,
                "a minted close must round-trip canonically: {class:?}"
            );

            // Stopping short of the class byte must refuse, not default.
            let short = encoded
                .get(.. encoded.len().saturating_sub(1))
                .unwrap_or(&[]);
            let mut reader = super::Reader {
                bytes: CheckpointBytesRef::from(short),
                pos: 0,
            };
            assert!(
                super::read_label(&mut reader).is_err(),
                "a stream truncated before the class must fail closed: {class:?}"
            );
        }

        // An unknown class byte is refused, never decoded as some other class.
        let mut writer = super::Writer { bytes: Vec::new() };
        super::write_label(&mut writer, NodeLabel::GhostClose {
            sort: GroutSort::from(7),
            class: ClosingClass::Paren,
        });
        let mut encoded = writer.bytes;
        if let Some(last) = encoded.last_mut() {
            *last = 200;
        }
        let mut reader = super::Reader {
            bytes: CheckpointBytesRef::from(encoded.as_slice()),
            pos: 0,
        };
        assert!(
            matches!(
                super::read_label(&mut reader),
                Err(CheckpointError::BadTag { tag: 200 })
            ),
            "an unknown class byte must be refused, never defaulted"
        );

        // Every other label rides the same wire unchanged.
        for other in [
            NodeLabel::Wald,
            NodeLabel::Meld(MoldId::from(9)),
            NodeLabel::Tile(MoldId::from(9)),
            NodeLabel::Grout {
                sort: GroutSort::from(7),
                shape: GroutShape::Postfix,
            },
            NodeLabel::Space,
        ] {
            let mut writer = super::Writer { bytes: Vec::new() };
            super::write_label(&mut writer, other);
            let encoded = writer.bytes;
            let mut reader = super::Reader {
                bytes: CheckpointBytesRef::from(encoded.as_slice()),
                pos: 0,
            };
            assert_eq!(other, super::read_label(&mut reader)?);
        }
        Ok(())
    }

    #[test]
    fn degrout_flags_one_ambiguous_prec_at_the_smallest_span() -> Result<(), Box<dyn Error>>
    {
        // `x @a x @b x`: `@a` and `@b` are precedence-incomparable within one
        // sort, so the melder emits exactly one AmbiguousPrec at the smallest
        // responsible span (the second operator `@b`) and the parse stays total.
        let pbg = ambiguous_pbg()?;
        let x = only(&pbg, TileLabel("x"));
        let opa = only(&pbg, TileLabel("@a"));
        let opb = only(&pbg, TileLabel("@b"));
        let mut state = MeldState::new(&pbg);
        let tiles = [
            MoldedTile::new(x, TileText::from("x")),
            MoldedTile::new(opa, TileText::from("@a")),
            MoldedTile::new(x, TileText::from("x")),
            MoldedTile::new(opb, TileText::from("@b")),
            MoldedTile::new(x, TileText::from("x")),
        ];
        for tile in &tiles {
            state.push(tile);
        }

        let ambiguities: Vec<_> = state
            .obligations()
            .iter()
            .filter(|obligation| obligation.class == Oblig::AmbiguousPrec)
            .collect();
        assert_eq!(1, ambiguities.len(), "exactly one AmbiguousPrec");

        // The smallest responsible span is the `@b` tile: source "x@ax@bx",
        // `@b` occupies bytes 4..6.
        let span = ambiguities[0].span;
        assert_eq!(
            (ByteOffset::from(4), ByteOffset::from(6)),
            (span.start(), span.end())
        );

        // Minimization never selects AmbiguousPrec when an alternative exists.
        let delta = state.delta();
        assert_eq!(1, u32::from(delta.inserted(Oblig::AmbiguousPrec)));

        // Totality: the parse still commits to a well-formed tree.
        let tree = state.commit(SourceText::from("x@ax@bx"))?;
        assert_eq!(Some(NodeLabel::Wald), label(&tree, tree.root()));
        Ok(())
    }

    #[test]
    fn single_atom_commits_to_one_token() -> Result<(), Box<dyn Error>>
    {
        let pbg = infix_pbg()?;
        let x = only(&pbg, TileLabel("x"));
        let mut state = MeldState::new(&pbg);
        state.push(&MoldedTile::new(x, TileText::from("x")));
        assert!(state.obligations().is_empty(), "a bare atom is complete");
        let tree = state.commit(SourceText::from("x"))?;
        assert_eq!(tile_texts(&tree, tree.root()), vec!["x".to_owned()]);
        Ok(())
    }
    #[test]
    fn brackets_close_on_the_matching_delimiter() -> Result<(), Box<dyn Error>>
    {
        let pbg = paren_pbg()?;
        let open = only(&pbg, TileLabel("("));
        let close = only(&pbg, TileLabel(")"));
        let x = only(&pbg, TileLabel("x"));
        let mut state = MeldState::new(&pbg);
        for tile in [
            MoldedTile::new(open, TileText::from("(")),
            MoldedTile::new(x, TileText::from("x")),
            MoldedTile::new(close, TileText::from(")")),
        ] {
            state.push(&tile);
        }
        assert!(state.obligations().is_empty(), "`( x )` is complete");
        let tree = state.commit(SourceText::from("(x)"))?;
        let root_children = children(&tree, tree.root());
        assert_eq!(1, root_children.len());
        assert_eq!(
            Some(NodeLabel::Meld(open)),
            label(&tree, root_children[0]),
            "a bracket form is named by its opener's mold"
        );
        // `(`, `x`, `)`
        assert_eq!(3, children(&tree, root_children[0]).len());
        Ok(())
    }
    /// A synthetic PBG with a bracket `( E )` and a bare atom `x`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the grammar passes every construction check.
    /// - fails: the grammar builder refuses the declaration.
    /// - panics: none.
    ///
    /// # Errors
    /// The builder's refusal.
    fn paren_pbg() -> Result<Pbg, Box<dyn Error>>
    {
        let mut spec = PrecSpec::new();
        let atom = spec.insert("atom", Assoc::Non)?;
        let dag = PrecDag::build(&spec)?;
        let pbg = Pbg::build(dag, vec![
            Rule::new(
                RuleName("group"),
                Sort::Expression,
                atom,
                Regex::seq([
                    Regex::tile(TileLabel("(")),
                    Regex::sort(Sort::Expression),
                    Regex::tile(TileLabel(")")),
                ]),
            ),
            Rule::new(
                RuleName("atom"),
                Sort::Expression,
                atom,
                Regex::tile(TileLabel("x")),
            ),
        ])?;
        Ok(pbg)
    }
    #[test]
    fn delta_reflects_the_buffered_obligations() -> Result<(), Box<dyn Error>>
    {
        let pbg = ambiguous_pbg()?;
        let x = only(&pbg, TileLabel("x"));
        let opa = only(&pbg, TileLabel("@a"));
        let opb = only(&pbg, TileLabel("@b"));
        let mut state = MeldState::new(&pbg);
        for tile in [
            MoldedTile::new(x, TileText::from("x")),
            MoldedTile::new(opa, TileText::from("@a")),
            MoldedTile::new(x, TileText::from("x")),
            MoldedTile::new(opb, TileText::from("@b")),
            MoldedTile::new(x, TileText::from("x")),
        ] {
            state.push(&tile);
        }
        let delta = state.delta();
        let buffered = state
            .obligations()
            .iter()
            .filter(|obligation| obligation.class == Oblig::AmbiguousPrec)
            .count();
        let inserted = usize::from(delta.inserted(Oblig::AmbiguousPrec));
        assert_eq!(inserted, buffered);
        Ok(())
    }
    #[test]
    fn finalize_is_non_destructive() -> Result<(), Box<dyn Error>>
    {
        let pbg = infix_pbg()?;
        let x = only(&pbg, TileLabel("x"));
        let plus = only(&pbg, TileLabel("+"));

        // An incomplete prefix `x +` expects a right-hand hole.
        let mut probing = MeldState::new(&pbg);
        probing.push(&MoldedTile::new(x, TileText::from("x")));
        probing.push(&MoldedTile::new(plus, TileText::from("+")));
        let completion = probing.finalize();
        assert!(!bool::from(completion.is_complete()));
        assert!(
            completion
                .expected()
                .iter()
                .any(|item| matches!(item, Expected::Hole(Sort::Expression))),
            "an operator missing its right operand expects a hole"
        );

        // Querying finalize at every prefix leaves the committed parse unchanged.
        let mut queried = MeldState::new(&pbg);
        for tile in [
            MoldedTile::new(x, TileText::from("x")),
            MoldedTile::new(plus, TileText::from("+")),
            MoldedTile::new(x, TileText::from("x")),
        ] {
            let _before = queried.finalize();
            queried.push(&tile);
            let _after = queried.finalize();
        }
        let queried_root = root_digest(&queried.commit(SourceText::from("x+x"))?);

        let mut plain = MeldState::new(&pbg);
        for tile in [
            MoldedTile::new(x, TileText::from("x")),
            MoldedTile::new(plus, TileText::from("+")),
            MoldedTile::new(x, TileText::from("x")),
        ] {
            plain.push(&tile);
        }
        let plain_root = root_digest(&plain.commit(SourceText::from("x+x"))?);
        assert_eq!(
            queried_root, plain_root,
            "finalize queries do not perturb the committed parse"
        );
        Ok(())
    }
    #[test]
    fn checkpoint_resume_is_equivalent() -> Result<(), Box<dyn Error>>
    {
        let pbg = infix_pbg()?;
        let x = only(&pbg, TileLabel("x"));
        let plus = only(&pbg, TileLabel("+"));
        let prefix = [
            MoldedTile::new(x, TileText::from("x")),
            MoldedTile::new(plus, TileText::from("+")),
        ];
        let suffix = [MoldedTile::new(x, TileText::from("x"))];

        // Uninterrupted run.
        let mut plain = MeldState::new(&pbg);
        for tile in prefix.iter().chain(suffix.iter()) {
            plain.push(tile);
        }
        let plain_obligations = plain.obligations().to_vec();
        let plain_root = root_digest(&plain.commit(SourceText::from("x+x"))?);

        // Checkpoint after the prefix, round-trip through bytes, resume.
        let mut prefix_state = MeldState::new(&pbg);
        for tile in &prefix {
            prefix_state.push(tile);
        }
        let checkpoint = prefix_state.checkpoint();
        let bytes = checkpoint.to_bytes();
        let restored = Checkpoint::from_bytes(CheckpointBytesRef::from(&bytes))?;
        assert_eq!(checkpoint, restored);
        let mut resumed = MeldState::resume(&pbg, &restored);
        for tile in &suffix {
            resumed.push(tile);
        }
        let resumed_obligations = resumed.obligations().to_vec();
        let resumed_root = root_digest(&resumed.commit(SourceText::from("x+x"))?);

        assert_eq!(resumed_root, plain_root, "resume yields an identical parse");
        assert_eq!(resumed_obligations, plain_obligations);
        Ok(())
    }
    #[test]
    fn mark_rollback_restores_state_exactly() -> Result<(), Box<dyn Error>>
    {
        // The molder's per-candidate transaction: mark, dry-run a two-tile
        // push, roll back, and the state is bytewise identical to before —
        // committing exactly as a run that never took the dry-run.
        let pbg = infix_pbg()?;
        let x = only(&pbg, TileLabel("x"));
        let plus = only(&pbg, TileLabel("+"));

        let mut state = MeldState::new(&pbg);
        state.push(&MoldedTile::new(x, TileText::from("x")));
        let mark = state.mark();
        state.push(&MoldedTile::new(plus, TileText::from("+")));
        state.push(&MoldedTile::new(x, TileText::from("x")));
        state.rollback_to(&mark);
        let rolled_obligations = state.obligations().to_vec();
        let rolled_hash = root_digest(&state.commit(SourceText::from("x"))?);

        let mut plain = MeldState::new(&pbg);
        plain.push(&MoldedTile::new(x, TileText::from("x")));
        let plain_obligations = plain.obligations().to_vec();
        let plain_hash = root_digest(&plain.commit(SourceText::from("x"))?);

        assert_eq!(rolled_obligations, plain_obligations);
        assert_eq!(rolled_hash, plain_hash, "rollback restores the exact state");
        Ok(())
    }

    #[test]
    fn a_foreign_source_is_refused_at_commit() -> Result<(), Box<dyn Error>>
    {
        // The tree borrows the caller's source, so commit checks that it is the
        // text the pushes assembled; any other text would mis-span every node.
        let pbg = infix_pbg()?;
        let x = only(&pbg, TileLabel("x"));
        let mut state = MeldState::new(&pbg);
        state.push(&MoldedTile::new(x, TileText::from("x")));
        assert_eq!(
            Some(MeldError::SourceMismatch),
            state.commit(SourceText::from("y")).err()
        );

        Ok(())
    }
    /// A synthetic PBG with an infix `E + E` and a bare atom `x`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the grammar passes every construction check.
    /// - fails: the grammar builder refuses the declaration.
    /// - panics: none.
    ///
    /// # Errors
    /// The builder's refusal.
    fn infix_pbg() -> Result<Pbg, Box<dyn Error>>
    {
        let mut spec = PrecSpec::new();
        let atom = spec.insert("atom", Assoc::Non)?;
        let add = spec.insert("add", Assoc::Left)?;
        spec.add_edge(atom, add)?;
        let dag = PrecDag::build(&spec)?;
        let pbg = Pbg::build(dag, vec![
            Rule::new(
                RuleName("add"),
                Sort::Expression,
                add,
                Regex::seq([
                    Regex::sort(Sort::Expression),
                    Regex::tile(TileLabel("+")),
                    Regex::sort(Sort::Expression),
                ]),
            ),
            Rule::new(
                RuleName("atom"),
                Sort::Expression,
                atom,
                Regex::tile(TileLabel("x")),
            ),
        ])?;
        Ok(pbg)
    }
    #[test]
    fn delta_since_reads_only_the_candidate_tail() -> Result<(), Box<dyn Error>>
    {
        // A candidate that introduces an ambiguity has a non-empty delta; one
        // that appends a plain operand has an empty delta — the molder's
        // per-candidate minimization key, read from the marked tail only.
        let pbg = ambiguous_pbg()?;
        let x = only(&pbg, TileLabel("x"));
        let opa = only(&pbg, TileLabel("@a"));
        let opb = only(&pbg, TileLabel("@b"));

        let mut state = MeldState::new(&pbg);
        for tile in [
            MoldedTile::new(x, TileText::from("x")),
            MoldedTile::new(opa, TileText::from("@a")),
            MoldedTile::new(x, TileText::from("x")),
        ] {
            state.push(&tile);
        }

        // Candidate A: the incomparable `@b` introduces one AmbiguousPrec.
        let mark = state.mark();
        state.push(&MoldedTile::new(opb, TileText::from("@b")));
        state.push(&MoldedTile::new(x, TileText::from("x")));
        let ambiguous_delta = state.delta_since(&mark);
        assert_eq!(1, u32::from(ambiguous_delta.inserted(Oblig::AmbiguousPrec)));
        state.rollback_to(&mark);

        // Candidate B over the same base: another operand adds no obligation.
        let operand_mark = state.mark();
        state.push(&MoldedTile::new(x, TileText::from("x")));
        let operand_delta = state.delta_since(&operand_mark);
        assert!(
            bool::from(operand_delta.is_empty()),
            "an operand push flags nothing"
        );
        state.rollback_to(&operand_mark);

        // Candidate B is the obligation minimum.
        assert!(operand_delta < ambiguous_delta);
        Ok(())
    }
    /// A synthetic PBG with two precedence-incomparable infix operators.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the grammar passes every construction check.
    /// - fails: the grammar builder refuses the declaration.
    /// - panics: none.
    ///
    /// # Errors
    /// The builder's refusal.
    fn ambiguous_pbg() -> Result<Pbg, Box<dyn Error>>
    {
        let mut spec = PrecSpec::new();
        let atom = spec.insert("atom", Assoc::Non)?;
        let pa = spec.insert("pa", Assoc::Non)?;
        let pb = spec.insert("pb", Assoc::Non)?;
        spec.add_edge(atom, pa)?;
        spec.add_edge(atom, pb)?;
        let dag = PrecDag::build(&spec)?;
        let pbg = Pbg::build(dag, vec![
            Rule::new(
                RuleName("opa"),
                Sort::Expression,
                pa,
                Regex::seq([
                    Regex::sort(Sort::Expression),
                    Regex::tile(TileLabel("@a")),
                    Regex::sort(Sort::Expression),
                ]),
            ),
            Rule::new(
                RuleName("opb"),
                Sort::Expression,
                pb,
                Regex::seq([
                    Regex::sort(Sort::Expression),
                    Regex::tile(TileLabel("@b")),
                    Regex::sort(Sort::Expression),
                ]),
            ),
            Rule::new(
                RuleName("atom"),
                Sort::Expression,
                atom,
                Regex::tile(TileLabel("x")),
            ),
        ])?;
        Ok(pbg)
    }

    #[test]
    fn admits_a_form_first_mid_at_a_fresh_slot() -> Result<(), Box<dyn Error>>
    {
        // The candidate pre-filter (`admits`): a `def` opens a definition at the
        // base even though the factored def gives its `def` a nullable `@[…]`
        // predecessor (a form-mid that is also form-first), while a stray `;`
        // (a form-end closer) has no open form to close and is inadmissible.
        let pbg = built_in()?;
        let state = MeldState::new(&pbg);
        let def = *pbg
            .candidates(TileLabel("def"))
            .first()
            .expect("a `def` mold");
        assert!(
            bool::from(state.admits(def)),
            "a form-first `def` opens at a fresh slot"
        );
        let semi = *pbg.candidates(TileLabel(";")).first().expect("a `;` mold");
        assert!(
            !bool::from(state.admits(semi)),
            "a stray `;` closer is inadmissible with no open form"
        );
        Ok(())
    }

    #[test]
    fn admits_rejects_a_stray_closer() -> Result<(), Box<dyn Error>>
    {
        // A form-end closer (`)` / `;` / a closing `"`) is admissible only when
        // it `≐`-continues an open form frontier: at the base none is open, so
        // every closer is rejected (the pre-filter cannot pick a mold that would
        // immediately flag a `MissingTile`).
        let pbg = built_in()?;
        let state = MeldState::new(&pbg);
        for closer in [")", "}", "]", ";"] {
            for &mold in pbg.candidates(TileLabel(closer)) {
                if matches!(state.classify(mold), Kind::FormEnd) {
                    assert!(
                        !bool::from(state.admits(mold)),
                        "a stray {closer:?} form-end is inadmissible at the base"
                    );
                }
            }
        }
        Ok(())
    }

    #[test]
    fn expected_sort_reads_the_open_slot() -> Result<(), Box<dyn Error>>
    {
        // `expected_operand_sort` reads the head's expected operand slot: at the
        // base it defaults to `Expression`, and after a `ret` prefix operator the
        // unsaturated right hole is still `Expression`.
        let pbg = built_in()?;
        let mut state = MeldState::new(&pbg);
        assert_eq!(Sort::Expression, state.expected_operand_sort());
        let ret = *pbg
            .candidates(TileLabel("ret"))
            .first()
            .expect("a `ret` mold");
        state.push(&MoldedTile::new(ret, TileText::from("ret")));
        assert_eq!(
            Sort::Expression,
            state.expected_operand_sort(),
            "a `ret` operator's right hole expects an expression"
        );
        Ok(())
    }

    #[test]
    fn head_caches_match_a_fresh_scan_across_streams() -> Result<(), Box<dyn Error>>
    {
        // The O(1) head caches (`frontiers` / `operators` / `barriers`) must
        // equal a fresh role scan after EVERY mutation: pushes (every Kind),
        // splice-reduces, form open/close flips, mark/rollback dry-runs, and
        // checkpoint resume. The sources cross the mutation classes: shell
        // juxtaposition (long operand runs over an open frontier), nested
        // forms, operators, strings, data members (closed-tile runs), and
        // malformed input (stray closers, force-closes at commit).
        let pbg = built_in()?;
        let sources = [
            "#!{ echo a b c d e f; ls | grep x && echo y; }",
            "#!{ [ cd d; ls ] | sort; echo ${x}${y} \"z $w\"; }",
            "def f(x: Integer) -> -F Integer { ret (x * x + 1) }",
            "data Tree(a) { Leaf, Node(l: Tree(a), v: a, r: Tree(a)) }",
            "def s = \"a ${ f(\"${x}\") } b\";",
            "case v { Inl(x) => x, Inr(y) => y }",
            "#!{ echo unclosed",
            ") } ] stray closers",
            "let p = (1, 2); if c { ret p } else { ret p }",
        ];
        for src in sources {
            let mut molder = crate::Molder::new(&pbg);
            let mut state = MeldState::new(&pbg);
            let source = SourceFragment::from(src);
            for token in crate::label(source) {
                if token.lexeme == Lexeme::Space {
                    let text = token.text(&source);
                    state.space(SpaceText::from(AsRef::<str>::as_ref(&text)));
                }
                else {
                    // A mark/rollback dry-run before the real push exercises
                    // the cache restore path at every position.
                    let mark = state.mark();
                    molder.mold(&mut state, token, SourceText::from(src));
                    state.assert_head_caches_exact();
                    state.rollback_to(&mark);
                    state.assert_head_caches_exact();
                    molder.mold(&mut state, token, SourceText::from(src));
                }
                state.assert_head_caches_exact();
            }
            // Checkpoint resume rebuilds the caches from the slope.
            let resumed = MeldState::resume(&pbg, &state.checkpoint());
            resumed.assert_head_caches_exact();
            let _tree = state.commit(SourceText::from(src))?;
        }
        Ok(())
    }

    #[test]
    fn completable_hole_closes_without_obligation() -> Result<(), Box<dyn Error>>
    {
        // A bare `?` whose optional `name` tail never arrives is a
        // *complete* form (its mold is in the grammar LAST set), so committing
        // closes it cleanly — a one-tile hole meld, ZERO obligations — rather
        // than force-closing an "incomplete" form with a ghost end and a
        // spurious MissingTile. `finalize` agrees (it reports the input complete).
        let pbg = completable_pbg()?;
        let only = |label: &'static str| -> MoldId {
            let molds = pbg.candidates(TileLabel(label));
            assert_eq!(1, molds.len(), "one mold for {label}");
            molds[0]
        };
        let mut state = MeldState::new(&pbg);
        state.push(&MoldedTile::new(only("?"), TileText::from("?")));
        // The completion query reports the input already complete: no expected
        // material, no would-introduce obligation.
        let completion = state.finalize();
        assert!(
            bool::from(completion.is_complete()),
            "a bare `?` hole is a complete form, expecting nothing"
        );
        assert!(
            completion.obligations().is_empty(),
            "a bare `?` hole introduces no completion obligation"
        );
        let (tree, obligations) = state.commit_with_obligations(SourceText::from("?"))?;
        assert!(
            obligations.is_empty(),
            "a bare `?` hole commits with zero obligations, got {:?}",
            obligations.iter().map(|o| o.class).collect::<Vec<_>>()
        );
        // The hole is a one-tile Meld (so the pipeline recognizer sees a hole
        // node, not a bare token), carrying just the `?`.
        let root_children = children(&tree, tree.root());
        assert_eq!(1, root_children.len(), "one top-level operand");
        assert_eq!(
            Some(NodeLabel::Meld(only("?"))),
            label(&tree, root_children[0]),
            "the hole is a meld named by its `?`"
        );
        assert_eq!(
            1,
            children(&tree, root_children[0]).len(),
            "the hole meld carries just `?`"
        );
        Ok(())
    }
    #[test]
    fn completable_hole_does_not_absorb_enclosing_closer() -> Result<(), Box<dyn Error>>
    {
        // An open completable `?` frontier does not shadow the
        // enclosing form — pushing the group's `)` closes the *hole* cleanly and
        // then the *group*, so the `)` is a sibling of the hole, never absorbed
        // into its meld (which is what structurally broke block recovery).
        let pbg = completable_pbg()?;
        let only = |label: &'static str| -> MoldId {
            let molds = pbg.candidates(TileLabel(label));
            assert_eq!(1, molds.len(), "one mold for {label}");
            molds[0]
        };
        let mut state = MeldState::new(&pbg);
        for (label, text) in [("(", "("), ("?", "?"), (")", ")")] {
            state.push(&MoldedTile::new(only(label), TileText::from(text)));
            // The completable-hole clean-close mutates the slope through
            // `close_form`; the head caches must stay exact across it (the
            // shared invariant with `head_caches_match_a_fresh_scan_across_streams`).
            state.assert_head_caches_exact();
        }
        let (tree, obligations) = state.commit_with_obligations(SourceText::from("(?)"))?;
        assert!(
            obligations.is_empty(),
            "`( ? )` commits with zero obligations, got {:?}",
            obligations.iter().map(|o| o.class).collect::<Vec<_>>()
        );
        // The group meld holds `(`, the hole meld, and `)` as three children;
        // the hole meld holds ONLY `?` (the `)` is a group sibling, not absorbed).
        let root_children = children(&tree, tree.root());
        assert_eq!(1, root_children.len(), "one top-level group");
        let group_children = children(&tree, root_children[0]);
        assert_eq!(3, group_children.len(), "( hole )");
        assert_eq!(
            Some(NodeLabel::Meld(only("?"))),
            label(&tree, group_children[1]),
            "the middle child is the hole meld"
        );
        assert_eq!(
            1,
            children(&tree, group_children[1]).len(),
            "the hole meld carries only `?`, not the enclosing `)`"
        );
        Ok(())
    }

    /// A closing bracket followed by a required operand is a mid tile: the
    /// type after `+U[r]` is the bridge's operand, however it is spaced, and a
    /// package's operand after `package [ T ]` stays the package's when a
    /// declaration follows. A closing bracket that ends its form still ends it:
    /// the arrow after a universe's `]` takes the universe as its domain.
    #[test]
    fn a_bracket_before_a_required_tail_keeps_its_form_open() -> Result<(), Box<dyn Error>>
    {
        let pbg = built_in()?;
        let spans_of = |source: &'static str, kind: &str| -> Result<Vec<String>, Box<dyn Error>> {
            let result = crate::parse::parse(&pbg, SourceText::from(source))?;
            assert!(bool::from(result.is_clean()), "{source} reads cleanly");
            let tree = result.into_tree();
            let mut spans = Vec::new();
            for position in tree.positions() {
                if let Some(NodeLabel::Meld(mold)) = label(&tree, position)
                    && pbg.named_kind(mold)?.0 == kind
                    && let Some(text) = tree.fragment(position)
                {
                    spans.push(AsRef::<str>::as_ref(&text).to_owned());
                }
            }
            Ok(spans)
        };
        for source in [
            "def g : +U[ω] (-F Integer) ;",
            "def g : +U[ω](-F Integer) ;",
        ] {
            let bridge = source.trim_start_matches("def g : ").trim_end_matches(" ;");
            assert_eq!(
                vec![bridge.to_owned()],
                spans_of(source, "u_type")?,
                "the bridge in {source} spans its operand"
            );
        }
        assert_eq!(
            vec!["+U[1] Integer -> -F Integer".to_owned()],
            spans_of("def g : +U[1] Integer -> -F Integer ;", "function_type")?,
            "an operand after the grade is the bridge's, below the arrow"
        );
        assert_eq!(
            vec!["package [ T ] Integer".to_owned()],
            spans_of(
                "def bad : package [ T ] Integer;\ndef bad = ret 1;",
                "package_type"
            )?,
            "a package's operand stays its own when another declaration follows"
        );
        assert_eq!(
            vec!["Type[+, 1] -> -F Integer".to_owned()],
            spans_of("def g : +U (Type[+, 1] -> -F Integer) ;", "function_type")?,
            "a universe's closing bracket ends it, so the arrow takes it as its domain"
        );
        Ok(())
    }

    /// A form ending in a required sort hole closes where a prefix operator at
    /// its group would: an operator its group yields to stays inside the
    /// tail, a prefix operator's operand completes it, and an operator its
    /// group takes from stands outside.
    #[test]
    fn a_required_tail_runs_as_far_as_its_group_yields() -> Result<(), Box<dyn Error>>
    {
        let pbg = built_in()?;
        let spans_of = |source: &'static str, kind: &str| -> Result<Vec<String>, Box<dyn Error>> {
            let result = crate::parse::parse(&pbg, SourceText::from(source))?;
            assert!(bool::from(result.is_clean()), "{source} reads cleanly");
            let tree = result.into_tree();
            let mut spans = Vec::new();
            for position in tree.positions() {
                if let Some(NodeLabel::Meld(mold)) = label(&tree, position)
                    && pbg.named_kind(mold)?.0 == kind
                    && let Some(text) = tree.fragment(position)
                {
                    spans.push(AsRef::<str>::as_ref(&text).to_owned());
                }
            }
            Ok(spans)
        };
        assert_eq!(
            vec!["forall a . a * b".to_owned()],
            spans_of("def g : forall a . a * b ;", "forall_type")?,
            "a product binds tighter than the quantifier and stays in its body"
        );
        assert_eq!(
            vec!["forall a . -F a".to_owned()],
            spans_of("def g : forall a . -F a ;", "forall_type")?,
            "a prefix operator's operand completes the body before the `;`"
        );
        assert_eq!(
            vec![r"\A. A => \B. B".to_owned(), r"\B. B".to_owned()],
            spans_of(r"def g : \A. A => \B. B ;", "static_abstraction")?,
            "an arrow of the abstraction's own right-associative group stays in its body"
        );
        assert_eq!(
            vec!["+U[1] C".to_owned()],
            spans_of("def g : +U[1] C * D ;", "u_type")?,
            "a bridge binds tighter than the product, which takes it as an operand"
        );
        Ok(())
    }

    /// `finalize` charges a required-tail frontier only when commit would:
    /// against a bridge with no operand yet, one whose operand is a written
    /// type owes one tile fewer, and one whose operand is an inner form already
    /// opened owes the same — the parenthesis's closer replaces the tail.
    #[test]
    fn finalize_charges_a_required_tail_only_when_it_is_absent() -> Result<(), Box<dyn Error>>
    {
        let pbg = built_in()?;
        let mold_of = |text: &'static str, kind: &str| -> Result<MoldId, Box<dyn Error>> {
            let label = match text {
                | "g" => "identifier",
                | other => other,
            };
            pbg.candidates(TileLabel(label))
                .iter()
                .copied()
                .find(|&mold| pbg.named_kind(mold).is_ok_and(|named| named.0 == kind))
                .ok_or_else(|| format!("no {kind} mold for {text}").into())
        };
        let owed = |tiles: &[(&'static str, &'static str)]| -> Result<usize, Box<dyn Error>> {
            let mut state = MeldState::new(&pbg);
            for (position, &(text, kind)) in tiles.iter().enumerate() {
                if position > 0 {
                    state.space(SpaceText::from(" "));
                }
                state.push(&MoldedTile::new(mold_of(text, kind)?, TileText::from(text)));
            }
            Ok(state
                .finalize()
                .obligations()
                .iter()
                .filter(|obligation| obligation.class == Oblig::MissingTile)
                .count())
        };
        let head = [
            ("def", "def_value"),
            ("g", "def_value"),
            (":", "def_value"),
            ("+U", "u_type"),
            ("[", "u_type"),
            ("ω", "u_type"),
            ("]", "u_type"),
        ];
        let bare = owed(&head)?;
        let with = |tail: (&'static str, &'static str)| {
            let mut tiles = head.to_vec();
            tiles.push(tail);
            tiles
        };
        assert_eq!(
            bare.saturating_sub(1),
            owed(&with(("Integer", "primitive_type")))?,
            "a written operand fills the tail, and the bridge owes nothing of its own"
        );
        assert_eq!(
            bare,
            owed(&with(("(", "parenthesized_type")))?,
            "an opened operand fills the tail, and only its `)` is owed in its place"
        );
        Ok(())
    }
    /// A synthetic PBG whose `hole = ? name?` form has a nullable tail (so `?`
    /// is in the LAST set — completable), nested inside a `group = ( E )`
    /// bracket, with a bare atom `x`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the grammar passes every construction check.
    /// - fails: the grammar builder refuses the declaration.
    /// - panics: none.
    ///
    /// # Errors
    /// The builder's refusal.
    fn completable_pbg() -> Result<Pbg, Box<dyn Error>>
    {
        let mut spec = PrecSpec::new();
        let atom = spec.insert("atom", Assoc::Non)?;
        let dag = PrecDag::build(&spec)?;
        let pbg = Pbg::build(dag, vec![
            Rule::new(
                RuleName("hole"),
                Sort::Expression,
                atom,
                Regex::seq([
                    Regex::tile(TileLabel("?")),
                    Regex::optional(Regex::tile(TileLabel("name"))),
                ]),
            ),
            Rule::new(
                RuleName("group"),
                Sort::Expression,
                atom,
                Regex::seq([
                    Regex::tile(TileLabel("(")),
                    Regex::sort(Sort::Expression),
                    Regex::tile(TileLabel(")")),
                ]),
            ),
            Rule::new(
                RuleName("atom"),
                Sort::Expression,
                atom,
                Regex::tile(TileLabel("x")),
            ),
        ])?;
        Ok(pbg)
    }
    /// The sole mold id declared for `label`.
    ///
    /// # Specification
    /// - requires: `label` declares exactly one mold.
    /// - ensures: that mold's id.
    /// - panics: when `label` declares none or several.
    fn only(
        pbg: &Pbg,
        label: TileLabel,
    ) -> MoldId
    {
        let molds = pbg.candidates(label);
        assert_eq!(1, molds.len(), "label {} must have one mold", label.0);
        molds[0]
    }
}
