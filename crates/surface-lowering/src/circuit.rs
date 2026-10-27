//! Ruled circuit bodies, their literal wiring diagrams and matcher boundary.

use alloc::vec::Vec;

use gandr_surface_syntax::ByteSpan;
use gandr_theory_levitation::CircuitDerivationError;
use gandr_theory_levitation::IncludeClash;
use gandr_theory_levitation::Name;
use gandr_theory_levitation::PortInstantiationError;

/// The row an arrow occupies in a ruled judgment.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ArrowRow
{
    /// An operation or constructor boundary.
    Mapping,
    /// A rewrite boundary.
    Face,
}

/// The number of output ports a redex line binds, where its rewrite binds one.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct OutputCount(pub usize);

/// A ruled signature's explicit boundary, independent of diagnostic wording.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SignatureFault
{
    /// A signature member requires its colon-led judgment.
    MissingJudgment,
    /// A theory block presents sorts, operations and rules, not item-level
    /// data.
    RetiredDataMember,
    /// A theory block's written face names itself, `rule name : lhs ==> rhs`;
    /// the unnamed face is the data and codata blocks' spelling.
    WrittenFace,
    /// An expression CST node cannot silently become a circuit binder group.
    ExpressionEndpoint,
    /// An operation filler is outside the description route.
    OperationFiller,
    /// An operation declared outside a theory block: no signature holds it.
    TopLevelOperation,
    /// A fillerless higher cell has no circuit body to elaborate.
    HigherCell,
    /// A redex line binds more than the one output port its rewrite has.
    MultipleOutputs(OutputCount),
    /// A circuit rule must name the output from which its boundary is derived.
    MissingOutput,
    /// A fed-back port no observation reads: every occurrence of it in the
    /// rule's body is bare, so the loop it closes is not guarded. The
    /// diagnostic's span is the bare occurrence.
    BareFeedback
    {
        /// The rule's name tile.
        rule: ByteSpan,
    },
    /// The glyph is reserved for reversible maps: `<->`.
    Reversible,
    /// The written arrow's row differs from the subject's declared kind.
    ArrowMismatch
    {
        /// The declared kind's row.
        expected: ArrowRow,
        /// The written glyph's row.
        actual: ArrowRow,
    },
    /// No rewrite port declares the head of this redex line.
    UndeclaredRewrite(Name),
    /// A rewrite port's endpoint does not instantiate at this wiring.
    Instantiation(PortInstantiationError),
    /// The written wiring cannot derive a finite boundary within its ceiling.
    Derivation(CircuitDerivationError),
    /// A port name written twice on an operation's boundary: two ports, not
    /// one wire.
    SharedPort(Name),
    /// An `include` names no `theory` block its source reads before the
    /// including one or imports unqualified.
    UnknownInclude(Name),
    /// An `include` names a `theory` block of two sources its source imports
    /// unqualified, and none of its own.
    AmbiguousInclude(Name),
    /// Two theories the block reaches through `include` have more than one
    /// join among the theories it sees.
    AmbiguousJoin(JoinFault),
    /// The included theory's members do not extend the block's.
    IncludeClash(IncludeClash),
    /// An `ext` member states no extension type the block can generate.
    Extension(ExtensionFault),
    /// A `law` member's statement is not a function type from named binders,
    /// sorts first and then paths, to a path between two terms.
    LawStatement,
    /// A `law` member named as an operation, a rule or another law of the
    /// block is: a model's members share one namespace.
    LawName(Name),
    /// An `under` row names no `theory` block its source reads before the
    /// rule's or imports unqualified.
    UnknownRowTheory(Name),
    /// An `under` row names a `theory` block of two sources its source
    /// imports unqualified, and none of its own.
    AmbiguousRowTheory(Name),
    /// An `under` row names one theory twice: a row holds each theory once.
    RepeatedRowTheory
    {
        /// The theory named twice.
        name: Name,
        /// The bytes its first naming covers.
        first: ByteSpan,
    },
}

/// A pair of theories a block reaches with more than one join among the
/// theories it sees: two minimal common extensions, neither reaching the
/// other.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct JoinFault
{
    /// The two theories, in the order the block reaches them.
    pub pair: [Name; 2],
    /// Every minimal common extension, in reading order, the block last.
    pub joins: Vec<Name>,
}

/// Why an `ext Cell = Val on left is zero` member generates nothing.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ExtensionFault
{
    /// The block states no `shape` for a cell to be stated over.
    Unshaped,
    /// The shape has no face of the name the member fixes the cell on.
    UnknownFace(Name),
    /// The face holds every point of the shape, so a cell has no value of its
    /// own and its η law no direction.
    CoveringFace(Name),
    /// The extended type is not an unindexed sort of the block, or is the
    /// cell sort itself.
    Carrier(Name),
    /// The boundary is neither a constant nor an operation of no inputs, of one
    /// output at the extended type.
    Boundary(Name),
}

pub mod embed;
