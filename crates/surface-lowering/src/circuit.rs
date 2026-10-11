//! Ruled circuit bodies, their literal wiring diagrams and matcher boundary.

use gandr_theory_levitation::CircuitDerivationError;
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

/// The number of output ports a term-shaped cell cannot represent.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct OutputCount(pub usize);

/// A ruled signature's explicit boundary, independent of diagnostic wording.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SignatureFault
{
    /// A signature member requires its colon-led judgment.
    MissingJudgment,
    /// A sign block presents sorts, operations and rules, not item-level data.
    RetiredDataMember,
    /// A written face belongs in a data or codata block.
    WrittenFace,
    /// An expression CST node cannot silently become a circuit binder group.
    ExpressionEndpoint,
    /// An operation filler is outside the description route.
    OperationFiller,
    /// A fillerless higher cell has no circuit body to elaborate.
    HigherCell,
    /// A node or rule interface has more than one output root.
    MultipleOutputs(OutputCount),
    /// A circuit rule must name the output from which its boundary is derived.
    MissingOutput,
    /// A feed line needs wheel semantics, not a term-shaped cell.
    Wheel,
    /// The glyph is reserved for reversible rewrites.
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
}

pub mod embed;
