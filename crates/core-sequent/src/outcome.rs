//! How a run of a focused command ends: a value returned to the empty frame
//! region, or a named reason the run stopped short of one. Every executor of
//! the IL answers in these terms, and the dispatcher spells them.

use core::fmt;

use gandr_kernel_term::ConstantIndex;

use crate::il::CommandId;
use crate::il::ConsumerId;
use crate::il::DestructorTag;
use crate::store::HeapValueId;

/// Why a run stopped short of a value.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Stuck
{
    /// No reachable source handler or host accepted this operation.
    PerformNoHandler(CommandId),
    /// No reset is reachable across the structural continuation prefix.
    ShiftNoReset(CommandId),
    /// A resumption was supplied a value which is not a first-class stack.
    ResumedNonStack
    {
        /// The resumption command.
        at: CommandId,
        /// The supplied value.
        value: HeapValueId,
    },
    /// A native operation refused its arguments, including zero division.
    Primitive(gandr_core_term::primitive::PrimitiveError),
    /// A native operand has no scalar interpretation, retaining its blame site.
    NonScalar(HeapValueId),
    /// A constant with no admitted definition.
    UndefinedConstant(ConstantIndex),
    /// A constant whose definition needs its own value.
    CyclicConstant(ConstantIndex),
    /// A destructor met a value it cannot observe.
    Unobservable
    {
        /// The value.
        value: HeapValueId,
        /// The destructor.
        head: DestructorTag,
    },
    /// A match, a fold or a selection has no arm for the value it met: a
    /// selection meets something other than a tuple or a record, or one
    /// without the component or the label it names.
    Unmatched
    {
        /// The value.
        value: HeapValueId,
        /// The match, the fold or the selection.
        arms: ConsumerId,
    },
    /// An access answered with its view never ended: neither eliminator ran.
    Unended(CommandId),
    /// An access's index named no element of its held list: negative, or
    /// past the list's end.
    Outside(CommandId),
}

impl fmt::Display for Stuck
{
    /// Names what stopped the run.
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
            Self::PerformNoHandler(at) => write!(f, "operation at command {at} has no handler"),
            Self::ShiftNoReset(at) => write!(f, "shift at command {at} has no reset"),
            Self::ResumedNonStack { at, value } => {
                write!(f, "resume at command {at} received non-stack value {value}")
            },
            Self::Primitive(error) => write!(f, "native operation: {error}"),
            Self::NonScalar(value) => write!(f, "native operand {value} is not a scalar"),
            Self::UndefinedConstant(constant) => {
                write!(f, "constant {} has no definition", usize::from(constant))
            },
            Self::CyclicConstant(constant) => {
                write!(f, "constant {} needs its own value", usize::from(constant))
            },
            Self::Unobservable { value, .. } => write!(f, "value {value} cannot be observed"),
            Self::Unmatched { value, arms } => {
                write!(f, "match {arms} has no arm for value {value}")
            },
            Self::Unended(at) => write!(f, "access {at} reached its end with its view unended"),
            Self::Outside(at) => write!(f, "access {at} names no element of its held list"),
        }
    }
}

/// How a run ended.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Outcome
{
    /// The value returned to an empty frame region.
    Halted(HeapValueId),
    /// The run stopped short of a value.
    Stuck(Stuck),
}
