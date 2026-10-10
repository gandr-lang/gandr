//! The first-order code universe of gandr's levitated descriptions: codes,
//! the declaration table they populate, and the generic programs and checks
//! driven by it.
//!
//! A [`Code`] is one constructor's payload shape in the fragment
//! `{1, var, ×, σ}` with two leaf decorations: a field over a symbolic value
//! type ([`ValueTypeRef`]) carrying a grade and an attribute Σ, and an
//! atom-abstraction. The fragment is first-order, so code equality is
//! decidable and [`Code`] derives it. A [`SignDesc`] is the declaration table
//! for one signature: its minted identity, its sort set, its graded
//! parameters, its constructors (the σ tag over codes), its operations with
//! multi-output [`BridgeArity`] shapes, its rule faces ([`RuleFace`]) over
//! free terms ([`FreeTerm`]), and its circuit rules ([`CircuitRule`]), whose
//! boundary pair is derived from a wiring ([`derive_boundaries`]) and whose
//! filler elaborates to a whiskered composite ([`elaborate_body`]).
//!
//! The generic programs — [`generic_eq`], [`serialize_value`] and
//! [`serialize_desc`] — read any description, declared or retrofitted
//! ([`bool_desc`], [`option_desc`], [`list_desc`], [`pair_desc`],
//! [`sum_desc`]), uniformly. [`check_desc`] is the host-side well-formedness
//! pass, and [`TypedRuleFace`] pairs a face with a signature context decoded
//! by a caller-supplied decoder.
//!
//! The crate names no type of any other gandr crate. A field's grade is the
//! type parameter `G` of [`Code`] and [`SignDesc`], and a decoded type is the
//! type parameter of [`PatternContext`]; decoding a code into a core type
//! universe belongs to the consumer that owns that universe. Every recursive
//! datum — a code, a value type reference, a free term, a payload, a
//! whiskered composite — is held flat, so no walk over one recurses.
//!
//! The crate is `no_std` and depends on `core`, `alloc` and the shape
//! vocabulary of `quenchant-shape`. The papers it draws on are in its
//! `README.md`, § References.

#![no_std]

extern crate alloc;

mod arity;
mod boundary;
mod builtin;
mod circuit;
mod code;
mod desc;
mod elaborate;
mod generic;
mod rule;
pub mod tree;
mod typed_rule;
mod wellformed;

pub use crate::arity::BridgeArity;
pub use crate::arity::SortRef;
pub use crate::boundary::AttributeEmptiness;
pub use crate::boundary::AttributePresence;
pub use crate::boundary::CircuitNodeBudget;
pub use crate::boundary::ConstructorTag;
pub use crate::boundary::ContextTotality;
pub use crate::boundary::DiagnosticMessage;
pub use crate::boundary::FirstOrderStatus;
pub use crate::boundary::GenericEquality;
pub use crate::boundary::LeafBytes;
pub use crate::boundary::MonomialCount;
pub use crate::boundary::NameRef;
pub use crate::boundary::NominalSerial;
pub use crate::boundary::PortArgumentCount;
pub use crate::boundary::RecursiveStatus;
pub use crate::boundary::RuleVariableLinearity;
pub use crate::boundary::SerializedDescText;
pub use crate::boundary::SerializedValueBytes;
pub use crate::boundary::SurfaceByteOffset;
pub use crate::boundary::TermPositionIndex;
pub use crate::builtin::bool_desc;
pub use crate::builtin::list_desc;
pub use crate::builtin::option_desc;
pub use crate::builtin::pair_desc;
pub use crate::builtin::sum_desc;
pub use crate::circuit::BoundaryReading;
pub use crate::circuit::CircuitBody;
pub use crate::circuit::CircuitDerivationError;
pub use crate::circuit::CircuitFrame;
pub use crate::circuit::CircuitNode;
pub use crate::circuit::CircuitRedex;
pub use crate::circuit::CircuitRule;
pub use crate::circuit::DerivedBoundaries;
pub use crate::circuit::FrameHead;
pub use crate::circuit::derive_boundaries;
pub use crate::circuit::derive_boundaries_within;
pub use crate::circuit::derive_boundary;
pub use crate::circuit::derive_boundary_within;
pub use crate::code::AtomSort;
pub use crate::code::Attr;
pub use crate::code::Attrs;
pub use crate::code::Code;
pub use crate::code::CodeArgs;
pub use crate::code::CodeNode;
pub use crate::code::CodeView;
pub use crate::code::Name;
pub use crate::code::PrimTy;
pub use crate::code::ValueTypeArgs;
pub use crate::code::ValueTypeNode;
pub use crate::code::ValueTypeRef;
pub use crate::code::ValueTypeView;
pub use crate::code::primitive_label;
pub use crate::desc::CtorDesc;
pub use crate::desc::DeclPolarity;
pub use crate::desc::NominalId;
pub use crate::desc::OperDesc;
pub use crate::desc::ParamDesc;
pub use crate::desc::SignDesc;
pub use crate::desc::SortDesc;
pub use crate::desc::SortIndex;
pub use crate::desc::SurfaceSpan;
pub use crate::elaborate::ActiveCell;
pub use crate::elaborate::CircuitElaborationError;
pub use crate::elaborate::InterfacePair;
pub use crate::elaborate::PortFace;
pub use crate::elaborate::PortInstantiationError;
pub use crate::elaborate::RedexOccurrence;
pub use crate::elaborate::RewritePort;
pub use crate::elaborate::Whisker;
pub use crate::elaborate::WhiskeredCell;
pub use crate::elaborate::active_position;
pub use crate::elaborate::elaborate_body;
pub use crate::elaborate::redex_occurrences;
pub use crate::generic::DescValue;
pub use crate::generic::Payload;
pub use crate::generic::PayloadArgs;
pub use crate::generic::PayloadNode;
pub use crate::generic::PayloadView;
pub use crate::generic::Side;
pub use crate::generic::generic_eq;
pub use crate::generic::serialize_desc;
pub use crate::generic::serialize_value;
pub use crate::rule::FreeTerm;
pub use crate::rule::RuleFace;
pub use crate::rule::RuleVarMeta;
pub use crate::rule::TermArgs;
pub use crate::rule::TermNode;
pub use crate::rule::TermView;
pub use crate::rule::Variance;
pub use crate::typed_rule::PatternContext;
pub use crate::typed_rule::TypedRuleFace;
pub use crate::typed_rule::pattern_variable;
pub use crate::wellformed::RESERVED_DERIVED_MARKERS;
pub use crate::wellformed::WfDiagnostic;
pub use crate::wellformed::WfKind;
pub use crate::wellformed::check_desc;
pub use crate::wellformed::derive_cell_var_meta;
pub use crate::wellformed::diagnostic_span;

#[cfg(test)]
mod test_support
{
    /// A stand-in grade vocabulary for the unit tests: the crate is generic
    /// over the grade a field carries, and a consumer supplies its own.
    #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
    pub enum Grade
    {
        /// The linear grade.
        One,
        /// The unrestricted grade.
        Omega,
    }
}
