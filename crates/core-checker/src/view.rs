//! The fragment's reading of a type node: the formers the judgement has rules
//! for, and a refusal by name for every other.
//!
//! # One place decides the fragment's types
//!
//! The core vocabulary has more type formers than the judgement has rules for.
//! Formation, the shape a check rule demands of its expected type, the shape an
//! elimination demands of a synthesised type, conversion and the kernel
//! bridge's erasure all read a type node through the two views here, so the
//! fragment's boundary on the type side is decided once: a former outside it is
//! [`FragmentRefusal::OutOfFragment`] wherever it is met, and no rule sees it.
//!
//! # A refusal only a view can give
//!
//! A view refuses for two reasons and no others, so its refusal is its own
//! two-variant type; the judgement and the bridge each convert it into their
//! own vocabulary, and neither handles a refusal a view cannot give.

use gandr_core_term::CompType;
use gandr_core_term::CompTypeId;
use gandr_core_term::CoreArena;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_kernel_term::BaseType;

use crate::refusal::CheckRefusal;
use crate::refusal::CoreNode;
use crate::refusal::TypeNode;
use crate::refusal::UnadmittedFormer;

/// Why a type node has no view.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum FragmentRefusal
{
    /// The id names no node of the arena.
    DanglingNode
    {
        /// The id.
        node: CoreNode,
    },
    /// The node's former has no rule in the fragment.
    OutOfFragment
    {
        /// The node carrying the former.
        at: CoreNode,
        /// The former.
        former: UnadmittedFormer,
    },
}

impl From<FragmentRefusal> for CheckRefusal
{
    /// The judgement's refusal for a node its views cannot read.
    ///
    /// # Specification
    /// - ensures: each variant becomes the [`CheckRefusal`] variant of the same
    ///   name, with the same payload.
    /// - panics: none.
    #[inline]
    fn from(refusal: FragmentRefusal) -> Self
    {
        match refusal {
            | FragmentRefusal::DanglingNode { node } => Self::DanglingNode { node },
            | FragmentRefusal::OutOfFragment { at, former } => Self::OutOfFragment { at, former },
        }
    }
}

/// A value type the fragment admits, with its children.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum ValueTypeView
{
    /// The integer atom.
    Integer,
    /// The string atom.
    String,
    /// The unit type.
    Unit,
    /// The thunk type `U C` of the computation type held.
    Thunk(CompTypeId),
}

/// A computation type the fragment admits, with its children.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum CompTypeView
{
    /// The returner `F A` of the value type held.
    Returner(ValueTypeId),
    /// The non-dependent arrow `A → C`.
    Arrow
    {
        /// The value-type domain.
        domain: ValueTypeId,
        /// The computation-type codomain.
        codomain: CompTypeId,
    },
}

/// Read a value-type node as the fragment admits it.
///
/// # Specification
/// - requires: nothing — a dangling id and a former outside the fragment are
///   both admissible input and both refused.
/// - ensures: the node's view when its former is the integer atom, the string
///   atom, the unit type or a thunk type; the children are the node's own.
/// - provides: the one decision of which value types the judgement and the
///   bridge reason about.
/// - fails: [`FragmentRefusal::DanglingNode`] when the id names no node of
///   `arena`; [`FragmentRefusal::OutOfFragment`], naming the former, for the
///   numeric atom, a product, a sum, a universe, a lift, an element type or an
///   abstract atom.
/// - panics: none.
///
/// # Errors
/// - [`FragmentRefusal::DanglingNode`] — the id does not resolve.
/// - [`FragmentRefusal::OutOfFragment`] — the former has no rule in the
///   fragment.
///
/// # Adequacy
/// - hypothesis: L3 — the decision surface is the per-former table, separated
///   by one node of every value-type former of the core vocabulary, each
///   asserted to view or to refuse with its exact former, plus a dangling id.
/// - witness: `formation::tests::every_value_type_former_is_answered_by_a_rule`
/// - witness: `formation::tests::a_dangling_type_is_refused_as_a_fault`
pub fn value_type_view(
    arena: &CoreArena,
    value_type: ValueTypeId,
) -> Result<ValueTypeView, FragmentRefusal>
{
    let at = CoreNode::Type(TypeNode::Value(value_type));
    let Some(node) = arena.value_type(value_type)
    else {
        return Err(FragmentRefusal::DanglingNode { node: at });
    };
    let unadmitted = |former| FragmentRefusal::OutOfFragment { at, former };
    match *node {
        | ValueType::Base(BaseType::Integer) => Ok(ValueTypeView::Integer),
        | ValueType::Base(BaseType::String) => Ok(ValueTypeView::String),
        | ValueType::Base(BaseType::Numeric) => Err(unadmitted(UnadmittedFormer::NumericAtom)),
        | ValueType::Unit => Ok(ValueTypeView::Unit),
        | ValueType::Thunk(body) => Ok(ValueTypeView::Thunk(body)),
        | ValueType::Product(..) => Err(unadmitted(UnadmittedFormer::Product)),
        | ValueType::Sum(..) => Err(unadmitted(UnadmittedFormer::Sum)),
        | ValueType::Universe(_) => Err(unadmitted(UnadmittedFormer::Universe)),
        | ValueType::Lift { .. } => Err(unadmitted(UnadmittedFormer::TypeLift)),
        | ValueType::Element { .. } => Err(unadmitted(UnadmittedFormer::Element)),
        | ValueType::Abstract(_) => Err(unadmitted(UnadmittedFormer::Abstract)),
    }
}

/// Read a computation-type node as the fragment admits it.
///
/// # Specification
/// - requires: nothing — a dangling id and a former outside the fragment are
///   both admissible input and both refused.
/// - ensures: the node's view when its former is a returner or a non-dependent
///   arrow; the children are the node's own.
/// - provides: the one decision of which computation types the judgement and
///   the bridge reason about.
/// - fails: [`FragmentRefusal::DanglingNode`] when the id names no node of
///   `arena`; [`FragmentRefusal::OutOfFragment`] naming
///   [`UnadmittedFormer::Pi`] for a dependent function type.
/// - panics: none.
///
/// # Errors
/// - [`FragmentRefusal::DanglingNode`] — the id does not resolve.
/// - [`FragmentRefusal::OutOfFragment`] — the dependent arrow has no rule in
///   the fragment.
///
/// # Adequacy
/// - hypothesis: L3 — the decision surface is the three-former table, separated
///   by one node of each former, the dependent arrow asserted to refuse with
///   its exact former and the arrow to view with its own children.
/// - witness: `formation::tests::every_comp_type_former_is_answered_by_a_rule`
/// - witness: `formation::tests::the_dependent_arrow_is_refused_and_the_arrow_forms`
pub fn comp_type_view(
    arena: &CoreArena,
    comp_type: CompTypeId,
) -> Result<CompTypeView, FragmentRefusal>
{
    let at = CoreNode::Type(TypeNode::Computation(comp_type));
    let Some(node) = arena.comp_type(comp_type)
    else {
        return Err(FragmentRefusal::DanglingNode { node: at });
    };
    match *node {
        | CompType::Returner(result) => Ok(CompTypeView::Returner(result)),
        | CompType::Arrow { domain, codomain } => Ok(CompTypeView::Arrow { domain, codomain }),
        | CompType::Pi { .. } => Err(FragmentRefusal::OutOfFragment {
            at,
            former: UnadmittedFormer::Pi,
        }),
    }
}
