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
//! # A view reads a node, and unfolds nothing
//!
//! A decode `El c` is viewed as it stands, its code and level exposed. Whether
//! the code is a constant whose body is a quote, so that the decode stands for
//! another type, is the judgement's question — it is answered through the
//! normaliser's conversion with a certificate — and never a view's.
//!
//! # A refusal only a view can give
//!
//! A view refuses for two reasons and no others, so its refusal is its own
//! two-variant type; the judgement and the bridge each convert it into their
//! own vocabulary, and neither handles a refusal a view cannot give.

use anodized::spec;
use gandr_core_term::CompType;
use gandr_core_term::CompTypeId;
use gandr_core_term::CoreArena;
use gandr_core_term::Sort;
use gandr_core_term::ValueId;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_kernel_strata::Level;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::GroundSort;

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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a dangling value-type id and each rejected former are
    ///   observed as named checker refusals; this separates a lost node
    ///   identity or a fragment refusal misclassified as an engine fault.
    ///   Successful views are outside this conversion.
    /// - witness: `formation::tests::a_dangling_type_is_refused_as_a_fault`
    /// - witness: `formation::tests::unsupported_forms_have_nominal_kinds`
    #[spec(ensures: |ret| match refusal {
        | FragmentRefusal::DanglingNode { node } => ret == Self::DanglingNode { node },
        | FragmentRefusal::OutOfFragment { at, former } => ret == Self::OutOfFragment { at, former },
    })]
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
pub enum ValueTypeView<'arena>
{
    /// A native universe-path classifier over two codes.
    PathUniverse(ValueId, ValueId),
    /// A sum of two value types.
    Sum(ValueTypeId, ValueTypeId),
    /// The integer atom.
    Integer,
    /// The string atom.
    String,
    /// The unit type.
    Unit,
    /// The thunk type `U C` of the computation type held.
    Thunk(CompTypeId),
    /// The universe `Type[s, l]` of a ground sort.
    Universe
    {
        /// The family the universe classifies.
        sort: GroundSort,
        /// Its level.
        level: &'arena Level,
    },
    /// The lift of a value type into a higher universe.
    Lift
    {
        /// The type lifted.
        inner: ValueTypeId,
        /// The level it is lifted to.
        target: &'arena Level,
    },
    /// The value type a code denotes.
    Element
    {
        /// The code.
        code: ValueId,
        /// The level of the universe the code inhabits.
        target: &'arena Level,
    },
    /// The eager product `A × B` of two value types.
    Product(ValueTypeId, ValueTypeId),
    /// The static Pi: the classifier of a type operator from codes of its
    /// domain to codes of its codomain, which stands in the ambient context.
    StaticPi
    {
        /// The classifier of the operator's argument.
        domain: ValueTypeId,
        /// The classifier of what it builds.
        codomain: ValueTypeId,
    },
}

/// A computation type the fragment admits, with its children.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum CompTypeView<'arena>
{
    /// The returner `F A` of the value type held.
    Returner(ValueTypeId),
    /// The non-dependent arrow `A → C`: its codomain stands in the ambient
    /// context.
    Arrow
    {
        /// The value-type domain.
        domain: ValueTypeId,
        /// The computation-type codomain.
        codomain: CompTypeId,
    },
    /// The dependent arrow `Π (x : A). C`: its codomain is scoped under one
    /// binder of the domain.
    Pi
    {
        /// The value-type domain.
        domain: ValueTypeId,
        /// The computation-type codomain, under the binder.
        codomain: CompTypeId,
    },
    /// The computation type a code denotes.
    Element
    {
        /// The code.
        code: ValueId,
        /// The level of the universe the code inhabits.
        target: &'arena Level,
    },
}

/// Read a value-type node as the fragment admits it.
///
/// # Specification
/// - requires: nothing — a dangling id and a former outside the fragment are
///   both admissible input and both refused.
/// - ensures: the node's view when its former is the integer atom, the string
///   atom, the unit type, a thunk type, a universe of a ground sort, a lift, a
///   decode, an eager product or a static Pi; the children are the node's own.
/// - provides: the one decision of which value types the judgement and the
///   bridge reason about.
/// - fails: [`FragmentRefusal::DanglingNode`] when the id names no node of
///   `arena`; [`FragmentRefusal::OutOfFragment`], naming the former, for the
///   numeric atom, a sum, an abstract atom and a universe over a sort
///   parameter.
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
/// - witness: `formation::tests::every_value_type_constructor_has_a_formation_rule`
/// - witness: `formation::tests::abstract_sort_raises_the_exact_variant`
/// - witness: `formation::tests::a_dangling_type_is_refused_as_a_fault`
#[spec(ensures: |ret| match ret {
    | Ok(ValueTypeView::Integer) => matches!(arena.value_type(value_type), Some(ValueType::Base(BaseType::Integer))),
    | Ok(ValueTypeView::String) => matches!(arena.value_type(value_type), Some(ValueType::Base(BaseType::String))),
    | Ok(ValueTypeView::Unit) => matches!(arena.value_type(value_type), Some(ValueType::Unit)),
    | Ok(ValueTypeView::Thunk(held)) => matches!(arena.value_type(value_type), Some(ValueType::Thunk(inner)) if *inner == held),
    | Ok(ValueTypeView::PathUniverse(first, second)) => matches!(arena.value_type(value_type), Some(ValueType::PathUniverse(left, right)) if *left == first && *right == second),
    | Ok(ValueTypeView::Sum(first, second)) => matches!(arena.value_type(value_type), Some(ValueType::Sum(left, right)) if *left == first && *right == second),
    | Ok(ValueTypeView::Product(first, second)) => matches!(arena.value_type(value_type), Some(ValueType::Product(left, right)) if *left == first && *right == second),
    | Ok(ValueTypeView::Universe { sort, level }) => matches!(arena.value_type(value_type), Some(ValueType::Universe { sort: Sort::Ground(found), level: found_level }) if *found == sort && found_level == level),
    | Ok(ValueTypeView::Lift { inner, target }) => matches!(arena.value_type(value_type), Some(ValueType::Lift { inner: found, target: found_target }) if *found == inner && found_target == target),
    | Ok(ValueTypeView::Element { code, target }) => matches!(arena.value_type(value_type), Some(ValueType::Element { code: found, target: found_target }) if *found == code && found_target == target),
    | Ok(ValueTypeView::StaticPi { domain, codomain }) => matches!(arena.value_type(value_type), Some(ValueType::StaticPi { domain: found_domain, codomain: found_codomain }) if *found_domain == domain && *found_codomain == codomain),
    | Err(FragmentRefusal::DanglingNode { node }) => arena.value_type(value_type).is_none() && node == CoreNode::Type(TypeNode::Value(value_type)),
    | Err(FragmentRefusal::OutOfFragment { at, former }) => at == CoreNode::Type(TypeNode::Value(value_type))
        && matches!((arena.value_type(value_type), former),
            (Some(ValueType::Base(BaseType::Numeric)), UnadmittedFormer::NumericAtom)

                | (Some(ValueType::Abstract(_)), UnadmittedFormer::Abstract)
                | (Some(ValueType::Universe { sort: Sort::Parameter(_), .. }), UnadmittedFormer::SortParameter)),
})]
pub fn value_type_view(
    arena: &CoreArena,
    value_type: ValueTypeId,
) -> Result<ValueTypeView<'_>, FragmentRefusal>
{
    let at = CoreNode::Type(TypeNode::Value(value_type));
    let Some(node) = arena.value_type(value_type)
    else {
        return Err(FragmentRefusal::DanglingNode { node: at });
    };
    let unadmitted = |former| FragmentRefusal::OutOfFragment { at, former };
    match *node {
        | ValueType::PathUniverse(source, target) => {
            Ok(ValueTypeView::PathUniverse(source, target))
        },
        | ValueType::Base(BaseType::Integer) => Ok(ValueTypeView::Integer),
        | ValueType::Base(BaseType::String) => Ok(ValueTypeView::String),
        | ValueType::Base(BaseType::Numeric) => Err(unadmitted(UnadmittedFormer::NumericAtom)),
        | ValueType::Unit => Ok(ValueTypeView::Unit),
        | ValueType::Thunk(body) => Ok(ValueTypeView::Thunk(body)),
        | ValueType::Product(first, second) => Ok(ValueTypeView::Product(first, second)),
        | ValueType::Sum(first, second) => Ok(ValueTypeView::Sum(first, second)),
        | ValueType::Universe {
            sort: Sort::Ground(sort),
            ref level,
        } => Ok(ValueTypeView::Universe { sort, level }),
        | ValueType::Universe {
            sort: Sort::Parameter(_),
            ..
        } => Err(unadmitted(UnadmittedFormer::SortParameter)),
        | ValueType::Lift { inner, ref target } => Ok(ValueTypeView::Lift { inner, target }),
        | ValueType::Element { code, ref target } => Ok(ValueTypeView::Element { code, target }),
        | ValueType::Abstract(_) => Err(unadmitted(UnadmittedFormer::Abstract)),
        | ValueType::StaticPi { domain, codomain } => {
            Ok(ValueTypeView::StaticPi { domain, codomain })
        },
    }
}

/// Read a computation-type node as the fragment admits it.
///
/// # Specification
/// - requires: nothing — a dangling id is admissible input and refused.
/// - ensures: the node's view for every computation former: a returner, an
///   arrow, a dependent arrow and a decode; the children are the node's own.
/// - provides: the one decision of which computation types the judgement and
///   the bridge reason about.
/// - fails: [`FragmentRefusal::DanglingNode`] when the id names no node of
///   `arena`.
/// - panics: none.
///
/// # Errors
/// - [`FragmentRefusal::DanglingNode`] — the id does not resolve.
///
/// # Adequacy
/// - hypothesis: L3 — the decision surface is the four-former table, separated
///   by one node of each former viewed with its own children.
/// - witness: `formation::tests::every_comp_type_constructor_has_a_formation_rule`
/// - witness: `formation::tests::the_dependent_arrow_forms_at_the_join_of_its_levels`
/// - witness: `view::tests::both_views_refuse_ids_missing_from_their_arena`
#[spec(ensures: |ret| match (arena.comp_type(comp_type), ret) {
    | (Some(&CompType::Returner(inner)), Ok(CompTypeView::Returner(held))) => inner == held,
    | (Some(&CompType::Arrow { domain, codomain }), Ok(CompTypeView::Arrow { domain: found_domain, codomain: found_codomain }))
    | (Some(&CompType::Pi { domain, codomain }), Ok(CompTypeView::Pi { domain: found_domain, codomain: found_codomain })) => domain == found_domain && codomain == found_codomain,
    | (Some(&CompType::Element { code, ref target }), Ok(CompTypeView::Element { code: found, target: found_target })) => code == found && target == found_target,
    | (None, Err(FragmentRefusal::DanglingNode { node })) => node == CoreNode::Type(TypeNode::Computation(comp_type)),
    | _ => false,
})]
pub fn comp_type_view(
    arena: &CoreArena,
    comp_type: CompTypeId,
) -> Result<CompTypeView<'_>, FragmentRefusal>
{
    let at = CoreNode::Type(TypeNode::Computation(comp_type));
    let Some(node) = arena.comp_type(comp_type)
    else {
        return Err(FragmentRefusal::DanglingNode { node: at });
    };
    match *node {
        | CompType::Returner(result) => Ok(CompTypeView::Returner(result)),
        | CompType::Arrow { domain, codomain } => Ok(CompTypeView::Arrow { domain, codomain }),
        | CompType::Pi { domain, codomain } => Ok(CompTypeView::Pi { domain, codomain }),
        | CompType::Element { code, ref target } => Ok(CompTypeView::Element { code, target }),
    }
}

#[cfg(test)]
mod tests
{
    use gandr_core_term::CoreArena;

    use super::FragmentRefusal;
    use super::comp_type_view;
    use super::value_type_view;
    use crate::refusal::CoreNode;
    use crate::refusal::TypeNode;

    #[test]
    fn both_views_refuse_ids_missing_from_their_arena()
    {
        let mut producer = CoreArena::new();
        let value_type = producer.value_type_unit();
        let comp_type = producer.comp_type_returner(value_type);
        let empty = CoreArena::new();
        assert_eq!(
            value_type_view(&empty, value_type),
            Err(FragmentRefusal::DanglingNode {
                node: CoreNode::Type(TypeNode::Value(value_type)),
            })
        );
        assert_eq!(
            comp_type_view(&empty, comp_type),
            Err(FragmentRefusal::DanglingNode {
                node: CoreNode::Type(TypeNode::Computation(comp_type)),
            })
        );
    }
}
