//! Type formation: a type is formed when every node it reaches is a former the
//! judgement has a rule for.
//!
//! # Formed is a type, not a promise
//!
//! The check faces take [`FormedValueType`] and [`FormedCompType`] rather than
//! bare ids, and the only ways to obtain one are formation itself and the
//! judgement, which hands out sub-nodes of formed types and the context's own
//! atoms. A check therefore never meets a former outside the fragment through
//! a fast path that did not look: the precondition is carried by the argument's
//! type.
//!
//! # The fragment's types carry no level
//!
//! The fragment has no universe, so every formed type lives at one implicit
//! level and formation decides membership alone; there is no classifier to
//! compute.
//!
//! # Linear in the distinct nodes
//!
//! Formation is a property of a node alone, so the walk visits each distinct
//! node once: a type sharing a subtree is formed in the number of its nodes,
//! not its expansion.

use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use gandr_core_term::CompTypeId;
use gandr_core_term::CoreArena;
use gandr_core_term::ValueTypeId;

use crate::context::CheckingContext;
use crate::refusal::CheckRefusal;
use crate::refusal::TypeNode;
use crate::view::CompTypeView;
use crate::view::ValueTypeView;
use crate::view::comp_type_view;
use crate::view::value_type_view;

/// A value type every node of which is a former of the fragment.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct FormedValueType(ValueTypeId);

/// A computation type every node of which is a former of the fragment.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct FormedCompType(CompTypeId);

impl FormedValueType
{
    /// A value type known formed because it is a sub-node of a formed type or
    /// one of the context's atoms.
    ///
    /// # Specification
    /// - requires: `id` is reachable from a formed type, or is an atom the
    ///   context minted.
    /// - ensures: [`Self::id`] returns `id`.
    /// - panics: none.
    pub(crate) const fn derived(id: ValueTypeId) -> Self
    {
        Self(id)
    }

    /// The node.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn id(self) -> ValueTypeId
    {
        self.0
    }
}

impl FormedCompType
{
    /// A computation type known formed because it is a sub-node of a formed
    /// type.
    ///
    /// # Specification
    /// - requires: `id` is reachable from a formed type.
    /// - ensures: [`Self::id`] returns `id`.
    /// - panics: none.
    pub(crate) const fn derived(id: CompTypeId) -> Self
    {
        Self(id)
    }

    /// The node.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn id(self) -> CompTypeId
    {
        self.0
    }
}

/// Form the value type `value_type`.
///
/// # Specification
/// - requires: nothing — a dangling id and a former outside the fragment are
///   admissible input and refused.
/// - ensures: every node `value_type` reaches is the integer atom, the string
///   atom, the unit type, a thunk type, a returner or a non-dependent arrow.
/// - provides: the formed type a check face takes.
/// - fails: [`CheckRefusal::OutOfFragment`] naming the first unadmitted former
///   the walk meets, and [`CheckRefusal::DanglingNode`] for an id the arena
///   does not hold.
/// - panics: none.
/// - intension: each distinct node is read once.
///
/// # Errors
/// - [`CheckRefusal::OutOfFragment`] — a reached former has no rule.
/// - [`CheckRefusal::DanglingNode`] — a reached id does not resolve.
///
/// # Adequacy
/// - hypothesis: L3 — the decision surfaces are the per-former views and the
///   walk's reach, separated by a formed type of every admitted former, an
///   unadmitted former at the root and one beneath an arrow, and a dangling
///   child.
/// - witness: `formation::tests::the_fragment_atoms_form`
/// - witness: `formation::tests::every_value_type_former_is_answered_by_a_rule`
/// - witness: `formation::tests::an_unadmitted_former_beneath_an_arrow_is_found`
/// - witness: `formation::tests::a_dangling_type_is_refused_as_a_fault`
#[inline]
pub fn form_value_type(
    context: &CheckingContext<'_>,
    value_type: ValueTypeId,
) -> Result<FormedValueType, CheckRefusal>
{
    walk(context.arena(), TypeNode::Value(value_type))?;
    Ok(FormedValueType(value_type))
}

/// Form the computation type `comp_type`.
///
/// # Specification
/// - requires: nothing — a dangling id and a former outside the fragment are
///   admissible input and refused.
/// - ensures: every node `comp_type` reaches is a former of the fragment, as
///   for [`form_value_type`].
/// - provides: the formed type a computation check face takes.
/// - fails: as for [`form_value_type`].
/// - panics: none.
/// - intension: each distinct node is read once.
///
/// # Errors
/// - [`CheckRefusal::OutOfFragment`] — a reached former has no rule.
/// - [`CheckRefusal::DanglingNode`] — a reached id does not resolve.
///
/// # Adequacy
/// - hypothesis: L3 — as for [`form_value_type`], over the computation formers,
///   separated by the arrow and the returner forming and the dependent arrow
///   refused by name.
/// - witness: `formation::tests::every_comp_type_former_is_answered_by_a_rule`
/// - witness: `formation::tests::the_dependent_arrow_is_refused_and_the_arrow_forms`
#[inline]
pub fn form_comp_type(
    context: &CheckingContext<'_>,
    comp_type: CompTypeId,
) -> Result<FormedCompType, CheckRefusal>
{
    walk(context.arena(), TypeNode::Computation(comp_type))?;
    Ok(FormedCompType(comp_type))
}

/// Read every node `root` reaches through the fragment's views.
///
/// # Specification
/// - requires: nothing.
/// - ensures: success exactly when every reached node views.
/// - fails: the first refusal a view gives, in the walk's order.
/// - panics: none.
/// - intension: a worklist with a visited set, so each distinct node is read
///   once and no depth overflows a stack.
fn walk(
    arena: &CoreArena,
    root: TypeNode,
) -> Result<(), CheckRefusal>
{
    let mut pending = Vec::from([root]);
    let mut visited = BTreeSet::new();
    while let Some(node) = pending.pop() {
        if !visited.insert(node) {
            continue;
        }
        match node {
            | TypeNode::Value(value_type) => match value_type_view(arena, value_type)? {
                | ValueTypeView::Integer | ValueTypeView::String | ValueTypeView::Unit => {},
                | ValueTypeView::Thunk(body) => pending.push(TypeNode::Computation(body)),
            },
            | TypeNode::Computation(comp_type) => match comp_type_view(arena, comp_type)? {
                | CompTypeView::Returner(result) => pending.push(TypeNode::Value(result)),
                | CompTypeView::Arrow { domain, codomain } => {
                    pending.push(TypeNode::Computation(codomain));
                    pending.push(TypeNode::Value(domain));
                },
            },
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests
{
    use gandr_core_term::CoreArena;
    use gandr_core_term::Sort;
    use gandr_core_term::ValueTypeId;
    use gandr_kernel_strata::Level;
    use gandr_kernel_term::BaseType;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::GroundSort;

    use super::form_comp_type;
    use super::form_value_type;
    use crate::context::CheckBudget;
    use crate::context::CheckingContext;
    use crate::fixture::dangling_value_type;
    use crate::refusal::CheckRefusal;
    use crate::refusal::CoreNode;
    use crate::refusal::TypeNode;
    use crate::refusal::UnadmittedFormer;

    #[test]
    fn the_fragment_atoms_form()
    {
        let mut arena = CoreArena::new();
        let atoms = [
            arena.value_type_unit(),
            arena.value_type_base(BaseType::Integer),
            arena.value_type_base(BaseType::String),
        ];
        let context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        for atom in atoms {
            assert_eq!(
                form_value_type(&context, atom).map(super::FormedValueType::id),
                Ok(atom),
                "a fragment atom forms as itself"
            );
        }
    }

    #[test]
    fn every_value_type_former_is_answered_by_a_rule()
    {
        let mut arena = CoreArena::new();
        let unit = arena.value_type_unit();
        let returner = arena.comp_type_returner(unit);
        let code = arena.value_unit();
        let cases: [(ValueTypeId, Result<(), UnadmittedFormer>); 11] = [
            (arena.value_type_base(BaseType::Integer), Ok(())),
            (arena.value_type_base(BaseType::String), Ok(())),
            (
                arena.value_type_base(BaseType::Numeric),
                Err(UnadmittedFormer::NumericAtom),
            ),
            (unit, Ok(())),
            (arena.value_type_thunk(returner), Ok(())),
            (
                arena.value_type_product(unit, unit),
                Err(UnadmittedFormer::Product),
            ),
            (arena.value_type_sum(unit, unit), Err(UnadmittedFormer::Sum)),
            (
                arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero()),
                Err(UnadmittedFormer::Universe),
            ),
            (
                arena.value_type_lift(unit, Level::zero()),
                Err(UnadmittedFormer::TypeLift),
            ),
            (
                arena.value_type_element(code, Level::zero()),
                Err(UnadmittedFormer::Element),
            ),
            (
                arena.value_type_abstract(ConstantIndex::from(0_usize)),
                Err(UnadmittedFormer::Abstract),
            ),
        ];
        let context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        for (value_type, answer) in cases {
            let expected =
                answer
                    .map(|()| value_type)
                    .map_err(|former| CheckRefusal::OutOfFragment {
                        at: CoreNode::Type(TypeNode::Value(value_type)),
                        former,
                    });
            assert_eq!(
                form_value_type(&context, value_type).map(super::FormedValueType::id),
                expected,
                "every value-type former forms or is refused by name, never by a fallthrough"
            );
        }
    }

    #[test]
    fn every_comp_type_former_is_answered_by_a_rule()
    {
        let mut arena = CoreArena::new();
        let unit = arena.value_type_unit();
        let returner = arena.comp_type_returner(unit);
        let arrow = arena.comp_type_arrow(unit, returner);
        let pi = arena.comp_type_pi(unit, returner);
        let context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        assert_eq!(
            form_comp_type(&context, returner).map(super::FormedCompType::id),
            Ok(returner),
            "a returner forms"
        );
        assert_eq!(
            form_comp_type(&context, arrow).map(super::FormedCompType::id),
            Ok(arrow),
            "a non-dependent arrow forms"
        );
        assert_eq!(
            form_comp_type(&context, pi),
            Err(CheckRefusal::OutOfFragment {
                at: CoreNode::Type(TypeNode::Computation(pi)),
                former: UnadmittedFormer::Pi,
            }),
            "the dependent arrow is refused by name"
        );
    }

    #[test]
    fn the_dependent_arrow_is_refused_and_the_arrow_forms()
    {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let result = arena.comp_type_returner(integer);
        let arrow = arena.comp_type_arrow(integer, result);
        let pi = arena.comp_type_pi(integer, result);
        let thunked_arrow = arena.value_type_thunk(arrow);
        let thunked_pi = arena.value_type_thunk(pi);
        let context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        assert_eq!(
            form_value_type(&context, thunked_arrow).map(super::FormedValueType::id),
            Ok(thunked_arrow),
            "the arrow carries no binder and forms beneath a thunk"
        );
        assert_eq!(
            form_value_type(&context, thunked_pi),
            Err(CheckRefusal::OutOfFragment {
                at: CoreNode::Type(TypeNode::Computation(pi)),
                former: UnadmittedFormer::Pi,
            }),
            "the same children under a binder are refused, at the dependent node"
        );
    }

    #[test]
    fn an_unadmitted_former_beneath_an_arrow_is_found()
    {
        let mut arena = CoreArena::new();
        let unit = arena.value_type_unit();
        let product = arena.value_type_product(unit, unit);
        let result = arena.comp_type_returner(product);
        let arrow = arena.comp_type_arrow(unit, result);
        let context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        assert_eq!(
            form_comp_type(&context, arrow),
            Err(CheckRefusal::OutOfFragment {
                at: CoreNode::Type(TypeNode::Value(product)),
                former: UnadmittedFormer::Product,
            }),
            "formation reaches every node, not only the root"
        );
    }

    #[test]
    fn a_dangling_type_is_refused_as_a_fault()
    {
        let mut arena = CoreArena::new();
        let dangling = dangling_value_type();
        let context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        let refused = form_value_type(&context, dangling);
        assert_eq!(
            refused,
            Err(CheckRefusal::DanglingNode {
                node: CoreNode::Type(TypeNode::Value(dangling)),
            }),
            "an id the arena does not hold is refused rather than read"
        );
    }
}
