//! Type formation: a type is formed when every node it reaches is a former the
//! judgement has a rule for, every code it decodes inhabits the universe the
//! decode names, and every lift raises; a formed type has exactly one
//! [`Classifier`].
//!
//! # Formed is a type, not a promise
//!
//! The check faces take [`FormedValueType`] and [`FormedCompType`] rather than
//! bare ids, and the only ways to obtain one are formation itself and the
//! judgement, which hands out sub-nodes of formed types, the types it rewrites
//! from them, and the context's own atoms. A check therefore never meets a
//! former outside the fragment through a fast path that did not look: the
//! precondition is carried by the argument's type.
//!
//! # Formation is a judgement
//!
//! A decode `El c` holds a term, so whether it is formed is whether `c`
//! synthesises the universe the decode names, and a dependent arrow's codomain
//! is formed under a binder of its domain. Formation therefore runs as goals
//! of the judgement's own machine, beside the term goals it calls: one
//! machine, one allowance, no recursion between the two.
//!
//! # The classifier is read off the type
//!
//! Formation never asks a smallness question: a type is formed at its natural
//! level, computed compositionally. A value type is classified by the value
//! universe and a computation type by the computation universe, so the sort is
//! the type's family; the level is [`level_of`] — an atom's zero, a universe's
//! successor, a lift's or a decode's own level, and the join of a former's
//! children.

use alloc::vec::Vec;

use gandr_core_term::Classifier;
use gandr_core_term::CompTypeId;
use gandr_core_term::CoreArena;
use gandr_core_term::ValueTypeId;
use gandr_kernel_strata::Level;
use gandr_kernel_term::GroundSort;

use crate::context::CheckingContext;
use crate::judgement::form;
use crate::refusal::CheckRefusal;
use crate::refusal::CoreNode;
use crate::refusal::TypeNode;
use crate::refusal::UnadmittedFormer;
use crate::view::CompTypeView;
use crate::view::ValueTypeView;
use crate::view::comp_type_view;
use crate::view::value_type_view;

/// A value type every node of which is a former of the fragment, every code
/// of which inhabits the universe its decode names.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct FormedValueType(ValueTypeId);

/// A computation type every node of which is a former of the fragment, every
/// code of which inhabits the universe its decode names.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct FormedCompType(CompTypeId);

impl FormedValueType
{
    /// A value type known formed because it is a sub-node of a formed type, a
    /// rewrite of one, or one of the context's atoms.
    ///
    /// # Specification
    /// - requires: `id` is reachable from a formed type, a shift or an
    ///   instantiation of one, a decode of a formed code, or an atom the
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
    /// type or a rewrite of one.
    ///
    /// # Specification
    /// - requires: `id` is reachable from a formed type, or a shift or an
    ///   instantiation of one.
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

/// Form the value type `value_type` in the context's binders.
///
/// # Specification
/// - requires: nothing — a dangling id, a former outside the fragment and a
///   decode of an ill-typed code are admissible input and refused.
/// - ensures: every node `value_type` reaches views; every decode's code
///   synthesises, in the binders it stands under, the universe of the decode's
///   sort at exactly the decode's level; every dependent arrow's codomain is
///   formed under a binder of its domain; every lift's target lies strictly
///   above its type's level; no universe stands at the greatest level.
/// - provides: the formed type a check face takes.
/// - fails: [`CheckRefusal::OutOfFragment`] naming the first unadmitted former
///   the walk meets; the code's refusal for a decode, among them
///   [`CheckRefusal::SortMismatch`] and [`CheckRefusal::LevelMismatch`];
///   [`CheckRefusal::DanglingNode`] for an id the arena does not hold.
/// - panics: none.
/// - intension: one machine run under the context's allowance; the binders
///   stand where they stood on entry, whatever the outcome.
///
/// # Errors
/// - [`CheckRefusal`] — the type is not formed.
///
/// # Adequacy
/// - hypothesis: L1 over generated types — formation is total and answers one
///   classifier, the one a reference computed beside the generator — over an L3
///   residue: one node of every former of the vocabulary, each formed or
///   refused by its exact name, an unadmitted former beneath an arrow, a decode
///   of a code of the wrong sort and of a non-code, and a dangling child.
/// - witness: `formation::tests::every_value_type_constructor_has_a_formation_rule`
/// - witness: `formation::tests::unsupported_forms_have_nominal_kinds`
/// - witness: `formation::tests::an_unadmitted_former_beneath_an_arrow_is_found`
/// - witness: `formation::tests::a_dangling_type_is_refused_as_a_fault`
/// - witness: `formation::tests::every_type_has_exactly_one_classifier`
/// - witness: `context::tests::a_value_typed_hypothesis_does_not_become_a_type_variable`
/// - witness: `judgement::tests::a_value_type_in_a_computation_universe_is_a_sort_mismatch`
#[inline]
pub fn form_value_type(
    context: &mut CheckingContext<'_>,
    value_type: ValueTypeId,
) -> Result<FormedValueType, CheckRefusal>
{
    form(context, TypeNode::Value(value_type))?;
    Ok(FormedValueType(value_type))
}

/// Form the computation type `comp_type` in the context's binders.
///
/// # Specification
/// - requires: nothing — as for [`form_value_type`].
/// - ensures: as for [`form_value_type`], over the computation formers.
/// - provides: the formed type a computation check face takes.
/// - fails: as for [`form_value_type`].
/// - panics: none.
/// - intension: as for [`form_value_type`].
///
/// # Errors
/// - [`CheckRefusal`] — the type is not formed.
///
/// # Adequacy
/// - hypothesis: L3 — as for [`form_value_type`], over the computation formers,
///   separated by the returner, the arrow, the dependent arrow and a decode
///   each forming at its own classifier.
/// - witness: `formation::tests::every_comp_type_constructor_has_a_formation_rule`
/// - witness: `formation::tests::the_dependent_arrow_forms_at_the_join_of_its_levels`
#[inline]
pub fn form_comp_type(
    context: &mut CheckingContext<'_>,
    comp_type: CompTypeId,
) -> Result<FormedCompType, CheckRefusal>
{
    form(context, TypeNode::Computation(comp_type))?;
    Ok(FormedCompType(comp_type))
}

/// The classifier of the formed value type `formed`: the value universe at
/// its natural level.
///
/// # Specification
/// - requires: `formed` was formed in the context's arena.
/// - ensures: the value sort beside [`level_of`] the type.
/// - provides: the universe a formed value type inhabits.
/// - fails: as [`level_of`], which a formed type never meets.
/// - panics: none.
///
/// # Errors
/// - [`CheckRefusal`] — as [`level_of`].
///
/// # Adequacy
/// - hypothesis: L1 — as [`form_value_type`].
/// - witness: `formation::tests::every_type_has_exactly_one_classifier`
/// - witness: `formation::tests::universe_families_form_one_level_up_in_the_value_sort`
#[inline]
pub fn classify_value_type(
    context: &CheckingContext<'_>,
    formed: FormedValueType,
) -> Result<Classifier, CheckRefusal>
{
    Ok(Classifier {
        sort: GroundSort::Value,
        level: level_of(context.arena(), TypeNode::Value(formed.id()))?,
    })
}

/// The classifier of the formed computation type `formed`: the computation
/// universe at its natural level.
///
/// # Specification
/// - requires: `formed` was formed in the context's arena.
/// - ensures: the computation sort beside [`level_of`] the type.
/// - provides: the universe a formed computation type inhabits.
/// - fails: as [`level_of`], which a formed type never meets.
/// - panics: none.
///
/// # Errors
/// - [`CheckRefusal`] — as [`level_of`].
///
/// # Adequacy
/// - hypothesis: L3 — as [`form_comp_type`].
/// - witness: `formation::tests::arrow_forms_at_the_join_of_its_premise_levels`
/// - witness: `formation::tests::the_dependent_arrow_forms_at_the_join_of_its_levels`
#[inline]
pub fn classify_comp_type(
    context: &CheckingContext<'_>,
    formed: FormedCompType,
) -> Result<Classifier, CheckRefusal>
{
    Ok(Classifier {
        sort: GroundSort::Computation,
        level: level_of(context.arena(), TypeNode::Computation(formed.id()))?,
    })
}

/// A step of [`level_of`]'s walk.
#[derive(Clone, Copy, Debug)]
enum Task
{
    /// Read the level of a node onto the result stack.
    Enter(TypeNode),
    /// Replace the two results on top of the stack by their join.
    Join,
}

/// The natural level of `root`: the level of the universe it inhabits.
///
/// # Specification
/// - requires: nothing — a node outside the fragment and a dangling id are
///   admissible input and refused.
/// - ensures: zero for an atom and the unit type; the successor of its level
///   for a universe; its own level for a lift and a decode; its child's level
///   for a thunk type and a returner; the join of its children's for an eager
///   product, a static Pi, an arrow and a dependent arrow, whose codomain's
///   level does not depend on the binder.
/// - provides: the level part of every classifier, and the level a code is
///   decoded at when the judgement unfolds a code constant.
/// - fails: the view's refusal for a node outside the fragment or a dangling
///   id; [`CheckRefusal::OutOfFragment`] naming
///   [`UnadmittedFormer::TopUniverse`] for a universe at the greatest level.
/// - panics: none.
/// - intension: an explicit task stack, so no depth overflows a native one.
///
/// # Errors
/// - [`CheckRefusal`] — as above.
///
/// # Adequacy
/// - hypothesis: L1 — as [`form_value_type`]; the generator computes the
///   expected level by its own construction.
/// - witness: `formation::tests::every_type_has_exactly_one_classifier`
/// - witness: `formation::tests::arrow_forms_at_the_join_of_its_premise_levels`
#[inline]
pub fn level_of(
    arena: &CoreArena,
    root: TypeNode,
) -> Result<Level, CheckRefusal>
{
    let mut tasks = Vec::from([Task::Enter(root)]);
    let mut levels: Vec<Level> = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            | Task::Join => {
                let (Some(right), Some(left)) = (levels.pop(), levels.pop())
                else {
                    return Err(CheckRefusal::MachineInvariant);
                };
                levels.push(left.max(&right));
            },
            | Task::Enter(TypeNode::Value(at)) => match value_type_view(arena, at)? {
                | ValueTypeView::PathUniverse(source, target) => {
                    let _source = path_code(arena, source)?;
                    let _target = path_code(arena, target)?;
                    levels.push(Level::zero());
                },
                | ValueTypeView::Integer | ValueTypeView::String | ValueTypeView::Unit => {
                    levels.push(Level::zero());
                },
                | ValueTypeView::Thunk(body) => {
                    tasks.push(Task::Enter(TypeNode::Computation(body)));
                },
                | ValueTypeView::Universe { level, .. } => {
                    let Ok(above) = level.succ()
                    else {
                        return Err(CheckRefusal::OutOfFragment {
                            at: CoreNode::Type(TypeNode::Value(at)),
                            former: UnadmittedFormer::TopUniverse,
                        });
                    };
                    levels.push(above);
                },
                | ValueTypeView::Lift { target, .. } | ValueTypeView::Element { target, .. } => {
                    levels.push(target.clone());
                },
                | ValueTypeView::Sum(first, second)
                | ValueTypeView::Product(first, second)
                | ValueTypeView::StaticPi {
                    domain: first,
                    codomain: second,
                } => {
                    tasks.push(Task::Join);
                    tasks.push(Task::Enter(TypeNode::Value(second)));
                    tasks.push(Task::Enter(TypeNode::Value(first)));
                },
            },
            | Task::Enter(TypeNode::Computation(at)) => match comp_type_view(arena, at)? {
                | CompTypeView::Returner(result) => {
                    tasks.push(Task::Enter(TypeNode::Value(result)));
                },
                | CompTypeView::Arrow { domain, codomain }
                | CompTypeView::Pi { domain, codomain } => {
                    tasks.push(Task::Join);
                    tasks.push(Task::Enter(TypeNode::Computation(codomain)));
                    tasks.push(Task::Enter(TypeNode::Value(domain)));
                },
                | CompTypeView::Element { target, .. } => levels.push(target.clone()),
            },
        }
    }
    match (levels.pop(), levels.is_empty()) {
        | (Some(level), true) => Ok(level),
        | (Some(_) | None, _) => Err(CheckRefusal::MachineInvariant),
    }
}

/// Decode exactly the closed first-order fragment used by native paths.
///
/// # Specification
/// - ensures: every reachable type is Unit, Base, Sum or Product.
/// - fails: `PathCode` for any other endpoint or reachable former.
/// - panics: none.
///
/// # Errors
/// `CheckRefusal::PathCode`.
///
/// # Termination
/// - reason: a visited-node worklist over the finite arena.
/// - measure: unvisited reachable nodes.
///
/// # Adequacy
/// - hypothesis: L3 — a native Bool equivalence crosses; open codes refuse.
/// - witness: `bridge::tests::native_path_module_round_trips`
pub fn path_code(
    arena: &CoreArena,
    code: gandr_core_term::ValueId,
) -> Result<ValueTypeId, CheckRefusal>
{
    let Some(&gandr_core_term::Value::Quote(root)) = arena.value(code)
    else {
        return Err(CheckRefusal::PathCode(code));
    };
    let mut pending = Vec::from([root]);
    let mut seen = alloc::collections::BTreeSet::new();
    while let Some(node) = pending.pop() {
        if !seen.insert(node) {
            continue;
        }
        match arena.value_type(node) {
            | Some(&(gandr_core_term::ValueType::Base(_) | gandr_core_term::ValueType::Unit)) => {},
            | Some(
                &(gandr_core_term::ValueType::Product(a, b)
                | gandr_core_term::ValueType::Sum(a, b)),
            ) => pending.extend([a, b]),
            | _ => return Err(CheckRefusal::PathCode(code)),
        }
    }
    Ok(root)
}

#[cfg(test)]
mod tests
{
    use alloc::vec::Vec;

    use gandr_core_term::Binders;
    use gandr_core_term::Classifier;
    use gandr_core_term::CompTypeId;
    use gandr_core_term::CoreArena;
    use gandr_core_term::Sort;
    use gandr_core_term::SortParameter;
    use gandr_core_term::ValueTypeId;
    use gandr_core_term::Zone;
    use gandr_core_term::shift_value_type;
    use gandr_kernel_strata::Level;
    use gandr_kernel_strata::LevelConstant;
    use gandr_kernel_term::BaseType;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::DeBruijnIndex;
    use gandr_kernel_term::GroundSort;
    use proptest::collection::vec;
    use proptest::prelude::ProptestConfig;
    use proptest::prelude::prop_assert_eq;
    use proptest::prelude::proptest;

    use super::classify_comp_type;
    use super::classify_value_type;
    use super::form_comp_type;
    use super::form_value_type;
    use crate::context::CheckBudget;
    use crate::context::CheckingContext;
    use crate::fixture::dangling_value_type;
    use crate::fixture::seed;
    use crate::refusal::CheckRefusal;
    use crate::refusal::CoreNode;
    use crate::refusal::TypeNode;
    use crate::refusal::UnadmittedFormer;

    /// The level `n`.
    ///
    /// # Specification
    /// trivial.
    fn level(n: LevelConstant) -> Level
    {
        Level::constant(n)
    }

    /// The classifier of a value type at level `n`.
    ///
    /// # Specification
    /// trivial.
    fn value_at(n: LevelConstant) -> Classifier
    {
        Classifier {
            sort: GroundSort::Value,
            level: level(n),
        }
    }

    /// The classifier of a computation type at level `n`.
    ///
    /// # Specification
    /// trivial.
    fn comp_at(n: LevelConstant) -> Classifier
    {
        Classifier {
            sort: GroundSort::Computation,
            level: level(n),
        }
    }

    /// Form `value_type` in `context` and classify it.
    ///
    /// # Specification
    /// trivial.
    fn classified(
        context: &mut CheckingContext<'_>,
        value_type: ValueTypeId,
    ) -> Result<Classifier, CheckRefusal>
    {
        let formed = form_value_type(context, value_type)?;
        classify_value_type(context, formed)
    }

    /// Form `comp_type` in `context` and classify it.
    ///
    /// # Specification
    /// trivial.
    fn classified_comp(
        context: &mut CheckingContext<'_>,
        comp_type: CompTypeId,
    ) -> Result<Classifier, CheckRefusal>
    {
        let formed = form_comp_type(context, comp_type)?;
        classify_comp_type(context, formed)
    }

    #[test]
    fn universe_families_form_one_level_up_in_the_value_sort()
    {
        let mut arena = CoreArena::new();
        let value = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
        let computation =
            arena.value_type_universe(Sort::Ground(GroundSort::Computation), Level::zero());
        assert_ne!(
            value, computation,
            "the two families are two nodes at one level"
        );
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        let one = LevelConstant::from(1_u64);
        assert_eq!(classified(&mut context, value), Ok(value_at(one)));
        assert_eq!(
            classified(&mut context, computation),
            Ok(value_at(one)),
            "the computation universe is itself a value type, one level up"
        );
    }

    /// Every supported classifier is formed at its semantic level, and
    /// unsupported classifiers are refused by their boundary.
    #[test]
    fn every_value_type_constructor_has_a_formation_rule()
    {
        let mut arena = CoreArena::new();
        let unit = arena.value_type_unit();
        let returner = arena.comp_type_returner(unit);
        let small = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
        let code = arena.value_constant(ConstantIndex::from(0_usize));
        let closed = arena.value_quote(unit);
        let path = arena.value_type_path_universe(closed, closed);
        let one = LevelConstant::from(1_u64);
        let zero = LevelConstant::from(0_u64);
        let rows: [(ValueTypeId, Result<Classifier, UnadmittedFormer>); 13] = [
            (path, Ok(value_at(zero))),
            (arena.value_type_base(BaseType::Integer), Ok(value_at(zero))),
            (arena.value_type_base(BaseType::String), Ok(value_at(zero))),
            (
                arena.value_type_base(BaseType::Numeric),
                Err(UnadmittedFormer::NumericAtom),
            ),
            (unit, Ok(value_at(zero))),
            (arena.value_type_thunk(returner), Ok(value_at(zero))),
            (arena.value_type_product(unit, unit), Ok(value_at(zero))),
            (arena.value_type_sum(unit, unit), Ok(value_at(zero))),
            (small, Ok(value_at(one))),
            (arena.value_type_lift(unit, level(one)), Ok(value_at(one))),
            (
                arena.value_type_element(code, Level::zero()),
                Ok(value_at(zero)),
            ),
            (
                arena.value_type_abstract(ConstantIndex::from(0_usize)),
                Err(UnadmittedFormer::Abstract),
            ),
            (arena.value_type_static_pi(small, small), Ok(value_at(one))),
        ];

        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        seed(&mut context, &[small]);
        for (value_type, answer) in rows {
            let expected = answer.map_err(|former| CheckRefusal::OutOfFragment {
                at: CoreNode::Type(TypeNode::Value(value_type)),
                former,
            });
            assert_eq!(
                classified(&mut context, value_type),
                expected,
                "every value-type former forms at its classifier or is refused by name"
            );
        }
    }

    #[test]
    fn every_comp_type_constructor_has_a_formation_rule()
    {
        let mut arena = CoreArena::new();
        let unit = arena.value_type_unit();
        let small = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
        let negative =
            arena.value_type_universe(Sort::Ground(GroundSort::Computation), Level::zero());
        let returner = arena.comp_type_returner(unit);
        let code = arena.value_constant(ConstantIndex::from(1_usize));
        let zero = LevelConstant::from(0_u64);
        let rows = [
            (returner, comp_at(zero)),
            (arena.comp_type_arrow(unit, returner), comp_at(zero)),
            (
                arena.comp_type_pi(small, returner),
                comp_at(LevelConstant::from(1_u64)),
            ),
            (arena.comp_type_element(code, Level::zero()), comp_at(zero)),
        ];
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        seed(&mut context, &[small, negative]);
        for (comp_type, classifier) in rows {
            assert_eq!(
                classified_comp(&mut context, comp_type),
                Ok(classifier),
                "every computation-type former forms at its classifier"
            );
        }
    }

    /// Every form the fragment refuses is refused under a name the caller
    /// matches on, never under prose.
    #[test]
    fn unsupported_forms_have_nominal_kinds()
    {
        let mut arena = CoreArena::new();
        let unit = arena.value_type_unit();
        let top = Level::constant(LevelConstant::from(u64::MAX));
        let rows = [
            (
                arena.value_type_base(BaseType::Numeric),
                UnadmittedFormer::NumericAtom,
            ),
            (
                arena.value_type_abstract(ConstantIndex::from(0_usize)),
                UnadmittedFormer::Abstract,
            ),
            (
                arena.value_type_universe(
                    Sort::Parameter(SortParameter::from(0_u32)),
                    Level::zero(),
                ),
                UnadmittedFormer::SortParameter,
            ),
            (
                arena.value_type_universe(Sort::Ground(GroundSort::Value), top),
                UnadmittedFormer::TopUniverse,
            ),
            (
                arena.value_type_lift(unit, Level::zero()),
                UnadmittedFormer::TypeLift,
            ),
        ];
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        for (value_type, former) in rows {
            assert_eq!(
                form_value_type(&mut context, value_type),
                Err(CheckRefusal::OutOfFragment {
                    at: CoreNode::Type(TypeNode::Value(value_type)),
                    former,
                }),
                "the refusal names the form"
            );
        }
    }

    #[test]
    fn arrow_forms_at_the_join_of_its_premise_levels()
    {
        let mut arena = CoreArena::new();
        let one = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
        let two = arena.value_type_universe(
            Sort::Ground(GroundSort::Value),
            level(LevelConstant::from(1_u64)),
        );
        let returns_two = arena.comp_type_returner(two);
        let returns_one = arena.comp_type_returner(one);
        let higher_codomain = arena.comp_type_arrow(one, returns_two);
        let higher_domain = arena.comp_type_arrow(two, returns_one);
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        let expected = Ok(comp_at(LevelConstant::from(2_u64)));
        assert_eq!(classified_comp(&mut context, higher_codomain), expected);
        assert_eq!(
            classified_comp(&mut context, higher_domain),
            expected,
            "the join is symmetric in its premises"
        );
    }

    #[test]
    fn abstract_sort_raises_the_exact_variant()
    {
        let mut arena = CoreArena::new();
        let universe =
            arena.value_type_universe(Sort::Parameter(SortParameter::from(0_u32)), Level::zero());
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        assert_eq!(
            form_value_type(&mut context, universe),
            Err(CheckRefusal::OutOfFragment {
                at: CoreNode::Type(TypeNode::Value(universe)),
                former: UnadmittedFormer::SortParameter,
            }),
            "a universe over a sort parameter has no ground reading"
        );
    }

    /// The core vocabulary has no dependent pair and no package; the sealed
    /// atom a package's abstract component is stays refused by name, and the
    /// eager product a dependent pair generalises and the dependent arrow,
    /// refused beside it before, now form.
    #[test]
    fn sigma_and_package_are_refused_by_name()
    {
        let mut arena = CoreArena::new();
        let unit = arena.value_type_unit();
        let small = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
        let product = arena.value_type_product(unit, unit);
        let sealed = arena.value_type_abstract(ConstantIndex::from(0_usize));
        let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let decoded = arena.value_type_element(bound, Level::zero());
        let returner = arena.comp_type_returner(decoded);
        let pi = arena.comp_type_pi(small, returner);
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        assert_eq!(
            form_value_type(&mut context, product).map(super::FormedValueType::id),
            Ok(product),
            "the eager product forms over formed factors"
        );
        assert_eq!(
            form_value_type(&mut context, sealed),
            Err(CheckRefusal::OutOfFragment {
                at: CoreNode::Type(TypeNode::Value(sealed)),
                former: UnadmittedFormer::Abstract,
            })
        );
        assert_eq!(
            form_comp_type(&mut context, pi).map(super::FormedCompType::id),
            Ok(pi),
            "the dependent arrow binds its argument over its result and forms"
        );
    }

    #[test]
    fn the_dependent_arrow_forms_at_the_join_of_its_levels()
    {
        let mut arena = CoreArena::new();
        let small = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
        let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let decoded = arena.value_type_element(bound, Level::zero());
        let returner = arena.comp_type_returner(decoded);
        let pi = arena.comp_type_pi(small, returner);
        let thunked = arena.value_type_thunk(pi);
        let arrow = arena.comp_type_arrow(small, returner);
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        assert_eq!(
            classified_comp(&mut context, pi),
            Ok(comp_at(LevelConstant::from(1_u64))),
            "the domain is a universe at level one, the codomain a type at zero"
        );
        assert_eq!(
            classified(&mut context, thunked),
            Ok(value_at(LevelConstant::from(1_u64))),
            "and it forms beneath a thunk"
        );
        assert_eq!(
            form_comp_type(&mut context, arrow),
            Err(CheckRefusal::UnboundIndex {
                at: bound,
                zone: Zone::Intuitionistic,
                index: DeBruijnIndex::from(0_u32),
                depth: gandr_core_term::BinderDepth::from(0_usize),
            }),
            "the same children without the binder mention a variable nothing binds"
        );
    }

    #[test]
    fn an_unadmitted_former_beneath_an_arrow_is_found()
    {
        let mut arena = CoreArena::new();
        let unit = arena.value_type_unit();
        let numeric = arena.value_type_base(BaseType::Numeric);
        let result = arena.comp_type_returner(numeric);
        let arrow = arena.comp_type_arrow(unit, result);
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        assert_eq!(
            form_comp_type(&mut context, arrow),
            Err(CheckRefusal::OutOfFragment {
                at: CoreNode::Type(TypeNode::Value(numeric)),
                former: UnadmittedFormer::NumericAtom,
            }),
            "formation reaches every node, not only the root"
        );
    }

    #[test]
    fn a_dangling_type_is_refused_as_a_fault()
    {
        let mut arena = CoreArena::new();
        let dangling = dangling_value_type();
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        let refused = form_value_type(&mut context, dangling);
        assert_eq!(
            refused,
            Err(CheckRefusal::DanglingNode {
                node: CoreNode::Type(TypeNode::Value(dangling)),
            }),
            "an id the arena does not hold is refused rather than read"
        );
    }

    /// A step of a generated type: a postfix program over a stack of value
    /// types and computation types, each carrying the level it is formed at.
    #[derive(Clone, Copy, Debug)]
    enum Step
    {
        /// Push the integer atom.
        Integer,
        /// Push the unit type.
        Unit,
        /// Push the universe of the value sort, or of the computation sort, at
        /// a small level.
        Universe(bool, u8),
        /// Push the decode of the binder of the context counted round by the
        /// number held.
        Decode(u8),
        /// Pop a value type and push its returner.
        Returner,
        /// Pop a computation type and push its thunk type.
        Thunk,
        /// Pop a value type and a computation type and push their arrow.
        Arrow,
        /// Lift the value type on top to one level above its own.
        Lift,
    }

    /// The step strategy.
    ///
    /// # Specification
    /// trivial.
    fn step() -> impl proptest::strategy::Strategy<Value = Step>
    {
        use proptest::prelude::Just;
        use proptest::prelude::any;
        use proptest::prop_oneof;
        use proptest::strategy::Strategy as _;
        prop_oneof![
            Just(Step::Integer),
            Just(Step::Unit),
            (any::<bool>(), 0_u8 .. 3_u8).prop_map(|(positive, at)| Step::Universe(positive, at)),
            any::<u8>().prop_map(Step::Decode),
            Just(Step::Returner),
            Just(Step::Thunk),
            Just(Step::Arrow),
            Just(Step::Lift),
        ]
    }

    /// The generated value type and the level a reference reads off its
    /// construction, over a context of value universes at `levels`.
    struct Generated
    {
        /// The value type.
        root: ValueTypeId,
        /// The level the construction gives it.
        level: Level,
    }

    /// A level a generated binder's universe stands at: zero to two.
    ///
    /// # Specification
    /// trivial.
    fn small_level() -> impl proptest::strategy::Strategy<Value = LevelConstant>
    {
        use proptest::strategy::Strategy as _;
        (0_u64 .. 3_u64).prop_map(LevelConstant::from)
    }

    /// Build `steps` over a context of binders, the `i`th from the innermost
    /// a value universe at `levels[i]`, skipping every step the stacks cannot
    /// take, and close the result with returners and thunks into one value
    /// type.
    ///
    /// # Specification
    /// trivial.
    fn build(
        arena: &mut CoreArena,
        levels: &[LevelConstant],
        steps: &[Step],
    ) -> Generated
    {
        let mut values: Vec<(ValueTypeId, Level)> = Vec::new();
        let mut comps: Vec<(CompTypeId, Level)> = Vec::new();
        for &step in steps {
            match step {
                | Step::Integer => {
                    values.push((arena.value_type_base(BaseType::Integer), Level::zero()));
                },
                | Step::Unit => values.push((arena.value_type_unit(), Level::zero())),
                | Step::Universe(positive, at) => {
                    let sort = if positive {
                        GroundSort::Value
                    }
                    else {
                        GroundSort::Computation
                    };
                    let own = level(LevelConstant::from(u64::from(at)));
                    let above = own.succ().expect("a small level has a successor");
                    values.push((arena.value_type_universe(Sort::Ground(sort), own), above));
                },
                | Step::Decode(pick) => {
                    if let Some(position) = usize::from(pick).checked_rem(levels.len())
                        && let Some(&at) = levels.get(position)
                    {
                        let index = DeBruijnIndex::from(u32::try_from(position).expect("small"));
                        let code = arena.value_variable(Zone::Intuitionistic, index);
                        let own = level(at);
                        values.push((arena.value_type_element(code, own.clone()), own));
                    }
                },
                | Step::Returner => {
                    if let Some((result, own)) = values.pop() {
                        comps.push((arena.comp_type_returner(result), own));
                    }
                },
                | Step::Thunk => {
                    if let Some((body, own)) = comps.pop() {
                        values.push((arena.value_type_thunk(body), own));
                    }
                },
                | Step::Arrow => {
                    if let (Some(&(domain, ref from)), Some(&(codomain, ref to))) =
                        (values.last(), comps.last())
                    {
                        let joined = from.max(to);
                        let arrow = arena.comp_type_arrow(domain, codomain);
                        values.pop();
                        comps.pop();
                        comps.push((arrow, joined));
                    }
                },
                | Step::Lift => {
                    if let Some((inner, own)) = values.pop() {
                        let above = own.succ().expect("a generated level has a successor");
                        values.push((arena.value_type_lift(inner, above.clone()), above));
                    }
                },
            }
        }
        let (mut root, mut at) = values
            .pop()
            .unwrap_or_else(|| (arena.value_type_unit(), Level::zero()));
        while let Some((body, own)) = comps.pop() {
            let arrow = arena.comp_type_arrow(root, body);
            at = at.max(&own);
            root = arena.value_type_thunk(arrow);
        }
        Generated { root, level: at }
    }

    /// Open one binder per level of `levels`, outermost first, each a value
    /// universe at its level.
    ///
    /// # Specification
    /// trivial.
    fn open_universes(
        context: &mut CheckingContext<'_>,
        levels: &[LevelConstant],
    )
    {
        for &at in levels.iter().rev() {
            let universe = context
                .arena_mut()
                .value_type_universe(Sort::Ground(GroundSort::Value), level(at));
            context.binders().open(Zone::Intuitionistic, universe);
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(256))]

        #[test]
        fn every_type_has_exactly_one_classifier(
            levels in vec(small_level(), 1 .. 4),
            steps in vec(step(), 1 .. 24),
        )
        {
            let mut arena = CoreArena::new();
            let generated = build(&mut arena, &levels, &steps);
            let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
            open_universes(&mut context, &levels);
            let expected = Classifier { sort: GroundSort::Value, level: generated.level };
            let first = classified(&mut context, generated.root);
            let second = classified(&mut context, generated.root);
            prop_assert_eq!(&first, &Ok(expected), "formation answers the classifier the construction gives");
            prop_assert_eq!(first, second, "and answers it again");
        }

        #[test]
        fn weakening_preserves_formation(
            levels in vec(small_level(), 1 .. 4),
            fresh in vec(small_level(), 0 .. 3),
            steps in vec(step(), 1 .. 24),
        )
        {
            let mut arena = CoreArena::new();
            let generated = build(&mut arena, &levels, &steps);
            let amount = Binders::from(u32::try_from(fresh.len()).expect("small"));
            let weakened = shift_value_type(&mut arena, generated.root, amount);
            let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
            open_universes(&mut context, &levels);
            let before = classified(&mut context, generated.root);
            open_universes(&mut context, &fresh);
            let after = classified(&mut context, weakened);
            prop_assert_eq!(before, after, "a type shifted past fresh binders forms at its classifier still");
        }
    }
}
