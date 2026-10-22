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
//!
//! The alternatives were a formation walker beside the judgement, over a
//! formation context kept in step with the judgement's by hand, which is two
//! contexts where one suffices, and a classifier cached on each arena node at
//! mint time, which puts a judgement's answer into the vocabulary crate and
//! charges every mint for a reading only formed types need. The choice reverses
//! if formation ever needs a context the judgement does not have.
//!
//! # Universes, quotes and decodes
//!
//! `Type[+, l]` classifies value types and `Type[-, l]` computation types, and
//! each is itself a value type at `Type[+, l+1]`: universes are values, both
//! towers sit in the value sort, and a universe of computation types is
//! something a value can be. A quote `⌜A⌝` is the code of a value type and
//! synthesises the value universe at `A`'s level; a computation quote does the
//! same for a computation type in the computation universe. A decode `El(c, l)`
//! turns a code back into a type, and a decode of a quote is never stored:
//! minting it returns the quoted type, so a decode in the arena always stands
//! over a variable or a constant, and type comparison stays structural
//! everywhere but there. A variable whose binder has a universe type is a type
//! variable; a variable bound at any other type is not, and its decode is
//! refused at the decode bridge. Witnesses:
//! `context::tests::a_universe_typed_hypothesis_becomes_a_type_variable` and
//! `context::tests::a_value_typed_hypothesis_does_not_become_a_type_variable`.
//!
//! Two universe forms are refused by name. A universe over a sort parameter has
//! no ground reading until sort binders exist to bind it, and a universe at the
//! greatest representable level has no level for its own universe to stand at.
//! The alternatives were a single universe with the sort read off context,
//! which loses the classifier's one-answer property, and a separate kind layer
//! above the universes, which ∂CBPV shows is unnecessary. The sort parameter
//! reverses with prenex sort quantification.
//!
//! # Arrows, products, dependent pairs and static Pis
//!
//! A dependent arrow `Π(x : A). C` forms when its domain forms and its codomain
//! forms under a binder of `A`; it is a computation type at the join of the two
//! levels. An eager product `A × B` forms when both factors form, a value type
//! at the join of their levels; its factors are value types, so a computation
//! type stands in one only under a thunk. A dependent pair `Σ (x : A). B`
//! forms as the dependent arrow does, its second factor under a binder of `A`,
//! a value type at the join of the two levels; the product over the same
//! factors leaves that binder unbound. Witness:
//! `formation::tests::the_dependent_pair_forms_at_the_join_of_its_levels`.
//! A static Pi `K ⇒ J` forms when both
//! classifiers form and each, at its weak head, is a universe or a static Pi: a
//! static operator ranges over codes and over operators on codes, and a static
//! Pi over any other classifier is `StaticClassifierExpected`, naming the
//! classifier. The static Pi is non-dependent, its codomain closed: every
//! operator the relative monad needs is non-dependent, and a dependent static
//! Pi waits for a family that needs it.
//!
//! Effect operation types take part in formation's levels and scope:
//! `formation::tests::effect_operation_types_participate_in_formation_levels_and_scope`.

use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::Classifier;
use gandr_core_term::CompTypeId;
use gandr_core_term::CoreArena;
use gandr_core_term::ValueTypeId;
use gandr_core_term::world::WorldType;
use gandr_kernel_strata::Level;
use gandr_kernel_term::GroundSort;
use quenchant_shape::shape::Maybe;

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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — literal, variable and application judgements expose
    ///   the derived value types by subsequent checking. Wrong selected
    ///   subtypes are separated for those forms, not arbitrary derivations.
    /// - witness: `judgement::tests::every_value_former_is_answered_in_both_modes`
    /// - witness: `judgement::tests::a_dependent_application_instantiates_its_codomain_at_the_argument`
    #[spec(ensures: |ret| ret.id() == id)]
    pub(crate) fn derived(id: ValueTypeId) -> Self
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — return, force, application and bind expose their
    ///   derived computation types through synthesis and checking. The named
    ///   forms separate a wrong selected result type, not every derivation.
    /// - witness: `judgement::tests::every_comp_former_is_answered_in_both_modes`
    /// - witness: `judgement::tests::a_bind_synthesises_its_continuations_type`
    #[spec(ensures: |ret| ret.id() == id)]
    pub(crate) fn derived(id: CompTypeId) -> Self
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
///   [`CheckRefusal::OpenSessionPayload`] for a session type whose payload
///   reads a binder outside it, anywhere but a run's protocol;
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
/// - witness: `judgement::tests::a_session_payload_reads_a_binder_only_in_a_run_protocol_1728`
#[spec(
    captures: depth = context.depth(gandr_core_term::Zone::Intuitionistic),
    ensures: |ret| context.depth(gandr_core_term::Zone::Intuitionistic) == depth
        && ret.is_ok_and(|formed| formed.id() == value_type) == ret.is_ok(),
)]
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
#[spec(
    captures: depth = context.depth(gandr_core_term::Zone::Intuitionistic),
    ensures: |ret| context.depth(gandr_core_term::Zone::Intuitionistic) == depth
        && ret.is_ok_and(|formed| formed.id() == comp_type) == ret.is_ok(),
)]
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
#[spec(ensures: |ret| ret.as_ref().is_ok_and(|classifier| classifier.sort == GroundSort::Value) == ret.is_ok())]
#[inline]
pub fn classify_value_type(
    context: &CheckingContext<'_>,
    formed: FormedValueType,
) -> Result<Classifier, CheckRefusal>
{
    Ok(Classifier {
        sort: GroundSort::Value,
        level: level_of(context, TypeNode::Value(formed.id()))?,
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
#[spec(ensures: |ret| ret.as_ref().is_ok_and(|classifier| classifier.sort == GroundSort::Computation) == ret.is_ok())]
#[inline]
pub fn classify_comp_type(
    context: &CheckingContext<'_>,
    formed: FormedCompType,
) -> Result<Classifier, CheckRefusal>
{
    Ok(Classifier {
        sort: GroundSort::Computation,
        level: level_of(context, TypeNode::Computation(formed.id()))?,
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
/// - ensures: zero for an atom, the unit type and the unknown type, whichever
///   spelling it has; the successor of its level for a universe; its own level
///   for a lift and a decode; its kind's level for a sealed atom; its child's
///   level for a thunk type and a returner, its carrier's for a path type and
///   its base's for a staged type; the join of its children's for an eager
///   product, a static Pi, a dependent pair, an arrow and a dependent arrow,
///   whose second factor's or codomain's level does not depend on the binder,
///   and of its payloads' for a session type, and of its operations' payloads
///   and replies for a capability.
/// - provides: the level part of every classifier, and the level a code is
///   decoded at when the judgement unfolds a code constant.
/// - fails: the view's refusal for a node outside the fragment or a dangling
///   id; [`CheckRefusal::OutOfFragment`] naming
///   [`UnadmittedFormer::TopUniverse`] for a universe at the greatest level;
///   [`CheckRefusal::NotAnAbstractType`] for a sealed atom no admitted abstract
///   type declares.
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
/// - witness: `formation::tests::each_carrying_former_stands_at_the_level_of_what_it_carries`
#[spec(ensures: |ret| match root {
    | TypeNode::Value(at) => match value_type_view(context.arena(), at) {
        | Ok(ValueTypeView::Integer | ValueTypeView::String | ValueTypeView::Unit | ValueTypeView::Unknown) => ret == Ok(Level::zero()),
        | Ok(ValueTypeView::Lift { target, .. } | ValueTypeView::Element { target, .. }) => ret.as_ref() == Ok(target),
        | Err(refusal) => ret == Err(CheckRefusal::from(refusal)),
        | Ok(_) => true,
    },
    | TypeNode::Computation(at) => match comp_type_view(context.arena(), at) {
        | Ok(CompTypeView::Element { target, .. }) => ret.as_ref() == Ok(target),
        | Ok(CompTypeView::Unknown) => ret == Ok(Level::zero()),
        | Err(refusal) => ret == Err(CheckRefusal::from(refusal)),
        | Ok(_) => true,
    },
})]
#[inline]
pub fn level_of(
    context: &CheckingContext<'_>,
    root: TypeNode,
) -> Result<Level, CheckRefusal>
{
    let arena = context.arena();
    let mut tasks = Vec::from([Task::Enter(root)]);
    let mut levels: Vec<Level> = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Join => {
                let (Some(right), Some(left)) = (levels.pop(), levels.pop())
                else {
                    return Err(CheckRefusal::MachineInvariant);
                };
                levels.push(left.max(&right));
            },
            Task::Enter(TypeNode::Value(at)) => match value_type_view(arena, at)? {
                ValueTypeView::Data { declaration, .. } => {
                    let Maybe::Present(signature) = context.data_in_scope(declaration)
                    else {
                        return Err(CheckRefusal::NotADataType(declaration));
                    };
                    levels.push(crate::former::kind_level(context, signature.kind())?);
                },
                ValueTypeView::Record(fields) => {
                    levels.push(Level::zero());
                    for &field in fields.values().rev() {
                        tasks.push(Task::Join);
                        tasks.push(Task::Enter(TypeNode::Value(field)));
                    }
                },
                ValueTypeView::Stack { input, output } => {
                    tasks.extend([
                        Task::Join,
                        Task::Enter(TypeNode::Computation(output)),
                        Task::Enter(TypeNode::Computation(input)),
                    ]);
                },
                ValueTypeView::PathUniverse(source, target) => {
                    let _source = path_code(arena, source)?;
                    let _target = path_code(arena, target)?;
                    levels.push(Level::zero());
                },
                ValueTypeView::Integer
                | ValueTypeView::String
                | ValueTypeView::Unit
                | ValueTypeView::Run(_)
                | ValueTypeView::Buffer
                | ValueTypeView::Unknown => {
                    levels.push(Level::zero());
                },
                ValueTypeView::Abstract(atom) => levels.push(context.abstract_level(atom)?),
                ValueTypeView::List(element)
                | ValueTypeView::Staged { base: element, .. }
                | ValueTypeView::Kept { value: element, .. }
                | ValueTypeView::Path {
                    carrier: element, ..
                }
                | ValueTypeView::Flow {
                    carrier: element, ..
                } => tasks.push(Task::Enter(TypeNode::Value(element))),
                ValueTypeView::Thunk(body) => {
                    tasks.push(Task::Enter(TypeNode::Computation(body)));
                },
                ValueTypeView::Universe { level, .. } => {
                    let Ok(above) = level.succ()
                    else {
                        return Err(CheckRefusal::OutOfFragment {
                            at: CoreNode::Type(TypeNode::Value(at)),
                            former: UnadmittedFormer::TopUniverse,
                        });
                    };
                    levels.push(above);
                },
                ValueTypeView::Lift { target, .. } | ValueTypeView::Element { target, .. } => {
                    levels.push(target.clone());
                },
                ValueTypeView::Sum(components) | ValueTypeView::Product(components) => {
                    levels.push(Level::zero());
                    for &component in components.iter().rev() {
                        tasks.push(Task::Join);
                        tasks.push(Task::Enter(TypeNode::Value(component)));
                    }
                },
                ValueTypeView::Session(session) => {
                    levels.push(Level::zero());
                    for &payload in session.payloads().iter().rev() {
                        tasks.push(Task::Join);
                        tasks.push(Task::Enter(TypeNode::Value(payload)));
                    }
                },
                ValueTypeView::Capability { authority, .. } => {
                    levels.push(Level::zero());
                    for operation_type in authority.types() {
                        tasks.push(Task::Join);
                        tasks.push(Task::Enter(TypeNode::Value(operation_type)));
                    }
                },
                ValueTypeView::World(WorldType::At { inner, .. }) => {
                    tasks.push(Task::Enter(TypeNode::Value(inner)));
                },
                ValueTypeView::World(WorldType::Capability(_)) => levels.push(Level::zero()),
                ValueTypeView::StaticPi {
                    domain: first,
                    codomain: second,
                }
                | ValueTypeView::Sigma { first, second } => {
                    tasks.push(Task::Join);
                    tasks.push(Task::Enter(TypeNode::Value(second)));
                    tasks.push(Task::Enter(TypeNode::Value(first)));
                },
            },
            Task::Enter(TypeNode::Computation(at)) => match comp_type_view(arena, at)? {
                CompTypeView::With(components) => {
                    levels.push(Level::zero());
                    for &component in components.iter().rev() {
                        tasks.push(Task::Join);
                        tasks.push(Task::Enter(TypeNode::Computation(component)));
                    }
                },
                CompTypeView::Returner { result, effects } => {
                    for operation_type in effects.types() {
                        tasks.push(Task::Join);
                        tasks.push(Task::Enter(TypeNode::Value(operation_type)));
                    }
                    tasks.push(Task::Enter(TypeNode::Value(result)));
                },
                CompTypeView::Arrow { domain, codomain }
                | CompTypeView::Pi { domain, codomain } => {
                    tasks.push(Task::Join);
                    tasks.push(Task::Enter(TypeNode::Computation(codomain)));
                    tasks.push(Task::Enter(TypeNode::Value(domain)));
                },
                CompTypeView::Element { target, .. } => levels.push(target.clone()),
                CompTypeView::Codata { declaration, .. } => {
                    let Maybe::Present(signature) = context.codata_in_scope(declaration)
                    else {
                        return Err(CheckRefusal::Codata {
                            at: crate::CoreNode::Type(TypeNode::Computation(at)),
                            fault: crate::codata::CodataFault::Undeclared,
                        });
                    };
                    levels.push(crate::codata::kind_level(context, signature.kind())?);
                },
                CompTypeView::Unknown => levels.push(Level::zero()),
            },
        }
    }
    match (levels.pop(), levels.is_empty()) {
        (Some(level), true) => Ok(level),
        (Some(_) | None, _) => Err(CheckRefusal::MachineInvariant),
    }
}

/// Decode exactly the closed first-order fragment used by native paths.
///
/// # Specification
/// - requires: nothing; a non-quote is refused.
/// - ensures: every reachable type is Base, a product of any arity, the unit
///   among them, or a sum of at least one summand: the kernel's universe-path
///   vocabulary less its session codes.
/// - provides: the decoded endpoint of an admitted native path.
/// - fails: `PathCode` for any other endpoint, reachable former or arity.
/// - panics: none.
///
/// # Errors
/// `CheckRefusal::PathCode`.
///
/// # Adequacy
/// - hypothesis: L3 — a native Bool equivalence crosses; open codes refuse; the
///   telescope of a binary corolla beside a constant, a sum of one summand
///   inside products, crosses.
/// - witness: `bridge::tests::native_path_module_round_trips`
/// - witness: `ua::tests::the_swap_of_a_binary_generator_is_a_path_of_the_certificate_universe`
/// - witness: `formation::tests::a_path_code_is_closed_first_order_and_inhabited`
#[spec(ensures: |ret| match ret { Ok(root) => matches!(arena.value(code), Some(&gandr_core_term::Value::Quote(quoted)) if root == quoted) && matches!(arena.value_type(root), Some(&(gandr_core_term::ValueType::Base(_) | gandr_core_term::ValueType::Product(_) | gandr_core_term::ValueType::Sum(_)))), Err(CheckRefusal::PathCode(found)) => found == code, Err(_) => false })]
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
            Some(&gandr_core_term::ValueType::Base(_)) => {},
            Some(&gandr_core_term::ValueType::Product(ref parts)) => {
                pending.extend(parts.iter().copied());
            },
            Some(&gandr_core_term::ValueType::Sum(ref parts)) if !parts.is_empty() => {
                pending.extend(parts.iter().copied());
            },
            _ => return Err(CheckRefusal::PathCode(code)),
        }
    }
    Ok(root)
}

#[cfg(test)]
mod tests;
