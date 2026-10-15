//! The recursion core: a structural fixpoint typed by stages.
//!
//! The rules, their place in the sized fragment and the alternatives weighed
//! are the crate documentation's § Recursion; this module states each rule
//! where it is applied.
//!
//! - **A fixpoint opens a stage.** [`open_fixpoint`] mints a root `ι` for the
//!   parameter the fixpoint recurses on: the body checks with that parameter at
//!   `A^ι`, and the self binder is the same telescope with it at `A^{<ι}`.
//! - **A case opens one stage below its scrutinee's.** [`open_case`] mints one
//!   child `s' < s` for a scrutinee at `A^s`, shared by the case's arms, after
//!   naming a scrutinee at a bound `A^{<^k ι}` by a chain of `k` fresh stages;
//!   [`stage_branch`] binds each recursive field at `s'`.
//! - **A constructor stands above its fields.** [`constructor_owes`] reads what
//!   a constructor checked at a stage owes: its recursive fields one step
//!   lower, and, for a constructor with none, a value in scope showing the
//!   stage is not the empty first one ([`room`]).
//! - **Subsumption is the order**, decided where a found value type meets a
//!   wanted one; the conversion reads a stage through
//!   [`gandr_kernel_core::stage_order::StageOrder::fit`].

use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::Binders;
use gandr_core_term::CompType;
use gandr_core_term::CompTypeId;
use gandr_core_term::ComputationId;
use gandr_core_term::Value;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_kernel_core::stage_order::Fit;
use gandr_kernel_core::stage_order::below;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::Stage;
use gandr_kernel_term::StageId;
use gandr_kernel_term::StagedPosition;
use quenchant_shape::shape::Maybe;

use crate::CheckRefusal;
use crate::CheckingContext;
use crate::conversion::Agreement;
use crate::refusal::ExpectedShape;
use crate::refusal::TermNode;
use crate::refusal::TypeNode;
use crate::view::CompTypeView;
use crate::view::ValueTypeView;
use crate::view::comp_type_view;
use crate::view::value_type_view;

/// Why a type opens no stage.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Unstaged
{
    /// The type is refined at no stage.
    Plain,
    /// The fixpoint's type is the unknown type: there is no telescope to
    /// refine, and the unknown type checks whatever the body is.
    Unknown,
}

/// The two types a fixpoint opening its stage checks at.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Opened
{
    /// The self binder's computation type: the recursed-on parameter at the
    /// bound `<ι`.
    pub own: CompTypeId,
    /// The body's computation type: the recursed-on parameter at `ι`.
    pub inside: CompTypeId,
}

/// Whether a value in scope shows a stage is not the empty first one.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Room
{
    /// A hypothesis stands at a stage of a data type at or below the wanted
    /// stage: that stage holds a value, so it is above the first, and every
    /// constructor without a recursive field stands within it.
    Witnessed,
    /// No hypothesis does.
    Unwitnessed,
}

/// What a constructor checked at a stage owes.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Owed
{
    /// The type the stage refines.
    pub base: ValueTypeId,
    /// The stage the constructor is checked at.
    pub wanted: Stage,
    /// The bound its recursive fields check at: one step below `wanted`.
    pub fields: Stage,
}

/// Open the stage of the fixpoint `at` checked at `expected`, recursing on
/// the parameter at `position`.
///
/// # Specification
/// - requires: `expected` is formed.
/// - ensures: over a telescope with an arrow at `position`, a root stage `ι`
///   minted, the body's type the telescope with that arrow's domain at `A^ι`,
///   and the self binder's the same telescope with it at `A^{<ι}`; every other
///   arrow, and the codomain past `position`, as `expected` holds them. The
///   unknown type, anywhere down the telescope, opens nothing.
/// - fails: [`CheckRefusal::ShapeMismatch`] wanting an arrow when the telescope
///   ends, in a returner, a lazy product or a rigid decode, before `position`;
///   a fixpoint at such a type is never checked unstaged, since a fixpoint
///   whose self-reference is not below its own stage need not terminate.
/// - panics: none.
///
/// # Errors
/// As `- fails:`, and the unfolding's refusal.
///
/// # Adequacy
/// - hypothesis: L3 — a first-parameter recursion opens the first arrow, a
///   recursion two parameters deep opens the second, and a fixpoint at a
///   returner is refused.
/// - witness: `recursion::tests::a_recursion_descends_on_its_first_parameter`
/// - witness: `recursion::tests::a_structural_fixpoint_needs_an_arrow_to_recurse_on`
#[spec(ensures: |ret| match ret {
    Ok(Maybe::Present(opened)) => context.arena().comp_type(opened.own).is_some() && context.arena().comp_type(opened.inside).is_some(),
    Ok(Maybe::Absent(reason)) => reason == Unstaged::Unknown,
    Err(_) => true,
})]
pub fn open_fixpoint(
    context: &mut CheckingContext<'_>,
    at: ComputationId,
    expected: CompTypeId,
    position: StagedPosition,
) -> Result<Maybe<Opened, Unstaged>, CheckRefusal>
{
    let refused = CheckRefusal::ShapeMismatch {
        at: TermNode::Computation(at),
        wanted: ExpectedShape::Arrow,
        found: TypeNode::Computation(expected),
    };
    // The telescope down to the recursed-on arrow, outermost first: each
    // domain, and whether its codomain is under its binder.
    let mut spine: Vec<(ValueTypeId, Dependence)> = Vec::new();
    let mut cursor = expected;
    let (domain, codomain, dependence) = loop {
        let head = context.whnf_comp_type(cursor)?;
        let (domain, codomain, dependence) = match comp_type_view(context.arena(), head)? {
            CompTypeView::Arrow { domain, codomain } => (domain, codomain, Dependence::Ambient),
            CompTypeView::Pi { domain, codomain } => (domain, codomain, Dependence::Dependent),
            CompTypeView::Unknown => return Ok(Maybe::Absent(Unstaged::Unknown)),
            CompTypeView::Returner { .. }
            | CompTypeView::With(..)
            | CompTypeView::Element { .. } => {
                return Err(refused);
            },
        };
        if spine.len() == usize::from(position) {
            break (domain, codomain, dependence);
        }
        spine.push((domain, dependence));
        cursor = codomain;
    };
    let root = context.stages_mut().mint_root();
    let arena = context.arena_mut();
    let inside_domain = arena.value_type_staged(domain, Stage::At(root));
    let own_domain = arena.value_type_staged(domain, below(Stage::At(root)));
    let mut own = dependence.former(arena, own_domain, codomain);
    let mut inside = dependence.former(arena, inside_domain, codomain);
    while let Some((outer, dependence)) = spine.pop() {
        own = dependence.former(arena, outer, own);
        inside = dependence.former(arena, outer, inside);
    }
    Ok(Maybe::Present(Opened { own, inside }))
}

/// Whether an arrow's codomain stands under its binder.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Dependence
{
    /// A non-dependent arrow: the codomain stands in the ambient context.
    Ambient,
    /// A dependent arrow: the codomain stands under the domain's binder.
    Dependent,
}

impl Dependence
{
    /// The arrow of this dependence from `domain` to `codomain`.
    ///
    /// # Specification
    /// trivial.
    fn former(
        self,
        arena: &mut gandr_core_term::CoreArena,
        domain: ValueTypeId,
        codomain: CompTypeId,
    ) -> CompTypeId
    {
        match self {
            Self::Ambient => arena.comp_type_arrow(domain, codomain),
            Self::Dependent => arena.comp_type_pi(domain, codomain),
        }
    }
}

/// Open a case on a scrutinee of type `scrutinee`: the type the case reads
/// it as, and the stage its arms bind recursive fields at.
///
/// # Specification
/// - requires: `scrutinee` is the type the case's scrutinee synthesised.
/// - ensures: for `A^s` at an exact `s`, `A` and a fresh child of `s`; for a
///   bound `A^{<^k ι}`, `A` and a fresh child of the last of `k` fresh stages
///   chained below `ι`, which name the scrutinee's stage; any other type as it
///   stands, with [`Unstaged::Plain`].
/// - fails: [`CheckRefusal::MachineInvariant`] for a stage this judgement did
///   not mint.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — a case on the recursed-on parameter and a case on one of
///   its fields each mint one child, so a call on a field two cases deep is two
///   steps below the fixpoint's stage.
/// - witness: `recursion::tests::a_call_on_a_value_rebuilt_below_the_stage_is_admitted`
#[spec(ensures: |ret| match ret {
    Ok((read, Maybe::Present(_))) => matches!(context.arena().value_type(scrutinee), Some(&ValueType::Staged { base, .. }) if base == read),
    Ok((read, Maybe::Absent(_))) => read == scrutinee,
    Err(_) => true,
})]
pub fn open_case(
    context: &mut CheckingContext<'_>,
    scrutinee: ValueTypeId,
) -> Result<(ValueTypeId, Maybe<StageId, Unstaged>), CheckRefusal>
{
    let Some(&ValueType::Staged { base, stage }) = context.arena().value_type(scrutinee)
    else {
        return Ok((scrutinee, Maybe::Absent(Unstaged::Plain)));
    };
    let unminted = |_unminted| CheckRefusal::MachineInvariant;
    let exact = match stage {
        Stage::At(exact) => exact,
        Stage::Below { anchor, depth } => {
            let mut parent = anchor;
            for _step in 0 .. u32::from(depth) {
                parent = context.stages_mut().mint_below(parent).map_err(unminted)?;
            }
            parent
        },
    };
    let child = context.stages_mut().mint_below(exact).map_err(unminted)?;
    Ok((base, Maybe::Present(child)))
}

/// Whether two formed value types convert, invariantly.
///
/// # Specification
/// trivial.
fn same(
    context: &mut CheckingContext<'_>,
    left: ValueTypeId,
    right: ValueTypeId,
) -> Result<Agreement, CheckRefusal>
{
    crate::conversion::equivalent(context, left, right)
}

/// A field type with its recursive occurrence refined at `stage`.
///
/// # Specification
/// - requires: `recursive` is the family's application at the field's depth.
/// - ensures: the family itself at `stage`; a thunk of an arrow whose codomain
///   returns the family with that result at `stage`; a data type with each
///   argument quoting the family quoting it at `stage`; the field itself when
///   it holds none of the three.
/// - fails: the conversion's refusal.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — a direct field, a function field and a field of a family
///   quoting the type each move to the stage, and a field holding none stays.
/// - witness: `recursion::tests::a_call_on_a_value_rebuilt_below_the_stage_is_admitted`
/// - witness: `recursion::tests::a_rose_tree_recurses_through_map_at_its_children_s_stage`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |&staged| staged == field
    || matches!(context.arena().value_type(staged), Some(ValueType::Staged { .. } | ValueType::Thunk(_) | ValueType::Data { .. }))))]
pub fn stage_field(
    context: &mut CheckingContext<'_>,
    field: ValueTypeId,
    recursive: ValueTypeId,
    stage: Stage,
) -> Result<ValueTypeId, CheckRefusal>
{
    if same(context, field, recursive)? == Agreement::Convertible {
        return Ok(context.arena_mut().value_type_staged(field, stage));
    }
    let head = context.whnf_value_type(field)?;
    match context.arena().value_type(head).cloned() {
        Some(ValueType::Thunk(body)) => {
            let (domain, codomain, dependence) = match context.arena().comp_type(body) {
                Some(&CompType::Arrow { domain, codomain }) => {
                    (domain, codomain, Dependence::Ambient)
                },
                Some(&CompType::Pi { domain, codomain }) => {
                    (domain, codomain, Dependence::Dependent)
                },
                Some(
                    &(CompType::Returner { .. }
                    | CompType::With(..)
                    | CompType::Element { .. }
                    | CompType::Unknown),
                )
                | None => return Ok(field),
            };
            let Some(CompType::Returner { result, effects }) =
                context.arena().comp_type(codomain).cloned()
            else {
                return Ok(field);
            };
            let under = match dependence {
                Dependence::Ambient => recursive,
                Dependence::Dependent => {
                    gandr_core_term::shift_value_type(context.arena_mut(), recursive, Binders::ONE)
                },
            };
            if same(context, result, under)? != Agreement::Convertible {
                return Ok(field);
            }
            let arena = context.arena_mut();
            let staged = arena.value_type_staged(result, stage);
            let returner = arena.comp_type_returner_with_effects(staged, effects);
            let function = dependence.former(arena, domain, returner);
            Ok(arena.value_type_thunk(function))
        },
        Some(ValueType::Data {
            declaration,
            arguments,
        }) => {
            let mut staged = arguments;
            let mut changed = Changed::Kept;
            for argument in &mut staged {
                if let Some(&Value::Quote(quoted)) = context.arena().value(*argument)
                    && same(context, quoted, recursive)? == Agreement::Convertible
                {
                    let arena = context.arena_mut();
                    let refined = arena.value_type_staged(quoted, stage);
                    *argument = arena.value_quote(refined);
                    changed = Changed::Refined;
                }
            }
            match changed {
                Changed::Kept => Ok(field),
                Changed::Refined => Ok(context.arena_mut().value_type_data(declaration, staged)),
            }
        },
        Some(_) | None => Ok(field),
    }
}

/// Whether a walk refined anything.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Changed
{
    /// Nothing.
    Kept,
    /// At least one argument.
    Refined,
}

/// A case branch's type with its recursive fields at the stage the case
/// opened.
///
/// # Specification
/// - requires: `branch` is the telescope over one binder per entry of `fields`
///   that [`crate::former::branch_type`] built over `datatype`: a Π where the
///   rest names the field, a plain arrow otherwise.
/// - ensures: the same telescope, each field under the same former, with each
///   recursive field domain at `child`.
/// - fails: [`CheckRefusal::MachineInvariant`] for a telescope shorter than
///   `fields`; the conversion's refusal.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — the successor's field moves to the case's stage and a
///   call on it is admitted, while the zero branch binds nothing; a rose tree's
///   node, whose result names none of its fields, stages its children under the
///   plain arrows `branch_type` builds there.
/// - witness: `recursion::tests::a_recursion_descends_on_its_first_parameter`
/// - witness: `recursion::tests::a_rose_tree_recurses_through_map_at_its_children_s_stage`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |&staged| context.arena().comp_type(staged).is_some()))]
pub fn stage_branch(
    context: &mut CheckingContext<'_>,
    datatype: ValueTypeId,
    branch: CompTypeId,
    (fields, child): (&[ValueTypeId], StageId),
) -> Result<CompTypeId, CheckRefusal>
{
    let mut domains = Vec::with_capacity(fields.len());
    let mut focus = branch;
    for _field in fields {
        let (domain, codomain, dependence) = match context.arena().comp_type(focus) {
            Some(&CompType::Arrow { domain, codomain }) => (domain, codomain, Dependence::Ambient),
            Some(&CompType::Pi { domain, codomain }) => (domain, codomain, Dependence::Dependent),
            Some(
                &(CompType::Returner { .. }
                | CompType::With(..)
                | CompType::Element { .. }
                | CompType::Unknown),
            )
            | None => return Err(CheckRefusal::MachineInvariant),
        };
        domains.push((domain, dependence));
        focus = codomain;
    }
    // A field stands under the Π binders before it, and only those: a plain
    // arrow's rest was strengthened past its field.
    let mut depth = 0_u32;
    for &mut (ref mut domain, dependence) in &mut domains {
        let recursive =
            gandr_core_term::shift_value_type(context.arena_mut(), datatype, Binders::from(depth));
        *domain = stage_field(context, *domain, recursive, Stage::At(child))?;
        if dependence == Dependence::Dependent {
            depth = depth.checked_add(1).ok_or(CheckRefusal::MachineInvariant)?;
        }
    }
    for &(domain, dependence) in domains.iter().rev() {
        focus = dependence.former(context.arena_mut(), domain, focus);
    }
    Ok(focus)
}

/// What a constructor checked at `expected` owes, when `expected` is staged.
///
/// # Specification
/// - ensures: for `A^s`, the base `A`, the stage `s`, and its recursive fields
///   one step below `s`; [`Unstaged::Plain`] for any other type.
/// - fails: the unfolding's refusal.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — a constructor rebuilt two cases deep checks at the bound,
///   and the same constructor rebuilt one case deep is refused.
/// - witness: `recursion::tests::a_call_on_a_value_rebuilt_below_the_stage_is_admitted`
#[spec(ensures: |ret| match ret {
    Ok(Maybe::Present(owed)) => owed.fields == below(owed.wanted),
    Ok(Maybe::Absent(reason)) => reason == Unstaged::Plain,
    Err(_) => true,
})]
pub fn constructor_owes(
    context: &mut CheckingContext<'_>,
    expected: ValueTypeId,
) -> Result<Maybe<Owed, Unstaged>, CheckRefusal>
{
    let head = context.whnf_value_type(expected)?;
    match value_type_view(context.arena(), head)? {
        ValueTypeView::Staged { base, stage } => Ok(Maybe::Present(Owed {
            base,
            wanted: stage,
            fields: below(stage),
        })),
        ValueTypeView::Data { .. }
        | ValueTypeView::Record(_)
        | ValueTypeView::Stack { .. }
        | ValueTypeView::PathUniverse(..)
        | ValueTypeView::Path { .. }
        | ValueTypeView::Flow { .. }
        | ValueTypeView::Run(_)
        | ValueTypeView::Sum(_)
        | ValueTypeView::List(_)
        | ValueTypeView::Integer
        | ValueTypeView::String
        | ValueTypeView::Unit
        | ValueTypeView::Thunk(_)
        | ValueTypeView::Universe { .. }
        | ValueTypeView::Lift { .. }
        | ValueTypeView::Element { .. }
        | ValueTypeView::Product(_)
        | ValueTypeView::StaticPi { .. }
        | ValueTypeView::Sigma { .. }
        | ValueTypeView::Abstract(_)
        | ValueTypeView::Capability { .. }
        | ValueTypeView::Session(_)
        | ValueTypeView::Unknown => Ok(Maybe::Absent(Unstaged::Plain)),
    }
}

/// Whether a hypothesis in scope shows `wanted` is above the first stage.
///
/// A data type's first stage is empty — every constructor stands one step
/// above its recursive fields — so a hypothesis at a stage of a data type is
/// a value there, and its stage is above the first. A constructor with no
/// recursive field stands at every stage above the first; so it stands within
/// `wanted` exactly when some such stage lies within it. A stage that only a
/// case minted shows nothing: an arm binding no recursive field holds no value
/// at the case's stage, and that stage may be the first.
///
/// # Specification
/// - ensures: [`Room::Witnessed`] exactly when some intuitionistic hypothesis
///   is `A^s` with `A` a data type and `s` within `wanted`.
/// - fails: [`CheckRefusal::MachineInvariant`] for a binder the context does
///   not hold.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — a nullary argument under a successor arm's field is
///   witnessed, and the same argument under the zero arm, where the case has
///   minted its stage but bound nothing at it, is not.
/// - witness: `recursion::tests::a_nullary_argument_needs_a_value_below_the_stage`
#[spec(ensures: |ret| !matches!(ret, Ok(Room::Witnessed)) || usize::from(context.depth(Zone::Intuitionistic)) > 0)]
pub fn room(
    context: &CheckingContext<'_>,
    wanted: Stage,
) -> Result<Room, CheckRefusal>
{
    let depth = usize::from(context.depth(Zone::Intuitionistic));
    for index in 0 .. depth {
        let index = u32::try_from(index).map_err(|_overflow| CheckRefusal::MachineInvariant)?;
        let declared = context.hypothesis(DeBruijnIndex::from(index))?;
        let arena = context.arena();
        if let Some(&ValueType::Staged { base, stage }) = arena.value_type(declared)
            && matches!(arena.value_type(base), Some(ValueType::Data { .. }))
            && context.stages().fit(stage, wanted) == Fit::Within
        {
            return Ok(Room::Witnessed);
        }
    }
    Ok(Room::Unwitnessed)
}

#[cfg(test)]
mod tests;
