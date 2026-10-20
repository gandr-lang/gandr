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
//!   naming a scrutinee at a bound `A^{<^k ι}` by a chain of `k` fresh stages,
//!   and a root for a stratified scrutinee at no stage; [`stage_branch`] binds
//!   each field at `s'` through [`stage_field`], which moves every occurrence
//!   of the block's families the occurrence walk placed — under a function's
//!   domain too — to `s'`.
//! - **A constructor stands above its fields.** [`constructor_owes`] reads what
//!   a constructor checked at a stage owes: its recursive fields one step
//!   lower, and, for a constructor with no field whose own type is the family,
//!   a value in scope showing the stage is not the empty first one ([`room`]).
//!   A thunked recursive field shows nothing: it may hold a computation that
//!   never returns (#598).
//! - **Subsumption is the order**, decided where a found value type meets a
//!   wanted one; the conversion reads a stage through
//!   [`gandr_kernel_core::stage_order::StageOrder::fit`].
//! - **A type parameter instantiates at a staged code.** [`instantiation`]
//!   reads the code a call hands a type parameter at the stage of the first
//!   later variable argument whose parameter's type holds it, so the call's
//!   codomain carries the stage while the term keeps the code it was written
//!   with.

use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::Binders;
use gandr_core_term::CompType;
use gandr_core_term::CompTypeId;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::shift_value_type;
use gandr_kernel_core::stage_order::Fit;
use gandr_kernel_core::stage_order::below;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::Stage;
use gandr_kernel_term::StageId;
use gandr_kernel_term::StagedPosition;
use quenchant_shape::shape::Maybe;

use crate::CheckRefusal;
use crate::CheckingContext;
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

/// How a definition's own fixpoint reads its result.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum ResultStage
{
    /// As its type declares it.
    Declared,
    /// For the fixpoint named, a result of the type the recursed-on parameter
    /// is refined from read at that parameter's stage: `F A^ι` in the body
    /// and `F A^{<ι}` at the self binder.
    Asked(ComputationId),
    /// The fixpoint asked for opened with its result read at the stage of its
    /// parameter at the position named.
    Staged(StagedPosition),
}

/// Whether a value in scope shows a stage is not the empty first one.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Room
{
    /// A hypothesis stands at a stage of a data type at or below the wanted
    /// stage: that stage holds a value, so it is above the first, and every
    /// constructor without a field of its family stands within it.
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

/// The families a case on `datatype`, or a constructor of it wanted at a
/// stage, refines at that stage: one mutual block's families share one
/// stage, as the kernel's do.
///
/// # Specification
/// - ensures: the mutual block of several families `datatype`'s declaration is
///   one of, or its declaration's block alone.
/// - fails: [`CheckRefusal::MachineInvariant`] for a type that is no data type;
///   the unfolding's refusal.
/// - panics: none.
/// - executable: none — the type is read through the weak-head unfolding the
///   body performs against the mutable context; a predicate would rerun it.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — a rose tree's node and its list of children, one block,
///   recurse through each other at one stage.
/// - witness: `tests::recursive_data::a_mutual_recursion_descends_through_its_block_s_families_in_both_checkers`
pub fn families(
    context: &mut CheckingContext<'_>,
    datatype: ValueTypeId,
) -> Result<crate::occurrence::Block, CheckRefusal>
{
    let head = context.whnf_value_type(datatype)?;
    let Some(&ValueType::Data { declaration, .. }) = context.arena().value_type(head)
    else {
        return Err(CheckRefusal::MachineInvariant);
    };
    Ok(match context.kin_of(declaration) {
        Maybe::Present(block) => block,
        Maybe::Absent(_) => crate::occurrence::Block::lone(declaration),
    })
}

/// Open the stage of the fixpoint `at` checked at `expected`, recursing on
/// the parameter at `position`.
///
/// # Specification
/// - requires: `expected` is formed.
/// - ensures: over a telescope with an arrow at `position`, a root stage `ι`
///   minted, the body's type the telescope with that arrow's domain at `A^ι`,
///   and the self binder's the same telescope with it at `A^{<ι}`; for `A` a
///   sum of data types, `A^ι` is the sum of each summand at `ι` — a mutual
///   block's recursion, its families' sum at one stage — and `A^{<ι}` the same
///   below it; every other arrow as `expected` holds them, and the codomain
///   past `position` too, except that a fixpoint the definition under way reads
///   as [`ResultStage::Asked`], at a plain arrow at `position`, returns a
///   result of type `A` past plain arrows at `A^ι` in the body and at `A^{<ι}`
///   at the self binder, and is then read as [`ResultStage::Staged`]. The
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
///   returner is refused; a recursion at the sum of a rose tree's two families
///   stages each summand.
/// - witness: `recursion::tests::a_recursion_descends_on_its_first_parameter`
/// - witness: `recursion::tests::a_structural_fixpoint_needs_an_arrow_to_recurse_on`
/// - witness: `tests::recursive_data::a_mutual_recursion_descends_through_its_block_s_families_in_both_checkers`
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
            | CompTypeView::Element { .. }
            | CompTypeView::Codata { .. } => {
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
    // A fixpoint asked to read its result at its parameter's stage returns a
    // result of the recursed-on type at `A^ι` in the body and at `A^{<ι}` at
    // the self binder, and notes that it did; a result under the parameter's
    // binder is read as declared.
    let (inside_codomain, own_codomain) = match context.result_stage() {
        ResultStage::Asked(fixpoint) if fixpoint == at && dependence == Dependence::Ambient => {
            let inside = result_at(context, codomain, (domain, Stage::At(root)))?;
            let own = result_at(context, codomain, (domain, below(Stage::At(root))))?;
            context.read_result(if inside == codomain {
                ResultStage::Declared
            }
            else {
                ResultStage::Staged(position)
            });
            (inside, own)
        },
        ResultStage::Asked(_) | ResultStage::Staged(_) | ResultStage::Declared => {
            (codomain, codomain)
        },
    };
    let arena = context.arena_mut();
    let (inside_domain, own_domain) = match arena.value_type(domain) {
        Some(&ValueType::Sum(ref summands))
            if !summands.is_empty()
                && summands.iter().all(|&summand| {
                    matches!(arena.value_type(summand), Some(&ValueType::Data { .. }))
                }) =>
        {
            let summands = summands.clone();
            let mut inside = Vec::with_capacity(summands.len());
            let mut own = Vec::with_capacity(summands.len());
            for &summand in &summands {
                inside.push(arena.value_type_staged(summand, Stage::At(root)));
                own.push(arena.value_type_staged(summand, below(Stage::At(root))));
            }
            (arena.value_type_sum(&inside), arena.value_type_sum(&own))
        },
        Some(_) | None => (
            arena.value_type_staged(domain, Stage::At(root)),
            arena.value_type_staged(domain, below(Stage::At(root))),
        ),
    };
    let mut own = dependence.former(arena, own_domain, own_codomain);
    let mut inside = dependence.former(arena, inside_domain, inside_codomain);
    while let Some((outer, dependence)) = spine.pop() {
        own = dependence.former(arena, outer, own);
        inside = dependence.former(arena, outer, inside);
    }
    Ok(Maybe::Present(Opened { own, inside }))
}

/// `codomain` with the result it returns read at `stage` where that result is
/// `base`, past every arrow before it.
///
/// # Specification
/// - requires: `codomain` is formed.
/// - ensures: for a telescope of arrows ending in a returner of `base`, the
///   same telescope ending in a returner of `base^stage` with the same effects;
///   `codomain` itself for any other.
/// - fails: the unfolding's refusal.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — a subtraction's result past its second argument is read
///   at its first argument's stage.
/// - witness: `recursion::tests::a_result_follows_the_parameter_it_recurses_on`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |&read| context.arena().comp_type(read).is_some()))]
fn result_at(
    context: &mut CheckingContext<'_>,
    codomain: CompTypeId,
    (base, stage): (ValueTypeId, Stage),
) -> Result<CompTypeId, CheckRefusal>
{
    let mut spine: Vec<ValueTypeId> = Vec::new();
    let mut cursor = codomain;
    let (result, effects) = loop {
        let head = context.whnf_comp_type(cursor)?;
        match comp_type_view(context.arena(), head)? {
            CompTypeView::Arrow { domain, codomain } => {
                spine.push(domain);
                cursor = codomain;
            },
            CompTypeView::Returner { result, effects } => break (result, effects.clone()),
            CompTypeView::Pi { .. }
            | CompTypeView::Unknown
            | CompTypeView::With(..)
            | CompTypeView::Element { .. }
            | CompTypeView::Codata { .. } => return Ok(codomain),
        }
    };
    if crate::conversion::equivalent(context, result, base)?
        != crate::conversion::Agreement::Convertible
    {
        return Ok(codomain);
    }
    let arena = context.arena_mut();
    let staged = arena.value_type_staged(base, stage);
    let mut read = arena.comp_type_returner_with_effects(staged, effects);
    while let Some(outer) = spine.pop() {
        read = arena.comp_type_arrow(outer, read);
    }
    Ok(read)
}

/// The motive a case checked at `expected` reads its branches at: the written
/// `motive` with its result read at the stage `expected` returns at, when the
/// motive names no scrutinee and returns the type that stage refines.
///
/// A motive is written without stages, as every type the lowering writes is:
/// a case in a body judged at a staged result returns at that stage, and its
/// branches owe it. The case's type is then compared with `expected` as any
/// other.
///
/// # Specification
/// - requires: `motive` is formed under one scrutinee binder, `expected` in the
///   case's context.
/// - ensures: present exactly when `expected` is a telescope of arrows ending
///   in a returner of a staged type `base^s`, `motive` strengthens past its
///   binder to a type `m` whose arrows end in a returner of `base`; then `m`
///   with that result read at `s`, shifted back under the binder.
/// - fails: the unfolding's refusal.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — a predecessor's case judged at a staged result reads its
///   branches there, and a motive at another type keeps its own.
/// - witness: `recursion::tests::a_result_follows_the_parameter_it_recurses_on`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |read| match *read {
    Maybe::Present(read) => context.arena().comp_type(read).is_some(),
    Maybe::Absent(reason) => reason == Unstaged::Plain,
}))]
pub fn motive_at(
    context: &mut CheckingContext<'_>,
    motive: CompTypeId,
    expected: CompTypeId,
) -> Result<Maybe<CompTypeId, Unstaged>, CheckRefusal>
{
    let plain = Maybe::Absent(Unstaged::Plain);
    let mut cursor = expected;
    let result = loop {
        let head = context.whnf_comp_type(cursor)?;
        match comp_type_view(context.arena(), head)? {
            CompTypeView::Arrow { codomain, .. } => cursor = codomain,
            CompTypeView::Returner { result, .. } => break result,
            CompTypeView::Pi { .. }
            | CompTypeView::Unknown
            | CompTypeView::With(..)
            | CompTypeView::Element { .. }
            | CompTypeView::Codata { .. } => return Ok(plain),
        }
    };
    let Some(&ValueType::Staged { base, stage }) = context.arena().value_type(result)
    else {
        return Ok(plain);
    };
    let Maybe::Present(written) =
        gandr_core_term::strengthen_comp_type(context.arena_mut(), motive)
    else {
        return Ok(plain);
    };
    let written = written.settle(context.arena_mut());
    let restaged = result_at(context, written, (base, stage))?;
    if restaged == written {
        return Ok(plain);
    }
    let read = gandr_core_term::shift_comp_type(context.arena_mut(), restaged, Binders::ONE)
        .settle(context.arena_mut());
    Ok(Maybe::Present(read))
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
/// A value of a stratified family at no stage is read at a fresh root: its
/// fields stand at that root, which nothing outside the arms is known to
/// reach, so a field under a function's domain takes only what the arm built
/// below it — never the scrutinee itself, which stands at no stage.
///
/// # Specification
/// - requires: `scrutinee` is the type the case's scrutinee synthesised.
/// - ensures: for `A^s` at an exact `s`, `A` and a fresh child of `s`; for a
///   bound `A^{<^k ι}`, `A` and a fresh child of the last of `k` fresh stages
///   chained below `ι`, which name the scrutinee's stage; for a stratified
///   family at no stage, the type as it stands and a fresh root; any other type
///   as it stands, with [`Unstaged::Plain`].
/// - fails: [`CheckRefusal::MachineInvariant`] for a stage this judgement did
///   not mint; the unfolding's refusal.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — a case on the recursed-on parameter and a case on one of
///   its fields each mint one child, so a call on a field two cases deep is two
///   steps below the fixpoint's stage; a case on a stratified value at no stage
///   binds its negative field at a root its own scrutinee does not fit.
/// - witness: `recursion::tests::a_call_on_a_value_rebuilt_below_the_stage_is_admitted`
/// - witness: `tests::recursive_data::currys_consumer_is_refused_at_its_call`
#[spec(ensures: |ret| match ret {
    Ok((read, Maybe::Present(_))) => read == scrutinee || matches!(context.arena().value_type(scrutinee), Some(&ValueType::Staged { base, .. }) if base == read),
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
        let head = context.whnf_value_type(scrutinee)?;
        if let Some(&ValueType::Data { declaration, .. }) = context.arena().value_type(head)
            && context.stratification(declaration) == crate::occurrence::Stratification::Stratified
        {
            return Ok((scrutinee, Maybe::Present(context.stages_mut().mint_root())));
        }
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

/// One node of a type a staging rebuild reads.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Part
{
    /// A value type.
    Value(ValueTypeId),
    /// A computation type.
    Computation(CompTypeId),
}

/// What a staging rebuild does with a node next.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Visit
{
    /// Read the node: stage it, or queue its placed children.
    Open(Part),
    /// Rebuild the node from its children's results.
    Close(Part),
}

/// Hand each child of `part` the stage order places to `each`, in order: the
/// former's own children where it is placeable, the types an argument of a
/// data type quotes, and none for any other former.
///
/// # Specification
/// trivial.
fn placed<Each>(
    arena: &CoreArena,
    part: Part,
    mut each: Each,
) where
    Each: FnMut(Part),
{
    match part {
        Part::Value(id) => match arena.value_type(id) {
            Some(&ValueType::Data { ref arguments, .. }) => {
                for &argument in arguments {
                    if let Some(&Value::Quote(quoted)) = arena.value(argument) {
                        each(Part::Value(quoted));
                    }
                }
            },
            Some(&ValueType::Thunk(body)) => each(Part::Computation(body)),
            Some(&ValueType::Record(ref fields)) => {
                for &field in fields.values() {
                    each(Part::Value(field));
                }
            },
            Some(&(ValueType::Product(ref parts) | ValueType::Sum(ref parts))) => {
                for &component in parts {
                    each(Part::Value(component));
                }
            },
            Some(&ValueType::Sigma { first, second }) => {
                each(Part::Value(first));
                each(Part::Value(second));
            },
            Some(&ValueType::List(element)) => each(Part::Value(element)),
            Some(_) | None => {},
        },
        Part::Computation(id) => match arena.comp_type(id) {
            Some(&(CompType::Arrow { domain, codomain } | CompType::Pi { domain, codomain })) => {
                each(Part::Value(domain));
                each(Part::Computation(codomain));
            },
            Some(&CompType::Returner { result, .. }) => each(Part::Value(result)),
            Some(&CompType::With(ref components)) => {
                for &component in components {
                    each(Part::Computation(component));
                }
            },
            Some(_) | None => {},
        },
    }
}

/// The value type a rebuilt child is.
///
/// # Specification
/// trivial.
const fn value_part(part: Part) -> Result<ValueTypeId, CheckRefusal>
{
    match part {
        Part::Value(id) => Ok(id),
        Part::Computation(_) => Err(CheckRefusal::MachineInvariant),
    }
}

/// The computation type a rebuilt child is.
///
/// # Specification
/// trivial.
const fn computation_part(part: Part) -> Result<CompTypeId, CheckRefusal>
{
    match part {
        Part::Computation(id) => Ok(id),
        Part::Value(_) => Err(CheckRefusal::MachineInvariant),
    }
}

/// `part` rebuilt over `children`, the results of its placed children in
/// order.
///
/// # Specification
/// - requires: `children` holds one result per child [`placed`] hands out for
///   `part`, of the same kind, in order.
/// - ensures: the same former over `children`.
/// - fails: [`CheckRefusal::MachineInvariant`] for a child of the wrong kind or
///   count.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — a function field over its own family is rebuilt at the
///   case's stage, so a call through it on the chain before the link is
///   admitted and one on the link itself is refused.
/// - witness: `tests::recursive_data::a_negative_occurrence_below_the_stage_declares`
/// - witness: `tests::recursive_data::currys_consumer_is_refused_at_its_call`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |rebuilt| matches!((part, *rebuilt),
    (Part::Value(_), Part::Value(_)) | (Part::Computation(_), Part::Computation(_)))))]
fn rebuild(
    arena: &mut CoreArena,
    part: Part,
    children: &[Part],
) -> Result<Part, CheckRefusal>
{
    let child = |position: usize| {
        children
            .get(position)
            .copied()
            .ok_or(CheckRefusal::MachineInvariant)
    };
    match part {
        Part::Value(id) => match arena.value_type(id).cloned() {
            Some(ValueType::Data {
                declaration,
                mut arguments,
            }) => {
                let mut next = 0_usize;
                for argument in &mut arguments {
                    if let Some(&Value::Quote(_)) = arena.value(*argument) {
                        let quoted = value_part(child(next)?)?;
                        next = next.saturating_add(1);
                        *argument = arena.value_quote(quoted);
                    }
                }
                Ok(Part::Value(arena.value_type_data(declaration, arguments)))
            },
            Some(ValueType::Thunk(_)) => {
                let body = computation_part(child(0)?)?;
                Ok(Part::Value(arena.value_type_thunk(body)))
            },
            Some(ValueType::Record(mut fields)) => {
                for (position, field) in fields.values_mut().enumerate() {
                    *field = value_part(child(position)?)?;
                }
                Ok(Part::Value(arena.value_type_record(fields)))
            },
            Some(ValueType::Product(_)) => {
                let parts = children
                    .iter()
                    .map(|&component| value_part(component))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(Part::Value(arena.value_type_product(&parts)))
            },
            Some(ValueType::Sum(_)) => {
                let parts = children
                    .iter()
                    .map(|&component| value_part(component))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(Part::Value(arena.value_type_sum(&parts)))
            },
            Some(ValueType::Sigma { .. }) => {
                let (first, second) = (value_part(child(0)?)?, value_part(child(1)?)?);
                Ok(Part::Value(arena.value_type_sigma(first, second)))
            },
            Some(ValueType::List(_)) => {
                let element = value_part(child(0)?)?;
                Ok(Part::Value(arena.value_type_list(element)))
            },
            Some(_) | None => Err(CheckRefusal::MachineInvariant),
        },
        Part::Computation(id) => match arena.comp_type(id).cloned() {
            Some(CompType::Arrow { .. }) => {
                let (domain, codomain) = (value_part(child(0)?)?, computation_part(child(1)?)?);
                Ok(Part::Computation(arena.comp_type_arrow(domain, codomain)))
            },
            Some(CompType::Pi { .. }) => {
                let (domain, codomain) = (value_part(child(0)?)?, computation_part(child(1)?)?);
                Ok(Part::Computation(arena.comp_type_pi(domain, codomain)))
            },
            Some(CompType::Returner { effects, .. }) => {
                let result = value_part(child(0)?)?;
                Ok(Part::Computation(
                    arena.comp_type_returner_with_effects(result, effects),
                ))
            },
            Some(CompType::With(_)) => {
                let parts = children
                    .iter()
                    .map(|&component| computation_part(component))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(Part::Computation(arena.comp_type_with(&parts)))
            },
            Some(_) | None => Err(CheckRefusal::MachineInvariant),
        },
    }
}

/// A field type with every occurrence of a family of `block` the stage order
/// places refined at `stage`.
///
/// The occurrence walk admitted the field only with every such occurrence
/// uniform, so each is matched by its declaration rather than by conversion:
/// the family at the constructor's arguments is the only application of it a
/// placed position holds.
///
/// # Specification
/// - requires: `field` is a field type of a family of `block` its occurrence
///   walk admitted.
/// - ensures: the field with each application of a family of `block` reached
///   through the placeable formers — a thunk, a function's domain and codomain,
///   a returner's result, a record's fields, a product's and a sum's parts, a
///   dependent pair, a list, a lazy product, and the types a data type's
///   arguments quote — at `stage`; the field itself, the same node, when it
///   holds none.
/// - fails: [`CheckRefusal::MachineInvariant`] for a malformed arena.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Termination
/// - reason: the `while let` worklist, not recursion; each node is opened once
///   and closed once.
/// - measure: the unread nodes under `field`, finite because the arena is
///   acyclic.
///
/// # Adequacy
/// - hypothesis: L3 — a direct field, a function field, a field under a
///   function's domain and a field of a family quoting the type each move to
///   the stage, and a field holding none stays.
/// - witness: `recursion::tests::a_call_on_a_value_rebuilt_below_the_stage_is_admitted`
/// - witness: `recursion::tests::a_type_parameter_instantiates_at_a_staged_code`
/// - witness: `tests::recursive_data::currys_consumer_is_refused_at_its_call`
/// - witness: `tests::recursive_data::accessibility_is_decided_on_every_former`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |&staged| staged == field
    || context.arena().value_type(staged).is_some()))]
pub fn stage_field(
    context: &mut CheckingContext<'_>,
    field: ValueTypeId,
    block: &crate::occurrence::Block,
    stage: Stage,
) -> Result<ValueTypeId, CheckRefusal>
{
    let arena = context.arena_mut();
    let mut visits = alloc::vec![Visit::Open(Part::Value(field))];
    let mut results: Vec<Part> = Vec::new();
    while let Some(visit) = visits.pop() {
        match visit {
            Visit::Open(part) => {
                if let Part::Value(id) = part
                    && let Some(&ValueType::Data { declaration, .. }) = arena.value_type(id)
                    && block.family(declaration) == crate::occurrence::Membership::Family
                {
                    results.push(Part::Value(arena.value_type_staged(id, stage)));
                    continue;
                }
                visits.push(Visit::Close(part));
                let start = visits.len();
                placed(arena, part, |child| visits.push(Visit::Open(child)));
                visits
                    .get_mut(start ..)
                    .ok_or(CheckRefusal::MachineInvariant)?
                    .reverse();
            },
            Visit::Close(part) => {
                let mut count = 0_usize;
                placed(arena, part, |_child| count = count.saturating_add(1));
                let first = results
                    .len()
                    .checked_sub(count)
                    .ok_or(CheckRefusal::MachineInvariant)?;
                let children = results
                    .get(first ..)
                    .ok_or(CheckRefusal::MachineInvariant)?;
                let mut kept = true;
                let mut position = 0_usize;
                placed(arena, part, |child| {
                    kept = kept && children.get(position) == Some(&child);
                    position = position.saturating_add(1);
                });
                let rebuilt = if kept {
                    part
                }
                else {
                    rebuild(arena, part, children)?
                };
                results.truncate(first);
                results.push(rebuilt);
            },
        }
    }
    match results.as_slice() {
        &[Part::Value(staged)] => Ok(staged),
        &[] | &[Part::Computation(_)] | &[_, _, ..] => Err(CheckRefusal::MachineInvariant),
    }
}

/// A case branch's type with its recursive fields at the stage the case
/// opened, and, inside the declaration's own fixpoint, its constant in the
/// fields read as its self binder.
///
/// The identification is the one a mutual block's definition needs: a
/// universe's field `b : +U (el(a) -> -F U)` names the decoder `el` being
/// admitted, and inside `el`'s own fixpoint the arm opening that field reads
/// `el(a)` as the self call `el[<](a)` on a field one stage below — the type
/// the arm's own staged decode `el[<](a)` has. It is not a new rule: the
/// field is the constructor's, the self binder the fixpoint's, and the
/// identified telescope is formed again before the branch checks at it, so a
/// field that applies the decoder where the stage does not descend is refused
/// `StageNotBelow` there.
///
/// # Specification
/// - requires: `branch` is the telescope over one binder per entry of `fields`
///   that [`crate::former::branch_type`] built over `datatype`: a Π where the
///   rest names the field, a plain arrow otherwise.
/// - ensures: the same telescope, each field under the same former, with each
///   field domain's placed occurrences of `datatype` — or of any family of its
///   mutual block, the [`families`] of it — at `child` through [`stage_field`];
///   inside the declaration's own fixpoint, every occurrence of its constant in
///   a field domain replaced by its self binder, and [`Identified::Read`]
///   exactly when one was, the telescope then owed its formation in the block's
///   foresight.
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
///   plain arrows `branch_type` builds there; a decoder's arm reads its
///   universe's field through its self binder, and a field decoding the
///   constructor's own result is refused.
/// - witness: `recursion::tests::a_recursion_descends_on_its_first_parameter`
/// - witness: `recursion::tests::a_type_parameter_instantiates_at_a_staged_code`
/// - witness: `tests::recursive_data::a_mutual_block_is_admitted_in_both_checkers`
/// - witness: `tests::recursive_data::a_mutual_recursion_descends_through_its_block_s_families_in_both_checkers`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |&(staged, _)| context.arena().comp_type(staged).is_some()))]
pub fn stage_branch(
    context: &mut CheckingContext<'_>,
    datatype: ValueTypeId,
    branch: CompTypeId,
    (fields, child): (&[ValueTypeId], StageId),
) -> Result<(CompTypeId, Identified), CheckRefusal>
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
                | CompType::Codata { .. }
                | CompType::Unknown),
            )
            | None => return Err(CheckRefusal::MachineInvariant),
        };
        domains.push((domain, dependence));
        focus = codomain;
    }
    let own = context.own_fixpoint();
    let block = families(context, datatype)?;
    let mut identified = Identified::Kept;
    // A field stands under the Π binders before it, and only those: a plain
    // arrow's rest was strengthened past its field.
    let mut depth = 0_u32;
    for &mut (ref mut domain, dependence) in &mut domains {
        *domain = stage_field(context, *domain, &block, Stage::At(child))?;
        if let Maybe::Present((constant, index)) = own {
            let past = u32::from(index)
                .checked_add(depth)
                .ok_or(CheckRefusal::MachineInvariant)?;
            let read = gandr_core_term::abstract_constant_value_type(
                context.arena_mut(),
                *domain,
                constant,
                DeBruijnIndex::from(past),
            );
            if read != *domain {
                *domain = read;
                identified = Identified::Read;
            }
        }
        if dependence == Dependence::Dependent {
            depth = depth.checked_add(1).ok_or(CheckRefusal::MachineInvariant)?;
        }
    }
    for &(domain, dependence) in domains.iter().rev() {
        focus = dependence.former(context.arena_mut(), domain, focus);
    }
    Ok((focus, identified))
}

/// Whether a branch read the declaration's constant as its self binder.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Identified
{
    /// No field named it.
    Kept,
    /// Some field did: the telescope forms again in the block's foresight.
    Read,
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
        | ValueTypeView::World(_)
        | ValueTypeView::Unknown => Ok(Maybe::Absent(Unstaged::Plain)),
    }
}

/// Whether a hypothesis in scope shows `wanted` is above the first stage.
///
/// A data type's first stage is empty — every constructor stands one step
/// above its recursive fields — so a hypothesis at a stage of a data type is
/// a value there, and its stage is above the first. A constructor with no
/// field whose own type is its family stands at every stage above the first;
/// so it stands within `wanted` exactly when some such stage lies within it.
/// A stage that only a case minted shows nothing: an arm binding no
/// recursive field holds no value at the case's stage, and that stage may be
/// the first.
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

/// The code a type parameter is instantiated at, when the code written for it
/// is plain and a later argument holds it at a stage: that staged code.
///
/// A source never writes a stage, so a type argument is its plain code `⌜T⌝`,
/// and the term keeps it on the wire. The stage is re-derived from the first
/// later argument of the application's spine that is a variable whose type, at
/// the place its own domain names the parameter, holds `T` at a stage: the
/// parameter itself (`El a` against `T^s`), or an argument of a data type
/// (`D(…, a, …)` against `D(…, ⌜T^s⌝, …)`). The stage is read off that
/// argument, never searched for, and every argument of the spine is then
/// checked at `⌜T^s⌝`: a function handed on with it must take values at `s`,
/// as a recursion's self binder does when `s` is below its stage. The
/// instantiation is a classifier like any other, so the result carries the
/// stage through.
///
/// # Specification
/// - requires: `codomain` is the codomain of the dependent arrow `code` checked
///   against, under that arrow's binder; `spine` the arguments applied after
///   `code`, in order.
/// - ensures: for `code` the quote of a type `T`, the first variable of
///   `spine`, walked down `codomain`'s arrows, whose type is `T^s` where its
///   domain is the binder's decode, or a data type holding `⌜T^s⌝` where its
///   domain, the same data type, holds the binder: the code `⌜T^s⌝`, with
///   `T^s`'s base equivalent to `T`; [`Unstaged::Plain`] when no argument holds
///   one, or for a `code` that is no quote.
/// - fails: the conversion's refusal.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — a rose tree's children handed to `map` instantiate its
///   element at their stage, and the claim handed beside them is admitted; the
///   node itself in a one-element list instantiates nothing and the claim is
///   refused; a value of a stage handed to a generic `apply` instantiates its
///   parameter at that stage.
/// - witness: `recursion::tests::a_type_parameter_instantiates_at_a_staged_code`
/// - witness: `recursion::tests::a_claim_at_the_scrutinee_through_map_is_refused`
#[spec(ensures: |ret| match ret {
    Ok(Maybe::Present(staged)) => matches!(context.arena().value(staged), Some(&Value::Quote(quoted))
        if matches!(context.arena().value_type(quoted), Some(ValueType::Staged { .. }))),
    Ok(Maybe::Absent(Unstaged::Plain)) | Err(_) => true,
    Ok(Maybe::Absent(Unstaged::Unknown)) => false,
})]
pub fn instantiation<Spine>(
    context: &mut CheckingContext<'_>,
    (code, codomain): (ValueId, CompTypeId),
    spine: Spine,
) -> Result<Maybe<ValueId, Unstaged>, CheckRefusal>
where
    Spine: IntoIterator<Item = ValueId>,
{
    let Some(&Value::Quote(written)) = context.arena().value(code)
    else {
        return Ok(Maybe::Absent(Unstaged::Plain));
    };
    let mut telescope = codomain;
    let mut binder = 0_u32;
    for argument in spine {
        let (domain, rest, binds) = match context.arena().comp_type(telescope) {
            Some(&CompType::Pi { domain, codomain }) => (domain, codomain, Dependence::Dependent),
            Some(&CompType::Arrow { domain, codomain }) => (domain, codomain, Dependence::Ambient),
            Some(_) | None => break,
        };
        if let Some(&Value::Variable {
            zone: Zone::Intuitionistic,
            index,
        }) = context.arena().value(argument)
        {
            let declared = context.hypothesis(index)?;
            let found = shift_value_type(context.arena_mut(), declared, Binders::past(index))
                .settle(context.arena_mut());
            if let Maybe::Present((base, held)) = held_at(
                context.arena(),
                (domain, DeBruijnIndex::from(binder)),
                found,
            ) && crate::conversion::equivalent(context, base, written)?
                == crate::conversion::Agreement::Convertible
            {
                let staged = match held {
                    Held::Itself => context.arena_mut().value_quote(found),
                    Held::Argument(staged) => staged,
                };
                return Ok(Maybe::Present(staged));
            }
        }
        if binds == Dependence::Dependent {
            binder = binder
                .checked_add(1)
                .ok_or(CheckRefusal::MachineInvariant)?;
        }
        telescope = rest;
    }
    Ok(Maybe::Absent(Unstaged::Plain))
}

/// The type an application of `head` to `last` reads, `applied` as the arrow
/// gives it: for a call into a definition whose result follows its parameter
/// at a position, a result of that parameter's type read at the stage of the
/// argument there.
///
/// The definition was judged with that result at its own parameter's stage
/// (`module`'s second judgement), so it holds at every stage the argument
/// stands at: `minus(p, d)`, for `p` a field one stage below a fixpoint's,
/// returns a natural at that stage, which the fixpoint's self binder then
/// takes. The stage is read off a variable argument, never searched for, as
/// [`instantiation`] reads a type parameter's.
///
/// # Specification
/// - requires: `applied` is the computation type the application of `head` to
///   `last` has.
/// - ensures: for `head` a spine of applications over the force of a following
///   constant, `applied` a returner of the type its argument at the followed
///   position is refined from, and that argument a variable at a stage, the
///   same returner at that stage; `applied` otherwise.
/// - fails: the unfolding's refusal; [`CheckRefusal::MachineInvariant`] for a
///   variable out of scope.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — a division calling a subtraction on its dividend's
///   predecessor descends on the result; a call on a value at no stage leaves
///   the result at none.
/// - witness: `recursion::tests::a_result_follows_the_parameter_it_recurses_on`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |&read| context.arena().comp_type(read).is_some()))]
pub fn followed(
    context: &mut CheckingContext<'_>,
    (head, last): (ComputationId, ValueId),
    applied: CompTypeId,
) -> Result<CompTypeId, CheckRefusal>
{
    let mut arguments = alloc::vec![last];
    let mut cursor = head;
    let constant = loop {
        match context.arena().computation(cursor) {
            Some(&gandr_core_term::Computation::Application(inner, argument)) => {
                arguments.push(argument);
                cursor = inner;
            },
            Some(&gandr_core_term::Computation::Force(forced)) => {
                match context.arena().value(forced) {
                    Some(&Value::Constant(constant)) => break constant,
                    Some(_) | None => return Ok(applied),
                }
            },
            Some(_) | None => return Ok(applied),
        }
    };
    let Maybe::Present(position) = context.following(constant)
    else {
        return Ok(applied);
    };
    let Some(&argument) = arguments
        .len()
        .checked_sub(usize::from(position).saturating_add(1))
        .and_then(|from_last| arguments.get(from_last))
    else {
        return Ok(applied);
    };
    let Some(&Value::Variable {
        zone: Zone::Intuitionistic,
        index,
    }) = context.arena().value(argument)
    else {
        return Ok(applied);
    };
    let declared = context.hypothesis(index)?;
    let found = shift_value_type(context.arena_mut(), declared, Binders::past(index))
        .settle(context.arena_mut());
    let Some(&ValueType::Staged { base, stage }) = context.arena().value_type(found)
    else {
        return Ok(applied);
    };
    let read = context.whnf_comp_type(applied)?;
    let CompTypeView::Returner { result, effects } = comp_type_view(context.arena(), read)?
    else {
        return Ok(applied);
    };
    let effects = effects.clone();
    if crate::conversion::equivalent(context, result, base)?
        != crate::conversion::Agreement::Convertible
    {
        return Ok(applied);
    }
    let arena = context.arena_mut();
    let staged = arena.value_type_staged(base, stage);
    Ok(arena.comp_type_returner_with_effects(staged, effects))
}

/// Where a variable's type holds a staged code for a type parameter.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Held
{
    /// The variable's type is itself the staged type.
    Itself,
    /// The variable's type holds the staged code as a data type's argument.
    Argument(ValueId),
}

/// The base of the staged type `found` holds where `domain` names `binder`,
/// and where it holds it.
///
/// # Specification
/// - ensures: for `domain` the decode of the variable `binder` and `found` a
///   staged type, its base and [`Held::Itself`]; for `domain` a data type with
///   an argument the variable `binder` and `found` — read through its own stage
///   — the same data type whose argument there is the quote of a staged type,
///   that type's base and [`Held::Argument`] of the quote, the first such
///   argument's; [`Unstaged::Plain`] otherwise.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — `map`'s list parameter meets a rose tree's children at
///   their stage, and `apply`'s decoded parameter a predecessor at its stage; a
///   list built around the scrutinee holds no stage.
/// - witness: `recursion::tests::a_type_parameter_instantiates_at_a_staged_code`
/// - witness: `recursion::tests::a_claim_at_the_scrutinee_through_map_is_refused`
#[spec(ensures: |ret| match ret {
    Maybe::Present((base, Held::Itself)) => matches!(arena.value_type(found),
        Some(&ValueType::Staged { base: inner, .. }) if inner == base),
    Maybe::Present((base, Held::Argument(quote))) => matches!(arena.value(quote), Some(&Value::Quote(quoted))
        if matches!(arena.value_type(quoted), Some(&ValueType::Staged { base: inner, .. }) if inner == base)),
    Maybe::Absent(Unstaged::Plain) => true,
    Maybe::Absent(Unstaged::Unknown) => false,
})]
fn held_at(
    arena: &CoreArena,
    (domain, binder): (ValueTypeId, DeBruijnIndex),
    found: ValueTypeId,
) -> Maybe<(ValueTypeId, Held), Unstaged>
{
    let names = |value: ValueId| {
        matches!(arena.value(value), Some(&Value::Variable {
            zone: Zone::Intuitionistic,
            index,
        }) if index == binder)
    };
    let staged = |value: ValueId| match arena.value(value) {
        Some(&Value::Quote(quoted)) => match arena.value_type(quoted) {
            Some(&ValueType::Staged { base, .. }) => Maybe::Present(base),
            Some(_) | None => Maybe::Absent(Unstaged::Plain),
        },
        Some(_) | None => Maybe::Absent(Unstaged::Plain),
    };
    let unstaged = match arena.value_type(found) {
        Some(&ValueType::Staged { base, .. }) => base,
        Some(_) | None => found,
    };
    match (arena.value_type(domain), arena.value_type(unstaged)) {
        (Some(&ValueType::Element { code, .. }), Some(_)) if names(code) && unstaged != found => {
            Maybe::Present((unstaged, Held::Itself))
        },
        (
            Some(&ValueType::Data {
                declaration: wanted,
                arguments: ref parameters,
            }),
            Some(&ValueType::Data {
                declaration,
                ref arguments,
            }),
        ) if wanted == declaration && parameters.len() == arguments.len() => parameters
            .iter()
            .zip(arguments)
            .find_map(
                |(&parameter, &argument)| match (names(parameter), staged(argument)) {
                    (true, Maybe::Present(base)) => Some((base, Held::Argument(argument))),
                    (true | false, Maybe::Present(_) | Maybe::Absent(_)) => None,
                },
            )
            .map_or(Maybe::Absent(Unstaged::Plain), Maybe::Present),
        (Some(_) | None, Some(_) | None) => Maybe::Absent(Unstaged::Plain),
    }
}

#[cfg(test)]
mod tests;
