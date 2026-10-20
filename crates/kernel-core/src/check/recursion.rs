//! The recursion core, re-derived: a structural fixpoint typed by stages.
//!
//! The rules are the checker's, read against the kernel's own terms, and the
//! order deciding "below" is [`crate::stage_order::StageOrder`], the one type
//! both judgements grow:
//!
//! - **A fixpoint opens a stage.** [`open_fixpoint`] mints a root `ι` for the
//!   parameter at the fixpoint's staged position: the body checks with that
//!   parameter at `A^ι`, the self binder with it at `A^{<ι}`.
//! - **A case opens one stage below its scrutinee's.** [`open_case`] mints one
//!   child of a scrutinee's stage, after naming a bound by fresh stages, and
//!   [`stage_branch`] binds each field at it through [`stage_field`], which
//!   moves every occurrence of the block's families the occurrence walk placed
//!   — under a function's domain too — to that child. A stratified value at no
//!   stage is read at a fresh root, so a function field it holds never takes
//!   the value itself.
//! - **A definition's own constant is its fixpoint's self binder.** Inside the
//!   structural fixpoint a definition opens first, [`stage_branch`] reads each
//!   occurrence of the definition's own constant in a field type as the self
//!   binder — how a family its mutual block admits names its decoder — and the
//!   case forms the branch so read, so a decoder named at a place that does not
//!   descend is refused by the stage order like any other call.
//! - **A constructor stands above its fields.** [`constructor_fields`] checks a
//!   constructor wanted at a stage with its recursive fields one step lower; a
//!   constructor with no field whose own type is its family needs a value in
//!   scope at a stage of a data type within the wanted one ([`room`]), since a
//!   thunked field may hold a computation that never returns (#598).
//! - **Subsumption is the order**, decided where a synthesized type meets a
//!   wanted one: [`unstage`] at the top, and [`subsumes`] through the thunked
//!   arrows a function field's stage stands under, covariantly in results and
//!   the components of records, products, sums, lists, Σ types and `&`, and
//!   contravariantly in domains; invariant conversion compares a stage as
//!   itself.
//! - **A type parameter instantiates at a staged code.** [`instantiation`]
//!   reads the code an application hands a type parameter at the stage of the
//!   first later variable argument whose parameter's type holds it — as `El a`
//!   or as a data type's argument — when the stage's base converts with the
//!   written code's type, so the plain code the wire carries re-derives the
//!   staged one the checker held.
//!
//! No stage reaches the wire and none is presented: formation refuses a stage
//! in a presented type, so every stage this module reads is one it minted, the
//! ones [`instantiation`] carries into a code included.

use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_term::CompType;
use gandr_kernel_term::CompTypeId;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::ConstructorTag;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FieldPosition;
use gandr_kernel_term::Stage;
use gandr_kernel_term::StageId;
use gandr_kernel_term::StagedPosition;
use gandr_kernel_term::Standing;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::Value;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueType;
use gandr_kernel_term::ValueTypeId;
use quenchant_shape::shape::Maybe;

use super::Goal;
use crate::env::AdmittedDeclaration;
use crate::error::ExpectedComputationShape;
use crate::error::KernelError;
use crate::rewrite;
use crate::stage_order::Fit;
use crate::stage_order::StageOrder;
use crate::stage_order::below;
use crate::support::SupportContext;

/// Why a type opens no stage.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(super) enum Unstaged
{
    /// The type is refined at no stage.
    Plain,
}

/// Why a case reads no constant as its definition's self binder.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(super) enum Unowned
{
    /// The case stands under no fixpoint its declaration opened first.
    Outside,
}

/// A field domain that named the definition's own constant, read at the self
/// binder before its recursive occurrences are staged: the type the case
/// forms, so a decode at a place that does not descend is refused.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct Read
{
    /// The constructor whose branch binds the field.
    pub tag: ConstructorTag,
    /// The field, by position.
    pub field: FieldPosition,
    /// Its domain with the constant read as the self binder.
    pub domain: ValueTypeId,
}

/// The families a case on `datatype`, or a constructor of it wanted at a
/// stage, refines at that stage: one mutual block's families share one stage.
///
/// A field of a sibling family is a structural part of the value as a field
/// of its own family is — the block's families are one inductive definition
/// read at several sorts — so a case binds it one stage below its scrutinee
/// and a constructor wants it one stage below its own, the same set on both
/// sides.
///
/// # Specification
/// - requires: `entries` are the admitted declarations `datatype` resolves in.
/// - ensures: the block `datatype`'s declaration was admitted in, or its
///   declaration's block alone when no entry holds it.
/// - fails: a shape mismatch wanting a data type for any other type.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — a rose tree's node and its list of children, one block,
///   recurse through each other at one stage, and a lone family's case stages
///   only its own fields.
/// - witness: `tests::recursive_data::a_mutual_recursion_descends_through_its_block_s_families`
#[spec(ensures: |ret| ret.is_ok() == matches!(arena.value_type(datatype), Some(&ValueType::Data { .. })))]
pub(super) fn families(
    arena: &TermArena,
    entries: &[AdmittedDeclaration],
    datatype: ValueTypeId,
) -> Result<super::occurrence::Block, KernelError>
{
    let Some(&ValueType::Data { declaration, .. }) = arena.value_type(datatype)
    else {
        return Err(super::value_shape_mismatch(
            arena,
            crate::error::ExpectedValueShape::Data,
            datatype,
        ));
    };
    Ok(entries.get(usize::from(declaration)).map_or_else(
        || super::occurrence::Block::lone(declaration),
        AdmittedDeclaration::block,
    ))
}

/// The two types a fixpoint opening its stage checks at.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct Opened
{
    /// The self binder's computation type: the recursed-on parameter at the
    /// bound `<ι`.
    pub own: CompTypeId,
    /// The body's computation type: the recursed-on parameter at `ι`.
    pub inside: CompTypeId,
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
        arena: &mut TermArena,
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

/// Open the stage of a fixpoint checked at `expected`, recursing on the
/// parameter at `position`.
///
/// # Specification
/// - requires: `expected` is formed.
/// - ensures: a root stage `ι` minted, the body's type the telescope with the
///   arrow at `position` taking `A^ι`, and the self binder's the same telescope
///   with it at `A^{<ι}`; for `A` a sum of data types, `A^ι` is the sum of each
///   summand at `ι` — a mutual block's recursion, its families' sum at one
///   stage — and `A^{<ι}` the same below it; every other arrow, and the
///   codomain past `position`, as `expected` holds them.
/// - fails: [`KernelError::ComputationShapeMismatch`] wanting an arrow when the
///   telescope ends, in a returner, a lazy product or a decode, before
///   `position`: a fixpoint whose self-reference is not below its own stage
///   need not terminate, so a structural one is never checked unstaged.
/// - panics: none.
///
/// # Errors
/// As `- fails:`, and [`KernelError::ArenaFault`] for an unreadable type.
///
/// # Adequacy
/// - hypothesis: L3 — a first-parameter recursion opens the first arrow and is
///   admitted, the same recursion calling itself at its own parameter is
///   refused, and a fixpoint at a returner opens nothing; a recursion at the
///   sum of a rose tree's two families stages each summand.
/// - witness: `tests::recursive_data::a_recursion_descends_on_its_first_parameter`
/// - witness: `tests::recursive_data::a_structural_fixpoint_needs_an_arrow_to_recurse_on`
/// - witness: `tests::recursive_data::a_mutual_recursion_descends_through_its_block_s_families`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |opened| arena.comp_type(opened.own).is_some() && arena.comp_type(opened.inside).is_some()))]
pub(super) fn open_fixpoint(
    arena: &mut TermArena,
    stages: &mut StageOrder,
    expected: CompTypeId,
    position: StagedPosition,
) -> Result<Opened, KernelError>
{
    // The telescope down to the recursed-on arrow, outermost first: each
    // domain, and whether its codomain is under its binder.
    let mut spine: Vec<(ValueTypeId, Dependence)> = Vec::new();
    let mut cursor = expected;
    let (domain, codomain, dependence) = loop {
        let (domain, codomain, dependence) = match arena.comp_type(cursor) {
            Some(&CompType::Arrow { domain, codomain }) => (domain, codomain, Dependence::Ambient),
            Some(&CompType::Pi { domain, codomain }) => (domain, codomain, Dependence::Dependent),
            Some(
                &(CompType::Returner(_)
                | CompType::With(..)
                | CompType::Element { .. }
                | CompType::Codata { .. }),
            ) => {
                return Err(super::comp_shape_mismatch(
                    arena,
                    ExpectedComputationShape::Arrow,
                    expected,
                ));
            },
            None => return Err(KernelError::ArenaFault),
        };
        if spine.len() == usize::from(position) {
            break (domain, codomain, dependence);
        }
        spine.push((domain, dependence));
        cursor = codomain;
    };
    let root = stages.mint_root();
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
    let mut own = dependence.former(arena, own_domain, codomain);
    let mut inside = dependence.former(arena, inside_domain, codomain);
    while let Some((outer, dependence)) = spine.pop() {
        own = dependence.former(arena, outer, own);
        inside = dependence.former(arena, outer, inside);
    }
    Ok(Opened { own, inside })
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
/// - requires: `scrutinee` is the type the case's scrutinee synthesized, and
///   `entries` the admitted declarations it resolves in.
/// - ensures: for `A^s` at an exact `s`, `A` and a fresh child of `s`; for a
///   bound `A^{<^k ι}`, `A` and a fresh child of the last of `k` fresh stages
///   chained below `ι`, which name the scrutinee's stage; for a stratified
///   family at no stage, the type as it stands and a fresh root; any other type
///   as it stands, with [`Unstaged::Plain`].
/// - fails: [`KernelError::StagePresented`] for a stage this order never
///   minted.
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
/// - witness: `tests::recursive_data::a_call_on_a_value_rebuilt_below_the_stage_is_admitted`
/// - witness: `tests::recursive_data::currys_consumer_is_refused_at_its_call`
#[spec(ensures: |ret| match ret {
    Ok((read, Maybe::Present(_))) => read == scrutinee || matches!(arena.value_type(scrutinee), Some(&ValueType::Staged { base, .. }) if base == read),
    Ok((read, Maybe::Absent(_))) => read == scrutinee,
    Err(_) => true,
})]
pub(super) fn open_case(
    arena: &TermArena,
    entries: &[AdmittedDeclaration],
    stages: &mut StageOrder,
    scrutinee: ValueTypeId,
) -> Result<(ValueTypeId, Maybe<StageId, Unstaged>), KernelError>
{
    let Some(&ValueType::Staged { base, stage }) = arena.value_type(scrutinee)
    else {
        if let Some(&ValueType::Data { declaration, .. }) = arena.value_type(scrutinee)
            && entries.get(usize::from(declaration)).is_some_and(|entry| {
                entry.accessibility().stratification()
                    == super::occurrence::Stratification::Stratified
            })
        {
            return Ok((scrutinee, Maybe::Present(stages.mint_root())));
        }
        return Ok((scrutinee, Maybe::Absent(Unstaged::Plain)));
    };
    let unminted = |_unminted| KernelError::StagePresented;
    let exact = match stage {
        Stage::At(exact) => exact,
        Stage::Below { anchor, depth } => {
            let mut parent = anchor;
            for _step in 0 .. u32::from(depth) {
                parent = stages.mint_below(parent).map_err(unminted)?;
            }
            parent
        },
    };
    let child = stages.mint_below(exact).map_err(unminted)?;
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
    arena: &TermArena,
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
            Some(
                &(ValueType::Session { .. }
                | ValueType::PathUniverse(..)
                | ValueType::FlowUniverse(..)
                | ValueType::Path { .. }
                | ValueType::Flow { .. }
                | ValueType::Bridge { .. }
                | ValueType::Base(_)
                | ValueType::Universe { .. }
                | ValueType::Lift { .. }
                | ValueType::Element { .. }
                | ValueType::Abstract(_)
                | ValueType::StaticPi { .. }
                | ValueType::Staged { .. }),
            )
            | None => {},
        },
        Part::Computation(id) => match arena.comp_type(id) {
            Some(&(CompType::Arrow { domain, codomain } | CompType::Pi { domain, codomain })) => {
                each(Part::Value(domain));
                each(Part::Computation(codomain));
            },
            Some(&CompType::Returner(result)) => each(Part::Value(result)),
            Some(&CompType::With(ref components)) => {
                for &component in components {
                    each(Part::Computation(component));
                }
            },
            Some(&(CompType::Element { .. } | CompType::Codata { .. })) | None => {},
        },
    }
}

/// The value type a rebuilt child is.
///
/// # Specification
/// trivial.
const fn value_part(part: Part) -> Result<ValueTypeId, KernelError>
{
    match part {
        Part::Value(id) => Ok(id),
        Part::Computation(_) => Err(KernelError::ArenaFault),
    }
}

/// The computation type a rebuilt child is.
///
/// # Specification
/// trivial.
const fn computation_part(part: Part) -> Result<CompTypeId, KernelError>
{
    match part {
        Part::Computation(id) => Ok(id),
        Part::Value(_) => Err(KernelError::ArenaFault),
    }
}

/// `part` rebuilt over `children`, the results of its placed children in
/// order.
///
/// # Specification
/// - requires: `children` holds one result per child [`placed`] hands out for
///   `part`, of the same kind, in order.
/// - ensures: the same former over `children`.
/// - fails: [`KernelError::ArenaFault`] for a child of the wrong kind or count.
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
    arena: &mut TermArena,
    part: Part,
    children: &[Part],
) -> Result<Part, KernelError>
{
    let child = |position: usize| {
        children
            .get(position)
            .copied()
            .ok_or(KernelError::ArenaFault)
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
            Some(
                ValueType::Session { .. }
                | ValueType::PathUniverse(..)
                | ValueType::FlowUniverse(..)
                | ValueType::Path { .. }
                | ValueType::Flow { .. }
                | ValueType::Bridge { .. }
                | ValueType::Base(_)
                | ValueType::Universe { .. }
                | ValueType::Lift { .. }
                | ValueType::Element { .. }
                | ValueType::Abstract(_)
                | ValueType::StaticPi { .. }
                | ValueType::Staged { .. },
            )
            | None => Err(KernelError::ArenaFault),
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
            Some(CompType::Returner(_)) => {
                let result = value_part(child(0)?)?;
                Ok(Part::Computation(arena.comp_type_returner(result)))
            },
            Some(CompType::With(_)) => {
                let parts = children
                    .iter()
                    .map(|&component| computation_part(component))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(Part::Computation(arena.comp_type_with(&parts)))
            },
            Some(CompType::Element { .. } | CompType::Codata { .. }) | None => {
                Err(KernelError::ArenaFault)
            },
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
/// - fails: [`KernelError::ArenaFault`] for an unreadable type.
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
/// - hypothesis: L3 — a direct field moves to the stage and a call on it is
///   admitted; a field under a function's domain moves with it; a field holding
///   no occurrence stays.
/// - witness: `tests::recursive_data::a_call_on_a_value_rebuilt_below_the_stage_is_admitted`
/// - witness: `tests::recursive_data::currys_consumer_is_refused_at_its_call`
/// - witness: `tests::recursive_data::a_negative_occurrence_below_the_stage_declares`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |&staged| staged == field
    || arena.value_type(staged).is_some()))]
pub(super) fn stage_field(
    arena: &mut TermArena,
    field: ValueTypeId,
    block: super::occurrence::Block,
    stage: Stage,
) -> Result<ValueTypeId, KernelError>
{
    let mut visits = alloc::vec![Visit::Open(Part::Value(field))];
    let mut results: Vec<Part> = Vec::new();
    while let Some(visit) = visits.pop() {
        match visit {
            Visit::Open(part) => {
                if let Part::Value(id) = part
                    && let Some(&ValueType::Data { declaration, .. }) = arena.value_type(id)
                    && block.membership(declaration) == super::occurrence::Membership::Family
                {
                    results.push(Part::Value(arena.value_type_staged(id, stage)));
                    continue;
                }
                visits.push(Visit::Close(part));
                let start = visits.len();
                placed(arena, part, |child| visits.push(Visit::Open(child)));
                visits
                    .get_mut(start ..)
                    .ok_or(KernelError::ArenaFault)?
                    .reverse();
            },
            Visit::Close(part) => {
                let mut count = 0_usize;
                placed(arena, part, |_child| count = count.saturating_add(1));
                let first = results
                    .len()
                    .checked_sub(count)
                    .ok_or(KernelError::ArenaFault)?;
                let children = results.get(first ..).ok_or(KernelError::ArenaFault)?;
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
        &[] | &[Part::Computation(_)] | &[_, _, ..] => Err(KernelError::ArenaFault),
    }
}

/// A case branch's type with its recursive fields at the stage the case
/// opened, and the definition's own constant read as its self binder.
///
/// # Specification
/// - requires: `branch` is the Pi telescope over one binder per entry of
///   `fields` that `former::branch_type` built over the case's data type, a
///   family of `block` — its [`families`]; `own`, when present, is the
///   declaration's position and its fixpoint's self binder as an index in the
///   case's context.
/// - ensures: the same telescope with each field domain's occurrences of a
///   family of `block` the stage order places at `child` ([`stage_field`]) and,
///   under `own`, every occurrence of the constant in a domain replaced by the
///   self binder raised past the fields before it; each domain that named the
///   constant pushed onto `reads` under `tag`, as read and before staging.
/// - fails: [`KernelError::ArenaFault`] for a telescope shorter than `fields`.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — the successor's field moves to the case's stage and a
///   call on it is admitted, while the zero branch binds nothing; a universe's
///   function field names its decoder, read as the self binder, and the decoder
///   at a place that does not descend is refused.
/// - witness: `tests::recursive_data::a_recursion_descends_on_its_first_parameter`
/// - witness: `tests::recursive_data::a_mutual_block_is_admitted`
/// - witness: `tests::recursive_data::a_mutual_recursion_descends_through_its_block_s_families`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |&staged| arena.comp_type(staged).is_some()))]
pub(super) fn stage_branch(
    arena: &mut TermArena,
    session: &mut SupportContext,
    (block, tag): (super::occurrence::Block, ConstructorTag),
    branch: CompTypeId,
    (fields, child): (&[ValueTypeId], StageId),
    (own, reads): (
        Maybe<(ConstantIndex, DeBruijnIndex), Unowned>,
        &mut Vec<Read>,
    ),
) -> Result<CompTypeId, KernelError>
{
    let mut domains = Vec::with_capacity(fields.len());
    let mut focus = branch;
    for _field in fields {
        let Some(&CompType::Pi { domain, codomain }) = arena.comp_type(focus)
        else {
            return Err(KernelError::ArenaFault);
        };
        domains.push(domain);
        focus = codomain;
    }
    for (index, domain) in domains.iter_mut().enumerate() {
        let depth = u32::try_from(index).map_err(|_overflow| KernelError::ConstructorArity)?;
        if let Maybe::Present((constant, binder)) = own {
            let (table, memo) = session.rewrite_parts();
            // The self binder stands outside the fields before this one.
            // reason: an index past the ceiling clamps, as a shift's does.
            let raised = DeBruijnIndex::from(u32::from(quenchant_arith::arith::saturating_add(
                quenchant_arith::arith::Int::from(u32::from(binder)),
                quenchant_arith::arith::Int::from(depth),
            )));
            let read = rewrite::abstract_constant_value_type(
                arena,
                table,
                memo,
                *domain,
                (constant, raised),
            );
            if read != *domain {
                reads.push(Read {
                    tag,
                    field: FieldPosition::from(index),
                    domain: read,
                });
                *domain = read;
            }
        }
        *domain = stage_field(arena, *domain, block, Stage::At(child))?;
    }
    for &domain in domains.iter().rev() {
        focus = arena.comp_type_pi(domain, focus);
    }
    Ok(focus)
}

/// The field goals of a constructor wanted at the stage `wanted` of `base`.
///
/// # Specification
/// - requires: `goals` are the field goals `former::constructor` built for a
///   constructor of a data type of `block` — its [`families`] — each a value
///   check.
/// - ensures: each goal with its field's occurrences of a family of `block` the
///   stage order places one step below `wanted` ([`stage_field`]); with no
///   field whose own type is a family of `block`, the goals so staged once
///   [`room`] witnesses a value in scope at a stage of a data type within
///   `wanted`.
/// - fails: [`KernelError::StageNotBelow`] from the top for a constructor with
///   no such field and no such value: the first stage of a data type is empty,
///   so nothing shows `wanted` holds one. A thunked recursive field shows
///   nothing: it may hold a computation that never returns (#598).
/// - panics: none.
///
/// # Errors
/// As `- fails:`, and [`KernelError::ArenaFault`] for an unreadable type.
///
/// # Adequacy
/// - hypothesis: L3 — a nullary argument under a successor arm's field is
///   admitted, and the same argument under the zero arm, where the case has
///   minted its stage but bound nothing at it, is refused; a rose tree's node
///   rebuilt below the stage wants its list of children below it; a constructor
///   whose one recursive field is thunked is refused with nothing below the
///   stage.
/// - witness: `tests::recursive_data::a_nullary_argument_needs_a_value_below_the_stage`
/// - witness: `tests::recursive_data::a_mutual_recursion_descends_through_its_block_s_families`
/// - witness: `tests::recursive_data::a_thunked_field_shows_no_value_below_the_stage_598`
#[spec(ensures: |ret| match ret {
    Ok(()) => true,
    Err(ref error) => matches!(*error, KernelError::StageNotBelow { found: Standing::Top, bound } if bound == wanted) || *error == KernelError::ArenaFault,
})]
pub(super) fn constructor_fields(
    arena: &mut TermArena,
    (stages, context): (&StageOrder, &[ValueTypeId]),
    block: super::occurrence::Block,
    wanted: Stage,
    goals: &mut [Goal],
) -> Result<(), KernelError>
{
    let mut holding = Holding::Nothing;
    for goal in goals.iter_mut() {
        let Goal::CheckValue(field, field_type) = *goal
        else {
            return Err(KernelError::ArenaFault);
        };
        let staged = stage_field(arena, field_type, block, below(wanted))?;
        if staged != field_type {
            *goal = Goal::CheckValue(field, staged);
        }
        if matches!(arena.value_type(staged), Some(ValueType::Staged { .. })) {
            holding = Holding::Field;
        }
    }
    match (holding, room(arena, stages, context, wanted)) {
        (Holding::Field, _) | (Holding::Nothing, Room::Witnessed) => Ok(()),
        (Holding::Nothing, Room::Unwitnessed) => Err(KernelError::StageNotBelow {
            found: Standing::Top,
            bound: wanted,
        }),
    }
}

/// Whether a constructor's fields hold a value below its stage.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Holding
{
    /// A field whose own type is a family of the block does.
    Field,
    /// None does.
    Nothing,
}

/// Whether a value in scope shows a stage is not the empty first one.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Room
{
    /// A hypothesis stands at a stage of a data type at or below the wanted
    /// stage.
    Witnessed,
    /// No hypothesis does.
    Unwitnessed,
}

/// Whether a hypothesis in `context` shows `wanted` is above the first stage.
///
/// A data type's first stage is empty, so a hypothesis at a stage of a data
/// type is a value there and its stage is above the first; a constructor with
/// no field of its family stands at every stage above the first. A stage only
/// a case minted shows nothing: an arm binding no recursive field holds no
/// value at the case's stage, which may be the first.
///
/// # Specification
/// - ensures: [`Room::Witnessed`] exactly when some slot of `context` is `A^s`
///   with `A` a data type and `s` within `wanted`.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`constructor_fields`].
/// - witness: `tests::recursive_data::a_nullary_argument_needs_a_value_below_the_stage`
#[spec(ensures: |ret| ret == Room::Unwitnessed || context.iter().any(|&slot| matches!(arena.value_type(slot), Some(ValueType::Staged { .. }))))]
fn room(
    arena: &TermArena,
    stages: &StageOrder,
    context: &[ValueTypeId],
    wanted: Stage,
) -> Room
{
    let witnessed = context.iter().any(|&slot| {
        matches!(arena.value_type(slot), Some(&ValueType::Staged { base, stage })
            if matches!(arena.value_type(base), Some(ValueType::Data { .. }))
                && stages.fit(stage, wanted) == Fit::Within)
    });
    if witnessed {
        Room::Witnessed
    }
    else {
        Room::Unwitnessed
    }
}

/// The pair a synthesized `found` meets a wanted `expected` as, once their
/// stages are decided.
///
/// # Specification
/// - ensures: two staged types at stages the order fits give their bases; a
///   staged `found` against an unstaged `expected` gives its base beside
///   `expected`, since a stage refines values and never identity; two unstaged
///   types are returned as they stand.
/// - fails: [`KernelError::StageNotBelow`] for two stages the order does not
///   fit, and from the top for an unstaged `found` where a stage is wanted.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — a field below the stage passes at the self binder's
///   bound, the parameter at the stage itself does not, and a value at no stage
///   does not.
/// - witness: `tests::recursive_data::a_recursion_descends_on_its_first_parameter`
#[spec(ensures: |ret| match ret {
    Ok((wanted, _)) => !matches!(arena.value_type(wanted), Some(ValueType::Staged { .. })),
    Err(ref error) => matches!(*error, KernelError::StageNotBelow { .. }),
})]
pub(super) fn unstage(
    arena: &TermArena,
    stages: &StageOrder,
    expected: ValueTypeId,
    found: ValueTypeId,
) -> Result<(ValueTypeId, ValueTypeId), KernelError>
{
    match (arena.value_type(expected), arena.value_type(found)) {
        (
            Some(&ValueType::Staged {
                base: wanted,
                stage: bound,
            }),
            Some(&ValueType::Staged { base, stage }),
        ) => match stages.fit(stage, bound) {
            Fit::Within => Ok((wanted, base)),
            Fit::NotBelow => Err(KernelError::StageNotBelow {
                found: Standing::Staged(stage),
                bound,
            }),
        },
        (Some(&ValueType::Staged { stage: bound, .. }), Some(_) | None) => {
            Err(KernelError::StageNotBelow {
                found: Standing::Top,
                bound,
            })
        },
        (Some(_) | None, Some(&ValueType::Staged { base, .. })) => Ok((expected, base)),
        (Some(_) | None, Some(_) | None) => Ok((expected, found)),
    }
}

/// A pair [`subsumes`] compares, the wanted side first.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(super) enum Subsumed
{
    /// Two value types.
    Values(ValueTypeId, ValueTypeId),
    /// Two computation types.
    Comps(CompTypeId, CompTypeId),
}

/// Whether the found side of `pair` stands where its wanted side is wanted,
/// each stage on either side decided by the order.
///
/// A recursive occurrence is staged wherever the stage order places it — under
/// a thunk and arrows (`U (A → F T^s)`), and through a product's, a sum's, a
/// record's, a list's, a dependent pair's and a lazy product's parts — so a
/// field handed on at its declared type meets that type below the top. The
/// walk reads a thunk, a returner, an arrow's result and those parts
/// covariantly and an arrow's domain contravariantly, as sized types order a
/// function space and the checker's subtyping orders the parts; every other
/// pair is compared by conversion.
///
/// # Specification
/// - ensures: `Ok` exactly when every pair the walk reaches is two equal types,
///   a found staged type within a wanted one's stage over agreeing bases, a
///   found staged type over a base agreeing with an unstaged wanted type, or
///   two types the conversion relates.
/// - fails: [`KernelError::StageNotBelow`] at the first stage the order does
///   not fit or the first unstaged found type where a stage is wanted; the
///   conversion's refusal at the first pair it separates.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — a function field at a stage handed on at its declared
///   type is admitted, and the self binder handed on where any value of its
///   domain is wanted is refused; a negative field below its stage, under its
///   thunk's domain, is handed on at the arm's stage.
/// - witness: `tests::recursive_data::derived_eliminators_are_admitted`
/// - witness: `tests::recursive_data::a_self_reference_never_stands_for_an_unstaged_function`
/// - witness: `tests::recursive_data::a_negative_occurrence_below_the_stage_declares`
#[spec(ensures: |ret| match pair {
    Subsumed::Values(wanted, found) if wanted == found => ret.is_ok(),
    Subsumed::Comps(wanted, found) if wanted == found => ret.is_ok(),
    Subsumed::Values(..) | Subsumed::Comps(..) => true,
})]
pub(super) fn subsumes(
    arena: &TermArena,
    stages: &StageOrder,
    pair: Subsumed,
) -> Result<(), KernelError>
{
    let mut work = alloc::vec![pair];
    while let Some(pair) = work.pop() {
        match pair {
            Subsumed::Values(wanted, found) if wanted == found => {},
            Subsumed::Values(wanted, found) => {
                match (arena.value_type(wanted), arena.value_type(found)) {
                    (
                        Some(&ValueType::Staged {
                            base: wanted,
                            stage: bound,
                        }),
                        Some(&ValueType::Staged { base, stage }),
                    ) => {
                        if stages.fit(stage, bound) == Fit::NotBelow {
                            return Err(KernelError::StageNotBelow {
                                found: Standing::Staged(stage),
                                bound,
                            });
                        }
                        work.push(Subsumed::Values(wanted, base));
                    },
                    (Some(&ValueType::Staged { stage: bound, .. }), Some(_) | None) => {
                        return Err(KernelError::StageNotBelow {
                            found: Standing::Top,
                            bound,
                        });
                    },
                    (Some(_) | None, Some(&ValueType::Staged { base, .. })) => {
                        work.push(Subsumed::Values(wanted, base));
                    },
                    (Some(&ValueType::Thunk(wanted)), Some(&ValueType::Thunk(found))) => {
                        work.push(Subsumed::Comps(wanted, found));
                    },
                    (Some(&ValueType::List(wanted)), Some(&ValueType::List(found))) => {
                        work.push(Subsumed::Values(wanted, found));
                    },
                    (
                        Some(&ValueType::Sigma {
                            first: wanted_first,
                            second: wanted_second,
                        }),
                        Some(&ValueType::Sigma { first, second }),
                    ) => {
                        work.push(Subsumed::Values(wanted_second, second));
                        work.push(Subsumed::Values(wanted_first, first));
                    },
                    (
                        Some(&ValueType::Product(ref wanted_parts)),
                        Some(&ValueType::Product(ref parts)),
                    )
                    | (Some(&ValueType::Sum(ref wanted_parts)), Some(&ValueType::Sum(ref parts)))
                        if wanted_parts.len() == parts.len() =>
                    {
                        work.extend(
                            wanted_parts
                                .iter()
                                .zip(parts)
                                .map(|(&wanted, &found)| Subsumed::Values(wanted, found)),
                        );
                    },
                    (
                        Some(&ValueType::Record(ref wanted_fields)),
                        Some(&ValueType::Record(ref fields)),
                    ) if wanted_fields.keys().eq(fields.keys()) => {
                        work.extend(
                            wanted_fields
                                .values()
                                .zip(fields.values())
                                .map(|(&wanted, &found)| Subsumed::Values(wanted, found)),
                        );
                    },
                    (Some(_) | None, Some(_) | None) => {
                        crate::conv::convert_value_type(arena, wanted, found)?;
                    },
                }
            },
            Subsumed::Comps(wanted, found) if wanted == found => {},
            Subsumed::Comps(wanted, found) => {
                match (arena.comp_type(wanted), arena.comp_type(found)) {
                    (
                        Some(&CompType::Arrow {
                            domain: wanted_domain,
                            codomain: wanted_codomain,
                        }),
                        Some(&CompType::Arrow { domain, codomain }),
                    )
                    | (
                        Some(&CompType::Pi {
                            domain: wanted_domain,
                            codomain: wanted_codomain,
                        }),
                        Some(&CompType::Pi { domain, codomain }),
                    ) => {
                        work.push(Subsumed::Comps(wanted_codomain, codomain));
                        work.push(Subsumed::Values(domain, wanted_domain));
                    },
                    (Some(&CompType::Returner(wanted)), Some(&CompType::Returner(found))) => {
                        work.push(Subsumed::Values(wanted, found));
                    },
                    (Some(&CompType::With(ref wanted)), Some(&CompType::With(ref found)))
                        if wanted.len() == found.len() =>
                    {
                        work.extend(
                            wanted
                                .iter()
                                .zip(found.iter())
                                .rev()
                                .map(|(&wanted, &found)| Subsumed::Comps(wanted, found)),
                        );
                    },
                    (Some(_) | None, Some(_) | None) => {
                        crate::conv::convert_comp_type(arena, wanted, found)?;
                    },
                }
            },
        }
    }
    Ok(())
}

/// The code a type parameter is instantiated at, when the code on the wire is
/// plain and a later argument holds it at a stage: that staged code,
/// re-derived.
///
/// No stage crosses the wire, so a type argument is its plain code `⌜T⌝`. The
/// kernel re-derives the stage the checker read: from the first later argument
/// of the application's spine that is a variable whose type — the case that
/// bound it staged it — holds `T` at a stage where its own domain names the
/// parameter: the parameter itself (`El a` against `T^s`), or an argument of a
/// data type (`D(…, a, …)` against `D(…, ⌜T^s⌝, …)`). Every argument of the
/// spine is then checked at `⌜T^s⌝`, so a function handed on with it must take
/// values at `s`, and a claim that does not descend is refused by the order.
///
/// # Specification
/// - requires: `codomain` is the codomain under the binder of the dependent
///   arrow `code` is applied to, `context` the machine's typing context, and
///   `spine` the arguments applied after `code`, in order.
/// - ensures: for `code` the quote of a type `T`, the first variable of
///   `spine`, walked down `codomain`'s arrows, whose type is `T^s` where its
///   domain is the binder's decode, or a data type holding `⌜T^s⌝` where its
///   domain, the same data type, holds the binder: the code `⌜T^s⌝`, with
///   `T^s`'s base convertible with `T`; [`Unstaged::Plain`] when no argument
///   holds one, or for a `code` that is no quote.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a rose tree's children handed to `map` instantiate its
///   element at their stage, and the claim handed beside them is admitted; the
///   node itself in a one-element list instantiates nothing and the claim is
///   refused; a value of a stage handed to a generic `apply` instantiates its
///   parameter at that stage.
/// - witness: `tests::recursive_data::a_type_parameter_instantiates_at_a_staged_code`
/// - witness: `tests::recursive_data::a_claim_at_the_scrutinee_through_map_is_refused`
#[spec(ensures: |ret| match ret {
    Maybe::Present(staged) => matches!(arena.value(staged), Some(&Value::Quote(quoted))
        if matches!(arena.value_type(quoted), Some(ValueType::Staged { .. }))),
    Maybe::Absent(Unstaged::Plain) => true,
})]
pub(super) fn instantiation<Spine>(
    arena: &mut TermArena,
    (session, context): (&mut SupportContext, &[ValueTypeId]),
    (code, codomain): (ValueId, CompTypeId),
    spine: Spine,
) -> Maybe<ValueId, Unstaged>
where
    Spine: IntoIterator<Item = ValueId>,
{
    let Some(&Value::Quote(written)) = arena.value(code)
    else {
        return Maybe::Absent(Unstaged::Plain);
    };
    let mut telescope = codomain;
    let mut binder = 0_u32;
    for argument in spine {
        let (domain, rest, binds) = match arena.comp_type(telescope) {
            Some(&CompType::Pi { domain, codomain }) => (domain, codomain, Dependence::Dependent),
            Some(&CompType::Arrow { domain, codomain }) => (domain, codomain, Dependence::Ambient),
            Some(_) | None => break,
        };
        if let Some(&Value::Variable(index)) = arena.value(argument)
            && let Maybe::Present(found) = super::lookup(arena, session, context, index)
            && let Maybe::Present((base, held)) =
                held_at(arena, (domain, DeBruijnIndex::from(binder)), found)
            && crate::conv::convertible_value_types(arena, base, written)
                == crate::conv::Convertibility::Convertible
        {
            return Maybe::Present(match held {
                Held::Itself => arena.value_quote(found),
                Held::Argument(staged) => staged,
            });
        }
        if binds == Dependence::Dependent {
            let Some(next) = binder.checked_add(1)
            else {
                break;
            };
            binder = next;
        }
        telescope = rest;
    }
    Maybe::Absent(Unstaged::Plain)
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
/// - witness: `tests::recursive_data::a_type_parameter_instantiates_at_a_staged_code`
/// - witness: `tests::recursive_data::a_claim_at_the_scrutinee_through_map_is_refused`
#[spec(ensures: |ret| match ret {
    Maybe::Present((base, Held::Itself)) => matches!(arena.value_type(found),
        Some(&ValueType::Staged { base: inner, .. }) if inner == base),
    Maybe::Present((base, Held::Argument(quote))) => matches!(arena.value(quote), Some(&Value::Quote(quoted))
        if matches!(arena.value_type(quoted), Some(&ValueType::Staged { base: inner, .. }) if inner == base)),
    Maybe::Absent(Unstaged::Plain) => true,
})]
fn held_at(
    arena: &TermArena,
    (domain, binder): (ValueTypeId, DeBruijnIndex),
    found: ValueTypeId,
) -> Maybe<(ValueTypeId, Held), Unstaged>
{
    let names = |value: ValueId| matches!(arena.value(value), Some(&Value::Variable(index)) if index == binder);
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
mod tests
{
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::Stage;
    use gandr_kernel_term::StageId;
    use gandr_kernel_term::Standing;
    use gandr_kernel_term::TermArena;
    use gandr_kernel_term::Value;
    use gandr_kernel_term::ValueType;

    use super::Subsumed;
    use super::stage_field;
    use super::subsumes;
    use crate::check::occurrence::Block;
    use crate::error::KernelError;
    use crate::stage_order::StageOrder;

    #[test]
    fn a_data_argument_moves_to_the_stage_only_where_it_quotes_the_family()
    {
        let mut arena = TermArena::new();
        let stage = Stage::At(StageId::from(0_usize));
        let family = ConstantIndex::from(0_usize);
        let recursive = arena.value_type_data(family, alloc::vec![]);
        let other = arena.value_type_unit();
        let holder = ConstantIndex::from(1_usize);
        let quoted = arena.value_quote(recursive);
        let holding = arena.value_type_data(holder, alloc::vec![quoted]);
        let refined =
            stage_field(&mut arena, holding, Block::lone(family), stage).expect("a readable field");
        let Some(&ValueType::Data { ref arguments, .. }) = arena.value_type(refined)
        else {
            panic!("a data field stays data");
        };
        let [argument] = **arguments
        else {
            panic!("one argument");
        };
        let Some(&Value::Quote(quoted)) = arena.value(argument)
        else {
            panic!("the argument quotes a type");
        };
        assert!(matches!(
            arena.value_type(quoted),
            Some(&ValueType::Staged { base, stage: at }) if base == recursive && at == stage
        ));
        let quoted_other = arena.value_quote(other);
        let elsewhere = arena.value_type_data(holder, alloc::vec![quoted_other]);
        assert_eq!(
            stage_field(&mut arena, elsewhere, Block::lone(family), stage),
            Ok(elsewhere),
            "an argument quoting another type stays"
        );
    }

    #[test]
    fn a_staged_type_meets_a_staged_bound_by_the_stage_order()
    {
        let mut arena = TermArena::new();
        let mut order = StageOrder::default();
        let root = order.mint_root();
        let child = order.mint_below(root).expect("the root is minted");
        let base = arena.value_type_unit();
        let at_root = arena.value_type_staged(base, Stage::At(root));
        let at_child = arena.value_type_staged(base, Stage::At(child));
        assert_eq!(
            subsumes(&arena, &order, Subsumed::Values(at_root, at_child)),
            Ok(()),
            "a child stage is within its parent"
        );
        assert_eq!(
            subsumes(&arena, &order, Subsumed::Values(at_child, at_root)),
            Err(KernelError::StageNotBelow {
                found: Standing::Staged(Stage::At(root)),
                bound: Stage::At(child),
            }),
            "a parent is not within its child"
        );
    }
}
