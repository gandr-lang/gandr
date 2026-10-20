//! Codata: a declaration's observations, read as one lazy product.
//!
//! A codata declaration `νX. &{dᵢ : Bᵢ}` states a parameter telescope, a
//! computation universe as its kind and one computation type per observation,
//! each scoped under the parameters. Its application `Codata(d, ā)` is a
//! computation type. It converts nominally — one declaration at convertible
//! arguments — and is read through its observations only where a rule needs
//! its shape: an introduction checked against it and an elimination of a
//! computation that synthesizes it. The read instantiates every observation at
//! `ā` and forms the lazy product of them, a single observation a lazy product
//! of one. There is no η: a codata type never converts with its observation
//! product.
//!
//! Inside its own admission the declaration names itself only at an
//! observation's result — the end of the observation's arrow spine — and only
//! at its parameter variables in telescope order, so every coinductive
//! occurrence stands behind an observation. The fixpoints that inhabit a
//! codata type are partial fixpoints; their productivity is not judged here.
//!
//! # References
//! - Andreas Abel, Brigitte Pientka, David Thibodeau and Anton Setzer,
//!   "Copatterns: programming infinite structures by observations", POPL 2013.

use anodized::spec;
use gandr_kernel_strata::Level;
use gandr_kernel_term::AnyNode;
use gandr_kernel_term::CompType;
use gandr_kernel_term::CompTypeId;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::DeclarationContent;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::Value;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueType;
use gandr_kernel_term::ValueTypeId;

use super::former::FamilyArity;
use super::former::ParameterPrefix;
use crate::env::AdmittedDeclaration;
use crate::env::ConstantSearch;
use crate::env::Mention;
use crate::error::KernelError;
use crate::rewrite;
use crate::rewrite::BinderDepth;
use crate::support::SupportContext;

/// A codata declaration's borrowed telescope and observations.
#[derive(Clone, Copy, Debug)]
pub(super) struct Signature<'signature>
{
    /// Classifiers scoped under their preceding parameters.
    pub parameters: &'signature [ValueTypeId],
    /// Observation types scoped under the entire parameter telescope.
    pub observations: &'signature [CompTypeId],
    /// The computation universe the declaration inhabits.
    pub kind: ValueTypeId,
}

/// Resolve a codata head through the declaration being admitted, then the
/// admitted prefix.
///
/// # Specification
/// - requires: the judgement's entries are the immutable admitted prefix.
/// - ensures: a head naming the codata declaration being admitted borrows its
///   own signature; any other head borrows the admitted codata declaration at
///   that position.
/// - provides: a codata declaration in scope at its own position while its
///   observations form.
/// - fails: a position that names no codata declaration.
/// - panics: none.
///
/// # Errors
/// Returns `NotACodataType` for a position naming neither the declaration
/// being admitted nor admitted codata.
///
/// # Adequacy
/// - hypothesis: L3 — a stream's tail forms through its own declaration, and
///   the same head after admission resolves through the prefix; a data position
///   is refused.
/// - witness: `tests::codata::a_stream_is_admitted_and_observed`
/// - witness: `tests::codata::a_data_head_is_not_codata`
#[spec(ensures: |ret| ret.is_ok() == (matches!(judgement.block, super::Block::Codata { position, .. } if position == index)
    || matches!(judgement.entries.get(usize::from(index)).map(AdmittedDeclaration::content), Some(DeclarationContent::Codata { .. }))))]
pub(super) fn resolve<'session>(
    judgement: super::Judgement<'session>,
    index: ConstantIndex,
) -> Result<Signature<'session>, KernelError>
{
    if let super::Block::Codata {
        position,
        signature,
    } = judgement.block
        && position == index
    {
        return Ok(signature);
    }
    let Some(&DeclarationContent::Codata {
        ref parameters,
        ref observations,
        kind,
    }) = judgement
        .entries
        .get(usize::from(index))
        .map(AdmittedDeclaration::content)
    else {
        return Err(KernelError::NotACodataType { index });
    };
    Ok(Signature {
        parameters,
        observations,
        kind,
    })
}

/// Read a codata declaration's computation universe level.
///
/// # Specification
/// - requires: nothing.
/// - ensures: success is exactly a computation universe, at its level.
/// - fails: a missing node or any other kind.
/// - panics: none.
///
/// # Errors
/// Returns `ArenaFault` or `CodataKindNotUniverse`.
///
/// # Adequacy
/// - hypothesis: L3 — a value universe as a codata kind is refused.
/// - witness: `tests::codata::a_value_universe_is_no_codata_kind`
#[spec(ensures: |ret| ret.is_ok() == matches!(arena.value_type(kind), Some(ValueType::Universe { sort: GroundSort::Computation, .. })))]
pub(super) fn level(
    arena: &TermArena,
    kind: ValueTypeId,
) -> Result<Level, KernelError>
{
    let &ValueType::Universe {
        sort: GroundSort::Computation,
        ref level,
    } = arena.value_type(kind).ok_or(KernelError::ArenaFault)?
    else {
        return Err(KernelError::CodataKindNotUniverse);
    };
    Ok(level.clone())
}

/// Refuse a self reference anywhere but at an observation's result.
///
/// # Specification
/// - requires: `observation` is scoped under `parameters` binders, the
///   declaration being admitted takes `position`, and `search` seeks
///   `position`.
/// - ensures: success exactly when `position` is named by no domain of the
///   observation's arrow spine and, at the spine's end, either not at all or by
///   a codata application of `position` whose arguments are the parameter
///   variables in telescope order, read under the spine's dependent binders.
/// - provides: the guard that keeps every coinductive occurrence behind an
///   observation; each domain is searched until its first occurrence, the nodes
///   earlier domains and observations shared walked once.
/// - fails: any other occurrence of `position`.
/// - panics: none.
///
/// # Errors
/// Returns `CodataOccurrence` for an unguarded or non-uniform self reference,
/// and `ArenaFault` for an unreadable node.
///
/// # Adequacy
/// - hypothesis: L3 — a stream's tail is admitted; a self reference in a domain
///   and one at other arguments are refused.
/// - witness: `tests::codata::a_stream_is_admitted_and_observed`
/// - witness: `tests::codata::an_unguarded_self_reference_is_refused`
/// - witness: `tests::codata::a_non_uniform_self_reference_is_refused`
#[spec(requires: arena.comp_type(observation).is_some())]
pub(super) fn guarded(
    arena: &TermArena,
    (position, search): (ConstantIndex, &mut ConstantSearch),
    FamilyArity(parameters): FamilyArity,
    observation: CompTypeId,
) -> Result<(), KernelError>
{
    let mut names = |node: AnyNode| search.names(arena, node) == Mention::Named;
    let mut binders = 0_usize;
    let mut cursor = observation;
    loop {
        match *arena.comp_type(cursor).ok_or(KernelError::ArenaFault)? {
            CompType::Arrow { domain, codomain } => {
                if names(AnyNode::ValueType(domain)) {
                    return Err(KernelError::CodataOccurrence);
                }
                cursor = codomain;
            },
            CompType::Pi { domain, codomain } => {
                if names(AnyNode::ValueType(domain)) {
                    return Err(KernelError::CodataOccurrence);
                }
                binders = binders.saturating_add(1);
                cursor = codomain;
            },
            CompType::Codata {
                declaration,
                ref arguments,
            } if declaration == position => {
                let uniform = arguments.len() == parameters
                    && arguments.iter().enumerate().all(|(index, argument)| {
                        let expected = parameters
                            .saturating_sub(index)
                            .saturating_sub(1)
                            .saturating_add(binders);
                        u32::try_from(expected).is_ok_and(|expected| {
                            arena.value(*argument)
                                == Some(&Value::Variable(DeBruijnIndex::from(expected)))
                        })
                    });
                return if uniform {
                    Ok(())
                }
                else {
                    Err(KernelError::CodataOccurrence)
                };
            },
            CompType::Returner(_)
            | CompType::Element { .. }
            | CompType::With(..)
            | CompType::Codata { .. } => {
                return if names(AnyNode::CompType(cursor)) {
                    Err(KernelError::CodataOccurrence)
                }
                else {
                    Ok(())
                };
            },
        }
    }
}

/// The `index`th argument of a codata application, with the classifier it
/// checks at: `classifier`, the telescope's `index`th parameter, instantiated
/// at the arguments before it.
///
/// # Specification
/// - requires: `classifier` is scoped under the parameters before it.
/// - ensures: the application's `index`th argument, and `classifier` with each
///   earlier parameter replaced by its argument; the first parameter's
///   classifier answers itself.
/// - fails: an unreadable or non-codata node, or an index past the arguments.
/// - panics: none.
///
/// # Errors
/// Returns `ArenaFault` or `DataArgumentArity`.
///
/// # Adequacy
/// - hypothesis: L3 — a stream at a type code checks its argument against the
///   universe; one at a bare natural is refused.
/// - witness: `tests::codata::a_stream_is_admitted_and_observed`
/// - witness: `tests::codata::an_ill_typed_codata_argument_is_refused`
#[spec(ensures: |ret| index.0 != 0 || ret.as_ref().map_or(true, |&(_, expected)| expected == classifier))]
pub(super) fn argument(
    arena: &mut TermArena,
    session: &mut SupportContext,
    (codata, classifier): (CompTypeId, ValueTypeId),
    index: ParameterPrefix,
) -> Result<(ValueId, ValueTypeId), KernelError>
{
    let argument = argument_at(arena, codata, index)?;
    let (table, memo) = session.rewrite_parts();
    let mut expected = classifier;
    for position in (0 .. index.0).rev() {
        let earlier = argument_at(arena, codata, ParameterPrefix(position))?;
        let depth = BinderDepth::from(
            u32::try_from(position).map_err(|_cause| KernelError::DataArgumentArity)?,
        );
        let shifted = rewrite::shift_value(arena, table, memo, earlier, BinderDepth::NONE, depth);
        expected = rewrite::substitute_value_type(arena, table, memo, expected, shifted);
    }
    Ok((argument, expected))
}

/// The `index`th argument of a codata application.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the argument at `index` of the codata application `codata`.
/// - fails: a node that is no codata application, or an index past its
///   arguments.
/// - panics: none.
///
/// # Errors
/// Returns `ArenaFault` or `DataArgumentArity`.
///
/// # Adequacy
/// - hypothesis: L3 — a stream's one argument is read at its position, and an
///   ill-typed argument is refused at the position it is read from.
/// - witness: `tests::codata::a_stream_is_admitted_and_observed`
/// - witness: `tests::codata::an_ill_typed_codata_argument_is_refused`
#[spec(ensures: |ret| ret.is_err() || matches!(arena.comp_type(codata), Some(&CompType::Codata { ref arguments, .. }) if arguments.get(index.0) == ret.as_ref().ok()))]
fn argument_at(
    arena: &TermArena,
    codata: CompTypeId,
    index: ParameterPrefix,
) -> Result<ValueId, KernelError>
{
    match arena.comp_type(codata) {
        Some(&CompType::Codata { ref arguments, .. }) => arguments
            .get(index.0)
            .copied()
            .ok_or(KernelError::DataArgumentArity),
        _ => Err(KernelError::ArenaFault),
    }
}

/// A codata application read through its observations.
///
/// # Specification
/// - requires: `codata` is a codata application in `arena`.
/// - ensures: every observation of the named declaration instantiated at the
///   application's arguments, the lazy product of them in declaration order.
/// - provides: the shape an introduction checks against and an elimination
///   reads.
/// - fails: an unreadable or non-codata node, an unresolvable head, an argument
///   count other than the telescope's, or a declaration with no observation.
/// - panics: none.
///
/// # Errors
/// Returns `ArenaFault`, `NotACodataType`, `DataArgumentArity` or
/// `CodataWithoutObservations`.
///
/// # Adequacy
/// - hypothesis: L3 — a stream of naturals reads as `F Nat & Stream Nat`, its
///   head observation instantiated at the argument; a one-observation codata
///   reads as the lazy product of that observation alone.
/// - witness: `tests::codata::a_stream_is_admitted_and_observed`
/// - witness: `tests::codata::a_single_observation_reads_as_a_lazy_product_of_one`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |read| arena.comp_type(*read).is_some()))]
pub(super) fn observed(
    arena: &mut TermArena,
    session: &mut SupportContext,
    judgement: super::Judgement<'_>,
    codata: CompTypeId,
) -> Result<CompTypeId, KernelError>
{
    let Some(&CompType::Codata {
        declaration,
        ref arguments,
    }) = arena.comp_type(codata)
    else {
        return Err(KernelError::ArenaFault);
    };
    let count = arguments.len();
    let signature = resolve(judgement, declaration)?;
    if signature.parameters.len() != count {
        return Err(KernelError::DataArgumentArity);
    }
    let (table, memo) = session.rewrite_parts();
    let mut read = alloc::vec::Vec::with_capacity(signature.observations.len());
    for &observation in signature.observations {
        let mut instantiated = observation;
        for index in (0 .. count).rev() {
            let argument = argument_at(arena, codata, ParameterPrefix(index))?;
            let depth = BinderDepth::from(
                u32::try_from(index).map_err(|_cause| KernelError::DataArgumentArity)?,
            );
            let argument =
                rewrite::shift_value(arena, table, memo, argument, BinderDepth::NONE, depth);
            instantiated =
                rewrite::substitute_comp_type(arena, table, memo, instantiated, argument);
        }
        read.push(instantiated);
    }
    if read.is_empty() {
        return Err(KernelError::CodataWithoutObservations);
    }
    Ok(arena.comp_type_with(&read))
}

/// `shape` read through its observations when it is a codata application,
/// and `shape` itself otherwise.
///
/// # Specification
/// - requires: `shape` is in `arena`.
/// - ensures: [`observed`] of a codata application; any other type unchanged.
/// - provides: the one place a rule reads a codata type's shape.
/// - fails: as [`observed`].
/// - panics: none.
///
/// # Errors
/// As [`observed`].
///
/// # Adequacy
/// - hypothesis: L3 — a stream's pairing checks through its observations and a
///   returner checks unchanged.
/// - witness: `tests::codata::a_stream_is_admitted_and_observed`
#[spec(ensures: |ret| matches!(arena.comp_type(shape), Some(CompType::Codata { .. })) || ret.as_ref() == Ok(&shape))]
pub(super) fn read(
    arena: &mut TermArena,
    session: &mut SupportContext,
    judgement: super::Judgement<'_>,
    shape: CompTypeId,
) -> Result<CompTypeId, KernelError>
{
    if matches!(arena.comp_type(shape), Some(CompType::Codata { .. })) {
        observed(arena, session, judgement, shape)
    }
    else {
        Ok(shape)
    }
}
