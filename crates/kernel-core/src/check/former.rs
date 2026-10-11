//! Native nominal signatures, capture-avoiding instantiation and case motives.

use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_strata::Level;
use gandr_kernel_term::CompTypeId;
use gandr_kernel_term::Computation;
use gandr_kernel_term::ComputationId;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::ConstructorTag;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::DeclarationContent;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::Value;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueType;
use gandr_kernel_term::ValueTypeId;

use super::Goal;
use crate::env::AdmittedDeclaration;
use crate::error::ExpectedValueShape;
use crate::error::KernelError;
use crate::rewrite;
use crate::rewrite::BinderDepth;
use crate::support::SupportContext;

/// How many leading nominal parameters a simultaneous substitution consumes.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(super) struct ParameterPrefix(
    /// The number of supplied parameters, without narrowing the arena count.
    pub usize,
);

/// A declaration's borrowed constructor table and telescope.
pub(super) struct Signature<'signature>
{
    /// Classifiers scoped under their preceding parameters.
    pub parameters: &'signature [ValueTypeId],
    /// Field types scoped under the entire parameter telescope.
    pub constructors: &'signature [Vec<ValueTypeId>],
    /// The positive universe bounding the fields.
    pub kind: ValueTypeId,
}

/// Resolve a nominal identity without unfolding its carrier.
///
/// # Specification
/// - requires: entries is the immutable admitted prefix.
/// - ensures: success borrows exactly the named data signature.
/// - fails: a non-data or unadmitted position is refused.
/// - panics: none.
///
/// # Errors
/// Returns `NotADataType` for a position that does not name data.
///
/// # Adequacy
/// - hypothesis: L3 — distinct declarations remain distinct even with equal
///   fields.
/// - witness: `native_formers::native_formers::nominal_identity_and_constructor_refusals`
#[spec(ensures: |ret| ret.is_ok() == matches!(entries.get(usize::from(index)).map(AdmittedDeclaration::content), Some(DeclarationContent::Data { .. })))]
pub(super) fn signature(
    entries: &[AdmittedDeclaration],
    index: ConstantIndex,
) -> Result<Signature<'_>, KernelError>
{
    match entries
        .get(usize::from(index))
        .map(AdmittedDeclaration::content)
    {
        | Some(&DeclarationContent::Data {
            ref parameters,
            ref constructors,
            ref kind,
        }) => Ok(Signature {
            parameters,
            constructors,
            kind: *kind,
        }),
        | _ => Err(KernelError::NotADataType { index }),
    }
}

/// Read a checked signature's positive universe level.
///
/// # Specification
/// - requires: nothing.
/// - ensures: success preserves the positive universe's exact level.
/// - fails: missing arena nodes or a non-positive-universe kind.
/// - panics: none.
///
/// # Errors
/// Returns `ArenaFault` or `DataKindNotUniverse`.
///
/// # Adequacy
/// - hypothesis: L3 — a forged kind cannot establish a data formation
///   judgement.
/// - witness: `native_formers::native_formers::data_signature_formation_checks_fields_and_parameters`
#[spec(ensures: |ret| ret.is_ok() == matches!(arena.value_type(kind), Some(ValueType::Universe { sort: GroundSort::Value, .. })))]
pub(super) fn level(
    arena: &TermArena,
    kind: ValueTypeId,
) -> Result<Level, KernelError>
{
    match arena.value_type(kind).ok_or(KernelError::ArenaFault)? {
        | &ValueType::Universe {
            sort: GroundSort::Value,
            ref level,
        } => Ok(level.clone()),
        | _ => Err(KernelError::DataKindNotUniverse),
    }
}

/// Instantiate a declaration telescope simultaneously with ambient arguments.
///
/// # Specification
/// - requires: the subject is scoped under exactly the supplied parameters.
/// - ensures: replacements retain their ambient scope; parameter binders
///   disappear.
/// - fails: a telescope exceeding the representable binder space.
/// - panics: none.
/// The empty-substitution postcondition is executable; capture avoidance is
/// observed by the dependent witness rather than a second rewrite engine.
///
/// # Errors
/// Returns `DataArgumentArity` for an unrepresentable telescope.
///
/// # Adequacy
/// - hypothesis: L3 — two dependent parameters distinguish reversal and
///   capture.
/// - witness: `native_formers::native_formers::data_parameters_preserve_open_indices`
#[spec(ensures: |ret| prefix.0 != 0 || ret.as_ref() == Ok(&subject))]
pub(super) fn instantiate(
    arena: &mut TermArena,
    session: &mut SupportContext,
    subject: ValueTypeId,
    datatype: ValueTypeId,
    prefix: ParameterPrefix,
) -> Result<ValueTypeId, KernelError>
{
    let (table, memo) = session.rewrite_parts();
    let mut result = subject;
    for index in (0 .. prefix.0).rev() {
        let argument = match arena.value_type(datatype) {
            | Some(&ValueType::Data { ref arguments, .. }) => arguments
                .get(index)
                .copied()
                .ok_or(KernelError::DataArgumentArity)?,
            | _ => return Err(KernelError::ArenaFault),
        };
        let depth = BinderDepth::from(
            u32::try_from(index).map_err(|_cause| KernelError::DataArgumentArity)?,
        );
        let argument = rewrite::shift_value(arena, table, memo, argument, BinderDepth::NONE, depth);
        result = rewrite::substitute_value_type(arena, table, memo, result, argument);
    }
    Ok(result)
}

/// Construct field-checking goals for one explicit constructor.
///
/// # Specification
/// - requires: the value id belongs to the current arena.
/// - ensures: every supplied field checks against its declaration-instantiated
///   type.
/// - fails: non-data classifiers, unknown tags, wrong argument or field
///   arities.
/// - panics: none.
/// Returned goals are executable field-check obligations, not synthesized
/// claims.
///
/// # Errors
/// Returns a native former refusal or an arena fault.
///
/// # Adequacy
/// - hypothesis: L3 — equal carriers do not erase identity, arity or payload
///   typing.
/// - witness: `native_formers::native_formers::nominal_identity_and_constructor_refusals`
#[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|result| result.1.iter().all(|goal| matches!(goal, &Goal::CheckValue(..)))))]
pub(super) fn constructor(
    arena: &mut TermArena,
    entries: &[AdmittedDeclaration],
    session: &mut SupportContext,
    value: ValueId,
) -> Result<(ValueTypeId, Vec<Goal>), KernelError>
{
    let (datatype, tag, count) = match arena.value(value).ok_or(KernelError::ArenaFault)? {
        | &Value::Constructor {
            ref datatype,
            ref tag,
            ref fields,
        } => (*datatype, *tag, fields.len()),
        | _ => return Err(KernelError::ArenaFault),
    };
    let (declaration, argument_count) =
        match arena.value_type(datatype).ok_or(KernelError::ArenaFault)? {
            | &ValueType::Data {
                ref declaration,
                ref arguments,
            } => (*declaration, arguments.len()),
            | _ => {
                return Err(super::value_shape_mismatch(
                    arena,
                    ExpectedValueShape::Data,
                    datatype,
                ));
            },
        };
    let signature = signature(entries, declaration)?;
    if signature.parameters.len() != argument_count {
        return Err(KernelError::DataArgumentArity);
    }
    let expected = signature
        .constructors
        .get(usize::from(tag))
        .ok_or(KernelError::UnknownConstructor { tag })?;
    if count != expected.len() {
        return Err(KernelError::ConstructorArity);
    }
    let mut goals = Vec::with_capacity(count);
    for (index, &ty) in expected.iter().enumerate() {
        let ty = instantiate(
            arena,
            session,
            ty,
            datatype,
            ParameterPrefix(argument_count),
        )?;
        let field = match arena.value(value) {
            | Some(&Value::Constructor { ref fields, .. }) => {
                fields.get(index).copied().ok_or(KernelError::ArenaFault)?
            },
            | _ => return Err(KernelError::ArenaFault),
        };
        goals.push(Goal::CheckValue(field, ty));
    }
    Ok((datatype, goals))
}

/// Build one branch classifier by substituting its constructor into the motive.
///
/// Branches are ordinary functions over their constructor fields. The motive
/// alone has an implicit binder; syntax walkers need no declaration lookup.
///
/// # Specification
/// - requires: field types are scoped under the declaration parameter
///   telescope.
/// - ensures: the result binds fields in declaration order and checks the
///   motive at the corresponding constructor, not merely at the original
///   scrutinee.
/// - fails: field count exceeds the representable binder space.
/// - panics: none.
/// The executable postcondition requires a live computation classifier.
///
/// # Errors
/// Returns `ConstructorArity` when the telescope cannot be represented.
///
/// # Adequacy
/// - hypothesis: L3 — a dependent motive rejects a branch at a wrong index.
/// - witness: `native_formers::native_formers::data_case_checks_coverage_and_motive`
#[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|id| arena.comp_type(*id).is_some()))]
pub(super) fn branch_type(
    arena: &mut TermArena,
    session: &mut SupportContext,
    datatype: ValueTypeId,
    tag: ConstructorTag,
    fields: &[ValueTypeId],
    motive: CompTypeId,
) -> Result<CompTypeId, KernelError>
{
    let count = u32::try_from(fields.len()).map_err(|_cause| KernelError::ConstructorArity)?;
    let parameters = match arena.value_type(datatype) {
        | Some(&ValueType::Data { ref arguments, .. }) => arguments.len(),
        | _ => return Err(KernelError::ArenaFault),
    };
    let (table, memo) = session.rewrite_parts();
    let shifted_datatype = rewrite::shift_value_type(
        arena,
        table,
        memo,
        datatype,
        BinderDepth::NONE,
        BinderDepth::from(count),
    );
    let values = (0 .. count)
        .rev()
        .map(|index| arena.value_variable(DeBruijnIndex::from(index)))
        .collect();
    let constructor = arena.value_constructor(shifted_datatype, tag, values);
    let shifted = rewrite::shift_comp_type(
        arena,
        table,
        memo,
        motive,
        BinderDepth::from(1_u32),
        BinderDepth::from(count),
    );
    let mut result = rewrite::substitute_comp_type(arena, table, memo, shifted, constructor);
    for (index, &field) in fields.iter().enumerate().rev() {
        let field = instantiate(arena, session, field, datatype, ParameterPrefix(parameters))?;
        let depth = BinderDepth::from(
            u32::try_from(index).map_err(|_cause| KernelError::ConstructorArity)?,
        );
        let (table, memo) = session.rewrite_parts();
        let domain = rewrite::shift_value_type(arena, table, memo, field, BinderDepth::NONE, depth);
        result = arena.comp_type_pi(domain, result);
    }
    Ok(result)
}

/// Collect the constructor-specific branch obligations and instantiated result.
///
/// # Specification
/// - requires: the scrutinee has the supplied data classifier; motive formation
///   is checked by the surrounding judgement.
/// - ensures: exactly one branch obligation per constructor, in table order.
/// - fails: wrong shape or a non-exhaustive branch vector.
/// - panics: none.
/// The executable postcondition classifies every returned computation check.
///
/// # Errors
/// Returns native shape, coverage, instantiation or arena refusals.
///
/// # Adequacy
/// - hypothesis: L3 — omitted and surplus arms both refuse before branch
///   checking.
/// - witness: `native_formers::native_formers::data_case_checks_coverage_and_motive`
#[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|result| result.1.iter().all(|goal| matches!(goal, &Goal::CheckComp(..)))))]
pub(super) fn case(
    arena: &mut TermArena,
    entries: &[AdmittedDeclaration],
    session: &mut SupportContext,
    case: ComputationId,
    datatype: ValueTypeId,
) -> Result<(CompTypeId, Vec<Goal>), KernelError>
{
    let (scrutinee, motive, count) = match arena.computation(case).ok_or(KernelError::ArenaFault)? {
        | &Computation::DataCase {
            ref scrutinee,
            ref motive,
            ref branches,
        } => (*scrutinee, *motive, branches.len()),
        | _ => return Err(KernelError::ArenaFault),
    };
    let (declaration, argument_count) =
        match arena.value_type(datatype).ok_or(KernelError::ArenaFault)? {
            | &ValueType::Data {
                ref declaration,
                ref arguments,
            } => (*declaration, arguments.len()),
            | _ => {
                return Err(super::value_shape_mismatch(
                    arena,
                    ExpectedValueShape::Data,
                    datatype,
                ));
            },
        };
    let signature = signature(entries, declaration)?;
    if signature.parameters.len() != argument_count {
        return Err(KernelError::DataArgumentArity);
    }
    if signature.constructors.len() != count {
        return Err(KernelError::NonExhaustiveDataCase);
    }
    let mut goals = Vec::with_capacity(count);
    for (index, fields) in signature.constructors.iter().enumerate() {
        let expected = branch_type(
            arena,
            session,
            datatype,
            ConstructorTag::from(index),
            fields,
            motive,
        )?;
        let branch = match arena.computation(case) {
            | Some(&Computation::DataCase { ref branches, .. }) => branches
                .get(index)
                .copied()
                .ok_or(KernelError::ArenaFault)?,
            | _ => return Err(KernelError::ArenaFault),
        };
        goals.push(Goal::CheckComp(branch, expected));
    }
    let (table, memo) = session.rewrite_parts();
    let result = rewrite::substitute_comp_type(arena, table, memo, motive, scrutinee);
    Ok((result, goals))
}

/// Check directional record inclusion without changing definitional equality.
///
/// # Specification
/// - requires: both types have already formed in the current context.
/// - ensures: each expected record label exists and its type accepts the actual
///   field type recursively; non-record leaves remain definitionally invariant.
/// - fails: a missing label or a non-convertible leaf.
/// - panics: none.
///
/// # Errors
/// Returns the value-type mismatch at the first separating pair.
///
/// # Adequacy
/// - hypothesis: L3 — a variable carrying a wider nested record can be returned
///   at a narrower type, but reversal and a mismatched nested field cannot.
/// - witness: `native_formers::native_formers::record_width_depth_projection_and_absent_fields`
#[spec(ensures: |ret| ret.is_err() || { let (matched_left_value, matched_right_value) = (arena.value_type(expected),arena.value_type(actual));
if let Some(matched_left_node) = matched_left_value && let ValueType::Record(ref wanted) = *matched_left_node && let Some(matched_right_node) = matched_right_value && let ValueType::Record(ref found) = *matched_right_node { wanted.keys().all(|label| found.contains_key(label)) }
 else { crate::conv::convertible_value_types(arena,expected,actual) == crate::conv::Convertibility::Convertible }
})]
pub(super) fn assignable(
    arena: &TermArena,
    expected: ValueTypeId,
    actual: ValueTypeId,
) -> Result<(), KernelError>
{
    if !matches!(
        (arena.value_type(expected), arena.value_type(actual)),
        (Some(ValueType::Record(_)), Some(ValueType::Record(_)))
    ) {
        return crate::conv::convert_value_type(arena, expected, actual);
    }
    let mut work = alloc::vec![(expected, actual)];
    let mut seen = alloc::collections::BTreeSet::new();
    while let Some((wanted, found)) = work.pop() {
        if !seen.insert((wanted, found)) {
            continue;
        }
        {
            let (matched_left_value, matched_right_value) =
                (arena.value_type(wanted), arena.value_type(found));
            if let Some(matched_left_node) = matched_left_value
                && let ValueType::Record(ref expected_fields) = *matched_left_node
                && let Some(matched_right_node) = matched_right_value
                && let ValueType::Record(ref actual_fields) = *matched_right_node
            {
                {
                    for (label, &expected_field) in expected_fields {
                        let Some(&actual_field) = actual_fields.get(label)
                        else {
                            return crate::conv::convert_value_type(arena, wanted, found);
                        };
                        work.push((expected_field, actual_field));
                    }
                }
            }
            else {
                crate::conv::convert_value_type(arena, wanted, found)?;
            }
        }
    }
    Ok(())
}
