//! Native nominal signature formation and capture-free telescope instantiation.

use alloc::sync::Arc;

use anodized::spec;
use gandr_core_term::Binders;
use gandr_core_term::CompTypeId;
use gandr_core_term::ConstructorTag;
use gandr_core_term::DataSignature;
use gandr_core_term::Sort;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_kernel_strata::Level;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::GroundSort;

use crate::CheckRefusal;
use crate::CheckingContext;
use crate::TypeNode;
use crate::formation::form_value_type;
use crate::formation::level_of;

/// Read a data kind's value-universe level.
///
/// # Specification
/// - requires: nothing; malformed kinds are admissible input.
/// - ensures: only a value universe supplies a level.
/// - fails: a named kind refusal for any other former or sort.
/// - panics: none.
///
/// # Errors
/// [`CheckRefusal::DataKindNotUniverse`] names the rejected kind.
///
/// # Adequacy
/// - hypothesis: L3 — both universe sorts and a non-universe separate the rule.
/// - witness: `native_formers::native_formers::data_declarations_and_refusals_agree_with_kernel`
#[spec(ensures: |ret| ret.as_ref().is_ok_and(|level| matches!(context.arena().value_type(kind), Some(ValueType::Universe { sort: Sort::Ground(GroundSort::Value), level: held }) if held == level)) == ret.is_ok())]
pub fn kind_level(
    context: &CheckingContext<'_>,
    kind: ValueTypeId,
) -> Result<Level, CheckRefusal>
{
    match context.arena().value_type(kind) {
        | Some(&ValueType::Universe {
            sort: Sort::Ground(GroundSort::Value),
            ref level,
        }) => Ok(level.clone()),
        | _ => Err(CheckRefusal::DataKindNotUniverse(kind)),
    }
}

/// Check a parameter telescope and every constructor field before admission.
///
/// Fields see the complete parameter telescope, but no constructor fields or
/// self reference. A refused signature leaves no binder or nominal entry.
///
/// # Specification
/// - requires: the nominal entry has not been installed in the context.
/// - ensures: every parameter and field forms in its declared scope; fields fit
///   the declared value universe; the original binder depth is restored.
/// - fails: kind, formation and field-universe refusals are retained.
/// - panics: none.
///
/// # Errors
/// [`CheckRefusal`] identifies the failed formation judgment.
///
/// # Adequacy
/// - hypothesis: L3 — dependent parameters, an invalid field, an excessive
///   field universe and a self reference distinguish the admission premises.
/// - witness: `native_formers::native_formers::data_declarations_and_refusals_agree_with_kernel`
#[spec(captures: depth = context.depth(Zone::Intuitionistic), ensures: context.depth(Zone::Intuitionistic) == depth)]
pub fn form_signature(
    context: &mut CheckingContext<'_>,
    signature: &DataSignature,
) -> Result<(), CheckRefusal>
{
    let depth = context.depth(Zone::Intuitionistic);
    let outcome = (|| {
        let _kind = form_value_type(context, signature.kind())?;
        let level = kind_level(context, signature.kind())?;
        let upper = level
            .succ()
            .map_err(|_cause| CheckRefusal::DataKindNotUniverse(signature.kind()))?;
        for &parameter in signature.parameters() {
            let _formed = form_value_type(context, parameter)?;
            context.binders().open(Zone::Intuitionistic, parameter);
        }
        for &field in signature.constructors().iter().flatten() {
            let _formed = form_value_type(context, field)?;
            if !bool::from(level_of(context, TypeNode::Value(field))?.lt(&upper)) {
                return Err(CheckRefusal::DataFieldLevel {
                    field,
                    kind: signature.kind(),
                });
            }
        }
        Ok(())
    })();
    while context.depth(Zone::Intuitionistic) != depth {
        let _closed = context
            .binders()
            .close(Zone::Intuitionistic)
            .map_err(|_cause| CheckRefusal::MachineInvariant)?;
    }
    outcome
}

/// Resolve the signature and check a nominal application's parameter count.
///
/// # Specification
/// - requires: `datatype` is a native Data node.
/// - ensures: success supplies exactly its admitted signature at matching
///   arity.
/// - fails: absent nominal identities and wrong arity have distinct refusals.
/// - panics: none.
///
/// # Errors
/// [`CheckRefusal::NotADataType`] or [`CheckRefusal::DataArgumentArity`].
///
/// # Adequacy
/// - hypothesis: L3 — equal carriers at distinct positions stay nominal.
/// - witness: `native_formers::native_formers::data_declarations_and_refusals_agree_with_kernel`
#[spec(ensures: |ret| ret.as_ref().is_ok_and(|signature| matches!(context.arena().value_type(datatype), Some(ValueType::Data { declaration, arguments }) if context.data_signatures().get(declaration) == Some(signature) && signature.parameters().len() == arguments.len())) == ret.is_ok())]
pub fn signature(
    context: &mut CheckingContext<'_>,
    datatype: ValueTypeId,
) -> Result<Arc<DataSignature>, CheckRefusal>
{
    let (declaration, count) = match context.arena().value_type(datatype) {
        | Some(&ValueType::Data {
            ref declaration,
            ref arguments,
        }) => (*declaration, arguments.len()),
        | _ => return Err(CheckRefusal::MachineInvariant),
    };
    let signature = context
        .consult_data(declaration)
        .ok_or(CheckRefusal::NotADataType(declaration))?;
    if signature.parameters().len() != count {
        return Err(CheckRefusal::DataArgumentArity(datatype));
    }
    Ok(signature)
}

/// Substitute a prefix of the application's arguments simultaneously.
///
/// # Specification
/// - requires: `subject` is scoped under `prefix` parameters of `datatype`.
/// - ensures: outer arguments retain their ambient indices; zero parameters
///   return the same node without rewriting.
/// - fails: malformed internal application references or an index ceiling.
/// - panics: none.
///
/// # Errors
/// [`CheckRefusal::MachineInvariant`] for an invalid internal application.
///
/// # Adequacy
/// - hypothesis: L3 — two open arguments distinguish reversal and capture.
/// - witness: `native_formers::native_formers::dependent_data_parameters_and_case_motives`
#[spec(ensures: |ret| usize::from(prefix) != 0 || ret == Ok(subject))]
pub fn instantiate(
    context: &mut CheckingContext<'_>,
    datatype: ValueTypeId,
    mut subject: ValueTypeId,
    prefix: gandr_core_term::BinderDepth,
) -> Result<ValueTypeId, CheckRefusal>
{
    for index in (0 .. usize::from(prefix)).rev() {
        let argument = match context.arena().value_type(datatype) {
            | Some(&ValueType::Data { ref arguments, .. }) => arguments
                .get(index)
                .copied()
                .ok_or(CheckRefusal::MachineInvariant)?,
            | _ => return Err(CheckRefusal::MachineInvariant),
        };
        let depth =
            Binders::from(u32::try_from(index).map_err(|_cause| CheckRefusal::MachineInvariant)?);
        let argument = gandr_core_term::shift_value(context.arena_mut(), argument, depth);
        subject = gandr_core_term::instantiate_value_type(context.arena_mut(), subject, argument);
    }
    Ok(subject)
}

/// Form the ordinary branch function's dependent classifier.
///
/// Only the motive has an implicit scrutinee binder. Branches abstract their
/// fields explicitly with ordinary lambdas, in declaration order.
///
/// # Specification
/// - requires: the datatype and motive have formed and `tag` belongs to it.
/// - ensures: the result is a Pi telescope ending in the motive applied to the
///   corresponding constructor, with ambient indices preserved.
/// - fails: a malformed application or an unrepresentable binder count.
/// - panics: none.
///
/// # Errors
/// [`CheckRefusal`] retains the failed nominal lookup or internal scope error.
///
/// # Adequacy
/// - hypothesis: L3 — dependent results and unequal fields separate motive
///   substitution, binder shifting and field order.
/// - witness: `native_formers::native_formers::dependent_data_parameters_and_case_motives`
#[spec(ensures: |ret| ret.as_ref().is_ok_and(|&id| context.arena().comp_type(id).is_some()) == ret.is_ok())]
pub fn branch_type(
    context: &mut CheckingContext<'_>,
    datatype: ValueTypeId,
    tag: ConstructorTag,
    motive: CompTypeId,
) -> Result<CompTypeId, CheckRefusal>
{
    let signature = signature(context, datatype)?;
    let fields = signature
        .constructors()
        .get(usize::from(tag))
        .ok_or(CheckRefusal::MachineInvariant)?;
    let count = u32::try_from(fields.len()).map_err(|_cause| CheckRefusal::MachineInvariant)?;
    let shifted_type =
        gandr_core_term::shift_value_type(context.arena_mut(), datatype, Binders::from(count));
    let values = (0 .. count)
        .rev()
        .map(|index| {
            context
                .arena_mut()
                .value_variable(Zone::Intuitionistic, DeBruijnIndex::from(index))
        })
        .collect();
    let constructor = context
        .arena_mut()
        .value_constructor(shifted_type, tag, values);
    let shifted = gandr_core_term::shift_comp_type_under(
        context.arena_mut(),
        motive,
        Binders::ONE,
        Binders::from(count),
    );
    let mut result =
        gandr_core_term::instantiate_comp_type(context.arena_mut(), shifted, constructor);
    for (index, &field) in fields.iter().enumerate().rev() {
        let domain = instantiate(
            context,
            datatype,
            field,
            gandr_core_term::BinderDepth::from(signature.parameters().len()),
        )?;
        let depth =
            Binders::from(u32::try_from(index).map_err(|_cause| CheckRefusal::MachineInvariant)?);
        let domain = gandr_core_term::shift_value_type(context.arena_mut(), domain, depth);
        result = context.arena_mut().comp_type_pi(domain, result);
    }
    Ok(result)
}
