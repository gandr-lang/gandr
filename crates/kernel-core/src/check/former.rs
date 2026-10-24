//! Native nominal signatures, capture-avoiding instantiation and case motives.
//!
//! Data admission forms each parameter beneath its predecessors, then every
//! constructor field beneath all parameters, and checks their universe bound.
//! Only the already admitted prefix and the declaration's own family are
//! visible; the sibling `occurrence` module states when a self occurrence is
//! admitted. The declaration's identity is generative and cannot synthesize as
//! an ordinary value constant.
//!
//! A nominal application checks its argument telescope. A constructor must
//! name that application, a declared tag and exactly its declared fields.
//! Data elimination checks a motive under one scrutinee binder and exact
//! constructor coverage; each ambient branch is checked as a function of its
//! constructor fields returning the instantiated motive. Empty data admits an
//! empty branch list without inventing a constructor or losing the surrounding
//! context.
//!
//! Records admit directional width and recursive depth assignment. Conversion
//! still requires the same labels. Projection checks the record and reports a
//! missing field rather than selecting by position. Nominal argument
//! conversion is invariant structural value equality; it performs no beta,
//! delta or eta search. The frontend observes this same boundary.
//!
//! **Choice.** Ordinary checked declarations and native term nodes, rather
//! than opaque axioms or an encoding that loses nominal identity.
//! **Reversal.** Variance annotations and definitional index conversion need
//! explicit formation or replay rules. The seven `native_formers` integration
//! witnesses cover admission, refusals, dependent arguments and motives,
//! record assignment and canonical artifact reconstruction.

use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_strata::Level;
use gandr_kernel_term::Apartness;
use gandr_kernel_term::CompTypeId;
use gandr_kernel_term::Computation;
use gandr_kernel_term::ComputationId;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::ConstructorTag;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::DeclarationContent;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::StageId;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::Value;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueType;
use gandr_kernel_term::ValueTypeId;
use quenchant_shape::shape::Maybe;

use super::Goal;
use crate::env::AdmittedDeclaration;
use crate::env::Entries;
use crate::error::ExpectedValueShape;
use crate::error::KernelError;
use crate::presented;
use crate::presented::Presentations;
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

/// How many arguments an application of a family takes: its parameters, then
/// its indices.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(super) struct FamilyArity(
    /// The number of arguments.
    pub usize,
);

/// A declaration's borrowed constructor table and telescope.
#[derive(Clone, Copy, Debug)]
pub(super) struct Signature<'signature>
{
    /// Classifiers scoped under their preceding parameters.
    pub parameters: &'signature [ValueTypeId],
    /// Index classifiers scoped under the parameters and the indices before
    /// them; empty for a family indexed by nothing.
    pub indices: &'signature [ValueTypeId],
    /// Field types scoped under the entire parameter telescope, then the
    /// fields before them in their constructor.
    pub constructors: &'signature [Vec<ValueTypeId>],
    /// Each constructor's result index, scoped under the parameters and its
    /// fields; empty when `indices` is.
    pub results: &'signature [Vec<ValueId>],
    /// The positive universe bounding the fields.
    pub kind: ValueTypeId,
}

impl Signature<'_>
{
    /// The arguments an application of the family takes: its parameters, then
    /// its indices.
    ///
    /// # Specification
    /// trivial.
    pub(super) const fn arity(&self) -> FamilyArity
    {
        FamilyArity(self.parameters.len().saturating_add(self.indices.len()))
    }
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
/// - witness: `tests::native_formers::nominal_identity_and_constructor_refusals`
#[spec(ensures: |ret| ret.is_ok() == matches!(entries.get(usize::from(index)).map(AdmittedDeclaration::content), Some(DeclarationContent::Data { .. })))]
pub(super) fn signature(
    entries: &Entries,
    index: ConstantIndex,
) -> Result<Signature<'_>, KernelError>
{
    match entries
        .get(usize::from(index))
        .map(AdmittedDeclaration::content)
    {
        Some(&DeclarationContent::Data {
            ref parameters,
            ref indices,
            ref constructors,
            ref results,
            ref kind,
        }) => Ok(Signature {
            parameters,
            indices,
            constructors,
            results,
            kind: *kind,
        }),
        _ => Err(KernelError::NotADataType { index }),
    }
}

/// Resolve a nominal head through the block being admitted, then the
/// admitted prefix.
///
/// # Specification
/// - requires: entries is the immutable admitted prefix.
/// - ensures: a head naming the block's own position borrows the block's
///   signature, and one naming a family of the mutual block whose families form
///   borrows that family's; any other head resolves as [`signature`] does.
/// - provides: self reference inside one block — a family is in scope at its
///   own position while the block's families form, and nowhere else.
/// - fails: a non-data or unadmitted position outside the block.
/// - panics: none.
///
/// # Errors
/// Returns `NotADataType` for a position that names neither the block nor
/// admitted data.
///
/// # Adequacy
/// - hypothesis: L3 — `Nat`'s `succ` field and `List A`'s `cons` tail form
///   through the block; the same head in a definition after admission resolves
///   through the prefix; a universe's family resolves in its mutual block.
/// - witness: `tests::recursive_data::recursive_blocks_are_admitted`
/// - witness: `tests::recursive_data::a_mutual_block_is_admitted`
#[spec(ensures: |ret| ret.is_ok() == (matches!(judgement.block, super::Block::Inside { position, .. } if position == index)
    || matches!(judgement.member(index), Maybe::Present((member, super::occurrence::Membership::Family)) if matches!(member.content(), DeclarationContent::Data { .. }))
    || matches!(judgement.entries.get(usize::from(index)).map(AdmittedDeclaration::content), Some(DeclarationContent::Data { .. }))))]
pub(super) fn resolve<'session>(
    judgement: super::Judgement<'session>,
    index: ConstantIndex,
) -> Result<Signature<'session>, KernelError>
{
    match judgement.block {
        super::Block::Inside {
            position,
            signature: own,
        } if position == index => Ok(own),
        super::Block::Mutual { .. } => match judgement.member(index) {
            Maybe::Present((member, super::occurrence::Membership::Family)) => {
                match *member.content() {
                    DeclarationContent::Data {
                        ref parameters,
                        ref indices,
                        ref constructors,
                        ref results,
                        kind,
                    } => Ok(Signature {
                        parameters,
                        indices,
                        constructors,
                        results,
                        kind,
                    }),
                    DeclarationContent::Codata { .. }
                    | DeclarationContent::Def { .. }
                    | DeclarationContent::Axiom { .. }
                    | DeclarationContent::AbstractType { .. } => {
                        Err(KernelError::NotADataType { index })
                    },
                }
            },
            Maybe::Present((
                _,
                super::occurrence::Membership::Definition | super::occurrence::Membership::Other,
            ))
            | Maybe::Absent(_) => signature(judgement.entries, index),
        },
        super::Block::Inside { .. } | super::Block::Codata { .. } | super::Block::Outside => {
            signature(judgement.entries, index)
        },
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
/// - witness: `tests::native_formers::data_signature_formation_checks_fields_and_parameters`
#[spec(ensures: |ret| ret.is_ok() == matches!(arena.value_type(kind), Some(ValueType::Universe { sort: GroundSort::Value, .. })))]
pub(super) fn level(
    arena: &TermArena,
    kind: ValueTypeId,
) -> Result<Level, KernelError>
{
    match arena.value_type(kind).ok_or(KernelError::ArenaFault)? {
        &ValueType::Universe {
            sort: GroundSort::Value,
            ref level,
        } => Ok(level.clone()),
        &ValueType::Data { .. }
        | &ValueType::Record(_)
        | &ValueType::Session { .. }
        | &ValueType::PathUniverse(..)
        | &ValueType::FlowUniverse(..)
        | &ValueType::Path { .. }
        | &ValueType::Flow { .. }
        | &ValueType::Bridge { .. }
        | &ValueType::Base(_)
        | &ValueType::Product(_)
        | &ValueType::Sigma { .. }
        | &ValueType::Sum(_)
        | &ValueType::List(_)
        | &ValueType::Thunk(_)
        | &ValueType::Universe { .. }
        | &ValueType::Lift { .. }
        | &ValueType::Element { .. }
        | &ValueType::Abstract(_)
        | &ValueType::StaticPi { .. }
        | &ValueType::Staged { .. } => Err(KernelError::DataKindNotUniverse),
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
/// - witness: `tests::native_formers::data_parameters_preserve_open_indices`
#[spec(ensures: |ret| prefix.0 != 0 || ret.as_ref() == Ok(&subject))]
pub(super) fn instantiate(
    arena: &mut TermArena,
    session: &mut SupportContext,
    subject: ValueTypeId,
    datatype: ValueTypeId,
    prefix: ParameterPrefix,
) -> Result<ValueTypeId, KernelError>
{
    field_type(
        arena,
        session,
        (subject, datatype),
        prefix,
        BinderDepth::NONE,
    )
}

/// The classifier a constructor's result index at `position` checks against:
/// the index classifier carried past the constructor's `fields` binders, the
/// indices before it replaced by the results the constructor states for them.
///
/// # Specification
/// - requires: `index` is scoped under the parameters and the `position`
///   indices before it; `stated` under the parameters and the `fields` binders
///   of the constructor.
/// - ensures: the classifier scoped under the parameters and those binders; at
///   position zero, `index` carried past the fields alone.
/// - fails: a telescope exceeding the representable binder space.
/// - panics: none.
///
/// # Errors
/// Returns `ConstructorArity` for an unrepresentable telescope, and
/// `IndexedSignature` for a position past the stated results.
///
/// # Adequacy
/// - hypothesis: L3 — `Cons`'s `S(n)` checks at `Nat` past its three fields.
/// - witness: `tests::native_formers::an_indexed_family_states_its_result_indices`
#[spec(ensures: |ret| ret.is_err() || usize::from(position) <= stated.len())]
pub(super) fn index_at(
    arena: &mut TermArena,
    session: &mut SupportContext,
    index: ValueTypeId,
    (stated, position): (&[ValueId], BinderDepth),
    fields: BinderDepth,
) -> Result<ValueTypeId, KernelError>
{
    let (table, memo) = session.rewrite_parts();
    let mut result = rewrite::shift_value_type(arena, table, memo, index, position, fields);
    for before in (0 .. usize::from(position)).rev() {
        let value = stated
            .get(before)
            .copied()
            .ok_or(KernelError::IndexedSignature)?;
        let depth = BinderDepth::from(
            u32::try_from(before).map_err(|_cause| KernelError::ConstructorArity)?,
        );
        let value = rewrite::shift_value(arena, table, memo, value, BinderDepth::NONE, depth);
        result = rewrite::substitute_value_type(arena, table, memo, result, value);
    }
    Ok(result)
}

/// A constructor field's type at a nominal application: the parameters
/// instantiated beneath the `earlier` field binders the field stands under.
///
/// # Specification
/// - requires: the subject is scoped under the supplied parameters, then
///   `earlier` binders: the constructor's fields before it.
/// - ensures: the same type under the ambient context and those binders, each
///   parameter replaced by its argument carried under them; zero parameters
///   return the subject.
/// - fails: a telescope exceeding the representable binder space.
/// - panics: none.
///
/// # Errors
/// Returns `DataArgumentArity` for an unrepresentable telescope.
///
/// # Adequacy
/// - hypothesis: L3 — a list's tail reads its element parameter past the head's
///   binder, and a dependent field keeps the binder it names.
/// - witness: `tests::recursive_data::dependent_fields_are_admitted`
#[spec(ensures: |ret| prefix.0 != 0 || ret.as_ref() == Ok(&subject))]
pub(super) fn field_type(
    arena: &mut TermArena,
    session: &mut SupportContext,
    (subject, datatype): (ValueTypeId, ValueTypeId),
    prefix: ParameterPrefix,
    earlier: BinderDepth,
) -> Result<ValueTypeId, KernelError>
{
    let (table, memo) = session.rewrite_parts();
    let mut result = subject;
    for index in (0 .. prefix.0).rev() {
        let argument = match arena.value_type(datatype) {
            Some(&ValueType::Data { ref arguments, .. }) => arguments
                .get(index)
                .copied()
                .ok_or(KernelError::DataArgumentArity)?,
            _ => return Err(KernelError::ArenaFault),
        };
        let depth = BinderDepth::from(
            u32::try_from(index).map_err(|_cause| KernelError::DataArgumentArity)?,
        );
        let argument = rewrite::shift_value(arena, table, memo, argument, BinderDepth::NONE, depth);
        result = rewrite::substitute_value_type_at(arena, table, memo, (result, argument), earlier);
    }
    Ok(result)
}

/// Construct field-checking goals for one explicit constructor.
///
/// # Specification
/// - requires: the value id belongs to the current arena.
/// - ensures: every supplied field checks against its declaration-instantiated
///   type, the fields before it in the constructor substituted by the values
///   the constructor gives them; an indexed family's constructor stands at the
///   index its classifier names, each stated result index instantiated at the
///   parameters and the fields α-equal to the classifier's index argument.
/// - fails: non-data classifiers, unknown tags, wrong argument or field
///   arities, and a classifier at another index than the constructor states.
/// - panics: none.
/// Returned goals are executable field-check obligations, not synthesized
/// claims.
///
/// # Errors
/// Returns a native former refusal, `ConstructorIndex` for a classifier at
/// another index, or an arena fault.
///
/// # Adequacy
/// - hypothesis: L3 — equal carriers do not erase identity, arity or payload
///   typing, and a field naming the code before it checks at that code's
///   decode; a vector's empty and cons constructors stand at their own lengths
///   and are refused at another.
/// - witness: `tests::native_formers::nominal_identity_and_constructor_refusals`
/// - witness: `tests::recursive_data::dependent_fields_are_admitted`
/// - witness: `tests::native_formers::an_indexed_constructor_stands_at_its_stated_index`
#[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|result| result.1.iter().all(|goal| matches!(goal, &Goal::CheckValue(..)))))]
pub(super) fn constructor(
    arena: &mut TermArena,
    entries: &Entries,
    session: &mut SupportContext,
    value: ValueId,
) -> Result<(ValueTypeId, Vec<Goal>), KernelError>
{
    let (datatype, tag, count) = match arena.value(value).ok_or(KernelError::ArenaFault)? {
        &Value::Constructor {
            ref datatype,
            ref tag,
            ref fields,
        } => (*datatype, *tag, fields.len()),
        &Value::Record(_)
        | &Value::SessionPath { .. }
        | &Value::SessionFlow { .. }
        | &Value::Stay { .. }
        | &Value::ForwardFlow { .. }
        | &Value::FunctionFlow { .. }
        | &Value::Then { .. }
        | &Value::FlowProduct(..)
        | &Value::PathRefl(_)
        | &Value::PathProduct(..)
        | &Value::PathEquiv { .. }
        | &Value::Univalence { .. }
        | &Value::Here { .. }
        | &Value::Returned(_)
        | &Value::Higher { .. }
        | &Value::HigherEvaluation { .. }
        | &Value::QuantifiedEvaluation { .. }
        | &Value::Variable(_)
        | &Value::Constant(_)
        | &Value::Literal(_)
        | &Value::Tuple(_)
        | &Value::Injection(..)
        | &Value::ListNil
        | &Value::ListCons(..)
        | &Value::Thunk(_)
        | &Value::Lift { .. }
        | &Value::Quote(_)
        | &Value::QuoteComputation(_)
        | &Value::StaticApplication(..) => return Err(KernelError::ArenaFault),
    };
    let (declaration, argument_count) =
        match arena.value_type(datatype).ok_or(KernelError::ArenaFault)? {
            &ValueType::Data {
                ref declaration,
                ref arguments,
            } => (*declaration, arguments.len()),
            &ValueType::Record(_)
            | &ValueType::Session { .. }
            | &ValueType::PathUniverse(..)
            | &ValueType::FlowUniverse(..)
            | &ValueType::Path { .. }
            | &ValueType::Flow { .. }
            | &ValueType::Bridge { .. }
            | &ValueType::Base(_)
            | &ValueType::Product(_)
            | &ValueType::Sigma { .. }
            | &ValueType::Sum(_)
            | &ValueType::List(_)
            | &ValueType::Thunk(_)
            | &ValueType::Universe { .. }
            | &ValueType::Lift { .. }
            | &ValueType::Element { .. }
            | &ValueType::Abstract(_)
            | &ValueType::StaticPi { .. }
            | &ValueType::Staged { .. } => {
                return Err(super::value_shape_mismatch(
                    arena,
                    ExpectedValueShape::Data,
                    datatype,
                ));
            },
        };
    let signature = signature(entries, declaration)?;
    if signature.arity() != FamilyArity(argument_count) {
        return Err(KernelError::DataArgumentArity);
    }
    let parameters = ParameterPrefix(signature.parameters.len());
    let expected = signature
        .constructors
        .get(usize::from(tag))
        .ok_or(KernelError::UnknownConstructor { tag })?;
    if count != expected.len() {
        return Err(KernelError::ConstructorArity);
    }
    let mut goals = Vec::with_capacity(count);
    for (index, &ty) in expected.iter().enumerate() {
        let earlier = BinderDepth::from(
            u32::try_from(index).map_err(|_cause| KernelError::ConstructorArity)?,
        );
        let mut ty = field_type(arena, session, (ty, datatype), parameters, earlier)?;
        // The fields before it stand at the values the constructor gives
        // them, the innermost first.
        for before in (0 .. index).rev() {
            let value = match arena.value(value) {
                Some(&Value::Constructor { ref fields, .. }) => {
                    fields.get(before).copied().ok_or(KernelError::ArenaFault)?
                },
                _ => return Err(KernelError::ArenaFault),
            };
            let depth = BinderDepth::from(
                u32::try_from(before).map_err(|_cause| KernelError::ConstructorArity)?,
            );
            let (table, memo) = session.rewrite_parts();
            let value = rewrite::shift_value(arena, table, memo, value, BinderDepth::NONE, depth);
            ty = rewrite::substitute_value_type(arena, table, memo, ty, value);
        }
        let field = match arena.value(value) {
            Some(&Value::Constructor { ref fields, .. }) => {
                fields.get(index).copied().ok_or(KernelError::ArenaFault)?
            },
            _ => return Err(KernelError::ArenaFault),
        };
        goals.push(Goal::CheckValue(field, ty));
    }
    if let Some(stated) = signature.results.get(usize::from(tag)) {
        for (position, &stated) in stated.iter().enumerate() {
            let stated = result_index(arena, session, (stated, datatype, value), parameters)?;
            let argument = match arena.value_type(datatype) {
                Some(&ValueType::Data { ref arguments, .. }) => parameters
                    .0
                    .checked_add(position)
                    .and_then(|at| arguments.get(at))
                    .copied()
                    .ok_or(KernelError::DataArgumentArity)?,
                _ => return Err(KernelError::ArenaFault),
            };
            if crate::conv::equal_values(arena, stated, argument)
                != crate::conv::Convertibility::Convertible
            {
                return Err(KernelError::ConstructorIndex { tag });
            }
        }
    }
    Ok((datatype, goals))
}

/// A constructor's stated result index with the family's parameters
/// instantiated beneath its `fields` binders, which it keeps.
///
/// # Specification
/// - requires: `stated` is scoped under the family's `parameters`, then the
///   constructor's `fields` binders; `datatype` is the family's application.
/// - ensures: the same value under the ambient context and the `fields`
///   binders, each parameter replaced by its argument carried under them.
/// - fails: a parameter telescope longer than the application's arguments, or
///   one exceeding the representable binder space.
/// - panics: none.
///
/// # Errors
/// Returns `DataArgumentArity` for an unrepresentable parameter telescope.
///
/// # Adequacy
/// - hypothesis: L3 — `Cons`'s `S(n)` keeps its length field while its element
///   parameter is instantiated.
/// - witness: `tests::native_formers::an_indexed_constructor_stands_at_its_stated_index`
#[spec(ensures: |ret| (parameters.0 != 0 || ret == Ok(stated))
    && ret.as_ref().map_or(true, |id| arena.value(*id).is_some() || arena.value(stated).is_none()))]
fn stated_beneath(
    arena: &mut TermArena,
    session: &mut SupportContext,
    (stated, datatype): (ValueId, ValueTypeId),
    parameters: ParameterPrefix,
    fields: BinderDepth,
) -> Result<ValueId, KernelError>
{
    let (table, memo) = session.rewrite_parts();
    let mut result = stated;
    for index in (0 .. parameters.0).rev() {
        let argument = match arena.value_type(datatype) {
            Some(&ValueType::Data { ref arguments, .. }) => arguments
                .get(index)
                .copied()
                .ok_or(KernelError::DataArgumentArity)?,
            _ => return Err(KernelError::ArenaFault),
        };
        let depth = BinderDepth::from(
            u32::try_from(index).map_err(|_cause| KernelError::DataArgumentArity)?,
        );
        let argument = rewrite::shift_value(arena, table, memo, argument, BinderDepth::NONE, depth);
        result = rewrite::substitute_value_at(arena, table, memo, (result, argument), fields);
    }
    Ok(result)
}

/// A constructor's stated result index at its application: the parameters
/// instantiated beneath its field binders, then each field at the value the
/// constructor gives it.
///
/// # Specification
/// - requires: `stated` is scoped under the family's `parameters`, then the
///   constructor's fields; `value` is a constructor of `datatype`.
/// - ensures: the same value under the ambient context, each parameter replaced
///   by its argument and each field by the constructor's, the innermost first.
/// - fails: a telescope exceeding the representable binder space, or a
///   constructor shorter than its binders.
/// - panics: none.
///
/// # Errors
/// Returns `ConstructorArity` for an unrepresentable field telescope and
/// `DataArgumentArity` for an unrepresentable parameter one.
///
/// # Adequacy
/// - hypothesis: L3 — `Cons`'s `S(n)` reads its length field.
/// - witness: `tests::native_formers::an_indexed_constructor_stands_at_its_stated_index`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |id| arena.value(*id).is_some() || arena.value(stated).is_none()))]
fn result_index(
    arena: &mut TermArena,
    session: &mut SupportContext,
    (stated, datatype, value): (ValueId, ValueTypeId, ValueId),
    parameters: ParameterPrefix,
) -> Result<ValueId, KernelError>
{
    let count = match arena.value(value) {
        Some(&Value::Constructor { ref fields, .. }) => fields.len(),
        _ => return Err(KernelError::ArenaFault),
    };
    let fields =
        BinderDepth::from(u32::try_from(count).map_err(|_cause| KernelError::ConstructorArity)?);
    let mut result = stated_beneath(arena, session, (stated, datatype), parameters, fields)?;
    let (table, memo) = session.rewrite_parts();
    for before in (0 .. count).rev() {
        let field = match arena.value(value) {
            Some(&Value::Constructor { ref fields, .. }) => {
                fields.get(before).copied().ok_or(KernelError::ArenaFault)?
            },
            _ => return Err(KernelError::ArenaFault),
        };
        let depth = BinderDepth::from(
            u32::try_from(before).map_err(|_cause| KernelError::ConstructorArity)?,
        );
        let field = rewrite::shift_value(arena, table, memo, field, BinderDepth::NONE, depth);
        result = rewrite::substitute_value(arena, table, memo, result, field);
    }
    Ok(result)
}

/// Build one branch classifier by substituting its constructor into the motive.
///
/// Branches are ordinary functions over their constructor fields, then, over
/// an indexed family, over one equation per index: a path in the index's type
/// from the index the constructor states to the scrutinee's. The motive alone
/// has an implicit binder; syntax walkers need no declaration lookup.
///
/// # Specification
/// - requires: field types are scoped under the declaration parameter telescope
///   and their constructor's fields before them; `parameters` counts that
///   telescope, which for an indexed family is fewer than the classifier's
///   arguments; `indices` is the family's index telescope, each scoped under
///   the parameters and the indices before it, and `stated` the constructor's
///   result index per index, each scoped under the parameters and its fields.
/// - ensures: the result binds fields in declaration order, each at its type
///   instantiated at the classifier's parameters alone, then the equation
///   `Path(I, stated, s)` per index `I` in order, `s` the classifier's argument
///   at that index and `I` instantiated at the classifier's parameters and its
///   indices before it; and checks the motive at the corresponding constructor,
///   not merely at the original scrutinee.
/// - fails: field count exceeds the representable binder space, or a stated
///   index or classifier argument is missing.
/// - panics: none.
/// The executable postcondition requires a live computation classifier.
///
/// # Errors
/// Returns `ConstructorArity` when the telescope cannot be represented,
/// `IndexedSignature` for a missing stated index and `DataArgumentArity` for a
/// missing classifier argument.
///
/// # Adequacy
/// - hypothesis: L3 — a dependent motive rejects a branch at a wrong index; a
///   vector's element field stands at the element type, not at its index; a
///   branch at a vector's empty constructor binds the path from zero to the
///   scrutinee's length.
/// - witness: `tests::native_formers::data_case_checks_coverage_and_motive`
/// - witness: `tests::native_formers::an_indexed_constructor_stands_at_its_stated_index`
/// - witness: `tests::native_formers::an_indexed_case_prunes_a_constructor_at_an_apart_index`
#[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|id| arena.comp_type(*id).is_some()))]
pub(super) fn branch_type(
    arena: &mut TermArena,
    session: &mut SupportContext,
    (datatype, tag): (ValueTypeId, ConstructorTag),
    (fields, parameters): (&[ValueTypeId], ParameterPrefix),
    (indices, stated): (&[ValueTypeId], &[ValueId]),
    motive: CompTypeId,
) -> Result<CompTypeId, KernelError>
{
    let count = u32::try_from(fields.len()).map_err(|_cause| KernelError::ConstructorArity)?;
    let equations = u32::try_from(indices.len()).map_err(|_cause| KernelError::ConstructorArity)?;
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
    let instantiated = rewrite::substitute_comp_type(arena, table, memo, shifted, constructor);
    // The equations bind after the fields, so the motive stands under them.
    let mut result = rewrite::shift_comp_type(
        arena,
        table,
        memo,
        instantiated,
        BinderDepth::NONE,
        BinderDepth::from(equations),
    );
    for (position, &index) in indices.iter().enumerate().rev() {
        let before = u32::try_from(position).map_err(|_cause| KernelError::ConstructorArity)?;
        let under = count
            .checked_add(before)
            .ok_or(KernelError::ConstructorArity)?;
        let prefix = parameters
            .0
            .checked_add(position)
            .ok_or(KernelError::DataArgumentArity)?;
        // The index's type names the parameters and the indices before it,
        // instantiated at the classifier's, then carried under the fields and
        // the equations before it.
        let carrier = field_type(
            arena,
            session,
            (index, datatype),
            ParameterPrefix(prefix),
            BinderDepth::NONE,
        )?;
        let own = stated
            .get(position)
            .copied()
            .ok_or(KernelError::IndexedSignature)?;
        let own = stated_beneath(
            arena,
            session,
            (own, datatype),
            parameters,
            BinderDepth::from(count),
        )?;
        let scrutinised = match arena.value_type(datatype) {
            Some(&ValueType::Data { ref arguments, .. }) => arguments
                .get(prefix)
                .copied()
                .ok_or(KernelError::DataArgumentArity)?,
            _ => return Err(KernelError::ArenaFault),
        };
        let (table, memo) = session.rewrite_parts();
        let carrier = rewrite::shift_value_type(
            arena,
            table,
            memo,
            carrier,
            BinderDepth::NONE,
            BinderDepth::from(under),
        );
        let left = rewrite::shift_value(
            arena,
            table,
            memo,
            own,
            BinderDepth::NONE,
            BinderDepth::from(before),
        );
        let right = rewrite::shift_value(
            arena,
            table,
            memo,
            scrutinised,
            BinderDepth::NONE,
            BinderDepth::from(under),
        );
        let equation = arena.value_type_path(carrier, left, right);
        result = arena.comp_type_pi(equation, result);
    }
    for (index, &field) in fields.iter().enumerate().rev() {
        let earlier = BinderDepth::from(
            u32::try_from(index).map_err(|_cause| KernelError::ConstructorArity)?,
        );
        let domain = field_type(arena, session, (field, datatype), parameters, earlier)?;
        result = arena.comp_type_pi(domain, result);
    }
    Ok(result)
}

/// Whether a case still owes its sort's loops once its branches check.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Looped
{
    /// The case carries one branch per constructor over a sort its words loop
    /// at: it owes each loop by conversion (`loops::respected`).
    Owed,
    /// No loop binds the case, or it carries a loop arm per loop, whose goals
    /// settle them.
    Settled,
}

/// What a case scrutinises: its data classifier, the stage the case opened
/// when it opened one, and the definition whose own constant reads as the
/// fixpoint's self binder in the branches' field types.
pub(super) type Scrutinised = (
    ValueTypeId,
    Maybe<StageId, super::recursion::Unstaged>,
    Maybe<(ConstantIndex, DeBruijnIndex), super::recursion::Unowned>,
);

/// Collect the constructor-specific branch obligations and instantiated result.
///
/// # Specification
/// - requires: the scrutinee has the supplied data classifier; motive formation
///   is checked by the surrounding judgement; `read` is the written motive or
///   the staged result the case is checked at (`recursion::motive_at`).
/// - ensures: exactly one branch obligation per constructor, in table order,
///   each binding its recursive fields at the stage the case `opened`
///   (`recursion::stage_branch`) when it opened one — with the declaration's
///   own constant read as the self binder `own` names, every field domain that
///   named it returned as a [`super::recursion::Read`] — then, for a case
///   carrying a loop arm per loop of its sort (`loops::loops`), one per loop
///   arm at `loops::arm_type`; [`Looped::Owed`] exactly when the sort has loops
///   and the case carries no loop arm. The branches and the result are read at
///   `read` over a sort with no loops, and at the written motive otherwise.
/// - fails: wrong shape or a non-exhaustive branch vector: neither one branch
///   per constructor nor one more per loop. A presented type's rules are an
///   obligation the caller decides once the branches have checked, by
///   `respect::respected`, and so are owed loops, by `loops::respected`.
/// - panics: none.
/// The executable postcondition classifies every returned computation check.
///
/// # Errors
/// Returns native shape, coverage, instantiation or arena refusals.
///
/// # Adequacy
/// - hypothesis: L3 — omitted and surplus arms both refuse before branch
///   checking; a circle case with its loop arm checks the arm.
/// - witness: `tests::native_formers::data_case_checks_coverage_and_motive`
/// - witness: `tests::recursive_data::a_recursion_descends_on_its_first_parameter`
/// - witness: `tests::recursive_data::a_mutual_block_is_admitted`
/// - witness: `tests::native_formers::a_loop_arm_checks_at_the_path_over_its_loop`
#[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|result| result.1.iter().all(|goal| matches!(goal, &Goal::CheckComp(..)))))]
pub(super) fn case(
    arena: &mut TermArena,
    (entries, presentations): (&Entries, &crate::presented::Presentations),
    session: &mut SupportContext,
    (case, read): (ComputationId, CompTypeId),
    (datatype, opened, own): Scrutinised,
) -> Result<(CompTypeId, Vec<Goal>, Looped, Vec<super::recursion::Read>), KernelError>
{
    let (scrutinee, written, count, equations) =
        match arena.computation(case).ok_or(KernelError::ArenaFault)? {
            &Computation::DataCase {
                ref scrutinee,
                ref motive,
                ref branches,
                equations,
            } => (*scrutinee, *motive, branches.len(), equations),
            &Computation::RecordProjection(..)
            | &Computation::TupleProjection(..)
            | &Computation::Lambda(_)
            | &Computation::Application(..)
            | &Computation::Return(_)
            | &Computation::Bind(..)
            | &Computation::Force(_)
            | &Computation::Case { .. }
            | &Computation::SigmaSplit { .. }
            | &Computation::ListFold { .. }
            | &Computation::ListCase { .. }
            | &Computation::Transport(..)
            | &Computation::PathTransport { .. }
            | &Computation::TelescopeTransport { .. }
            | &Computation::Ride { .. }
            | &Computation::TelescopeRide { .. }
            | &Computation::RelatedApplication { .. }
            | &Computation::With(..)
            | &Computation::Project(..)
            | &Computation::Fixpoint { .. } => return Err(KernelError::ArenaFault),
        };
    let (declaration, argument_count) =
        match arena.value_type(datatype).ok_or(KernelError::ArenaFault)? {
            &ValueType::Data {
                ref declaration,
                ref arguments,
            } => (*declaration, arguments.len()),
            &ValueType::Record(_)
            | &ValueType::Session { .. }
            | &ValueType::PathUniverse(..)
            | &ValueType::FlowUniverse(..)
            | &ValueType::Path { .. }
            | &ValueType::Flow { .. }
            | &ValueType::Bridge { .. }
            | &ValueType::Base(_)
            | &ValueType::Product(_)
            | &ValueType::Sigma { .. }
            | &ValueType::Sum(_)
            | &ValueType::List(_)
            | &ValueType::Thunk(_)
            | &ValueType::Universe { .. }
            | &ValueType::Lift { .. }
            | &ValueType::Element { .. }
            | &ValueType::Abstract(_)
            | &ValueType::StaticPi { .. }
            | &ValueType::Staged { .. } => {
                return Err(super::value_shape_mismatch(
                    arena,
                    ExpectedValueShape::Data,
                    datatype,
                ));
            },
        };
    let signature = signature(entries, declaration)?;
    if signature.arity() != FamilyArity(argument_count) {
        return Err(KernelError::DataArgumentArity);
    }
    let owed = super::loops::loops(arena, presentations, datatype);
    // A loop is owed at the written motive.
    let motive = if owed.is_empty() { read } else { written };
    let constructors = signature.constructors.len();
    let looped = if count == constructors {
        if owed.is_empty() {
            Looped::Settled
        }
        else {
            Looped::Owed
        }
    }
    else if !owed.is_empty() && constructors.checked_add(owed.len()) == Some(count) {
        Looped::Settled
    }
    else {
        return Err(KernelError::NonExhaustiveDataCase);
    };
    // Every branch over an indexed family binds one equation per index.
    if usize::from(equations) != signature.indices.len() {
        return Err(KernelError::NonExhaustiveDataCase);
    }
    let mut goals = Vec::with_capacity(count);
    let mut reads = Vec::new();
    // A mutual block's families share the stage the case opened.
    let block = match opened {
        Maybe::Present(_) => super::recursion::families(arena, entries, datatype)?,
        Maybe::Absent(_) => super::occurrence::Block::lone(declaration),
    };
    for (index, fields) in signature.constructors.iter().enumerate() {
        let tag = ConstructorTag::from(index);
        let stated = signature.results.get(index).map_or(&[][..], Vec::as_slice);
        let expected = branch_type(
            arena,
            session,
            (datatype, tag),
            (fields, ParameterPrefix(signature.parameters.len())),
            (signature.indices, stated),
            motive,
        )?;
        let expected = match opened {
            Maybe::Present(child) => super::recursion::stage_branch(
                arena,
                session,
                (block, tag),
                expected,
                (fields, child),
                (own, &mut reads),
            )?,
            Maybe::Absent(_plain) => expected,
        };
        let branch = match arena.computation(case) {
            Some(&Computation::DataCase { ref branches, .. }) => branches
                .get(index)
                .copied()
                .ok_or(KernelError::ArenaFault)?,
            _ => return Err(KernelError::ArenaFault),
        };
        goals.push(Goal::CheckComp(branch, expected));
    }
    if count != constructors {
        for (position, &owed_loop) in owed.iter().enumerate() {
            let expected =
                super::loops::arm_type(arena, presentations, (case, datatype, motive), owed_loop)?;
            let arm = match arena.computation(case) {
                Some(&Computation::DataCase { ref branches, .. }) => constructors
                    .checked_add(position)
                    .and_then(|index| branches.get(index))
                    .copied()
                    .ok_or(KernelError::ArenaFault)?,
                _ => return Err(KernelError::ArenaFault),
            };
            goals.push(Goal::CheckComp(arm, expected));
        }
    }
    let (table, memo) = session.rewrite_parts();
    let result = rewrite::substitute_comp_type(arena, table, memo, motive, scrutinee);
    Ok((result, goals, looped, reads))
}

quenchant_shape::reason_enum! {
    /// Why a data case is no appeal to the apartness rule.
    pub(super) mod absurd {
        /// The reason the case splits by its type's constructors instead.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub(in crate::check) enum Absent {
            /// The case has branches.
            Branched,
            /// The scrutinee's type is no path between two terms of a data
            /// type.
            NotAPath,
        }
    }
}

/// The result of a case of no branches over a path between two apart terms
/// of a data type: the motive at the scrutinee, with no branch owed.
///
/// # Specification
/// - requires: the scrutinee has the classifier `datatype`, read as its words
///   where it is a path at a looped point; the motive has formed under one
///   binder of it.
/// - ensures: `Present(motive[scrutinee])` exactly when the case has no branch,
///   `datatype` is `Path(domain, left, right)` with `domain` — read as its
///   words where it is itself a path at a looped point — a data type, and
///   [`crate::presented::apart`] decides `left` and `right` apart;
///   [`absurd::Absent::Branched`] or [`absurd::Absent::NotAPath`] when the case
///   is no such appeal, which [`case`] then checks as a split.
/// - provides: the elimination of a path between apart terms, the absurd case's
///   one admission rule.
/// - fails: [`KernelError::NotApart`] naming why the endpoints are not shown
///   apart, [`KernelError::NotADataType`] or [`KernelError::ArenaFault`].
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — a case of no branches over `Path(N, Succ(Zero), Zero)` at
///   the naturals modulo two admits, and one over `Path(N, Succ(Succ(Zero)),
///   Zero)`, whose normal forms agree, is refused by name.
/// - witness: `tests::native_formers::an_absurd_case_rests_on_apart_endpoints`
#[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(KernelError::NotApart(_) | KernelError::NotADataType { .. } | KernelError::ArenaFault)))]
pub(super) fn absurd(
    arena: &mut TermArena,
    (entries, presentations): (&Entries, &Presentations),
    session: &mut SupportContext,
    case: ComputationId,
    datatype: ValueTypeId,
) -> Result<Maybe<CompTypeId, absurd::Absent>, KernelError>
{
    let (scrutinee, motive) = match arena.computation(case).ok_or(KernelError::ArenaFault)? {
        &Computation::DataCase {
            scrutinee,
            motive,
            ref branches,
            ..
        } => {
            if !branches.is_empty() {
                return Ok(Maybe::Absent(absurd::Absent::Branched));
            }
            (scrutinee, motive)
        },
        &Computation::RecordProjection(..)
        | &Computation::TupleProjection(..)
        | &Computation::Lambda(_)
        | &Computation::Application(..)
        | &Computation::Return(_)
        | &Computation::Bind(..)
        | &Computation::Force(_)
        | &Computation::Case { .. }
        | &Computation::SigmaSplit { .. }
        | &Computation::ListFold { .. }
        | &Computation::ListCase { .. }
        | &Computation::Transport(..)
        | &Computation::PathTransport { .. }
        | &Computation::TelescopeTransport { .. }
        | &Computation::Ride { .. }
        | &Computation::TelescopeRide { .. }
        | &Computation::RelatedApplication { .. }
        | &Computation::With(..)
        | &Computation::Project(..)
        | &Computation::Fixpoint { .. } => return Err(KernelError::ArenaFault),
    };
    let Some(&ValueType::Path {
        domain,
        left,
        right,
    }) = arena.value_type(datatype)
    else {
        return Ok(Maybe::Absent(absurd::Absent::NotAPath));
    };
    let domain = presentations.identified(arena, domain);
    let Some(&ValueType::Data { declaration, .. }) = arena.value_type(domain)
    else {
        return Ok(Maybe::Absent(absurd::Absent::NotAPath));
    };
    match presented::apart(arena, entries, declaration, (left, right))? {
        Apartness::Apart => {},
        reason @ (Apartness::Agree
        | Apartness::Open
        | Apartness::Leaf
        | Apartness::Diverges { .. }
        | Apartness::Undecided) => return Err(KernelError::NotApart(reason)),
    }
    let (table, memo) = session.rewrite_parts();
    Ok(Maybe::Present(rewrite::substitute_comp_type(
        arena, table, memo, motive, scrutinee,
    )))
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
/// - witness: `tests::native_formers::record_width_depth_projection_and_absent_fields`
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
