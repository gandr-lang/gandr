//! Native nominal signature formation, sealed abstract-type formation and
//! capture-free telescope instantiation.
//!
//! # Nominal data
//!
//! A data declaration admits a nominal identity with a parameter telescope, an
//! ordered constructor table and a positive universe bound. Its signature is
//! not a value type for the declaration's constant: `Verdict::Data` is distinct
//! from a checked value, and a term reference to that position is refused. A
//! `Data` application checks each explicit argument against its instantiated
//! parameter classifier. Constructors retain that complete application and
//! their tag; fields check against the declaration's instantiated field types.
//! A case supplies exactly one branch per tag and a computation motive under
//! one scrutinee binder. Branches are ambient functions over their constructor
//! fields, not syntax under implicit field binders.
//!
//! **Choice.** Nominal identity stays separate from structural records; neither
//! is an abstract atom or a product encoding. Type parameters are quoted codes
//! and value indices are ordinary terms in one typed telescope. All arguments
//! are invariant: declaration formation proves no variance property that would
//! justify covariance. Constructor fields may use parameters and the
//! declaration's own family, but do not bind subsequent fields, and a
//! declaration cannot see a later declaration.
//!
//! **Conversion boundary.** Index equality is structural in both checkers,
//! including under thunks, and ignores only candidate path evidence as ordinary
//! kernel conversion does. It does not reduce beta, delta or eta redexes.
//! General definitional index conversion waits for a certified kernel
//! conversion reader; frontend conversion alone cannot authorize it.
//! `term_indices_are_structural_in_both_checkers` witnesses separately
//! allocated equal function indices and constant references, and refuses beta-
//! and delta-related indices rather than accepting a declaration the kernel
//! rejects. **Reversal.** Widen this boundary only with replay-checked index
//! conversion and independent readmission witnesses.
//!
//! The programmatic forms cross ordinary checked kernel admission, canonical
//! artifacts, incremental support and edit snapshots, and
//! `gandr-core-sequent`'s machine runs nominal constructors, cases and
//! fixpoints. There is no parser notation, description decoder or graded thunk
//! former for them. Native declarations export as data declarations, not
//! axioms.
//!
//! # Sealed abstract types
//!
//! An abstract type forms when its kind is a value universe and its
//! representation forms at or below that universe's level; then its site
//! mints its atom and the context retains it. Like a data declaration it is
//! nominal — `Verdict::Data` answers it, and no value type enters the
//! signature table at its position — but its atom has no constructors and no
//! eliminator: inside its seal the weak head reads it as its representation,
//! and outside it relates to nothing but itself. The kernel admits the same
//! declaration under the same two premises.

use alloc::sync::Arc;
use alloc::vec::Vec;

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
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::RuleSlot;
use quenchant_shape::shape::Maybe;

use crate::CheckRefusal;
use crate::CheckingContext;
use crate::TypeNode;
use crate::declaration::AbstractType;
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
/// Fields see the complete parameter telescope and the declaration's own
/// family, at its admission position, but no constructor fields. The family
/// may occur in a field only strictly positively and at its parameter
/// variables, which the occurrence walk decides before anything forms. A
/// refused signature leaves no binder, block or nominal entry.
///
/// # Specification
/// - requires: the nominal entry has not been installed in the context, and
///   `position` is the admission position the declaration takes.
/// - ensures: every occurrence of the family is strictly positive and uniform;
///   every parameter and field forms in its declared scope; fields fit the
///   declared value universe; the original binder depth is restored and the
///   block closed.
/// - fails: occurrence, kind, formation and field-universe refusals are
///   retained.
/// - panics: none.
///
/// # Errors
/// [`CheckRefusal`] identifies the failed formation judgment.
///
/// # Adequacy
/// - hypothesis: L3 — dependent parameters, an invalid field, an excessive
///   field universe, admitted self references and refused occurrences
///   distinguish the admission premises.
/// - witness: `native_formers::native_formers::data_declarations_and_refusals_agree_with_kernel`
/// - witness: `recursive_data::recursive_data::recursive_blocks_are_admitted_in_both_checkers`
/// - witness: `recursive_data::recursive_data::occurrences_are_refused_by_name_in_both_checkers`
#[spec(captures: depth = context.depth(Zone::Intuitionistic), ensures: context.depth(Zone::Intuitionistic) == depth
    && (matches!(context.data_in_scope(position), Maybe::Absent(_)) || context.data_signatures().contains_key(&position)))]
pub fn form_signature(
    context: &mut CheckingContext<'_>,
    position: ConstantIndex,
    signature: &Arc<DataSignature>,
) -> Result<(), CheckRefusal>
{
    crate::occurrence::occurrences(context.arena(), position, signature)?;
    let depth = context.depth(Zone::Intuitionistic);
    context.open_block(position, Arc::clone(signature));
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
        present(context, position, signature)
    })();
    context.close_block();
    while context.depth(Zone::Intuitionistic) != depth {
        let _closed = context
            .binders()
            .close(Zone::Intuitionistic)
            .map_err(|_cause| CheckRefusal::MachineInvariant)?;
    }
    outcome
}

/// Check a data declaration's rules against its constructor table.
///
/// # Specification
/// - requires: `signature` is the declaration's at `position`, its fields
///   formed.
/// - ensures: `Ok(())` exactly when the rules validate against the table, a
///   field reading as the declaration's own type where it is the family at
///   `position` and as its classifier elsewhere — the table the kernel's
///   admission reads, so the two refuse alike.
/// - fails: [`CheckRefusal::RuleNotPresentable`] naming the first rule that
///   does not present the type and why.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — a rule placing a constructor of the family at a field of
///   another type is refused by name in both checkers, and the circle's
///   cancellations admit.
/// - witness: `native_formers::native_formers::a_misplaced_rule_is_refused_in_both_checkers`
/// - witness: `native_formers::native_formers::a_presented_word_meets_its_reduced_word_in_both_checkers`
#[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(CheckRefusal::RuleNotPresentable { .. })))]
fn present(
    context: &CheckingContext<'_>,
    position: ConstantIndex,
    signature: &DataSignature,
) -> Result<(), CheckRefusal>
{
    let presentation = signature.presentation();
    if presentation.rules().is_empty() {
        return Ok(());
    }
    let table: Vec<Vec<RuleSlot<ValueTypeId>>> = signature
        .constructors()
        .iter()
        .map(|fields| {
            fields
                .iter()
                .map(|&field| match context.arena().value_type(field) {
                    | Some(&ValueType::Data { declaration, .. }) if declaration == position => {
                        RuleSlot::Own
                    },
                    | _ => RuleSlot::Other(field),
                })
                .collect()
        })
        .collect();
    presentation
        .validate(&table)
        .map_err(|refusal| CheckRefusal::RuleNotPresentable {
            kind: signature.kind(),
            refusal,
        })
}

/// Form an abstract type's kind and representation: the level of the universe
/// its atom will inhabit.
///
/// # Specification
/// - requires: nothing.
/// - ensures: on success the kind is a value universe whose level is returned,
///   the representation forms at or below that level, and the site has not
///   minted an atom; the seal table is unchanged either way.
/// - fails: the formation refusal of the kind or the representation;
///   [`CheckRefusal::AbstractKindNotUniverse`] for a kind that is no value
///   universe, or one at the greatest level;
///   [`CheckRefusal::RepresentationAboveKind`] for a representation above it;
///   [`CheckRefusal::SealSiteRepeated`] for a site minted before.
/// - panics: none.
///
/// # Errors
/// [`CheckRefusal`] identifies the failed premise.
///
/// # Adequacy
/// - hypothesis: L3 — a kind at a value universe, a kind that is no universe, a
///   representation above its kind and a repeated site separate the premises.
/// - witness: `module::tests::an_abstract_type_forms_at_a_value_universe_and_mints_its_site`
/// - witness: `module::tests::a_repeated_sealing_site_is_refused_and_mints_nothing`
#[spec(
    captures: minted = context.seal_table().sites().len(),
    ensures: |ret| context.seal_table().sites().len() == minted
        && (ret.is_err() || matches!(context.seal_table().lookup(declared.site()), Maybe::Absent(_))),
)]
pub fn form_abstract(
    context: &mut CheckingContext<'_>,
    declared: AbstractType,
) -> Result<Level, CheckRefusal>
{
    let kind = declared.kind();
    let _formed = form_value_type(context, kind)?;
    let level = match context.arena().value_type(kind) {
        | Some(&ValueType::Universe {
            sort: Sort::Ground(GroundSort::Value),
            ref level,
        }) => level.clone(),
        | _ => return Err(CheckRefusal::AbstractKindNotUniverse(kind)),
    };
    let upper = level
        .succ()
        .map_err(|_cause| CheckRefusal::AbstractKindNotUniverse(kind))?;
    let representation = declared.representation();
    let _formed = form_value_type(context, representation)?;
    if !bool::from(level_of(context, TypeNode::Value(representation))?.lt(&upper)) {
        return Err(CheckRefusal::RepresentationAboveKind {
            representation,
            kind,
        });
    }
    if let Maybe::Present(_) = context.seal_table().lookup(declared.site()) {
        return Err(CheckRefusal::SealSiteRepeated(declared.site()));
    }
    Ok(level)
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
#[spec(ensures: |ret| ret.as_ref().is_ok_and(|signature| matches!(context.arena().value_type(datatype), Some(ValueType::Data { declaration, arguments }) if matches!(context.data_in_scope(*declaration), Maybe::Present(ref held) if held == signature) && signature.parameters().len() == arguments.len())) == ret.is_ok())]
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
