//! Codata: a declaration's observations, read as one lazy product.
//!
//! A codata declaration `νX. &{dᵢ : Bᵢ}` states a parameter telescope, a
//! computation universe as its kind and one computation type per observation,
//! each scoped under the parameters. Its application `Codata(d, ā)` is a
//! computation type. It converts nominally — one declaration at convertible
//! arguments — and is read through its observations only where a rule needs
//! its shape: a lambda, a return or a lazy pair checked against it, and an
//! application, a projection or a bind of a computation that synthesizes it.
//! [`read`] instantiates every observation at `ā` and joins them
//! right-nested with `With`, a single observation standing as itself. There is
//! no η: a codata type never converts with its observation product.
//!
//! While its observations form, the declaration names itself only at an
//! observation's result — the end of the observation's arrow spine — and only
//! at its parameter variables in telescope order, so every coinductive
//! occurrence stands behind an observation. [`form_signature`] forms that
//! result without the formation rules; anywhere else, the rule forming a codata
//! application refuses the declaration being formed as
//! [`CodataFault::Occurrence`]. The kernel admits the same declarations by the
//! same guard. The fixpoints that inhabit a codata type are partial fixpoints;
//! their productivity is not judged here.
//!
//! # References
//! - Andreas Abel, Brigitte Pientka, David Thibodeau and Anton Setzer,
//!   "Copatterns: programming infinite structures by observations", POPL 2013.

use alloc::sync::Arc;

use anodized::spec;
use gandr_core_term::Binders;
use gandr_core_term::CodataSignature;
use gandr_core_term::CompTypeId;
use gandr_core_term::Sort;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_kernel_strata::Level;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::GroundSort;
use quenchant_shape::shape::Maybe;

use crate::CheckRefusal;
use crate::CheckingContext;
use crate::CoreNode;
use crate::TypeNode;
use crate::formation::form_comp_type;
use crate::formation::form_value_type;
use crate::formation::level_of;
use crate::view::CompTypeView;
use crate::view::comp_type_view;

/// Why a codata declaration or application is refused.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum CodataFault
{
    /// The application's head names no admitted codata declaration.
    Undeclared,
    /// The declaration's kind is not a computation universe.
    KindNotUniverse,
    /// The declaration states no observation.
    WithoutObservations,
    /// The declaration names itself other than at an observation's result at
    /// its parameter variables in telescope order.
    Occurrence,
    /// An observation lives above the declared universe.
    ObservationLevel,
    /// The application supplies another number of arguments than the
    /// declaration's telescope.
    Arity,
}

/// The refusal `fault` at the computation type `at`.
///
/// # Specification
/// trivial.
const fn refused(
    at: CompTypeId,
    fault: CodataFault,
) -> CheckRefusal
{
    CheckRefusal::Codata {
        at: CoreNode::Type(TypeNode::Computation(at)),
        fault,
    }
}

/// A position in a codata declaration's parameter telescope, or the count of
/// the parameters before it.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(crate) struct ParameterAt(pub usize);

/// The dependent binders an observation's arrow spine opens past its
/// declaration's telescope.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct SpineBinders(usize);

/// Read a codata kind's computation-universe level.
///
/// # Specification
/// - requires: nothing; malformed kinds are admissible input.
/// - ensures: only a computation universe supplies a level, its own.
/// - fails: [`CodataFault::KindNotUniverse`] at the kind for any other former
///   or sort.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — a value universe as a codata kind is refused and a
///   computation universe admitted.
/// - witness: `tests::codata::a_value_universe_is_no_codata_kind`
#[spec(ensures: |ret| ret.as_ref().is_ok_and(|level| matches!(context.arena().value_type(kind), Some(ValueType::Universe { sort: Sort::Ground(GroundSort::Computation), level: held }) if held == level)) == ret.is_ok())]
#[inline]
pub fn kind_level(
    context: &CheckingContext<'_>,
    kind: ValueTypeId,
) -> Result<Level, CheckRefusal>
{
    match context.arena().value_type(kind) {
        Some(&ValueType::Universe {
            sort: Sort::Ground(GroundSort::Computation),
            ref level,
        }) => Ok(level.clone()),
        _ => Err(CheckRefusal::Codata {
            at: CoreNode::Type(TypeNode::Value(kind)),
            fault: CodataFault::KindNotUniverse,
        }),
    }
}

/// Check a codata declaration's kind, parameter telescope and observations
/// before admission.
///
/// # Specification
/// - requires: the declaration has not been admitted, and `position` is the
///   admission position it takes.
/// - ensures: success exactly when the kind is a computation universe, there is
///   an observation, every parameter forms under those before it, and every
///   observation forms under the parameters below the kind's universe, naming
///   the declaration only at its result at the parameter variables
///   ([`observation`]); the binder depth is restored and the declaration is out
///   of scope afterwards.
/// - fails: [`CheckRefusal::Codata`] for the kind, a missing observation, a
///   self reference or an observation above the universe; a formation refusal
///   of a parameter or an observation.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — a stream is admitted; a value-universe kind, a
///   declaration without observations, a self reference in a domain, one at
///   other arguments and an observation above its universe are each refused by
///   name.
/// - witness: `tests::codata::a_stream_is_admitted_observed_and_adopted`
/// - witness: `tests::codata::a_value_universe_is_no_codata_kind`
/// - witness: `tests::codata::a_self_reference_off_an_observations_result_is_refused`
#[spec(captures: depth = context.depth(Zone::Intuitionistic), ensures: context.depth(Zone::Intuitionistic) == depth)]
#[inline]
pub fn form_signature(
    context: &mut CheckingContext<'_>,
    position: ConstantIndex,
    signature: &Arc<CodataSignature>,
) -> Result<(), CheckRefusal>
{
    let depth = context.depth(Zone::Intuitionistic);
    context.open_codata(position, Arc::clone(signature));
    let outcome = (|| {
        let _kind = form_value_type(context, signature.kind())?;
        let level = kind_level(context, signature.kind())?;
        if signature.observations().is_empty() {
            return Err(CheckRefusal::Codata {
                at: CoreNode::Type(TypeNode::Value(signature.kind())),
                fault: CodataFault::WithoutObservations,
            });
        }
        let upper = level.succ().map_err(|_cause| CheckRefusal::Codata {
            at: CoreNode::Type(TypeNode::Value(signature.kind())),
            fault: CodataFault::KindNotUniverse,
        })?;
        for &parameter in signature.parameters() {
            let _formed = form_value_type(context, parameter)?;
            context.binders().open(Zone::Intuitionistic, parameter);
        }
        for &observed in signature.observations() {
            observation(
                context,
                position,
                ParameterAt(signature.parameters().len()),
                observed,
            )?;
            if !bool::from(level_of(context, TypeNode::Computation(observed))?.lt(&upper)) {
                return Err(refused(observed, CodataFault::ObservationLevel));
            }
        }
        Ok(())
    })();
    context.close_codata();
    while context.depth(Zone::Intuitionistic) != depth {
        let _closed = context
            .binders()
            .close(Zone::Intuitionistic)
            .map_err(|_cause| CheckRefusal::MachineInvariant)?;
    }
    outcome
}

/// Form one observation of the codata declaration at `position`, whose
/// observations are forming, under its `parameters` parameters.
///
/// # Specification
/// - requires: the declaration at `position` is forming and the context is
///   under its parameters.
/// - ensures: success exactly when every domain of the observation's arrow
///   spine forms — a dependent one opening its binder for the rest — and the
///   spine ends either in a codata application of `position` whose arguments
///   are the parameter variables in telescope order, read past the spine's
///   dependent binders, or in a computation type that forms; formation refuses
///   `position` anywhere else. The binder depth is restored on success.
/// - fails: [`CodataFault::Occurrence`] at a self application at other
///   arguments, and the formation refusal of a domain or of the spine's end.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Termination
/// - reason: a loop down the arrow spine, not recursion.
/// - measure: the spine's length; each codomain is a fresh arena node below its
///   arrow.
///
/// # Adequacy
/// - hypothesis: L3 — a stream's tail at its parameter forms, a tail at another
///   argument and a self reference in a domain are refused by name.
/// - witness: `tests::codata::a_stream_is_admitted_observed_and_adopted`
/// - witness: `tests::codata::a_self_reference_off_an_observations_result_is_refused`
#[spec(captures: depth = context.depth(Zone::Intuitionistic), ensures: |ret| ret.is_err() || context.depth(Zone::Intuitionistic) == depth)]
fn observation(
    context: &mut CheckingContext<'_>,
    position: ConstantIndex,
    parameters: ParameterAt,
    observed: gandr_core_term::CompTypeId,
) -> Result<(), CheckRefusal>
{
    let depth = context.depth(Zone::Intuitionistic);
    let mut binders = SpineBinders::default();
    let mut cursor = observed;
    loop {
        match comp_type_view(context.arena(), cursor)? {
            CompTypeView::Arrow { domain, codomain } => {
                let _formed = form_value_type(context, domain)?;
                cursor = codomain;
            },
            CompTypeView::Pi { domain, codomain } => {
                let _formed = form_value_type(context, domain)?;
                context.binders().open(Zone::Intuitionistic, domain);
                binders = SpineBinders(binders.0.saturating_add(1));
                cursor = codomain;
            },
            CompTypeView::Codata {
                declaration,
                arguments,
            } if declaration == position => {
                uniform(context, (cursor, arguments), parameters, binders)?;
                break;
            },
            CompTypeView::Returner { .. }
            | CompTypeView::With(..)
            | CompTypeView::Element { .. }
            | CompTypeView::Codata { .. }
            | CompTypeView::Unknown => {
                let _formed = form_comp_type(context, cursor)?;
                break;
            },
        }
    }
    while context.depth(Zone::Intuitionistic) != depth {
        let _closed = context
            .binders()
            .close(Zone::Intuitionistic)
            .map_err(|_cause| CheckRefusal::MachineInvariant)?;
    }
    Ok(())
}

/// Refuse `arguments`, the arguments of the self application `at`, unless
/// they are a codata telescope's `parameters` parameter variables in order,
/// read `binders` binders past the telescope.
///
/// # Specification
/// - ensures: success exactly when there are `parameters` arguments and
///   argument `i` is the intuitionistic variable `parameters - 1 - i +
///   binders`.
/// - fails: [`CodataFault::Occurrence`] at `at` otherwise.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Clause cost
/// - bound: one arena read per argument.
///
/// # Adequacy
/// - hypothesis: L3 — a stream's tail at its parameter succeeds, a tail at
///   another argument is refused by name.
/// - witness: `tests::codata::a_stream_is_admitted_observed_and_adopted`
/// - witness: `tests::codata::a_self_reference_off_an_observations_result_is_refused`
#[spec(ensures: |ret| ret.is_err() || arguments.len() == parameters.0)]
fn uniform(
    context: &CheckingContext<'_>,
    (at, arguments): (CompTypeId, &[ValueId]),
    parameters: ParameterAt,
    binders: SpineBinders,
) -> Result<(), CheckRefusal>
{
    let held = arguments.len() == parameters.0
        && arguments.iter().enumerate().all(|(index, &argument)| {
            let expected = parameters
                .0
                .saturating_sub(index)
                .saturating_sub(1)
                .saturating_add(binders.0);
            u32::try_from(expected).is_ok_and(|expected| {
                context.arena().value(argument)
                    == Some(&Value::Variable {
                        zone: Zone::Intuitionistic,
                        index: DeBruijnIndex::from(expected),
                    })
            })
        });
    if held {
        Ok(())
    }
    else {
        Err(refused(at, CodataFault::Occurrence))
    }
}

/// The admitted signature a codata application names, at its arity.
///
/// # Specification
/// - requires: `codata` is a codata application.
/// - ensures: the logged signature of the application's declaration, whose
///   telescope has one parameter per argument.
/// - fails: [`CodataFault::Occurrence`] for the declaration whose observations
///   are forming, [`CodataFault::Undeclared`] for a position naming no admitted
///   codata declaration, [`CodataFault::Arity`] for another argument count.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — a stream at one argument resolves; a data position and a
///   stream at two arguments are refused by name.
/// - witness: `tests::codata::a_codata_application_names_an_admitted_declaration_at_its_arity`
#[spec(ensures: |ret| ret.as_ref().is_ok_and(|signature| matches!(comp_type_view(context.arena(), codata), Ok(CompTypeView::Codata { arguments, .. }) if arguments.len() == signature.parameters().len())) == ret.is_ok())]
pub(crate) fn signature(
    context: &mut CheckingContext<'_>,
    codata: CompTypeId,
) -> Result<Arc<CodataSignature>, CheckRefusal>
{
    let CompTypeView::Codata {
        declaration,
        arguments,
    } = comp_type_view(context.arena(), codata)?
    else {
        return Err(CheckRefusal::MachineInvariant);
    };
    let count = arguments.len();
    if let Maybe::Present(_) = context.codata_forming_at(declaration) {
        return Err(refused(codata, CodataFault::Occurrence));
    }
    let Maybe::Present(signature) = context.consult_codata(declaration)
    else {
        return Err(refused(codata, CodataFault::Undeclared));
    };
    if signature.parameters().len() != count {
        return Err(refused(codata, CodataFault::Arity));
    }
    Ok(signature)
}

/// The `index`th argument of the codata application `codata`.
///
/// # Specification
/// - ensures: the argument at `index`.
/// - fails: [`CheckRefusal::MachineInvariant`] for a node that is no codata
///   application or an index past its arguments.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — a stream's one argument is read at its position.
/// - witness: `tests::codata::a_stream_is_admitted_observed_and_adopted`
#[spec(ensures: |ret| ret.is_err() || matches!(comp_type_view(context.arena(), codata), Ok(CompTypeView::Codata { arguments, .. }) if arguments.get(index.0).copied() == ret.ok()))]
pub(crate) fn argument(
    context: &CheckingContext<'_>,
    codata: CompTypeId,
    index: ParameterAt,
) -> Result<ValueId, CheckRefusal>
{
    match comp_type_view(context.arena(), codata)? {
        CompTypeView::Codata { arguments, .. } => arguments
            .get(index.0)
            .copied()
            .ok_or(CheckRefusal::MachineInvariant),
        CompTypeView::Returner { .. }
        | CompTypeView::With(..)
        | CompTypeView::Arrow { .. }
        | CompTypeView::Pi { .. }
        | CompTypeView::Element { .. }
        | CompTypeView::Unknown => Err(CheckRefusal::MachineInvariant),
    }
}

/// `subject`, scoped under the first `prefix` parameters of `codata`'s
/// declaration, with each replaced by the application's argument.
///
/// # Specification
/// - requires: `subject` is scoped under `prefix` parameters of the declaration
///   `codata` names.
/// - ensures: the arguments substituted simultaneously, each carried under the
///   parameters still bound; zero parameters return the same node.
/// - fails: as [`argument`].
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — a stream of units reads its head at the unit type.
/// - witness: `tests::codata::a_stream_is_admitted_observed_and_adopted`
#[spec(ensures: |ret| prefix.0 != 0 || ret == Ok(subject))]
pub(crate) fn instantiate_value(
    context: &mut CheckingContext<'_>,
    codata: CompTypeId,
    mut subject: ValueTypeId,
    prefix: ParameterAt,
) -> Result<ValueTypeId, CheckRefusal>
{
    for index in (0 .. prefix.0).rev() {
        let carried = carried(context, codata, ParameterAt(index))?;
        subject = gandr_core_term::instantiate_value_type(context.arena_mut(), subject, carried);
    }
    Ok(subject)
}

/// The `index`th argument of `codata`, carried past the `index` parameters
/// before it.
///
/// # Specification
/// - ensures: the argument shifted by `index` binders.
/// - fails: as [`argument`].
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — as [`instantiate_value`].
/// - witness: `tests::codata::a_stream_is_admitted_observed_and_adopted`
#[spec(ensures: |ret| ret.is_err() || index.0 != 0 || ret == argument(context, codata, index))]
fn carried(
    context: &mut CheckingContext<'_>,
    codata: CompTypeId,
    index: ParameterAt,
) -> Result<ValueId, CheckRefusal>
{
    let argument = argument(context, codata, index)?;
    let depth =
        Binders::from(u32::try_from(index.0).map_err(|_cause| CheckRefusal::MachineInvariant)?);
    Ok(
        gandr_core_term::shift_value(context.arena_mut(), argument, depth)
            .settle(context.arena_mut()),
    )
}

/// `shape` at its weak head, read through its observations when it is a
/// codata application.
///
/// # Specification
/// - requires: `shape` is formed.
/// - ensures: for a codata application, every observation of its declaration
///   instantiated at the arguments, joined right-nested with `With` in
///   declaration order — one observation standing as itself — at its weak head;
///   any other type at its weak head.
/// - provides: the one place a rule reads a codata type's shape.
/// - fails: as [`signature`] and [`argument`]; the unfolding's refusal.
/// - panics: none.
///
/// # Errors
/// As `- fails:`.
///
/// # Adequacy
/// - hypothesis: L3 — a stream of units reads as `F Unit & Stream Unit`, a
///   one-observation codata as that observation, and a returner unchanged.
/// - witness: `tests::codata::a_stream_is_admitted_observed_and_adopted`
/// - witness: `tests::codata::a_single_observation_reads_as_itself`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |read| context.arena().comp_type(*read).is_some()))]
#[inline]
pub fn read(
    context: &mut CheckingContext<'_>,
    shape: CompTypeId,
) -> Result<CompTypeId, CheckRefusal>
{
    let head = context.whnf_comp_type(shape)?;
    if !matches!(
        comp_type_view(context.arena(), head)?,
        CompTypeView::Codata { .. }
    ) {
        return Ok(head);
    }
    let signature = signature(context, head)?;
    let count = signature.parameters().len();
    // The observations are read last to first, so each one joins the product
    // of those after it.
    let mut read = Maybe::Absent(reading::Absent::Unread);
    for &observation in signature.observations().iter().rev() {
        let mut instantiated = observation;
        for index in (0 .. count).rev() {
            let carried = carried(context, head, ParameterAt(index))?;
            instantiated =
                gandr_core_term::instantiate_comp_type(context.arena_mut(), instantiated, carried);
        }
        read = Maybe::Present(match read {
            Maybe::Present(rest) => context.arena_mut().comp_type_with(instantiated, rest),
            Maybe::Absent(_) => instantiated,
        });
    }
    let Maybe::Present(read) = read
    else {
        return Err(refused(head, CodataFault::WithoutObservations));
    };
    context.whnf_comp_type(read)
}

quenchant_shape::reason_enum! {
    /// Why a codata application has no reading yet.
    mod reading {
        /// The reason it has none.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No observation has been read.
            Unread,
        }
    }
}
