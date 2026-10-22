use alloc::vec;

use gandr_core_nbe::Calls;
use gandr_core_term::CertificateEquality;
use gandr_core_term::CompTypeId;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::effect::EffectRow;
use gandr_core_term::effect::host::divergence;
use gandr_core_term::equal_comp_type_syntax;
use gandr_kernel_conversion_trace::ConversionDecision;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FieldCount;
use gandr_kernel_term::FixpointEvidence;
use gandr_kernel_term::OperationNode;
use gandr_kernel_term::OperationRule;
use gandr_kernel_term::OperationRules;
use gandr_kernel_term::RuleVariable;
use quenchant_shape::shape::Maybe;

use super::Divergence;
use super::calls;
use super::returning;
use super::stated;
use crate::context::CheckBudget;
use crate::context::CheckingContext;
use crate::declaration::Declaration;
use crate::declaration::OriginToken;
use crate::module::Judged;
use crate::module::Verdict;
use crate::module::check_module;
use crate::refusal::CheckRefusal;
use crate::refusal::Mismatch;

/// `F^⟨Div⟩ A`.
///
/// # Specification
/// trivial.
fn diverging(
    arena: &mut CoreArena,
    result: ValueTypeId,
) -> CompTypeId
{
    arena.comp_type_returner_with_effects(result, EffectRow::singleton(divergence()))
}

/// `thunk(fix f. λx. body)` with partial evidence, declared at `U (Unit →
/// returner)`, at position `at`.
///
/// # Specification
/// trivial.
fn looping(
    arena: &mut CoreArena,
    at: ConstantIndex,
    returner: CompTypeId,
    body: ComputationId,
) -> (Declaration, ComputationId, CompTypeId)
{
    let unit = arena.value_type_unit();
    let arrow = arena.comp_type_arrow(unit, returner);
    let declared = arena.value_type_thunk(arrow);
    let lambda = arena.computation_lambda(body);
    let fixpoint = arena.computation_fixpoint(lambda, FixpointEvidence::Partial);
    let thunk = arena.value_thunk(fixpoint);
    let declaration = Declaration::new(
        at,
        Maybe::Present(declared),
        Maybe::Present(thunk),
        OriginToken::from(usize::from(at)),
    );
    (declaration, fixpoint, arrow)
}

/// `(force f) x` under the fixpoint's binder `f` and the lambda's `x`.
///
/// # Specification
/// trivial.
fn again(arena: &mut CoreArena) -> ComputationId
{
    let own = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
    let argument = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let forced = arena.computation_force(own);
    arena.computation_application(forced, argument)
}

/// The verdict of each declaration of `declarations`, judged as one module.
///
/// # Specification
/// trivial.
fn verdicts(
    arena: &mut CoreArena,
    declarations: &[Declaration],
) -> alloc::vec::Vec<Verdict>
{
    let mut context = CheckingContext::new(arena, CheckBudget::DEFAULT);
    check_module(&mut context, declarations)
        .judged()
        .iter()
        .map(Judged::verdict)
        .collect()
}

#[test]
fn a_partial_fixpoint_states_div_in_every_row_it_ends_in()
{
    let mut arena = CoreArena::new();
    let unit = arena.value_type_unit();
    let pure = arena.comp_type_returner(unit);
    let stated_row = diverging(&mut arena, unit);
    let body = again(&mut arena);
    let (bare, fixpoint, expected) = looping(&mut arena, ConstantIndex::from(0_usize), pure, body);
    let (holding, ..) = looping(&mut arena, ConstantIndex::from(1_usize), stated_row, body);
    let verdicts = verdicts(&mut arena, &[bare, holding]);
    let &[
        Verdict::Refused(CheckRefusal::TypeMismatch(Mismatch::Computation {
            at,
            synthesised,
            expected: wanted,
        })),
        Verdict::Checked { .. },
    ] = verdicts.as_slice()
    else {
        panic!("a loop at the empty row is refused and one stating `Div` checks: {verdicts:?}");
    };
    assert_eq!(
        (at, wanted),
        (fixpoint, expected),
        "the refusal stands at the fixpoint, against its declared type"
    );
    let rebuilt = arena.comp_type_arrow(unit, stated_row);
    assert_eq!(
        equal_comp_type_syntax(&arena, synthesised, rebuilt),
        CertificateEquality::Equal,
        "the refusal names the type with `Div` in its row"
    );

    // Through a lazy product, only the component that lacks the entry gains it.
    let with = arena.comp_type_with(&[pure, stated_row]);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let answer = stated(&mut context, fixpoint, with);
    let both = arena.comp_type_with(&[stated_row, stated_row]);
    let Ok(Divergence::Unstated(rebuilt)) = answer
    else {
        panic!("a lazy product with a pure component does not state `Div`: {answer:?}");
    };
    assert_eq!(
        equal_comp_type_syntax(&arena, rebuilt, both),
        CertificateEquality::Equal,
        "each component ends in a row holding `Div`"
    );
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    assert_eq!(
        stated(&mut context, fixpoint, both),
        Ok(Divergence::Stated),
        "a lazy product whose every component holds `Div` states it"
    );
}

/// A dependent arrow states `Div` where its codomain does, and gains it
/// there otherwise; a decode no definition unfolds has no returner to
/// state it in and is refused for wanting one.
#[test]
fn a_dependent_arrow_states_div_in_its_codomain_and_a_stuck_decode_is_refused()
{
    use gandr_kernel_strata::Level;

    use crate::refusal::ExpectedShape;
    use crate::refusal::TermNode;

    let mut arena = CoreArena::new();
    let unit = arena.value_type_unit();
    let pure = arena.comp_type_returner(unit);
    let stated_row = diverging(&mut arena, unit);
    let at = again(&mut arena);
    let pi = arena.comp_type_pi(unit, pure);
    let stated_pi = arena.comp_type_pi(unit, stated_row);
    let code = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let stuck = arena.comp_type_element(code, Level::zero());
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let answer = stated(&mut context, at, pi);
    let Ok(Divergence::Unstated(rebuilt)) = answer
    else {
        panic!("a dependent arrow to a pure returner does not state `Div`: {answer:?}");
    };
    assert_eq!(
        equal_comp_type_syntax(context.arena(), rebuilt, stated_pi),
        CertificateEquality::Equal,
        "the codomain gains `Div`"
    );
    assert_eq!(
        stated(&mut context, at, stated_pi),
        Ok(Divergence::Stated),
        "a dependent arrow whose codomain holds `Div` states it"
    );
    assert!(
        matches!(
            stated(&mut context, at, stuck),
            Err(CheckRefusal::ShapeMismatch {
                at: TermNode::Computation(refused),
                wanted: ExpectedShape::Returner,
                ..
            }) if refused == at
        ),
        "a stuck decode has no returner"
    );
}

#[test]
fn a_fixpoint_that_never_recurses_needs_no_entry()
{
    let mut arena = CoreArena::new();
    let unit = arena.value_type_unit();
    let pure = arena.comp_type_returner(unit);
    let argument = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let returned = arena.computation_return(argument);
    let (once, ..) = looping(&mut arena, ConstantIndex::from(0_usize), pure, returned);
    let verdicts = verdicts(&mut arena, &[once]);
    assert!(
        matches!(*verdicts.as_slice(), [Verdict::Checked { .. }]),
        "a fixpoint whose body never names itself runs its body once: {verdicts:?}"
    );
}

#[test]
fn no_handler_discharges_div()
{
    let mut arena = CoreArena::new();
    let unit = arena.value_type_unit();
    let pure = arena.comp_type_returner(unit);
    let stated_row = diverging(&mut arena, unit);
    // `handle Div { (fix f. force f : F^⟨Div⟩ 1) } with { return x ↦ return x }`.
    let own = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let forced = arena.computation_force(own);
    let fixpoint = arena.computation_fixpoint(forced, FixpointEvidence::Partial);
    let subject = arena.computation_ascribe(fixpoint, stated_row);
    let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let returned = arena.computation_return(bound);
    let handled = arena.computation_handle(divergence(), subject, returned, [].into());
    // The same subject under a capability scope of `Div`, its binder unused.
    let scoped = arena.computation_scope(divergence(), subject, returned, [].into());
    let declare = |arena: &mut CoreArena, at: ConstantIndex, returner: CompTypeId, term| {
        let declared = arena.value_type_thunk(returner);
        let body = arena.value_thunk(term);
        Declaration::new(
            at,
            Maybe::Present(declared),
            Maybe::Present(body),
            OriginToken::from(usize::from(at)),
        )
    };
    let tamed = declare(&mut arena, ConstantIndex::from(0_usize), pure, handled);
    let kept = declare(
        &mut arena,
        ConstantIndex::from(1_usize),
        stated_row,
        handled,
    );
    let scope_tamed = declare(&mut arena, ConstantIndex::from(2_usize), pure, scoped);
    let scope_kept = declare(&mut arena, ConstantIndex::from(3_usize), stated_row, scoped);
    let verdicts = verdicts(&mut arena, &[tamed, kept, scope_tamed, scope_kept]);
    assert!(
        matches!(
            *verdicts.as_slice(),
            [
                Verdict::Refused(CheckRefusal::TypeMismatch(Mismatch::Computation { at: handler, .. })),
                Verdict::Checked { .. },
                Verdict::Refused(CheckRefusal::TypeMismatch(Mismatch::Computation { at: run, .. })),
                Verdict::Checked { .. },
            ] if handler == handled && run == subject
        ),
        "a handler or a scope of `Div` leaves it in the row it answers at: {verdicts:?}"
    );
}

#[test]
fn a_ruled_operation_terminates_by_its_rules()
{
    let own = ConstantIndex::from(0_usize);
    let call = OperationNode::Operation {
        constant: own,
        arity: FieldCount::from(1_usize),
    };
    let x = OperationNode::Variable(RuleVariable::from(0_u32));
    let rules = OperationRules::new(vec![OperationRule::new(
        alloc::boxed::Box::from([call, x].as_slice()),
        alloc::boxed::Box::from([x].as_slice()),
    )]);
    let mut arena = CoreArena::new();
    let unit = arena.value_type_unit();
    let pure = arena.comp_type_returner(unit);
    let body = again(&mut arena);
    let (operation, ..) = looping(&mut arena, own, pure, body);
    let verdicts = verdicts(&mut arena, &[operation.ruled(rules)]);
    assert!(
        matches!(*verdicts.as_slice(), [Verdict::Checked { .. }]),
        "a ruled operation's fixpoint needs no entry: the kernel orients its rules: {verdicts:?}"
    );
}

#[test]
fn a_call_returns_only_where_every_row_is_empty()
{
    let mut arena = CoreArena::new();
    let unit = arena.value_type_unit();
    let pure = arena.comp_type_returner(unit);
    let stated_row = diverging(&mut arena, unit);
    let function = arena.comp_type_arrow(unit, pure);
    let partial = arena.comp_type_arrow(unit, stated_row);
    let both_pure = arena.comp_type_with(&[pure, function]);
    let one_partial = arena.comp_type_with(&[pure, partial]);
    let rows = [
        (arena.value_type_thunk(function), Calls::Return),
        (arena.value_type_thunk(both_pure), Calls::Return),
        (arena.value_type_thunk(partial), Calls::Unknown),
        (arena.value_type_thunk(one_partial), Calls::Unknown),
        (unit, Calls::Unknown),
    ];
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    for (bound, answer) in rows {
        assert_eq!(
            calls(&mut context, bound),
            Ok(answer),
            "a thunk's calls return when each returner it reaches has the empty row; anything else \
             is unknown: {bound:?}"
        );
    }
}

#[test]
fn an_unread_call_converts_only_where_its_row_is_empty()
{
    // Under `f` and `g`, `thunk (λx. force g x to v. force f x)` against `f`:
    // the call of `g` is dropped exactly when `g`'s row is empty.
    let mut arena = CoreArena::new();
    let unit = arena.value_type_unit();
    let pure = arena.comp_type_returner(unit);
    let stated_row = diverging(&mut arena, unit);
    let function = arena.comp_type_arrow(unit, pure);
    let function = arena.value_type_thunk(function);
    let partial = arena.comp_type_arrow(unit, stated_row);
    let partial = arena.value_type_thunk(partial);
    let variable = |arena: &mut CoreArena, index: u32| {
        arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(index))
    };
    let call = |arena: &mut CoreArena, (function, argument): (u32, u32)| {
        let function = variable(arena, function);
        let forced = arena.computation_force(function);
        let argument = variable(arena, argument);
        arena.computation_application(forced, argument)
    };
    let dropped = call(&mut arena, (1, 0));
    let followed = call(&mut arena, (3, 1));
    let bound = arena.computation_bind(dropped, followed);
    let lambda = arena.computation_lambda(bound);
    let point = arena.value_thunk(lambda);
    let endpoint = variable(&mut arena, 1);
    for (called, discarded) in [(function, true), (partial, false)] {
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        context.binders().open(Zone::Intuitionistic, function);
        context.binders().open(Zone::Intuitionistic, called);
        let returning = returning(&mut context).expect("both binders are formed");
        let related =
            context
                .definitions()
                .relate_terms(context.arena(), point, endpoint, &returning);
        let found = match related {
            Ok(Maybe::Present(ref decisions)) => decisions
                .iter()
                .any(|decision| matches!(decision, ConversionDecision::Discard { .. })),
            Ok(Maybe::Absent(_)) | Err(_) => false,
        };
        assert_eq!(
            found, discarded,
            "the call converts away with the empty row and stands with `Div`: {returning:?} \
             {related:?}"
        );
    }
}
