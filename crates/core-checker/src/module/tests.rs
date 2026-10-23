use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::CoreArena;
use gandr_core_term::FailureClass;
use gandr_core_term::Sort;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::effect::Purity;
use gandr_kernel_strata::Level;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::SealExtent;
use quenchant_shape::shape::Maybe;

use super::ModuleRun;
use super::Verdict;
use super::check_declaration;
use super::check_module;
use super::type_module;
use crate::context::Atom;
use crate::context::CheckBudget;
use crate::context::CheckingContext;
use crate::context::Formations;
use crate::conversion::ConversionCount;
use crate::declaration::AbstractType;
use crate::declaration::Declaration;
use crate::declaration::OriginToken;
use crate::declaration::body;
use crate::declaration::signature;
use crate::failure::FrameRole;
use crate::failure::Pursuit;
use crate::failure::Stage;
use crate::failure::judged;
use crate::fixture::RetireAt;
use crate::fixture::integer_literal;
use crate::fixture::text_literal;
use crate::nested::Nesting;
use crate::refusal::CheckRefusal;
use crate::refusal::CheckingForm;
use crate::refusal::CoreNode;
use crate::refusal::Mismatch;
use crate::refusal::TermNode;
use crate::refusal::TypeNode;
use crate::refusal::UnadmittedFormer;
use crate::retire::Polled;
use crate::seal::ComponentOrdinal;
use crate::seal::SealSite;
use crate::seal::SealingSite;

/// An admission position in a fixture module.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct At(usize);

/// The declaration at `position`, its origin `position + 100`.
///
/// # Specification
/// - requires: adding the origin offset one hundred does not overflow.
/// - ensures: the fixture position and the distinct origin are retained
///   alongside the supplied signature and body.
/// - panics: the position lies outside the offset domain.
///
/// # Adequacy
/// - hypothesis: L3 — a module with all four declaration shapes observes
///   verdicts and displaced origins, separating a lost half or confusion
///   between admission position and diagnostic origin.
/// - witness: `module::tests::each_combination_of_halves_gets_its_verdict`
/// - witness: `module::tests::every_owed_hole_enters_the_ledger_in_order`
#[spec(
        requires: position.0.checked_add(100).is_some(),
        ensures: |ret| usize::from(ret.constant()) == position.0
            && Some(usize::from(ret.origin())) == position.0.checked_add(100)
            && matches!(ret.content(),&crate::DeclarationContent::Value {signature,body} if signature == declared && body == defined),
    )]
fn declaration(
    position: At,
    declared: Maybe<ValueTypeId, signature::Absent>,
    defined: Maybe<ValueId, body::Absent>,
) -> Declaration
{
    Declaration::new(
        ConstantIndex::from(position.0),
        declared,
        defined,
        OriginToken::from(position.0.checked_add(100).unwrap()),
    )
}

/// No declared type.
const UNSIGNED: Maybe<ValueTypeId, signature::Absent> = Maybe::Absent(signature::Absent::Unsigned);

/// No declared type: a source's run target.
const RUN_TARGET: Maybe<ValueTypeId, signature::Absent> =
    Maybe::Absent(signature::Absent::RunTarget);

/// No body.
const HOLE: Maybe<ValueId, body::Absent> = Maybe::Absent(body::Absent::Hole);

#[test]
fn each_combination_of_halves_gets_its_verdict()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let zero = arena.value_literal(integer_literal());
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let Verdict::Checked {
        declared,
        body,
        evidence,
    } = check_declaration(
        &mut context,
        &declaration(At(0), Maybe::Present(integer), Maybe::Present(zero)),
    )
    else {
        panic!("a signature and a body check");
    };
    assert_eq!(
        (declared.id(), body),
        (integer, zero),
        "the verdict carries the declared type and the body it checked"
    );
    assert_eq!(
        evidence.conversions(),
        ConversionCount::from(1_usize),
        "the literal crossed the value bridge once"
    );
    let Verdict::Owed(entry) = check_declaration(
        &mut context,
        &declaration(At(1), Maybe::Present(integer), HOLE),
    )
    else {
        panic!("a signature over a hole is owed");
    };
    assert_eq!(
        (
            entry.absence().constant(),
            entry.absence().declared().id(),
            entry.absence().origin()
        ),
        (
            ConstantIndex::from(1_usize),
            integer,
            OriginToken::from(101_usize)
        ),
        "the hole in checking position absorbs the declared type and owes it"
    );
    let Verdict::Synthesised { body, synthesised } = check_declaration(
        &mut context,
        &declaration(At(2), UNSIGNED, Maybe::Present(zero)),
    )
    else {
        panic!("a body alone synthesises");
    };
    assert_eq!(
        (body, synthesised.produced()),
        (zero, context.atom(Atom::Integer)),
        "the unsigned literal synthesises its atom, and the verdict carries the body"
    );
    assert_eq!(
        check_declaration(&mut context, &declaration(At(3), UNSIGNED, HOLE)),
        Verdict::Refused(CheckRefusal::NotSynthesisable {
            form: CheckingForm::Hole(ConstantIndex::from(3_usize)),
        }),
        "a hole in synthesis position has nothing to absorb and is refused"
    );
}

#[test]
fn an_admission_out_of_order_is_refused()
{
    let mut arena = CoreArena::new();
    let zero = arena.value_literal(integer_literal());
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    assert!(
        matches!(
            check_declaration(
                &mut context,
                &declaration(At(1), UNSIGNED, Maybe::Present(zero))
            ),
            Verdict::Synthesised { .. }
        ),
        "the first admission may take any position"
    );
    for repeated in [1_usize, 0_usize] {
        let verdict = check_declaration(
            &mut context,
            &declaration(At(repeated), UNSIGNED, Maybe::Present(zero)),
        );
        assert_eq!(
            verdict,
            Verdict::Refused(CheckRefusal::AdmissionOrder {
                constant: ConstantIndex::from(repeated),
                admitted: ConstantIndex::from(1_usize),
            }),
            "a position not above every admitted one is refused with both positions"
        );
        let Verdict::Refused(refusal) = verdict
        else {
            panic!("refused above");
        };
        assert_eq!(
            refusal.classify(),
            FailureClass::EngineFault,
            "an admission out of order is the producer's fault"
        );
    }
}

#[test]
fn a_declaration_cannot_read_its_own_type()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let itself = arena.value_constant(ConstantIndex::from(0_usize));
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let verdict = check_declaration(
        &mut context,
        &declaration(At(0), Maybe::Present(integer), Maybe::Present(itself)),
    );
    assert_eq!(
        verdict,
        Verdict::Refused(CheckRefusal::UnknownConstant {
            at: itself,
            constant: ConstantIndex::from(0_usize),
        }),
        "a body sees only the declarations strictly before it, so self-reference finds no type"
    );
    let Verdict::Refused(refusal) = verdict
    else {
        panic!("refused above");
    };
    assert_eq!(
        refusal.classify(),
        FailureClass::MalformedSource,
        "an unknown constant is the author's"
    );
}

#[test]
fn a_refused_signed_body_still_supplies_its_type()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let text = arena.value_literal(text_literal());
    let earlier = arena.value_constant(ConstantIndex::from(0_usize));
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    assert!(
        matches!(
            check_declaration(
                &mut context,
                &declaration(At(0), Maybe::Present(integer), Maybe::Present(text))
            ),
            Verdict::Refused(CheckRefusal::TypeMismatch(Mismatch::Value { .. }))
        ),
        "the text does not have the declared integer type"
    );
    let Verdict::Synthesised { synthesised, .. } = check_declaration(
        &mut context,
        &declaration(At(1), UNSIGNED, Maybe::Present(earlier)),
    )
    else {
        panic!("the reference synthesises");
    };
    assert_eq!(
        synthesised.produced().id(),
        integer,
        "the declared type is the contract a later reference reads, whatever the body did"
    );
}

#[test]
fn a_body_that_synthesised_nothing_supplies_no_type()
{
    let mut arena = CoreArena::new();
    let zero = arena.value_literal(integer_literal());
    let returned = arena.computation_return(zero);
    let thunk = arena.value_thunk(returned);
    let earlier = arena.value_constant(ConstantIndex::from(0_usize));
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    assert_eq!(
        check_declaration(
            &mut context,
            &declaration(At(0), UNSIGNED, Maybe::Present(thunk))
        ),
        Verdict::Refused(CheckRefusal::NotSynthesisable {
            form: CheckingForm::Thunk(thunk),
        }),
        "an unsigned thunk does not synthesise"
    );
    assert_eq!(
        context.signature(ConstantIndex::from(0_usize)),
        Maybe::Absent(crate::context::signature_table::Absent::Untyped),
        "the refused body supplied no type"
    );
    assert_eq!(
        check_declaration(
            &mut context,
            &declaration(At(1), UNSIGNED, Maybe::Present(earlier))
        ),
        Verdict::Refused(CheckRefusal::UnknownConstant {
            at: earlier,
            constant: ConstantIndex::from(0_usize),
        }),
        "a reference to it finds no type"
    );
}

#[test]
fn a_run_target_has_the_thunk_type_an_unsigned_thunk_lacks_1105()
{
    // The thunk an unsigned declaration refuses is, as a source's run target,
    // typed by the computation it suspends, and enters the table at that
    // type for a later reference to read.
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let returns_integer = arena.comp_type_returner(integer);
    let suspended = arena.value_type_thunk(returns_integer);
    let zero = arena.value_literal(integer_literal());
    let returned = arena.computation_return(zero);
    let thunk = arena.value_thunk(returned);
    let target = arena.value_constant(ConstantIndex::from(1_usize));
    let forced = arena.computation_force(zero);
    let ill_typed = arena.value_thunk(forced);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    assert_eq!(
        check_declaration(
            &mut context,
            &declaration(At(0), UNSIGNED, Maybe::Present(thunk))
        ),
        Verdict::Refused(CheckRefusal::NotSynthesisable {
            form: CheckingForm::Thunk(thunk),
        }),
        "unsigned, the thunk does not synthesise"
    );
    let Verdict::Synthesised { synthesised, body } = check_declaration(
        &mut context,
        &declaration(At(1), RUN_TARGET, Maybe::Present(thunk)),
    )
    else {
        panic!("as a run target, the thunk synthesises");
    };
    assert_eq!(
        (body, context.signature(ConstantIndex::from(1_usize))),
        (thunk, Maybe::Present(synthesised.produced())),
        "the run target enters the table at the type it synthesised"
    );
    assert!(
        matches!(
            check_declaration(
                &mut context,
                &declaration(At(2), Maybe::Present(suspended), Maybe::Present(target))
            ),
            Verdict::Checked { .. }
        ),
        "a reference to the run target reads the thunk of a computation returning an integer"
    );
    assert!(
        matches!(
            check_declaration(
                &mut context,
                &declaration(At(3), RUN_TARGET, Maybe::Present(ill_typed))
            ),
            Verdict::Refused(CheckRefusal::ShapeMismatch { .. })
        ),
        "a run target whose computation does not synthesise refuses as the computation does"
    );
}

#[test]
fn a_later_declaration_reads_an_earlier_type()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let returns_integer = arena.comp_type_returner(integer);
    let thunk_type = arena.value_type_thunk(returns_integer);
    let zero = arena.value_literal(integer_literal());
    let returned = arena.computation_return(zero);
    let thunk = arena.value_thunk(returned);
    let suspended = arena.value_constant(ConstantIndex::from(0_usize));
    let owed = arena.value_constant(ConstantIndex::from(1_usize));
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let module = [
        declaration(At(0), Maybe::Present(thunk_type), Maybe::Present(thunk)),
        declaration(At(1), Maybe::Present(integer), HOLE),
        declaration(At(2), UNSIGNED, Maybe::Present(suspended)),
        declaration(At(3), Maybe::Present(integer), Maybe::Present(owed)),
    ];
    let report = check_module(&mut context, &module);
    let verdicts: Vec<_> = report.judged().iter().map(super::Judged::verdict).collect();
    assert!(
        matches!(verdicts[2], Verdict::Synthesised { synthesised, .. } if synthesised.produced().id() == thunk_type),
        "a reference synthesises the exact type its declaration supplied"
    );
    assert!(
        matches!(verdicts[3], Verdict::Checked { .. }),
        "an owed declaration supplies its declared type to later references"
    );
    assert_eq!(
        context
            .signature(ConstantIndex::from(1_usize))
            .map(crate::formation::FormedValueType::id),
        Maybe::Present(integer),
        "the table holds the owed declaration's type"
    );
}

#[test]
fn an_ascription_keeps_the_endpoints_it_related()
{
    // def k : U (Integer -> F Integer) = thunk { \x. return x } ;
    // def j : U (Integer -> F Integer) = k ;
    // def given : Path(U (…), thunk { force j }, k) = here(k) ;
    // def law : Path(U (…), k, k) = given ;
    // def again : Path(U (…), thunk { force j }, k) = given ;
    // `law`'s ascription relates `thunk { force j }` to `k`, unfolding `j`
    // under the thunk; `again`'s endpoints are the same syntax.
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let returns = arena.comp_type_returner(integer);
    let arrow = arena.comp_type_arrow(integer, returns);
    let function = arena.value_type_thunk(arrow);
    let bound = arena.value_variable(
        gandr_core_term::Zone::Intuitionistic,
        DeBruijnIndex::from(0_u32),
    );
    let returned = arena.computation_return(bound);
    let lambda = arena.computation_lambda(returned);
    let identity = arena.value_thunk(lambda);
    let [k, j, given] = [0_usize, 1, 2].map(|at| arena.value_constant(ConstantIndex::from(at)));
    let forced = arena.computation_force(j);
    let delayed = arena.value_thunk(forced);
    let stated = arena.value_type_path(function, delayed, k);
    let diagonal = arena.value_type_path(function, k, k);
    let here = arena.value_here(k);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let module = [
        declaration(At(0), Maybe::Present(function), Maybe::Present(identity)),
        declaration(At(1), Maybe::Present(function), Maybe::Present(k)),
        declaration(At(2), Maybe::Present(stated), Maybe::Present(here)),
        declaration(At(3), Maybe::Present(diagonal), Maybe::Present(given)),
        declaration(At(4), Maybe::Present(stated), Maybe::Present(given)),
    ];
    let report = check_module(&mut context, &module);
    assert!(
        report
            .judged()
            .iter()
            .all(|judged| matches!(judged.verdict(), Verdict::Checked { .. })),
        "every declaration checks: {:?}",
        report.judged()
    );
    assert_eq!(
        report.relations().keys().copied().collect::<Vec<_>>(),
        [ConstantIndex::from(3_usize)],
        "only the ascription whose endpoints differ keeps a pair"
    );
    let relations = report
        .relations()
        .get(&ConstantIndex::from(3_usize))
        .expect("the law's pairs");
    let [ref relation] = *relations.as_slice()
    else {
        panic!("one pair of endpoints differs: {relations:?}");
    };
    assert_eq!(
        (relation.left(), relation.right()),
        (delayed, k),
        "the pair is the synthesised endpoint against the declared one"
    );
    assert!(
        relation.decisions().iter().any(|decision| matches!(
            decision,
            gandr_kernel_conversion_trace::ConversionDecision::Unfold { .. }
        )),
        "the derivation names the unfoldings the kernel replays"
    );
}

#[test]
fn a_refusal_does_not_stop_the_run()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let zero = arena.value_literal(integer_literal());
    let text = arena.value_literal(text_literal());
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let module = [
        declaration(At(0), Maybe::Present(integer), Maybe::Present(text)),
        declaration(At(1), Maybe::Present(integer), Maybe::Present(zero)),
        declaration(At(2), Maybe::Present(integer), HOLE),
        declaration(At(3), UNSIGNED, HOLE),
        declaration(At(4), UNSIGNED, Maybe::Present(zero)),
    ];
    let report = check_module(&mut context, &module);
    let judged = report.judged();
    for (entry, offered) in judged.iter().zip(&module) {
        assert_eq!(
            (entry.constant(), entry.origin()),
            (offered.constant(), offered.origin()),
            "each verdict echoes its declaration's position and origin, in order"
        );
    }
    let [
        ref mismatched,
        ref checked,
        ref owed,
        ref unsigned_hole,
        ref synthesised,
    ] = *judged
    else {
        panic!("every declaration gets a verdict");
    };
    assert!(
        matches!(
            mismatched.verdict(),
            Verdict::Refused(CheckRefusal::TypeMismatch(_))
        ),
        "the first declaration is refused"
    );
    assert!(
        matches!(checked.verdict(), Verdict::Checked { .. }),
        "the next is judged on its own"
    );
    assert!(
        matches!(owed.verdict(), Verdict::Owed(_)),
        "the signed hole is owed"
    );
    assert!(
        matches!(
            unsigned_hole.verdict(),
            Verdict::Refused(CheckRefusal::NotSynthesisable { .. })
        ),
        "the unsigned hole is refused"
    );
    assert!(
        matches!(synthesised.verdict(), Verdict::Synthesised { .. }),
        "and the run goes on past it"
    );
}

/// #1663: a run polled to retirement before its second declaration judges and
/// settles the first alone, and answers what retired it; a run whose poll
/// never retires it judges every declaration, polled once before each, and
/// reports as the run nobody polls.
#[test]
fn a_retired_run_judges_nothing_after_its_poll_1663()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let zero = arena.value_literal(integer_literal());
    let module = [
        declaration(At(0), Maybe::Present(integer), Maybe::Present(zero)),
        declaration(At(1), Maybe::Present(integer), Maybe::Present(zero)),
        declaration(At(2), Maybe::Present(integer), HOLE),
    ];
    let mut whole_arena = arena.clone();
    let whole = {
        let mut context = CheckingContext::new(&mut whole_arena, CheckBudget::DEFAULT);
        let mut run = ModuleRun::new();
        run.judge(&mut context, &module, |_, _, _| {});
        run.finish(&mut context)
    };

    let mut retired_arena = arena.clone();
    let mut context = CheckingContext::new(&mut retired_arena, CheckBudget::DEFAULT);
    let mut run = ModuleRun::new();
    let mut settled = Vec::new();
    let at_second = RetireAt {
        at: 2,
        readings: core::cell::Cell::new(0),
    };
    let retired = run.judge_retiring(
        &mut context,
        &module,
        |_, declaration, _| settled.push(declaration.constant()),
        &at_second,
    );
    assert_eq!(
        retired,
        Polled::Retired((), ()),
        "the poll before the second declaration retires the run"
    );
    assert_eq!(
        at_second.readings.get(),
        2,
        "polled before the first declaration and the second, never the third"
    );
    assert_eq!(
        settled,
        [ConstantIndex::from(0_usize)],
        "the first declaration alone is settled"
    );
    assert_eq!(run.judged.len(), 1, "and judged");

    let mut polled_arena = arena;
    let never = RetireAt {
        at: 4,
        readings: core::cell::Cell::new(0),
    };
    let (answer, polled) = {
        let mut context = CheckingContext::new(&mut polled_arena, CheckBudget::DEFAULT);
        let mut run = ModuleRun::new();
        let answer = run.judge_retiring(&mut context, &module, |_, _, _| {}, &never);
        (answer, run.finish(&mut context))
    };
    assert_eq!(
        answer,
        Polled::Whole(()),
        "a poll never retired answers whole"
    );
    assert_eq!(
        never.readings.get(),
        3,
        "polled once before each declaration"
    );
    assert_eq!(polled, whole, "and reports as the run nobody polls");
    assert_eq!(polled_arena, whole_arena, "over the arena it mints");
}

#[test]
fn every_owed_hole_enters_the_ledger_in_order()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let string = arena.value_type_base(BaseType::String);
    let zero = arena.value_literal(integer_literal());
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let module = [
        declaration(At(0), Maybe::Present(integer), Maybe::Present(zero)),
        declaration(At(1), Maybe::Present(string), HOLE),
        declaration(At(2), UNSIGNED, Maybe::Present(zero)),
        declaration(At(3), Maybe::Present(integer), HOLE),
    ];
    let report = check_module(&mut context, &module);
    let owed: Vec<_> = report
        .ledger()
        .entries()
        .iter()
        .map(|entry| {
            let absence = entry.absence();
            (
                absence.constant(),
                absence.declared().id(),
                absence.origin(),
            )
        })
        .collect();
    assert_eq!(
        owed,
        [
            (
                ConstantIndex::from(1_usize),
                string,
                OriginToken::from(101_usize)
            ),
            (
                ConstantIndex::from(3_usize),
                integer,
                OriginToken::from(103_usize)
            ),
        ],
        "the ledger holds each owed hole, in module order"
    );
    assert_eq!(
        usize::from(report.ledger().count()),
        2_usize,
        "the count is the holes owed"
    );
}

#[test]
fn a_refusal_never_enters_the_ledger()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let unformed = arena.value_type_base(BaseType::Numeric);
    let text = arena.value_literal(text_literal());
    let unknown = arena.value_constant(ConstantIndex::from(9_usize));
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let module = [
        declaration(At(0), Maybe::Present(integer), Maybe::Present(text)),
        declaration(At(1), UNSIGNED, HOLE),
        declaration(At(2), UNSIGNED, Maybe::Present(unknown)),
        declaration(At(3), Maybe::Present(unformed), HOLE),
        declaration(At(3), Maybe::Present(integer), HOLE),
    ];
    let report = check_module(&mut context, &module);
    assert!(
        report
            .judged()
            .iter()
            .all(|entry| matches!(entry.verdict(), Verdict::Refused(_))),
        "every declaration of this module is refused"
    );
    assert_eq!(
        report.judged()[3].verdict(),
        Verdict::Refused(CheckRefusal::OutOfFragment {
            at: CoreNode::Type(TypeNode::Value(unformed)),
            former: UnadmittedFormer::NumericAtom,
        }),
        "a signed hole under an unformed signature is refused, not owed"
    );
    assert_eq!(
        usize::from(report.ledger().count()),
        0_usize,
        "a refusal of any class leaves the ledger empty"
    );
}

#[test]
fn a_refused_body_keeps_the_rules_it_was_refused_inside()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let unformed = arena.value_type_base(BaseType::Numeric);
    let itself = arena.value_constant(ConstantIndex::from(0_usize));
    let text = arena.value_literal(text_literal());
    let zero = arena.value_literal(integer_literal());
    let forced = arena.computation_force(zero);
    let thunk = arena.value_thunk(forced);
    let pair = arena.value_tuple(&[zero, thunk]);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let module = [
        declaration(At(0), Maybe::Present(integer), Maybe::Present(itself)),
        declaration(At(1), UNSIGNED, Maybe::Present(text)),
        declaration(At(2), Maybe::Present(unformed), Maybe::Present(text)),
        declaration(At(3), UNSIGNED, Maybe::Present(pair)),
    ];
    let report = check_module(&mut context, &module);
    assert_eq!(
        report.failures().keys().copied().collect::<Vec<_>>(),
        [ConstantIndex::from(0_usize), ConstantIndex::from(3_usize)],
        "the two refused bodies keep their failures; the accepted body and \
             the body under an unformed signature, never run, keep none"
    );
    let reference = &report.failures()[&ConstantIndex::from(0_usize)];
    assert_eq!(
        reference.refusal(),
        CheckRefusal::UnknownConstant {
            at: itself,
            constant: ConstantIndex::from(0_usize),
        },
        "the self-reference is refused before its type enters the table"
    );
    let [ref bridge] = *reference.obligations()
    else {
        panic!("one rule waits on the self-reference: {reference:?}");
    };
    assert_eq!(
        (bridge.role(), bridge.at()),
        (
            FrameRole::ValueBridge,
            CoreNode::Term(TermNode::Value(itself))
        ),
        "the check of the body waits on its synthesis, to cross the bridge"
    );
    assert!(
        matches!(bridge.expected(), Maybe::Present(TypeNode::Value(_))),
        "the body was checked against its declared type"
    );
    let synthesis = &report.failures()[&ConstantIndex::from(3_usize)];
    assert_eq!(
        synthesis
            .obligations()
            .iter()
            .map(|obligation| (obligation.role(), obligation.at()))
            .collect::<Vec<_>>(),
        [
            (
                FrameRole::NativeTuple,
                CoreNode::Term(TermNode::Value(pair))
            ),
            (
                FrameRole::NativeCollect,
                CoreNode::Term(TermNode::Value(pair))
            ),
        ],
        "the pair waits on its second component's type, outermost first"
    );
    assert_eq!(
        synthesis.pursuit(),
        Pursuit::new(
            CoreNode::Term(TermNode::Value(thunk)),
            Maybe::Absent(judged::Absent::Synthesised),
            Stage::Starting,
        ),
        "the thunk, which cannot synthesise, is the goal the refusal met"
    );
}

#[test]
fn a_typed_module_keeps_each_judged_body_s_term_types()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let product = arena.value_type_product(&[integer, integer]);
    let zero = arena.value_literal(integer_literal());
    let text = arena.value_literal(text_literal());
    let pair = arena.value_tuple(&[zero, text]);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let module = [
        declaration(At(0), UNSIGNED, Maybe::Present(zero)),
        declaration(At(1), Maybe::Present(product), Maybe::Present(pair)),
        declaration(At(2), Maybe::Present(integer), HOLE),
    ];
    let run = type_module(&mut context, &module);
    assert_eq!(
        run.refused().keys().copied().collect::<Vec<_>>(),
        [ConstantIndex::from(1_usize)],
        "the refused body's refusal is kept, and no other declaration's"
    );
    let typed = run.typings();
    assert_eq!(
        typed.keys().copied().collect::<Vec<_>>(),
        [
            ConstantIndex::from(0_usize),
            ConstantIndex::from(1_usize),
            ConstantIndex::from(2_usize)
        ],
        "both judged bodies are typed, and the hole's signature"
    );
    let owed = &typed[&ConstantIndex::from(2_usize)];
    assert!(
        owed.typings().is_empty()
            && owed
                .formed()
                .iter()
                .any(|formed| formed.ty == TypeNode::Value(integer)),
        "the hole judges no term; its signature is formed: {owed:?}"
    );
    let accepted = typed[&ConstantIndex::from(0_usize)].typings();
    assert_eq!(
        accepted
            .iter()
            .map(|typing| typing.term)
            .collect::<Vec<_>>(),
        [TermNode::Value(zero)],
        "the literal body is its only term"
    );
    let refused = &typed[&ConstantIndex::from(1_usize)];
    assert!(
        refused
            .typings()
            .iter()
            .any(|typing| typing.term == TermNode::Value(text)),
        "the refused component is typed where it was recovered"
    );
    assert_eq!(
        refused.typings().last().map(|typing| typing.term),
        Some(TermNode::Value(pair)),
        "the refused body itself finishes last"
    );
    assert_eq!(
        refused.marks().len(),
        1_usize,
        "the text component is the one mark"
    );
}

/// A typed run keys a declaration exactly when it formed or judged something,
/// refused or not: a formed data declaration and one refused at a field keep
/// the kind they formed, a signature refused at its second component keeps
/// the first, and a signature refused before forming anything is not keyed.
#[test]
fn a_typed_module_keys_what_each_run_formed()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let kind = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let dangling = crate::fixture::dangling_value_type();
    let partial = arena.value_type_product(&[integer, dangling]);
    let zero = arena.value_literal(integer_literal());
    let [formed, refused] = [Vec::new(), Vec::from([dangling])]
        .map(|fields| gandr_core_term::DataSignature::new(Vec::new(), Vec::from([fields]), kind));
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let module = [
        Declaration::data(
            ConstantIndex::from(0_usize),
            formed.into(),
            OriginToken::from(0_usize),
        ),
        Declaration::data(
            ConstantIndex::from(1_usize),
            refused.into(),
            OriginToken::from(1_usize),
        ),
        declaration(At(2), Maybe::Present(dangling), Maybe::Present(zero)),
        declaration(At(3), Maybe::Present(partial), Maybe::Present(zero)),
    ];
    let run = type_module(&mut context, &module);
    let typed = run.typings();
    assert_eq!(
        typed.keys().copied().collect::<Vec<_>>(),
        [
            ConstantIndex::from(0_usize),
            ConstantIndex::from(1_usize),
            ConstantIndex::from(3_usize)
        ],
        "a run that formed nothing is not keyed: {typed:?}"
    );
    for (constant, ty) in [(0_usize, kind), (1, kind), (3, integer)] {
        assert!(
            typed[&ConstantIndex::from(constant)]
                .formed()
                .iter()
                .any(|formed| formed.ty == TypeNode::Value(ty)),
            "the declaration at {constant} keeps what it formed: {typed:?}"
        );
    }
}

/// A declaration's judgement says why it carries no elaboration: a body
/// with no nested computation is unnested, and a first run that decided a
/// nesting and was refused is unaccepted.
#[test]
fn a_refused_first_run_leaves_its_nesting_unaccepted()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let pair = arena.value_type_product(&[integer, integer]);
    let (function, identity) = integer_function(&mut arena);
    let zero = arena.value_literal(integer_literal());
    let text = arena.value_literal(text_literal());
    let applied = call(&mut arena, ConstantIndex::from(0_usize), zero);
    let nested = arena.value_nested(applied);
    let refused = arena.value_tuple(&[nested, text]);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let plain = super::decide(
        &mut context,
        &declaration(At(0), Maybe::Present(function), Maybe::Present(identity)),
        super::Run::Judged,
    );
    assert!(
        matches!(plain.verdict, Verdict::Checked { .. })
            && matches!(
                plain.elaboration,
                Maybe::Absent(super::elaborated::Absent::Unnested)
            ),
        "a body with no nested computation is unnested: {plain:?}"
    );
    let unaccepted = super::decide(
        &mut context,
        &declaration(At(1), Maybe::Present(pair), Maybe::Present(refused)),
        super::Run::Judged,
    );
    assert!(
        matches!(unaccepted.verdict, Verdict::Refused(_))
            && matches!(
                unaccepted.elaboration,
                Maybe::Absent(super::elaborated::Absent::Unaccepted)
            ),
        "a refused first run that decided a nesting is unaccepted: {unaccepted:?}"
    );
}

#[test]
fn a_typed_module_keeps_the_terms_its_signature_judges()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let zero = arena.value_literal(integer_literal());
    let one = arena.value_literal(integer_literal());
    let path = arena.value_type_path(integer, zero, one);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let module = [declaration(At(0), Maybe::Present(path), HOLE)];
    let run = type_module(&mut context, &module);
    let judged = run.typings();
    let Some(owed) = judged.get(&ConstantIndex::from(0_usize))
    else {
        panic!("the signature's formation is kept");
    };
    for endpoint in [zero, one] {
        assert!(
            owed.typings()
                .iter()
                .any(|typing| typing.term == TermNode::Value(endpoint)
                    && typing.ty == TypeNode::Value(integer)),
            "each endpoint is kept at the carrier: {owed:?}"
        );
    }
    assert!(
        [path, integer].iter().all(|&ty| owed
            .formed()
            .iter()
            .any(|formed| formed.ty == TypeNode::Value(ty))),
        "the path type and its carrier are kept at their levels: {owed:?}"
    );
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let zero = arena.value_literal(integer_literal());
    let one = arena.value_literal(integer_literal());
    let path = arena.value_type_path(integer, zero, one);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    context.keep_formations(Formations::Firsts(Vec::from([TypeNode::Value(path)])));
    let module = [
        declaration(At(0), Maybe::Present(path), HOLE),
        declaration(At(1), Maybe::Present(path), HOLE),
    ];
    let run = type_module(&mut context, &module);
    let judged = run.typings();
    let formed = |at: usize| {
        judged.get(&ConstantIndex::from(at)).map(|owed| {
            owed.formed()
                .iter()
                .map(|formed| formed.ty)
                .collect::<Vec<_>>()
        })
    };
    assert_eq!(
        (formed(0_usize), formed(1_usize)),
        (Some(Vec::from([TypeNode::Value(path)])), Some(Vec::new())),
        "asked for the path type's first formation, the first signature keeps it and no other, and the second, forming it again, keeps nothing"
    );
}

/// `U (Integer -> F Integer)`, and the identity function of that type.
///
/// # Specification
/// trivial.
fn integer_function(arena: &mut CoreArena) -> (ValueTypeId, ValueId)
{
    let integer = arena.value_type_base(BaseType::Integer);
    let returns = arena.comp_type_returner(integer);
    let arrow = arena.comp_type_arrow(integer, returns);
    let function = arena.value_type_thunk(arrow);
    let argument = arena.value_variable(
        gandr_core_term::Zone::Intuitionistic,
        DeBruijnIndex::from(0_u32),
    );
    let returned = arena.computation_return(argument);
    let lambda = arena.computation_lambda(returned);
    (function, arena.value_thunk(lambda))
}

/// A call of the constant `callee`, forced, at `argument`.
///
/// # Specification
/// trivial.
fn call(
    arena: &mut CoreArena,
    callee: ConstantIndex,
    argument: ValueId,
) -> gandr_core_term::ComputationId
{
    let callee = arena.value_constant(callee);
    let forced = arena.computation_force(callee);
    arena.computation_application(forced, argument)
}

#[test]
fn a_nested_run_elaborates_into_a_bind_before_its_region()
{
    let mut arena = CoreArena::new();
    let (function, identity) = integer_function(&mut arena);
    let [inner_x, expected_x, expected_inner_r, expected_r] = [(); 4].map(|()| {
        arena.value_variable(
            gandr_core_term::Zone::Intuitionistic,
            DeBruijnIndex::from(0_u32),
        )
    });
    let inner = call(&mut arena, ConstantIndex::from(0_usize), inner_x);
    let inner = arena.value_nested(inner);
    let outer = call(&mut arena, ConstantIndex::from(0_usize), inner);
    let outer = arena.value_nested(outer);
    let returned = arena.computation_return(outer);
    let lambda = arena.computation_lambda(returned);
    let twice = arena.value_thunk(lambda);
    let expected = {
        let first = call(&mut arena, ConstantIndex::from(0_usize), expected_x);
        let second = call(&mut arena, ConstantIndex::from(0_usize), expected_inner_r);
        let ran = arena.computation_bind(first, second);
        let returned = arena.computation_return(expected_r);
        let bound = arena.computation_bind(ran, returned);
        let lambda = arena.computation_lambda(bound);
        arena.value_thunk(lambda)
    };
    let report = {
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        check_module(&mut context, &[
            declaration(At(0), Maybe::Present(function), Maybe::Present(identity)),
            declaration(At(1), Maybe::Present(function), Maybe::Present(twice)),
        ])
    };
    let Verdict::Checked { body, .. } = report.judged()[1].verdict()
    else {
        panic!("the nested calls check: {:?}", report.judged()[1].verdict());
    };
    assert_ne!(body, twice, "the verdict carries the elaborated body");
    assert_eq!(
        gandr_core_term::equal_certificate_syntax(&arena, body, expected),
        gandr_core_term::CertificateEquality::Equal,
        "the inner call runs inside the outer one's computation, and the outer before the return"
    );
    assert_eq!(
        report.definitions().get(&ConstantIndex::from(1_usize)),
        Some(&body),
        "the constant is defined as the elaborated body"
    );
    let elaboration = &report.nested_elaborations()[&ConstantIndex::from(1_usize)];
    assert_eq!(
        elaboration
            .decisions()
            .iter()
            .map(|(&at, &decided)| (at, decided))
            .collect::<Vec<_>>(),
        [
            (inner, Nesting::Ran(Purity::Pure)),
            (outer, Nesting::Ran(Purity::Pure))
        ],
        "both nested calls run, and neither performs an effect"
    );
    assert_eq!(
        elaboration
            .binds()
            .iter()
            .map(|&(run, _)| run)
            .collect::<Vec<_>>(),
        [inner, outer],
        "each run is reported beside the bind minted for it, the inner first"
    );
    assert!(
        elaboration
            .carried()
            .contains(&gandr_core_term::Carried::Value(twice, body)),
        "the rebuild reports the body it stands for the written one: {:?}",
        elaboration.carried()
    );
    assert!(
        !report
            .nested_elaborations()
            .contains_key(&ConstantIndex::from(0_usize)),
        "a body holding no nested computation is not elaborated"
    );
    let readmission = crate::bridge::readmit(&mut arena, &report);
    assert!(
        readmission.readmitted().iter().all(|readmitted| matches!(
            readmitted.outcome(),
            crate::bridge::Outcome::Defined { .. }
        )),
        "the kernel re-derives the elaborated body: {readmission:?}"
    );
}

/// A checked record update elaborates to the record of the fields its overlay
/// writes beside each kept field of its base, read off the base by a
/// projection; a base written as a call runs once, bound before the record,
/// and each kept field reads the record it bound. The kernel re-derives both
/// bodies.
#[test]
fn a_record_update_builds_its_base_s_kept_fields_beside_its_overlay()
{
    let mut arena = CoreArena::new();
    let label = |name: &str| gandr_kernel_term::FieldLabel::from(alloc::string::String::from(name));
    let integer = arena.value_type_base(BaseType::Integer);
    let string = arena.value_type_base(BaseType::String);
    let zero = arena.value_literal(integer_literal());
    let word = arena.value_literal(text_literal());
    let [bound, argument, expected_argument, expected_bound] = [(); 4].map(|()| {
        arena.value_variable(
            gandr_core_term::Zone::Intuitionistic,
            DeBruijnIndex::from(0_u32),
        )
    });
    // `r = #{a = 0, b = 0}` and `s = #{r | b = "", c = 0}`.
    let pair_type = arena.value_type_record(alloc::collections::BTreeMap::from([
        (label("a"), integer),
        (label("b"), integer),
    ]));
    let updated_type = arena.value_type_record(alloc::collections::BTreeMap::from([
        (label("a"), integer),
        (label("b"), string),
        (label("c"), integer),
    ]));
    let pair = arena.value_record(alloc::collections::BTreeMap::from([
        (label("a"), zero),
        (label("b"), zero),
    ]));
    let r = arena.value_constant(ConstantIndex::from(0_usize));
    let overlay = arena.value_record(alloc::collections::BTreeMap::from([
        (label("b"), word),
        (label("c"), zero),
    ]));
    let updated = arena.value_record_update(r, overlay);
    let kept_a = arena.computation_record_projection(r, label("a"));
    let kept_a = arena.value_returned(kept_a);
    let expected_updated = arena.value_record(alloc::collections::BTreeMap::from([
        (label("a"), kept_a),
        (label("b"), word),
        (label("c"), zero),
    ]));
    // `point = fn (n) { return #{a = n, b = n} }` and
    // `moved = fn (n) { return #{point(n) | a = 0} }`.
    let returns_pair = arena.comp_type_returner(pair_type);
    let to_pair = arena.comp_type_arrow(integer, returns_pair);
    let to_pair = arena.value_type_thunk(to_pair);
    let point = {
        let both = arena.value_record(alloc::collections::BTreeMap::from([
            (label("a"), bound),
            (label("b"), bound),
        ]));
        let returned = arena.computation_return(both);
        let lambda = arena.computation_lambda(returned);
        arena.value_thunk(lambda)
    };
    let written_a = arena.value_record(alloc::collections::BTreeMap::from([(label("a"), zero)]));
    let moved = {
        let called = call(&mut arena, ConstantIndex::from(2_usize), argument);
        let called = arena.value_nested(called);
        let update = arena.value_record_update(called, written_a);
        let returned = arena.computation_return(update);
        let lambda = arena.computation_lambda(returned);
        arena.value_thunk(lambda)
    };
    let expected_moved = {
        let called = call(&mut arena, ConstantIndex::from(2_usize), expected_argument);
        let kept_b = arena.computation_record_projection(expected_bound, label("b"));
        let kept_b = arena.value_returned(kept_b);
        let record = arena.value_record(alloc::collections::BTreeMap::from([
            (label("a"), zero),
            (label("b"), kept_b),
        ]));
        let returned = arena.computation_return(record);
        let bound = arena.computation_bind(called, returned);
        let lambda = arena.computation_lambda(bound);
        arena.value_thunk(lambda)
    };
    let report = {
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        check_module(&mut context, &[
            declaration(At(0), Maybe::Present(pair_type), Maybe::Present(pair)),
            declaration(At(1), Maybe::Present(updated_type), Maybe::Present(updated)),
            declaration(At(2), Maybe::Present(to_pair), Maybe::Present(point)),
            declaration(At(3), Maybe::Present(to_pair), Maybe::Present(moved)),
        ])
    };
    for (position, expected, what) in [
        (
            1_usize,
            expected_updated,
            "the kept `a` is read off `r` beside the written fields",
        ),
        (
            3_usize,
            expected_moved,
            "the call is bound once, and the kept `b` is read off the record it bound",
        ),
    ] {
        let Verdict::Checked { body, .. } = report.judged()[position].verdict()
        else {
            panic!(
                "the update checks: {:?}",
                report.judged()[position].verdict()
            );
        };
        assert_eq!(
            gandr_core_term::equal_certificate_syntax(&arena, body, expected),
            gandr_core_term::CertificateEquality::Equal,
            "{what}"
        );
    }
    let readmission = crate::bridge::readmit(&mut arena, &report);
    assert!(
        readmission.readmitted().iter().all(|readmitted| matches!(
            readmitted.outcome(),
            crate::bridge::Outcome::Defined { .. }
        )),
        "the kernel re-derives the built records: {readmission:?}"
    );
}

/// #2159: a record update written in a signature reads the record it builds,
/// so a path between two updates at distinct labels, or between an update
/// writing a field's own value and its base, holds at one point. The kernel
/// re-derives both.
#[test]
fn a_record_update_in_a_signature_reads_its_record_2159()
{
    let mut arena = CoreArena::new();
    let label = |name: &str| gandr_kernel_term::FieldLabel::from(alloc::string::String::from(name));
    let integer = arena.value_type_base(BaseType::Integer);
    let zero = arena.value_literal(integer_literal());
    // `point = #{x = 0, y = 0}`.
    let pair_type = arena.value_type_record(alloc::collections::BTreeMap::from([
        (label("x"), integer),
        (label("y"), integer),
    ]));
    let pair = arena.value_record(alloc::collections::BTreeMap::from([
        (label("x"), zero),
        (label("y"), zero),
    ]));
    let point = arena.value_constant(ConstantIndex::from(0_usize));
    let written = |arena: &mut CoreArena, base, name| {
        let overlay = arena.value_record(alloc::collections::BTreeMap::from([(label(name), zero)]));
        arena.value_record_update(base, overlay)
    };
    // `commute : Path(R, #{#{point | x = 0} | y = 0}, #{#{point | y = 0} | x =
    // 0})`.
    let commuted = {
        let first = written(&mut arena, point, "x");
        let left = written(&mut arena, first, "y");
        let second = written(&mut arena, point, "y");
        let right = written(&mut arena, second, "x");
        arena.value_type_path(pair_type, left, right)
    };
    let commute = arena.value_here(pair);
    // `unchanged : Path(R, #{point | x = 0}, point)`.
    let unchanged_type = {
        let left = written(&mut arena, point, "x");
        arena.value_type_path(pair_type, left, point)
    };
    let unchanged = arena.value_here(point);
    let report = {
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        check_module(&mut context, &[
            declaration(At(0), Maybe::Present(pair_type), Maybe::Present(pair)),
            declaration(At(1), Maybe::Present(commuted), Maybe::Present(commute)),
            declaration(
                At(2),
                Maybe::Present(unchanged_type),
                Maybe::Present(unchanged),
            ),
        ])
    };
    for (position, what) in [
        (1_usize, "updates at distinct labels commute"),
        (2_usize, "an update writing a field's own value is its base"),
    ] {
        assert!(
            matches!(report.judged()[position].verdict(), Verdict::Checked { .. }),
            "{what}: {:?}",
            report.judged()[position].verdict()
        );
    }
    let readmission = crate::bridge::readmit(&mut arena, &report);
    assert!(
        readmission.readmitted().iter().all(|readmitted| matches!(
            readmitted.outcome(),
            crate::bridge::Outcome::Defined { .. }
        )),
        "the kernel re-derives each built signature: {readmission:?}"
    );
}

#[test]
fn a_model_crosses_to_an_included_theory_s_by_its_reduct()
{
    let variable = |arena: &mut CoreArena, index: u32| {
        arena.value_variable(
            gandr_core_term::Zone::Intuitionistic,
            DeBruijnIndex::from(index),
        )
    };
    // The narrow pair keeps the first two of the wide nesting's three
    // components, as a theory included in another keeps some of its members.
    let check = |kept: &[ConstantIndex]| {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let narrow = arena.value_type_product(&[integer, integer]);
        let wide = arena.value_type_product(&[integer, narrow]);
        let thunk_of = |arena: &mut CoreArena, domain, result| {
            let returns = arena.comp_type_returner(result);
            let arrow = arena.comp_type_arrow(domain, returns);
            arena.value_type_thunk(arrow)
        };
        // `reduct = thunk(λm. split m as (a, r). split r as (b, c). return (a, b))`.
        let reduct_type = thunk_of(&mut arena, wide, narrow);
        let reduct = {
            let a = variable(&mut arena, 3);
            let b = variable(&mut arena, 1);
            let pair = arena.value_tuple(&[a, b]);
            let returned = arena.computation_return(pair);
            let pair_of = gandr_core_term::ComponentCount::from(2_usize);
            let rest = variable(&mut arena, 0);
            let inner = arena.computation_split(rest, pair_of, returned);
            let model = variable(&mut arena, 0);
            let outer = arena.computation_split(model, pair_of, inner);
            let lambda = arena.computation_lambda(outer);
            arena.value_thunk(lambda)
        };
        // `taker = thunk(λn. return 0)`, asking for the narrow pair.
        let taker_type = thunk_of(&mut arena, narrow, integer);
        let taker = {
            let zero = arena.value_literal(crate::fixture::integer_literal());
            let returned = arena.computation_return(zero);
            let lambda = arena.computation_lambda(returned);
            arena.value_thunk(lambda)
        };
        // `user = thunk(λm. taker(m))`, `m` the wide nesting.
        let user_type = thunk_of(&mut arena, wide, integer);
        let site = variable(&mut arena, 0);
        let user = {
            let called = call(&mut arena, ConstantIndex::from(1_usize), site);
            let lambda = arena.computation_lambda(called);
            arena.value_thunk(lambda)
        };
        // `thunk(λm. bind reduct(m) as n. taker(n))`.
        let expected = {
            let model = variable(&mut arena, 0);
            let reduced = call(&mut arena, ConstantIndex::from(0_usize), model);
            let bound = variable(&mut arena, 0);
            let called = call(&mut arena, ConstantIndex::from(1_usize), bound);
            let ran = arena.computation_bind(reduced, called);
            let lambda = arena.computation_lambda(ran);
            arena.value_thunk(lambda)
        };
        let report = {
            let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
            context.keep_reducts(kept);
            check_module(&mut context, &[
                declaration(At(0), Maybe::Present(reduct_type), Maybe::Present(reduct)),
                declaration(At(1), Maybe::Present(taker_type), Maybe::Present(taker)),
                declaration(At(2), Maybe::Present(user_type), Maybe::Present(user)),
            ])
        };
        (arena, report, site, expected)
    };
    let (mut arena, report, site, expected) = check(&[ConstantIndex::from(0_usize)]);
    let Verdict::Checked { body, .. } = report.judged()[2].verdict()
    else {
        panic!(
            "the wide nesting checks where the narrow pair is asked: {:?}",
            report.judged()[2].verdict()
        );
    };
    assert_eq!(
        gandr_core_term::equal_certificate_syntax(&arena, body, expected),
        gandr_core_term::CertificateEquality::Equal,
        "the reduct runs at the wide nesting, and the call reads what it returns"
    );
    assert_eq!(
        report.nested_elaborations()[&ConstantIndex::from(2_usize)]
            .crossings()
            .iter()
            .map(|(&at, crossing)| (at, crossing.by, crossing.carriers.len()))
            .collect::<Vec<_>>(),
        [(site, ConstantIndex::from(0_usize), 0)],
        "the crossing is recorded at the argument, by the reduct, at no carrier"
    );
    let readmission = crate::bridge::readmit(&mut arena, &report);
    assert!(
        readmission.readmitted().iter().all(|readmitted| matches!(
            readmitted.outcome(),
            crate::bridge::Outcome::Defined { .. }
        )),
        "the kernel re-derives the application of the reduct: {readmission:?}"
    );
    let (_, unkept, ..) = check(&[]);
    assert!(
        matches!(
            unkept.judged()[2].verdict(),
            Verdict::Refused(CheckRefusal::TypeMismatch(_))
        ),
        "with no reduct kept, the wide nesting is refused where the narrow pair is asked: {:?}",
        unkept.judged()[2].verdict()
    );
}

#[test]
fn a_manifest_model_crosses_by_its_forgetting_map_at_its_carrier()
{
    let variable = |arena: &mut CoreArena, index: u32| {
        arena.value_variable(
            gandr_core_term::Zone::Intuitionistic,
            DeBruijnIndex::from(index),
        )
    };
    // A pointed type's models, `Σ(c : U). El(c)`; with its carrier manifest
    // at `x`, a model is the point alone, `El(x)`.
    let check = |kept: &[ConstantIndex]| {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let small = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
        let bound = variable(&mut arena, 0);
        let point = arena.value_type_element(bound, Level::zero());
        let model = arena.value_type_sigma(small, point);
        // `forget : U(Π(x : U). El(x) → F Σ(c : U). El(c))`.
        let forget_type = {
            let returns = arena.comp_type_returner(model);
            let arrow = arena.comp_type_arrow(point, returns);
            let pi = arena.comp_type_pi(small, arrow);
            arena.value_type_thunk(pi)
        };
        // `forget = thunk(λx. λm. return (x, m))`.
        let forget = {
            let carrier = variable(&mut arena, 1);
            let manifest = variable(&mut arena, 0);
            let pair = arena.value_tuple(&[carrier, manifest]);
            let returned = arena.computation_return(pair);
            let inner = arena.computation_lambda(returned);
            let outer = arena.computation_lambda(inner);
            arena.value_thunk(outer)
        };
        // `taker = thunk(λp. return 0)`, asking for a pointed type's model.
        let integer_returns = arena.comp_type_returner(integer);
        let taker_arrow = arena.comp_type_arrow(model, integer_returns);
        let taker_type = arena.value_type_thunk(taker_arrow);
        let taker = {
            let zero = arena.value_literal(crate::fixture::integer_literal());
            let returned = arena.computation_return(zero);
            let lambda = arena.computation_lambda(returned);
            arena.value_thunk(lambda)
        };
        // `user = thunk(λm. taker(m))`, `m` an integer: a model whose carrier
        // is manifest at the integers.
        let user_arrow = arena.comp_type_arrow(integer, integer_returns);
        let user_type = arena.value_type_thunk(user_arrow);
        let site = variable(&mut arena, 0);
        let user = {
            let called = call(&mut arena, ConstantIndex::from(1_usize), site);
            let lambda = arena.computation_lambda(called);
            arena.value_thunk(lambda)
        };
        // `thunk(λm. bind forget(⌜Integer⌝, m) as n. taker(n))`.
        let quoted = arena.value_quote(integer);
        let expected = {
            let manifest = variable(&mut arena, 0);
            let map = arena.value_constant(ConstantIndex::from(0_usize));
            let forced = arena.computation_force(map);
            let at_carrier = arena.computation_application(forced, quoted);
            let forgot = arena.computation_application(at_carrier, manifest);
            let bound = variable(&mut arena, 0);
            let called = call(&mut arena, ConstantIndex::from(1_usize), bound);
            let ran = arena.computation_bind(forgot, called);
            let lambda = arena.computation_lambda(ran);
            arena.value_thunk(lambda)
        };
        let report = {
            let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
            context.keep_reducts(kept);
            check_module(&mut context, &[
                declaration(At(0), Maybe::Present(forget_type), Maybe::Present(forget)),
                declaration(At(1), Maybe::Present(taker_type), Maybe::Present(taker)),
                declaration(At(2), Maybe::Present(user_type), Maybe::Present(user)),
            ])
        };
        (arena, report, (site, quoted), expected)
    };
    let (mut arena, report, (site, quoted), expected) = check(&[ConstantIndex::from(0_usize)]);
    let Verdict::Checked { body, .. } = report.judged()[2].verdict()
    else {
        panic!(
            "the manifest model checks where the pointed type's model is asked: {:?}",
            report.judged()[2].verdict()
        );
    };
    assert_eq!(
        gandr_core_term::equal_certificate_syntax(&arena, body, expected),
        gandr_core_term::CertificateEquality::Equal,
        "the forgetting map runs at the integers' code and the manifest model"
    );
    let crossings = report.nested_elaborations()[&ConstantIndex::from(2_usize)].crossings();
    let [(&at, crossing)] = crossings.iter().collect::<Vec<_>>()[..]
    else {
        panic!("one crossing is recorded: {crossings:?}");
    };
    assert_eq!(
        (at, crossing.by),
        (site, ConstantIndex::from(0_usize)),
        "the crossing is recorded at the argument, by the forgetting map"
    );
    let &[carrier] = crossing.carriers.as_slice()
    else {
        panic!("the map takes one carrier: {crossing:?}");
    };
    assert_eq!(
        gandr_core_term::equal_certificate_syntax(&arena, carrier, quoted),
        gandr_core_term::CertificateEquality::Equal,
        "the carrier solved is the integers' code"
    );
    let readmission = crate::bridge::readmit(&mut arena, &report);
    assert!(
        readmission.readmitted().iter().all(|readmitted| matches!(
            readmitted.outcome(),
            crate::bridge::Outcome::Defined { .. }
        )),
        "the kernel re-derives the application of the forgetting map: {readmission:?}"
    );
    let (_, unkept, ..) = check(&[]);
    assert!(
        matches!(
            unkept.judged()[2].verdict(),
            Verdict::Refused(CheckRefusal::TypeMismatch(_))
        ),
        "with no forgetting map kept, the manifest model is refused where the model is asked: {:?}",
        unkept.judged()[2].verdict()
    );
}

#[test]
fn a_nested_call_runs_with_the_effects_its_returner_performs()
{
    use gandr_core_term::effect::EffectOp;
    use gandr_core_term::effect::EffectRow;
    use gandr_core_term::effect::EffectSig;
    use gandr_core_term::effect::OperationName;
    let mut arena = CoreArena::new();
    let (function, identity) = integer_function(&mut arena);
    let integer = arena.value_type_base(BaseType::Integer);
    let interface = EffectSig::new("Ask".into(), [EffectOp {
        name: OperationName::from("ask"),
        payload: integer,
        reply: integer,
    }])
    .expect("one operation");
    let asks =
        arena.comp_type_returner_with_effects(integer, EffectRow::singleton(interface.clone()));
    let asking_arrow = arena.comp_type_arrow(integer, asks);
    let asking_type = arena.value_type_thunk(asking_arrow);
    let [asked_x, effectful_x, pure_x] = [(); 3].map(|()| {
        arena.value_variable(
            gandr_core_term::Zone::Intuitionistic,
            DeBruijnIndex::from(0_u32),
        )
    });
    let asking = {
        let performed = arena.computation_perform(interface, OperationName::from("ask"), asked_x);
        let lambda = arena.computation_lambda(performed);
        arena.value_thunk(lambda)
    };
    let returned_of = |arena: &mut CoreArena, callee: ConstantIndex, argument: ValueId| {
        let called = call(arena, callee, argument);
        let nested = arena.value_nested(called);
        let returned = arena.computation_return(nested);
        let lambda = arena.computation_lambda(returned);
        (nested, arena.value_thunk(lambda))
    };
    let (effectful, asks_twice) =
        returned_of(&mut arena, ConstantIndex::from(1_usize), effectful_x);
    let (pure, identity_twice) = returned_of(&mut arena, ConstantIndex::from(0_usize), pure_x);
    let report = {
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        check_module(&mut context, &[
            declaration(At(0), Maybe::Present(function), Maybe::Present(identity)),
            declaration(At(1), Maybe::Present(asking_type), Maybe::Present(asking)),
            declaration(
                At(2),
                Maybe::Present(asking_type),
                Maybe::Present(asks_twice),
            ),
            declaration(
                At(3),
                Maybe::Present(function),
                Maybe::Present(identity_twice),
            ),
        ])
    };
    let decided = |constant: usize, at: ValueId| {
        report
            .nested_elaborations()
            .get(&ConstantIndex::from(constant))
            .and_then(|elaboration| elaboration.decisions().get(&at).copied())
    };
    assert_eq!(
        decided(2, effectful),
        Some(Nesting::Ran(Purity::Effectful)),
        "a call whose returner performs `Ask` runs effectfully: {:?}",
        report.judged()[2].verdict()
    );
    assert_eq!(
        decided(3, pure),
        Some(Nesting::Ran(Purity::Pure)),
        "a call whose returner performs nothing runs purely"
    );
}

#[test]
fn a_pure_run_a_type_reads_stands_as_what_it_returns_444()
{
    let mut arena = CoreArena::new();
    let (function, identity) = integer_function(&mut arena);
    let integer = arena.value_type_base(BaseType::Integer);
    // `Σ (y : Integer). Path(Integer, y, y)`.
    let bound = arena.value_variable(
        gandr_core_term::Zone::Intuitionistic,
        DeBruijnIndex::from(0_u32),
    );
    let looped = arena.value_type_path(integer, bound, bound);
    let sigma = arena.value_type_sigma(integer, looped);
    let returns = arena.comp_type_returner(sigma);
    let arrow = arena.comp_type_arrow(integer, returns);
    let pairing_type = arena.value_type_thunk(arrow);
    // `λx. return (id(x), here(⟨id(x)⟩))`, the first component a nested
    // call the second's type reads.
    let [nested_x, point_x] = [(); 2].map(|()| {
        arena.value_variable(
            gandr_core_term::Zone::Intuitionistic,
            DeBruijnIndex::from(0_u32),
        )
    });
    let first = call(&mut arena, ConstantIndex::from(0_usize), nested_x);
    let first = arena.value_nested(first);
    let point = call(&mut arena, ConstantIndex::from(0_usize), point_x);
    let point = arena.value_returned(point);
    let reflexive = arena.value_here(point);
    let pair = arena.value_tuple(&[first, reflexive]);
    let returned = arena.computation_return(pair);
    let lambda = arena.computation_lambda(returned);
    let pairing = arena.value_thunk(lambda);
    let report = {
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        check_module(&mut context, &[
            declaration(At(0), Maybe::Present(function), Maybe::Present(identity)),
            declaration(At(1), Maybe::Present(pairing_type), Maybe::Present(pairing)),
        ])
    };
    let Verdict::Checked { body, .. } = report.judged()[1].verdict()
    else {
        panic!(
            "the second component checks at the first's call: {:?}",
            report.judged()[1].verdict()
        );
    };
    let elaboration = &report.nested_elaborations()[&ConstantIndex::from(1_usize)];
    assert_eq!(
        elaboration.decisions().get(&first),
        Some(&Nesting::Returned),
        "a pure call the second component's type reads stands as what it returns"
    );
    assert!(elaboration.binds().is_empty(), "and mints no bind");
    let Some(&gandr_core_term::Value::Thunk(lambda)) = arena.value(body)
    else {
        panic!("the body stays a thunk");
    };
    let Some(&gandr_core_term::Computation::Lambda(returned)) = arena.computation(lambda)
    else {
        panic!("over its lambda");
    };
    let Some(&gandr_core_term::Computation::Return(pair)) = arena.computation(returned)
    else {
        panic!("returning the pair, with nothing bound before it");
    };
    assert!(
        matches!(
            arena.value(pair).and_then(gandr_core_term::Value::components),
            Some(&[component, _]) if matches!(arena.value(component), Some(&gandr_core_term::Value::Returned(_)))
        ),
        "the first component is the call's returned value"
    );
    let readmission = crate::bridge::readmit(&mut arena, &report);
    assert!(
        readmission.readmitted().iter().all(|readmitted| matches!(
            readmitted.outcome(),
            crate::bridge::Outcome::Defined { .. }
        )),
        "the kernel re-derives the elaborated body: {readmission:?}"
    );
}

/// A reflexivity over `carrier`, `U ((y : carrier) -> F Path(carrier, y,
/// y))`, and its body `λy. return here(y)`.
///
/// # Specification
/// trivial.
fn reflexivity(
    arena: &mut CoreArena,
    carrier: ValueTypeId,
) -> (ValueTypeId, ValueId)
{
    let [left, right, point] = [(); 3].map(|()| {
        arena.value_variable(
            gandr_core_term::Zone::Intuitionistic,
            DeBruijnIndex::from(0_u32),
        )
    });
    let path = arena.value_type_path(carrier, left, right);
    let returns = arena.comp_type_returner(path);
    let pi = arena.comp_type_pi(carrier, returns);
    let here = arena.value_here(point);
    let returned = arena.computation_return(here);
    let lambda = arena.computation_lambda(returned);
    (arena.value_type_thunk(pi), arena.value_thunk(lambda))
}

#[test]
fn a_call_beneath_a_type_read_argument_stands_as_written_762()
{
    let mut arena = CoreArena::new();
    let (function, identity) = integer_function(&mut arena);
    let integer = arena.value_type_base(BaseType::Integer);
    let pair = arena.value_type_product(&[integer, integer]);
    let (at_integer, integer_body) = reflexivity(&mut arena, integer);
    let (at_pair, pair_body) = reflexivity(&mut arena, pair);
    let variable = |arena: &mut CoreArena| {
        arena.value_variable(
            gandr_core_term::Zone::Intuitionistic,
            DeBruijnIndex::from(0_u32),
        )
    };
    // `id(id(x))` as a written type reads it, and as an argument writes it:
    // the inner call nested beneath the outer.
    let returned_twice = |arena: &mut CoreArena| {
        let x = variable(arena);
        let inner = call(arena, ConstantIndex::from(0_usize), x);
        let inner = arena.value_returned(inner);
        let outer = call(arena, ConstantIndex::from(0_usize), inner);
        arena.value_returned(outer)
    };
    // `(id(x), x)` likewise, the call beneath a tuple.
    let returned_paired = |arena: &mut CoreArena| {
        let x = variable(arena);
        let inner = call(arena, ConstantIndex::from(0_usize), x);
        let inner = arena.value_returned(inner);
        let x = variable(arena);
        arena.value_tuple(&[inner, x])
    };
    let declared = |arena: &mut CoreArena, carrier: ValueTypeId, endpoint: ValueId| {
        let path = arena.value_type_path(carrier, endpoint, endpoint);
        let returns = arena.comp_type_returner(path);
        let pi = arena.comp_type_pi(integer, returns);
        arena.value_type_thunk(pi)
    };
    let twice_endpoint = returned_twice(&mut arena);
    let twice_type = declared(&mut arena, integer, twice_endpoint);
    let x = variable(&mut arena);
    let inner_twice = call(&mut arena, ConstantIndex::from(0_usize), x);
    let inner_twice = arena.value_nested(inner_twice);
    let outer_twice = call(&mut arena, ConstantIndex::from(0_usize), inner_twice);
    let outer_twice = arena.value_nested(outer_twice);
    let twice_call = call(&mut arena, ConstantIndex::from(1_usize), outer_twice);
    let twice_lambda = arena.computation_lambda(twice_call);
    let twice_body = arena.value_thunk(twice_lambda);
    let paired_endpoint = returned_paired(&mut arena);
    let paired_type = declared(&mut arena, pair, paired_endpoint);
    let x = variable(&mut arena);
    let inner_paired = call(&mut arena, ConstantIndex::from(0_usize), x);
    let inner_paired = arena.value_nested(inner_paired);
    let x = variable(&mut arena);
    let paired_argument = arena.value_tuple(&[inner_paired, x]);
    let paired_call = call(&mut arena, ConstantIndex::from(2_usize), paired_argument);
    let paired_lambda = arena.computation_lambda(paired_call);
    let paired_body = arena.value_thunk(paired_lambda);
    let report = {
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        check_module(&mut context, &[
            declaration(At(0), Maybe::Present(function), Maybe::Present(identity)),
            declaration(
                At(1),
                Maybe::Present(at_integer),
                Maybe::Present(integer_body),
            ),
            declaration(At(2), Maybe::Present(at_pair), Maybe::Present(pair_body)),
            declaration(
                At(3),
                Maybe::Present(twice_type),
                Maybe::Present(twice_body),
            ),
            declaration(
                At(4),
                Maybe::Present(paired_type),
                Maybe::Present(paired_body),
            ),
        ])
    };
    for (constant, nested) in [
        (3_usize, [inner_twice, outer_twice]),
        (4_usize, [inner_paired, inner_paired]),
    ] {
        assert!(
            matches!(report.judged()[constant].verdict(), Verdict::Checked { .. }),
            "the argument converts with the type written with it: {:?}",
            report.judged()[constant].verdict()
        );
        let elaboration = &report.nested_elaborations()[&ConstantIndex::from(constant)];
        for at in nested {
            assert_eq!(
                elaboration.decisions().get(&at),
                Some(&Nesting::Returned),
                "a pure call beneath the argument stands as what it returns"
            );
        }
        assert!(elaboration.binds().is_empty(), "and mints no bind");
    }
    let readmission = crate::bridge::readmit(&mut arena, &report);
    assert!(
        readmission.readmitted().iter().all(|readmitted| matches!(
            readmitted.outcome(),
            crate::bridge::Outcome::Defined { .. }
        )),
        "the kernel re-derives the elaborated bodies: {readmission:?}"
    );
}

#[test]
fn a_nested_computation_is_decided_by_its_expected_type()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let returns = arena.comp_type_returner(integer);
    let suspended_type = arena.value_type_thunk(returns);
    let parameter = arena.comp_type_arrow(suspended_type, returns);
    let consumer_type = arena.value_type_thunk(parameter);
    let consumer = {
        let argument = arena.value_variable(
            gandr_core_term::Zone::Intuitionistic,
            DeBruijnIndex::from(0_u32),
        );
        let forced = arena.computation_force(argument);
        let lambda = arena.computation_lambda(forced);
        arena.value_thunk(lambda)
    };
    let zero = arena.value_literal(integer_literal());
    let produce = arena.computation_return(zero);
    let suspended = arena.value_nested(produce);
    let consumed = call(&mut arena, ConstantIndex::from(0_usize), suspended);
    let use_site = arena.value_thunk(consumed);
    let unsigned_zero = arena.value_literal(integer_literal());
    let unsigned_produce = arena.computation_return(unsigned_zero);
    let unsigned = arena.value_nested(unsigned_produce);
    let report = {
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        check_module(&mut context, &[
            declaration(
                At(0),
                Maybe::Present(consumer_type),
                Maybe::Present(consumer),
            ),
            declaration(
                At(1),
                Maybe::Present(suspended_type),
                Maybe::Present(use_site),
            ),
            declaration(At(2), UNSIGNED, Maybe::Present(unsigned)),
        ])
    };
    let Verdict::Checked { body, .. } = report.judged()[1].verdict()
    else {
        panic!(
            "the nested computation checks at the thunk type: {:?}",
            report.judged()[1].verdict()
        );
    };
    let elaboration = &report.nested_elaborations()[&ConstantIndex::from(1_usize)];
    assert_eq!(
        elaboration.decisions().get(&suspended),
        Some(&Nesting::Suspended),
        "at a thunk-typed parameter it is suspended"
    );
    assert!(elaboration.binds().is_empty(), "a suspension mints no bind");
    let Some(&gandr_core_term::Value::Thunk(call_body)) = arena.value(body)
    else {
        panic!("the use site stays a thunk");
    };
    let Some(&gandr_core_term::Computation::Application(_, argument)) =
        arena.computation(call_body)
    else {
        panic!("the call stands as written");
    };
    assert_eq!(
        arena.value(argument),
        Some(&gandr_core_term::Value::Thunk(produce)),
        "the argument is the thunk of the written computation"
    );
    assert_eq!(
        report.judged()[2].verdict(),
        Verdict::Refused(CheckRefusal::NotSynthesisable {
            form: CheckingForm::Nested(unsigned),
        }),
        "with no type expected there is nothing to decide by, and it is refused by name"
    );
}

#[test]
fn a_computation_written_as_a_scrutinee_runs_1141()
{
    let mut arena = CoreArena::new();
    let unit = arena.value_type_unit();
    let boolean = arena.value_type_sum(&[unit, unit]);
    let integer = arena.value_type_base(BaseType::Integer);
    // `decide : unit -> F (1 + 1)`, answering the left summand.
    let decides = arena.comp_type_returner(boolean);
    let decide_arrow = arena.comp_type_arrow(unit, decides);
    let decide_type = arena.value_type_thunk(decide_arrow);
    let decide = {
        let empty = arena.value_unit();
        let left = arena.value_injection(0_usize.into(), empty);
        let returned = arena.computation_return(left);
        let lambda = arena.computation_lambda(returned);
        arena.value_thunk(lambda)
    };
    // `cased : unit -> F Integer`, `λu. case decide(u) { _ => 1, _ => 2 }`.
    let answers = arena.comp_type_returner(integer);
    let cased_arrow = arena.comp_type_arrow(unit, answers);
    let cased_type = arena.value_type_thunk(cased_arrow);
    let argument = arena.value_variable(
        gandr_core_term::Zone::Intuitionistic,
        DeBruijnIndex::from(0_u32),
    );
    let decided = call(&mut arena, ConstantIndex::from(0_usize), argument);
    let scrutinee = arena.value_nested(decided);
    let branches = [(); 2].map(|()| {
        let answer = arena.value_literal(integer_literal());
        arena.computation_return(answer)
    });
    let case = arena.computation_case(scrutinee, &branches);
    let lambda = arena.computation_lambda(case);
    let cased = arena.value_thunk(lambda);
    let module = [
        declaration(At(0), Maybe::Present(decide_type), Maybe::Present(decide)),
        declaration(At(1), Maybe::Present(cased_type), Maybe::Present(cased)),
    ];
    let report = {
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        check_module(&mut context, &module)
    };
    assert!(
        matches!(report.judged()[1].verdict(), Verdict::Checked { .. }),
        "a scrutinee is never a thunk, so the call written there runs and the case reads its \
         answer: {:?}",
        report.judged()[1].verdict()
    );
    assert_eq!(
        report.nested_elaborations()[&ConstantIndex::from(1_usize)]
            .decisions()
            .get(&scrutinee),
        Some(&Nesting::Ran(Purity::Pure)),
        "the call runs, purely"
    );
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let run = type_module(&mut context, &module);
    let kept: Vec<_> = run.typings()[&ConstantIndex::from(1_usize)]
        .typings()
        .iter()
        .filter(|typing| typing.term == TermNode::Value(scrutinee))
        .map(|typing| typing.ty)
        .collect();
    assert_eq!(
        kept,
        [TypeNode::Value(boolean)],
        "the scrutinee is no goal of its own, so its run keeps its typing, once, at what it returns"
    );
}

/// A projection's record is never a thunk, so a projection written there runs
/// and the outer projection reads the record it returns: a field of a field
/// checks (#1106).
#[test]
fn a_computation_written_as_a_projected_record_runs_1106()
{
    let mut arena = CoreArena::new();
    let label = |name: &str| gandr_kernel_term::FieldLabel::from(alloc::string::String::from(name));
    let unit = arena.value_type_unit();
    let integer = arena.value_type_base(BaseType::Integer);
    // `outer : #{inner : #{x : Integer}} = #{inner = #{x = 0}}`.
    let inner_type =
        arena.value_type_record(alloc::collections::BTreeMap::from([(label("x"), integer)]));
    let outer_type = arena.value_type_record(alloc::collections::BTreeMap::from([(
        label("inner"),
        inner_type,
    )]));
    let zero = arena.value_literal(integer_literal());
    let inner = arena.value_record(alloc::collections::BTreeMap::from([(label("x"), zero)]));
    let outer = arena.value_record(alloc::collections::BTreeMap::from([(
        label("inner"),
        inner,
    )]));
    // `picked : unit -> F Integer`, `λu. outer.inner.x`.
    let answers = arena.comp_type_returner(integer);
    let picked_arrow = arena.comp_type_arrow(unit, answers);
    let picked_type = arena.value_type_thunk(picked_arrow);
    let named = arena.value_constant(ConstantIndex::from(0_usize));
    let projected = arena.computation_record_projection(named, label("inner"));
    let record = arena.value_nested(projected);
    let field = arena.computation_record_projection(record, label("x"));
    let lambda = arena.computation_lambda(field);
    let picked = arena.value_thunk(lambda);
    let module = [
        declaration(At(0), Maybe::Present(outer_type), Maybe::Present(outer)),
        declaration(At(1), Maybe::Present(picked_type), Maybe::Present(picked)),
    ];
    let report = {
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        check_module(&mut context, &module)
    };
    assert!(
        matches!(report.judged()[1].verdict(), Verdict::Checked { .. }),
        "the inner projection runs and the outer one reads its field: {:?}",
        report.judged()[1].verdict()
    );
    assert_eq!(
        report.nested_elaborations()[&ConstantIndex::from(1_usize)]
            .decisions()
            .get(&record),
        Some(&Nesting::Ran(Purity::Pure)),
        "the inner projection runs, purely"
    );
}

#[test]
fn a_run_in_a_definition_s_own_value_is_unenclosed()
{
    let mut arena = CoreArena::new();
    let (function, identity) = integer_function(&mut arena);
    let integer = arena.value_type_base(BaseType::Integer);
    let zero = arena.value_literal(integer_literal());
    let computation = call(&mut arena, ConstantIndex::from(0_usize), zero);
    let nested = arena.value_nested(computation);
    let report = {
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        check_module(&mut context, &[
            declaration(At(0), Maybe::Present(function), Maybe::Present(identity)),
            declaration(At(1), Maybe::Present(integer), Maybe::Present(nested)),
        ])
    };
    let refusal = CheckRefusal::UnenclosedRun { at: nested };
    assert_eq!(
        report.judged()[1].verdict(),
        Verdict::Refused(refusal),
        "the call checks at the integer, but no computation encloses it to run before"
    );
    assert_eq!(refusal.classify(), FailureClass::MalformedSource);
    let failure = &report.failures()[&ConstantIndex::from(1_usize)];
    assert!(
        failure.obligations().is_empty(),
        "no rule of the judgement is pending"
    );
    assert_eq!(
        failure.pursuit().at(),
        CoreNode::Term(TermNode::Value(nested))
    );
    assert!(
        !report
            .definitions()
            .contains_key(&ConstantIndex::from(1_usize)),
        "a refused body defines nothing"
    );
}

/// The answers of `supported`, positions and type ids, in order.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one position and underlying type-id answer per consultation, in
///   the same order and retaining absence reasons.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — repeated, absent and interrupted consultation reads are
///   compared with exact position/type pairs; the observer exposes wrong order,
///   missing answers or loss of an absence.
/// - witness: `module::tests::the_support_holds_each_consulted_answer_once_in_position_order`
/// - witness: `module::tests::a_refusal_cuts_the_support_where_the_run_stopped`
#[spec(ensures: |ret| ret.iter().copied().eq(supported.support().consulted().iter()
        .map(|entry| (entry.constant(), entry.answer().map(crate::formation::FormedValueType::id)))))]
fn answers(
    supported: &super::Supported
) -> Vec<(
    ConstantIndex,
    Maybe<ValueTypeId, crate::context::signature_table::Absent>,
)>
{
    supported
        .support()
        .consulted()
        .iter()
        .map(|consulted| {
            (
                consulted.constant(),
                consulted
                    .answer()
                    .map(crate::formation::FormedValueType::id),
            )
        })
        .collect()
}

#[test]
fn the_support_holds_each_consulted_answer_once_in_position_order()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let returns_integer = arena.comp_type_returner(integer);
    let inner = arena.comp_type_arrow(integer, returns_integer);
    let outer = arena.comp_type_arrow(integer, inner);
    let function_type = arena.value_type_thunk(outer);
    let suspended_type = arena.value_type_thunk(returns_integer);
    let zero = arena.value_literal(integer_literal());
    let x = arena.value_constant(ConstantIndex::from(0_usize));
    let f = arena.value_constant(ConstantIndex::from(1_usize));
    let unknown = arena.value_constant(ConstantIndex::from(7_usize));
    // thunk ((force f) x) x: reads f, then x, then x again.
    let forced = arena.computation_force(f);
    let once = arena.computation_application(forced, x);
    let twice = arena.computation_application(once, x);
    let suspended = arena.value_thunk(twice);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let _x = check_declaration(
        &mut context,
        &declaration(At(0), Maybe::Present(integer), Maybe::Present(zero)),
    );
    let _f = check_declaration(
        &mut context,
        &declaration(At(1), Maybe::Present(function_type), HOLE),
    );
    let _read = check_declaration(
        &mut context,
        &declaration(At(2), UNSIGNED, Maybe::Present(x)),
    );
    let literal = super::check_declaration_supported(
        &mut context,
        &declaration(At(3), UNSIGNED, Maybe::Present(zero)),
    );
    assert_eq!(
        answers(&literal),
        [],
        "a judgement that reads no constant consults nothing, whatever ran before it"
    );
    let applied = super::check_declaration_supported(
        &mut context,
        &declaration(
            At(4),
            Maybe::Present(suspended_type),
            Maybe::Present(suspended),
        ),
    );
    assert!(
        matches!(applied.verdict(), Verdict::Checked { .. }),
        "the application checks"
    );
    assert_eq!(
        answers(&applied),
        [
            (ConstantIndex::from(0_usize), Maybe::Present(integer)),
            (ConstantIndex::from(1_usize), Maybe::Present(function_type)),
        ],
        "f read first and x read twice are each held once, ascending by position"
    );
    let missing = super::check_declaration_supported(
        &mut context,
        &declaration(At(5), UNSIGNED, Maybe::Present(unknown)),
    );
    assert_eq!(
        answers(&missing),
        [(
            ConstantIndex::from(7_usize),
            Maybe::Absent(crate::context::signature_table::Absent::Untyped)
        )],
        "an unadmitted position is consulted and answers its absence"
    );
}

#[test]
fn a_refusal_cuts_the_support_where_the_run_stopped()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let returns_integer = arena.comp_type_returner(integer);
    let inner = arena.comp_type_arrow(integer, returns_integer);
    let outer = arena.comp_type_arrow(integer, inner);
    let function_type = arena.value_type_thunk(outer);
    let suspended_type = arena.value_type_thunk(returns_integer);
    let zero = arena.value_literal(integer_literal());
    let text = arena.value_literal(text_literal());
    let s = arena.value_constant(ConstantIndex::from(0_usize));
    let f = arena.value_constant(ConstantIndex::from(1_usize));
    let x = arena.value_constant(ConstantIndex::from(2_usize));
    // thunk ((force f) s) x: s is a string, so the run stops before x.
    let forced = arena.computation_force(f);
    let once = arena.computation_application(forced, s);
    let twice = arena.computation_application(once, x);
    let suspended = arena.value_thunk(twice);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let module = [
        declaration(At(0), UNSIGNED, Maybe::Present(text)),
        declaration(At(1), Maybe::Present(function_type), HOLE),
        declaration(At(2), Maybe::Present(integer), Maybe::Present(zero)),
    ];
    for offered in &module {
        let _judged = check_declaration(&mut context, offered);
    }
    let string = context.atom(Atom::String).id();
    let refused = super::check_declaration_supported(
        &mut context,
        &declaration(
            At(3),
            Maybe::Present(suspended_type),
            Maybe::Present(suspended),
        ),
    );
    assert!(
        matches!(
            refused.verdict(),
            Verdict::Refused(CheckRefusal::TypeMismatch(Mismatch::Value { at, .. })) if at == s
        ),
        "the string argument is refused at the value bridge"
    );
    assert_eq!(
        answers(&refused),
        [
            (ConstantIndex::from(0_usize), Maybe::Present(string)),
            (ConstantIndex::from(1_usize), Maybe::Present(function_type)),
        ],
        "the support holds what the run consulted before the refusal and nothing after it"
    );
}

#[test]
fn an_adopted_answer_is_read_as_if_judged()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let small = arena.value_type_universe(
        gandr_core_term::Sort::Ground(gandr_kernel_term::GroundSort::Value),
        gandr_kernel_strata::Level::zero(),
    );
    let code = arena.value_quote(integer);
    let adopted = arena.value_constant(ConstantIndex::from(0_usize));
    let untyped = arena.value_constant(ConstantIndex::from(1_usize));
    let decoded = arena.value_type_element(adopted, gandr_kernel_strata::Level::zero());
    let zero = arena.value_literal(integer_literal());
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    assert_eq!(
        context.adopt_formed(ConstantIndex::from(0_usize), small, Maybe::Present(code)),
        Ok(()),
        "a first adoption takes any position, its type seated as the reused judgement formed it"
    );
    assert_eq!(
        context.adopt(
            ConstantIndex::from(1_usize),
            Maybe::Absent(crate::context::signature_table::Absent::Untyped),
            Maybe::Absent(crate::code::unfolding::Absent::Rigid)
        ),
        Ok(()),
        "an adopted absence is admitted"
    );
    assert!(
        matches!(
            check_declaration(&mut context, &declaration(At(2), UNSIGNED, Maybe::Present(adopted))),
            Verdict::Synthesised { synthesised, .. } if synthesised.produced().id() == small
        ),
        "a later declaration reads the adopted type"
    );
    assert_eq!(
        check_declaration(
            &mut context,
            &declaration(At(3), UNSIGNED, Maybe::Present(untyped))
        ),
        Verdict::Refused(CheckRefusal::UnknownConstant {
            at: untyped,
            constant: ConstantIndex::from(1_usize),
        }),
        "a later declaration finds no type at an adopted absence"
    );
    assert_eq!(
        context.adopt(
            ConstantIndex::from(2_usize),
            Maybe::Absent(crate::context::signature_table::Absent::Untyped),
            Maybe::Absent(crate::code::unfolding::Absent::Rigid)
        ),
        Err(CheckRefusal::AdmissionOrder {
            constant: ConstantIndex::from(2_usize),
            admitted: ConstantIndex::from(3_usize),
        }),
        "an adoption out of order is refused with both positions"
    );
    assert_eq!(
        context
            .signature(ConstantIndex::from(2_usize))
            .map(crate::formation::FormedValueType::id),
        Maybe::Present(small),
        "the refused adoption left the table as it was"
    );
    assert!(
        matches!(
            check_declaration(
                &mut context,
                &declaration(At(4), Maybe::Present(decoded), Maybe::Present(zero))
            ),
            Verdict::Checked { .. }
        ),
        "a decode of the adopted code unfolds to the adopted body"
    );
}

/// The abstract type at `position`, of `kind`, represented by
/// `representation`, sealing the `extent` declarations after it, minted at
/// component `component` of ascription zero; its origin `position + 100`.
///
/// # Specification
/// - requires: adding the origin offset one hundred does not overflow.
/// - ensures: the abstract type is offered at the fixture position with the
///   distinct origin.
/// - panics: the position lies outside the offset domain.
///
/// # Adequacy
/// - hypothesis: L3 — a sealed module observes each premise of abstract type
///   formation and the reach of its seal.
/// - witness: `module::tests::an_abstract_type_forms_at_a_value_universe_and_mints_its_site`
/// - witness: `module::tests::a_sealed_member_checks_at_the_representation_inside`
#[spec(
        requires: position.0.checked_add(100).is_some(),
        ensures: |ret| usize::from(ret.constant()) == position.0
            && matches!(ret.content(), &crate::DeclarationContent::Abstract(held)
                if held.kind() == kind && held.representation() == representation),
    )]
fn sealed(
    position: At,
    kind: ValueTypeId,
    representation: ValueTypeId,
    extent: SealExtent,
    component: ComponentOrdinal,
) -> Declaration
{
    Declaration::abstract_type(
        ConstantIndex::from(position.0),
        AbstractType::new(
            kind,
            representation,
            extent,
            SealSite::new(SealingSite::from(0_usize), component),
        ),
        OriginToken::from(position.0.checked_add(100).unwrap()),
    )
}

#[test]
fn an_abstract_type_forms_at_a_value_universe_and_mints_its_site()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let small = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let module = [
        sealed(At(0), small, integer, 0_usize.into(), 0_usize.into()),
        sealed(At(1), integer, integer, 0_usize.into(), 1_usize.into()),
        sealed(At(2), small, small, 0_usize.into(), 2_usize.into()),
    ];
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let report = check_module(&mut context, &module);
    let verdicts: Vec<_> = report.judged().iter().map(super::Judged::verdict).collect();
    assert_eq!(
        verdicts,
        [
            Verdict::Data,
            Verdict::Refused(CheckRefusal::AbstractKindNotUniverse(integer)),
            Verdict::Refused(CheckRefusal::RepresentationAboveKind {
                representation: small,
                kind: small,
            }),
        ],
        "a kind at a value universe forms; a kind that is no universe and a representation above its kind are refused by name"
    );
    assert_eq!(
        report.seal_table().sites(),
        [SealSite::new(
            SealingSite::from(0_usize),
            ComponentOrdinal::from(0_usize)
        )],
        "only the abstract type that formed minted its site"
    );
    assert_eq!(
        report.abstract_types().keys().copied().collect::<Vec<_>>(),
        [ConstantIndex::from(0_usize)],
        "and only it is retained for readmission"
    );
    assert_eq!(
        context.abstract_level(ConstantIndex::from(0_usize)),
        Ok(Level::zero()),
        "its atom inhabits its kind's universe"
    );
}

#[test]
fn a_repeated_sealing_site_is_refused_and_mints_nothing()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let small = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let module = [
        sealed(At(0), small, integer, 0_usize.into(), 0_usize.into()),
        sealed(At(1), small, integer, 0_usize.into(), 0_usize.into()),
    ];
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let report = check_module(&mut context, &module);
    let site = SealSite::new(SealingSite::from(0_usize), ComponentOrdinal::from(0_usize));
    assert_eq!(
        report.judged()[1].verdict(),
        Verdict::Refused(CheckRefusal::SealSiteRepeated(site)),
        "a second abstract type at one site is refused naming the site"
    );
    assert_eq!(
        (report.seal_table().sites(), report.abstract_types().len()),
        ([site].as_slice(), 1),
        "the refused one minted no second atom and was not retained"
    );
}

#[test]
fn an_atom_naming_no_abstract_type_is_refused()
{
    let mut arena = CoreArena::new();
    let zero = arena.value_literal(integer_literal());
    let named = arena.value_type_abstract(ConstantIndex::from(0_usize));
    let module = [
        declaration(At(0), UNSIGNED, Maybe::Present(zero)),
        declaration(At(1), Maybe::Present(named), HOLE),
    ];
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let report = check_module(&mut context, &module);
    assert_eq!(
        report.judged()[1].verdict(),
        Verdict::Refused(CheckRefusal::NotAnAbstractType(ConstantIndex::from(
            0_usize
        ))),
        "an atom at a value declaration's position is no type"
    );
}

/// `module Counter :> #{ type T, seed : T } { type T = Integer ; def seed
/// = 7 ; }` as the lowering admits it: the atom, the body member, the
/// witness exporting it at the component type, then two clients.
#[test]
fn a_sealed_member_checks_at_the_representation_inside()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let small = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let seven = arena.value_literal(integer_literal());
    let atom = arena.value_type_abstract(ConstantIndex::from(0_usize));
    let member = arena.value_constant(ConstantIndex::from(1_usize));
    let export = arena.value_constant(ConstantIndex::from(2_usize));
    let module = [
        sealed(At(0), small, integer, 2_usize.into(), 0_usize.into()),
        declaration(At(1), Maybe::Present(integer), Maybe::Present(seven)),
        declaration(At(2), Maybe::Present(atom), Maybe::Present(member)),
        declaration(At(3), Maybe::Present(atom), Maybe::Present(export)),
        declaration(At(4), Maybe::Present(integer), Maybe::Present(export)),
        declaration(At(5), Maybe::Present(atom), Maybe::Present(seven)),
    ];
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let report = check_module(&mut context, &module);
    let verdicts: Vec<_> = report.judged().iter().map(super::Judged::verdict).collect();
    assert!(
        matches!(verdicts[2], Verdict::Checked { .. }),
        "inside the seal the member's Integer is the atom's representation"
    );
    assert!(
        matches!(verdicts[3], Verdict::Checked { .. }),
        "outside, the export reads at the atom, which is itself"
    );
    assert_eq!(
        verdicts[4],
        Verdict::Refused(CheckRefusal::TypeMismatch(Mismatch::Value {
            at: export,
            synthesised: atom,
            expected: integer,
        })),
        "outside, the atom is not its representation, and the mismatch names it"
    );
    assert!(
        matches!(verdicts[5], Verdict::Refused(CheckRefusal::TypeMismatch(_))),
        "nor does a literal of the representation inhabit it"
    );
}

#[test]
fn a_solution_naming_a_later_hole_is_read_through_1216()
{
    use alloc::collections::BTreeMap;

    use gandr_core_term::BinderDepth;
    use gandr_core_term::Binders;
    use gandr_core_term::Value;
    use gandr_core_term::ValueType;
    use gandr_core_term::Zone;
    use gandr_core_term::hole::HoleId;
    use gandr_core_term::hole::NominationIndex;

    // `?first`, declared two binders deep, is solved as `?second`, declared
    // one binder deep and solved as `#0`. In `thunk λ λ. return ?first` the
    // second round reads `?second` two binders deep, raised past one: `#1`.
    // A type recorded two binders deep reads the same.
    let mut arena = CoreArena::new();
    let [first, second] = [0_u32, 1]
        .map(|index| HoleId::nominated(NominationIndex::from(index)).expect("a nominated name"));
    let first_at = arena.value_hole(first);
    let second_at = arena.value_hole(second);
    let innermost = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let outer = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
    let solutions = BTreeMap::from([
        (first, (second_at, Binders::from(2_u32))),
        (second, (innermost, Binders::ONE)),
    ]);
    let suspended = |arena: &mut CoreArena, value| {
        let returned = arena.computation_return(value);
        let inner = arena.computation_lambda(returned);
        let lambda = arena.computation_lambda(inner);
        arena.value_thunk(lambda)
    };
    let holed = suspended(&mut arena, first_at);
    let filled = suspended(&mut arena, outer);
    let read = super::fill(&mut arena, holed, &solutions);
    assert_eq!(
        gandr_core_term::equal_certificate_syntax(&arena, read, filled),
        gandr_core_term::CertificateEquality::Equal,
        "the hole reads through both solutions, the second raised past one binder"
    );
    assert_eq!(
        super::fill(&mut arena, filled, &solutions),
        filled,
        "a body holding no hole is its own filling"
    );
    let decoded = arena.value_type_element(first_at, Level::zero());
    let TypeNode::Value(typed) = super::solved_type(
        &mut arena,
        (TypeNode::Value(decoded), BinderDepth::from(2_usize)),
        &solutions,
    )
    else {
        panic!("a value type reads as a value type");
    };
    assert!(
        matches!(
            arena.value_type(typed),
            Some(&ValueType::Element { code, .. }) if arena.value(code)
                == Some(&Value::Variable { zone: Zone::Intuitionistic, index: DeBruijnIndex::from(1_u32) })
        ),
        "a type recorded two binders deep reads the same: {:?}",
        arena.value_type(typed)
    );
}

#[test]
fn an_omitted_implicit_is_typed_at_its_solution_1216()
{
    use gandr_core_term::CompType;
    use gandr_core_term::ValueType;
    use gandr_core_term::Zone;
    use gandr_core_term::hole::HoleId;
    use gandr_core_term::hole::NominationIndex;

    // def id : U ((a : Type) -> El a -> F (El a)) = thunk λ λ. return x ;
    // def k  : U (F Integer) = thunk ((force id) ?a) 0 ;   `same(3)`
    // The typed run keeps the instantiated head `(force id) ?a` at
    // `Integer -> F Integer`: the hole read as its solution, whose decode is
    // the integers.
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let small = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let element = arena.value_type_element(bound, Level::zero());
    let returns_element = arena.comp_type_returner(element);
    let arrow = arena.comp_type_arrow(element, returns_element);
    let polymorphic = arena.comp_type_pi(small, arrow);
    let identity_type = arena.value_type_thunk(polymorphic);
    let returned = arena.computation_return(bound);
    let inner = arena.computation_lambda(returned);
    let outer = arena.computation_lambda(inner);
    let identity = arena.value_thunk(outer);
    let returns_integer = arena.comp_type_returner(integer);
    let suspended = arena.value_type_thunk(returns_integer);
    let zero = arena.value_literal(integer_literal());
    let hole = arena.value_hole(
        HoleId::nominated(NominationIndex::from(0_u32)).expect("the first nominated name"),
    );
    let constant = arena.value_constant(ConstantIndex::from(0_usize));
    let forced = arena.computation_force(constant);
    let head = arena.computation_application(forced, hole);
    let applied = arena.computation_application(head, zero);
    let call = arena.value_thunk(applied);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let module = [
        declaration(
            At(0),
            Maybe::Present(identity_type),
            Maybe::Present(identity),
        ),
        declaration(At(1), Maybe::Present(suspended), Maybe::Present(call)),
    ];
    let run = type_module(&mut context, &module);
    assert!(
        run.refused().is_empty(),
        "both declarations check: {:?}",
        run.refused()
    );
    let typed = run.typings()[&ConstantIndex::from(1_usize)].typings();
    let headed = typed
        .iter()
        .find(|typing| typing.term == TermNode::Computation(head))
        .expect("the instantiated head is typed");
    let arena = context.arena();
    let TypeNode::Computation(at) = headed.ty
    else {
        panic!("a head synthesises a computation type: {headed:?}");
    };
    let Some(&CompType::Arrow { domain, .. }) = arena.comp_type(at)
    else {
        panic!(
            "the head takes the explicit argument: {:?}",
            arena.comp_type(at)
        );
    };
    assert_eq!(
        arena.value_type(domain),
        Some(&ValueType::Base(BaseType::Integer)),
        "the domain is the integers, the decode of the solution, not of the hole"
    );
}
