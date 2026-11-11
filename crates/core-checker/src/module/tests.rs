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

/// #3575: one declaration of the judgement a built-in role fits holds the
/// role. A second holder is refused by the first's position. A role on the
/// other judgement is refused by name. Neither refusal moves the holder, and
/// each is the source's fault. #5255: a value that holds `E` answers its
/// canonical body, which reads the pair type.
#[test]
fn a_builtin_role_is_held_once_by_a_declaration_of_its_judgement_3575()
{
    use gandr_kernel_term::Builtin;
    use gandr_kernel_term::Departure;

    let mut arena = CoreArena::new();
    let kind = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let zero = arena.value_literal(integer_literal());
    let codes = gandr_core_term::DataSignature::new(Vec::new(), Vec::from([Vec::new()]), kind);
    let codes = alloc::sync::Arc::new(codes);
    let canonical = crate::fixture::canonical_signature(&mut arena, ConstantIndex::from(0_usize));
    let canonical = alloc::sync::Arc::new(canonical);
    let again = crate::fixture::canonical_signature(&mut arena, ConstantIndex::from(2_usize));
    let again = alloc::sync::Arc::new(again);
    let data = |at: usize| {
        Declaration::data(
            ConstantIndex::from(at),
            alloc::sync::Arc::clone(&codes),
            OriginToken::from(at),
        )
    };
    let value = |at: usize| declaration(At(at), UNSIGNED, Maybe::Present(zero));
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let signature = Declaration::data(
        ConstantIndex::from(0_usize),
        canonical,
        OriginToken::from(0_usize),
    );
    assert_eq!(
        check_declaration(&mut context, &signature.built_in(Builtin::IrSignature)),
        Verdict::Data,
        "a datatype holds the signature role"
    );
    assert_eq!(
        check_declaration(&mut context, &value(1).built_in(Builtin::IrArgs)),
        Verdict::Refused(CheckRefusal::BuiltinNotCanonical {
            role: Builtin::IrArgs,
            departure: Departure::Reads(Builtin::IrPair),
        }),
        "`E` reads the pair type, and no declaration holds it"
    );
    let repeated = CheckRefusal::BuiltinRepeated {
        role: Builtin::IrSignature,
        holder: ConstantIndex::from(0_usize),
    };
    let second = Declaration::data(
        ConstantIndex::from(2_usize),
        again,
        OriginToken::from(2_usize),
    );
    assert_eq!(
        check_declaration(&mut context, &second.built_in(Builtin::IrSignature)),
        Verdict::Refused(repeated),
        "a second holder is refused by the first's position"
    );
    assert_eq!(
        check_declaration(&mut context, &value(3).built_in(Builtin::IrSignature)),
        Verdict::Refused(CheckRefusal::BuiltinMisplaced(Builtin::IrSignature)),
        "the signature role on a definition is refused"
    );
    assert_eq!(
        check_declaration(&mut context, &data(4).built_in(Builtin::IrDecode)),
        Verdict::Refused(CheckRefusal::BuiltinMisplaced(Builtin::IrDecode)),
        "the decode role on a datatype is refused"
    );
    let third =
        crate::fixture::canonical_signature(context.arena_mut(), ConstantIndex::from(5_usize));
    let third = Declaration::data(
        ConstantIndex::from(5_usize),
        alloc::sync::Arc::new(third),
        OriginToken::from(5_usize),
    );
    assert_eq!(
        check_declaration(&mut context, &third.built_in(Builtin::IrSignature)),
        Verdict::Refused(repeated),
        "the refusals leave the first holder in place"
    );
    let world = Declaration::world(
        ConstantIndex::from(6_usize),
        gandr_core_term::effect::EffectRow::EMPTY,
        OriginToken::from(6_usize),
    );
    assert_eq!(
        check_declaration(&mut context, &world.built_in(Builtin::IrArgs)),
        Verdict::Refused(CheckRefusal::BuiltinMisplaced(Builtin::IrArgs)),
        "a declaration that is neither data nor a value holds no role"
    );
    assert_eq!(
        check_declaration(&mut context, &value(7).built_in(Builtin::IrArgs)),
        Verdict::Refused(CheckRefusal::BuiltinNotCanonical {
            role: Builtin::IrArgs,
            departure: Departure::Reads(Builtin::IrPair),
        }),
        "the refused holder of `E` gave its role back, so the next one is no second holder"
    );
    assert_eq!(
        [
            repeated.classify(),
            CheckRefusal::BuiltinMisplaced(Builtin::IrDecode).classify()
        ],
        [FailureClass::MalformedSource; 2],
        "each refusal is the source's fault"
    );
}

/// #5255: the checker refuses the pair role on a datatype that departs from
/// the canonical pair type, naming the first departure. The refused
/// declaration holds no role, so a canonical datatype after it holds the role.
#[test]
fn a_pair_type_in_another_shape_holds_no_role_5255()
{
    use gandr_kernel_term::Builtin;
    use gandr_kernel_term::ConstructorTag;
    use gandr_kernel_term::Departure;
    use gandr_kernel_term::FieldPosition;

    let mut arena = CoreArena::new();
    let [parameters, fields] = crate::fixture::pair_parts(&mut arena);
    let kind = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let swapped = gandr_core_term::DataSignature::new(
        parameters,
        Vec::from([Vec::from([fields[1], fields[0]])]),
        kind,
    );
    let canonical = crate::fixture::canonical_pair(&mut arena);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let swapped = Declaration::data(
        ConstantIndex::from(0_usize),
        alloc::sync::Arc::new(swapped),
        OriginToken::from(0_usize),
    );
    let refusal = CheckRefusal::BuiltinNotCanonical {
        role: Builtin::IrPair,
        departure: Departure::Field {
            tag: ConstructorTag::from(0_usize),
            field: FieldPosition::from(0_usize),
        },
    };
    assert_eq!(
        check_declaration(&mut context, &swapped.built_in(Builtin::IrPair)),
        Verdict::Refused(refusal),
        "the fields in the other order depart at the first field"
    );
    let canonical = Declaration::data(
        ConstantIndex::from(1_usize),
        alloc::sync::Arc::new(canonical),
        OriginToken::from(1_usize),
    );
    assert_eq!(
        check_declaration(&mut context, &canonical.built_in(Builtin::IrPair)),
        Verdict::Data,
        "the refused datatype held no role, so the canonical one takes it"
    );
}

/// #5254: the checker refuses the signature role on a datatype that departs
/// from the canonical signature type, naming the first departure. The refused
/// declaration holds no role, so a canonical datatype after it holds the role.
#[test]
fn a_signature_type_in_another_shape_holds_no_role_5254()
{
    use gandr_kernel_term::Builtin;
    use gandr_kernel_term::ConstructorTag;
    use gandr_kernel_term::Departure;
    use gandr_kernel_term::FieldPosition;

    let mut arena = CoreArena::new();
    let [parameters, iota, sigma, delta] =
        crate::fixture::signature_parts(&mut arena, ConstantIndex::from(0_usize));
    let kind = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let swapped =
        gandr_core_term::DataSignature::new(parameters, Vec::from([iota, delta, sigma]), kind);
    let canonical = crate::fixture::canonical_signature(&mut arena, ConstantIndex::from(1_usize));
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let swapped = Declaration::data(
        ConstantIndex::from(0_usize),
        alloc::sync::Arc::new(swapped),
        OriginToken::from(0_usize),
    );
    let refusal = CheckRefusal::BuiltinNotCanonical {
        role: Builtin::IrSignature,
        departure: Departure::Field {
            tag: ConstructorTag::from(1_usize),
            field: FieldPosition::from(1_usize),
        },
    };
    assert_eq!(
        check_declaration(&mut context, &swapped.built_in(Builtin::IrSignature)),
        Verdict::Refused(refusal),
        "σ and δ in the other order depart at σ's function"
    );
    assert_eq!(
        refusal.classify(),
        FailureClass::MalformedSource,
        "the departure is the source's fault"
    );
    let canonical = Declaration::data(
        ConstantIndex::from(1_usize),
        alloc::sync::Arc::new(canonical),
        OriginToken::from(1_usize),
    );
    assert_eq!(
        check_declaration(&mut context, &canonical.built_in(Builtin::IrSignature)),
        Verdict::Data,
        "the refused datatype held no role, so the canonical one takes it"
    );
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
    // def given : Path[.A = U (…)](thunk { force j }, k) = here(k) ;
    // def law : Path[.A = U (…)](k, k) = given ;
    // def again : Path[.A = U (…)](thunk { force j }, k) = given ;
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
        [
            ConstantIndex::from(0_usize),
            ConstantIndex::from(2_usize),
            ConstantIndex::from(3_usize)
        ],
        "the two refused bodies and the unformed signature keep their failures; \
             the accepted body keeps none"
    );
    assert_eq!(
        report.failures()[&ConstantIndex::from(2_usize)].refusal(),
        CheckRefusal::OutOfFragment {
            at: CoreNode::Type(TypeNode::Value(unformed)),
            former: UnadmittedFormer::NumericAtom,
        },
        "the unformed signature keeps the failure forming it (#4043)"
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

/// A variable read past the binders between it and its slot is typed at a
/// copy of its slot's type: the record keeps the copy beside the type it
/// copies, so a reader that names the slot's type names the copy alike.
#[test]
fn a_variable_s_type_keeps_the_copies_its_reading_mints()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    // `(n : Integer) -> (r : (x : Integer) * Path[.A = Integer](n, x)) -> F
    // Integer`.
    let [own, outer] = [0_u32, 1].map(|index| {
        arena.value_variable(
            gandr_core_term::Zone::Intuitionistic,
            DeBruijnIndex::from(index),
        )
    });
    let path = arena.value_type_path(integer, outer, own);
    let sigma = arena.value_type_sigma(integer, path);
    let returns = arena.comp_type_returner(integer);
    let inner = arena.comp_type_pi(sigma, returns);
    let outer_pi = arena.comp_type_pi(integer, inner);
    let declared = arena.value_type_thunk(outer_pi);
    // `λn. λr. r.0`.
    let projected =
        arena.computation_tuple_projection(own, gandr_kernel_term::Component::from(0_usize));
    let inner_lambda = arena.computation_lambda(projected);
    let outer_lambda = arena.computation_lambda(inner_lambda);
    let defined = arena.value_thunk(outer_lambda);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let module = [declaration(
        At(0),
        Maybe::Present(declared),
        Maybe::Present(defined),
    )];
    let run = type_module(&mut context, &module);
    assert!(
        run.refused().is_empty(),
        "the declaration checks: {:?}",
        run.refused()
    );
    let typed = &run.typings()[&ConstantIndex::from(0_usize)];
    let copies: alloc::collections::BTreeSet<gandr_core_term::Carried> =
        typed.copies().iter().copied().collect();
    let copied = typed
        .typings()
        .iter()
        .filter(|typing| typing.term == TermNode::Value(own))
        .find_map(|typing| match typing.ty {
            TypeNode::Value(copy) => copies
                .contains(&gandr_core_term::Carried::ValueType(sigma, copy))
                .then_some(copy),
            TypeNode::Computation(_) => None,
        });
    assert!(
        copied.is_some_and(|copy| copy != sigma),
        "the variable is typed at a copy of its slot's type, kept beside it: {typed:?}"
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
    let [inner_x, expected_x, expected_inner_r] = [(); 3].map(|()| {
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
        let lambda = arena.computation_lambda(ran);
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
        "the inner call runs inside the outer one's computation, and the outer, which the \
         return only returns, is the body"
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
        [inner],
        "the inner run is reported beside the bind minted for it; the outer, which its region \
         only returns, mints none"
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
    // `point = fun (n) { return #{a = n, b = n} }` and
    // `moved = fun (n) { return #{point(n) | a = 0} }`.
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

/// #5578: a value of a record type stands at a patched type of it by the
/// coercion in. The judgement records the fixed fields it compared at the
/// value, and the value crosses as its restriction to the free fields, whose
/// conversions the kernel replays. A value whose field is another value is
/// refused at the value, least label first. A crossing with one comparison
/// removed keeps that field, and the kernel refuses it by the field's label.
#[test]
fn a_base_value_at_a_patched_type_crosses_as_a_restriction_5578()
{
    let mut arena = CoreArena::new();
    let label = |name: &str| gandr_kernel_term::FieldLabel::from(alloc::string::String::from(name));
    let integer = arena.value_type_base(BaseType::Integer);
    let zero = arena.value_literal(integer_literal());
    let one = arena.value_literal(gandr_kernel_term::Literal::Integer(
        gandr_kernel_term::IntegerLiteral::new(
            gandr_kernel_term::Sign::NonNegative,
            gandr_kernel_term::Magnitude::from_decimal_text(alloc::string::String::from("1"))
                .expect("decimal digits"),
        ),
    ));
    // `base : *{host, port, tls : Integer} = *{.host = 0, .port = 0, .tls = 0}`
    // and `other` the same record with its port at 1.
    let record_type = arena.value_type_record(alloc::collections::BTreeMap::from([
        (label("host"), integer),
        (label("port"), integer),
        (label("tls"), integer),
    ]));
    let base = arena.value_record(alloc::collections::BTreeMap::from([
        (label("host"), zero),
        (label("port"), zero),
        (label("tls"), zero),
    ]));
    let other = arena.value_record(alloc::collections::BTreeMap::from([
        (label("host"), zero),
        (label("port"), one),
        (label("tls"), zero),
    ]));
    // `secured : *{…}[.port = 0, .tls = 0] = base` and the same of `other`.
    let fixed = alloc::collections::BTreeMap::from([(label("port"), zero), (label("tls"), zero)]);
    let patched = arena.value_type_patched(record_type, fixed.clone());
    let named = arena.value_constant(ConstantIndex::from(0_usize));
    let named_other = arena.value_constant(ConstantIndex::from(2_usize));
    let mut report = {
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        check_module(&mut context, &[
            declaration(At(0), Maybe::Present(record_type), Maybe::Present(base)),
            declaration(At(1), Maybe::Present(patched), Maybe::Present(named)),
            declaration(At(2), Maybe::Present(record_type), Maybe::Present(other)),
            declaration(At(3), Maybe::Present(patched), Maybe::Present(named_other)),
        ])
    };
    let Verdict::Checked { body, .. } = report.judged()[1].verdict()
    else {
        panic!(
            "a value whose fixed fields convert checks: {:?}",
            report.judged()[1].verdict()
        );
    };
    assert_eq!(
        body, named,
        "the body runs as written: the coercion copies no record at run time"
    );
    assert_eq!(
        report.coercions().get(&named),
        Some(&fixed),
        "the judgement records both fixed fields at the value it coerced in"
    );
    assert_eq!(
        report.judged()[3].verdict(),
        Verdict::Refused(CheckRefusal::FixedFieldDiffers {
            at: named_other,
            fixed: zero,
        }),
        "a value whose port is another value is refused at the value, by the port"
    );
    let readmission = crate::bridge::readmit(&mut arena, &report);
    let crate::bridge::Outcome::Defined { admitted, .. } = *readmission.readmitted()[1].outcome()
    else {
        panic!(
            "the kernel admits the restriction: {:?}",
            readmission.readmitted()[1].outcome()
        );
    };
    let environment = readmission.environment();
    let entry = environment
        .entries()
        .get(usize::from(admitted.position()))
        .expect("the admitted position holds an entry");
    let gandr_kernel_term::DeclarationContent::Def { body, .. } = *entry.declaration().content()
    else {
        panic!("the coerced value is admitted as a definition");
    };
    assert!(
        matches!(environment.arena().value(body), Some(gandr_kernel_term::Value::Restrict { fixed, .. })
            if fixed.keys().eq([&label("port"), &label("tls")])),
        "the value crosses as its restriction at both fixed fields: {:?}",
        environment.arena().value(body)
    );
    report
        .coercions
        .get_mut(&named)
        .expect("the coercion is recorded")
        .remove(&label("tls"));
    let readmission = crate::bridge::readmit(&mut arena, &report);
    assert_eq!(
        readmission.readmitted()[1].outcome(),
        &crate::bridge::Outcome::Rejected(gandr_kernel_core::KernelError::KeptRecordField {
            label: label("tls"),
        }),
        "a crossing that drops the comparison of `tls` keeps it, and the kernel refuses it by `tls`"
    );
}

/// #5106: a system of faces forms where each later face's value on a meet
/// converts with the value the first face fixes there, and is refused at that
/// value where it does not.
#[test]
fn a_system_of_faces_is_formed_where_its_faces_agree_on_their_meet_5106()
{
    let mut arena = CoreArena::new();
    let label = |name: &str| gandr_kernel_term::FieldLabel::from(alloc::string::String::from(name));
    let integer = arena.value_type_base(BaseType::Integer);
    let zero = arena.value_literal(integer_literal());
    let also_zero = arena.value_literal(integer_literal());
    let one = arena.value_literal(gandr_kernel_term::Literal::Integer(
        gandr_kernel_term::IntegerLiteral::new(
            gandr_kernel_term::Sign::NonNegative,
            gandr_kernel_term::Magnitude::from_decimal_text(alloc::string::String::from("1"))
                .expect("decimal digits"),
        ),
    ));
    // `*{host, port, tls, mode : Integer}[secure ↦ {port, tls}, addr ↦ {host,
    // port}]`: the glued fixed map, and `addr`'s port on the meet, at a second
    // zero and at one.
    let record_type = arena.value_type_record(alloc::collections::BTreeMap::from([
        (label("host"), integer),
        (label("mode"), integer),
        (label("port"), integer),
        (label("tls"), integer),
    ]));
    let fixed = alloc::collections::BTreeMap::from([
        (label("host"), zero),
        (label("port"), zero),
        (label("tls"), zero),
    ]);
    let agreeing = arena.value_type_system(record_type, fixed.clone(), alloc::vec![(
        label("port"),
        also_zero
    )]);
    let disagreeing =
        arena.value_type_system(record_type, fixed, alloc::vec![(label("port"), one)]);
    let free = arena.value_record(alloc::collections::BTreeMap::from([(label("mode"), zero)]));
    let report = {
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        check_module(&mut context, &[
            declaration(At(0), Maybe::Present(agreeing), Maybe::Present(free)),
            declaration(At(1), Maybe::Present(disagreeing), Maybe::Present(free)),
        ])
    };
    assert!(
        matches!(report.judged()[0].verdict(), Verdict::Checked { .. }),
        "faces that agree on their meet form a type: {:?}",
        report.judged()[0].verdict()
    );
    assert_eq!(
        report.judged()[1].verdict(),
        Verdict::Refused(CheckRefusal::FixedFieldDiffers {
            at: one,
            fixed: zero,
        }),
        "faces that disagree on their meet are refused at the later face's port"
    );
}

/// #5663: the kernel replays the formation of a patched type and the meets of
/// its faces. Each crossing admits a record of the fixed fields at their
/// field's types and that record's restriction at the glued values, so a meet
/// costs one kernel conversion. A crossing whose meet value differs from the
/// glued value, or whose glued value has another type, is refused by `port`.
#[test]
fn a_patched_type_crosses_its_formation_and_the_meets_of_its_faces_5663()
{
    let mut arena = CoreArena::new();
    let label = |name: &str| gandr_kernel_term::FieldLabel::from(alloc::string::String::from(name));
    let integer = arena.value_type_base(BaseType::Integer);
    let zero = arena.value_literal(integer_literal());
    let also_zero = arena.value_literal(integer_literal());
    let eighty = arena.value_literal(gandr_kernel_term::Literal::Integer(
        gandr_kernel_term::IntegerLiteral::new(
            gandr_kernel_term::Sign::NonNegative,
            gandr_kernel_term::Magnitude::from_decimal_text(alloc::string::String::from("80"))
                .expect("decimal digits"),
        ),
    ));
    let unit = arena.value_unit();
    let truth = arena.value_injection(gandr_core_term::Summand::from(1_usize), unit);
    // `*{host, port, tls, mode : Integer}[secure ↦ {port, tls}, addr ↦ {host,
    // port}]`, whose faces agree on `port`.
    let record_type = arena.value_type_record(alloc::collections::BTreeMap::from([
        (label("host"), integer),
        (label("mode"), integer),
        (label("port"), integer),
        (label("tls"), integer),
    ]));
    let fixed = alloc::collections::BTreeMap::from([
        (label("host"), zero),
        (label("port"), zero),
        (label("tls"), zero),
    ]);
    let agreeing = arena.value_type_system(record_type, fixed.clone(), alloc::vec![(
        label("port"),
        also_zero
    )]);
    let free = arena.value_record(alloc::collections::BTreeMap::from([(label("mode"), zero)]));
    let mut report = {
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        check_module(&mut context, &[declaration(
            At(0),
            Maybe::Present(agreeing),
            Maybe::Present(free),
        )])
    };
    let Verdict::Checked { body, evidence, .. } = report.judged()[0].verdict()
    else {
        panic!(
            "faces that agree on their meet form a type: {:?}",
            report.judged()[0].verdict()
        );
    };
    let readmission = crate::bridge::readmit(&mut arena, &report);
    let crate::bridge::Outcome::Defined { admitted, .. } = *readmission.readmitted()[0].outcome()
    else {
        panic!(
            "the kernel admits the declaration after its formation: {:?}",
            readmission.readmitted()[0].outcome()
        );
    };
    let environment = readmission.environment();
    let restriction = usize::from(admitted.position())
        .checked_sub(1)
        .and_then(|at| environment.entries().get(at))
        .expect("the formation's restriction crosses just before the declaration");
    let gandr_kernel_term::DeclarationContent::Def { body: crossed, .. } =
        *restriction.declaration().content()
    else {
        panic!("the meet crosses as a definition");
    };
    assert!(
        matches!(environment.arena().value(crossed), Some(gandr_kernel_term::Value::Restrict { fixed, .. })
            if fixed.keys().eq([&label("port")])),
        "the meet crosses as the restriction at `port` alone, one conversion for its one meet \
         field: {:?}",
        environment.arena().value(crossed)
    );
    // A crossing whose later face holds 80 at the meet: the kernel converts
    // it with the glued 0 and refuses it by `port`.
    let differing = arena.value_type_system(record_type, fixed.clone(), alloc::vec![(
        label("port"),
        eighty
    )]);
    report.judged[0].verdict = Verdict::Checked {
        declared: crate::formation::FormedValueType::derived(differing),
        body,
        evidence,
    };
    assert_eq!(
        crate::bridge::readmit(&mut arena, &report).readmitted()[0].outcome(),
        &crate::bridge::Outcome::Rejected(gandr_kernel_core::KernelError::FixedFieldDiffers {
            label: label("port"),
        }),
        "a meet value that does not convert with the glued value is refused by its label"
    );
    // A crossing whose glued value at `port` is `true`, of another type
    // than the port's: the kernel refuses it at `port`.
    let mut mistyped = fixed;
    mistyped.insert(label("port"), truth);
    let mistyped = arena.value_type_system(record_type, mistyped, alloc::vec![(
        label("port"),
        also_zero
    )]);
    report.judged[0].verdict = Verdict::Checked {
        declared: crate::formation::FormedValueType::derived(mistyped),
        body,
        evidence,
    };
    let readmission = crate::bridge::readmit(&mut arena, &report);
    assert!(
        matches!(
            readmission.readmitted()[0].outcome(),
            crate::bridge::Outcome::Rejected(gandr_kernel_core::KernelError::FieldRefused {
                label: refused,
                ..
            }) if *refused == label("port")
        ),
        "a glued value of another type than its field's is refused at its label: {:?}",
        readmission.readmitted()[0].outcome()
    );
}

/// #5748: two equal patched types at two core nodes cross one formation, and
/// two that differ in one fixed value cross two. A formation with no meet
/// crosses one record witness, ahead of the first declaration that holds it.
#[test]
fn equal_patched_types_share_one_formation_5748()
{
    let label = |name: &str| gandr_kernel_term::FieldLabel::from(alloc::string::String::from(name));
    let one = || {
        gandr_kernel_term::Literal::Integer(gandr_kernel_term::IntegerLiteral::new(
            gandr_kernel_term::Sign::NonNegative,
            gandr_kernel_term::Magnitude::from_decimal_text(alloc::string::String::from("1"))
                .expect("decimal digits"),
        ))
    };
    // `*{port, tls : Integer}[.port = n]`, minted at a node of its own for each
    // declaration, and each declaration's body the record of its free field.
    let crossed = |ports: [gandr_kernel_term::Literal; 2]| {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let record_type = arena.value_type_record(alloc::collections::BTreeMap::from([
            (label("port"), integer),
            (label("tls"), integer),
        ]));
        let module = ports.map(|port| {
            let port = arena.value_literal(port);
            let system = arena.value_type_system(
                record_type,
                alloc::collections::BTreeMap::from([(label("port"), port)]),
                alloc::vec::Vec::new(),
            );
            let tls = arena.value_literal(integer_literal());
            let free =
                arena.value_record(alloc::collections::BTreeMap::from([(label("tls"), tls)]));
            (system, free)
        });
        assert_ne!(
            module[0].0, module[1].0,
            "each declaration holds its own core node"
        );
        let module = [0_usize, 1].map(|at| {
            declaration(
                At(at),
                Maybe::Present(module[at].0),
                Maybe::Present(module[at].1),
            )
        });
        let report = {
            let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
            check_module(&mut context, &module)
        };
        let readmission = crate::bridge::readmit(&mut arena, &report);
        for entry in readmission.readmitted() {
            assert!(
                matches!(entry.outcome(), crate::bridge::Outcome::Defined { .. }),
                "each declaration crosses after its formation: {:?}",
                entry.outcome()
            );
        }
        readmission.environment().entries().len()
    };
    assert_eq!(
        crossed([integer_literal(), integer_literal()]),
        3,
        "two equal formations cross one record witness, then the two declarations"
    );
    assert_eq!(
        crossed([integer_literal(), one()]),
        4,
        "formations that differ at `port` cross one record witness each"
    );
}

/// #5748: the key of a formation holds its glued values beside its meets. Two
/// formations whose meets hold 80 at `port` share no witness when one glues 80
/// and the other glues 0 there. Their first witnesses are equal records, but
/// the kernel still converts the second meet and refuses it by `port`.
#[test]
fn equal_meets_over_other_glued_values_share_no_formation_5748()
{
    let mut arena = CoreArena::new();
    let label = |name: &str| gandr_kernel_term::FieldLabel::from(alloc::string::String::from(name));
    let eighty = || {
        gandr_kernel_term::Literal::Integer(gandr_kernel_term::IntegerLiteral::new(
            gandr_kernel_term::Sign::NonNegative,
            gandr_kernel_term::Magnitude::from_decimal_text(alloc::string::String::from("80"))
                .expect("decimal digits"),
        ))
    };
    let integer = arena.value_type_base(BaseType::Integer);
    let record_type = arena.value_type_record(alloc::collections::BTreeMap::from([
        (label("port"), integer),
        (label("tls"), integer),
    ]));
    // `*{port, tls : Integer}` whose later face holds 80 at its meet `port`,
    // glued at `glued`.
    let system = |arena: &mut CoreArena, glued: gandr_kernel_term::Literal| {
        let glued = arena.value_literal(glued);
        let meet = arena.value_literal(eighty());
        arena.value_type_system(
            record_type,
            alloc::collections::BTreeMap::from([(label("port"), glued)]),
            alloc::vec![(label("port"), meet)],
        )
    };
    let agreeing = [system(&mut arena, eighty()), system(&mut arena, eighty())];
    let module = [0_usize, 1].map(|at| {
        let tls = arena.value_literal(integer_literal());
        let free = arena.value_record(alloc::collections::BTreeMap::from([(label("tls"), tls)]));
        declaration(At(at), Maybe::Present(agreeing[at]), Maybe::Present(free))
    });
    let mut report = {
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        check_module(&mut context, &module)
    };
    let Verdict::Checked { body, evidence, .. } = report.judged()[1].verdict()
    else {
        panic!(
            "faces that agree on their meet form a type: {:?}",
            report.judged()[1].verdict()
        );
    };
    let differing = system(&mut arena, integer_literal());
    report.judged[1].verdict = Verdict::Checked {
        declared: crate::formation::FormedValueType::derived(differing),
        body,
        evidence,
    };
    let readmission = crate::bridge::readmit(&mut arena, &report);
    assert!(
        matches!(
            readmission.readmitted()[0].outcome(),
            crate::bridge::Outcome::Defined { .. }
        ),
        "the glued 80 converts with its meet: {:?}",
        readmission.readmitted()[0].outcome()
    );
    assert_eq!(
        readmission.readmitted()[1].outcome(),
        &crate::bridge::Outcome::Rejected(gandr_kernel_core::KernelError::FixedFieldDiffers {
            label: label("port"),
        }),
        "the glued 0 shares no formation with the glued 80, so its meet is refused by its label"
    );
}

/// #5579: an element of a patched type stands at its base by the coercion out,
/// as the record of its free fields beside the values the type fixes; a
/// selection of a fixed field reads the fixed value. A nested computation
/// whose result stands at the base runs before the record is built. The
/// kernel admits each body as it admits any record.
#[test]
fn an_element_of_a_patched_type_stands_at_its_base_as_its_record_5579()
{
    let mut arena = CoreArena::new();
    let label = |name: &str| gandr_kernel_term::FieldLabel::from(alloc::string::String::from(name));
    let integer = arena.value_type_base(BaseType::Integer);
    let zero = arena.value_literal(integer_literal());
    // `secured : *{host, port, tls : Integer}[.port = 0, .tls = 0] = *{.host = 0}`.
    let record_type = arena.value_type_record(alloc::collections::BTreeMap::from([
        (label("host"), integer),
        (label("port"), integer),
        (label("tls"), integer),
    ]));
    let fixed = alloc::collections::BTreeMap::from([(label("port"), zero), (label("tls"), zero)]);
    let patched = arena.value_type_patched(record_type, fixed);
    let free = arena.value_record(alloc::collections::BTreeMap::from([(label("host"), zero)]));
    // `whole : *{…} = secured`, `port : Integer = ⟨secured.port⟩` and
    // `ran : *{…} = ⟨return secured⟩`.
    let whole = arena.value_constant(ConstantIndex::from(0_usize));
    let selected = arena.value_constant(ConstantIndex::from(0_usize));
    let projection = arena.computation_record_projection(selected, label("port"));
    let port = arena.value_returned(projection);
    let returned = arena.value_constant(ConstantIndex::from(0_usize));
    let returning = arena.computation_return(returned);
    let ran = arena.value_nested(returning);
    let report = {
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        check_module(&mut context, &[
            declaration(At(0), Maybe::Present(patched), Maybe::Present(free)),
            declaration(At(1), Maybe::Present(record_type), Maybe::Present(whole)),
            declaration(At(2), Maybe::Present(integer), Maybe::Present(port)),
            declaration(At(3), Maybe::Present(record_type), Maybe::Present(ran)),
        ])
    };
    let body = |at: usize| {
        let Verdict::Checked { body, .. } = report.judged()[at].verdict()
        else {
            panic!(
                "declaration {at} checks: {:?}",
                report.judged()[at].verdict()
            );
        };
        body
    };
    assert_eq!(
        body(0),
        free,
        "the element keeps the record of its free fields"
    );
    let Some(gandr_core_term::Value::Record(fields)) = arena.value(body(1)).cloned()
    else {
        panic!("the element stands as a record: {:?}", arena.value(body(1)));
    };
    assert_eq!(
        (fields.get(&label("port")), fields.get(&label("tls"))),
        (Some(&zero), Some(&zero)),
        "the record holds the values the type fixes"
    );
    assert!(
        matches!(
            fields.get(&label("host")).and_then(|&host| arena.value(host)),
            Some(&gandr_core_term::Value::Returned(read))
                if arena.computation(read) == Some(&gandr_core_term::Computation::RecordProjection(whole, label("host")))
        ),
        "the record reads its free field off the element: {fields:?}"
    );
    let Some(&gandr_core_term::Value::Returned(read)) = arena.value(body(2))
    else {
        panic!(
            "the selection stands as what it returns: {:?}",
            arena.value(body(2))
        );
    };
    let Some(&gandr_core_term::Computation::RecordProjection(record, ref projected)) =
        arena.computation(read)
    else {
        panic!("the selection projects: {:?}", arena.computation(read));
    };
    assert_eq!(projected, &label("port"));
    assert_eq!(
        arena.value(record),
        Some(&gandr_core_term::Value::Record(
            alloc::collections::BTreeMap::from([(label("port"), zero)])
        )),
        "a fixed field is read off the record of the value the type fixes"
    );
    // `ran` binds the run once, and its record reads the free field off what
    // the run bound: `⟨x ← return secured; return *{.host = ⟨x.host⟩, …}⟩`.
    let expected_ran = {
        let bound = arena.value_variable(
            gandr_core_term::Zone::Intuitionistic,
            DeBruijnIndex::from(0_u32),
        );
        let host = arena.computation_record_projection(bound, label("host"));
        let host = arena.value_returned(host);
        let record = arena.value_record(alloc::collections::BTreeMap::from([
            (label("host"), host),
            (label("port"), zero),
            (label("tls"), zero),
        ]));
        let built = arena.computation_return(record);
        let secured = arena.value_constant(ConstantIndex::from(0_usize));
        let first = arena.computation_return(secured);
        let bind = arena.computation_bind(first, built);
        arena.value_returned(bind)
    };
    assert_eq!(
        gandr_core_term::equal_certificate_syntax(&arena, body(3), expected_ran),
        gandr_core_term::CertificateEquality::Equal,
        "the run is bound once, before the record of what it returns"
    );
    let readmission = crate::bridge::readmit(&mut arena, &report);
    assert!(
        readmission.readmitted().iter().all(|readmitted| matches!(
            readmitted.outcome(),
            crate::bridge::Outcome::Defined { .. }
        )),
        "the kernel admits each record at the base: {readmission:?}"
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
    // `commute : Path[.A = R](#{#{point | x = 0} | y = 0}, #{#{point | y = 0} | x =
    // 0})`.
    let commuted = {
        let first = written(&mut arena, point, "x");
        let left = written(&mut arena, first, "y");
        let second = written(&mut arena, point, "y");
        let right = written(&mut arena, second, "x");
        arena.value_type_path(pair_type, left, right)
    };
    let commute = arena.value_here(pair);
    // `unchanged : Path[.A = R](#{point | x = 0}, point)`.
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
        [(site, Maybe::Present(ConstantIndex::from(0_usize)), 0)],
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

/// Beside a kept reduct, a value at one owed code's decode where another's is
/// wanted is still apart: the crossing's comparisons are decided rigidly, so
/// neither decode converts with the reduct's types by a residual, and no
/// reduct runs in the definition's value.
#[test]
fn an_owed_decode_crosses_by_no_reduct()
{
    let mut arena = CoreArena::new();
    let universe = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let integer = arena.value_type_base(BaseType::Integer);
    // `reduct = thunk(λn. return n)`, a map from the integers to the integers.
    let reduct_type = {
        let returns = arena.comp_type_returner(integer);
        let arrow = arena.comp_type_arrow(integer, returns);
        arena.value_type_thunk(arrow)
    };
    let reduct = {
        let bound = arena.value_variable(
            gandr_core_term::Zone::Intuitionistic,
            DeBruijnIndex::from(0_u32),
        );
        let returned = arena.computation_return(bound);
        let lambda = arena.computation_lambda(returned);
        arena.value_thunk(lambda)
    };
    let decode = |arena: &mut CoreArena, at: usize| {
        let code = arena.value_constant(ConstantIndex::from(at));
        arena.value_type_element(code, Level::zero())
    };
    let code = decode(&mut arena, 1);
    let other = decode(&mut arena, 2);
    let held = arena.value_constant(ConstantIndex::from(3_usize));
    let report = {
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        context.keep_reducts(&[ConstantIndex::from(0_usize)]);
        check_module(&mut context, &[
            declaration(At(0), Maybe::Present(reduct_type), Maybe::Present(reduct)),
            declaration(At(1), Maybe::Present(universe), HOLE),
            declaration(At(2), Maybe::Present(universe), HOLE),
            declaration(At(3), Maybe::Present(other), HOLE),
            declaration(At(4), Maybe::Present(code), Maybe::Present(held)),
        ])
    };
    assert!(
        matches!(
            report.judged()[4].verdict(),
            Verdict::Refused(CheckRefusal::TypeMismatch(_))
        ),
        "two owed decodes stay apart, the reduct crossing neither: {:?}",
        report.judged()[4].verdict()
    );
}

/// The fixture of the literal readers: `word : U(Integer → F String)` reads
/// every natural as the same string, `flag` and `bit : U(Integer → F
/// Character)` are owed, `taker : U(String → F Integer)` and `chooser :
/// U(Character → F Integer)` are owed, and the declaration at 5 is
/// `thunk(callee(n))` at `U(F Integer)`, `n` the literal `written`. The checker
/// keeps `kept` as its readers.
///
/// # Specification
/// trivial.
fn read_literal(
    kept: &[gandr_core_term::LiteralReader],
    callee: ConstantIndex,
    written: gandr_kernel_term::Literal,
) -> (CoreArena, super::ModuleReport, ValueId)
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let text = arena.value_type_base(BaseType::String);
    let boolean = arena.value_type_base(BaseType::Character);
    let thunk_of = |arena: &mut CoreArena, domain, result| {
        let returns = arena.comp_type_returner(result);
        let arrow = arena.comp_type_arrow(domain, returns);
        arena.value_type_thunk(arrow)
    };
    let word_type = thunk_of(&mut arena, integer, text);
    let word = {
        let read = arena.value_literal(text_literal());
        let returned = arena.computation_return(read);
        let lambda = arena.computation_lambda(returned);
        arena.value_thunk(lambda)
    };
    let flag_type = thunk_of(&mut arena, integer, boolean);
    let taker_type = thunk_of(&mut arena, text, integer);
    let chooser_type = thunk_of(&mut arena, boolean, integer);
    let user_type = {
        let returns = arena.comp_type_returner(integer);
        arena.value_type_thunk(returns)
    };
    let literal = arena.value_literal(written);
    let user = {
        let called = call(&mut arena, callee, literal);
        arena.value_thunk(called)
    };
    let report = {
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        context.keep_readers(kept);
        check_module(&mut context, &[
            declaration(At(0), Maybe::Present(word_type), Maybe::Present(word)),
            declaration(At(1), Maybe::Present(flag_type), HOLE),
            declaration(At(2), Maybe::Present(flag_type), HOLE),
            declaration(At(3), Maybe::Present(taker_type), HOLE),
            declaration(At(4), Maybe::Present(chooser_type), HOLE),
            declaration(At(5), Maybe::Present(user_type), Maybe::Present(user)),
        ])
    };
    (arena, report, literal)
}

/// #4528: a natural literal checked at a type apart from `Integer` crosses by
/// the one kept reader whose result is that type, recorded at the literal, and
/// the kernel re-derives the application; with no reader kept it is refused.
#[test]
fn a_natural_literal_crosses_by_the_reader_of_its_type_4528()
{
    let readers = naturals(&[ConstantIndex::from(0_usize), ConstantIndex::from(1_usize)]);
    let (mut arena, report, literal) =
        read_literal(&readers, ConstantIndex::from(3_usize), integer_literal());
    assert!(
        matches!(report.judged()[5].verdict(), Verdict::Checked { .. }),
        "the literal checks where text is asked: {:?}",
        report.judged()[5].verdict()
    );
    assert_eq!(
        report.nested_elaborations()[&ConstantIndex::from(5_usize)]
            .crossings()
            .iter()
            .map(|(&at, crossing)| (at, crossing.by, crossing.carriers.len()))
            .collect::<Vec<_>>(),
        [(literal, Maybe::Present(ConstantIndex::from(0_usize)), 0)],
        "the crossing is recorded at the literal, by the text reader alone"
    );
    let readmission = crate::bridge::readmit(&mut arena, &report);
    assert!(
        readmission.readmitted().iter().all(|readmitted| matches!(
            readmitted.outcome(),
            crate::bridge::Outcome::Defined { .. } | crate::bridge::Outcome::Assumed { .. }
        )),
        "the kernel re-derives the application of the reader: {readmission:?}"
    );
    let (_, unkept, _) = read_literal(&[], ConstantIndex::from(3_usize), integer_literal());
    assert!(
        matches!(
            unkept.judged()[5].verdict(),
            Verdict::Refused(CheckRefusal::TypeMismatch(_))
        ),
        "with no reader kept, the literal is refused where text is asked: {:?}",
        unkept.judged()[5].verdict()
    );
}

/// #4812: a natural literal written as a definition's own value, at a type a
/// reader answers, crosses by the reader, and the reader's call is pure: the
/// definition stands as the value the call returns, which the kernel types.
#[test]
fn a_literal_read_in_a_definition_s_own_value_stands_as_its_reading_4812()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let text = arena.value_type_base(BaseType::String);
    let word_type = {
        let returns = arena.comp_type_returner(text);
        let arrow = arena.comp_type_arrow(integer, returns);
        arena.value_type_thunk(arrow)
    };
    let word = {
        let read = arena.value_literal(text_literal());
        let returned = arena.computation_return(read);
        let lambda = arena.computation_lambda(returned);
        arena.value_thunk(lambda)
    };
    let literal = arena.value_literal(integer_literal());
    let report = {
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        context.keep_readers(&naturals(&[ConstantIndex::from(0_usize)]));
        check_module(&mut context, &[
            declaration(At(0), Maybe::Present(word_type), Maybe::Present(word)),
            declaration(At(1), Maybe::Present(text), Maybe::Present(literal)),
        ])
    };
    assert!(
        matches!(report.judged()[1].verdict(), Verdict::Checked { .. }),
        "the reader's call stands in the definition's own value, and it is pure: {:?}",
        report.judged()[1].verdict()
    );
    assert!(
        matches!(
            report
                .definitions()
                .get(&ConstantIndex::from(1_usize))
                .and_then(|&body| arena.value(body)),
            Some(&gandr_core_term::Value::Returned(_))
        ),
        "the definition is the value the reader's call returns"
    );
    let readmission = crate::bridge::readmit(&mut arena, &report);
    assert!(
        readmission.readmitted().iter().all(|readmitted| matches!(
            readmitted.outcome(),
            crate::bridge::Outcome::Defined { .. } | crate::bridge::Outcome::Assumed { .. }
        )),
        "the kernel types the returned call: {readmission:?}"
    );
}

/// #4528: a literal at a type two kept readers answer is refused naming the
/// literal and the type, and one reader of it crosses.
#[test]
fn a_literal_two_readers_answer_is_ambiguous_4528()
{
    let both = naturals(&[
        ConstantIndex::from(0_usize),
        ConstantIndex::from(1_usize),
        ConstantIndex::from(2_usize),
    ]);
    let (arena, report, literal) =
        read_literal(&both, ConstantIndex::from(4_usize), integer_literal());
    let Verdict::Refused(CheckRefusal::LiteralAmbiguous { at, expected }) =
        report.judged()[5].verdict()
    else {
        panic!(
            "two character readers leave the literal ambiguous: {:?}",
            report.judged()[5].verdict()
        );
    };
    assert_eq!(at, literal, "the refusal names the literal");
    assert!(
        matches!(
            arena.value_type(expected),
            Some(gandr_core_term::ValueType::Base(BaseType::Character))
        ),
        "the refusal names the character type the literal stands at"
    );
    let one = naturals(&[ConstantIndex::from(0_usize), ConstantIndex::from(2_usize)]);
    let (_, read, _) = read_literal(&one, ConstantIndex::from(4_usize), integer_literal());
    assert!(
        matches!(read.judged()[5].verdict(), Verdict::Checked { .. }),
        "one boolean reader carries the literal: {:?}",
        read.judged()[5].verdict()
    );
}

/// The natural-literal readers at the positions `at`.
///
/// # Specification
/// trivial.
fn naturals(at: &[ConstantIndex]) -> Vec<gandr_core_term::LiteralReader>
{
    at.iter()
        .map(|&by| gandr_core_term::LiteralReader {
            by,
            reads: gandr_core_term::LiteralKind::Natural,
        })
        .collect()
}

/// #4732: a negative literal checked at a type apart from `Integer` crosses by
/// the one kept negative reader whose result is that type, applied to the
/// literal's magnitude; a natural reader of the type does not carry it.
#[test]
fn a_negative_literal_crosses_by_from_neg_at_its_magnitude_4732()
{
    let negative = gandr_kernel_term::Literal::Integer(gandr_kernel_term::IntegerLiteral::new(
        gandr_kernel_term::Sign::Negative,
        gandr_kernel_term::Magnitude::from_decimal_text(alloc::string::String::from("4"))
            .expect("decimal digits"),
    ));
    let readers = [
        gandr_core_term::LiteralReader {
            by: ConstantIndex::from(0_usize),
            reads: gandr_core_term::LiteralKind::Negative,
        },
        gandr_core_term::LiteralReader {
            by: ConstantIndex::from(1_usize),
            reads: gandr_core_term::LiteralKind::Natural,
        },
    ];
    let (mut arena, report, literal) =
        read_literal(&readers, ConstantIndex::from(3_usize), negative.clone());
    assert!(
        matches!(report.judged()[5].verdict(), Verdict::Checked { .. }),
        "the negative literal checks where text is asked: {:?}",
        report.judged()[5].verdict()
    );
    let crossings = report.nested_elaborations()[&ConstantIndex::from(5_usize)].crossings();
    let [(&at, crossing)] = crossings.iter().collect::<Vec<_>>()[..]
    else {
        panic!("one crossing is recorded: {crossings:?}");
    };
    assert_eq!(
        (at, crossing.by),
        (literal, Maybe::Present(ConstantIndex::from(0_usize))),
        "the crossing is recorded at the literal, by the negative reader"
    );
    let gandr_core_term::CrossedOperand::Standing(standing) = crossing.operand
    else {
        panic!("the reader takes a value standing for the literal: {crossing:?}");
    };
    assert!(
        matches!(
            arena.value(standing),
            Some(&gandr_core_term::Value::Literal(gandr_kernel_term::Literal::Integer(ref magnitude)))
                if magnitude.sign() == gandr_kernel_term::Sign::NonNegative
                    && magnitude.magnitude().as_ref() == "4"
        ),
        "the reader is applied to the magnitude: {:?}",
        arena.value(standing)
    );
    let readmission = crate::bridge::readmit(&mut arena, &report);
    assert!(
        readmission.readmitted().iter().all(|readmitted| matches!(
            readmitted.outcome(),
            crate::bridge::Outcome::Defined { .. } | crate::bridge::Outcome::Assumed { .. }
        )),
        "the kernel re-derives the reader's application: {readmission:?}"
    );
    let (_, natural, _) = read_literal(
        &naturals(&[ConstantIndex::from(0_usize)]),
        ConstantIndex::from(3_usize),
        negative,
    );
    assert!(
        matches!(
            natural.judged()[5].verdict(),
            Verdict::Refused(CheckRefusal::TypeMismatch(_))
        ),
        "a natural reader does not carry a negative literal: {:?}",
        natural.judged()[5].verdict()
    );
}

/// The decimal literal `1.25`.
///
/// # Specification
/// trivial.
fn decimal_literal() -> gandr_kernel_term::Literal
{
    gandr_kernel_term::Literal::Numeric(gandr_kernel_term::NumericLiteral::new(
        gandr_kernel_term::Sign::NonNegative,
        gandr_kernel_term::Magnitude::from_decimal_text(alloc::string::String::from("1"))
            .expect("decimal digits"),
        gandr_kernel_term::FractionDigits::from_decimal_text(alloc::string::String::from("25"))
            .expect("decimal digits"),
    ))
}

/// Assert that the kernel re-derives or assumes every declaration of
/// `report`, a decimal's crossing among them.
///
/// # Specification
/// trivial.
fn assert_readmitted(
    arena: &mut CoreArena,
    report: &super::ModuleReport,
)
{
    let readmission = crate::bridge::readmit(arena, report);
    assert!(
        readmission.readmitted().iter().all(|readmitted| matches!(
            readmitted.outcome(),
            crate::bridge::Outcome::Defined { .. } | crate::bridge::Outcome::Assumed { .. }
        )),
        "the kernel re-derives every declaration, the decimal's crossing among them: \
         {readmission:?}"
    );
}

/// #4807: a decimal checked at `f64` crosses by no map and stands as the
/// float it rounds to, so the kernel re-derives a float where the source
/// wrote a decimal; a decimal synthesised with no type stated is refused.
#[test]
fn a_decimal_at_f64_stands_as_its_float_4807()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let float = arena.value_type_base(BaseType::Float64);
    let taker_type = {
        let returns = arena.comp_type_returner(integer);
        let arrow = arena.comp_type_arrow(float, returns);
        arena.value_type_thunk(arrow)
    };
    let user_type = {
        let returns = arena.comp_type_returner(integer);
        arena.value_type_thunk(returns)
    };
    let literal = arena.value_literal(decimal_literal());
    let user = {
        let called = call(&mut arena, ConstantIndex::from(0_usize), literal);
        arena.value_thunk(called)
    };
    let report = {
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        check_module(&mut context, &[
            declaration(At(0), Maybe::Present(taker_type), HOLE),
            declaration(At(1), Maybe::Present(user_type), Maybe::Present(user)),
        ])
    };
    assert!(
        matches!(report.judged()[1].verdict(), Verdict::Checked { .. }),
        "the decimal checks where a float is asked: {:?}",
        report.judged()[1].verdict()
    );
    let crossings = report.nested_elaborations()[&ConstantIndex::from(1_usize)].crossings();
    let [(&at, crossing)] = crossings.iter().collect::<Vec<_>>()[..]
    else {
        panic!("one crossing is recorded: {crossings:?}");
    };
    let gandr_core_term::CrossedOperand::Standing(standing) = crossing.operand
    else {
        panic!("the decimal stands as a value of its own: {crossing:?}");
    };
    assert_eq!(
        (at, crossing.by, arena.value(standing)),
        (
            literal,
            Maybe::Absent(()),
            Some(&gandr_core_term::Value::Literal(
                gandr_kernel_term::Literal::Float64(gandr_kernel_term::Float64Literal::from(
                    1.25_f64
                ))
            ))
        ),
        "the decimal stands as its float, by no map"
    );
    assert_readmitted(&mut arena, &report);
    let unsigned = {
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        check_module(&mut context, &[declaration(
            At(0),
            UNSIGNED,
            Maybe::Present(literal),
        )])
    };
    assert!(
        matches!(
            unsigned.judged()[0].verdict(),
            Verdict::Refused(CheckRefusal::NotSynthesisable {
                form: crate::refusal::CheckingForm::Decimal(_),
            })
        ),
        "a decimal with no type stated is refused: {:?}",
        unsigned.judged()[0].verdict()
    );
}

/// #4807: a decimal checked at a type a kept decimal reader carries crosses
/// by it, applied to the decimal's digits and then its exponent; two readers
/// refuse it naming the type, and with none it is refused as a float.
#[test]
fn a_decimal_crosses_by_from_decimal_at_its_digits_and_exponent_4807()
{
    let judged = |kept: &[ConstantIndex]| {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let text = arena.value_type_base(BaseType::String);
        let reader_type = {
            let returns = arena.comp_type_returner(text);
            let inner = arena.comp_type_arrow(integer, returns);
            let outer = arena.comp_type_arrow(integer, inner);
            arena.value_type_thunk(outer)
        };
        let reader = {
            let read = arena.value_literal(text_literal());
            let returned = arena.computation_return(read);
            let inner = arena.computation_lambda(returned);
            let outer = arena.computation_lambda(inner);
            arena.value_thunk(outer)
        };
        let taker_type = {
            let returns = arena.comp_type_returner(integer);
            let arrow = arena.comp_type_arrow(text, returns);
            arena.value_type_thunk(arrow)
        };
        let user_type = {
            let returns = arena.comp_type_returner(integer);
            arena.value_type_thunk(returns)
        };
        let literal = arena.value_literal(decimal_literal());
        let user = {
            let called = call(&mut arena, ConstantIndex::from(2_usize), literal);
            arena.value_thunk(called)
        };
        let report = {
            let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
            let readers: Vec<gandr_core_term::LiteralReader> = kept
                .iter()
                .map(|&by| gandr_core_term::LiteralReader {
                    by,
                    reads: gandr_core_term::LiteralKind::Decimal,
                })
                .collect();
            context.keep_readers(&readers);
            check_module(&mut context, &[
                declaration(At(0), Maybe::Present(reader_type), Maybe::Present(reader)),
                declaration(At(1), Maybe::Present(reader_type), Maybe::Present(reader)),
                declaration(At(2), Maybe::Present(taker_type), HOLE),
                declaration(At(3), Maybe::Present(user_type), Maybe::Present(user)),
            ])
        };
        (arena, report, literal)
    };
    let (mut arena, report, literal) = judged(&[ConstantIndex::from(0_usize)]);
    assert!(
        matches!(report.judged()[3].verdict(), Verdict::Checked { .. }),
        "the decimal checks where text is asked: {:?}",
        report.judged()[3].verdict()
    );
    let crossings = report.nested_elaborations()[&ConstantIndex::from(3_usize)].crossings();
    let [(&at, crossing)] = crossings.iter().collect::<Vec<_>>()[..]
    else {
        panic!("one crossing is recorded: {crossings:?}");
    };
    let (&[digits], gandr_core_term::CrossedOperand::Standing(exponent)) =
        (crossing.carriers.as_slice(), crossing.operand)
    else {
        panic!("the reader takes the digits, then the exponent: {crossing:?}");
    };
    let integer_of = |value| match arena.value(value) {
        Some(&gandr_core_term::Value::Literal(gandr_kernel_term::Literal::Integer(
            ref integer,
        ))) => Some((
            integer.sign(),
            alloc::string::String::from(integer.magnitude().as_ref()),
        )),
        _ => None,
    };
    assert_eq!(
        (at, crossing.by, integer_of(digits), integer_of(exponent)),
        (
            literal,
            Maybe::Present(ConstantIndex::from(0_usize)),
            Some((
                gandr_kernel_term::Sign::NonNegative,
                alloc::string::String::from("125")
            )),
            Some((
                gandr_kernel_term::Sign::Negative,
                alloc::string::String::from("2")
            )),
        ),
        "1.25 crosses by the reader at 125 and -2"
    );
    assert_readmitted(&mut arena, &report);
    let (_, both, _) = judged(&[ConstantIndex::from(0_usize), ConstantIndex::from(1_usize)]);
    assert!(
        matches!(
            both.judged()[3].verdict(),
            Verdict::Refused(CheckRefusal::LiteralAmbiguous { .. })
        ),
        "two readers of the type refuse the decimal: {:?}",
        both.judged()[3].verdict()
    );
    let (_, none, _) = judged(&[]);
    assert!(
        matches!(
            none.judged()[3].verdict(),
            Verdict::Refused(CheckRefusal::TypeMismatch(_))
        ),
        "with no reader the decimal is refused: {:?}",
        none.judged()[3].verdict()
    );
}

/// #4528: only a literal is read: an integer variable where text is asked is
/// refused whatever readers are kept.
#[test]
fn an_integer_variable_crosses_by_no_reader_4528()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let text = arena.value_type_base(BaseType::String);
    let thunk_of = |arena: &mut CoreArena, domain, result| {
        let returns = arena.comp_type_returner(result);
        let arrow = arena.comp_type_arrow(domain, returns);
        arena.value_type_thunk(arrow)
    };
    let word_type = thunk_of(&mut arena, integer, text);
    let taker_type = thunk_of(&mut arena, text, integer);
    let user_type = thunk_of(&mut arena, integer, integer);
    let user = {
        let bound = arena.value_variable(
            gandr_core_term::Zone::Intuitionistic,
            DeBruijnIndex::from(0_u32),
        );
        let called = call(&mut arena, ConstantIndex::from(1_usize), bound);
        let lambda = arena.computation_lambda(called);
        arena.value_thunk(lambda)
    };
    let report = {
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        context.keep_readers(&naturals(&[ConstantIndex::from(0_usize)]));
        check_module(&mut context, &[
            declaration(At(0), Maybe::Present(word_type), HOLE),
            declaration(At(1), Maybe::Present(taker_type), HOLE),
            declaration(At(2), Maybe::Present(user_type), Maybe::Present(user)),
        ])
    };
    assert!(
        matches!(
            report.judged()[2].verdict(),
            Verdict::Refused(CheckRefusal::TypeMismatch(_))
        ),
        "a variable is no literal, so no reader carries it: {:?}",
        report.judged()[2].verdict()
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
        (site, Maybe::Present(ConstantIndex::from(0_usize))),
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
    // `Σ (y : Integer). Path[.A = Integer](y, y)`.
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

/// A reflexivity over `carrier`, `U ((y : carrier) -> F Path[.A = carrier](y,
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

/// #2327: a call returning a function, read where that function's thunk is
/// read, runs before the call it is passed to; a call returning an integer,
/// read where a thunk of its returner is read, stays suspended.
#[test]
fn a_call_returning_a_function_runs_where_one_is_read_2327()
{
    let mut arena = CoreArena::new();
    let (function, identity) = integer_function(&mut arena);
    let integer = arena.value_type_base(BaseType::Integer);
    let returns = arena.comp_type_returner(integer);
    // `maker : U (Integer -> F (U (Integer -> F Integer)))`, `λn. return identity`.
    let makes = arena.comp_type_returner(function);
    let maker_arrow = arena.comp_type_arrow(integer, makes);
    let maker_type = arena.value_type_thunk(maker_arrow);
    let maker = {
        let held = arena.value_constant(ConstantIndex::from(0_usize));
        let returned = arena.computation_return(held);
        let lambda = arena.computation_lambda(returned);
        arena.value_thunk(lambda)
    };
    // `at_zero : U (U (Integer -> F Integer) -> F Integer)`, `λg. force g 0`.
    let at_zero_arrow = arena.comp_type_arrow(function, returns);
    let at_zero_type = arena.value_type_thunk(at_zero_arrow);
    let at_zero = {
        let applied = arena.value_variable(
            gandr_core_term::Zone::Intuitionistic,
            DeBruijnIndex::from(0_u32),
        );
        let forced = arena.computation_force(applied);
        let zero = arena.value_literal(integer_literal());
        let application = arena.computation_application(forced, zero);
        let lambda = arena.computation_lambda(application);
        arena.value_thunk(lambda)
    };
    let suspended_type = arena.value_type_thunk(returns);
    // `passed : U (F Integer)`, `thunk (at_zero (maker 0))`, `maker 0` nested.
    let made_at = arena.value_literal(integer_literal());
    let made = call(&mut arena, ConstantIndex::from(1_usize), made_at);
    let ran = arena.value_nested(made);
    let passed_call = call(&mut arena, ConstantIndex::from(2_usize), ran);
    let passed = arena.value_thunk(passed_call);
    // `held : U (F Integer)`, `identity 0` nested.
    let held_at = arena.value_literal(integer_literal());
    let held_call = call(&mut arena, ConstantIndex::from(0_usize), held_at);
    let held = arena.value_nested(held_call);
    let report = {
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        check_module(&mut context, &[
            declaration(At(0), Maybe::Present(function), Maybe::Present(identity)),
            declaration(At(1), Maybe::Present(maker_type), Maybe::Present(maker)),
            declaration(At(2), Maybe::Present(at_zero_type), Maybe::Present(at_zero)),
            declaration(
                At(3),
                Maybe::Present(suspended_type),
                Maybe::Present(passed),
            ),
            declaration(At(4), Maybe::Present(suspended_type), Maybe::Present(held)),
        ])
    };
    assert!(
        matches!(report.judged()[3].verdict(), Verdict::Checked { .. }),
        "the call returning a function checks where the function is read: {:?}",
        report.judged()[3].verdict()
    );
    let passing = &report.nested_elaborations()[&ConstantIndex::from(3_usize)];
    assert_eq!(
        passing.decisions().get(&ran),
        Some(&Nesting::Ran(Purity::Pure)),
        "it runs, purely"
    );
    assert_eq!(
        passing
            .binds()
            .iter()
            .map(|&(run, _)| run)
            .collect::<Vec<_>>(),
        [ran],
        "and binds what it returns before the call it is passed to"
    );
    assert!(
        matches!(report.judged()[4].verdict(), Verdict::Checked { .. }),
        "the call returning an integer checks at a thunk of its returner: {:?}",
        report.judged()[4].verdict()
    );
    assert_eq!(
        report.nested_elaborations()[&ConstantIndex::from(4_usize)]
            .decisions()
            .get(&held),
        Some(&Nesting::Suspended),
        "it is suspended, as a thunk of its returner reads it"
    );
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
fn a_run_in_a_definition_s_own_value_is_unenclosed_only_when_effectful_4812()
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
    let asking = {
        let asked = arena.value_variable(
            gandr_core_term::Zone::Intuitionistic,
            DeBruijnIndex::from(0_u32),
        );
        let performed = arena.computation_perform(interface, OperationName::from("ask"), asked);
        let lambda = arena.computation_lambda(performed);
        arena.value_thunk(lambda)
    };
    let [pure, effectful] = [0_usize, 1].map(|callee| {
        let zero = arena.value_literal(integer_literal());
        let computation = call(&mut arena, ConstantIndex::from(callee), zero);
        arena.value_nested(computation)
    });
    let report = {
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        check_module(&mut context, &[
            declaration(At(0), Maybe::Present(function), Maybe::Present(identity)),
            declaration(At(1), Maybe::Present(asking_type), Maybe::Present(asking)),
            declaration(At(2), Maybe::Present(integer), Maybe::Present(pure)),
            declaration(At(3), Maybe::Present(integer), Maybe::Present(effectful)),
        ])
    };
    assert!(
        matches!(report.judged()[2].verdict(), Verdict::Checked { .. }),
        "a pure call needs no computation around it: {:?}",
        report.judged()[2].verdict()
    );
    assert!(
        matches!(
            report
                .definitions()
                .get(&ConstantIndex::from(2_usize))
                .and_then(|&body| arena.value(body)),
            Some(&gandr_core_term::Value::Returned(_))
        ),
        "the definition is the value the call returns, which a read of it runs"
    );
    let refusal = CheckRefusal::UnenclosedRun { at: effectful };
    assert_eq!(
        report.judged()[3].verdict(),
        Verdict::Refused(refusal),
        "the call checks at the integer, but no computation encloses its effect to run before"
    );
    assert_eq!(refusal.classify(), FailureClass::MalformedSource);
    let failure = &report.failures()[&ConstantIndex::from(3_usize)];
    assert!(
        failure.obligations().is_empty(),
        "no rule of the judgement is pending"
    );
    assert_eq!(
        failure.pursuit().at(),
        CoreNode::Term(TermNode::Value(effectful))
    );
    assert!(
        !report
            .definitions()
            .contains_key(&ConstantIndex::from(3_usize)),
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
fn a_kept_support_is_the_support_of_the_judgement_alone_6573()
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
    // thunk ((force f) s) x: the judgement stops at s, and the typed run
    // recovers and reads x after it.
    let forced = arena.computation_force(f);
    let once = arena.computation_application(forced, s);
    let twice = arena.computation_application(once, x);
    let suspended = arena.value_thunk(twice);
    let module = [
        declaration(At(0), UNSIGNED, Maybe::Present(text)),
        declaration(At(1), Maybe::Present(function_type), HOLE),
        declaration(At(2), Maybe::Present(integer), Maybe::Present(zero)),
        declaration(
            At(3),
            Maybe::Present(suspended_type),
            Maybe::Present(suspended),
        ),
    ];
    let mut alone = arena.clone();
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let mut run = ModuleRun::new();
    run.keep_typings();
    run.keep_supports();
    run.judge(&mut context, &module, |_, _, _| {});
    let typed = run.take_typings().expect("the run keeps its typings");
    let report = run.finish(&mut context);
    assert!(
        typed
            .typings()
            .get(&ConstantIndex::from(3_usize))
            .is_some_and(|kept| kept
                .typings()
                .iter()
                .any(|typing| typing.term == TermNode::Value(x))),
        "the typed run reads x after the refusal"
    );
    let mut single = CheckingContext::new(&mut alone, CheckBudget::DEFAULT);
    let each: alloc::collections::BTreeMap<ConstantIndex, super::Supported> = module
        .iter()
        .map(|offered| {
            (
                offered.constant(),
                super::check_declaration_supported(&mut single, offered),
            )
        })
        .collect();
    // The memo's count of each decision is the instrument's, not the verdict's.
    let read = |supported: &alloc::collections::BTreeMap<ConstantIndex, super::Supported>| {
        supported
            .iter()
            .map(|(&constant, kept)| (constant, kept.verdict(), kept.support().clone()))
            .collect::<Vec<_>>()
    };
    assert_eq!(
        read(report.supported()),
        read(&each),
        "each kept verdict and support is the one the judgement alone gives, with no read of the typed run"
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

/// A sealed atom no signature marks `mobile` is met wherever a type holds it:
/// alone, in a pair, in a list, in a function's answer, and an atom the run
/// formed no abstract type at; a marked atom and a type naming no atom hold
/// none (#3375).
#[test]
fn an_unmarked_atom_is_met_wherever_a_type_holds_it_3375()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let small = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let [unmarked, mobile, foreign] = [0_usize, 1, 7].map(ConstantIndex::from);
    let secret = arena.value_type_abstract(unmarked);
    let report = arena.value_type_abstract(mobile);
    let stranger = arena.value_type_abstract(foreign);
    let paired = arena.value_type_product(&[integer, secret]);
    let listed = arena.value_type_list(secret);
    let returned = arena.comp_type_returner(secret);
    let function = arena.comp_type_arrow(integer, returned);
    let answered = arena.value_type_thunk(function);
    let reported = arena.value_type_product(&[report, integer]);
    let module = [
        sealed(At(0), small, integer, 0_usize.into(), 0_usize.into()),
        Declaration::abstract_type(
            mobile,
            AbstractType::new(
                small,
                integer,
                0_usize.into(),
                SealSite::new(SealingSite::from(0_usize), ComponentOrdinal::from(1_usize)),
            )
            .marked(crate::worlds::Mobility::Mobile),
            OriginToken::from(101_usize),
        ),
    ];
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let checked = check_module(&mut context, &module);
    for (ty, held, what) in [
        (secret, Maybe::Present(unmarked), "the atom alone"),
        (paired, Maybe::Present(unmarked), "the atom in a pair"),
        (listed, Maybe::Present(unmarked), "the atom in a list"),
        (
            answered,
            Maybe::Present(unmarked),
            "the atom a function answers",
        ),
        (
            stranger,
            Maybe::Present(foreign),
            "an atom no abstract type formed at",
        ),
        (
            reported,
            Maybe::Absent(super::unmarked::Absent::Unheld),
            "a marked atom",
        ),
        (
            integer,
            Maybe::Absent(super::unmarked::Absent::Unheld),
            "a type naming no atom",
        ),
    ] {
        assert_eq!(checked.unmarked_atom(&arena, ty), held, "{what}");
    }
}

/// An unmarked atom stands beside a pair thirty levels deep, whose two fields
/// at each level are one node. The walk reads the pair before the atom, so a
/// walk that reads each path to a node reads 2^30 leaves first. The walk reads
/// each node once and meets the atom (#5796).
#[test]
fn an_unmarked_atom_beside_a_shared_pair_thirty_deep_is_met_5796()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let small = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let unmarked = ConstantIndex::from(0_usize);
    let secret = arena.value_type_abstract(unmarked);
    let shared = (0_u8 .. 30).fold(integer, |level, _| {
        arena.value_type_product(&[level, level])
    });
    let beside = arena.value_type_product(&[secret, shared]);
    let module = [sealed(
        At(0),
        small,
        integer,
        0_usize.into(),
        0_usize.into(),
    )];
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let checked = check_module(&mut context, &module);
    assert_eq!(
        checked.unmarked_atom(&arena, beside),
        Maybe::Present(unmarked),
        "the atom beside the shared pair is met after one read of each level"
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
    // walk reads `?second` inside the first solution two binders deep, raised
    // past one: `#1`. A type recorded two binders deep reads the same.
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

/// A declaration owing a law whose sides its clauses identify checks; one
/// owing a second law whose sides return different metavariables is refused
/// at the scope, naming that law: a metavariable is held rigid, never solved
/// to make the sides agree.
#[test]
fn a_scope_is_checked_as_a_model_of_its_theory_2272()
{
    use gandr_core_term::handler::HandlerLaw;
    use gandr_kernel_term::RuleIndex;

    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let zero = arena.value_literal(integer_literal());
    let returned = |arena: &mut CoreArena, index: u32| {
        let value = arena.value_variable(
            gandr_core_term::Zone::Intuitionistic,
            DeBruijnIndex::from(index),
        );
        arena.computation_return(value)
    };
    let scope = returned(&mut arena, 0);
    let same = HandlerLaw {
        scope,
        rule: RuleIndex::from(0_usize),
        left: returned(&mut arena, 0),
        right: returned(&mut arena, 0),
    };
    let apart = HandlerLaw {
        scope,
        rule: RuleIndex::from(1_usize),
        left: returned(&mut arena, 0),
        right: returned(&mut arena, 1),
    };
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let report = check_module(&mut context, &[
        declaration(At(0), Maybe::Present(integer), Maybe::Present(zero))
            .obliged(Vec::from([same])),
        declaration(At(1), Maybe::Present(integer), Maybe::Present(zero))
            .obliged(Vec::from([same, apart])),
    ]);
    assert!(
        matches!(report.judged()[0].verdict(), Verdict::Checked { .. }),
        "{:?}",
        report.judged()[0].verdict()
    );
    assert_eq!(
        report.judged()[1].verdict(),
        Verdict::Refused(CheckRefusal::HandlerUnlawful {
            at: scope,
            rule: RuleIndex::from(1_usize),
            left: apart.left,
            right: apart.right,
        })
    );
}

#[test]
fn a_nested_argument_binds_the_implicit_it_is_read_at()
{
    use gandr_core_term::Zone;
    use gandr_core_term::hole::HoleId;
    use gandr_core_term::hole::NominationIndex;

    // def forget : U ((a : Type) -> El a -> F unit) = thunk λ λ. return () ;
    // def k      : U (F unit) = thunk ((force forget) ?a) (nested (return 0)) ;
    // Only the computation written as the argument determines `a`: read at
    // the decode of a hole nothing has bound yet, it runs, and the integers
    // it returns bind `a`.
    let mut arena = CoreArena::new();
    let small = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let unit = arena.value_type_unit();
    let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let element = arena.value_type_element(bound, Level::zero());
    let returns_unit = arena.comp_type_returner(unit);
    let arrow = arena.comp_type_arrow(element, returns_unit);
    let polymorphic = arena.comp_type_pi(small, arrow);
    let forget_type = arena.value_type_thunk(polymorphic);
    let forget = {
        let nothing = arena.value_unit();
        let returned = arena.computation_return(nothing);
        let inner = arena.computation_lambda(returned);
        let outer = arena.computation_lambda(inner);
        arena.value_thunk(outer)
    };
    let suspended = arena.value_type_thunk(returns_unit);
    let zero = arena.value_literal(integer_literal());
    let produce = arena.computation_return(zero);
    let argument = arena.value_nested(produce);
    let hole = arena.value_hole(
        HoleId::nominated(NominationIndex::from(0_u32)).expect("the first nominated name"),
    );
    let constant = arena.value_constant(ConstantIndex::from(0_usize));
    let forced = arena.computation_force(constant);
    let head = arena.computation_application(forced, hole);
    let applied = arena.computation_application(head, argument);
    let call = arena.value_thunk(applied);
    let report = {
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        check_module(&mut context, &[
            declaration(At(0), Maybe::Present(forget_type), Maybe::Present(forget)),
            declaration(At(1), Maybe::Present(suspended), Maybe::Present(call)),
        ])
    };
    assert!(
        matches!(report.judged()[1].verdict(), Verdict::Checked { .. }),
        "the argument's integers bind the implicit: {:?}",
        report.judged()[1].verdict()
    );
    assert_eq!(
        report.nested_elaborations()[&ConstantIndex::from(1_usize)]
            .decisions()
            .get(&argument),
        Some(&Nesting::Ran(Purity::Pure)),
        "the argument runs, never suspended at the hole's decode"
    );
}

#[test]
fn a_decoded_hole_in_a_signature_is_solved_where_it_forms_5026()
{
    use gandr_core_term::hole::HoleId;
    use gandr_core_term::hole::NominationIndex;

    // def agreed : Path[.A = El ?a](0, 0) = here(0) ;
    // def mixed  : Path[.A = El ?b](0, ()) ;
    // def free   : El ?c ;
    // The carrier is the decode of a hole a call nominated, as `Path(x, y)`
    // lowers it: the first endpoint binds it, so the second meets it bound.
    let mut arena = CoreArena::new();
    let [first, second, third] = [0_u32, 1, 2].map(|index| {
        arena.value_hole(HoleId::nominated(NominationIndex::from(index)).expect("a nominated name"))
    });
    let carrier = |arena: &mut CoreArena, hole| arena.value_type_element(hole, Level::zero());
    let zero = arena.value_literal(integer_literal());
    let nothing = arena.value_unit();
    let agreed_carrier = carrier(&mut arena, first);
    let agreed = arena.value_type_path(agreed_carrier, zero, zero);
    let here = arena.value_here(zero);
    let mixed_carrier = carrier(&mut arena, second);
    let mixed = arena.value_type_path(mixed_carrier, zero, nothing);
    let free = carrier(&mut arena, third);
    let report = {
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        check_module(&mut context, &[
            declaration(At(0), Maybe::Present(agreed), Maybe::Present(here)),
            declaration(At(1), Maybe::Present(mixed), HOLE),
            declaration(At(2), Maybe::Present(free), HOLE),
        ])
    };
    let Verdict::Checked { declared, .. } = report.judged()[0].verdict()
    else {
        panic!(
            "the endpoints bind the carrier: {:?}",
            report.judged()[0].verdict()
        );
    };
    assert!(
        matches!(
            arena.value_type(declared.id()),
            Some(&gandr_core_term::ValueType::Path { carrier, .. })
                if arena.value_type(carrier) == Some(&gandr_core_term::ValueType::Base(BaseType::Integer))
        ),
        "the body is judged against the carrier the endpoints fix: {:?}",
        arena.value_type(declared.id())
    );
    assert!(
        matches!(
            report.judged()[1].verdict(),
            Verdict::Refused(CheckRefusal::TypeMismatch(_))
        ),
        "the unit end meets the integers the zero end bound: {:?}",
        report.judged()[1].verdict()
    );
    assert_eq!(
        report.judged()[2].verdict(),
        Verdict::Refused(CheckRefusal::ImplicitUnsolved {
            at: third,
            reason: crate::Unsolved::Unforced,
        }),
        "a signature no comparison fixes is refused where the hole stands"
    );
}

#[test]
fn a_hosted_law_is_admitted_only_where_the_host_asserts_it_2302()
{
    use gandr_core_term::primitive::PRELUDE;
    use gandr_core_term::primitive::PrimitiveType;

    let mut arena = CoreArena::new();
    let boolean = PrimitiveType::Boolean.mint(&mut arena);
    let unit = arena.value_unit();
    let truth = arena.value_injection(gandr_kernel_term::Summand::from(0_usize), unit);
    let named = |name: &str| {
        PRELUDE
            .iter()
            .copied()
            .find(|primitive| primitive.name().as_ref() == name)
            .expect("the prelude holds the row")
    };
    // A component deciding two values of `carrier`, defined as the primitive.
    let component = |arena: &mut CoreArena, name: &str, carrier: BaseType| {
        let carrier = arena.value_type_base(carrier);
        let answer = arena.comp_type_returner(boolean);
        let second = arena.comp_type_arrow(carrier, answer);
        let first = arena.comp_type_arrow(carrier, second);
        let declared = arena.value_type_thunk(first);
        (declared, named(name).thunk(arena), carrier)
    };
    // `component(x, y)` at de Bruijn indices `x` and `y`.
    let applied = |arena: &mut CoreArena, at: usize, left: u32, right: u32| {
        let head = arena.value_constant(ConstantIndex::from(at));
        let forced = arena.computation_force(head);
        let left = arena.value_variable(
            gandr_core_term::Zone::Intuitionistic,
            DeBruijnIndex::from(left),
        );
        let right = arena.value_variable(
            gandr_core_term::Zone::Intuitionistic,
            DeBruijnIndex::from(right),
        );
        let once = arena.computation_application(forced, left);
        let twice = arena.computation_application(once, right);
        arena.value_returned(twice)
    };
    let quantified =
        |arena: &mut CoreArena, path: ValueTypeId, carrier: ValueTypeId, over: usize| {
            let mut chain = arena.comp_type_returner(path);
            for _ in 0 .. over {
                chain = arena.comp_type_pi(carrier, chain);
            }
            arena.value_type_thunk(chain)
        };
    let refl = |arena: &mut CoreArena, at: usize, carrier: ValueTypeId| {
        let decided = applied(arena, at, 0, 0);
        let path = arena.value_type_path(boolean, decided, truth);
        quantified(arena, path, carrier, 1)
    };
    let sym = |arena: &mut CoreArena, at: usize, carrier: ValueTypeId| {
        let forward = applied(arena, at, 1, 0);
        let backward = applied(arena, at, 0, 1);
        let path = arena.value_type_path(boolean, forward, backward);
        quantified(arena, path, carrier, 2)
    };
    let (integers, integers_body, integer) = component(&mut arena, "int.eq", BaseType::Integer);
    let (floats, floats_body, float) = component(&mut arena, "float64.eq", BaseType::Float64);
    let (below, below_body, _) = component(&mut arena, "int.lt", BaseType::Integer);
    let integer_refl = refl(&mut arena, 0, integer);
    let float_refl = refl(&mut arena, 1, float);
    let float_sym = sym(&mut arena, 1, float);
    let below_refl = refl(&mut arena, 2, integer);
    let hosted = Maybe::Absent(body::Absent::Hosted);
    let report = {
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        check_module(&mut context, &[
            declaration(
                At(0),
                Maybe::Present(integers),
                Maybe::Present(integers_body),
            ),
            declaration(At(1), Maybe::Present(floats), Maybe::Present(floats_body)),
            declaration(At(2), Maybe::Present(below), Maybe::Present(below_body)),
            declaration(At(3), Maybe::Present(integer_refl), hosted),
            declaration(At(4), Maybe::Present(float_refl), hosted),
            declaration(At(5), Maybe::Present(float_sym), hosted),
            declaration(At(6), Maybe::Present(below_refl), hosted),
            declaration(At(7), Maybe::Present(float_refl), HOLE),
        ])
    };
    let verdicts: Vec<_> = report.judged().iter().map(super::Judged::verdict).collect();
    for (at, owed, what) in [
        (3, true, "the integers' equality is reflexive"),
        (4, false, "a NaN is not equal to itself"),
        (5, true, "the floats' equality is symmetric"),
        (6, false, "the host asserts no law of an ordering"),
        (7, true, "a hole owes its type whatever it states"),
    ] {
        let verdict = verdicts.get(at).copied();
        assert_eq!(
            matches!(verdict, Some(Verdict::Owed(_))),
            owed,
            "{what}: {verdict:?}"
        );
    }
    for (at, declared) in [(4, float_refl), (6, below_refl)] {
        assert_eq!(
            verdicts.get(at).copied(),
            Some(Verdict::Refused(CheckRefusal::UnassertedLaw {
                at: declared
            })),
            "an unasserted law is refused at its statement"
        );
    }
}

/// #5033: a refusal after a call whose argument bound the call's implicit
/// names the solution, never the hole. `same` at `unit` returns `Unit`, and
/// the body is checked at `F Integer`.
#[test]
fn a_refusal_names_the_implicit_its_call_solved_5033()
{
    use gandr_core_term::Zone;
    use gandr_core_term::hole::HoleId;
    use gandr_core_term::hole::NominationIndex;

    // def same : U ((a : Type) -> El a -> F (El a)) = thunk λ λ. return x ;
    // def wrongly : U (F Integer) = thunk ((force same) ?a) unit ;
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let small = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let element = arena.value_type_element(bound, Level::zero());
    let returns_element = arena.comp_type_returner(element);
    let arrow = arena.comp_type_arrow(element, returns_element);
    let polymorphic = arena.comp_type_pi(small, arrow);
    let same_type = arena.value_type_thunk(polymorphic);
    let returned = arena.computation_return(bound);
    let inner = arena.computation_lambda(returned);
    let outer = arena.computation_lambda(inner);
    let same = arena.value_thunk(outer);
    let returns_integer = arena.comp_type_returner(integer);
    let suspended = arena.value_type_thunk(returns_integer);
    let unit = arena.value_unit();
    let hole = arena.value_hole(
        HoleId::nominated(NominationIndex::from(0_u32)).expect("the first nominated name"),
    );
    let constant = arena.value_constant(ConstantIndex::from(0_usize));
    let forced = arena.computation_force(constant);
    let head = arena.computation_application(forced, hole);
    let applied = arena.computation_application(head, unit);
    let call = arena.value_thunk(applied);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let report = check_module(&mut context, &[
        declaration(At(0), Maybe::Present(same_type), Maybe::Present(same)),
        declaration(At(1), Maybe::Present(suspended), Maybe::Present(call)),
    ]);
    let failure = &report.failures()[&ConstantIndex::from(1_usize)];
    let Maybe::Present(crate::refusal::TypeNode::Computation(found)) =
        failure.refusal().compared().found
    else {
        panic!(
            "the mismatch names the computation type it found: {:?}",
            failure.refusal()
        );
    };
    let crate::refusal::TypeNode::Computation(solved) =
        failure.solved(crate::refusal::TypeNode::Computation(found))
    else {
        panic!("the found type reads as a computation type: {failure:?}");
    };
    let arena = context.arena();
    let returned = |at| match arena.comp_type(at) {
        Some(&gandr_core_term::CompType::Returner { result, .. }) => arena.value_type(result),
        _ => None,
    };
    assert!(
        matches!(
            returned(found),
            Some(gandr_core_term::ValueType::Element { .. })
        ),
        "as written, the call returns the decode of the hole: {:?}",
        returned(found)
    );
    assert!(
        matches!(returned(solved), Some(gandr_core_term::ValueType::Product(fields)) if fields.is_empty()),
        "as solved, it returns the unit the argument bound: {:?}",
        returned(solved)
    );
}
