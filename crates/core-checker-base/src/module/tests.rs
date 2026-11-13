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
use crate::failure::FrameRole;
use crate::failure::Pursuit;
use crate::failure::Stage;
use crate::failure::judged;
use crate::fixture::RetireAt;
use crate::fixture::integer_literal;
use crate::fixture::module::At;
use crate::fixture::module::HOLE;
use crate::fixture::module::UNSIGNED;
use crate::fixture::module::answers;
use crate::fixture::module::call;
use crate::fixture::module::declaration;
use crate::fixture::module::integer_function;
use crate::fixture::module::naturals;
use crate::fixture::module::read_literal;
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

/// The caller that takes each accepted declaration from the report of a whole
/// run, and enters it as an adoption enters it.
struct FromReport<'report>
{
    /// The report of the whole run.
    report: &'report super::ModuleReport,
    /// The positions taken, in order.
    taken: Vec<ConstantIndex>,
}

impl super::Taking for FromReport<'_>
{
    /// The whole run's decision of `declaration` when it accepted the body,
    /// entered at the declared type and the definition that the run kept.
    ///
    /// # Specification
    /// trivial.
    fn take(
        &mut self,
        context: &mut CheckingContext<'_>,
        declaration: &Declaration,
    ) -> Maybe<super::Taken, super::taken::Absent>
    {
        let constant = declaration.constant();
        let Some(verdict) = self
            .report
            .judged()
            .iter()
            .find(|judged| judged.constant() == constant)
            .map(super::Judged::verdict)
        else {
            return Maybe::Absent(super::taken::Absent::Unheld);
        };
        let (declared, body) = match verdict {
            Verdict::Checked { declared, body, .. } => (declared, body),
            Verdict::Synthesised { body, synthesised } => (synthesised.produced(), body),
            Verdict::Data | Verdict::Owed(_) | Verdict::Suspended(_) | Verdict::Refused(_) => {
                return Maybe::Absent(super::taken::Absent::Unheld);
            },
        };
        let defined = self
            .report
            .definitions()
            .get(&constant)
            .copied()
            .unwrap_or(body);
        if context
            .adopt_formed(constant, declared.id(), Maybe::Present(defined))
            .is_err()
        {
            return Maybe::Absent(super::taken::Absent::Unheld);
        }
        self.taken.push(constant);
        Maybe::Present(super::Taken::new(
            verdict,
            (
                Maybe::Absent(crate::support::kept::Absent::Accepted),
                Maybe::Absent(crate::support::elaborated::Absent::Unnested),
                Maybe::Absent(crate::support::waits::Absent::Unsuspended),
            ),
        ))
    }
}

/// #6620: a run that takes each accepted declaration of a module from the
/// report of a whole run decides only the owed and the refused ones. Its
/// report holds the verdicts, the definitions, the failures and the ledger of
/// the whole run. A taken declaration that a later one reads supplies its type
/// as the judged one does, so the later verdicts agree too.
#[test]
fn a_run_that_takes_each_accepted_declaration_reports_as_the_whole_run_6620()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let returns_integer = arena.comp_type_returner(integer);
    let thunk_type = arena.value_type_thunk(returns_integer);
    let zero = arena.value_literal(integer_literal());
    let text = arena.value_literal(text_literal());
    let returned = arena.computation_return(zero);
    let thunk = arena.value_thunk(returned);
    let suspended = arena.value_constant(ConstantIndex::from(0_usize));
    let owed = arena.value_constant(ConstantIndex::from(1_usize));
    let module = [
        declaration(At(0), Maybe::Present(thunk_type), Maybe::Present(thunk)),
        declaration(At(1), Maybe::Present(integer), HOLE),
        declaration(At(2), UNSIGNED, Maybe::Present(suspended)),
        declaration(At(3), Maybe::Present(integer), Maybe::Present(owed)),
        declaration(At(4), Maybe::Present(integer), Maybe::Present(text)),
    ];
    let mut taking_arena = arena.clone();
    let whole = {
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        check_module(&mut context, &module)
    };
    let mut from = FromReport {
        report: &whole,
        taken: Vec::new(),
    };
    let taking = {
        let mut context = CheckingContext::new(&mut taking_arena, CheckBudget::DEFAULT);
        let mut run = ModuleRun::new();
        let polled = run.judge_taking(
            &mut context,
            &module,
            |_, _, _| {},
            (&crate::retire::Unretired, &mut from),
        );
        assert!(
            matches!(polled, Polled::Whole(())),
            "nobody retires the run"
        );
        run.finish(&mut context)
    };
    assert_eq!(
        from.taken,
        [0_usize, 2, 3].map(ConstantIndex::from),
        "the run takes the three accepted declarations and decides the owed and the refused one"
    );
    assert_eq!(
        (
            taking.judged(),
            taking.definitions(),
            taking.failures(),
            taking.ledger()
        ),
        (
            whole.judged(),
            whole.definitions(),
            whole.failures(),
            whole.ledger()
        ),
        "the taking run reports the verdicts, the definitions, the failures and the ledger of the whole run"
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

/// A refusal that a judgement takes from a checkpoint replaces the verdict of
/// its declaration and the failure kept at it, and leaves every other entry.
#[test]
fn a_refusal_taken_from_a_checkpoint_replaces_the_verdict_and_the_failure()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let zero = arena.value_literal(integer_literal());
    let text = arena.value_literal(text_literal());
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let module = [
        declaration(At(0), Maybe::Present(integer), Maybe::Present(text)),
        declaration(At(1), Maybe::Present(integer), Maybe::Present(zero)),
    ];
    let mut report = check_module(&mut context, &module);
    let (refused, checked) = (ConstantIndex::from(0_usize), ConstantIndex::from(1_usize));
    let kept = report.failures()[&refused].clone();
    let refusal = kept.refusal();
    report.refuse(refused, refusal, None);
    assert_eq!(
        report.failures().get(&refused),
        None,
        "a refusal taken with no failure keeps none"
    );
    report.refuse(checked, refusal, Some(kept.clone()));
    let [ref first, ref second] = *report.judged()
    else {
        panic!("every declaration keeps its verdict");
    };
    assert_eq!(
        (first.verdict(), second.verdict()),
        (Verdict::Refused(refusal), Verdict::Refused(refusal)),
        "the taken refusal replaces the accepted verdict, and the refused one stays"
    );
    assert_eq!(
        report.failures().get(&checked),
        Some(&kept),
        "the taken failure is kept at its declaration"
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
            Maybe::Absent(crate::report::unmarked::Absent::Unheld),
            "a marked atom",
        ),
        (
            integer,
            Maybe::Absent(crate::report::unmarked::Absent::Unheld),
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
