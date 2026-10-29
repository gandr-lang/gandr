//! Nominal and record judgments, including independent kernel readmission.

use alloc::collections::BTreeMap;

use anodized::spec;
use gandr_core_checker::CheckBudget;
use gandr_core_checker::CheckRefusal;
use gandr_core_checker::CheckingContext;
use gandr_core_checker::CoreNode;
use gandr_core_checker::Declaration;
use gandr_core_checker::FrameRole;
use gandr_core_checker::Mismatch;
use gandr_core_checker::ModuleReport;
use gandr_core_checker::Obligation;
use gandr_core_checker::OriginToken;
use gandr_core_checker::Verdict;
use gandr_core_checker::bridge;
use gandr_core_checker::bridge::Outcome;
use gandr_core_checker::check_module;
use gandr_core_term::CoreArena;
use gandr_core_term::DataSignature;
use gandr_core_term::Sort;
use gandr_core_term::ValueId;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_kernel_strata::Level;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::ConstructorTag;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FieldLabel;
use gandr_kernel_term::GroundSort;
use quenchant_shape::shape::Maybe;

/// A definition at its source position.
///
/// # Specification
/// trivial.
fn definition(
    constant: ConstantIndex,
    declared: ValueTypeId,
    body: ValueId,
) -> Declaration
{
    Declaration::new(
        constant,
        Maybe::Present(declared),
        Maybe::Present(body),
        OriginToken::from(usize::from(constant)),
    )
}

/// Run the producer and its independent kernel boundary.
///
/// # Specification
/// - requires: declaration ids refer to `arena`.
/// - ensures: each source position has a producer verdict and a boundary
///   outcome.
/// - panics: only if a called judgment violates its contract.
///
/// # Adequacy
/// - hypothesis: L3 — the witnesses inspect exact positive and negative
///   outcomes, including native identities after admission renumbering.
/// - witness: `tests::native_formers::data_declarations_and_refusals_agree_with_kernel`
#[spec(ensures: |ret| ret.0.judged().len() == declarations.len() && ret.1.readmitted().len() == declarations.len())]
fn run(
    arena: &mut CoreArena,
    declarations: &[Declaration],
) -> (ModuleReport, bridge::Readmission)
{
    let report = check_module(
        &mut CheckingContext::new(arena, CheckBudget::DEFAULT),
        declarations,
    );
    let crossed = bridge::readmit(arena, &report);
    (report, crossed)
}

#[test]
fn data_declarations_and_refusals_agree_with_kernel()
{
    let mut arena = CoreArena::new();
    let unit_type = arena.value_type_unit();
    let unit = arena.value_unit();
    let kind = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let bad_kind = arena.value_type_universe(Sort::Ground(GroundSort::Computation), Level::zero());
    let bad = Declaration::data(
        ConstantIndex::from(0_usize),
        DataSignature::new(vec![], vec![], bad_kind).into(),
        OriginToken::from(0_usize),
    );
    let first = ConstantIndex::from(1_usize);
    let second = ConstantIndex::from(2_usize);
    let one = Declaration::data(
        first,
        DataSignature::new(vec![], vec![vec![unit_type]], kind).into(),
        OriginToken::from(1_usize),
    );
    let two = Declaration::data(
        second,
        DataSignature::new(vec![], vec![vec![unit_type]], kind).into(),
        OriginToken::from(2_usize),
    );
    let datatype = arena.value_type_data(first, vec![]);
    let other = arena.value_type_data(second, vec![]);
    let good = arena.value_constructor(datatype, ConstructorTag::from(0_usize), vec![unit]);
    let bad_tag = arena.value_constructor(datatype, ConstructorTag::from(1_usize), vec![unit]);
    let bad_fields = arena.value_constructor(datatype, ConstructorTag::from(0_usize), vec![]);
    let bad_arguments = arena.value_type_data(first, vec![unit]);
    let bad_application =
        arena.value_constructor(bad_arguments, ConstructorTag::from(0_usize), vec![unit]);
    let declarations = vec![
        bad,
        one,
        two,
        definition(ConstantIndex::from(3_usize), datatype, good),
        definition(ConstantIndex::from(4_usize), datatype, bad_tag),
        definition(ConstantIndex::from(5_usize), datatype, bad_fields),
        definition(ConstantIndex::from(6_usize), bad_arguments, bad_application),
        definition(ConstantIndex::from(7_usize), other, good),
    ];
    let (report, crossed) = run(&mut arena, &declarations);
    assert_eq!(
        report.judged()[0].verdict(),
        Verdict::Refused(CheckRefusal::DataKindNotUniverse(bad_kind))
    );
    assert_eq!(report.judged()[1].verdict(), Verdict::Data);
    assert_eq!(report.judged()[2].verdict(), Verdict::Data);
    assert!(matches!(
        report.judged()[3].verdict(),
        Verdict::Checked { .. }
    ));
    assert_eq!(
        report.judged()[4].verdict(),
        Verdict::Refused(CheckRefusal::UnknownConstructor {
            at: bad_tag,
            tag: ConstructorTag::from(1_usize)
        })
    );
    assert_eq!(
        report.judged()[5].verdict(),
        Verdict::Refused(CheckRefusal::ConstructorArity(bad_fields))
    );
    assert_eq!(
        report.judged()[6].verdict(),
        Verdict::Refused(CheckRefusal::DataArgumentArity(bad_arguments))
    );
    assert!(matches!(
        report.judged()[7].verdict(),
        Verdict::Refused(CheckRefusal::TypeMismatch(_))
    ));
    for position in [0_usize, 4, 5, 6, 7] {
        let Verdict::Refused(reason) = report.judged()[position].verdict()
        else {
            panic!("malformed declaration must be refused");
        };
        assert_eq!(
            reason.classify(),
            gandr_core_term::FailureClass::MalformedSource
        );
    }
    assert!(
        matches!(crossed.readmitted()[1].outcome(),Outcome::Data { admitted,.. } if admitted.position() == ConstantIndex::from(0_usize))
    );
    assert!(
        matches!(crossed.readmitted()[2].outcome(),Outcome::Data { admitted,.. } if admitted.position() == ConstantIndex::from(1_usize))
    );
    assert!(
        matches!(crossed.readmitted()[3].outcome(), Outcome::Defined { .. }),
        "{:?}",
        crossed.readmitted()[3].outcome()
    );
    assert!(crossed.audit().axioms().is_empty());
    let family = gandr_kernel_term::StructuredName::from(vec![
        gandr_kernel_term::NameSegment::from_text(String::from("Unit1")).unwrap(),
    ]);
    let artifact = gandr_kernel_term::decode(
        crossed
            .export(BTreeMap::from([(first, family.clone())]))
            .as_image(),
    )
    .unwrap();
    assert_eq!(
        artifact.declarations()[0].declaration().name(),
        &family,
        "a nominal declaration crosses under its own name"
    );
    let gandr_kernel_term::DeclarationContent::Def { body, .. } =
        *artifact.declarations()[2].declaration().content()
    else {
        panic!("a native constructor definition");
    };
    let Some(matched_native_node) = artifact.arena().value(body)
    else {
        panic!("native constructor, not a pair encoding");
    };
    let gandr_kernel_term::Value::Constructor { ref datatype, .. } = *matched_native_node
    else {
        panic!("native constructor, not a pair encoding");
    };
    assert!(
        matches!(artifact.arena().value_type(*datatype),Some(gandr_kernel_term::ValueType::Data { declaration,.. }) if *declaration == ConstantIndex::from(0_usize))
    );
}

/// The circle's word over `base` (tag 0), spelled by `letters` outermost
/// first: tag 1 a `Loop`, tag 2 an `Unloop`.
///
/// # Specification
/// trivial.
fn word(
    arena: &mut CoreArena,
    letters: &[ConstructorTag],
) -> ValueId
{
    let own = arena.value_type_data(ConstantIndex::from(0_usize), vec![]);
    let mut built = arena.value_constructor(own, ConstructorTag::from(0_usize), vec![]);
    for &letter in letters.iter().rev() {
        built = arena.value_constructor(own, letter, vec![built]);
    }
    built
}

/// The circle at position zero, presented by `rules`.
///
/// # Specification
/// trivial.
fn circle(
    arena: &mut CoreArena,
    rules: Vec<gandr_kernel_term::PresentedRule>,
) -> Declaration
{
    let kind = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let own = arena.value_type_data(ConstantIndex::from(0_usize), vec![]);
    Declaration::data(
        ConstantIndex::from(0_usize),
        DataSignature::new(vec![], vec![vec![], vec![own], vec![own]], kind)
            .presented(gandr_kernel_term::Presentation::new(rules))
            .into(),
        OriginToken::from(0_usize),
    )
}

/// The circle's cancellations `Loop(Unloop(x)) ~> x` and
/// `Unloop(Loop(x)) ~> x`.
///
/// # Specification
/// trivial.
fn cancellations() -> Vec<gandr_kernel_term::PresentedRule>
{
    use gandr_kernel_term::RuleNode;
    let c = |tag: usize| RuleNode::Constructor(ConstructorTag::from(tag));
    let x = RuleNode::Variable(gandr_kernel_term::RuleVariable::from(0_u32));
    vec![
        gandr_kernel_term::PresentedRule::new([c(1), c(2), x].into(), [x].into()),
        gandr_kernel_term::PresentedRule::new([c(2), c(1), x].into(), [x].into()),
    ]
}

#[test]
fn a_presented_word_meets_its_reduced_word_in_both_checkers()
{
    let looped = ConstructorTag::from(1_usize);
    let unlooped = ConstructorTag::from(2_usize);
    for (rules, admitted) in [(cancellations(), true), (vec![], false)] {
        let mut arena = CoreArena::new();
        let own = arena.value_type_data(ConstantIndex::from(0_usize), vec![]);
        let written = word(&mut arena, &[looped, unlooped, looped]);
        let reduced = word(&mut arena, &[looped]);
        let declared = arena.value_type_path(own, written, reduced);
        let point = word(&mut arena, &[looped]);
        let reflexivity = arena.value_here(point);
        let declarations = vec![
            circle(&mut arena, rules),
            definition(ConstantIndex::from(1_usize), declared, reflexivity),
        ];
        let (report, crossed) = run(&mut arena, &declarations);
        assert_eq!(report.judged()[0].verdict(), Verdict::Data);
        if admitted {
            assert!(
                matches!(report.judged()[1].verdict(), Verdict::Checked { .. }),
                "`here(Loop(Base))` meets `Loop(Unloop(Loop(Base)))` under the rules: {:?}",
                report.judged()[1].verdict()
            );
            assert!(
                matches!(crossed.readmitted()[1].outcome(), Outcome::Defined { .. }),
                "the kernel admits the reflexivity by the same normal forms: {:?}",
                crossed.readmitted()[1].outcome()
            );
        }
        else {
            assert!(
                matches!(
                    report.judged()[1].verdict(),
                    Verdict::Refused(CheckRefusal::EndpointMismatch { .. })
                ),
                "over a free circle the two words are two terms: {:?}",
                report.judged()[1].verdict()
            );
        }
    }
}

#[test]
fn a_misplaced_rule_is_refused_in_both_checkers()
{
    use gandr_kernel_term::RuleNode;
    let mut arena = CoreArena::new();
    let kind = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let integer = arena.value_type_base(gandr_kernel_term::BaseType::Integer);
    // `Mark(Empty) ~> Empty`, with `Mark`'s field an integer: no term of
    // the family stands there.
    let misplaced = gandr_kernel_term::PresentedRule::new(
        [
            RuleNode::Constructor(ConstructorTag::from(1_usize)),
            RuleNode::Constructor(ConstructorTag::from(0_usize)),
        ]
        .into(),
        [RuleNode::Constructor(ConstructorTag::from(0_usize))].into(),
    );
    let presentation = gandr_kernel_term::Presentation::new(vec![misplaced]);
    let tally = Declaration::data(
        ConstantIndex::from(0_usize),
        DataSignature::new(vec![], vec![vec![], vec![integer]], kind)
            .presented(presentation.clone())
            .into(),
        OriginToken::from(0_usize),
    );
    let refusal = gandr_kernel_term::RuleRefusal {
        rule: gandr_kernel_term::RuleIndex::from(0_usize),
        fault: gandr_kernel_term::RuleFault::NotOwnPosition,
    };
    let (report, _crossed) = run(&mut arena, &[tally]);
    assert_eq!(
        report.judged()[0].verdict(),
        Verdict::Refused(CheckRefusal::RuleNotPresentable { kind, refusal }),
        "the checker names the rule and its fault"
    );
    let mut environment = gandr_kernel_core::Environment::new();
    let mut staging = environment.stage();
    let kernel_kind = staging
        .arena()
        .value_type_universe(GroundSort::Value, Level::zero());
    let kernel_integer = staging
        .arena()
        .value_type_base(gandr_kernel_term::BaseType::Integer);
    let staged = staging
        .data(
            gandr_kernel_term::LevelSignature::monomorphic(),
            vec![],
            vec![vec![], vec![kernel_integer]],
            kernel_kind,
        )
        .presented(presentation);
    assert_eq!(
        environment.add_decl(staged).map(|_admitted| ()),
        Err(gandr_kernel_core::KernelError::RuleNotPresentable(refusal)),
        "the kernel refuses the same rule for the same fault"
    );
}

#[test]
fn a_rule_binding_a_dependent_field_is_refused_in_both_checkers()
{
    use gandr_kernel_term::RuleNode;
    use gandr_kernel_term::RuleVariable;
    // `P(a : Type) { Mk : (x : El a, y : El a); S : (p : P(a)) }` with
    // `S(Mk(x, y)) ~> Mk(x, y)`: `y`'s type reads `a` past `x`'s binder,
    // so a rule variable there has no classifier of its own.
    let rule = gandr_kernel_term::PresentedRule::new(
        [
            RuleNode::Constructor(ConstructorTag::from(1_usize)),
            RuleNode::Constructor(ConstructorTag::from(0_usize)),
            RuleNode::Variable(RuleVariable::from(0_u32)),
            RuleNode::Variable(RuleVariable::from(1_u32)),
        ]
        .into(),
        [
            RuleNode::Constructor(ConstructorTag::from(0_usize)),
            RuleNode::Variable(RuleVariable::from(0_u32)),
            RuleNode::Variable(RuleVariable::from(1_u32)),
        ]
        .into(),
    );
    let presentation = gandr_kernel_term::Presentation::new(vec![rule]);
    let refusal = gandr_kernel_term::RuleRefusal {
        rule: gandr_kernel_term::RuleIndex::from(0_usize),
        fault: gandr_kernel_term::RuleFault::DependentSlot,
    };
    let mut arena = CoreArena::new();
    let kind = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let near = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let far = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
    let first = arena.value_type_element(near, Level::zero());
    let second = arena.value_type_element(far, Level::zero());
    let own = arena.value_type_data(ConstantIndex::from(0_usize), vec![near]);
    let pairs = Declaration::data(
        ConstantIndex::from(0_usize),
        DataSignature::new(vec![kind], vec![vec![first, second], vec![own]], kind)
            .presented(presentation.clone())
            .into(),
        OriginToken::from(0_usize),
    );
    let (report, _crossed) = run(&mut arena, &[pairs]);
    assert_eq!(
        report.judged()[0].verdict(),
        Verdict::Refused(CheckRefusal::RuleNotPresentable { kind, refusal }),
        "the checker names the rule and its fault"
    );
    let mut environment = gandr_kernel_core::Environment::new();
    let mut staging = environment.stage();
    let arena = staging.arena();
    let kernel_kind = arena.value_type_universe(GroundSort::Value, Level::zero());
    let near = arena.value_variable(DeBruijnIndex::from(0_u32));
    let far = arena.value_variable(DeBruijnIndex::from(1_u32));
    let first = arena.value_type_element(near, Level::zero());
    let second = arena.value_type_element(far, Level::zero());
    let own = arena.value_type_data(ConstantIndex::from(0_usize), vec![near]);
    let staged = staging
        .data(
            gandr_kernel_term::LevelSignature::monomorphic(),
            vec![kernel_kind],
            vec![vec![first, second], vec![own]],
            kernel_kind,
        )
        .presented(presentation);
    assert_eq!(
        environment.add_decl(staged).map(|_admitted| ()),
        Err(gandr_kernel_core::KernelError::RuleNotPresentable(refusal)),
        "the kernel refuses the same rule for the same fault"
    );
}

/// `fix f. λy. case y { Base ⇒ return (); Loop(x) ⇒ f(x); Unloop(x) ⇒
/// f(x) }` at `Circle → F Unit`, its descent claimed, and the case at its
/// root.
///
/// # Specification
/// trivial.
fn unwinding(arena: &mut CoreArena) -> (ValueId, ValueTypeId, gandr_core_term::ComputationId)
{
    let own = arena.value_type_data(ConstantIndex::from(0_usize), vec![]);
    let unit_type = arena.value_type_unit();
    let unit = arena.value_unit();
    let motive = arena.comp_type_returner(unit_type);
    let returned = arena.computation_return(unit);
    // Under the self binder, the argument and the field: `f` is two out.
    let recursive = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(2_u32));
    let field = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let forced = arena.computation_force(recursive);
    let called = arena.computation_application(forced, field);
    let recursing = arena.computation_lambda(called);
    let argument = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let case = arena.computation_data_case(
        argument,
        motive,
        vec![returned, recursing, recursing],
        [0_usize, 1, 1]
            .map(gandr_kernel_term::FieldCount::from)
            .to_vec(),
    );
    let lambda = arena.computation_lambda(case);
    let fixpoint = arena.computation_fixpoint(
        lambda,
        gandr_kernel_term::FixpointEvidence::StructuralDescent,
    );
    let arrow = arena.comp_type_arrow(own, motive);
    (
        arena.value_thunk(fixpoint),
        arena.value_type_thunk(arrow),
        case,
    )
}

#[test]
fn a_case_respects_its_type_s_rules_or_is_refused_by_the_rule_357()
{
    let looped = ConstructorTag::from(1_usize);
    let unlooped = ConstructorTag::from(2_usize);
    for (rules, presented) in [(cancellations(), true), (vec![], false)] {
        let mut arena = CoreArena::new();
        // `Loop(Unloop(Base))`, which the rules identify with `Base`.
        let scrutinee = word(&mut arena, &[looped, unlooped]);
        let unit_type = arena.value_type_unit();
        let unit = arena.value_unit();
        let motive = arena.comp_type_returner(unit_type);
        let returned = arena.computation_return(unit);
        let lettered = arena.computation_lambda(returned);
        // A bare case: its arms return at once, so at `Loop(Unloop(x))`
        // it returns while at `x` it is stuck on the variable.
        let case = arena.computation_data_case(
            scrutinee,
            motive,
            vec![returned, lettered, lettered],
            [0_usize, 1, 1]
                .map(gandr_kernel_term::FieldCount::from)
                .to_vec(),
        );
        let body = arena.value_thunk(case);
        let declared = arena.value_type_thunk(motive);
        let (unwound, unwinding_type, _root) = unwinding(&mut arena);
        let declarations = vec![
            circle(&mut arena, rules),
            definition(ConstantIndex::from(1_usize), declared, body),
            definition(ConstantIndex::from(2_usize), unwinding_type, unwound),
        ];
        let (report, crossed) = run(&mut arena, &declarations);
        assert_eq!(report.judged()[0].verdict(), Verdict::Data);
        assert!(
            matches!(report.judged()[2].verdict(), Verdict::Checked { .. }),
            "a fixpoint recursing through both letters meets itself at the cancelled word: \
                 {:?}",
            report.judged()[2].verdict()
        );
        assert!(
            matches!(crossed.readmitted()[2].outcome(), Outcome::Defined { .. }),
            "and the kernel re-derives the respect: {:?}",
            crossed.readmitted()[2].outcome()
        );
        if presented {
            let Verdict::Refused(CheckRefusal::RuleNotRespected {
                at,
                rule,
                left,
                right,
            }) = report.judged()[1].verdict()
            else {
                panic!(
                    "a bare case over the circle is refused: {:?}",
                    report.judged()[1].verdict()
                );
            };
            assert_eq!(
                (at, rule),
                (case, gandr_kernel_term::RuleIndex::from(0_usize)),
                "at the first rule"
            );
            assert!(
                matches!(
                    arena.value(left),
                    Some(gandr_core_term::Value::Constructor { tag, .. }) if *tag == looped
                ),
                "naming its left side, `Loop(Unloop(x))`"
            );
            assert!(
                matches!(
                    arena.value(right),
                    Some(gandr_core_term::Value::Variable { .. })
                ),
                "and its right side, `x`"
            );
        }
        else {
            assert!(
                matches!(crossed.readmitted()[1].outcome(), Outcome::Defined { .. }),
                "the same case over a free circle checks and readmits: {:?}",
                crossed.readmitted()[1].outcome()
            );
        }
    }
}

#[test]
fn a_fold_nesting_its_call_is_judged_on_the_bind_it_elaborates_to()
{
    let (looped, unlooped) = (ConstructorTag::from(1_usize), ConstructorTag::from(2_usize));
    // `fix f. λy. case y { Base ⇒ return Base; Loop(x) ⇒ return
    // Loop^n(f(x)); Unloop(x) ⇒ return Unloop(Unloop(f(x))) }`, the call
    // written where a value is read: doubling at `n = 2`, and at `n = 1` a
    // fold that tells `Loop(Unloop(x))` apart from `x`.
    for (loops, respected) in [(2_usize, true), (1_usize, false)] {
        let mut arena = CoreArena::new();
        let own = arena.value_type_data(ConstantIndex::from(0_usize), vec![]);
        let motive = arena.comp_type_returner(own);
        let base = word(&mut arena, &[]);
        let returned = arena.computation_return(base);
        let mut arm = |letter: ConstructorTag, count: usize| {
            let recursive = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(2_u32));
            let field = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
            let forced = arena.computation_force(recursive);
            let called = arena.computation_application(forced, field);
            let mut built = arena.value_nested(called);
            for _ in 0_usize .. count {
                built = arena.value_constructor(own, letter, vec![built]);
            }
            let result = arena.computation_return(built);
            arena.computation_lambda(result)
        };
        let (lettered, inverted) = (arm(looped, loops), arm(unlooped, 2_usize));
        let argument = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let case = arena.computation_data_case(
            argument,
            motive,
            vec![returned, lettered, inverted],
            [0_usize, 1, 1]
                .map(gandr_kernel_term::FieldCount::from)
                .to_vec(),
        );
        let lambda = arena.computation_lambda(case);
        let fixpoint = arena.computation_fixpoint(
            lambda,
            gandr_kernel_term::FixpointEvidence::StructuralDescent,
        );
        let fold = arena.value_thunk(fixpoint);
        let arrow = arena.comp_type_arrow(own, motive);
        let fold_type = arena.value_type_thunk(arrow);
        let declarations = vec![
            circle(&mut arena, cancellations()),
            definition(ConstantIndex::from(1_usize), fold_type, fold),
        ];
        let (report, crossed) = run(&mut arena, &declarations);
        if respected {
            assert!(
                matches!(report.judged()[1].verdict(), Verdict::Checked { .. }),
                "the doubling fold's call, bound ahead of its arm, unfolds at the cancelled \
                     word: {:?}",
                report.judged()[1].verdict()
            );
            assert!(
                matches!(crossed.readmitted()[1].outcome(), Outcome::Defined { .. }),
                "and the kernel re-derives the respect: {:?}",
                crossed.readmitted()[1].outcome()
            );
        }
        else {
            assert!(
                matches!(
                    report.judged()[1].verdict(),
                    Verdict::Refused(CheckRefusal::RuleNotRespected { rule, .. })
                        if rule == gandr_kernel_term::RuleIndex::from(0_usize)
                ),
                "a fold the first rule tells apart is refused there: {:?}",
                report.judged()[1].verdict()
            );
        }
    }
}

#[test]
fn a_fold_before_a_trailing_parameter_is_read_as_the_fixpoint()
{
    let (looped, unlooped) = (ConstructorTag::from(1_usize), ConstructorTag::from(2_usize));
    // `fix f. λw. λs. case w { Base ⇒ return s; Loop(x) ⇒ f(x, Loop(s));
    // Unloop(x) ⇒ f(x, L(s)) }` at `Circle → Circle → F Circle`, the case
    // beneath the state's binder: the word wound onto the state. With `L`
    // the inverse letter the state cancels as the word does; with `L` the
    // loop again, `Loop(Unloop(x))` winds the state twice where `x` leaves it.
    for (inverse, respected) in [(unlooped, true), (looped, false)] {
        let mut arena = CoreArena::new();
        let own = arena.value_type_data(ConstantIndex::from(0_usize), vec![]);
        let motive = arena.comp_type_returner(own);
        let state = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let ended = arena.computation_return(state);
        let mut arm = |letter: ConstructorTag| {
            // Under the self binder, the word, the state and the field: `f`
            // is three out and the state one.
            let recursive = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(3_u32));
            let field = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
            let state = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
            let wound = arena.value_constructor(own, letter, vec![state]);
            let forced = arena.computation_force(recursive);
            let called = arena.computation_application(forced, field);
            let passed = arena.computation_application(called, wound);
            arena.computation_lambda(passed)
        };
        let (lettered, inverted) = (arm(looped), arm(inverse));
        let word = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
        let case = arena.computation_data_case(
            word,
            motive,
            vec![ended, lettered, inverted],
            [0_usize, 1, 1]
                .map(gandr_kernel_term::FieldCount::from)
                .to_vec(),
        );
        let stated = arena.computation_lambda(case);
        let lambda = arena.computation_lambda(stated);
        let fixpoint = arena.computation_fixpoint(
            lambda,
            gandr_kernel_term::FixpointEvidence::StructuralDescent,
        );
        let fold = arena.value_thunk(fixpoint);
        let passing = arena.comp_type_arrow(own, motive);
        let arrow = arena.comp_type_arrow(own, passing);
        let fold_type = arena.value_type_thunk(arrow);
        let declarations = vec![
            circle(&mut arena, cancellations()),
            definition(ConstantIndex::from(1_usize), fold_type, fold),
        ];
        let (report, crossed) = run(&mut arena, &declarations);
        if respected {
            assert!(
                matches!(report.judged()[1].verdict(), Verdict::Checked { .. }),
                "the fold meets itself at the cancelled word from one fresh state: {:?}",
                report.judged()[1].verdict()
            );
            assert!(
                matches!(crossed.readmitted()[1].outcome(), Outcome::Defined { .. }),
                "and the kernel re-derives the respect: {:?}",
                crossed.readmitted()[1].outcome()
            );
        }
        else {
            assert!(
                matches!(
                    report.judged()[1].verdict(),
                    Verdict::Refused(CheckRefusal::RuleNotRespected { at, rule, .. })
                        if at == case && rule == gandr_kernel_term::RuleIndex::from(0_usize)
                ),
                "a state wound twice is told apart from the state at the first rule: {:?}",
                report.judged()[1].verdict()
            );
        }
    }
}

#[test]
fn a_loop_is_a_word_at_its_path_in_both_checkers()
{
    use gandr_kernel_term::FreeCell;
    use gandr_kernel_term::FreeCells;
    use gandr_kernel_term::Presentation;
    use gandr_kernel_term::RuleNode;

    let mut arena = CoreArena::new();
    let kind = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let (sort, words) = (ConstantIndex::from(0_usize), ConstantIndex::from(1_usize));
    let carrier = arena.value_type_data(sort, vec![]);
    let own = arena.value_type_data(words, vec![]);
    let point = arena.value_constructor(carrier, ConstructorTag::from(0_usize), vec![]);
    let path = arena.value_type_path(carrier, point, point);
    let base =
        || -> Box<[RuleNode]> { [RuleNode::Constructor(ConstructorTag::from(0_usize))].into() };
    let cells = FreeCells::new(sort, vec![FreeCell::new(base(), base())]);
    let table = || vec![vec![], vec![own], vec![own]];
    // The one-point sort, and the words of one loop at its point.
    let one_point = Declaration::data(
        sort,
        DataSignature::new(vec![], vec![vec![]], kind).into(),
        OriginToken::from(0_usize),
    );
    let loops = Declaration::data(
        words,
        DataSignature::new(vec![], table(), kind)
            .presented(Presentation::words(cells.clone()))
            .into(),
        OriginToken::from(1_usize),
    );
    // `loop : Path(S, base, base)`, the word of its one letter.
    let empty = arena.value_constructor(own, ConstructorTag::from(0_usize), vec![]);
    let letter = arena.value_constructor(own, ConstructorTag::from(1_usize), vec![empty]);
    // Read back at the words' own type.
    let named = arena.value_constant(ConstantIndex::from(2_usize));
    // `fix f. λp. case p { here ⇒ return here; g ∷ q ⇒ r ← f(q); return
    // g ∷ r; … }` at `Path(S, base, base) → F Path(S, base, base)`.
    let motive = arena.comp_type_returner(path);
    let nil = arena.computation_return(empty);
    let mut arm = |tag: usize| {
        let recursive = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(2_u32));
        let field = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let forced = arena.computation_force(recursive);
        let folded = arena.computation_application(forced, field);
        let result = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let rebuilt = arena.value_constructor(own, ConstructorTag::from(tag), vec![result]);
        let returned = arena.computation_return(rebuilt);
        let sequenced = arena.computation_bind(folded, returned);
        arena.computation_lambda(sequenced)
    };
    let (lettered, inverted) = (arm(1), arm(2));
    let argument = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let case = arena.computation_data_case(
        argument,
        motive,
        vec![nil, lettered, inverted],
        [0_usize, 1, 1]
            .map(gandr_kernel_term::FieldCount::from)
            .to_vec(),
    );
    let lambda = arena.computation_lambda(case);
    let fixpoint = arena.computation_fixpoint(
        lambda,
        gandr_kernel_term::FixpointEvidence::StructuralDescent,
    );
    let fold = arena.value_thunk(fixpoint);
    let arrow = arena.comp_type_arrow(path, motive);
    let fold_type = arena.value_type_thunk(arrow);
    // The same words with their cancellations dropped.
    let tampered = Declaration::data(
        ConstantIndex::from(5_usize),
        DataSignature::new(vec![], table(), kind)
            .presented(Presentation::new(vec![]).carrying(cells))
            .into(),
        OriginToken::from(5_usize),
    );
    let declarations = vec![
        one_point,
        loops,
        definition(ConstantIndex::from(2_usize), path, letter),
        definition(ConstantIndex::from(3_usize), own, named),
        definition(ConstantIndex::from(4_usize), fold_type, fold),
        tampered,
    ];
    let (report, crossed) = run(&mut arena, &declarations);
    for (position, what) in [
        (2, "a word checks at the path of its point"),
        (3, "a path at the looped point converts with its words"),
        (
            4,
            "a fold over a path splits its words and respects both cancellations",
        ),
    ] {
        assert!(
            matches!(report.judged()[position].verdict(), Verdict::Checked { .. }),
            "{what}: {:?}",
            report.judged()[position].verdict()
        );
        assert!(
            matches!(
                crossed.readmitted()[position].outcome(),
                Outcome::Defined { .. }
            ),
            "and the kernel agrees: {:?}",
            crossed.readmitted()[position].outcome()
        );
    }
    assert!(
        matches!(crossed.readmitted()[1].outcome(), Outcome::Data { .. }),
        "the words admit as their cells mint them: {:?}",
        crossed.readmitted()[1].outcome()
    );
    assert_eq!(
        crossed.readmitted()[5].outcome(),
        &Outcome::Rejected(gandr_kernel_core::KernelError::WordsRefused(
            gandr_kernel_term::CellFault::NotMinted
        )),
        "the kernel re-mints the words and refuses a twin whose cancellations were dropped"
    );
}

/// The parts of the one-loop circle the loop witnesses build on.
struct OneLoop
{
    /// The sort, `S`.
    carrier: ValueTypeId,
    /// Its point, `Base`.
    point: ValueId,
    /// The words' empty word, reflexivity at the point.
    empty: ValueId,
    /// The word of the loop's inverse letter.
    inverse: ValueId,
    /// The constant `loop`, whose body is the word of its letter.
    named: ValueId,
}

/// The one-point sort at constant 0, the words of one loop at its point at
/// constant 1, and `loop` at constant 2, the word of its one letter at
/// `Path(S, Base, Base)`.
///
/// # Specification
/// trivial.
fn one_loop(arena: &mut CoreArena) -> (Vec<Declaration>, OneLoop)
{
    use gandr_kernel_term::FreeCell;
    use gandr_kernel_term::FreeCells;
    use gandr_kernel_term::Presentation;
    use gandr_kernel_term::RuleNode;

    let kind = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let (sort, words) = (ConstantIndex::from(0_usize), ConstantIndex::from(1_usize));
    let carrier = arena.value_type_data(sort, vec![]);
    let own = arena.value_type_data(words, vec![]);
    let point = arena.value_constructor(carrier, ConstructorTag::from(0_usize), vec![]);
    let path = arena.value_type_path(carrier, point, point);
    let base =
        || -> Box<[RuleNode]> { [RuleNode::Constructor(ConstructorTag::from(0_usize))].into() };
    let cells = FreeCells::new(sort, vec![FreeCell::new(base(), base())]);
    let empty = arena.value_constructor(own, ConstructorTag::from(0_usize), vec![]);
    let letter = arena.value_constructor(own, ConstructorTag::from(1_usize), vec![empty]);
    let inverse = arena.value_constructor(own, ConstructorTag::from(2_usize), vec![empty]);
    let named = arena.value_constant(ConstantIndex::from(2_usize));
    let declarations = vec![
        Declaration::data(
            sort,
            DataSignature::new(vec![], vec![vec![]], kind).into(),
            OriginToken::from(0_usize),
        ),
        Declaration::data(
            words,
            DataSignature::new(vec![], vec![vec![], vec![own], vec![own]], kind)
                .presented(Presentation::words(cells))
                .into(),
            OriginToken::from(1_usize),
        ),
        definition(ConstantIndex::from(2_usize), path, letter),
    ];
    (declarations, OneLoop {
        carrier,
        point,
        empty,
        inverse,
        named,
    })
}

/// `thunk (λx. case x { Base ⇒ return answer; loop ⇒ arm… })` at
/// `motive`, the case's motive and the function's codomain alike.
///
/// # Specification
/// trivial.
fn case_over(
    arena: &mut CoreArena,
    (carrier, motive): (ValueTypeId, gandr_core_term::CompTypeId),
    answer: ValueId,
    arms: &[ValueId],
) -> (ValueTypeId, ValueId)
{
    let mut branches = vec![arena.computation_return(answer)];
    branches.extend(arms.iter().map(|&arm| arena.computation_return(arm)));
    let scrutinee = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let case = arena.computation_data_case(
        scrutinee,
        motive,
        branches,
        [0_usize].map(gandr_kernel_term::FieldCount::from).to_vec(),
    );
    let lambda = arena.computation_lambda(case);
    let pi = arena.comp_type_pi(carrier, motive);
    (arena.value_type_thunk(pi), arena.value_thunk(lambda))
}

#[test]
fn a_case_over_the_circle_owes_its_loop_377()
{
    let mut arena = CoreArena::new();
    let (mut declarations, circle) = one_loop(&mut arena);
    let x = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let joined = arena.value_type_path(circle.carrier, circle.point, x);
    let joined = arena.comp_type_returner(joined);
    let looped = arena.value_type_path(circle.carrier, x, x);
    let looped = arena.comp_type_returner(looped);
    let kept = arena.comp_type_returner(circle.carrier);
    // Reflexivity joining the point to every point, which the loop carries
    // to the loop; reflexivity and the loop at every point, each of which
    // conjugation by the loop fixes; and the map collapsing the circle,
    // whose constant family owes nothing.
    for (position, (motive, answer)) in [
        (joined, circle.empty),
        (looped, circle.empty),
        (looped, circle.named),
        (kept, circle.point),
    ]
    .into_iter()
    .enumerate()
    {
        let (declared, body) = case_over(&mut arena, (circle.carrier, motive), answer, &[]);
        let constant = ConstantIndex::from(position.saturating_add(3));
        declarations.push(definition(constant, declared, body));
    }
    // The family `x ↦ Unit → F (Path(S, x, x))`, dependent and no returner,
    // owed at the loop and refused with an arm for the loop alike.
    let unit = arena.value_type_unit();
    let behind = arena.comp_type_arrow(unit, looped);
    let answered = arena.computation_return(circle.empty);
    let answered = arena.computation_lambda(answered);
    for (constant, branches) in [(7_usize, 1_usize), (8, 2)] {
        let scrutinee = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let case = arena.computation_data_case(
            scrutinee,
            behind,
            vec![answered; branches],
            [0_usize].map(gandr_kernel_term::FieldCount::from).to_vec(),
        );
        let lambda = arena.computation_lambda(case);
        let pi = arena.comp_type_pi(circle.carrier, behind);
        let declared = arena.value_type_thunk(pi);
        let body = arena.value_thunk(lambda);
        declarations.push(definition(ConstantIndex::from(constant), declared, body));
    }
    let (report, crossed) = run(&mut arena, &declarations);
    assert!(
        matches!(
            report.judged()[3].verdict(),
            Verdict::Refused(CheckRefusal::LoopNotRespected { cell, .. })
                if cell == gandr_kernel_term::CellIndex::from(0_usize)
        ),
        "the circle is not contractible: carried along the loop, reflexivity at the \
             point is the loop: {:?}",
        report.judged()[3].verdict()
    );
    for (position, what) in [
        (4, "reflexivity at every point respects the loop"),
        (
            5,
            "the loop at every point respects the loop, read as its word",
        ),
        (6, "a non-dependent case owes no loop"),
    ] {
        assert!(
            matches!(report.judged()[position].verdict(), Verdict::Checked { .. }),
            "{what}: {:?}",
            report.judged()[position].verdict()
        );
        assert!(
            matches!(
                crossed.readmitted()[position].outcome(),
                Outcome::Defined { .. }
            ),
            "and the kernel re-derives it: {:?}",
            crossed.readmitted()[position].outcome()
        );
    }
    for position in [7_usize, 8] {
        assert!(
            matches!(
                report.judged()[position].verdict(),
                Verdict::Refused(CheckRefusal::LoopNotRespected {
                    reason: gandr_core_checker::LoopRespect::Apart,
                    ..
                })
            ),
            "a dependent family that is no returner carries no loop: {:?}",
            report.judged()[position].verdict()
        );
    }
}

/// A case over a sort with loops takes one branch per constructor, or one
/// more per loop, and no other count: over the one-loop circle, three
/// branches are refused as non-exhaustive.
#[test]
fn a_case_over_the_circle_takes_its_constructors_and_loops_only()
{
    let mut arena = CoreArena::new();
    let (mut declarations, circle) = one_loop(&mut arena);
    let kept = arena.comp_type_returner(circle.carrier);
    let (declared, body) = case_over(&mut arena, (circle.carrier, kept), circle.point, &[
        circle.point,
        circle.point,
    ]);
    declarations.push(definition(ConstantIndex::from(3_usize), declared, body));
    let (report, _) = run(&mut arena, &declarations);
    assert!(
        matches!(
            report.judged()[3].verdict(),
            Verdict::Refused(CheckRefusal::NonExhaustiveDataCase(_))
        ),
        "one constructor and one loop admit one or two branches, not three: {:?}",
        report.judged()[3].verdict()
    );
}

/// `thunk (λa. λb. case a { Base ⇒ case b { Base ⇒ answer } })` at `(a b
/// : S) → motive`, `motive` read under both binders and the outer case's
/// motive the same family over its own binder.
///
/// # Specification
/// trivial.
fn nested_over(
    arena: &mut CoreArena,
    (carrier, nested): (ValueTypeId, Nested),
    answer: gandr_core_term::ComputationId,
) -> (ValueTypeId, ValueId)
{
    // Inside the outer case's branch at `Base`, the inner case answers at
    // the family's instance at the point, whose binder it ignores.
    let inner_motive = nested_motive(arena, (carrier, nested), None);
    let b = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let inner = arena.computation_data_case(
        b,
        inner_motive,
        vec![answer],
        [0_usize].map(gandr_kernel_term::FieldCount::from).to_vec(),
    );
    let outer_motive = nested_motive(arena, (carrier, nested), Some(DeBruijnIndex::from(0_u32)));
    let a = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
    let outer = arena.computation_data_case(
        a,
        outer_motive,
        vec![inner],
        [0_usize].map(gandr_kernel_term::FieldCount::from).to_vec(),
    );
    let body = arena.computation_lambda(outer);
    let body = arena.computation_lambda(body);
    let codomain = nested_motive(arena, (carrier, nested), Some(DeBruijnIndex::from(1_u32)));
    let pi = arena.comp_type_pi(carrier, codomain);
    let pi = arena.comp_type_pi(carrier, pi);
    (arena.value_type_thunk(pi), arena.value_thunk(body))
}

/// The point `Base` of [`one_loop`]'s sort, for a family read at the
/// point rather than at a variable.
///
/// # Specification
/// trivial.
fn base(
    arena: &mut CoreArena,
    carrier: ValueTypeId,
) -> ValueId
{
    arena.value_constructor(carrier, ConstructorTag::from(0_usize), vec![])
}

/// The fibre a nested witness answers in, over the sort's point `a`.
#[derive(Clone, Copy, Debug)]
enum Nested
{
    /// `F Path(S, a, a)`.
    Looped,
    /// `F Path(S, Base, a)`.
    Joined,
    /// `F U (Path(S, a, a) → F Path(S, a, a))`: a fibre that reads `a` and
    /// is no path type over the sort.
    Endomaps,
}

/// `nested`'s returner with `a` the variable `index` past `past` more
/// binders, or the point for `None`.
///
/// # Specification
/// trivial.
fn nested_motive(
    arena: &mut CoreArena,
    (carrier, nested): (ValueTypeId, Nested),
    index: Option<DeBruijnIndex>,
) -> gandr_core_term::CompTypeId
{
    let at = |arena: &mut CoreArena, past: u32| match index {
        Some(index) => {
            let index = DeBruijnIndex::from(u32::from(index).saturating_add(past));
            arena.value_variable(Zone::Intuitionistic, index)
        },
        None => base(arena, carrier),
    };
    let a = at(arena, 0);
    let fibre = match nested {
        Nested::Looped => arena.value_type_path(carrier, a, a),
        Nested::Joined => {
            let point = base(arena, carrier);
            arena.value_type_path(carrier, point, a)
        },
        Nested::Endomaps => {
            let path = arena.value_type_path(carrier, a, a);
            // Under the function's own binder `a` is lifted past it.
            let lifted = at(arena, 1);
            let codomain = arena.value_type_path(carrier, lifted, lifted);
            let returns = arena.comp_type_returner(codomain);
            let arrow = arena.comp_type_pi(path, returns);
            arena.value_type_thunk(arrow)
        },
    };
    arena.comp_type_returner(fibre)
}

#[test]
fn a_nested_loop_obligation_holds_the_other_scrutinee_at_its_point_464()
{
    let mut arena = CoreArena::new();
    let (mut declarations, circle) = one_loop(&mut arena);
    for (position, nested) in [(3_usize, Nested::Looped), (4_usize, Nested::Joined)] {
        let answer = arena.computation_return(circle.empty);
        let (declared, body) = nested_over(&mut arena, (circle.carrier, nested), answer);
        declarations.push(definition(ConstantIndex::from(position), declared, body));
    }
    let (report, crossed) = run(&mut arena, &declarations);
    assert!(
        matches!(report.judged()[3].verdict(), Verdict::Checked { .. }),
        "held at `b = Base`, the answer over `a` is reflexivity, which the loop fixes: {:?}",
        report.judged()[3].verdict()
    );
    assert!(
        matches!(crossed.readmitted()[3].outcome(), Outcome::Defined { .. }),
        "and the kernel re-derives it, holding `b` as the checker does: {:?}",
        crossed.readmitted()[3].outcome()
    );
    assert!(
        matches!(
            report.judged()[4].verdict(),
            Verdict::Refused(CheckRefusal::LoopNotRespected {
                reason: gandr_core_checker::LoopRespect::Apart,
                ..
            })
        ),
        "holding `b` leaves the obligation over `a` owed: the circle is still not \
             contractible: {:?}",
        report.judged()[4].verdict()
    );
}

#[test]
fn a_nested_loop_obligation_owes_its_square_off_a_set_464()
{
    let mut arena = CoreArena::new();
    let (mut declarations, circle) = one_loop(&mut arena);
    // `U (Path(S, a, a) → F Path(S, a, a))`, answered by the identity at
    // the point.
    let p = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let identity = arena.computation_return(p);
    let identity = arena.computation_lambda(identity);
    let identity = arena.value_thunk(identity);
    let answer = arena.computation_return(identity);
    let (declared, body) = nested_over(&mut arena, (circle.carrier, Nested::Endomaps), answer);
    declarations.push(definition(ConstantIndex::from(3_usize), declared, body));
    let (report, _crossed) = run(&mut arena, &declarations);
    assert!(
        matches!(
            report.judged()[3].verdict(),
            Verdict::Refused(CheckRefusal::LoopNotRespected {
                reason: gandr_core_checker::LoopRespect::NotPresentedSet,
                ..
            })
        ),
        "off a set, holding `b` at its point drops the square between the loops, which \
             is owed: {:?}",
        report.judged()[3].verdict()
    );
}

#[test]
fn a_path_whose_endpoints_compute_the_point_is_its_words_485()
{
    let mut arena = CoreArena::new();
    let (mut declarations, circle) = one_loop(&mut arena);
    // `kept = thunk (λx. case x { Base ⇒ return Base })` at constant 3,
    // which each endpoint calls at the point: it computes the point
    // without spelling it.
    let returner = arena.comp_type_returner(circle.carrier);
    let (kept_type, kept) = case_over(&mut arena, (circle.carrier, returner), circle.point, &[]);
    declarations.push(definition(ConstantIndex::from(3_usize), kept_type, kept));
    // `thunk (return ε)` at `U F Path(S, ⟨kept(Base)⟩, ⟨kept(Base)⟩)`: the
    // empty word, reflexivity at the point as the surface lowers it,
    // synthesises the words and crosses to the path.
    let function = arena.value_constant(ConstantIndex::from(3_usize));
    let forced = arena.computation_force(function);
    let applied = arena.computation_application(forced, circle.point);
    let computed = arena.value_returned(applied);
    let path = arena.value_type_path(circle.carrier, computed, computed);
    let returns_path = arena.comp_type_returner(path);
    let declared = arena.value_type_thunk(returns_path);
    let returned = arena.computation_return(circle.empty);
    let body = arena.value_thunk(returned);
    declarations.push(definition(ConstantIndex::from(4_usize), declared, body));
    let (report, crossed) = run(&mut arena, &declarations);
    assert!(
        matches!(report.judged()[4].verdict(), Verdict::Checked { .. }),
        "the path at a computed point is the words, which reflexivity at the point inhabits: \
             {:?}",
        report.judged()[4].verdict()
    );
    assert!(
        matches!(crossed.readmitted()[4].outcome(), Outcome::Defined { .. }),
        "and the kernel re-derives it at the path at the point: {:?}",
        crossed.readmitted()[4].outcome()
    );
}

#[test]
fn a_loop_obligation_unfolds_the_arm_s_definitions()
{
    let mut arena = CoreArena::new();
    let (mut declarations, circle) = one_loop(&mut arena);
    // `stay = thunk(return refl)` at constant 3, a definition the case's
    // point branch runs rather than a value it names.
    let at_point = arena.value_type_path(circle.carrier, circle.point, circle.point);
    let returner = arena.comp_type_returner(at_point);
    let suspended = arena.value_type_thunk(returner);
    let returned = arena.computation_return(circle.empty);
    let stay = arena.value_thunk(returned);
    declarations.push(definition(ConstantIndex::from(3_usize), suspended, stay));
    let x = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let looped = arena.value_type_path(circle.carrier, x, x);
    let looped = arena.comp_type_returner(looped);
    let joined = arena.value_type_path(circle.carrier, circle.point, x);
    let joined = arena.comp_type_returner(joined);
    // `λx. case x { Base ⇒ force stay }` at `Path(S, x, x)`, whose answer
    // conjugation by the loop fixes once `stay` unfolds, and at
    // `Path(S, Base, x)`, which the loop carries to the loop however far
    // `stay` unfolds.
    for (position, motive) in [(4_usize, looped), (5_usize, joined)] {
        let named = arena.value_constant(ConstantIndex::from(3_usize));
        let branch = arena.computation_force(named);
        let scrutinee = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let case = arena.computation_data_case(
            scrutinee,
            motive,
            vec![branch],
            [0_usize].map(gandr_kernel_term::FieldCount::from).to_vec(),
        );
        let lambda = arena.computation_lambda(case);
        let pi = arena.comp_type_pi(circle.carrier, motive);
        let declared = arena.value_type_thunk(pi);
        let body = arena.value_thunk(lambda);
        declarations.push(definition(ConstantIndex::from(position), declared, body));
    }
    let (report, crossed) = run(&mut arena, &declarations);
    assert!(
        matches!(report.judged()[4].verdict(), Verdict::Checked { .. }),
        "the obligation reads `stay` by what it computes: {:?}",
        report.judged()[4].verdict()
    );
    assert!(
        matches!(crossed.readmitted()[4].outcome(), Outcome::Defined { .. }),
        "and the kernel re-derives it by its own unfolding: {:?}",
        crossed.readmitted()[4].outcome()
    );
    assert!(
        matches!(
            report.judged()[5].verdict(),
            Verdict::Refused(CheckRefusal::LoopNotRespected { .. })
        ),
        "unfolding admits no case the obligation refutes: {:?}",
        report.judged()[5].verdict()
    );
}

#[test]
fn a_loop_arm_checks_at_the_path_over_its_loop()
{
    let mut arena = CoreArena::new();
    let (mut declarations, circle) = one_loop(&mut arena);
    let x = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let joined = arena.value_type_path(circle.carrier, circle.point, x);
    let joined = arena.comp_type_returner(joined);
    let looped = arena.value_type_path(circle.carrier, x, x);
    let looped = arena.comp_type_returner(looped);
    let kept = arena.comp_type_returner(circle.carrier);
    let stays = arena.value_here(circle.empty);
    // The flip: the loop's image is its inverse, a loop at the point's
    // image. Reflexivity at every point, its arm the path from its
    // conjugate to itself. Reflexivity joining the point to every point,
    // whose arm owes a path from the loop to reflexivity and offers
    // reflexivity at reflexivity.
    for (position, (motive, answer, arm)) in [
        (kept, circle.point, circle.inverse),
        (looped, circle.empty, stays),
        (joined, circle.empty, stays),
    ]
    .into_iter()
    .enumerate()
    {
        let (declared, body) = case_over(&mut arena, (circle.carrier, motive), answer, &[arm]);
        let constant = ConstantIndex::from(position.saturating_add(3));
        declarations.push(definition(constant, declared, body));
    }
    let (report, crossed) = run(&mut arena, &declarations);
    for (position, what) in [
        (3, "a non-dependent loop arm chooses the loop's image"),
        (4, "a dependent loop arm checks at the path over the loop"),
    ] {
        assert!(
            matches!(report.judged()[position].verdict(), Verdict::Checked { .. }),
            "{what}: {:?}",
            report.judged()[position].verdict()
        );
        assert!(
            matches!(
                crossed.readmitted()[position].outcome(),
                Outcome::Defined { .. }
            ),
            "and the kernel re-derives it: {:?}",
            crossed.readmitted()[position].outcome()
        );
    }
    assert!(
        matches!(
            report.judged()[5].verdict(),
            Verdict::Refused(CheckRefusal::EndpointMismatch { .. })
        ),
        "a dependent loop arm at the wrong endpoints is refused: {:?}",
        report.judged()[5].verdict()
    );
}

#[test]
fn a_composite_along_a_returned_path_cancels_in_both_checkers()
{
    let mut arena = CoreArena::new();
    let (mut declarations, circle) = one_loop(&mut arena);
    // `loop then back(loop)`: the composite runs along the inverse's
    // returned transport, which only computes once that path has run.
    let inverse =
        gandr_core_term::identity::back(&mut arena, circle.carrier, circle.point, circle.named);
    let inverse = arena.value_returned(inverse);
    let composite = gandr_core_term::identity::then(
        &mut arena,
        circle.carrier,
        circle.point,
        circle.named,
        inverse,
    );
    let composite = arena.value_returned(composite);
    let at_point = arena.value_type_path(circle.carrier, circle.point, circle.point);
    let cancelled = arena.value_type_path(at_point, composite, circle.empty);
    let reflexivity = arena.value_here(circle.empty);
    declarations.push(definition(
        ConstantIndex::from(3_usize),
        cancelled,
        reflexivity,
    ));
    // The same composite is not the loop.
    let apart = arena.value_type_path(at_point, composite, circle.named);
    let wrong = arena.value_here(circle.named);
    declarations.push(definition(ConstantIndex::from(4_usize), apart, wrong));
    let (report, crossed) = run(&mut arena, &declarations);
    assert!(
        matches!(report.judged()[3].verdict(), Verdict::Checked { .. }),
        "the composite cancels to the empty word: {:?}",
        report.judged()[3].verdict()
    );
    assert!(
        matches!(crossed.readmitted()[3].outcome(), Outcome::Defined { .. }),
        "and the kernel runs the returned path before transporting along it: {:?}",
        crossed.readmitted()[3].outcome()
    );
    assert!(
        matches!(
            report.judged()[4].verdict(),
            Verdict::Refused(CheckRefusal::EndpointMismatch { .. })
        ),
        "the composite is not the loop: {:?}",
        report.judged()[4].verdict()
    );
}

#[test]
fn a_word_written_as_a_transport_path_is_that_path_in_both_checkers_397()
{
    let mut arena = CoreArena::new();
    let (mut declarations, circle) = one_loop(&mut arena);
    let at_point = arena.value_type_path(circle.carrier, circle.point, circle.point);
    // `loop then ε`: the loop transported along the empty word, written
    // as a constructor of the words, whose type is the words' own.
    let joined = gandr_core_term::identity::then(
        &mut arena,
        circle.carrier,
        circle.point,
        circle.named,
        circle.empty,
    );
    let joined = arena.value_returned(joined);
    let composed = arena.value_type_path(at_point, joined, circle.named);
    let looped = arena.value_here(circle.named);
    declarations.push(definition(ConstantIndex::from(3_usize), composed, looped));
    // `back(ℓ⁻¹ ∷ ε)`: the inverse letter's word, inverted, is the loop.
    let inverted =
        gandr_core_term::identity::back(&mut arena, circle.carrier, circle.point, circle.inverse);
    let inverted = arena.value_returned(inverted);
    let reverted = arena.value_type_path(at_point, inverted, circle.named);
    declarations.push(definition(ConstantIndex::from(4_usize), reverted, looped));
    // The composite is not reflexivity.
    let reflexive = arena.value_type_path(at_point, joined, circle.empty);
    let stays = arena.value_here(circle.empty);
    declarations.push(definition(ConstantIndex::from(5_usize), reflexive, stays));
    let (report, crossed) = run(&mut arena, &declarations);
    for (position, what) in [
        (3, "the loop composed with the empty word is the loop"),
        (4, "the inverse letter's word inverted is the loop"),
    ] {
        assert!(
            matches!(report.judged()[position].verdict(), Verdict::Checked { .. }),
            "{what}: {:?}",
            report.judged()[position].verdict()
        );
        assert!(
            matches!(
                crossed.readmitted()[position].outcome(),
                Outcome::Defined { .. }
            ),
            "and the kernel follows the word as the same path: {:?}",
            crossed.readmitted()[position].outcome()
        );
    }
    assert!(
        matches!(
            report.judged()[5].verdict(),
            Verdict::Refused(CheckRefusal::EndpointMismatch { .. })
        ),
        "the composite is not reflexivity: {:?}",
        report.judged()[5].verdict()
    );
}

#[test]
fn an_absurd_case_rests_on_apart_endpoints_in_both_checkers()
{
    let looped = ConstructorTag::from(1_usize);
    let unlooped = ConstructorTag::from(2_usize);
    let mut arena = CoreArena::new();
    let kind = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let own = arena.value_type_data(ConstantIndex::from(0_usize), vec![]);
    let empty = arena.value_type_data(ConstantIndex::from(1_usize), vec![]);
    let base = word(&mut arena, &[]);
    // `λe. case e {}` at `Path(Circle, left, right) → F Empty`, its type,
    // its lambda and its case.
    let absurd = |arena: &mut CoreArena, left: ValueId, right: ValueId| {
        let path = arena.value_type_path(own, left, right);
        let motive = arena.comp_type_returner(empty);
        let scrutinee = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let case = arena.computation_data_case(scrutinee, motive, vec![], vec![]);
        let lambda = arena.computation_lambda(case);
        let arrow = arena.comp_type_arrow(path, motive);
        (lambda, arrow, case)
    };
    let thunked = |arena: &mut CoreArena,
                   (lambda, arrow, case): (
        gandr_core_term::ComputationId,
        gandr_core_term::CompTypeId,
        gandr_core_term::ComputationId,
    )| {
        (
            arena.value_thunk(lambda),
            arena.value_type_thunk(arrow),
            case,
        )
    };
    let once = word(&mut arena, &[looped]);
    let formed = absurd(&mut arena, once, base);
    let (apart, apart_type, _) = thunked(&mut arena, formed);
    let named = arena.value_constant(ConstantIndex::from(3_usize));
    let formed = absurd(&mut arena, named, base);
    let (by_name, by_name_type, _) = thunked(&mut arena, formed);
    let cancelled = word(&mut arena, &[looped, unlooped]);
    let formed = absurd(&mut arena, cancelled, base);
    let (agree, agree_type, agree_case) = thunked(&mut arena, formed);
    // `λx. λe. case e {}` at `(x : Circle) → Path(Circle, Loop(x), Base)
    // → F Empty`: an endpoint holds a variable of the circle.
    let variable = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let open_word = arena.value_constructor(own, looped, vec![variable]);
    let (inner, arrow, open_case) = absurd(&mut arena, open_word, base);
    let outer = arena.computation_lambda(inner);
    let open = arena.value_thunk(outer);
    let pi = arena.comp_type_pi(own, arrow);
    let open_type = arena.value_type_thunk(pi);
    let declarations = vec![
        circle(&mut arena, cancellations()),
        Declaration::data(
            ConstantIndex::from(1_usize),
            DataSignature::new(vec![], vec![], kind).into(),
            OriginToken::from(1_usize),
        ),
        definition(ConstantIndex::from(2_usize), apart_type, apart),
        definition(ConstantIndex::from(3_usize), own, once),
        definition(ConstantIndex::from(4_usize), by_name_type, by_name),
        definition(ConstantIndex::from(5_usize), agree_type, agree),
        definition(ConstantIndex::from(6_usize), open_type, open),
    ];
    let (report, crossed) = run(&mut arena, &declarations);
    for (position, what) in [
        (2, "`Loop(Base)` and `Base` are apart"),
        (4, "a definition of `Loop(Base)` is read as its body"),
    ] {
        assert!(
            matches!(report.judged()[position].verdict(), Verdict::Checked { .. }),
            "{what}: {:?}",
            report.judged()[position].verdict()
        );
        assert!(
            matches!(
                crossed.readmitted()[position].outcome(),
                Outcome::Defined { .. }
            ),
            "and the kernel decides alike: {:?}",
            crossed.readmitted()[position].outcome()
        );
    }
    assert_eq!(
        report.judged()[5].verdict(),
        Verdict::Refused(CheckRefusal::NotApart {
            at: agree_case,
            reason: gandr_kernel_term::Apartness::Agree,
        }),
        "`Loop(Unloop(Base))` is `Base`"
    );
    assert_eq!(
        report.judged()[6].verdict(),
        Verdict::Refused(CheckRefusal::NotApart {
            at: open_case,
            reason: gandr_kernel_term::Apartness::Open,
        }),
        "`Loop(x)` is `Base` once `x` is `Unloop(Base)`"
    );
}

#[test]
fn a_fold_rests_on_the_laws_of_the_rules_it_computes_apart()
{
    let (turn, unturn) = (ConstantIndex::from(1_usize), ConstantIndex::from(2_usize));
    let (turn_unturn, unturn_turn) = (ConstantIndex::from(3_usize), ConstantIndex::from(4_usize));
    let wind = ConstantIndex::from(5_usize);
    let first = gandr_kernel_term::RuleIndex::from(0_usize);
    for (laws, admitted) in [
        (vec![turn_unturn, unturn_turn], true),
        (vec![], false),
        (vec![unturn_turn, turn_unturn], false),
    ] {
        let mut arena = CoreArena::new();
        let own = arena.value_type_data(ConstantIndex::from(0_usize), vec![]);
        let integer = arena.value_type_base(gandr_kernel_term::BaseType::Integer);
        let returner = arena.comp_type_returner(integer);
        // The integers' successor and predecessor, holes conversion
        // cannot see through.
        let step = arena.comp_type_arrow(integer, returner);
        let step = arena.value_type_thunk(step);
        let call = |arena: &mut CoreArena, operation, argument| {
            let operation = arena.value_constant(operation);
            let forced = arena.computation_force(operation);
            arena.computation_application(forced, argument)
        };
        // `Π n. turn(unturn(n)) = n`, the law of `Loop(Unloop(x)) ~> x`,
        // and its mirror.
        let mut law = |first_operation, second_operation| {
            let n = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
            let inner = call(&mut arena, second_operation, n);
            let inner = arena.value_returned(inner);
            let outer = call(&mut arena, first_operation, inner);
            let outer = arena.value_returned(outer);
            let path = arena.value_type_path(integer, outer, n);
            let returner = arena.comp_type_returner(path);
            let pi = arena.comp_type_pi(integer, returner);
            arena.value_type_thunk(pi)
        };
        let first_law = law(turn, unturn);
        let second_law = law(unturn, turn);
        // `fix f. λy. case y { Base ⇒ return 0; Loop(x) ⇒ turn(f(x));
        // Unloop(x) ⇒ unturn(f(x)) }`, each recursive run written where
        // a value is read: at `Loop(Unloop(x))` it computes
        // `turn(unturn(f(x)))`, which meets `f(x)` only by the first law.
        let zero = arena.value_literal(gandr_kernel_term::Literal::Integer(
            gandr_kernel_term::IntegerLiteral::new(
                gandr_kernel_term::Sign::NonNegative,
                gandr_kernel_term::Magnitude::zero(),
            ),
        ));
        let base = arena.computation_return(zero);
        let mut arm = |operation| {
            let recursive = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(2_u32));
            let field = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
            let forced = arena.computation_force(recursive);
            let folded = arena.computation_application(forced, field);
            let folded = arena.value_returned(folded);
            let applied = call(&mut arena, operation, folded);
            arena.computation_lambda(applied)
        };
        let looping = arm(turn);
        let unlooping = arm(unturn);
        let argument = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let case = arena.computation_data_case(
            argument,
            returner,
            vec![base, looping, unlooping],
            [0_usize, 1, 1]
                .map(gandr_kernel_term::FieldCount::from)
                .to_vec(),
        );
        let lambda = arena.computation_lambda(case);
        let fixpoint = arena.computation_fixpoint(
            lambda,
            gandr_kernel_term::FixpointEvidence::StructuralDescent,
        );
        let body = arena.value_thunk(fixpoint);
        let arrow = arena.comp_type_arrow(own, returner);
        let declared = arena.value_type_thunk(arrow);
        let hole = |constant: ConstantIndex, stated| {
            Declaration::new(
                constant,
                Maybe::Present(stated),
                Maybe::Absent(gandr_core_checker::body::Absent::Hole),
                OriginToken::from(usize::from(constant)),
            )
        };
        let declarations = vec![
            circle(&mut arena, cancellations()),
            hole(turn, step),
            hole(unturn, step),
            hole(turn_unturn, first_law),
            hole(unturn_turn, second_law),
            definition(wind, declared, body).lawful(laws),
        ];
        let (report, crossed) = run(&mut arena, &declarations);
        let verdict = report.judged()[5].verdict();
        if admitted {
            assert!(
                matches!(verdict, Verdict::Checked { .. }),
                "each rule's law relates the fold's two sides of it: {verdict:?}"
            );
            let assumed: Vec<_> = crossed.readmitted()[1 .. 5]
                .iter()
                .map(|entry| match *entry.outcome() {
                    Outcome::Assumed { admitted, .. } => admitted.position(),
                    ref other @ (Outcome::Data { .. }
                    | Outcome::Defined { .. }
                    | Outcome::Marked(_)
                    | Outcome::Static
                    | Outcome::Suspended
                    | Outcome::Refused(_)
                    | Outcome::Rejected(_)) => {
                        panic!("each hole crosses as an axiom: {other:?}")
                    },
                })
                .collect();
            let Outcome::Defined { ref audit, .. } = *crossed.readmitted()[5].outcome()
            else {
                panic!(
                    "and the kernel re-derives the fold from its laws: {:?}",
                    crossed.readmitted()[5].outcome()
                );
            };
            assert_eq!(
                audit.axioms(),
                assumed.as_slice(),
                "the fold rests on its laws as on the operations it calls"
            );
        }
        else {
            assert!(
                matches!(
                    verdict,
                    Verdict::Refused(CheckRefusal::RuleNotRespected { rule, .. }) if rule == first
                ),
                "without the first rule's law the fold is refused by that rule: {verdict:?}"
            );
            assert!(
                matches!(crossed.readmitted()[5].outcome(), Outcome::Marked(_)),
                "and the kernel is offered nothing: {:?}",
                crossed.readmitted()[5].outcome()
            );
        }
    }
}

/// A law states its path bare only for a rule over no variable, and
/// behind one parameter per variable otherwise, an arrow as well as a
/// Π: over `Twist(Base) ~> Base` and `Loop(Wrap(x)) ~> Base`, a fold
/// returning `c` at `Base` and `d` elsewhere rests on `d = c` stated bare
/// for the first rule and behind `Integer →`, the fold's value at `x`,
/// for the second; a bare statement for the second is refused by that
/// rule.
#[test]
fn a_law_is_stated_bare_only_over_no_variable()
{
    use gandr_kernel_term::RuleNode;
    let c = |tag: usize| RuleNode::Constructor(ConstructorTag::from(tag));
    let x = RuleNode::Variable(gandr_kernel_term::RuleVariable::from(0_u32));
    let (base, twist) = (ConstantIndex::from(1_usize), ConstantIndex::from(2_usize));
    let (closed, open) = (ConstantIndex::from(3_usize), ConstantIndex::from(4_usize));
    let second = gandr_kernel_term::RuleIndex::from(1_usize);
    for behind_an_arrow in [true, false] {
        let mut arena = CoreArena::new();
        let kind = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
        let own = arena.value_type_data(ConstantIndex::from(0_usize), vec![]);
        let integer = arena.value_type_base(gandr_kernel_term::BaseType::Integer);
        let returner = arena.comp_type_returner(integer);
        let rules = vec![
            gandr_kernel_term::PresentedRule::new([c(1), c(0)].into(), [c(0)].into()),
            gandr_kernel_term::PresentedRule::new([c(2), c(3), x].into(), [c(0)].into()),
        ];
        let presented = Declaration::data(
            ConstantIndex::from(0_usize),
            DataSignature::new(vec![], vec![vec![], vec![own], vec![own], vec![own]], kind)
                .presented(gandr_kernel_term::Presentation::new(rules))
                .into(),
            OriginToken::from(0_usize),
        );
        let [at_base, elsewhere] = [base, twist].map(|constant| arena.value_constant(constant));
        let bare = arena.value_type_path(integer, elsewhere, at_base);
        let stated = if behind_an_arrow {
            let returns = arena.comp_type_returner(bare);
            let arrow = arena.comp_type_arrow(integer, returns);
            arena.value_type_thunk(arrow)
        }
        else {
            bare
        };
        // `λy. case y { Base ⇒ return c; Twist(_) | Loop(_) | Wrap(_) ⇒ return d }`
        let base_arm = arena.computation_return(at_base);
        let [twist_arm, loop_arm, wrap_arm] = [(); 3].map(|()| {
            let returned = arena.computation_return(elsewhere);
            arena.computation_lambda(returned)
        });
        let scrutinee = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let case = arena.computation_data_case(
            scrutinee,
            returner,
            vec![base_arm, twist_arm, loop_arm, wrap_arm],
            [0_usize, 1, 1, 1]
                .map(gandr_kernel_term::FieldCount::from)
                .to_vec(),
        );
        let lambda = arena.computation_lambda(case);
        let fixpoint = arena.computation_fixpoint(
            lambda,
            gandr_kernel_term::FixpointEvidence::StructuralDescent,
        );
        let body = arena.value_thunk(fixpoint);
        let arrow = arena.comp_type_arrow(own, returner);
        let declared = arena.value_type_thunk(arrow);
        let hole = |constant: ConstantIndex, stated| {
            Declaration::new(
                constant,
                Maybe::Present(stated),
                Maybe::Absent(gandr_core_checker::body::Absent::Hole),
                OriginToken::from(usize::from(constant)),
            )
        };
        let declarations = vec![
            presented,
            hole(base, integer),
            hole(twist, integer),
            hole(closed, bare),
            hole(open, stated),
            definition(ConstantIndex::from(5_usize), declared, body).lawful(vec![closed, open]),
        ];
        let (report, _) = run(&mut arena, &declarations);
        let verdict = report.judged()[5].verdict();
        if behind_an_arrow {
            assert!(
                matches!(verdict, Verdict::Checked { .. }),
                "a bare law for the closed rule and an arrow-stated one for `Loop(x)` \
                     relate the fold: {verdict:?}"
            );
        }
        else {
            assert!(
                matches!(
                    verdict,
                    Verdict::Refused(CheckRefusal::RuleNotRespected { rule, .. }) if rule == second
                ),
                "a law over a variable stated bare relates nothing: {verdict:?}"
            );
        }
    }
}

#[test]
fn a_fold_into_the_paths_of_a_set_respects_its_rules()
{
    let first = gandr_kernel_term::RuleIndex::from(0_usize);
    let (lemma, fold) = (ConstantIndex::from(1_usize), ConstantIndex::from(2_usize));
    // The presented integers are a set: no cells, no loop at them. The
    // native integers are no data type, so nothing reads them as one.
    for set in [true, false] {
        let mut arena = CoreArena::new();
        let own = arena.value_type_data(ConstantIndex::from(0_usize), vec![]);
        let (carrier, point) = if set {
            (own, word(&mut arena, &[]))
        }
        else {
            let integer = arena.value_type_base(gandr_kernel_term::BaseType::Integer);
            let zero = arena.value_literal(gandr_kernel_term::Literal::Integer(
                gandr_kernel_term::IntegerLiteral::new(
                    gandr_kernel_term::Sign::NonNegative,
                    gandr_kernel_term::Magnitude::zero(),
                ),
            ));
            (integer, zero)
        };
        let path = arena.value_type_path(carrier, point, point);
        let returner = arena.comp_type_returner(path);
        // A lemma conversion cannot see through, from a loop at the point
        // to a loop at the point.
        let step = arena.comp_type_arrow(path, returner);
        let step = arena.value_type_thunk(step);
        // `fix f. λy. case y { Base ⇒ return here(p); Loop(x) ⇒
        // lemma(f(x)); Unloop(x) ⇒ lemma(f(x)) }`: at `Loop(Unloop(x))`
        // it computes `lemma(lemma(f(x)))`, which conversion never meets
        // with `f(x)`; both are loops at `p`.
        let reflexivity = arena.value_here(point);
        let base = arena.computation_return(reflexivity);
        let mut arm = || {
            let recursive = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(2_u32));
            let field = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
            let forced = arena.computation_force(recursive);
            let folded = arena.computation_application(forced, field);
            let folded = arena.value_returned(folded);
            let operation = arena.value_constant(lemma);
            let operation = arena.computation_force(operation);
            let applied = arena.computation_application(operation, folded);
            arena.computation_lambda(applied)
        };
        let looping = arm();
        let unlooping = arm();
        let argument = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let case = arena.computation_data_case(
            argument,
            returner,
            vec![base, looping, unlooping],
            [0_usize, 1, 1]
                .map(gandr_kernel_term::FieldCount::from)
                .to_vec(),
        );
        let lambda = arena.computation_lambda(case);
        let fixpoint = arena.computation_fixpoint(
            lambda,
            gandr_kernel_term::FixpointEvidence::StructuralDescent,
        );
        let body = arena.value_thunk(fixpoint);
        let arrow = arena.comp_type_arrow(own, returner);
        let declared = arena.value_type_thunk(arrow);
        let declarations = vec![
            circle(&mut arena, cancellations()),
            Declaration::new(
                lemma,
                Maybe::Present(step),
                Maybe::Absent(gandr_core_checker::body::Absent::Hole),
                OriginToken::from(usize::from(lemma)),
            ),
            definition(fold, declared, body),
        ];
        let (report, crossed) = run(&mut arena, &declarations);
        let verdict = report.judged()[2].verdict();
        if set {
            assert!(
                matches!(verdict, Verdict::Checked { .. }),
                "two loops at one point of a set are one loop: {verdict:?}"
            );
            assert!(
                matches!(crossed.readmitted()[2].outcome(), Outcome::Defined { .. }),
                "and the kernel re-derives the fold: {:?}",
                crossed.readmitted()[2].outcome()
            );
        }
        else {
            assert!(
                matches!(
                    verdict,
                    Verdict::Refused(CheckRefusal::RuleNotRespected { rule, .. }) if rule == first
                ),
                "loops in a type not read as a set are compared as written: {verdict:?}"
            );
        }
    }
}

#[test]
fn dependent_data_parameters_and_case_motives()
{
    let mut arena = CoreArena::new();
    let kind = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let parameter = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let element = arena.value_type_element(parameter, Level::zero());
    let family = ConstantIndex::from(0_usize);
    let indexed = ConstantIndex::from(1_usize);
    let declaration = Declaration::data(
        family,
        DataSignature::new(vec![kind], vec![vec![element]], kind).into(),
        OriginToken::from(0_usize),
    );
    let unit_type = arena.value_type_unit();
    let unit_code = arena.value_quote(unit_type);
    let unit = arena.value_unit();
    let datatype = arena.value_type_data(family, vec![unit_code]);
    let index_declaration = Declaration::data(
        indexed,
        DataSignature::new(vec![datatype], vec![vec![]], kind).into(),
        OriginToken::from(1_usize),
    );
    let scrutinee = arena.value_constructor(datatype, ConstructorTag::from(0_usize), vec![unit]);
    let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let motive_type = arena.value_type_data(indexed, vec![bound]);
    let motive = arena.comp_type_returner(motive_type);
    let branch_index =
        arena.value_constructor(datatype, ConstructorTag::from(0_usize), vec![bound]);
    let branch_type = arena.value_type_data(indexed, vec![branch_index]);
    let branch_value = arena.value_constructor(branch_type, ConstructorTag::from(0_usize), vec![]);
    let returned = arena.computation_return(branch_value);
    let branch = arena.computation_lambda(returned);
    let case = arena.computation_data_case(
        scrutinee,
        motive,
        vec![branch],
        [1_usize].map(gandr_kernel_term::FieldCount::from).to_vec(),
    );
    let body = arena.value_thunk(case);
    let expected_type = arena.value_type_data(indexed, vec![scrutinee]);
    let expected = arena.comp_type_returner(expected_type);
    let expected = arena.value_type_thunk(expected);
    let missing = arena.computation_data_case(scrutinee, motive, vec![], vec![]);
    let missing_body = arena.value_thunk(missing);
    // The branch's constructor has one field; a case stating none is minted
    // wrong, never written.
    let misstated = arena.computation_data_case(
        scrutinee,
        motive,
        vec![branch],
        [0_usize].map(gandr_kernel_term::FieldCount::from).to_vec(),
    );
    let misstated_body = arena.value_thunk(misstated);
    let declarations = [
        declaration,
        index_declaration,
        definition(ConstantIndex::from(2_usize), expected, body),
        definition(ConstantIndex::from(3_usize), expected, missing_body),
        definition(ConstantIndex::from(4_usize), expected, misstated_body),
    ];
    let (report, crossed) = run(&mut arena, &declarations);
    assert!(
        matches!(report.judged()[2].verdict(), Verdict::Checked { .. }),
        "{:?}",
        report.judged()[2].verdict()
    );
    assert!(
        matches!(crossed.readmitted()[2].outcome(), Outcome::Defined { .. }),
        "{:?}",
        crossed.readmitted()[2].outcome()
    );
    assert_eq!(
        report.judged()[3].verdict(),
        Verdict::Refused(CheckRefusal::NonExhaustiveDataCase(missing))
    );
    assert_eq!(
        report.judged()[4].verdict(),
        Verdict::Refused(CheckRefusal::MachineInvariant),
        "a case whose arities misstate its constructors' fields is refused"
    );
    assert!(crossed.audit().axioms().is_empty());
}

#[test]
fn record_width_depth_and_projection()
{
    let mut arena = CoreArena::new();
    let x = FieldLabel::from(String::from("x"));
    let y = FieldLabel::from(String::from("y"));
    let nested = FieldLabel::from(String::from("nested"));
    let missing = FieldLabel::from(String::from("missing"));
    let unit_type = arena.value_type_unit();
    let unit = arena.value_unit();
    let inner_wide = arena.value_type_record(BTreeMap::from([
        (x.clone(), unit_type),
        (y.clone(), unit_type),
    ]));
    let inner_narrow = arena.value_type_record(BTreeMap::from([(x.clone(), unit_type)]));
    let wide = arena.value_type_record(BTreeMap::from([
        (nested.clone(), inner_wide),
        (x.clone(), unit_type),
    ]));
    let narrow = arena.value_type_record(BTreeMap::from([(nested.clone(), inner_narrow)]));
    let empty = arena.value_type_record(BTreeMap::new());
    let inner = arena.value_record(BTreeMap::from([(x.clone(), unit), (y, unit)]));
    let record = arena.value_record(BTreeMap::from([(nested.clone(), inner), (x, unit)]));
    let variable = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let returned = arena.computation_return(variable);
    let lambda = arena.computation_lambda(returned);
    let function = arena.value_thunk(lambda);
    let result = arena.comp_type_returner(narrow);
    let arrow = arena.comp_type_arrow(wide, result);
    let arrow = arena.value_type_thunk(arrow);
    let reverse_result = arena.comp_type_returner(wide);
    let reverse = arena.comp_type_arrow(narrow, reverse_result);
    let reverse = arena.value_type_thunk(reverse);
    let projection = arena.computation_record_projection(record, nested);
    let projected = arena.value_thunk(projection);
    let projected_type = arena.comp_type_returner(inner_wide);
    let projected_type = arena.value_type_thunk(projected_type);
    let absent = arena.computation_record_projection(record, missing.clone());
    let absent_body = arena.value_thunk(absent);
    let missing_type = arena.value_type_record(BTreeMap::from([(missing, unit_type)]));
    let wrong_depth = arena.value_type_record(BTreeMap::from([(
        FieldLabel::from(String::from("nested")),
        unit_type,
    )]));
    let empty_record = arena.value_record(BTreeMap::new());
    let declarations = [
        definition(ConstantIndex::from(0_usize), narrow, record),
        definition(ConstantIndex::from(1_usize), arrow, function),
        definition(ConstantIndex::from(2_usize), projected_type, projected),
        definition(ConstantIndex::from(3_usize), empty, record),
        definition(ConstantIndex::from(4_usize), projected_type, absent_body),
        definition(ConstantIndex::from(5_usize), missing_type, record),
        definition(ConstantIndex::from(6_usize), wrong_depth, record),
        definition(ConstantIndex::from(7_usize), reverse, function),
        Declaration::new(
            ConstantIndex::from(8_usize),
            Maybe::Absent(gandr_core_checker::signature::Absent::Unsigned),
            Maybe::Present(record),
            OriginToken::from(8_usize),
        ),
        Declaration::new(
            ConstantIndex::from(9_usize),
            Maybe::Absent(gandr_core_checker::signature::Absent::Unsigned),
            Maybe::Present(empty_record),
            OriginToken::from(9_usize),
        ),
    ];
    let (report, crossed) = run(&mut arena, &declarations);
    for position in 0 .. 4_usize {
        assert!(
            matches!(report.judged()[position].verdict(), Verdict::Checked { .. }),
            "{position}: {:?}",
            report.judged()[position].verdict()
        );
        assert!(
            matches!(
                crossed.readmitted()[position].outcome(),
                Outcome::Defined { .. }
            ),
            "{position}: {:?}",
            crossed.readmitted()[position].outcome()
        );
    }
    assert_eq!(
        report.judged()[4].verdict(),
        Verdict::Refused(CheckRefusal::AbsentRecordField(absent))
    );
    assert_eq!(
        report.judged()[5].verdict(),
        Verdict::Refused(CheckRefusal::MissingRecordField {
            at: record,
            expected: missing_type
        })
    );
    assert!(matches!(
        report.judged()[6].verdict(),
        Verdict::Refused(CheckRefusal::ShapeMismatch { .. })
    ));
    assert!(matches!(
        report.judged()[7].verdict(),
        Verdict::Refused(CheckRefusal::TypeMismatch(_))
    ));
    let Verdict::Synthesised { synthesised, .. } = report.judged()[8].verdict()
    else {
        panic!("an unsigned record infers its fields");
    };
    let Some(matched_native_node) = arena.value_type(synthesised.produced().id())
    else {
        panic!("record classifier");
    };
    let ValueType::Record(ref fields) = *matched_native_node
    else {
        panic!("record classifier");
    };
    assert!(
        fields
            .keys()
            .map(core::convert::AsRef::as_ref)
            .eq(["nested", "x"])
    );
    for (label, &field) in fields {
        if label.as_ref() == "x" {
            assert!(arena.value_type(field).is_some_and(
                |held| matches!(*held, ValueType::Product(ref parts) if parts.is_empty())
            ));
        }
        else {
            let Some(matched_native_node) = arena.value_type(field)
            else {
                panic!("nested record classifier");
            };
            let ValueType::Record(ref inner) = *matched_native_node
            else {
                panic!("nested record classifier");
            };
            assert!(
                inner
                    .keys()
                    .map(core::convert::AsRef::as_ref)
                    .eq(["x", "y"])
            );
            assert!(inner.values().all(|&ty| arena.value_type(ty).is_some_and(
                |held| matches!(*held, ValueType::Product(ref parts) if parts.is_empty())
            )));
        }
    }
    let Verdict::Synthesised { synthesised, .. } = report.judged()[9].verdict()
    else {
        panic!("the empty record has an exact empty classifier");
    };
    assert_eq!(
        arena.value_type(synthesised.produced().id()),
        arena.value_type(empty)
    );
    for position in [8_usize, 9] {
        assert!(matches!(
            crossed.readmitted()[position].outcome(),
            Outcome::Defined { .. }
        ));
    }
    assert!(crossed.audit().axioms().is_empty());
}

#[test]
fn term_indices_are_structural_in_both_checkers()
{
    let mut arena = CoreArena::new();
    let unit_type = arena.value_type_unit();
    let unit = arena.value_unit();
    let returns_unit = arena.comp_type_returner(unit_type);
    let function = arena.comp_type_arrow(unit_type, returns_unit);
    let function = arena.value_type_thunk(function);
    let kind = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let data = ConstantIndex::from(1_usize);
    let declaration = Declaration::data(
        data,
        DataSignature::new(vec![function], vec![vec![]], kind).into(),
        OriginToken::from(1_usize),
    );
    let returned = arena.computation_return(unit);
    let normal = arena.computation_lambda(returned);
    let normal = arena.value_thunk(normal);
    let variable = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let identity = arena.computation_return(variable);
    let identity = arena.computation_lambda(identity);
    let identity = arena.value_thunk(identity);
    let identity_definition = definition(ConstantIndex::from(0_usize), function, identity);
    let identity_reference = arena.value_constant(ConstantIndex::from(0_usize));
    let identity = arena.computation_force(identity_reference);
    let redex = arena.computation_application(identity, unit);
    let redex = arena.computation_lambda(redex);
    let redex = arena.value_thunk(redex);
    let copied_unit = arena.value_unit();
    let copied = arena.computation_return(copied_unit);
    let copied = arena.computation_lambda(copied);
    let copied = arena.value_thunk(copied);
    let reference = arena.value_constant(ConstantIndex::from(2_usize));
    let reference_copy = arena.value_constant(ConstantIndex::from(2_usize));
    let declared = arena.value_type_data(data, vec![normal]);
    let copied_type = arena.value_type_data(data, vec![copied]);
    let redex_type = arena.value_type_data(data, vec![redex]);
    let named_type = arena.value_type_data(data, vec![reference]);
    let named_copy_type = arena.value_type_data(data, vec![reference_copy]);
    let tag = ConstructorTag::from(0_usize);
    let copied_value = arena.value_constructor(copied_type, tag, vec![]);
    let redex_value = arena.value_constructor(redex_type, tag, vec![]);
    let named_value = arena.value_constructor(named_type, tag, vec![]);
    let named_copy_value = arena.value_constructor(named_copy_type, tag, vec![]);
    let (report, crossed) = run(&mut arena, &[
        identity_definition,
        declaration,
        definition(ConstantIndex::from(2_usize), function, normal),
        definition(ConstantIndex::from(3_usize), declared, copied_value),
        definition(ConstantIndex::from(4_usize), declared, redex_value),
        definition(ConstantIndex::from(5_usize), declared, named_value),
        definition(ConstantIndex::from(6_usize), named_type, named_copy_value),
    ]);
    for position in [0, 2, 3, 6] {
        assert!(
            matches!(report.judged()[position].verdict(), Verdict::Checked { .. }),
            "{:?}",
            report.judged()[position].verdict()
        );
        assert!(
            matches!(
                crossed.readmitted()[position].outcome(),
                Outcome::Defined { .. }
            ),
            "{:?}",
            crossed.readmitted()[position].outcome()
        );
    }
    assert_eq!(report.judged()[1].verdict(), Verdict::Data);
    for position in [4, 5] {
        assert!(matches!(
            report.judged()[position].verdict(),
            Verdict::Refused(CheckRefusal::TypeMismatch(_))
        ));
        assert!(matches!(
            crossed.readmitted()[position].outcome(),
            Outcome::Marked(CheckRefusal::TypeMismatch(_))
        ));
    }
}

#[test]
fn a_family_argument_written_as_a_call_converts_with_its_value_3579()
{
    use gandr_core_term::Summand;
    let mut arena = CoreArena::new();
    let unit_type = arena.value_type_unit();
    let unit = arena.value_unit();
    let truth = arena.value_type_sum(&[unit_type, unit_type]);
    let returns_truth = arena.comp_type_returner(truth);
    let asked = arena.comp_type_arrow(unit_type, returns_truth);
    let asked = arena.value_type_thunk(asked);
    let kind = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let data = ConstantIndex::from(1_usize);
    let declaration = Declaration::data(
        data,
        DataSignature::new(vec![truth], vec![vec![]], kind).into(),
        OriginToken::from(1_usize),
    );
    let yes = arena.value_injection(Summand::from(0_usize), unit);
    let no = arena.value_injection(Summand::from(1_usize), unit);
    // `fn (_) { return yes }`, the definition the call unfolds.
    let answered = arena.computation_return(yes);
    let answered = arena.computation_lambda(answered);
    let answered = arena.value_thunk(answered);
    let answer = arena.value_constant(ConstantIndex::from(0_usize));
    let answer = arena.computation_force(answer);
    let call = arena.computation_application(answer, unit);
    let call = arena.value_returned(call);
    let called_type = arena.value_type_data(data, vec![call]);
    let yes_type = arena.value_type_data(data, vec![yes]);
    let no_type = arena.value_type_data(data, vec![no]);
    let tag = ConstructorTag::from(0_usize);
    let called_value = arena.value_constructor(called_type, tag, vec![]);
    let (report, crossed) = run(&mut arena, &[
        definition(ConstantIndex::from(0_usize), asked, answered),
        declaration,
        definition(ConstantIndex::from(2_usize), yes_type, called_value),
        definition(ConstantIndex::from(3_usize), no_type, called_value),
    ]);
    assert!(
        matches!(report.judged()[2].verdict(), Verdict::Checked { .. }),
        "a call stands at the value it returns: {:?}",
        report.judged()[2].verdict()
    );
    assert!(
        matches!(crossed.readmitted()[2].outcome(), Outcome::Defined { .. }),
        "the kernel reads the call as its value: {:?}",
        crossed.readmitted()[2].outcome()
    );
    assert!(
        matches!(
            report.judged()[3].verdict(),
            Verdict::Refused(CheckRefusal::TypeMismatch(_))
        ),
        "a call is apart from a value it does not return: {:?}",
        report.judged()[3].verdict()
    );
    assert!(matches!(
        crossed.readmitted()[3].outcome(),
        Outcome::Marked(CheckRefusal::TypeMismatch(_))
    ));
}

#[test]
fn a_constructor_annotated_at_a_call_meets_its_stated_index_3627()
{
    use gandr_core_term::Summand;
    let mut arena = CoreArena::new();
    let unit_type = arena.value_type_unit();
    let unit = arena.value_unit();
    let truth = arena.value_type_sum(&[unit_type, unit_type]);
    let returns_truth = arena.comp_type_returner(truth);
    let asked = arena.comp_type_arrow(unit_type, returns_truth);
    let asked = arena.value_type_thunk(asked);
    let kind = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let yes = arena.value_injection(Summand::from(0_usize), unit);
    let no = arena.value_injection(Summand::from(1_usize), unit);
    // `fn (_) { return yes }` and `fn (_) { return no }`, the definitions the
    // calls unfold.
    let [answered, refuted] = [yes, no].map(|answer| {
        let returned = arena.computation_return(answer);
        let lambda = arena.computation_lambda(returned);
        arena.value_thunk(lambda)
    });
    let [call, call_no] = [0_usize, 4_usize].map(|position| {
        let answer = arena.value_constant(ConstantIndex::from(position));
        let answer = arena.computation_force(answer);
        let called = arena.computation_application(answer, unit);
        arena.value_returned(called)
    });
    // `I : Truth -> Type { Made : I(yes); }`: `Made` annotated at a call that
    // returns `yes` crosses at `I(yes)`, ascribed the call, as the kernel
    // compares a stated index with its annotation's as syntax. `Made` at a
    // call that returns `no` stands apart from its stated index.
    let indexed = ConstantIndex::from(1_usize);
    let family = Declaration::data(
        indexed,
        DataSignature::new(vec![], vec![vec![]], kind)
            .indexed(vec![truth], vec![vec![yes]])
            .into(),
        OriginToken::from(1_usize),
    );
    let tag = ConstructorTag::from(0_usize);
    let at_call = arena.value_type_data(indexed, vec![call]);
    let at_yes = arena.value_type_data(indexed, vec![yes]);
    let at_call_no = arena.value_type_data(indexed, vec![call_no]);
    let made_at_call = arena.value_constructor(at_call, tag, vec![]);
    let made_at_yes = arena.value_constructor(at_yes, tag, vec![]);
    let made_at_call_no = arena.value_constructor(at_call_no, tag, vec![]);
    let (report, crossed) = run(&mut arena, &[
        definition(ConstantIndex::from(0_usize), asked, answered),
        family,
        definition(ConstantIndex::from(2_usize), at_yes, made_at_call),
        definition(ConstantIndex::from(3_usize), at_call, made_at_yes),
        definition(ConstantIndex::from(4_usize), asked, refuted),
        definition(ConstantIndex::from(5_usize), at_call_no, made_at_call_no),
    ]);
    for position in [2_usize, 3_usize] {
        assert!(
            matches!(report.judged()[position].verdict(), Verdict::Checked { .. }),
            "a constructor at a call that computes its stated index checks: {:?}",
            report.judged()[position].verdict()
        );
        assert!(
            matches!(
                crossed.readmitted()[position].outcome(),
                Outcome::Defined { .. }
            ),
            "the kernel admits it: {:?}",
            crossed.readmitted()[position].outcome()
        );
    }
    assert!(
        matches!(
            report.judged()[5].verdict(),
            Verdict::Refused(CheckRefusal::TypeMismatch(_))
        ),
        "a constructor at a call that computes another index is refused: {:?}",
        report.judged()[5].verdict()
    );
    assert!(
        matches!(
            crossed.readmitted()[5].outcome(),
            Outcome::Marked(CheckRefusal::TypeMismatch(_))
        ),
        "{:?}",
        crossed.readmitted()[5].outcome()
    );
}

#[test]
fn a_constructor_field_written_as_a_call_meets_its_annotation_3625()
{
    let (zeroth, first) = (ConstructorTag::from(0_usize), ConstructorTag::from(1_usize));
    let mut arena = CoreArena::new();
    let kind = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let (natural, count) = (ConstantIndex::from(0_usize), ConstantIndex::from(2_usize));
    let nat = arena.value_type_data(natural, vec![]);
    let naturals = Declaration::data(
        natural,
        DataSignature::new(vec![], vec![vec![], vec![nat]], kind).into(),
        OriginToken::from(0_usize),
    );
    // `ident = fn (x) { return x }`, a pure definition to call.
    let returns_nat = arena.comp_type_returner(nat);
    let ident_type = arena.comp_type_arrow(nat, returns_nat);
    let ident_type = arena.value_type_thunk(ident_type);
    let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let ident = arena.computation_return(bound);
    let ident = arena.computation_lambda(ident);
    let ident = arena.value_thunk(ident);
    let called = |arena: &mut CoreArena, at: u32| {
        let argument = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(at));
        let head = arena.value_constant(ConstantIndex::from(1_usize));
        let head = arena.computation_force(head);
        arena.computation_application(head, argument)
    };
    // `Count : Nat -> Type { None : Count(Z); More : (n : Nat, c : Count(n))
    // --> Count(S(n)); }`: `More`'s count is read by its tail's type and by
    // its stated index.
    let zero = arena.value_constructor(nat, zeroth, vec![]);
    let under_one = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let counted = arena.value_type_data(count, vec![under_one]);
    let under_both = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
    let stated = arena.value_constructor(nat, first, vec![under_both]);
    let counts = Declaration::data(
        count,
        DataSignature::new(vec![], vec![vec![], vec![nat, counted]], kind)
            .indexed(vec![nat], vec![vec![zero], vec![stated]])
            .into(),
        OriginToken::from(2_usize),
    );
    // `more(m : Nat, c : Count(ident(m))) -> Count(S(ident(m))) { More(ident(m),
    // c) }`: the count is written as the call the types write.
    let in_tail = called(&mut arena, 0);
    let in_tail = arena.value_returned(in_tail);
    let tail_type = arena.value_type_data(count, vec![in_tail]);
    let in_result = called(&mut arena, 1);
    let in_result = arena.value_returned(in_result);
    let successor = arena.value_constructor(nat, first, vec![in_result]);
    let result_type = arena.value_type_data(count, vec![successor]);
    let returns = arena.comp_type_returner(result_type);
    let inner = arena.comp_type_pi(tail_type, returns);
    let outer = arena.comp_type_pi(nat, inner);
    let declared = arena.value_type_thunk(outer);
    let field = called(&mut arena, 1);
    let field = arena.value_nested(field);
    let tail = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let more = arena.value_constructor(result_type, first, vec![field, tail]);
    let body = arena.computation_return(more);
    let body = arena.computation_lambda(body);
    let body = arena.computation_lambda(body);
    let body = arena.value_thunk(body);
    let (report, crossed) = run(&mut arena, &[
        naturals,
        definition(ConstantIndex::from(1_usize), ident_type, ident),
        counts,
        definition(ConstantIndex::from(3_usize), declared, body),
    ]);
    assert!(
        matches!(report.judged()[3].verdict(), Verdict::Checked { .. }),
        "a field written as the call the types write meets them: {:?}",
        report.judged()[3].verdict()
    );
    assert!(
        matches!(crossed.readmitted()[3].outcome(), Outcome::Defined { .. }),
        "the kernel admits the field held in place: {:?}",
        crossed.readmitted()[3].outcome()
    );
}

/// `T : Type { Yes; No }` at position 0, and `B(t : T) : Type { Mk : B(t) }`
/// at position 1: a two-code universe and a family over it.
///
/// # Specification
/// trivial.
fn codes_and_boxes(arena: &mut CoreArena) -> (ValueTypeId, [Declaration; 2])
{
    let kind = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let codes = ConstantIndex::from(0_usize);
    let code = arena.value_type_data(codes, vec![]);
    let declarations = [
        Declaration::data(
            codes,
            DataSignature::new(vec![], vec![vec![], vec![]], kind).into(),
            OriginToken::from(0_usize),
        ),
        Declaration::data(
            ConstantIndex::from(1_usize),
            DataSignature::new(vec![code], vec![vec![]], kind).into(),
            OriginToken::from(1_usize),
        ),
    ];
    (code, declarations)
}

#[test]
fn an_arm_is_refined_by_its_index_equation_in_both_checkers_3483()
{
    let (yes_tag, mut arena) = (ConstructorTag::from(0_usize), CoreArena::new());
    let kind = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let (code, [codes, boxes]) = codes_and_boxes(&mut arena);
    let (boxed, indexed) = (ConstantIndex::from(1_usize), ConstantIndex::from(2_usize));
    let yes = arena.value_constructor(code, yes_tag, vec![]);
    // `I : T -> Type { Made : I(Yes); }`: an arm on `Made` binds the equation
    // `Path(T, Yes, t)` past its fields.
    let family = Declaration::data(
        indexed,
        DataSignature::new(vec![], vec![vec![]], kind)
            .indexed(vec![code], vec![vec![yes]])
            .into(),
        OriginToken::from(2_usize),
    );
    let variable = |arena: &mut CoreArena, at: u32| {
        arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(at))
    };
    let one_equation = gandr_kernel_term::EquationCount::from(1_usize);
    let no_fields = [0_usize].map(gandr_kernel_term::FieldCount::from).to_vec();
    // `pick(t : T, i : I(t)) -> I(t) { case i { Made => Made } }`: the arm's
    // goal reads `t`, and `Made` stands at `Yes`.
    let t_outer = variable(&mut arena, 0);
    let at_t = arena.value_type_data(indexed, vec![t_outer]);
    let t_under = variable(&mut arena, 1);
    let at_t_under = arena.value_type_data(indexed, vec![t_under]);
    let answers = arena.comp_type_returner(at_t_under);
    let picked_type = arena.comp_type_pi(at_t, answers);
    let picked_type = arena.comp_type_pi(code, picked_type);
    let picked_type = arena.value_type_thunk(picked_type);
    let at_yes = arena.value_type_data(indexed, vec![yes]);
    let made = arena.value_constructor(at_yes, yes_tag, vec![]);
    let returned = arena.computation_return(made);
    let arm = arena.computation_lambda(returned);
    let t_in_motive = variable(&mut arena, 2);
    let motive = arena.value_type_data(indexed, vec![t_in_motive]);
    let motive = arena.comp_type_returner(motive);
    let scrutinee = variable(&mut arena, 0);
    let case = arena.computation_data_case_with_equations(
        scrutinee,
        motive,
        (vec![arm], no_fields.clone()),
        one_equation,
    );
    let picked = arena.computation_lambda(case);
    let picked = arena.computation_lambda(picked);
    let picked = arena.value_thunk(picked);
    // `carry(t : T, i : I(t), w : B(t)) -> B(Yes) { case i { Made => w } }`:
    // the arm reads `w`, a binder after the scrutinee whose type reads `t`.
    let t_box = variable(&mut arena, 1);
    let box_at_t = arena.value_type_data(boxed, vec![t_box]);
    let box_at_yes = arena.value_type_data(boxed, vec![yes]);
    let carried_answer = arena.comp_type_returner(box_at_yes);
    let carried_type = arena.comp_type_pi(box_at_t, carried_answer);
    let carried_type = arena.comp_type_pi(at_t, carried_type);
    let carried_type = arena.comp_type_pi(code, carried_type);
    let carried_type = arena.value_type_thunk(carried_type);
    let w = variable(&mut arena, 1);
    let returned = arena.computation_return(w);
    let arm = arena.computation_lambda(returned);
    let scrutinee = variable(&mut arena, 1);
    let case = arena.computation_data_case_with_equations(
        scrutinee,
        carried_answer,
        (vec![arm], no_fields),
        one_equation,
    );
    let carried = arena.computation_lambda(case);
    let carried = arena.computation_lambda(carried);
    let carried = arena.computation_lambda(carried);
    let carried = arena.value_thunk(carried);
    let (report, crossed) = run(&mut arena, &[
        codes,
        boxes,
        family,
        definition(ConstantIndex::from(3_usize), picked_type, picked),
        definition(ConstantIndex::from(4_usize), carried_type, carried),
    ]);
    for (position, what) in [(3, "the arm's goal"), (4, "a binder after the scrutinee")] {
        assert!(
            matches!(report.judged()[position].verdict(), Verdict::Checked { .. }),
            "{what} is read at the arm's index: {:?}",
            report.judged()[position].verdict()
        );
        assert!(
            matches!(
                crossed.readmitted()[position].outcome(),
                Outcome::Defined { .. }
            ),
            "the kernel admits the arm refined for {what}: {:?}",
            crossed.readmitted()[position].outcome()
        );
    }
    assert!(crossed.audit().axioms().is_empty());
}

#[test]
fn a_binder_after_the_scrutinee_is_read_at_each_arm_in_both_checkers_3483()
{
    let (yes_tag, mut arena) = (ConstructorTag::from(0_usize), CoreArena::new());
    let (code, [codes, boxes]) = codes_and_boxes(&mut arena);
    let boxed = ConstantIndex::from(1_usize);
    let yes = arena.value_constructor(code, yes_tag, vec![]);
    let variable = |arena: &mut CoreArena, at: u32| {
        arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(at))
    };
    let no_fields = [0_usize, 0]
        .map(gandr_kernel_term::FieldCount::from)
        .to_vec();
    let u_outer = variable(&mut arena, 0);
    let box_at_u = arena.value_type_data(boxed, vec![u_outer]);
    // `same(u : T, v : B(u)) -> B(u) { case u { Yes => v, No => v } }`: each
    // arm reads `v` at its own code.
    let u_under = variable(&mut arena, 1);
    let box_under = arena.value_type_data(boxed, vec![u_under]);
    let answers = arena.comp_type_returner(box_under);
    let same_type = arena.comp_type_pi(box_at_u, answers);
    let same_type = arena.comp_type_pi(code, same_type);
    let same_type = arena.value_type_thunk(same_type);
    let scrutinee_bound = variable(&mut arena, 0);
    let motive = arena.value_type_data(boxed, vec![scrutinee_bound]);
    let motive = arena.comp_type_returner(motive);
    let v = variable(&mut arena, 0);
    let returned = arena.computation_return(v);
    let scrutinee = variable(&mut arena, 1);
    let case = arena.computation_data_case(
        scrutinee,
        motive,
        vec![returned, returned],
        no_fields.clone(),
    );
    let same = arena.computation_lambda(case);
    let same = arena.computation_lambda(same);
    let same = arena.value_thunk(same);
    // `back(u : T, v : B(u)) -> B(Yes) { case u { Yes => v, No => Mk } }`:
    // one arm reads `v`, at `Yes`.
    let box_at_yes = arena.value_type_data(boxed, vec![yes]);
    let answer = arena.comp_type_returner(box_at_yes);
    let back_type = arena.comp_type_pi(box_at_u, answer);
    let back_type = arena.comp_type_pi(code, back_type);
    let back_type = arena.value_type_thunk(back_type);
    let made = arena.value_constructor(box_at_yes, ConstructorTag::from(0_usize), vec![]);
    let made = arena.computation_return(made);
    let case = arena.computation_data_case(scrutinee, answer, vec![returned, made], no_fields);
    let back = arena.computation_lambda(case);
    let back = arena.computation_lambda(back);
    let back = arena.value_thunk(back);
    let (report, crossed) = run(&mut arena, &[
        codes,
        boxes,
        definition(ConstantIndex::from(2_usize), same_type, same),
        definition(ConstantIndex::from(3_usize), back_type, back),
    ]);
    for (position, what) in [(2, "each arm"), (3, "the one arm that reads it")] {
        assert!(
            matches!(report.judged()[position].verdict(), Verdict::Checked { .. }),
            "the binder after the scrutinee is read at {what}: {:?}",
            report.judged()[position].verdict()
        );
        assert!(
            matches!(
                crossed.readmitted()[position].outcome(),
                Outcome::Defined { .. }
            ),
            "the kernel admits the case refined at {what}: {:?}",
            crossed.readmitted()[position].outcome()
        );
    }
    assert!(crossed.audit().axioms().is_empty());
}

#[test]
fn a_refined_arm_elaborates_its_nested_call_where_it_is_written_3483()
{
    let (yes_tag, mut arena) = (ConstructorTag::from(0_usize), CoreArena::new());
    let kind = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let (code, [codes, boxes]) = codes_and_boxes(&mut arena);
    let (boxed, indexed) = (ConstantIndex::from(1_usize), ConstantIndex::from(2_usize));
    let yes = arena.value_constructor(code, yes_tag, vec![]);
    let family = Declaration::data(
        indexed,
        DataSignature::new(vec![], vec![vec![]], kind)
            .indexed(vec![code], vec![vec![yes]])
            .into(),
        OriginToken::from(2_usize),
    );
    let variable = |arena: &mut CoreArena, at: u32| {
        arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(at))
    };
    // `keep(x : B(Yes)) -> B(Yes) { x }`, a call to nest.
    let box_at_yes = arena.value_type_data(boxed, vec![yes]);
    let answer = arena.comp_type_returner(box_at_yes);
    let keep_type = arena.comp_type_arrow(box_at_yes, answer);
    let keep_type = arena.value_type_thunk(keep_type);
    let x = variable(&mut arena, 0);
    let keep = arena.computation_return(x);
    let keep = arena.computation_lambda(keep);
    let keep = arena.value_thunk(keep);
    // `wrap(t : T, i : I(t), w : B(t)) -> B(Yes) { case i { Made => keep(w) }
    // }`, the call nested in the returned value: the refined arm reads `w` at
    // `Yes`, and the run binds where the arm was written.
    let t_outer = variable(&mut arena, 0);
    let at_t = arena.value_type_data(indexed, vec![t_outer]);
    let t_box = variable(&mut arena, 1);
    let box_at_t = arena.value_type_data(boxed, vec![t_box]);
    let wrap_type = arena.comp_type_pi(box_at_t, answer);
    let wrap_type = arena.comp_type_pi(at_t, wrap_type);
    let wrap_type = arena.comp_type_pi(code, wrap_type);
    let wrap_type = arena.value_type_thunk(wrap_type);
    let head = arena.value_constant(ConstantIndex::from(3_usize));
    let head = arena.computation_force(head);
    let w = variable(&mut arena, 1);
    let call = arena.computation_application(head, w);
    let nested = arena.value_nested(call);
    let returned = arena.computation_return(nested);
    let arm = arena.computation_lambda(returned);
    let scrutinee = variable(&mut arena, 1);
    let case = arena.computation_data_case_with_equations(
        scrutinee,
        answer,
        (
            vec![arm],
            [0_usize].map(gandr_kernel_term::FieldCount::from).to_vec(),
        ),
        gandr_kernel_term::EquationCount::from(1_usize),
    );
    let wrap = arena.computation_lambda(case);
    let wrap = arena.computation_lambda(wrap);
    let wrap = arena.computation_lambda(wrap);
    let wrap = arena.value_thunk(wrap);
    let (report, crossed) = run(&mut arena, &[
        codes,
        boxes,
        family,
        definition(ConstantIndex::from(3_usize), keep_type, keep),
        definition(ConstantIndex::from(4_usize), wrap_type, wrap),
    ]);
    assert!(
        matches!(report.judged()[4].verdict(), Verdict::Checked { .. }),
        "the refined arm's nested call is decided where it is written: {:?}",
        report.judged()[4].verdict()
    );
    assert!(
        matches!(crossed.readmitted()[4].outcome(), Outcome::Defined { .. }),
        "the kernel admits the refined arm over the bound call: {:?}",
        crossed.readmitted()[4].outcome()
    );
}

/// `carry(t : T, i : I(t), w : B(t)) -> B(No) { case i { Made => w } }`: the
/// refined arm reads `w` at `B(Yes)`, which is refused against `B(No)`. The
/// failure names the written `w`, stands the copy of `w` on the lambda that
/// binds `w`, and keeps no frame of the transport, thunk or bind the
/// refinement minted.
#[test]
fn a_refusal_inside_a_refined_arm_names_the_written_term_3694()
{
    let (yes_tag, mut arena) = (ConstructorTag::from(0_usize), CoreArena::new());
    let kind = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let (code, [codes, boxes]) = codes_and_boxes(&mut arena);
    let (boxed, indexed) = (ConstantIndex::from(1_usize), ConstantIndex::from(2_usize));
    let yes = arena.value_constructor(code, yes_tag, vec![]);
    let no = arena.value_constructor(code, ConstructorTag::from(1_usize), vec![]);
    let family = Declaration::data(
        indexed,
        DataSignature::new(vec![], vec![vec![]], kind)
            .indexed(vec![code], vec![vec![yes]])
            .into(),
        OriginToken::from(2_usize),
    );
    let variable = |arena: &mut CoreArena, at: u32| {
        arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(at))
    };
    let t_outer = variable(&mut arena, 0);
    let at_t = arena.value_type_data(indexed, vec![t_outer]);
    let t_box = variable(&mut arena, 1);
    let box_at_t = arena.value_type_data(boxed, vec![t_box]);
    let box_at_no = arena.value_type_data(boxed, vec![no]);
    let answer = arena.comp_type_returner(box_at_no);
    let carry_type = arena.comp_type_pi(box_at_t, answer);
    let carry_type = arena.comp_type_pi(at_t, carry_type);
    let carry_type = arena.comp_type_pi(code, carry_type);
    let carry_type = arena.value_type_thunk(carry_type);
    let w = variable(&mut arena, 1);
    let returned = arena.computation_return(w);
    let arm = arena.computation_lambda(returned);
    let scrutinee = variable(&mut arena, 1);
    let case = arena.computation_data_case_with_equations(
        scrutinee,
        answer,
        (
            vec![arm],
            [0_usize].map(gandr_kernel_term::FieldCount::from).to_vec(),
        ),
        gandr_kernel_term::EquationCount::from(1_usize),
    );
    let binds_w = arena.computation_lambda(case);
    let carry = arena.computation_lambda(binds_w);
    let carry = arena.computation_lambda(carry);
    let carry = arena.value_thunk(carry);
    let constant = ConstantIndex::from(3_usize);
    let (report, _) = run(&mut arena, &[
        codes,
        boxes,
        family,
        definition(constant, carry_type, carry),
    ]);
    assert!(
        matches!(
            report.judged()[3].verdict(),
            Verdict::Refused(CheckRefusal::TypeMismatch(Mismatch::Value { at, .. })) if at == w
        ),
        "the mismatch names the written `w`, not its copy: {:?}",
        report.judged()[3].verdict()
    );
    let failure = &report.failures()[&constant];
    let roles: Vec<FrameRole> = failure.obligations().iter().map(Obligation::role).collect();
    for minted in [FrameRole::BindBound, FrameRole::TransportOperand] {
        assert!(
            !roles.contains(&minted),
            "no frame of the refinement's {minted:?} stands: {roles:?}"
        );
    }
    assert_eq!(
        roles
            .iter()
            .filter(|&&role| role == FrameRole::ThunkBody)
            .count(),
        1,
        "the definition's thunk stands, and the refinement's thunk does not: {roles:?}"
    );
    let at_w = |obligation: &&Obligation| {
        obligation.at() == CoreNode::Term(gandr_core_checker::TermNode::Computation(binds_w))
    };
    assert_eq!(
        failure.obligations().iter().filter(at_w).count(),
        2,
        "the lambda that binds `w` and the copy of `w` both stand on it: {:?}",
        failure.obligations()
    );
}

/// `same(u : T, v : B(u), w : Unit) -> Path(B(u), v, v)`, its `Yes` arm
/// `_ ← return unit; return here(v)` and its `No` arm `return here(v)`: the
/// case reads `v` at each arm through a copy, and the typed run reads each
/// written term of the `Yes` arm back in the arm's written context.
#[test]
fn a_refined_arm_types_its_written_terms_in_their_own_context_3483()
{
    let mut arena = CoreArena::new();
    let (code, [codes, boxes]) = codes_and_boxes(&mut arena);
    let boxed = ConstantIndex::from(1_usize);
    let variable = |arena: &mut CoreArena, at: u32| {
        arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(at))
    };
    let unit_type = arena.value_type_unit();
    let u_outer = variable(&mut arena, 0);
    let box_at_u = arena.value_type_data(boxed, vec![u_outer]);
    let u_result = variable(&mut arena, 2);
    let box_result = arena.value_type_data(boxed, vec![u_result]);
    let v_result = variable(&mut arena, 1);
    let result = arena.value_type_path(box_result, v_result, v_result);
    let answers = arena.comp_type_returner(result);
    let same_type = arena.comp_type_pi(unit_type, answers);
    let same_type = arena.comp_type_pi(box_at_u, same_type);
    let same_type = arena.comp_type_pi(code, same_type);
    let same_type = arena.value_type_thunk(same_type);
    // The motive under the scrutinee's binder: `Path(B(s), v, v)`.
    let scrutinised = variable(&mut arena, 0);
    let box_scrutinised = arena.value_type_data(boxed, vec![scrutinised]);
    let v_motive = variable(&mut arena, 2);
    let motive = arena.value_type_path(box_scrutinised, v_motive, v_motive);
    let motive = arena.comp_type_returner(motive);
    let unit = arena.value_unit();
    let first = arena.computation_return(unit);
    let v_under = variable(&mut arena, 2);
    let here_under = arena.value_here(v_under);
    let then = arena.computation_return(here_under);
    let on_yes = arena.computation_bind(first, then);
    let v_top = variable(&mut arena, 1);
    let here_top = arena.value_here(v_top);
    let on_no = arena.computation_return(here_top);
    let scrutinee = variable(&mut arena, 2);
    let no_fields = [0_usize, 0]
        .map(gandr_kernel_term::FieldCount::from)
        .to_vec();
    let case = arena.computation_data_case(scrutinee, motive, vec![on_yes, on_no], no_fields);
    let same = arena.computation_lambda(case);
    let same = arena.computation_lambda(same);
    let same = arena.computation_lambda(same);
    let same = arena.value_thunk(same);
    let constant = ConstantIndex::from(2_usize);
    let typed = gandr_core_checker::type_module(
        &mut CheckingContext::new(&mut arena, CheckBudget::DEFAULT),
        &[codes, boxes, definition(constant, same_type, same)],
    );
    assert!(
        !typed.refused().contains_key(&constant),
        "the case reads `v` at each arm: {:?}",
        typed.refused()
    );
    let typings = typed
        .typings()
        .get(&constant)
        .expect("the body is typed")
        .typings();
    let index_of = |at: ValueId| match arena.value(at) {
        Some(&gandr_core_term::Value::Variable { index, .. }) => Some(u32::from(index)),
        Some(_) | None => None,
    };
    // Under `u, v, w` and the bind's binder, `v` is the third binder out.
    let read = |term: ValueId| {
        typings
            .iter()
            .filter(|typing| typing.term == gandr_core_checker::TermNode::Value(term))
            .map(|typing| {
                let ends = match typing.ty {
                    gandr_core_checker::TypeNode::Value(ty) => match arena.value_type(ty) {
                        Some(&ValueType::Path { left, right, .. }) => {
                            Some((index_of(left), index_of(right)))
                        },
                        Some(_) | None => None,
                    },
                    gandr_core_checker::TypeNode::Computation(_) => None,
                };
                (usize::from(typing.depth), ends)
            })
            .collect::<Vec<_>>()
    };
    assert_eq!(
        read(here_under),
        [(4, Some((Some(2), Some(2))))],
        "the written path is typed between the written `v`s, at the arm's own depth"
    );
    let depths: Vec<usize> = read(v_under).iter().map(|&(depth, _)| depth).collect();
    assert!(
        !depths.is_empty() && depths.iter().all(|&depth| depth == 4),
        "the written `v` under the bind is typed as written, not as the copy: {depths:?}"
    );
    assert_eq!(
        read(here_top),
        [(3, Some((Some(1), Some(1))))],
        "the other arm's path reads the written `v` at the written depth"
    );
}

#[test]
fn a_staged_field_keeps_its_stage_across_its_equation_in_both_checkers_3631()
{
    let (yes_tag, mut arena) = (ConstructorTag::from(0_usize), CoreArena::new());
    let kind = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let (code, [codes, boxes]) = codes_and_boxes(&mut arena);
    let wrapped = ConstantIndex::from(2_usize);
    let yes = arena.value_constructor(code, yes_tag, vec![]);
    let no = arena.value_constructor(code, ConstructorTag::from(1_usize), vec![]);
    let variable = |arena: &mut CoreArena, at: u32| {
        arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(at))
    };
    // `E : T -> Type { Leaf : E(Yes); Wrap : (t : T, e : E(t)) --> E(t); Off
    // : E(No) }`: `Wrap` states its index as its first field.
    let under_one = variable(&mut arena, 0);
    let nested = arena.value_type_data(wrapped, vec![under_one]);
    let under_both = variable(&mut arena, 1);
    let family = Declaration::data(
        wrapped,
        DataSignature::new(vec![], vec![vec![], vec![code, nested], vec![]], kind)
            .indexed(vec![code], vec![vec![yes], vec![under_both], vec![no]])
            .into(),
        OriginToken::from(2_usize),
    );
    let fields = |counts: [usize; 3]| counts.map(gandr_kernel_term::FieldCount::from).to_vec();
    let one_equation = gandr_kernel_term::EquationCount::from(1_usize);
    let unit_type = arena.value_type_unit();
    let unit = arena.value_unit();
    let answer = arena.comp_type_returner(unit_type);
    let returned = arena.computation_return(unit);
    let bare = arena.computation_lambda(returned);
    let two_fields = arena.computation_lambda(bare);
    let two_fields = arena.computation_lambda(two_fields);
    // `fix f. λe. case e { Leaf ⇒ (); Wrap(t, e′) ⇒ f(e′); Off ⇒ () }` at
    // `E(Yes) → F Unit`: the stated side. The call reads `e′ : E(t)` at
    // `E(Yes)`, and it descends only if `e′` keeps its stage across `t = Yes`.
    let at_yes = arena.value_type_data(wrapped, vec![yes]);
    // Under `Wrap`'s arm: the equation 0, `e′` 1, `t` 2, `e` 3, `f` 4.
    let recursive = variable(&mut arena, 4);
    let forced = arena.computation_force(recursive);
    let field = variable(&mut arena, 1);
    let called = arena.computation_application(forced, field);
    let descending = arena.computation_lambda(called);
    let descending = arena.computation_lambda(descending);
    let descending = arena.computation_lambda(descending);
    let scrutinee = variable(&mut arena, 0);
    let case = arena.computation_data_case_with_equations(
        scrutinee,
        answer,
        (vec![bare, descending, bare], fields([0, 2, 0])),
        one_equation,
    );
    let lambda = arena.computation_lambda(case);
    let fixpoint = arena.computation_fixpoint(
        lambda,
        gandr_kernel_term::FixpointEvidence::StructuralDescent,
    );
    let dropped = arena.value_thunk(fixpoint);
    let dropped_type = arena.comp_type_arrow(at_yes, answer);
    let dropped_type = arena.value_type_thunk(dropped_type);
    // `fix g. λt. λw. λe. case e { Leaf ⇒ case w { Leaf ⇒ (); Wrap(u, w′) ⇒
    // g(u)(w′)(w′); Off ⇒ absurd }; Wrap(..) ⇒ (); Off ⇒ () }` at `(t : T) →
    // E(t) → E(t) → F Unit`, staged at `w`: the scrutinee side. The inner
    // case prunes `Off` only at `w : E(Yes)`, and its call descends only if
    // `w` keeps its stage across `Yes = t`.
    let t_outer = variable(&mut arena, 0);
    let at_t = arena.value_type_data(wrapped, vec![t_outer]);
    let t_under = variable(&mut arena, 1);
    let at_t_under = arena.value_type_data(wrapped, vec![t_under]);
    let walked_type = arena.comp_type_pi(at_t_under, answer);
    let walked_type = arena.comp_type_pi(at_t, walked_type);
    let walked_type = arena.comp_type_pi(code, walked_type);
    let walked_type = arena.value_type_thunk(walked_type);
    // Under the inner `Wrap` arm: the equation 0, `w′` 1, `u` 2, the outer
    // equation 3, `e` 4, `w` 5, `t` 6, `g` 7.
    let recursive = variable(&mut arena, 7);
    let forced = arena.computation_force(recursive);
    let index = variable(&mut arena, 2);
    let called = arena.computation_application(forced, index);
    let field = variable(&mut arena, 1);
    let called = arena.computation_application(called, field);
    let called = arena.computation_application(called, field);
    let inner_descending = arena.computation_lambda(called);
    let inner_descending = arena.computation_lambda(inner_descending);
    let inner_descending = arena.computation_lambda(inner_descending);
    let equation = variable(&mut arena, 0);
    let absurd = arena.computation_data_case(equation, answer, vec![], vec![]);
    let pruned = arena.computation_lambda(absurd);
    // Under the outer `Leaf` arm: the equation 0, `e` 1, `w` 2.
    let staged = variable(&mut arena, 2);
    let inner = arena.computation_data_case_with_equations(
        staged,
        answer,
        (vec![bare, inner_descending, pruned], fields([0, 2, 0])),
        one_equation,
    );
    let leaf = arena.computation_lambda(inner);
    let scrutinee = variable(&mut arena, 0);
    let case = arena.computation_data_case_with_equations(
        scrutinee,
        answer,
        (vec![leaf, two_fields, bare], fields([0, 2, 0])),
        one_equation,
    );
    let walked = arena.computation_lambda(case);
    let walked = arena.computation_lambda(walked);
    let walked = arena.computation_lambda(walked);
    let walked = arena.computation_fixpoint(walked, gandr_kernel_term::FixpointEvidence::Staged {
        position: gandr_kernel_term::StagedPosition::from(1_usize),
    });
    let walked = arena.value_thunk(walked);
    let (report, crossed) = run(&mut arena, &[
        codes,
        boxes,
        family,
        definition(ConstantIndex::from(3_usize), dropped_type, dropped),
        definition(ConstantIndex::from(4_usize), walked_type, walked),
    ]);
    for (position, what) in [(3, "the stated side"), (4, "the scrutinee side")] {
        assert!(
            matches!(report.judged()[position].verdict(), Verdict::Checked { .. }),
            "a staged binder keeps its stage across {what}'s equation: {:?}",
            report.judged()[position].verdict()
        );
        assert!(
            matches!(
                crossed.readmitted()[position].outcome(),
                Outcome::Defined { .. }
            ),
            "the kernel admits the transport that carries the stage on {what}: {:?}",
            crossed.readmitted()[position].outcome()
        );
    }
    assert!(crossed.audit().axioms().is_empty());
}

#[test]
fn a_stage_is_carried_across_a_set_and_not_along_a_loop_3631()
{
    let mut arena = CoreArena::new();
    let (mut declarations, circle) = one_loop(&mut arena);
    let kind = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let naturals = ConstantIndex::from(3_usize);
    let nat = arena.value_type_data(naturals, vec![]);
    declarations.push(Declaration::data(
        naturals,
        DataSignature::new(vec![], vec![vec![], vec![nat]], kind).into(),
        OriginToken::from(3_usize),
    ));
    let zero = arena.value_constructor(nat, ConstructorTag::from(0_usize), vec![]);
    let variable = |arena: &mut CoreArena, at: u32| {
        arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(at))
    };
    // `fix f. λn. λq. case n { Z ⇒ return Z; S(m) ⇒ f(transport(N, q,
    // m))(q) }` at `N → P → F N`, `P` a path in the naturals or the circle.
    let answer = arena.comp_type_returner(nat);
    let returned = arena.computation_return(zero);
    // Under the field: `m` 0, `q` 1, `n` 2, `f` 3.
    let q = variable(&mut arena, 1);
    let m = variable(&mut arena, 0);
    let moved = arena.computation_path_transport(nat, q, m);
    // Past the moved field: `m′` 0, `q` 2, `f` 4.
    let recursive = variable(&mut arena, 4);
    let forced = arena.computation_force(recursive);
    let field = variable(&mut arena, 0);
    let called = arena.computation_application(forced, field);
    let q = variable(&mut arena, 2);
    let called = arena.computation_application(called, q);
    let descending = arena.computation_bind(moved, called);
    let descending = arena.computation_lambda(descending);
    let scrutinee = variable(&mut arena, 1);
    let case = arena.computation_data_case(
        scrutinee,
        answer,
        vec![returned, descending],
        [0_usize, 1]
            .map(gandr_kernel_term::FieldCount::from)
            .to_vec(),
    );
    let body = arena.computation_lambda(case);
    let body = arena.computation_lambda(body);
    let fixpoint =
        arena.computation_fixpoint(body, gandr_kernel_term::FixpointEvidence::StructuralDescent);
    let value = arena.value_thunk(fixpoint);
    let along_set = arena.value_type_path(nat, zero, zero);
    let along_loop = arena.value_type_path(circle.carrier, circle.point, circle.point);
    for (position, path) in [(4_usize, along_set), (5, along_loop)] {
        let declared = arena.comp_type_arrow(path, answer);
        let declared = arena.comp_type_arrow(nat, declared);
        let declared = arena.value_type_thunk(declared);
        declarations.push(definition(ConstantIndex::from(position), declared, value));
    }
    // `C : S -> Type { Leaf : C(Base); Wrap : (s : S, c : C(s)) --> C(s) }`
    // and `fix g. λs. λw. λc. case c { Leaf ⇒ case w { Leaf ⇒ (); Wrap(s′, w′)
    // ⇒ g(s′)(w′)(w′) }; Wrap(..) ⇒ () }` at `(s : S) → C(s) → C(s) → F Unit`,
    // staged at `w`: the outer `Leaf` arm checks as written, so `w` stays
    // rather than move along a loop from `s` to `Base`.
    let circled = ConstantIndex::from(6_usize);
    let under_one = variable(&mut arena, 0);
    let nested = arena.value_type_data(circled, vec![under_one]);
    let under_both = variable(&mut arena, 1);
    declarations.push(Declaration::data(
        circled,
        DataSignature::new(vec![], vec![vec![], vec![circle.carrier, nested]], kind)
            .indexed(vec![circle.carrier], vec![vec![circle.point], vec![
                under_both,
            ]])
            .into(),
        OriginToken::from(6_usize),
    ));
    let unit_type = arena.value_type_unit();
    let unit = arena.value_unit();
    let finished = arena.comp_type_returner(unit_type);
    let returned = arena.computation_return(unit);
    let leaf = arena.computation_lambda(returned);
    let two_fields = arena.computation_lambda(leaf);
    let two_fields = arena.computation_lambda(two_fields);
    // Under the inner `Wrap` arm: the equation 0, `w′` 1, `s′` 2, the outer
    // equation 3, `c` 4, `w` 5, `s` 6, `g` 7.
    let recursive = variable(&mut arena, 7);
    let forced = arena.computation_force(recursive);
    let index = variable(&mut arena, 2);
    let called = arena.computation_application(forced, index);
    let field = variable(&mut arena, 1);
    let called = arena.computation_application(called, field);
    let called = arena.computation_application(called, field);
    let descending = arena.computation_lambda(called);
    let descending = arena.computation_lambda(descending);
    let descending = arena.computation_lambda(descending);
    let wrap_fields = [0_usize, 2]
        .map(gandr_kernel_term::FieldCount::from)
        .to_vec();
    let one_equation = gandr_kernel_term::EquationCount::from(1_usize);
    // Under the outer `Leaf` arm: the equation 0, `c` 1, `w` 2.
    let staged = variable(&mut arena, 2);
    let inner = arena.computation_data_case_with_equations(
        staged,
        finished,
        (vec![leaf, descending], wrap_fields.clone()),
        one_equation,
    );
    let outer_leaf = arena.computation_lambda(inner);
    let scrutinee = variable(&mut arena, 0);
    let case = arena.computation_data_case_with_equations(
        scrutinee,
        finished,
        (vec![outer_leaf, two_fields], wrap_fields),
        one_equation,
    );
    let walked = arena.computation_lambda(case);
    let walked = arena.computation_lambda(walked);
    let walked = arena.computation_lambda(walked);
    let walked = arena.computation_fixpoint(walked, gandr_kernel_term::FixpointEvidence::Staged {
        position: gandr_kernel_term::StagedPosition::from(1_usize),
    });
    let walked = arena.value_thunk(walked);
    let at_s = arena.value_type_data(circled, vec![under_one]);
    let at_s_under = arena.value_type_data(circled, vec![under_both]);
    let walked_type = arena.comp_type_pi(at_s_under, finished);
    let walked_type = arena.comp_type_pi(at_s, walked_type);
    let walked_type = arena.comp_type_pi(circle.carrier, walked_type);
    let walked_type = arena.value_type_thunk(walked_type);
    declarations.push(definition(
        ConstantIndex::from(7_usize),
        walked_type,
        walked,
    ));
    let (report, crossed) = run(&mut arena, &declarations);
    assert!(
        matches!(report.judged()[4].verdict(), Verdict::Checked { .. }),
        "a field moved along a path in a set keeps its stage: {:?}",
        report.judged()[4].verdict()
    );
    assert!(
        matches!(crossed.readmitted()[4].outcome(), Outcome::Defined { .. }),
        "the kernel carries the stage across the set: {:?}",
        crossed.readmitted()[4].outcome()
    );
    assert!(
        matches!(
            report.judged()[5].verdict(),
            Verdict::Refused(CheckRefusal::StageNotCarried { .. })
        ),
        "a field moved along a path in the circle carries no stage, by name: {:?}",
        report.judged()[5].verdict()
    );
    assert!(
        matches!(report.judged()[7].verdict(), Verdict::Checked { .. }),
        "a staged field indexed over the circle stays, and its arm checks as written: {:?}",
        report.judged()[7].verdict()
    );
    assert!(
        matches!(crossed.readmitted()[7].outcome(), Outcome::Defined { .. }),
        "the kernel admits the arm as written: {:?}",
        crossed.readmitted()[7].outcome()
    );
}

#[test]
fn empty_data_elimination_preserves_the_ambient_scope()
{
    let mut arena = CoreArena::new();
    let kind = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let constant = ConstantIndex::from(0_usize);
    let declaration = Declaration::data(
        constant,
        DataSignature::new(vec![], vec![], kind).into(),
        OriginToken::from(0_usize),
    );
    let datatype = arena.value_type_data(constant, vec![]);
    let unit_type = arena.value_type_unit();
    let motive = arena.comp_type_returner(unit_type);
    let impossible = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let case = arena.computation_data_case(impossible, motive, vec![], vec![]);
    let lambda = arena.computation_lambda(case);
    let body = arena.value_thunk(lambda);
    let arrow = arena.comp_type_pi(datatype, motive);
    let declared = arena.value_type_thunk(arrow);
    let (report, crossed) = run(&mut arena, &[
        declaration,
        definition(ConstantIndex::from(1_usize), declared, body),
    ]);
    assert!(
        matches!(report.judged()[1].verdict(), Verdict::Checked { .. }),
        "{:?}",
        report.judged()[1].verdict()
    );
    assert!(
        matches!(crossed.readmitted()[1].outcome(), Outcome::Defined { .. }),
        "{:?}",
        crossed.readmitted()[1].outcome()
    );
    assert!(crossed.audit().axioms().is_empty());
}

#[test]
fn native_signature_support_and_adoption()
{
    use alloc::sync::Arc;

    use gandr_core_checker::DeclarationContent;
    use gandr_core_checker::check_declaration;
    use gandr_core_checker::check_declaration_supported;
    let mut arena = CoreArena::new();
    let unit_type = arena.value_type_unit();
    let kind = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let constant = ConstantIndex::from(0_usize);
    let declaration = Declaration::data(
        constant,
        DataSignature::new(vec![], vec![vec![unit_type]], kind).into(),
        OriginToken::from(0_usize),
    );
    let datatype = arena.value_type_data(constant, vec![]);
    let unit = arena.value_unit();
    let constructor = arena.value_constructor(datatype, ConstructorTag::from(0_usize), vec![unit]);
    let use_site = definition(ConstantIndex::from(1_usize), datatype, constructor);
    let fresh = {
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        assert_eq!(check_declaration(&mut context, &declaration), Verdict::Data);
        check_declaration_supported(&mut context, &use_site)
    };
    let DeclarationContent::Data(ref signature) = *(declaration.content())
    else {
        panic!("native signature");
    };
    let adopted = {
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        context.adopt_data(constant, Arc::clone(signature)).unwrap();
        check_declaration_supported(&mut context, &use_site)
    };
    assert!(matches!(adopted.verdict(), Verdict::Checked { .. }));
    assert_eq!(fresh.verdict(), adopted.verdict());
    assert_eq!(fresh.support(), adopted.support());
    let [ref answer] = *(fresh.support().data_consulted())
    else {
        panic!("one nominal consultation despite repeated formation and introduction");
    };
    assert_eq!(answer.constant(), constant);
    assert_eq!(answer.signature(), Some(signature.as_ref()));

    let changed_declaration = Declaration::data(
        constant,
        DataSignature::new(vec![], vec![vec![]], kind).into(),
        OriginToken::from(0_usize),
    );
    let changed = {
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        assert_eq!(
            check_declaration(&mut context, &changed_declaration),
            Verdict::Data
        );
        check_declaration_supported(&mut context, &use_site)
    };
    assert_eq!(
        changed.verdict(),
        Verdict::Refused(CheckRefusal::ConstructorArity(constructor))
    );
    assert_ne!(
        fresh.support().data_consulted(),
        changed.support().data_consulted(),
        "an unchanged kind does not hide a changed constructor table"
    );
    let missing = check_declaration_supported(
        &mut CheckingContext::new(&mut arena, CheckBudget::DEFAULT),
        &use_site,
    );
    assert_eq!(
        missing.verdict(),
        Verdict::Refused(CheckRefusal::NotADataType(constant))
    );
    let [ref absent] = *(missing.support().data_consulted())
    else {
        panic!("the missing nominal declaration was consulted");
    };
    assert_eq!(absent.constant(), constant);
    assert!(absent.signature().is_none());
}

#[test]
fn tuple_projection_reads_each_component()
{
    use gandr_core_term::Component;
    let mut arena = CoreArena::new();
    let unit_type = arena.value_type_unit();
    let empty_type = arena.value_type_record(BTreeMap::new());
    let pair_type = arena.value_type_product(&[unit_type, unit_type]);
    let unit = arena.value_unit();
    let empty = arena.value_record(BTreeMap::new());
    let pair = arena.value_tuple(&[unit, unit]);
    let tuple = arena.value_tuple(&[unit, empty, pair]);
    let mut declarations = Vec::new();
    for (position, classifier) in [unit_type, empty_type, pair_type].into_iter().enumerate() {
        let projection = arena.computation_tuple_projection(tuple, Component::from(position));
        let body = arena.value_thunk(projection);
        let returner = arena.comp_type_returner(classifier);
        let declared = arena.value_type_thunk(returner);
        declarations.push(definition(ConstantIndex::from(position), declared, body));
    }
    let returner = arena.comp_type_returner(unit_type);
    let declared = arena.value_type_thunk(returner);
    let absent = arena.computation_tuple_projection(tuple, Component::from(3_usize));
    let absent_body = arena.value_thunk(absent);
    declarations.push(definition(
        ConstantIndex::from(3_usize),
        declared,
        absent_body,
    ));
    let second = arena.computation_tuple_projection(tuple, Component::from(1_usize));
    let second_body = arena.value_thunk(second);
    declarations.push(definition(
        ConstantIndex::from(4_usize),
        declared,
        second_body,
    ));
    let record = arena.value_record(BTreeMap::from([(
        FieldLabel::from(String::from("a")),
        unit,
    )]));
    let of_record = arena.computation_tuple_projection(record, Component::from(0_usize));
    let of_record_body = arena.value_thunk(of_record);
    declarations.push(definition(
        ConstantIndex::from(5_usize),
        declared,
        of_record_body,
    ));
    let (report, crossed) = run(&mut arena, &declarations);
    for position in 0 .. 3_usize {
        assert!(
            matches!(report.judged()[position].verdict(), Verdict::Checked { .. }),
            "{position}: {:?}",
            report.judged()[position].verdict()
        );
        assert!(
            matches!(
                crossed.readmitted()[position].outcome(),
                Outcome::Defined { .. }
            ),
            "{position}: {:?}",
            crossed.readmitted()[position].outcome()
        );
    }
    assert_eq!(
        report.judged()[3].verdict(),
        Verdict::Refused(CheckRefusal::AbsentTupleComponent(absent))
    );
    assert!(matches!(
        report.judged()[4].verdict(),
        Verdict::Refused(CheckRefusal::TypeMismatch(_))
    ));
    assert!(matches!(
        report.judged()[5].verdict(),
        Verdict::Refused(CheckRefusal::ShapeMismatch { .. })
    ));
    assert!(crossed.audit().axioms().is_empty());
}

/// A split crosses as the projection binds the kernel judges: reading the
/// last of a variable pair's components, which a wrong shift would read
/// from the first and the kernel would refuse; reading a closed triple's
/// last component; and splitting the unit into its body.
#[test]
fn a_split_crosses_as_its_projection_binds()
{
    use gandr_core_term::ComponentCount;
    let mut arena = CoreArena::new();
    let unit_type = arena.value_type_unit();
    let pair_type = arena.value_type_product(&[unit_type, unit_type]);
    let nested_type = arena.value_type_product(&[unit_type, pair_type]);
    let unit = arena.value_unit();
    let empty = arena.value_record(BTreeMap::new());
    let pair = arena.value_tuple(&[unit, unit]);
    let tuple = arena.value_tuple(&[unit, empty, pair]);
    let innermost = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let returns_last = arena.computation_return(innermost);
    let split_argument =
        arena.computation_split(innermost, ComponentCount::from(2_usize), returns_last);
    let lambda = arena.computation_lambda(split_argument);
    let returns_pair = arena.comp_type_returner(pair_type);
    let arrow = arena.comp_type_arrow(nested_type, returns_pair);
    let function_type = arena.value_type_thunk(arrow);
    let function = arena.value_thunk(lambda);
    let split_tuple = arena.computation_split(tuple, ComponentCount::from(3_usize), returns_last);
    let returns_unit = arena.computation_return(unit);
    let split_unit = arena.computation_split(unit, ComponentCount::default(), returns_unit);
    let declared_pair = arena.value_type_thunk(returns_pair);
    let returns_unit_type = arena.comp_type_returner(unit_type);
    let declared_unit = arena.value_type_thunk(returns_unit_type);
    let tuple_body = arena.value_thunk(split_tuple);
    let unit_body = arena.value_thunk(split_unit);
    let declarations = [
        definition(ConstantIndex::from(0_usize), function_type, function),
        definition(ConstantIndex::from(1_usize), declared_pair, tuple_body),
        definition(ConstantIndex::from(2_usize), declared_unit, unit_body),
    ];
    let (report, crossed) = run(&mut arena, &declarations);
    for position in 0 .. 3_usize {
        assert!(
            matches!(report.judged()[position].verdict(), Verdict::Checked { .. }),
            "{position}: {:?}",
            report.judged()[position].verdict()
        );
        assert!(
            matches!(
                crossed.readmitted()[position].outcome(),
                Outcome::Defined { .. }
            ),
            "{position}: {:?}",
            crossed.readmitted()[position].outcome()
        );
    }
    assert!(crossed.audit().axioms().is_empty());
}

#[test]
fn an_indexed_family_stands_at_its_indices_in_both_checkers()
{
    let (zeroth, first) = (ConstructorTag::from(0_usize), ConstructorTag::from(1_usize));
    let mut arena = CoreArena::new();
    let kind = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let (natural, count) = (ConstantIndex::from(0_usize), ConstantIndex::from(1_usize));
    let nat = arena.value_type_data(natural, vec![]);
    let naturals = Declaration::data(
        natural,
        DataSignature::new(vec![], vec![vec![], vec![nat]], kind).into(),
        OriginToken::from(0_usize),
    );
    // `Count : Nat -> Type { None : Count(Z); More : (n : Nat, c : Count(n))
    // --> Count(S(n)); }`: `n` is the variable 0 under the first field and 1
    // under both.
    let zero = arena.value_constructor(nat, zeroth, vec![]);
    let under_one = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let counted = arena.value_type_data(count, vec![under_one]);
    let under_both = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
    let stated = arena.value_constructor(nat, first, vec![under_both]);
    let counts = Declaration::data(
        count,
        DataSignature::new(vec![], vec![vec![], vec![nat, counted]], kind)
            .indexed(vec![nat], vec![vec![zero], vec![stated]])
            .into(),
        OriginToken::from(1_usize),
    );
    let one = arena.value_constructor(nat, first, vec![zero]);
    let two = arena.value_constructor(nat, first, vec![one]);
    let at_zero = arena.value_type_data(count, vec![zero]);
    let at_one = arena.value_type_data(count, vec![one]);
    let at_two = arena.value_type_data(count, vec![two]);
    let none = arena.value_constructor(at_zero, zeroth, vec![]);
    let more = arena.value_constructor(at_one, first, vec![zero, none]);
    let overstated = arena.value_constructor(at_two, first, vec![zero, none]);
    let answer = arena.comp_type_returner(nat);
    let returned = arena.computation_return(zero);
    // Each branch binds, past its fields, its equation at the one index.
    let bare = arena.computation_lambda(returned);
    let inner = arena.computation_lambda(returned);
    let middle = arena.computation_lambda(inner);
    let both = arena.computation_lambda(middle);
    let arities = [0_usize, 2]
        .map(gandr_kernel_term::FieldCount::from)
        .to_vec();
    let one_equation = gandr_kernel_term::EquationCount::from(1_usize);
    let case = arena.computation_data_case_with_equations(
        more,
        answer,
        (vec![bare, both], arities.clone()),
        one_equation,
    );
    let cased = arena.value_thunk(case);
    let thunked = arena.value_type_thunk(answer);
    // The same case with `None` pruned: its equation runs from `Z` to the
    // scrutinee's `S(Z)`, apart, so its branch is the case of no branches on
    // it.
    let equation = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let absurd = arena.computation_data_case(equation, answer, vec![], vec![]);
    let pruned_branch = arena.computation_lambda(absurd);
    let pruned = arena.computation_data_case_with_equations(
        more,
        answer,
        (vec![pruned_branch, both], arities),
        one_equation,
    );
    let pruned = arena.value_thunk(pruned);
    // `Pairs (a : Type) : Nat -> Nat -> Type { Mk : Pairs(a, Z, Z); }`: a
    // parameter before two indices.
    let paired = ConstantIndex::from(5_usize);
    let pairs = Declaration::data(
        paired,
        DataSignature::new(vec![kind], vec![vec![]], kind)
            .indexed(vec![nat, nat], vec![vec![zero, zero]])
            .into(),
        OriginToken::from(5_usize),
    );
    let code = arena.value_quote(nat);
    let at_zeros = arena.value_type_data(paired, vec![code, zero, zero]);
    let made = arena.value_constructor(at_zeros, zeroth, vec![]);
    let declarations = [
        naturals,
        counts,
        definition(ConstantIndex::from(2_usize), at_one, more),
        definition(ConstantIndex::from(3_usize), at_two, overstated),
        definition(ConstantIndex::from(4_usize), thunked, cased),
        pairs,
        definition(ConstantIndex::from(6_usize), at_zeros, made),
        definition(ConstantIndex::from(7_usize), thunked, pruned),
    ];
    let (report, crossed) = run(&mut arena, &declarations);
    assert_eq!(report.judged()[1].verdict(), Verdict::Data);
    assert!(
        matches!(report.judged()[2].verdict(), Verdict::Checked { .. }),
        "`More(Z, None)` stands at one: {:?}",
        report.judged()[2].verdict()
    );
    assert!(
        matches!(
            report.judged()[3].verdict(),
            Verdict::Refused(CheckRefusal::TypeMismatch(_))
        ),
        "`More(Z, None)` stands at no two: {:?}",
        report.judged()[3].verdict()
    );
    assert!(
        matches!(report.judged()[4].verdict(), Verdict::Checked { .. }),
        "a case on a count checks each constructor's branch at its own fields: {:?}",
        report.judged()[4].verdict()
    );
    assert!(
        matches!(crossed.readmitted()[4].outcome(), Outcome::Defined { .. }),
        "and the kernel admits the case: {:?}",
        crossed.readmitted()[4].outcome()
    );
    assert!(
        matches!(crossed.readmitted()[1].outcome(), Outcome::Data { .. }),
        "{:?}",
        crossed.readmitted()[1].outcome()
    );
    assert!(
        matches!(crossed.readmitted()[2].outcome(), Outcome::Defined { .. }),
        "the kernel admits the value at its stated index: {:?}",
        crossed.readmitted()[2].outcome()
    );
    assert!(crossed.audit().axioms().is_empty());
    assert!(
        matches!(report.judged()[6].verdict(), Verdict::Checked { .. }),
        "`Mk` stands at its family's parameter and both its indices: {:?}",
        report.judged()[6].verdict()
    );
    assert!(
        matches!(crossed.readmitted()[6].outcome(), Outcome::Defined { .. }),
        "and the kernel admits it there: {:?}",
        crossed.readmitted()[6].outcome()
    );
    assert!(
        matches!(report.judged()[7].verdict(), Verdict::Checked { .. }),
        "a case on a count one high prunes `None`, whose index is apart: {:?}",
        report.judged()[7].verdict()
    );
    assert!(
        matches!(crossed.readmitted()[7].outcome(), Outcome::Defined { .. }),
        "and the kernel admits the pruned case: {:?}",
        crossed.readmitted()[7].outcome()
    );
    let family = gandr_kernel_term::StructuredName::from(vec![
        gandr_kernel_term::NameSegment::from_text(String::from("Count")).unwrap(),
    ]);
    let artifact =
        gandr_kernel_term::decode(crossed.export(BTreeMap::from([(count, family)])).as_image())
            .unwrap();
    let gandr_kernel_term::DeclarationContent::Data {
        ref indices,
        ref results,
        ..
    } = *artifact.declarations()[1].declaration().content()
    else {
        panic!("the family crosses as data");
    };
    assert_eq!(
        (
            indices.len(),
            results.iter().map(Vec::len).collect::<Vec<_>>()
        ),
        (1_usize, vec![1_usize, 1]),
        "the family crosses with its index and each constructor's"
    );
}

/// A constructor at a type a definition computes checks at the family the
/// definition returns, and the kernel admits it (#3570).
#[test]
fn a_constructor_at_a_computed_type_checks_at_its_family_3570()
{
    let mut arena = CoreArena::new();
    let unit_type = arena.value_type_unit();
    let unit = arena.value_unit();
    let kind = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let boxes = ConstantIndex::from(0_usize);
    let box_type = arena.value_type_data(boxes, vec![]);
    let code = arena.value_quote(box_type);
    let boxed = arena.value_constant(ConstantIndex::from(1_usize));
    let computed = arena.value_type_element(boxed, Level::zero());
    let made = arena.value_constructor(computed, ConstructorTag::from(0_usize), vec![unit]);
    let (report, crossed) = run(&mut arena, &[
        Declaration::data(
            boxes,
            DataSignature::new(vec![], vec![vec![unit_type]], kind).into(),
            OriginToken::from(0_usize),
        ),
        definition(ConstantIndex::from(1_usize), kind, code),
        definition(ConstantIndex::from(2_usize), computed, made),
    ]);
    assert!(
        matches!(report.judged()[2].verdict(), Verdict::Checked { .. }),
        "the constructor reads the computed type at the family it unfolds to: {:?}",
        report.judged()[2].verdict()
    );
    assert!(
        matches!(crossed.readmitted()[2].outcome(), Outcome::Defined { .. }),
        "and the kernel admits it: {:?}",
        crossed.readmitted()[2].outcome()
    );
}
