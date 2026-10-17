use alloc::string::String;
use alloc::vec;

use gandr_core_term::CertificateEquality;
use gandr_core_term::Computation;
use gandr_core_term::CoreArena;
use gandr_core_term::DefinitionalEnvironment;
use gandr_core_term::ValueId;
use gandr_core_term::Zone;
use gandr_core_term::equal_certificate_syntax;
use gandr_core_term::fill_hole;
use gandr_core_term::hole::HoleId;
use gandr_core_term::hole::MarkIndex;
use gandr_core_term::hole::TermId;
use gandr_core_term::pattern::BranchStatus;
use gandr_core_term::pattern::Pattern;
use gandr_core_term::pattern::Patterns;
use gandr_kernel_check_memo::NullMemo;
use gandr_kernel_conversion_trace::NullSink;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Side;
use gandr_kernel_term::StringLiteral;

use super::ArmIndex;
use super::Matched;
use super::Selection;
use super::fill_and_resume;
use super::match_pattern;
use super::select_arm;
use crate::arena::DomainArena;
use crate::closure::ValueBody;
use crate::conv::Deferral;
use crate::conv::Settlement;
use crate::conv::convert_values;
use crate::domain::DomainComp;
use crate::domain::DomainValue;
use crate::domain::Glued;
use crate::domain::NeutralHead;
use crate::domain::Suspended;
use crate::eval::Definitions;
use crate::eval::Fuel;
use crate::eval::LoweredChain;
use crate::eval::eval_computation;
use crate::eval::eval_value;
use crate::machine::DeclineReason;
use crate::machine::MachineSettings;
use crate::machine::MachineVerdict;
use crate::machine::Problem;
use crate::machine::decide;
use crate::readback::ReadbackMode;
use crate::readback::readback_computation;
use crate::readback::readback_value;

/// A budget far above the step count any fixture below needs.
///
/// # Specification
/// trivial.
fn ample() -> Fuel
{
    Fuel::from(100_000_u32)
}

/// The text literal `five`.
///
/// # Specification
/// trivial.
fn literal_five(core: &mut CoreArena) -> ValueId
{
    core.value_literal(Literal::Text(StringLiteral::new(String::from("five"))))
}

/// The text literal `six`.
///
/// # Specification
/// trivial.
fn literal_six(core: &mut CoreArena) -> ValueId
{
    core.value_literal(Literal::Text(StringLiteral::new(String::from("six"))))
}

/// The variable at the innermost binder.
///
/// # Specification
/// trivial.
fn innermost(core: &mut CoreArena) -> ValueId
{
    core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32))
}

#[test]
fn a_hole_evaluates_to_a_neutral_carrying_its_environment()
{
    let mut core = CoreArena::new();
    let five = literal_five(&mut core);
    let hole = HoleId::from(0_u32);
    let standing = core.value_hole(hole);
    let returned = core.computation_return(standing);
    let lambda = core.computation_lambda(returned);
    let applied = core.computation_application(lambda, five);
    let chain = LoweredChain::new();
    let environment = DefinitionalEnvironment::new();
    let definitions = Definitions::new(&chain, &environment, environment.root());
    let mut domain = DomainArena::new();

    let evaluated = eval_computation(&core, &mut domain, definitions, ample(), applied)
        .expect("a hole does not stop evaluation");
    let Some(&DomainComp::Return { value, .. }) = domain.computation(evaluated)
    else {
        panic!("the redex fires around the hole and returns");
    };
    let Some(&DomainValue::Neutral { neutral, .. }) = domain.value(value)
    else {
        panic!("the hole stands as a neutral");
    };
    let held = domain.neutral(neutral).expect("the neutral resolves");
    let NeutralHead::Hole {
        hole: named,
        closure: Suspended::Value(closure),
    } = held.head()
    else {
        panic!("the hole is the neutral's head, in value position");
    };
    assert_eq!(named, hole);
    assert!(held.spine().is_empty(), "nothing eliminated the hole");
    let closure = domain.value_closure(closure).expect("the closure resolves");
    assert_eq!(
        closure.body(),
        ValueBody::Source(standing),
        "the closure suspends the hole itself"
    );
    let bound = closure
        .environment()
        .lookup(Zone::Intuitionistic, DeBruijnIndex::from(0_u32))
        .expect("the argument the hole was met under is in its environment");
    assert!(
        matches!(domain.value(bound), Some(&DomainValue::Literal { literal, .. }) if literal == five),
        "the environment binds the argument"
    );

    let read = readback_computation(
        &mut core,
        &mut domain,
        definitions,
        ReadbackMode::Unfolding,
        ample(),
        evaluated,
    )
    .expect("an indeterminate result reads back");
    assert!(
        matches!(core.computation(read), Some(&Computation::Return(read_hole)) if read_hole == standing),
        "a hole reads back as itself"
    );
}

#[test]
fn a_computation_hole_keeps_the_eliminations_that_could_not_fire()
{
    let mut core = CoreArena::new();
    let five = literal_five(&mut core);
    let hole = HoleId::from(1_u32);
    let head = core.computation_hole(hole);
    let applied = core.computation_application(head, five);
    let chain = LoweredChain::new();
    let environment = DefinitionalEnvironment::new();
    let definitions = Definitions::new(&chain, &environment, environment.root());
    let mut domain = DomainArena::new();

    let evaluated = eval_computation(&core, &mut domain, definitions, ample(), applied)
        .expect("an applied hole evaluates");
    let Some(&DomainComp::Neutral { neutral, .. }) = domain.computation(evaluated)
    else {
        panic!("an applied hole is stuck");
    };
    let held = domain.neutral(neutral).expect("the neutral resolves");
    assert!(
        matches!(
            held.head(),
            NeutralHead::Hole { hole: named, closure: Suspended::Computation(_) } if named == hole
        ),
        "the hole is the head, in computation position"
    );
    assert_eq!(held.spine().len(), 1, "the application waits on the hole");

    let read = readback_computation(
        &mut core,
        &mut domain,
        definitions,
        ReadbackMode::Unfolding,
        ample(),
        evaluated,
    )
    .expect("a stuck application reads back");
    let Some(&Computation::Application(read_head, argument)) = core.computation(read)
    else {
        panic!("the elimination folds back over the hole");
    };
    assert_eq!(core.computation(read_head), Some(&Computation::Hole(hole)));
    assert_eq!(
        equal_certificate_syntax(&core, argument, five),
        CertificateEquality::Equal
    );

    let body = returned_innermost(&mut core);
    let filling = core.computation_lambda(body);
    let (filled, _) = fill_and_resume(
        &mut core,
        &mut domain,
        definitions,
        ample(),
        Glued::Computation(evaluated),
        hole,
        TermId::Computation(filling),
    )
    .expect("a computation hole fills");
    let Glued::Computation(filled) = filled
    else {
        panic!("a computation result stays a computation");
    };
    let Some(&DomainComp::Return { value, .. }) = domain.computation(filled)
    else {
        panic!("the application fires once its head is a lambda");
    };
    assert!(
        matches!(domain.value(value), Some(&DomainValue::Literal { .. })),
        "and returns its argument"
    );
}

/// A return of the variable at the innermost binder.
///
/// # Specification
/// trivial.
fn returned_innermost(core: &mut CoreArena) -> gandr_core_term::ComputationId
{
    let occurrence = innermost(core);
    core.computation_return(occurrence)
}

#[test]
fn a_mark_reads_back_through_its_environment()
{
    let mut core = CoreArena::new();
    let five = literal_five(&mut core);
    let occurrence = innermost(&mut core);
    let mark = MarkIndex::from(0_u32);
    let marked = core.value_mark(mark, occurrence);
    let returned = core.computation_return(marked);
    let lambda = core.computation_lambda(returned);
    let applied = core.computation_application(lambda, five);
    let closed = core.value_mark(mark, five);
    let chain = LoweredChain::new();
    let environment = DefinitionalEnvironment::new();
    let definitions = Definitions::new(&chain, &environment, environment.root());
    let mut domain = DomainArena::new();

    let evaluated = eval_computation(&core, &mut domain, definitions, ample(), applied)
        .expect("a mark does not stop evaluation");
    let read = readback_computation(
        &mut core,
        &mut domain,
        definitions,
        ReadbackMode::Unfolding,
        ample(),
        evaluated,
    )
    .expect("a marked result reads back");
    let Some(&Computation::Return(read_mark)) = core.computation(read)
    else {
        panic!("the redex fires around the mark");
    };
    assert_eq!(
        equal_certificate_syntax(&core, read_mark, closed),
        CertificateEquality::Equal,
        "the mark's body reads the argument its environment binds"
    );
    assert_ne!(read_mark, marked, "a substituted mark is a new term");

    let alone = eval_value(&core, &mut domain, definitions, ample(), closed)
        .expect("a closed mark evaluates");
    let read_alone = readback_value(
        &mut core,
        &mut domain,
        definitions,
        ReadbackMode::Unfolding,
        ample(),
        alone,
    )
    .expect("a closed mark reads back");
    assert_eq!(read_alone, closed, "a mark met in no environment is itself");
}

#[test]
fn a_comparison_that_meets_a_hole_declines()
{
    let mut core = CoreArena::new();
    let five = literal_five(&mut core);
    let six = literal_six(&mut core);
    let hole = core.value_hole(HoleId::from(0_u32));
    let other = core.value_hole(HoleId::from(0_u32));
    let left_pair = core.value_tuple(&[hole, five]);
    let right_pair = core.value_tuple(&[other, six]);
    let chain = LoweredChain::new();
    let environment = DefinitionalEnvironment::new();
    let definitions = Definitions::new(&chain, &environment, environment.root());
    let mut domain = DomainArena::new();
    let mut eval =
        |term| eval_value(&core, &mut domain, definitions, ample(), term).expect("closed values");
    let (hole, other, five, left_pair, right_pair) = (
        eval(hole),
        eval(other),
        eval(five),
        eval(left_pair),
        eval(right_pair),
    );

    assert_eq!(
        convert_values(&core, &domain, hole, five),
        Ok(Settlement::Deferred(Deferral::Indeterminate)),
        "a hole against a literal is not apart: a fill may write the literal"
    );
    assert_eq!(
        convert_values(&core, &domain, hole, other),
        Ok(Settlement::Deferred(Deferral::Indeterminate)),
        "two occurrences of one hole may still be filled apart"
    );
    let mut decided = |left, right| {
        decide::<NullSink, NullMemo>(
            &core,
            &mut domain,
            definitions,
            MachineSettings::default(),
            Problem::values(left, right),
            &mut NullSink,
        )
        .expect("the machine answers")
        .verdict()
    };
    assert_eq!(
        decided(hole, five),
        MachineVerdict::Declined(DeclineReason::Indeterminate),
        "the machine declines rather than refuting"
    );
    assert_eq!(
        decided(hole, other),
        MachineVerdict::Declined(DeclineReason::Indeterminate)
    );
    assert_eq!(
        decided(left_pair, right_pair),
        MachineVerdict::NotConvertible,
        "a difference beside the hole refutes whatever the fill"
    );
    assert_eq!(
        decided(hole, hole),
        MachineVerdict::Convertible,
        "one node is itself"
    );
}

#[test]
fn filling_resumes_where_the_hole_stood()
{
    let mut core = CoreArena::new();
    let five = literal_five(&mut core);
    let hole = HoleId::from(0_u32);
    let standing = core.value_hole(hole);
    let forced = core.computation_force(standing);
    let lambda = core.computation_lambda(forced);
    let returned = core.computation_return(five);
    let thunk = core.value_thunk(returned);
    let program = core.computation_application(lambda, thunk);
    let filling = innermost(&mut core);
    let chain = LoweredChain::new();
    let environment = DefinitionalEnvironment::new();
    let definitions = Definitions::new(&chain, &environment, environment.root());
    let mut domain = DomainArena::new();

    let evaluated = eval_computation(&core, &mut domain, definitions, ample(), program)
        .expect("the program runs to the hole");
    assert!(
        matches!(
            domain.computation(evaluated),
            Some(DomainComp::Neutral { .. })
        ),
        "the force is stuck on the hole"
    );
    let (filled, _) = fill_and_resume(
        &mut core,
        &mut domain,
        definitions,
        ample(),
        Glued::Computation(evaluated),
        hole,
        TermId::Value(filling),
    )
    .expect("the fill resumes");
    let Glued::Computation(filled) = filled
    else {
        panic!("a computation result stays a computation");
    };
    let resumed = readback_computation(
        &mut core,
        &mut domain,
        definitions,
        ReadbackMode::Unfolding,
        ample(),
        filled,
    )
    .expect("the resumed result reads back");

    let TermId::Computation(written) = fill_hole(
        &mut core,
        TermId::Computation(program),
        hole,
        TermId::Value(filling),
    )
    else {
        panic!("filling a computation leaves a computation");
    };
    let direct = eval_computation(&core, &mut domain, definitions, ample(), written)
        .expect("the filled program runs");
    let expected = readback_computation(
        &mut core,
        &mut domain,
        definitions,
        ReadbackMode::Unfolding,
        ample(),
        direct,
    )
    .expect("the filled program's result reads back");
    let (Some(&Computation::Return(resumed)), Some(&Computation::Return(expected))) =
        (core.computation(resumed), core.computation(expected))
    else {
        panic!("both force the bound thunk and return");
    };
    assert_eq!(
        equal_certificate_syntax(&core, resumed, expected),
        CertificateEquality::Equal,
        "filling the result agrees with running the filled program"
    );
    assert_eq!(
        equal_certificate_syntax(&core, resumed, five),
        CertificateEquality::Equal,
        "and both return what the thunk the filling reads returns"
    );
}

#[test]
fn a_fill_leaves_other_holes_standing()
{
    let mut core = CoreArena::new();
    let five = literal_five(&mut core);
    let first = HoleId::from(0_u32);
    let second = HoleId::from(1_u32);
    let written = core.value_hole(first);
    let standing = core.value_hole(second);
    let pair = core.value_tuple(&[written, standing]);
    let returned = core.computation_return(pair);
    let lambda = core.computation_lambda(returned);
    let program = core.computation_application(lambda, five);
    let filling = innermost(&mut core);
    let chain = LoweredChain::new();
    let environment = DefinitionalEnvironment::new();
    let definitions = Definitions::new(&chain, &environment, environment.root());
    let mut domain = DomainArena::new();

    let evaluated = eval_computation(&core, &mut domain, definitions, ample(), program)
        .expect("the program runs");
    let (filled, _) = fill_and_resume(
        &mut core,
        &mut domain,
        definitions,
        ample(),
        Glued::Computation(evaluated),
        first,
        TermId::Value(filling),
    )
    .expect("the fill resumes");
    let Glued::Computation(filled) = filled
    else {
        panic!("a computation result stays a computation");
    };
    let read = readback_computation(
        &mut core,
        &mut domain,
        definitions,
        ReadbackMode::Unfolding,
        ample(),
        filled,
    )
    .expect("the filled result reads back");
    let expected_pair = core.value_tuple(&[five, standing]);
    let Some(&Computation::Return(read_pair)) = core.computation(read)
    else {
        panic!("the result still returns");
    };
    assert_eq!(
        equal_certificate_syntax(&core, read_pair, expected_pair),
        CertificateEquality::Equal,
        "the written hole reads the bound argument and the other stands"
    );
}

#[test]
fn a_match_over_a_hole_answers_per_arm()
{
    let mut core = CoreArena::new();
    let three = Literal::Text(StringLiteral::new(String::from("three")));
    let hole = core.value_hole(HoleId::from(0_u32));
    let injected = core.value_injection(Side::Left.into(), hole);
    let chain = LoweredChain::new();
    let environment = DefinitionalEnvironment::new();
    let definitions = Definitions::new(&chain, &environment, environment.root());
    let mut domain = DomainArena::new();
    let scrutinee = eval_value(&core, &mut domain, definitions, ample(), injected)
        .expect("an injected hole evaluates");

    let mut patterns = Patterns::new();
    let wildcard = patterns.mint(Pattern::Wildcard);
    let literal = patterns.mint(Pattern::Literal(three));
    let pattern_hole = patterns.mint(Pattern::Hole(HoleId::from(7_u32)));
    let right = patterns.mint(Pattern::Injection(Side::Right, wildcard));
    let left_literal = patterns.mint(Pattern::Injection(Side::Left, literal));
    let left_any = patterns.mint(Pattern::Injection(Side::Left, wildcard));
    let pair = patterns.mint(Pattern::Pair(wildcard, wildcard));

    let status = |arm| {
        match_pattern(&core, &domain, &patterns, arm, scrutinee)
            .expect("the arm classifies")
            .status()
    };
    assert_eq!(status(right), BranchStatus::Refuted, "the side is known");
    assert_eq!(
        status(left_literal),
        BranchStatus::Possibly,
        "the hole inside decides the literal"
    );
    assert_eq!(
        status(left_any),
        BranchStatus::Satisfied,
        "a wildcard decides nothing"
    );
    assert_eq!(
        status(pattern_hole),
        BranchStatus::Possibly,
        "a pattern hole decides itself"
    );
    assert_eq!(
        match_pattern(&core, &domain, &patterns, pair, scrutinee),
        Err(super::MatchFault::Mismatched),
        "a pair pattern cannot classify an injection"
    );
    assert_eq!(
        select_arm(
            &core,
            &domain,
            &patterns,
            &[right, left_literal, left_any],
            scrutinee
        ),
        Ok(Selection::Indeterminate {
            arm: ArmIndex::from(1_usize)
        }),
        "the match stops at the first arm a hole decides"
    );
    assert_eq!(
        select_arm(&core, &domain, &patterns, &[right], scrutinee),
        Ok(Selection::Exhausted)
    );
}

#[test]
fn a_determinate_match_binds_left_to_right()
{
    let mut core = CoreArena::new();
    let five = literal_five(&mut core);
    let six = literal_six(&mut core);
    let pair = core.value_tuple(&[five, six]);
    let chain = LoweredChain::new();
    let environment = DefinitionalEnvironment::new();
    let definitions = Definitions::new(&chain, &environment, environment.root());
    let mut domain = DomainArena::new();
    let scrutinee =
        eval_value(&core, &mut domain, definitions, ample(), pair).expect("a pair evaluates");
    let Some(&[first, second]) = domain
        .value(scrutinee)
        .and_then(|held| domain.components(held))
    else {
        panic!("a pair evaluates to a pair");
    };

    let mut patterns = Patterns::new();
    let binder = patterns.mint(Pattern::Binder);
    let six_pattern = patterns.mint(Pattern::Literal(Literal::Text(StringLiteral::new(
        String::from("six"),
    ))));
    let five_pattern = patterns.mint(Pattern::Literal(Literal::Text(StringLiteral::new(
        String::from("five"),
    ))));
    let both = patterns.mint(Pattern::Pair(binder, binder));
    let wrong = patterns.mint(Pattern::Pair(binder, five_pattern));
    let right = patterns.mint(Pattern::Pair(binder, six_pattern));

    assert_eq!(
        match_pattern(&core, &domain, &patterns, both, scrutinee),
        Ok(Matched::Satisfied(vec![first, second])),
        "binders bind left to right"
    );
    assert_eq!(
        select_arm(&core, &domain, &patterns, &[wrong, right], scrutinee),
        Ok(Selection::Taken {
            arm: ArmIndex::from(1_usize),
            bindings: vec![first]
        }),
        "a determinate scrutinee takes the first arm that matches"
    );
}

#[test]
fn a_constructor_pattern_matches_its_own_tag_at_its_own_arity()
{
    use gandr_core_term::ConstructorTag;

    let mut core = CoreArena::new();
    let unit_type = core.value_type_unit();
    let mut domain = DomainArena::new();
    let datatype = domain.value_closure_node(
        ValueBody::ValueType(unit_type),
        crate::closure::Environment::new(),
    );
    let field = domain.value_unit(crate::TermFace::Reduced);
    let fields = domain.hold_fields([field]);
    let scrutinee = domain.value_constructor(
        datatype,
        ConstructorTag::from(1_usize),
        fields,
        crate::TermFace::Reduced,
    );
    let mut patterns = Patterns::new();
    let binder = patterns.mint(Pattern::Binder);
    let mut constructor = |tag: usize, arity: usize| {
        patterns.mint(Pattern::Constructor {
            tag: ConstructorTag::from(tag),
            fields: vec![binder; arity],
        })
    };
    let own = constructor(1, 1);
    let other = constructor(0, 1);
    let wider = constructor(1, 2);
    assert_eq!(
        match_pattern(&core, &domain, &patterns, own, scrutinee),
        Ok(Matched::Satisfied(vec![field])),
        "its own tag at its own arity binds its field"
    );
    assert_eq!(
        match_pattern(&core, &domain, &patterns, other, scrutinee),
        Ok(Matched::Refuted),
        "another tag refutes"
    );
    assert_eq!(
        match_pattern(&core, &domain, &patterns, wider, scrutinee),
        Err(super::MatchFault::Mismatched),
        "and its own tag at another arity is a mismatch"
    );
}
