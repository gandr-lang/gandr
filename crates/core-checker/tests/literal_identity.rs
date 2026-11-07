//! A literal identity test answers alike in the native table's evaluation, in
//! the checker's evaluator and in the kernel's reduction.

use alloc::string::ToString as _;
use alloc::vec::Vec;

use gandr_core_checker::CheckBudget;
use gandr_core_checker::CheckingContext;
use gandr_core_checker::Declaration;
use gandr_core_checker::OriginToken;
use gandr_core_checker::Verdict;
use gandr_core_checker::bridge;
use gandr_core_checker::bridge::Outcome;
use gandr_core_checker::check_module;
use gandr_core_term::CoreArena;
use gandr_core_term::Summand;
use gandr_core_term::primitive::Arguments;
use gandr_core_term::primitive::PRELUDE;
use gandr_core_term::primitive::Primitive;
use gandr_core_term::primitive::Scalar;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::IdentityBase;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Magnitude;
use gandr_kernel_term::Side;
use gandr_kernel_term::Sign;
use gandr_kernel_term::StringLiteral;
use proptest::prelude::ProptestConfig;
use proptest::prelude::any;
use proptest::prelude::prop_assert;
use proptest::prelude::proptest;
use proptest::test_runner::TestCaseError;
use quenchant_shape::shape::Maybe;

/// The native rows that are literal identity tests.
///
/// # Specification
/// trivial.
fn identity_rows() -> Vec<Primitive>
{
    PRELUDE
        .iter()
        .copied()
        .filter(|row| row.literal_identity().is_some())
        .collect()
}

/// `def answered : U (F Path[.A = 1 + 1](row(left, right), answer)) = thunk {
/// return here(answer) }`, where `answer` injects the unit at `summand`.
///
/// # Specification
/// trivial.
fn answered(
    arena: &mut CoreArena,
    row: Primitive,
    operands: [Literal; 2],
    summand: Summand,
) -> Declaration
{
    let unit_type = arena.value_type_unit();
    let boolean = arena.value_type_sum(&[unit_type, unit_type]);
    let operands = operands.map(|literal| arena.value_literal(literal));
    let call = arena.computation_primitive(row, Arguments::Binary(operands));
    let computed = arena.value_returned(call);
    let unit = arena.value_unit();
    let answer = arena.value_injection(summand, unit);
    let path = arena.value_type_path(boolean, computed, answer);
    let returner = arena.comp_type_returner(path);
    let declared = arena.value_type_thunk(returner);
    let reflexivity = arena.value_here(answer);
    let returned = arena.computation_return(reflexivity);
    let body = arena.value_thunk(returned);
    Declaration::new(
        ConstantIndex::from(0_usize),
        Maybe::Present(declared),
        Maybe::Present(body),
        OriginToken::from(0_usize),
    )
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(64))]

    #[test]
    fn a_literal_identity_test_answers_alike_in_the_checker_and_the_kernel(
        row in 0_usize .. 4,
        integers in (any::<i64>(), any::<i64>()),
        texts in ("[ab\u{e9}]{0,3}", "[ab\u{e9}]{0,3}"),
        same in any::<bool>(),
    ) {
        let rows = identity_rows();
        let row = *rows.get(row).expect("four identity rows");
        let test = row.literal_identity().expect("an identity row");
        let integer = |value: i64| {
            let sign = if value < 0 { Sign::Negative } else { Sign::NonNegative };
            let magnitude = Magnitude::from_decimal_text(value.unsigned_abs().to_string())
                .expect("decimal digits");
            IntegerLiteral::new(sign, magnitude)
        };
        let (scalars, operands) = match test.base() {
            IdentityBase::Integer => {
                let first = integer(integers.0);
                let second = integer(if same { integers.0 } else { integers.1 });
                (
                    [Scalar::Integer(first.clone()), Scalar::Integer(second.clone())],
                    [Literal::Integer(first), Literal::Integer(second)],
                )
            },
            IdentityBase::Text => {
                let first = StringLiteral::new(texts.0.clone());
                let second = StringLiteral::new(if same { texts.0 } else { texts.1 });
                (
                    [Scalar::Text(first.clone()), Scalar::Text(second.clone())],
                    [Literal::Text(first), Literal::Text(second)],
                )
            },
        };
        let [ref first, ref second] = scalars;
        let evaluated = row
            .evaluate(&[first.borrowed(), second.borrowed()])
            .expect("an identity row evaluates on its base");
        let holds = evaluated == Scalar::Boolean(Side::Left);
        prop_assert!(
            holds || evaluated == Scalar::Boolean(Side::Right),
            "an identity row answers a boolean: {evaluated:?}"
        );
        let summand = Summand::from(usize::from(!holds));
        let mut arena = CoreArena::new();
        let declaration = answered(&mut arena, row, operands.clone(), summand);
        let report = check_module(
            &mut CheckingContext::new(&mut arena, CheckBudget::DEFAULT),
            &[declaration],
        );
        prop_assert!(
            matches!(report.judged()[0].verdict(), Verdict::Checked { .. }),
            "the checker answers as the table: {:?}",
            report.judged()[0].verdict()
        );
        let crossed = bridge::readmit(&mut arena, &report);
        let Outcome::Defined { ref audit, .. } = *crossed.readmitted()[0].outcome()
        else {
            return Err(TestCaseError::fail(alloc::format!(
                "the kernel replays the answer: {:?}",
                crossed.readmitted()[0].outcome()
            )));
        };
        prop_assert!(
            audit.axioms().is_empty() && audit.primitives().len() == 1,
            "the kernel computes the test, so the audit names it a primitive and no axiom: {audit:?}"
        );
        let other = Summand::from(usize::from(holds));
        let mut arena = CoreArena::new();
        let declaration = answered(&mut arena, row, operands, other);
        let report = check_module(
            &mut CheckingContext::new(&mut arena, CheckBudget::DEFAULT),
            &[declaration],
        );
        prop_assert!(
            matches!(report.judged()[0].verdict(), Verdict::Refused(_)),
            "the other answer is refused: {:?}",
            report.judged()[0].verdict()
        );
    }
}
