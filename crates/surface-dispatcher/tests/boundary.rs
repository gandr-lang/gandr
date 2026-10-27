//! Definitions of a composed program called from Rust on values the caller
//! builds, each answer read back into the caller's arena.

use anodized::spec;
use gandr_core_term::Computation;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Magnitude;
use gandr_kernel_term::Sign;
use gandr_surface_corpus::CorpusRoot;
use gandr_surface_dispatcher::Composed;
use gandr_surface_dispatcher::Evaluation;
use gandr_surface_dispatcher::LoweringCount;
use gandr_surface_dispatcher::Terminal;
use gandr_surface_dispatcher::Unrunnable;
use gandr_surface_dispatcher::compose;
use gandr_surface_grammar::built_in;
use gandr_surface_lowering::SurfaceName;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

/// The exemplar whose definitions the tests call.
const ROUND_TRIP: &str = include_str!("../../../corpus/model/interop/boundary/round-trip.gandr");

/// An integer the Rust caller passes to a definition or expects back.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Integer(i64);

/// The integer literal denoting `value`.
///
/// # Specification
/// trivial.
fn literal(value: Integer) -> Literal
{
    let Integer(value) = value;
    let sign = if value < 0 {
        Sign::Negative
    }
    else {
        Sign::NonNegative
    };
    let magnitude = Magnitude::from_decimal_text(value.unsigned_abs().to_string())
        .expect("an integer's magnitude is decimal digits");
    Literal::Integer(IntegerLiteral::new(sign, magnitude))
}

/// The value a call's answer returns, as `arena` holds it.
///
/// # Specification
/// trivial.
fn returned<'arena>(
    arena: &'arena CoreArena,
    terminal: &Terminal<'_>,
) -> Option<&'arena Value>
{
    let Terminal::Read(read) = *terminal
    else {
        return None;
    };
    let Some(&Computation::Return(value)) = arena.computation(read)
    else {
        return None;
    };
    arena.value(value)
}

/// Compose `source`, call its definition `name` on `arguments`, and answer
/// the caller's arena beside how the call ended.
///
/// # Specification
/// - requires: `source` composes and declares `name` at its top level.
/// - ensures: the arena holding the arguments and any read-back answer, and the
///   terminal the real dispatcher's call ended at.
/// - panics: if composition or the lookup of `name` fails.
///
/// # Adequacy
/// - hypothesis: L3 — integer answers, an order-dependent answer, a function
///   answered and a refused definition have distinct observations.
/// - witness: `tests::boundary::a_definition_answers_the_integer_rust_passes`
/// - witness: `tests::boundary::the_arguments_apply_in_the_order_passed`
/// - witness: `tests::boundary::a_function_answered_is_not_forced`
/// - witness: `tests::boundary::an_unrunnable_definition_ends_before_a_run`
#[spec(ensures: |ref ret| !matches!(ret.1, Terminal::Ended(Evaluation::Unrunnable(Unrunnable::Undeclared(_)))))]
fn call(
    source: SourceText<'static>,
    name: SurfaceName<'_>,
    arguments: &[Integer],
) -> (CoreArena, Terminal<'static>)
{
    let grammar = built_in().expect("built-in grammar");
    let mut lowerings = LoweringCount::default();
    let Composed::Settled { mut program, .. } =
        compose(&grammar, CorpusRoot::Fixture, source, &mut lowerings).expect("composition")
    else {
        panic!("module was refused");
    };
    let Maybe::Present(constant) = program.named(name)
    else {
        panic!("`{name}` is declared");
    };
    let mut arena = CoreArena::new();
    let arguments: Vec<_> = arguments
        .iter()
        .map(|&argument| arena.value_literal(literal(argument)))
        .collect();
    let terminal = program.call(constant, &arguments, &mut arena);
    (arena, terminal)
}

#[test]
fn a_definition_answers_the_integer_rust_passes()
{
    for (argument, answer) in [
        (Integer(21), Integer(42)),
        (Integer(-3), Integer(-6)),
        (Integer(0), Integer(0)),
    ] {
        let (arena, terminal) = call(
            SourceText::from(ROUND_TRIP),
            SurfaceName::from("double"),
            &[argument],
        );
        assert_eq!(
            returned(&arena, &terminal),
            Some(&Value::Literal(literal(answer))),
            "double({argument:?}): {terminal:?}"
        );
    }
}

#[test]
fn the_arguments_apply_in_the_order_passed()
{
    for (arguments, answer) in [
        ([Integer(19), Integer(7)], Integer(12)),
        ([Integer(7), Integer(19)], Integer(-12)),
    ] {
        let (arena, terminal) = call(
            SourceText::from(ROUND_TRIP),
            SurfaceName::from("less"),
            &arguments,
        );
        assert_eq!(
            returned(&arena, &terminal),
            Some(&Value::Literal(literal(answer))),
            "less{arguments:?}: {terminal:?}"
        );
    }
}

#[test]
fn a_function_answered_is_not_forced()
{
    let (arena, terminal) = call(SourceText::from(ROUND_TRIP), SurfaceName::from("adder"), &[
        Integer(5),
    ]);
    assert!(
        matches!(returned(&arena, &terminal), Some(&Value::Thunk(_))),
        "{terminal:?}"
    );
}

#[test]
fn an_unrunnable_definition_ends_before_a_run()
{
    let (_, terminal) = call(
        SourceText::from("def refused(x : Integer) -> Integer { sub(\"wrong\", x) }"),
        SurfaceName::from("refused"),
        &[Integer(1)],
    );
    assert!(
        matches!(
            terminal,
            Terminal::Ended(Evaluation::Unrunnable(Unrunnable::Refused(name)))
                if name.as_ref() == "refused"
        ),
        "{terminal:?}"
    );
}
