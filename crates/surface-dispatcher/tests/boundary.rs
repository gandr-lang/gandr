//! Definitions of a composed program called from Rust on values the caller
//! builds, each answer read back into the caller's arena.

use core::convert::Infallible;
use std::path::Path;
use std::sync::OnceLock;

use anodized::spec;
use gandr_core_checker::HostGrant;
use gandr_core_sequent::ConstructorTag;
use gandr_core_sequent::HeapValue;
use gandr_core_sequent::HeapValueId;
use gandr_core_sequent::Stuck;
use gandr_core_term::Computation;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_kernel_term::FixedInteger;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Magnitude;
use gandr_kernel_term::Sign;
use gandr_runtime_emitter::HostHandler;
use gandr_runtime_emitter::HostReply;
use gandr_runtime_emitter::HostRequest;
use gandr_runtime_emitter::HostValues;
use gandr_surface_corpus::CorpusRoot;
use gandr_surface_dispatcher::Composed;
use gandr_surface_dispatcher::Evaluation;
use gandr_surface_dispatcher::Laid;
use gandr_surface_dispatcher::Lowered;
use gandr_surface_dispatcher::LoweringCount;
use gandr_surface_dispatcher::Terminal;
use gandr_surface_dispatcher::Unrunnable;
use gandr_surface_dispatcher::classify;
use gandr_surface_dispatcher::judge_member;
use gandr_surface_dispatcher::lay_out;
use gandr_surface_dispatcher::lower_unit_source;
use gandr_surface_grammar::built_in;
use gandr_surface_lowering::SurfaceName;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

/// `text`, read as the source at `path`, laid out as one unit with the sources
/// it imports.
///
/// # Specification
/// - ensures: the unit [`lay_out`] reads for `text` at `path`, its imports
///   resolved beside `path`.
/// - panics: if the built-in grammar does not build.
/// - executable: none — the layout is the dispatcher's; the calls compose it.
///
/// # Adequacy
/// - hypothesis: L3 — the exemplar's imports resolve, and a source no file
///   holds lays out alone.
/// - witness: `tests::boundary::a_definition_answers_the_integer_rust_passes`
/// - witness: `tests::boundary::an_unrunnable_definition_ends_before_a_run`
fn laid(
    path: &Path,
    text: SourceText<'_>,
) -> Laid
{
    let grammar = built_in().expect("built-in grammar");
    lay_out(&grammar, path, classify(path), text)
}

/// The exemplar whose definitions the tests call, laid out once with the `std`
/// modules it imports.
///
/// # Specification
/// - ensures: the unit of `round-trip.gandr` as the corpus holds it.
/// - panics: if the exemplar does not read.
/// - executable: none — as [`laid`].
///
/// # Adequacy
/// - hypothesis: L3 — as [`laid`].
/// - witness: `tests::boundary::a_definition_answers_the_integer_rust_passes`
fn round_trip() -> &'static Laid
{
    static ROUND_TRIP: OnceLock<Laid> = OnceLock::new();
    ROUND_TRIP.get_or_init(|| {
        let path = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../corpus/model/interop/boundary/round-trip.gandr");
        let text = std::fs::read_to_string(&path).expect("the exemplar reads");
        laid(&path, SourceText::from(text.as_str()))
    })
}

/// A definition the checker refuses, laid out alone.
///
/// # Specification
/// - ensures: the unit of one definition calling `sub` on a text.
/// - panics: none.
/// - executable: none — as [`laid`].
///
/// # Adequacy
/// - hypothesis: L3 — as [`laid`].
/// - witness: `tests::boundary::an_unrunnable_definition_ends_before_a_run`
fn refused() -> &'static Laid
{
    static REFUSED: OnceLock<Laid> = OnceLock::new();
    REFUSED.get_or_init(|| {
        laid(
            Path::new("refused.gandr"),
            SourceText::from("def refused(x : Integer) -> Integer { sub(\"wrong\", x) }"),
        )
    })
}

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

/// A `u32` as the Rust side of the exemplar's extern block takes and answers
/// it.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Word(u32);

/// The Rust function the exemplar's extern block declares, `add(x: u32, n:
/// u32) -> u32`, wrapping as Rust's `u32` addition does in a release build.
///
/// # Specification
/// trivial.
fn add(
    x: Word,
    n: Word,
) -> Word
{
    Word(x.0.wrapping_add(n.0))
}

/// The literal of `word`, a `u32`.
///
/// # Specification
/// trivial.
const fn word(word: Word) -> Literal
{
    Literal::Fixed(FixedInteger::U32(word.0))
}

/// A host answering nothing: every operation it is offered stays unhandled.
struct Declining;

impl HostHandler for Declining
{
    type Abort = Infallible;

    /// Decline the operation.
    ///
    /// # Specification
    /// trivial.
    fn handle(
        &mut self,
        _request: HostRequest<'_>,
        _values: &mut HostValues<'_>,
    ) -> HostReply<Infallible>
    {
        HostReply::Decline
    }
}

/// The Rust side of the exemplar's extern block: a host answering
/// `Boundary.add` with [`add`], keeping each pair of arguments it is passed,
/// and declining any other operation.
#[repr(transparent)]
struct RustSide
{
    /// The arguments of each `Boundary.add` answered, in order.
    received: Vec<(Word, Word)>,
}

impl HostHandler for RustSide
{
    type Abort = Infallible;

    /// Answer `Boundary.add` on two `u32` with their [`add`], declining any
    /// other operation or payload.
    ///
    /// # Specification
    /// trivial.
    fn handle(
        &mut self,
        request: HostRequest<'_>,
        values: &mut HostValues<'_>,
    ) -> HostReply<Infallible>
    {
        if request.signature.name().as_ref() != "Boundary" || request.operation.as_ref() != "add" {
            return HostReply::Decline;
        }
        let Some(&HeapValue::Constructed {
            tag: ConstructorTag::Tuple(_),
            ref fields,
        }) = values.value(request.payload)
        else {
            return HostReply::Decline;
        };
        let read = |at: HeapValueId| match values.value(at) {
            Some(&HeapValue::Literal(Literal::Fixed(FixedInteger::U32(value)))) => {
                Some(Word(value))
            },
            _ => None,
        };
        let (Some(x), Some(n)) = (
            fields.first().copied().and_then(read),
            fields.get(1).copied().and_then(read),
        )
        else {
            return HostReply::Decline;
        };
        self.received.push((x, n));
        match values.allocate(HeapValue::Literal(word(add(x, n)))) {
            Ok(sum) => HostReply::Resume(sum),
            Err(_spent) => HostReply::Decline,
        }
    }
}

/// Compose `laid`, call its definition `name` on `arguments` under `host`, and
/// answer the caller's arena beside how the call ended.
///
/// # Specification
/// - requires: `laid` composes and its own source declares `name` at its top
///   level.
/// - ensures: the arena holding the arguments and any read-back answer, and the
///   terminal the real dispatcher's call ended at.
/// - panics: if composition or the lookup of `name` fails.
///
/// # Adequacy
/// - hypothesis: L3 — integer answers, an order-dependent answer, a function
///   answered, a refused definition, an extern operation answered and one
///   declined have distinct observations.
/// - witness: `tests::boundary::a_definition_answers_the_integer_rust_passes`
/// - witness: `tests::boundary::an_extern_operation_is_answered_by_the_rust_caller`
/// - witness: `tests::boundary::an_extern_operation_no_host_answers_sticks_the_run`
#[spec(ensures: |ref ret| !matches!(ret.1, Terminal::Ended(Evaluation::Unrunnable(Unrunnable::Undeclared(_)))))]
fn call_under<Host>(
    laid: &'static Laid,
    name: SurfaceName<'_>,
    arguments: &[Literal],
    host: &mut Host,
) -> (CoreArena, Terminal<'static>)
where
    Host: HostHandler<Abort = Infallible>,
{
    let grammar = built_in().expect("built-in grammar");
    let source = SourceText::from(laid.text.as_str());
    let lowering = lower_unit_source(&grammar, source, &laid.unit, &mut LoweringCount::default())
        .expect("the unit lowers");
    let Lowered::Module { module, arena } = lowering.into_lowered()
    else {
        panic!("the unit is read as a module");
    };
    let Composed::Settled { mut program, .. } = judge_member(
        CorpusRoot::Fixture,
        (module, source),
        arena,
        &HostGrant::UNBOUNDED,
        laid.base,
    )
    .admit()
    .expect("composition")
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
        .map(|argument| arena.value_literal(argument.clone()))
        .collect();
    let Ok(terminal) = program.call(constant, &arguments, &mut arena, host);
    (arena, terminal)
}

/// Compose `source` and call its definition `name` on `arguments`, integers,
/// under a host answering nothing.
///
/// # Specification
/// - requires: as [`call_under`].
/// - ensures: as [`call_under`].
/// - panics: as [`call_under`].
///
/// # Adequacy
/// - hypothesis: L3 — as [`call_under`].
/// - witness: `tests::boundary::the_arguments_apply_in_the_order_passed`
/// - witness: `tests::boundary::a_function_answered_is_not_forced`
/// - witness: `tests::boundary::an_unrunnable_definition_ends_before_a_run`
#[spec(ensures: |ref ret| !matches!(ret.1, Terminal::Ended(Evaluation::Unrunnable(Unrunnable::Undeclared(_)))))]
fn call(
    laid: &'static Laid,
    name: SurfaceName<'_>,
    arguments: &[Integer],
) -> (CoreArena, Terminal<'static>)
{
    let literals: Vec<Literal> = arguments
        .iter()
        .map(|&argument| literal(argument))
        .collect();
    call_under(laid, name, &literals, &mut Declining)
}

#[test]
fn a_definition_answers_the_integer_rust_passes()
{
    for (argument, answer) in [
        (Integer(21), Integer(42)),
        (Integer(-3), Integer(-6)),
        (Integer(0), Integer(0)),
    ] {
        let (arena, terminal) = call(round_trip(), SurfaceName::from("double"), &[argument]);
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
        let (arena, terminal) = call(round_trip(), SurfaceName::from("less"), &arguments);
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
    let (arena, terminal) = call(round_trip(), SurfaceName::from("adder"), &[Integer(5)]);
    assert!(
        matches!(returned(&arena, &terminal), Some(&Value::Thunk(_))),
        "{terminal:?}"
    );
}

#[test]
fn an_unrunnable_definition_ends_before_a_run()
{
    let (_, terminal) = call(refused(), SurfaceName::from("refused"), &[Integer(1)]);
    assert!(
        matches!(
            terminal,
            Terminal::Ended(Evaluation::Unrunnable(Unrunnable::Refused(name)))
                if name.as_ref() == "refused"
        ),
        "{terminal:?}"
    );
}

#[test]
fn an_extern_operation_is_answered_by_the_rust_caller()
{
    for (argument, answer, received) in [
        (Word(5), Word(20), [
            (Word(5), Word(5)),
            (Word(10), Word(10)),
        ]),
        // Rust's addition wraps where gandr's `Integer` would not.
        (Word(0x8000_0001), Word(4), [
            (Word(0x8000_0001), Word(0x8000_0001)),
            (Word(2), Word(2)),
        ]),
    ] {
        let mut rust = RustSide {
            received: Vec::new(),
        };
        let (arena, terminal) = call_under(
            round_trip(),
            SurfaceName::from("quadrupled"),
            &[word(argument)],
            &mut rust,
        );
        assert_eq!(
            returned(&arena, &terminal),
            Some(&Value::Literal(word(answer))),
            "quadrupled({argument:?}): {terminal:?}"
        );
        assert_eq!(
            rust.received, received,
            "each perform reached Rust with its arguments, in order"
        );
    }
}

#[test]
fn an_extern_operation_no_host_answers_sticks_the_run()
{
    let (_, terminal) = call_under(
        round_trip(),
        SurfaceName::from("quadrupled"),
        &[word(Word(5))],
        &mut Declining,
    );
    assert!(
        matches!(
            terminal,
            Terminal::Ended(Evaluation::Stuck(Stuck::PerformNoHandler(_)))
        ),
        "{terminal:?}"
    );
}
