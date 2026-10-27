use alloc::boxed::Box;

use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Magnitude;
use gandr_kernel_term::Sign;

use super::*;
use crate::boundary::ProducerArity;
use crate::check::check_command;
use crate::il::ConstructorTag;
use crate::pretty::render_command;
use crate::pretty::render_producer;

/// Mint the variable `xindex`.
///
/// # Specification
/// trivial.
fn variable(
    arena: &mut CommandArena,
    index: DeBruijnIndex,
) -> ProducerId
{
    arena
        .mint_producer(ProducerNode::Variable {
            zone: Zone::Intuitionistic,
            index,
        })
        .expect("a leaf mints")
}

/// Mint `★`.
///
/// # Specification
/// trivial.
fn top(arena: &mut CommandArena) -> ConsumerId
{
    arena
        .mint_consumer(ConsumerNode::Top)
        .expect("a leaf mints")
}

/// Mint `cocase {apply(x; α) ⇒ ⟨returned |+ α0⟩}`.
///
/// # Specification
/// trivial.
fn function(
    arena: &mut CommandArena,
    returned: ProducerId,
) -> ProducerId
{
    let back = arena
        .mint_consumer(ConsumerNode::Covariable(CovariableIndex::from(0_u32)))
        .expect("a leaf mints");
    let body = arena
        .mint_cut(Polarity::Positive, returned, back)
        .expect("children resolve");
    arena
        .mint_producer(ProducerNode::Cocase {
            arms: Box::from([CopatternArm {
                destructor: DestructorTag::Apply,
                body,
            }]),
        })
        .expect("children resolve")
}

/// Mint the pair `(first, second)`.
///
/// # Specification
/// trivial.
fn pair(
    arena: &mut CommandArena,
    first: ProducerId,
    second: ProducerId,
) -> ProducerId
{
    arena
        .mint_producer(ProducerNode::Constructor {
            tag: ConstructorTag::Tuple(ProducerArity::TWO),
            producers: Box::from([first, second]),
            consumers: Box::from([]),
        })
        .expect("children resolve")
}

/// A function returning the pair of its two context variables, `x1` and
/// `x2` under its argument, steps first to the greater, `x1`, then to the
/// lesser, then stops: the environment holds both, outermost first, and the
/// code reads them where it read the context.
#[test]
fn a_step_captures_the_greatest_context_variable()
{
    let mut arena = CommandArena::new();
    let first = variable(&mut arena, DeBruijnIndex::from(1_u32));
    let second = variable(&mut arena, DeBruijnIndex::from(2_u32));
    let both = pair(&mut arena, first, second);
    let object = function(&mut arena, both);
    assert_eq!(
        "cocase {apply(x; α) ⇒ ⟨pair(x1, x2) |+ α0⟩}",
        render_producer(&arena, object)
    );

    let once = convert_step(&mut arena, object)
        .expect("a function converts")
        .expect("it names a context variable");
    assert_eq!(
        "{x1; cocase {apply(x; α) ⇒ ⟨pair(x2, x1) |+ α0⟩}}",
        render_producer(&arena, once),
        "the greater variable moves in first"
    );
    let twice = convert_step(&mut arena, once)
        .expect("a closure converts")
        .expect("it names a context variable");
    assert_eq!(
        "{x1, x0; cocase {apply(x; α) ⇒ ⟨pair(x1, x2) |+ α0⟩}}",
        render_producer(&arena, twice),
        "the lesser one follows, innermost"
    );
    let mark = arena.watermark();
    assert_eq!(
        Ok(None),
        convert_step(&mut arena, twice),
        "a converted closure takes no step"
    );
    assert_eq!(mark, arena.watermark(), "a stopped step mints nothing");
    let converted = convert(&mut arena, object).expect("a function converts");
    assert_eq!(
        render_producer(&arena, twice),
        render_producer(&arena, converted),
        "conversion reaches the normal form the steps reach"
    );
}

/// A constructor is no closure; a closed former is converted as it stands.
#[test]
fn only_closures_convert()
{
    let mut arena = CommandArena::new();
    let unit = arena
        .mint_producer(ProducerNode::Constructor {
            tag: ConstructorTag::Tuple(ProducerArity::ZERO),
            producers: Box::from([]),
            consumers: Box::from([]),
        })
        .expect("a leaf mints");
    let mark = arena.watermark();
    assert_eq!(
        Err(ClosureRefusal::NotAClosure(unit)),
        convert_step(&mut arena, unit)
    );
    assert_eq!(
        Err(ClosureRefusal::NotAClosure(unit)),
        convert(&mut arena, unit)
    );
    assert_eq!(mark, arena.watermark(), "a refusal mints nothing");

    let argument = variable(&mut arena, DeBruijnIndex::from(0_u32));
    let identity = function(&mut arena, argument);
    let mark = arena.watermark();
    assert_eq!(Ok(None), convert_step(&mut arena, identity));
    assert_eq!(Ok(identity), convert(&mut arena, identity));
    assert_eq!(mark, arena.watermark(), "a closed former stays bare");
}

/// A converted closure converts to itself.
#[test]
fn conversion_is_idempotent()
{
    let mut arena = CommandArena::new();
    let free = variable(&mut arena, DeBruijnIndex::from(3_u32));
    let object = function(&mut arena, free);
    let converted = convert(&mut arena, object).expect("a function converts");
    assert_eq!(
        "{x2; cocase {apply(x; α) ⇒ ⟨x1 |+ α0⟩}}",
        render_producer(&arena, converted)
    );
    assert_eq!(Ok(converted), convert(&mut arena, converted));
}

/// A thunk returning a function that names the context's `x1` converts
/// inside out: the function first, over `x1` where it stands, then the thunk,
/// whose conversion renames the function's environment to read the thunk's.
#[test]
fn a_nested_function_converts_inside_out()
{
    let mut arena = CommandArena::new();
    let free = variable(&mut arena, DeBruijnIndex::from(2_u32));
    let object = function(&mut arena, free);
    let back = arena
        .mint_consumer(ConsumerNode::Covariable(CovariableIndex::from(0_u32)))
        .expect("a leaf mints");
    let body = arena
        .mint_cut(Polarity::Negative, object, back)
        .expect("children resolve");
    let thunk = arena
        .mint_producer(ProducerNode::Thunk { body })
        .expect("children resolve");
    let observer = top(&mut arena);
    let root = arena
        .mint_cut(Polarity::Positive, thunk, observer)
        .expect("children resolve");
    let NodeAddress::Command(converted) =
        convert_all(&mut arena, NodeAddress::Command(root)).expect("the command converts")
    else {
        panic!("a command converts to a command");
    };
    assert_eq!(
        "⟨{x1; {force(α) ⇒ ⟨{x0; cocase {apply(x; α) ⇒ ⟨x1 |+ α0⟩}} |− α0⟩}} |+ ★⟩",
        render_command(&arena, converted)
    );
    assert_eq!(
        check_command(&arena, root),
        check_command(&arena, converted),
        "conversion keeps the command's free variables"
    );
    assert_eq!(
        Ok(NodeAddress::Command(converted)),
        convert_all(&mut arena, NodeAddress::Command(converted)),
        "a converted command converts to itself"
    );
}

/// The constant function `fn (_m) { n }`, converted over `n` and applied to
/// 5, binds its continuation, then `n`, then 5, over its arm's body as
/// written. A value against a match, and a closure against a frame its code
/// does not answer, are no redex.
#[test]
fn beta_binds_the_environment_and_the_argument_together()
{
    let mut arena = CommandArena::new();
    let held = variable(&mut arena, DeBruijnIndex::from(1_u32));
    let constantly = function(&mut arena, held);
    let closure = convert(&mut arena, constantly).expect("a function converts");
    assert_eq!(
        "{x0; cocase {apply(x; α) ⇒ ⟨x1 |+ α0⟩}}",
        render_producer(&arena, closure)
    );
    let magnitude =
        Magnitude::from_decimal_text(alloc::string::String::from("5")).expect("decimal digits");
    let five = arena
        .mint_producer(ProducerNode::Literal(Literal::Integer(
            IntegerLiteral::new(Sign::NonNegative, magnitude),
        )))
        .expect("a leaf mints");
    let observer = top(&mut arena);
    let frame = arena
        .mint_consumer(ConsumerNode::Destructor {
            tag: DestructorTag::Apply,
            producers: Box::from([five]),
            consumers: Box::from([observer]),
        })
        .expect("children resolve");
    let cut = arena
        .mint_cut(Polarity::Negative, closure, frame)
        .expect("children resolve");
    let entered = beta(&mut arena, cut)
        .expect("the redex enters")
        .expect("it is a redex");
    assert_eq!(
        "⟨μα. ⟨x0 |+ μ̃x. ⟨5 |+ μ̃x. ⟨x1 |+ α0⟩⟩⟩ |+ ★⟩",
        render_command(&arena, entered)
    );
    assert_eq!(
        check_command(&arena, cut),
        check_command(&arena, entered),
        "the reduct names what the redex named"
    );

    let unit = arena
        .mint_producer(ProducerNode::Constructor {
            tag: ConstructorTag::Tuple(ProducerArity::ZERO),
            producers: Box::from([]),
            consumers: Box::from([]),
        })
        .expect("a leaf mints");
    let matched = arena
        .mint_cut(Polarity::Positive, unit, observer)
        .expect("children resolve");
    let forced = arena
        .mint_consumer(ConsumerNode::Destructor {
            tag: DestructorTag::Force,
            producers: Box::from([]),
            consumers: Box::from([observer]),
        })
        .expect("children resolve");
    let unanswered = arena
        .mint_cut(Polarity::Negative, closure, forced)
        .expect("children resolve");
    for (command, what) in [(matched, "a value"), (unanswered, "an unanswered frame")] {
        let mark = arena.watermark();
        assert_eq!(Ok(None), beta(&mut arena, command), "{what} is no redex");
        assert_eq!(mark, arena.watermark(), "{what} mints nothing");
    }
}
