use super::*;
use crate::CompType;
use crate::Computation;
use crate::Value;
use crate::ValueType;
use crate::rewrite::instantiate_value;

/// A fixture's signed decimal spelling.
#[repr(transparent)]
#[derive(Clone, Copy)]
struct Digits(&'static str);

/// Read a fixture's canonical signed integer.
///
/// # Specification
/// trivial.
fn integer(digits: Digits) -> Scalar
{
    let (sign, text) = digits
        .0
        .strip_prefix('-')
        .map_or((Sign::NonNegative, digits.0), |magnitude| {
            (Sign::Negative, magnitude)
        });
    Scalar::Integer(IntegerLiteral::new(
        sign,
        Magnitude::from_decimal_text(text.into()).expect("decimal fixture"),
    ))
}

/// Look up a fixture's native function.
///
/// # Specification
/// trivial.
fn named(name: PrimitiveName) -> Primitive
{
    PRELUDE
        .iter()
        .copied()
        .find(|primitive| primitive.name() == name)
        .expect("native fixture name")
}

#[test]
fn exact_arithmetic_and_errors()
{
    for (name, left, right, expected) in [
        (
            "add",
            "99999999999999999999999999999999999999",
            "1",
            "100000000000000000000000000000000000000",
        ),
        ("sub", "7", "11", "-4"),
        (
            "mul",
            "-100000000000000000000",
            "100000000000000000000",
            "-10000000000000000000000000000000000000000",
        ),
        ("int.div", "-19", "4", "-4"),
        ("int.mod", "-19", "4", "-3"),
        ("prim.const", "23", "45", "23"),
    ] {
        let operands = [integer(Digits(left)), integer(Digits(right))];
        assert_eq!(
            named(PrimitiveName(name)).evaluate(&operands.each_ref().map(Scalar::borrowed)),
            Ok(integer(Digits(expected))),
            "{name}"
        );
    }
    for (name, input, expected) in [("neg", "-7", "7"), ("prim.id", "-8", "-8")] {
        let operand = integer(Digits(input));
        assert_eq!(
            named(PrimitiveName(name)).evaluate(&[operand.borrowed()]),
            Ok(integer(Digits(expected)))
        );
    }
    let zero = integer(Digits("0"));
    let one = integer(Digits("1"));
    assert_eq!(
        named(PrimitiveName("neg")).evaluate(&[zero.borrowed()]),
        Ok(zero.clone())
    );
    for name in ["int.div", "int.mod"] {
        assert_eq!(
            named(PrimitiveName(name)).evaluate(&[one.borrowed(), zero.borrowed()]),
            Err(PrimitiveError::DivisionByZero)
        );
    }
    let add = named(PrimitiveName("add"));
    assert_eq!(add.evaluate(&[]), Err(PrimitiveError::Arity));
    assert_eq!(
        add.evaluate(&[Scalar::Boolean(Side::Left)]),
        Err(PrimitiveError::Arity)
    );
    assert_eq!(
        add.evaluate(&[one.borrowed(), Scalar::Boolean(Side::Left)]),
        Err(PrimitiveError::ArgumentType)
    );
}

#[test]
fn comparisons_and_booleans()
{
    let less = integer(Digits("-4"));
    let more = integer(Digits("9"));
    for (name, expected) in [
        ("eq", Side::Right),
        ("ne", Side::Left),
        ("lt", Side::Left),
        ("le", Side::Left),
        ("gt", Side::Right),
        ("ge", Side::Right),
    ] {
        assert_eq!(
            named(PrimitiveName(name)).evaluate(&[less.borrowed(), more.borrowed()]),
            Ok(Scalar::Boolean(expected)),
            "{name}"
        );
    }
    for (name, expected) in [
        ("eq", Side::Left),
        ("ne", Side::Right),
        ("lt", Side::Right),
        ("le", Side::Left),
        ("gt", Side::Right),
        ("ge", Side::Left),
    ] {
        assert_eq!(
            named(PrimitiveName(name)).evaluate(&[less.borrowed(), less.borrowed()]),
            Ok(Scalar::Boolean(expected)),
            "{name} equality boundary"
        );
    }
    for (left, right, conjunction, disjunction) in [
        (Side::Left, Side::Left, Side::Left, Side::Left),
        (Side::Left, Side::Right, Side::Right, Side::Left),
        (Side::Right, Side::Left, Side::Right, Side::Left),
        (Side::Right, Side::Right, Side::Right, Side::Right),
    ] {
        let arguments = [Scalar::Boolean(left), Scalar::Boolean(right)];
        assert_eq!(
            named(PrimitiveName("and")).evaluate(&arguments),
            Ok(Scalar::Boolean(conjunction))
        );
        assert_eq!(
            named(PrimitiveName("or")).evaluate(&arguments),
            Ok(Scalar::Boolean(disjunction))
        );
    }
    for (input, expected) in [(Side::Left, Side::Right), (Side::Right, Side::Left)] {
        assert_eq!(
            named(PrimitiveName("bool.not")).evaluate(&[Scalar::Boolean(input)]),
            Ok(Scalar::Boolean(expected))
        );
    }
}

#[test]
fn table_signatures_and_currying_agree()
{
    let mut arena = CoreArena::new();
    let primitive = named(PrimitiveName("sub"));
    assert_eq!(
        "sub",
        primitive.name().as_ref(),
        "a name borrows its spelling"
    );
    let mut signature = primitive.declared_type(&mut arena);
    let thunk = primitive.thunk(&mut arena);
    let Some(&Value::Primitive { mut body, .. }) = arena.value(thunk)
    else {
        panic!("native thunk");
    };
    for input in ["19", "7"] {
        let Some(&CompType::Arrow { domain, codomain }) = arena.comp_type(signature)
        else {
            panic!("curried arrow");
        };
        assert_eq!(
            arena.value_type(domain),
            Some(&ValueType::Base(BaseType::Integer))
        );
        signature = codomain;
        let Some(&Computation::Lambda(inner)) = arena.computation(body)
        else {
            panic!("curried lambda");
        };
        let wrapper = arena.value_thunk(inner);
        let argument = integer(Digits(input)).mint(&mut arena);
        let applied = instantiate_value(&mut arena, wrapper, argument);
        let Some(&Value::Thunk(inner)) = arena.value(applied)
        else {
            panic!("substituted thunk");
        };
        body = inner;
    }
    let Some(&CompType::Returner { result, .. }) = arena.comp_type(signature)
    else {
        panic!("returner");
    };
    assert_eq!(
        arena.value_type(result),
        Some(&ValueType::Base(BaseType::Integer))
    );
    let Some(&Computation::Primitive {
        primitive,
        arguments: Arguments::Binary(arguments),
    }) = arena.computation(body)
    else {
        panic!("saturated primitive");
    };
    let operands = arguments.map(|argument| match arena.value(argument) {
        Some(&Value::Literal(Literal::Integer(ref integer))) => Scalar::Integer(integer),
        _ => panic!("substituted operand"),
    });
    assert_eq!(primitive.evaluate(&operands), Ok(integer(Digits("12"))));
}
