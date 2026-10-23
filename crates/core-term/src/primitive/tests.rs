use alloc::vec::Vec;

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
fn an_append_writes_the_first_string_then_the_second()
{
    let append = named(PrimitiveName("string.append"));
    let text = |content: &str| Scalar::Text(StringLiteral::new(String::from(content)));
    let (types, machines) = (text("types are "), text("machines"));
    assert_eq!(
        append.evaluate(&[types.borrowed(), machines.borrowed()]),
        Ok(text("types are machines"))
    );
    assert_eq!(
        append.evaluate(&[machines.borrowed(), types.borrowed()]),
        Ok(text("machinestypes are ")),
        "the order is the operands'"
    );
    assert_eq!(
        append.evaluate(&[text("").borrowed(), text("λ\n").borrowed()]),
        Ok(text("λ\n"))
    );
    assert_eq!(
        append.evaluate(&[types.borrowed(), integer(Digits("1")).borrowed()]),
        Err(PrimitiveError::ArgumentType),
        "a text row refuses an integer"
    );
    assert_eq!(
        named(PrimitiveName("add")).evaluate(&[types.borrowed(), machines.borrowed()]),
        Err(PrimitiveError::ArgumentType),
        "an integer row refuses text"
    );
    let mut arena = CoreArena::new();
    let signature = append.declared_type(&mut arena);
    let Some(&CompType::Arrow { domain, .. }) = arena.comp_type(signature)
    else {
        panic!("curried arrow");
    };
    assert_eq!(
        arena.value_type(domain),
        Some(&ValueType::Base(BaseType::String))
    );
    let minted = types.mint(&mut arena);
    assert!(matches!(
        arena.value(minted),
        Some(Value::Literal(Literal::Text(content))) if content.as_ref() == "types are "
    ));
}

#[test]
fn floating_point_rows_are_ieee_binary64()
{
    let float = |value: f64| Scalar::Float64(Float64Literal::from(value));
    let apply = |name: &'static str, operands: &[Scalar]| {
        let borrowed: Vec<Scalar<&IntegerLiteral, &StringLiteral>> =
            operands.iter().map(Scalar::borrowed).collect();
        named(PrimitiveName(name)).evaluate(&borrowed)
    };
    assert_eq!(
        apply("float64.add", &[float(0.1_f64), float(0.2_f64)]),
        Ok(float(0.300_000_000_000_000_04_f64)),
        "a sum rounds to the nearest double, not to the decimal"
    );
    assert_eq!(
        apply("float64.div", &[float(1.0_f64), float(-0.0_f64)]),
        Ok(float(f64::NEG_INFINITY)),
        "a quotient by a signed zero is the signed infinity"
    );
    assert_eq!(
        apply("float64.sub", &[float(f64::INFINITY), float(f64::INFINITY)]),
        Ok(Scalar::Float64(Float64Literal::NAN)),
        "an invalid operation is the one canonical NaN"
    );
    assert_eq!(
        apply("float64.eq", &[float(f64::NAN), float(f64::NAN)]),
        Ok(Scalar::Boolean(Side::Right)),
        "a NaN equals nothing, itself included"
    );
    assert_eq!(
        apply("float64.ne", &[float(f64::NAN), float(f64::NAN)]),
        Ok(Scalar::Boolean(Side::Left))
    );
    assert_eq!(
        apply("float64.eq", &[float(-0.0_f64), float(0.0_f64)]),
        Ok(Scalar::Boolean(Side::Left)),
        "the zeros are equal"
    );
    assert_eq!(
        apply("float64.lt", &[float(-0.0_f64), float(0.0_f64)]),
        Ok(Scalar::Boolean(Side::Right)),
        "and neither is below the other"
    );
    assert_eq!(apply("float64.exp", &[float(0.0_f64)]), Ok(float(1.0_f64)));
    assert_eq!(
        apply("float64.exp", &[float(1.0_f64)]),
        Ok(float(f64::from_bits(0x4005_bf0a_8b14_576a_u64))),
        "`exp` at one is libm's double, one unit in the last place above e, on every host"
    );
    assert_eq!(apply("float64.neg", &[float(0.0_f64)]), Ok(float(-0.0_f64)));
    for (input, expected) in [
        (2.5_f64, "2"),
        (3.5_f64, "4"),
        (-2.5_f64, "-2"),
        (-0.4_f64, "0"),
        (1.0e20_f64, "100000000000000000000"),
    ] {
        assert_eq!(
            apply("float64.round", &[float(input)]),
            Ok(integer(Digits(expected))),
            "{input} rounds to the nearest integer, ties to even"
        );
    }
    for unbounded in [f64::INFINITY, f64::NAN] {
        assert_eq!(
            apply("float64.round", &[float(unbounded)]),
            Err(PrimitiveError::NotFinite),
            "no integer is nearest {unbounded}"
        );
    }
    assert_eq!(
        apply("float64.from_integer", &[integer(Digits(
            "-9007199254740993"
        ))]),
        Ok(float(-9_007_199_254_740_992.0_f64)),
        "an integer past 2^53 rounds to the nearest double, ties to even"
    );
    assert_eq!(
        apply("float64.add", &[float(1.0_f64), integer(Digits("1"))]),
        Err(PrimitiveError::ArgumentType),
        "a floating-point row refuses an integer"
    );
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
