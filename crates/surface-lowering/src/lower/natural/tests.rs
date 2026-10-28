use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;

use gandr_core_term::ConstructorTag;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Magnitude;
use gandr_surface_syntax::SourceText;

use super::Digit;
use super::binary_digits;
use crate::lower::native::tests::assert_checked;
use crate::lower::native::tests::preluded;
use crate::module::DeclarationOutcome;
use crate::module::LoweredDeclaration;
use crate::module::LoweredModule;
use crate::resolve::SurfaceName;
use crate::unit::Unit;

/// The value `name`'s definition lowers to, past an ascription.
///
/// # Specification
/// trivial.
fn body(
    module: &LoweredModule<'_>,
    arena: &CoreArena,
    name: SurfaceName<'_>,
) -> ValueId
{
    let outcome = module
        .declarations()
        .iter()
        .find(|declaration| declaration.name() == name)
        .map(LoweredDeclaration::outcome);
    let body = match outcome {
        Some(DeclarationOutcome::Completed { body, .. } | DeclarationOutcome::Bodied { body }) => {
            body
        },
        other => panic!("`{name:?}` lowers complete: {other:?}"),
    };
    match arena.value(body) {
        Some(&Value::Ascribe { value, .. }) => value,
        _ => body,
    }
}

/// The constructor term `value` is, read as a natural: `Zero`, or `Positive`
/// over a positive.
///
/// # Specification
/// trivial.
fn natural_spelled(
    arena: &CoreArena,
    value: ValueId,
) -> String
{
    match arena.value(value) {
        Some(&Value::Constructor {
            tag, ref fields, ..
        }) => match *fields.as_slice() {
            [] if tag == ConstructorTag::from(0_usize) => String::from("Zero"),
            [positive] if tag == ConstructorTag::from(1_usize) => {
                format!("Positive({})", positive_spelled(arena, positive))
            },
            _ => format!("no natural: {tag:?} over {fields:?}"),
        },
        other => format!("{other:?}"),
    }
}

/// The constructor term `value` is, read as a positive: `One`, or `Bit0` or
/// `Bit1` over a positive, each digit opened in turn and all closed after the
/// `One` that ends them.
///
/// # Specification
/// trivial.
fn positive_spelled(
    arena: &CoreArena,
    value: ValueId,
) -> String
{
    let mut opened = String::new();
    let mut depth = 0_usize;
    let mut at = value;
    let tail = loop {
        let Some(&Value::Constructor {
            tag, ref fields, ..
        }) = arena.value(at)
        else {
            break format!("{:?}", arena.value(at));
        };
        let (digit, inner) = match *fields.as_slice() {
            [] if tag == ConstructorTag::from(0_usize) => break String::from("One"),
            [inner] if tag == ConstructorTag::from(1_usize) => ("Bit0(", inner),
            [inner] if tag == ConstructorTag::from(2_usize) => ("Bit1(", inner),
            _ => break format!("no positive: {tag:?} over {fields:?}"),
        };
        opened.push_str(digit);
        depth = depth.saturating_add(1);
        at = inner;
    };
    format!("{opened}{tail}{}", ")".repeat(depth))
}

#[test]
fn a_numeral_at_nat_is_its_binary_constructor_term_3287()
{
    // A numeral annotated at the prelude's `Nat` is the constructor term its
    // binary digits spell, the lowest outermost: zero is `Zero`, five is one,
    // zero, one read from the outside in, and two to the thirty-first is
    // thirty-one doublings of one. Each checks at `Nat`.
    let source = "\
def zero = (0 : Nat) ;
def five = (5 : Nat) ;
def large = (2147483648 : Nat) ;
";
    let (text, unit) = crate::prelude::lay(SourceText::from(source), &Unit::single()).unwrap();
    let mut arena = CoreArena::new();
    let module = preluded(SourceText::from(text.as_str()), &unit, &mut arena);
    let large = format!("Positive({}One{})", "Bit0(".repeat(31), ")".repeat(31));
    for (name, expected) in [
        ("zero", String::from("Zero")),
        ("five", String::from("Positive(Bit1(Bit0(One)))")),
        ("large", large),
    ] {
        assert_eq!(
            natural_spelled(&arena, body(&module, &arena, SurfaceName::from(name))),
            expected,
            "`{name}` is its binary constructor term"
        );
    }
    assert_checked(&module, &mut arena);
}

#[test]
fn a_numeral_at_a_source_s_own_nat_stays_an_integer_3287()
{
    // A source's own `Nat` shadows the prelude's where the annotation is
    // written, so the numeral stays the integer its lexeme is.
    let source = "\
data Nat : Type { Zero : Nat; Succ : (n : Nat) --> Nat; }
def five = (5 : Nat) ;
";
    let (text, unit) = crate::prelude::lay(SourceText::from(source), &Unit::single()).unwrap();
    let mut arena = CoreArena::new();
    let module = preluded(SourceText::from(text.as_str()), &unit, &mut arena);
    assert!(
        matches!(
            arena.value(body(&module, &arena, SurfaceName::from("five"))),
            Some(&Value::Literal(Literal::Integer(_)))
        ),
        "the source's `Nat` is no binary natural"
    );
}

#[test]
fn a_magnitude_s_binary_digits_are_its_halvings_3287()
{
    let digits = |decimal: &str| {
        binary_digits(&Magnitude::from_decimal_text(String::from(decimal)).unwrap())
    };
    let thirty_one: Vec<Digit> = core::iter::repeat_n(Digit::Zero, 31)
        .chain([Digit::One])
        .collect();
    for (decimal, expected) in [
        ("0", Vec::new()),
        ("1", Vec::from([Digit::One])),
        ("5", Vec::from([Digit::One, Digit::Zero, Digit::One])),
        (
            "10",
            Vec::from([Digit::Zero, Digit::One, Digit::Zero, Digit::One]),
        ),
        ("2147483648", thirty_one),
    ] {
        assert_eq!(
            digits(decimal),
            expected,
            "{decimal}'s digits, the lowest first"
        );
    }
}
