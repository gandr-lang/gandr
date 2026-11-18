use alloc::vec;
use alloc::vec::Vec;

use gandr_core_term::CertificateEquality;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::equal_certificate_syntax;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::SourceText;

use crate::NativeFault;
use crate::error::LoweringRefusal;
use crate::lower::native::tests::assert_accepted;
use crate::lower::native::tests::body_named;
use crate::lower::native::tests::judged;
use crate::lower::native::tests::outcome_of;
use crate::lower::native::tests::preluded;
use crate::lower::native::tests::refusal_of;
use crate::module::DeclarationOutcome;
use crate::resolve::SurfaceName;
use crate::unit::Unit;
use crate::unit::UnitSource;

/// A unit of one source, laid as the `std` module `std.string`.
///
/// # Specification
/// trivial.
fn homed() -> Unit
{
    Unit::new(vec![
        UnitSource::new(ByteOffset::from(0_usize), Vec::new())
            .homed(SurfaceName::from("std.string")),
    ])
    .expect("one source starts at zero")
}

/// The span of the `n`-th `native` mark of `text`, from its name through its
/// closing parenthesis.
///
/// # Specification
/// trivial.
fn mark(
    text: &str,
    n: usize,
) -> ByteSpan
{
    let start = text
        .match_indices("native(")
        .nth(n)
        .map_or(0_usize, |(at, _)| at);
    let end = text
        .get(start ..)
        .and_then(|rest| rest.find(')'))
        .map_or(start, |close| {
            start.saturating_add(close).saturating_add(1_usize)
        });
    ByteSpan::new(ByteOffset::from(start), ByteOffset::from(end)).expect("a mark's span")
}

/// #7961: a signature of `std` that `native` marks takes the row's value at
/// its declared type, and the checker accepts it. A call of the declaration
/// lowers to the same term as a call of the row's own name.
#[test]
fn a_native_signature_lowers_to_its_row_7961()
{
    let text = include_str!("tests/unformatted/a-native-signature-lowers-to-its-row-7961.gandr");
    let mut arena = CoreArena::new();
    let module = preluded(SourceText::from(text), &homed(), &mut arena);
    let DeclarationOutcome::Completed { body, .. } =
        outcome_of(&module, SurfaceName::from("append"))
    else {
        panic!("`append` takes the row's value");
    };
    assert!(
        matches!(
            arena.value(body),
            Some(&Value::Primitive { primitive, .. }) if primitive.name().as_ref() == "string.append"
        ),
        "the value is the row `string.append`: {:?}",
        arena.value(body)
    );
    assert_eq!(
        equal_certificate_syntax(
            &arena,
            body_named(&module, SurfaceName::from("joined")),
            body_named(&module, SurfaceName::from("direct")),
        ),
        CertificateEquality::Equal,
        "a call of the declaration lowers as a call of the row"
    );
    assert_accepted(&judged(&module, &mut arena));
}

/// #7961: each fault of a `native` mark is refused by name at the mark. The
/// mark names no row; it decorates a body; its type is not the row's; an
/// earlier declaration declares the row; the source is no module of `std`.
#[test]
fn a_faulty_native_mark_is_refused_by_name_7961()
{
    let text = include_str!("tests/unformatted/a-faulty-native-mark-is-refused-by-name-7961.gandr");
    let mut arena = CoreArena::new();
    let module = preluded(SourceText::from(text), &homed(), &mut arena);
    for (name, n, fault) in [
        ("unrowed", 0_usize, NativeFault::NoRow),
        ("bodied", 1_usize, NativeFault::Bodied),
        ("narrow", 2_usize, NativeFault::TypeDiffers),
        ("second", 4_usize, NativeFault::SecondDeclaration),
    ] {
        assert_eq!(
            refusal_of(&module, SurfaceName::from(name)),
            LoweringRefusal::NativeMark {
                span: mark(text, n),
                fault,
            },
            "`{name}` is refused by its fault"
        );
    }
    let first = outcome_of(&module, SurfaceName::from("first"));
    assert!(
        matches!(first, DeclarationOutcome::Completed { .. }),
        "the first declaration of a row stands: {first:?}"
    );

    let outside = include_str!("tests/unformatted/a-native-signature-lowers-to-its-row-7961.gandr");
    let module = preluded(SourceText::from(outside), &Unit::single(), &mut arena);
    assert_eq!(
        refusal_of(&module, SurfaceName::from("append")),
        LoweringRefusal::NativeMark {
            span: mark(outside, 0_usize),
            fault: NativeFault::OutsideStd,
        },
        "a source that is no module of `std` writes no `native` mark"
    );
}
