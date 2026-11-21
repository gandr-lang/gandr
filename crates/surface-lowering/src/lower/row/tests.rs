use alloc::vec;
use alloc::vec::Vec;

use gandr_core_term::CertificateEquality;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::equal_certificate_syntax;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::SourceText;

use crate::BuiltinFault;
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

/// #8071: a signature of `std` that a `builtin` mark binds to a given row
/// takes the row's value at its declared type, and the checker accepts it. A
/// call of the declaration lowers to the same term as a call of the row's own
/// name.
#[test]
fn a_given_row_lowers_to_its_value_8071()
{
    let text = include_str!("tests/unformatted/a-given-row-lowers-to-its-value-8071.gandr");
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

/// #8071: each fault of a `builtin` mark is refused by name at the mark. In a
/// module of `std`: the key names no row; a given row's declaration has a
/// body; its type is not the row's; an earlier declaration holds the given
/// row; a found row's declaration has no body; an earlier declaration holds
/// the role. Outside `std`, the mark is refused as outside the toolchain
/// first, also when its key names no row.
#[test]
fn each_fault_of_a_builtin_mark_is_refused_by_name_8071()
{
    let text = include_str!(
        "tests/unformatted/each-fault-of-a-builtin-mark-is-refused-by-name-8071.gandr"
    );
    // The span of the `n`-th `builtin` mark of a text, from its name through
    // its closing parenthesis.
    let mark = |text: &str, n| {
        let start = text
            .match_indices("builtin(")
            .nth(n)
            .map_or(0_usize, |(at, _)| at);
        let end = text
            .get(start ..)
            .and_then(|rest| rest.find(')'))
            .map_or(start, |close| {
                start.saturating_add(close).saturating_add(1_usize)
            });
        ByteSpan::new(ByteOffset::from(start), ByteOffset::from(end)).expect("a mark's span")
    };
    let mut arena = CoreArena::new();
    let module = preluded(SourceText::from(text), &homed(), &mut arena);
    for (name, n, fault) in [
        ("unrowed", 0_usize, BuiltinFault::NoRow),
        ("bodied", 1_usize, BuiltinFault::Bodied),
        ("narrow", 2_usize, BuiltinFault::TypeDiffers),
        ("second", 4_usize, BuiltinFault::Repeated),
        ("unbodied", 5_usize, BuiltinFault::Unbodied),
        ("again", 7_usize, BuiltinFault::Repeated),
    ] {
        assert_eq!(
            refusal_of(&module, SurfaceName::from(name)),
            LoweringRefusal::BuiltinMark {
                span: mark(text, n),
                fault,
            },
            "`{name}` is refused by its fault"
        );
    }
    let first = outcome_of(&module, SurfaceName::from("first"));
    assert!(
        matches!(first, DeclarationOutcome::Completed { .. }),
        "the first declaration of a given row stands: {first:?}"
    );

    let module = preluded(SourceText::from(text), &Unit::single(), &mut arena);
    for (name, n) in [("unrowed", 0_usize), ("first", 3_usize), ("held", 6_usize)] {
        assert_eq!(
            refusal_of(&module, SurfaceName::from(name)),
            LoweringRefusal::BuiltinMark {
                span: mark(text, n),
                fault: BuiltinFault::OutsideToolchain,
            },
            "`{name}` outside `std` is refused as outside the toolchain"
        );
    }
}

/// #8073: a type signature of `std` with no body, which a `builtin` mark binds
/// to the row of an atom, reads the atom of that row. A value at the declared
/// name checks at the name that the table answers, in each direction, and it
/// does not check at another atom.
#[test]
fn a_type_signature_under_builtin_reads_its_atom_8073()
{
    let text =
        include_str!("tests/unformatted/a-type-signature-under-builtin-reads-its-atom-8073.gandr");
    let mut arena = CoreArena::new();
    let module = preluded(SourceText::from(text), &homed(), &mut arena);
    let report = judged(&module, &mut arena);
    let verdicts: Vec<bool> = report
        .judged()
        .iter()
        .map(|judged| {
            matches!(
                judged.verdict(),
                gandr_core_checker::Verdict::Checked { .. }
            )
        })
        .collect();
    assert_eq!(
        verdicts,
        vec![true, true, false],
        "`onward` and `back` check, and `wide` is refused: {report:?}"
    );
}
