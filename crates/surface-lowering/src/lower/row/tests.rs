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

/// #8074: a type signature of `std` with one parameter and no body, which a
/// `builtin` mark binds to the row of a former, applies that former. A list
/// literal checks at the declared former, and a list of words and a number do
/// not.
#[test]
fn a_type_signature_with_a_parameter_reads_its_former_8074()
{
    let text = include_str!(
        "tests/unformatted/a-type-signature-with-a-parameter-reads-its-former-8074.gandr"
    );
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
        vec![true, false, false],
        "`three` checks, and `words` and `number` are refused: {report:?}"
    );
}

/// #8074: a former's row binds one parameter and an atom's row binds none. A
/// type signature that binds another count is refused at its mark, as of a
/// type that is not the row's.
#[test]
fn a_builtin_type_signature_binds_the_parameters_of_its_row_8074()
{
    let text = include_str!(
        "tests/unformatted/a-builtin-type-signature-binds-the-parameters-of-its-row-8074.gandr"
    );
    let mark = |n| {
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
    for (name, n) in [("Bare", 0_usize), ("Wide", 1_usize)] {
        assert_eq!(
            refusal_of(&module, SurfaceName::from(name)),
            LoweringRefusal::BuiltinMark {
                span: mark(n),
                fault: BuiltinFault::TypeDiffers,
            },
            "`{name}` binds a count of parameters that its row does not"
        );
    }
}

/// #8139: a port at a name that no scope of its source binds refuses its
/// theory at the name's bytes, with the reason that the description read gave
/// before the resolve. A result and an input are refused alike.
#[test]
fn a_port_sort_no_scope_binds_is_refused_at_its_bytes_8139()
{
    use gandr_theory_levitation::WfKind;
    use quenchant_shape::shape::Maybe;

    for (text, theory, unbound) in [
        (
            "theory FailNonsense where { sort Reason : Type; oper raise : (r : Reason) --> Nonsense; }",
            "FailNonsense",
            "Nonsense",
        ),
        (
            "theory Fail where { oper raise : (r : Reason) --> Void; }",
            "Fail",
            "Reason",
        ),
    ] {
        let start = text.rfind(unbound).expect("the port is written");
        let at = ByteSpan::new(
            ByteOffset::from(start),
            ByteOffset::from(start.saturating_add(unbound.len())),
        )
        .expect("the name's span");
        let mut arena = CoreArena::new();
        let module = preluded(SourceText::from(text), &Unit::single(), &mut arena);
        let refusal = refusal_of(&module, SurfaceName::from(theory));
        assert!(
            matches!(
                refusal,
                LoweringRefusal::IllFormedDescription {
                    span,
                    fault,
                    kind: WfKind::UnknownPortSort,
                    subjects: [Maybe::Present(operation), Maybe::Present(sort)],
                } if span == at
                    && fault == at
                    && operation == SurfaceName::from("raise")
                    && sort == SurfaceName::from(unbound)
            ),
            "`{theory}` is refused at the unbound `{unbound}`: {refusal:?}"
        );
    }
}

/// #8139: a name that the scope of its source binds reads that binding, and
/// the table of atoms answers only a name that no scope binds. A source binds
/// `Integer` to the strings, so a word checks at it and a number does not.
#[test]
fn the_scope_wins_over_the_atom_8139()
{
    let text = include_str!("tests/unformatted/the-scope-wins-over-the-atom-8139.gandr");
    let mut arena = CoreArena::new();
    let module = preluded(SourceText::from(text), &Unit::single(), &mut arena);
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
        vec![true, false],
        "`word` checks at the source's `Integer`, and `number` is refused: {report:?}"
    );
}

/// #8139: a port names the type member that the scope of its theory's source
/// binds, in a unit whose other source uses the theory. The first source
/// binds `Integer` to the strings and declares `Shout`, whose `say` gives an
/// `Integer`. The second source imports it and sees the atom `Integer`. A
/// model whose `say` gives a string checks, and a model whose `say` gives the
/// atom is refused.
#[test]
fn a_port_sort_reads_the_binding_of_its_theory_s_source_8139()
{
    use alloc::format;

    use crate::unit::ImportTarget;
    use crate::unit::SourceIndex;

    let shout = include_str!(
        "tests/unformatted/a-port-sort-reads-the-binding-of-its-theory-s-source-8139-shout.gandr"
    );
    let own = include_str!(
        "tests/unformatted/a-port-sort-reads-the-binding-of-its-theory-s-source-8139.gandr"
    );
    let text = format!("{shout}{own}");
    let unit = Unit::new(vec![
        UnitSource::new(ByteOffset::from(0_usize), Vec::new()),
        UnitSource::new(ByteOffset::from(shout.len()), vec![ImportTarget::Source(
            SourceIndex::from(0_usize),
        )]),
    ])
    .expect("two sources make a unit");
    let mut arena = CoreArena::new();
    let module = preluded(SourceText::from(text.as_str()), &unit, &mut arena);
    let report = judged(&module, &mut arena);
    let said: Vec<bool> = module
        .declarations()
        .iter()
        .filter(|declaration| !matches!(declaration.outcome(), DeclarationOutcome::Refused(_)))
        .zip(report.judged())
        .filter(|&(declaration, _)| declaration.name() == SurfaceName::from("say"))
        .map(|(_, judged)| {
            matches!(
                judged.verdict(),
                gandr_core_checker::Verdict::Checked { .. }
            )
        })
        .collect();
    assert_eq!(
        said,
        vec![true, true, false, false],
        "each model declares its `say` twice: `Loud`'s word checks and `Quiet`'s number is \
         refused, so the port names the first source's `Integer`, the strings: {report:?}"
    );
}
