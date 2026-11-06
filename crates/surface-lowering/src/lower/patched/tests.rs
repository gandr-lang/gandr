use alloc::collections::BTreeSet;
use alloc::format;

use gandr_core_term::Computation;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueType;
use gandr_kernel_term::Literal;
use gandr_surface_syntax::SourceText;

use crate::error::FormFault;
use crate::error::FragmentBoundary;
use crate::error::LoweringRefusal;
use crate::lower::native::tests::assert_accepted;
use crate::lower::native::tests::body_named;
use crate::lower::native::tests::judged;
use crate::lower::native::tests::lowered;
use crate::lower::native::tests::refusal_of;
use crate::lower::native::tests::tail_of;
use crate::resolve::SurfaceName;
use crate::unbuilt::Unbuilt;

/// A record type member with two faces that meet at the port.
const CONFIG: &str = include_str!("tests/unformatted/config.gandr");

#[test]
fn a_patched_type_is_the_record_of_its_free_fields()
{
    // Both spellings, and a quantified function whose stage sits beside a
    // patched parameter: the stage is marked, the patch is not.
    let source = format!(
        include_str!("tests/unformatted/a-patched-type-is-the-record-of-its-free-fields.gandr"),
        CONFIG = CONFIG
    );
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let report = judged(&module, &mut arena);
    assert_accepted(&report);
    for name in ["fielded", "faced", "ascii", "placed"] {
        let body = body_named(&module, SurfaceName::from(name));
        let Some(&Value::Record(ref fields)) = arena.value(body)
        else {
            panic!("`{name}` is a record");
        };
        assert_eq!(fields.len(), 1, "`{name}` holds its one free field alone");
    }
}

#[test]
fn a_base_named_by_a_type_member_keeps_the_name()
{
    // Three bases written by the member's name, a fourth beside a stage, and
    // a record written in place, which keeps no name.
    let source = format!(
        include_str!("tests/unformatted/a-patched-type-is-the-record-of-its-free-fields.gandr"),
        CONFIG = CONFIG
    );
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let members = module.origins().members();
    let named: BTreeSet<(usize, Option<&str>)> = members
        .iter()
        .map(|&(_, name)| {
            let (start, end) = (
                usize::from(name.span().start()),
                usize::from(name.span().end()),
            );
            (start, source.get(start .. end))
        })
        .collect();
    let written: BTreeSet<(usize, Option<&str>)> = source
        .match_indices("Config[")
        .map(|(start, _)| (start, Some("Config")))
        .collect();
    assert_eq!(
        named, written,
        "each base written by the member's name keeps the name"
    );
    assert!(
        members
            .iter()
            .all(|&(ty, _)| matches!(arena.value_type(ty), Some(&ValueType::Record(_)))),
        "the name stands for the record the patched type is over"
    );
}

#[test]
fn a_fixed_field_reads_its_value_back()
{
    let source = format!(
        include_str!("tests/unformatted/a-fixed-field-reads-its-value-back.gandr"),
        CONFIG = CONFIG
    );
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let report = judged(&module, &mut arena);
    assert_accepted(&report);
    let returned = |name: &str| {
        let tail = tail_of(&arena, body_named(&module, SurfaceName::from(name)));
        let Some(&Computation::Return(value)) = arena.computation(tail)
        else {
            panic!("`{name}` returns a value: {:?}", arena.computation(tail));
        };
        arena.value(value).cloned()
    };
    assert!(
        matches!(returned("port"), Some(Value::Literal(Literal::Integer(_)))),
        "a fixed field reads the number the bracket fixes"
    );
    // A boolean stands ascribed its type, around the injection it is.
    let tls = match returned("tls") {
        Some(Value::Ascribe { value, .. }) => arena.value(value).cloned(),
        other => other,
    };
    assert!(
        matches!(tls, Some(Value::Injection(..))),
        "a face's field reads the boolean its value fixes: {tls:?}"
    );
    let tail = tail_of(&arena, body_named(&module, SurfaceName::from("host")));
    assert!(
        matches!(
            arena.computation(tail),
            Some(Computation::RecordProjection(_, label)) if label.as_ref() == "host"
        ),
        "a free field projects the record: {:?}",
        arena.computation(tail)
    );
}

#[test]
fn a_bracket_naming_what_its_base_lacks_is_refused_by_the_name()
{
    let source = format!(
        include_str!(
            "tests/unformatted/a-bracket-naming-what-its-base-lacks-is-refused-by-the-name.gandr"
        ),
        CONFIG = CONFIG
    );
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    for (declared, named, why) in [
        ("moded", "mode", "a fixed field the record lacks"),
        ("remote", "remote", "a face the type member does not name"),
        ("leaking", "host", "a field of the value outside the face"),
        ("atomic", "port", "a base that is no record"),
    ] {
        let refusal = refusal_of(&module, SurfaceName::from(declared));
        assert!(
            matches!(refusal, LoweringRefusal::UnresolvedName { name, .. } if name == SurfaceName::from(named)),
            "{why} is refused at `{named}`: {refusal:?}"
        );
    }
    assert!(
        matches!(
            refusal_of(&module, SurfaceName::from("partial")),
            LoweringRefusal::MalformedForm {
                fault: FormFault::MissingOperand,
                ..
            }
        ),
        "a face's value states every field of the face"
    );
}

#[test]
fn a_fixed_value_the_lowering_does_not_read_leaves_the_fragment()
{
    let source = format!(
        include_str!(
            "tests/unformatted/a-fixed-value-the-lowering-does-not-read-leaves-the-fragment.gandr"
        ),
        CONFIG = CONFIG
    );
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    for (name, why) in [
        ("named", "a fixed name is not read back"),
        ("bound", "a face's value is a record written in place"),
    ] {
        assert!(
            matches!(
                refusal_of(&module, SurfaceName::from(name)),
                LoweringRefusal::OutOfFragment {
                    boundary: FragmentBoundary::Unadmitted(Unbuilt::FixedValue),
                    ..
                }
            ),
            "{why}"
        );
    }
    let report = judged(&module, &mut arena);
    assert_accepted(&report);
}
