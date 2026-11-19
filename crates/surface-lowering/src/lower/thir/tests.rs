use alloc::sync::Arc;
use alloc::vec;
use alloc::vec::Vec;

use gandr_core_term::CertificateEquality;
use gandr_core_term::CoreArena;
use gandr_core_term::equal_certificate_syntax;
use gandr_runtime_rust_record::Body;
use gandr_runtime_rust_record::Literal;
use gandr_runtime_rust_record::Magnitude;
use gandr_runtime_rust_record::Node;
use gandr_runtime_rust_record::NodeIndex;
use gandr_runtime_rust_record::Outside;
use gandr_runtime_rust_record::Sign;
use gandr_runtime_rust_record::Staging;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::SourceText;

use crate::StagedFault;
use crate::error::LoweringRefusal;
use crate::lower::native::tests::assert_accepted;
use crate::lower::native::tests::body_named;
use crate::lower::native::tests::judged;
use crate::lower::native::tests::outcome_of;
use crate::lower::native::tests::preluded;
use crate::lower::native::tests::refusal_of;
use crate::module::DeclarationOutcome;
use crate::resolve::SurfaceName;
use crate::unit::MarkIndex;
use crate::unit::Staged;
use crate::unit::Unit;
use crate::unit::UnitSource;
use crate::unit::Unstaged;

/// A unit of one source, laid as the `std` module `std.thir`, whose `thir`
/// marks staged `marks`.
///
/// # Specification
/// trivial.
fn homed(marks: Vec<Staged>) -> Unit
{
    Unit::new(vec![
        UnitSource::new(ByteOffset::from(0_usize), Vec::new())
            .homed(SurfaceName::from("std.thir"))
            .staged(marks),
    ])
    .expect("one source starts at zero")
}

/// #8117: a signature that a `thir` mark gives `example`'s staged body takes
/// the body as constructors of `Expr`. It is the value of the same body
/// written by hand, and the checker accepts both.
#[test]
fn a_staged_body_lowers_to_its_constructors_8117()
{
    let mark = |file: &str, function: &str, staging| Staged {
        file: Arc::from(file),
        function: function.into(),
        staging,
    };
    let literal = |n: u128| {
        Node::Literal(Literal {
            sign: Sign::Plus,
            magnitude: Magnitude::from(n),
        })
    };
    let text =
        include_str!("tests/unformatted/a-staged-body-lowers-to-its-constructors-8117.gandr");
    let at = |place: u32| NodeIndex::from(place);
    let body = Body {
        nodes: Vec::from([
            Node::Parameter,
            literal(1),
            literal(0),
            Node::Return(at(2)),
            Node::If {
                condition: at(0),
                then: at(1),
                otherwise: at(3),
            },
            Node::Call {
                callee: "identity".into(),
                argument: at(4),
            },
            Node::Return(at(5)),
        ]),
    };
    let unit = homed(Vec::from([mark(
        "example.rs",
        "example",
        Ok(Staging::Staged(body)),
    )]));
    let mut arena = CoreArena::new();
    let module = preluded(SourceText::from(text), &unit, &mut arena);
    assert!(
        matches!(
            outcome_of(&module, SurfaceName::from("staged")),
            DeclarationOutcome::Completed { .. }
        ),
        "`staged` takes the staged body"
    );
    assert_eq!(
        equal_certificate_syntax(
            &arena,
            body_named(&module, SurfaceName::from("staged")),
            body_named(&module, SurfaceName::from("written")),
        ),
        CertificateEquality::Equal,
        "the staged body is the body written by hand"
    );
    assert_accepted(&judged(&module, &mut arena));
}

/// #8117: each fault of a `thir` mark is refused by name at the mark. The
/// signature has a body; no staged answer matches the mark; no reader is
/// installed; the reader read no body; the body is outside the fragment; the
/// type is no `Expr`; a call names a path that the item mark does not state;
/// the item mark names no constructor of its type.
#[test]
fn each_fault_of_a_thir_mark_is_refused_by_name_8117()
{
    let mark = |file: &str, function: &str, staging| Staged {
        file: Arc::from(file),
        function: function.into(),
        staging,
    };
    let text =
        include_str!("tests/unformatted/each-fault-of-a-thir-mark-is-refused-by-name-8117.gandr");
    // The span of the `n`-th `thir` mark of the text, from its name through
    // its closing parenthesis.
    let span = |n| {
        let start = text
            .match_indices("thir(")
            .nth(n)
            .map_or(0_usize, |(at, _)| at);
        let end = text
            .get(start ..)
            .and_then(|rest| rest.find("))"))
            .map_or(start, |close| {
                start.saturating_add(close).saturating_add(2_usize)
            });
        ByteSpan::new(ByteOffset::from(start), ByteOffset::from(end)).expect("a mark's span")
    };
    let calls = || {
        Ok(Staging::Staged(Body {
            nodes: Vec::from([Node::Parameter, Node::Call {
                callee: "helper".into(),
                argument: NodeIndex::from(0_u32),
            }]),
        }))
    };
    let unit = homed(Vec::from([
        mark("a.rs", "noReader", Err(Unstaged::NoReader)),
        mark(
            "a.rs",
            "unread",
            Err(Unstaged::Unread(Arc::from("no such crate"))),
        ),
        mark(
            "a.rs",
            "outside",
            Ok(Staging::Outside(Outside::Node("Binary".into()))),
        ),
        mark(
            "a.rs",
            "notExpr",
            Ok(Staging::Staged(Body {
                nodes: Vec::from([Node::Parameter]),
            })),
        ),
        mark("a.rs", "unmapped", calls()),
        mark("a.rs", "broken", calls()),
    ]));
    let mut arena = CoreArena::new();
    let module = preluded(SourceText::from(text), &unit, &mut arena);
    let at = MarkIndex::from;
    for (name, n, fault) in [
        ("bodied", 0_usize, StagedFault::Bodied),
        ("unanswered", 1_usize, StagedFault::Unanswered),
        ("noReader", 2_usize, StagedFault::NoReader),
        ("unread", 3_usize, StagedFault::Unread(at(1))),
        ("outside", 4_usize, StagedFault::Outside(at(2))),
        ("notExpr", 5_usize, StagedFault::NotExpr),
        ("unmapped", 6_usize, StagedFault::Unmapped {
            mark: at(4),
            node: NodeIndex::from(1_u32),
        }),
        ("broken", 7_usize, StagedFault::ItemMark),
    ] {
        assert_eq!(
            refusal_of(&module, SurfaceName::from(name)),
            LoweringRefusal::StagedBody {
                span: span(n),
                fault,
            },
            "`{name}` is refused by its fault"
        );
    }
}
