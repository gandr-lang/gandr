use alloc::format;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::CertificateEquality;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::equal_certificate_syntax;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::NodeIndex;
use gandr_surface_syntax::SourceText;

use super::Leaves;
use crate::error::FragmentBoundary;
use crate::error::LoweringRefusal;
use crate::fixture::grammar;
use crate::fixture::parsed;
use crate::fixture::span;
use crate::form::FormName;
use crate::form::Shape;
use crate::form::shape_of;
use crate::lower::Fuel;
use crate::lower::Lowerer;
use crate::lower::LoweringBudget;
use crate::lower::native::tests::assert_accepted;
use crate::lower::native::tests::body_named;
use crate::lower::native::tests::judged;
use crate::lower::native::tests::lowered;
use crate::lower::native::tests::refusal_of;
use crate::lower::native::tests::tail_of;
use crate::module::collect;
use crate::namespace::Recognition;
use crate::resolve::SurfaceName;

/// The naturals every witness matches on.
const NAT: &str = "data Nat : Type { Zero : Nat; Succ : (n : Nat) --> Nat; }\n";

/// The bytes `needle` spells in `source`, which spells it once.
///
/// # Specification
/// - requires: `source` spells `needle` exactly once.
/// - ensures: the span of that spelling.
/// - fails: never.
/// - panics: if `needle` is spelled no time or more than once.
///
/// # Adequacy
/// - hypothesis: L3 — the survey and refusal witnesses locate their forms here.
/// - witness: `lower::exits::tests::code_no_path_reaches_is_refused`
#[spec(ensures: |ret| source.as_ref().get(usize::from(ret.start()) .. usize::from(ret.end())) == Some(needle.as_ref()))]
fn spelled(
    source: SourceText<'_>,
    needle: SourceText<'_>,
) -> ByteSpan
{
    let (text, wanted): (&str, &str) = (source.as_ref(), needle.as_ref());
    let Some(start) = text.find(wanted)
    else {
        panic!("`{needle}` is spelled");
    };
    assert_eq!(
        text.rfind(wanted),
        Some(start),
        "`{needle}` is spelled once"
    );
    let Some(end) = start.checked_add(wanted.len())
    else {
        panic!("a spelling ends inside the source");
    };

    span(ByteOffset::from(start), ByteOffset::from(end))
}

/// Assert that every form spelling exactly each needle of `source` surveys
/// as the answer beside it.
///
/// # Specification
/// trivial.
fn assert_surveyed(
    source: SourceText<'_>,
    expected: &[(SourceText<'_>, Leaves)],
)
{
    let pbg = grammar();
    let tree = parsed(&pbg, source);
    let mut fuel = Fuel::new(LoweringBudget::DEFAULT);
    let collected = collect(&pbg, &tree, &mut fuel).expect("the module collects");
    let mut lowerer = Lowerer::new(&pbg, &tree, collected, fuel, Recognition::default());
    lowerer
        .survey()
        .expect("the survey stays within the allowance");
    for &(needle, leaves) in expected {
        let at = spelled(source, needle);
        let surveyed: Vec<Leaves> = (0 .. usize::from(tree.node_count()))
            .map(NodeIndex::from)
            .filter(|&position| {
                tree.node(position).is_some_and(|node| {
                    node.span() == at && matches!(shape_of(&pbg, node), Ok(Shape::Form { .. }))
                })
            })
            .map(|position| lowerer.leaves_at(position))
            .collect();
        assert!(!surveyed.is_empty(), "`{needle}` is a form");
        assert!(
            surveyed.iter().all(|&held| held == leaves),
            "`{needle}` surveys as {leaves:?}, not {surveyed:?}"
        );
    }
}

/// Every computation reachable from `root` through binds, lambdas and
/// matches.
///
/// # Specification
/// trivial.
fn reachable(
    arena: &CoreArena,
    root: ComputationId,
) -> Vec<ComputationId>
{
    let mut seen = Vec::new();
    let mut pending = Vec::from([root]);
    while let Some(next) = pending.pop() {
        seen.push(next);
        match arena.computation(next) {
            | Some(&Computation::Bind(first, second)) => pending.extend([first, second]),
            | Some(&Computation::Lambda(under)) => pending.push(under),
            | Some(&Computation::DataCase { ref branches, .. }) => {
                pending.extend(branches.iter().copied());
            },
            | Some(&Computation::Case { ref branches, .. }) => {
                pending.extend(branches.iter().copied());
            },
            | _ => {},
        }
    }

    seen
}

/// Assert that the bodies of `lowered` and `written` are the same syntax.
///
/// # Specification
/// trivial.
fn assert_same_body(
    module: &crate::module::LoweredModule<'_>,
    arena: &CoreArena,
    (lowered, written): (SurfaceName<'_>, SurfaceName<'_>),
)
{
    let (left, right) = (body_named(module, lowered), body_named(module, written));
    assert_eq!(
        equal_certificate_syntax(arena, left, right),
        CertificateEquality::Equal,
        "`{lowered}` lowers to the body `{written}` spells by hand"
    );
}

#[test]
fn the_paths_of_a_computation_are_surveyed_through_nesting()
{
    let source = format!(
        "{NAT}def f(n : Nat) -> -F Nat {{\n\
         run a <- case n {{ Zero => pure n, Succ(p) => pure p }} ;\n\
         run b <- case n {{ Zero => return n, Succ(p) => pure p }} ;\n\
         run c <- case n {{ Zero => pure n, Succ(p) => case p {{ Zero => return p, Succ(q) => pure q }} }} ;\n\
         run d <- case n {{ Zero => pure n, Succ(p) => case p {{ Zero => pure p, Succ(q) => pure q }} }} ;\n\
         run e <- case n {{ Zero => return n, Succ(p) => case p {{ Zero => return p, Succ(q) => return q }} }} ;\n\
         case n {{ Zero => return n, Succ(p) => return p }}\n\
         }}\n\
         def g : +U (-F Nat) ;\ndef g = thunk {{ return Zero }} ;\n\
         def h : +U (-F Nat & -F Nat) ;\ndef h = thunk {{ &{{.0 => return Succ(Zero), .1 => pure Zero}} }} ;\n"
    );
    assert_surveyed(SourceText::from(source.as_str()), &[
        (
            "case n { Zero => pure n, Succ(p) => pure p }",
            Leaves::Never,
        ),
        (
            "case n { Zero => return n, Succ(p) => pure p }",
            Leaves::Sometimes,
        ),
        (
            "case n { Zero => pure n, Succ(p) => case p { Zero => return p, Succ(q) => pure q } }",
            Leaves::Sometimes,
        ),
        (
            "case p { Zero => return p, Succ(q) => pure q }",
            Leaves::Sometimes,
        ),
        (
            "case n { Zero => pure n, Succ(p) => case p { Zero => pure p, Succ(q) => pure q } }",
            Leaves::Never,
        ),
        (
            "case n { Zero => return n, Succ(p) => case p { Zero => return p, Succ(q) => return q } }",
            Leaves::Always,
        ),
        (
            "case p { Zero => return p, Succ(q) => return q }",
            Leaves::Always,
        ),
        (
            "case n { Zero => return n, Succ(p) => return p }",
            Leaves::Always,
        ),
        ("thunk { return Zero }", Leaves::Never),
        ("return Zero", Leaves::Always),
        ("&{.0 => return Succ(Zero), .1 => pure Zero}", Leaves::Never),
    ].map(|(needle, leaves)| (SourceText::from(needle), leaves)));
}

#[test]
fn a_bound_match_continues_its_block_at_each_local_arm()
{
    let source = format!(
        "{NAT}def once(n : Nat) -> -F Nat {{ run m <- case n {{ Zero => return n, Succ(p) => pure p }} ; return Succ(m) }}\n\
         def once_by_hand(n : Nat) -> -F Nat {{ case n {{ Zero => return n, Succ(p) => return Succ(p) }} }}\n\
         def kept(n : Nat) -> -F Nat {{ run m <- case n -> -F Nat {{ Zero => pure n, Succ(p) => pure p }} ; return Succ(m) }}\n"
    );
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    assert_same_body(
        &module,
        &arena,
        (SurfaceName::from("once"), SurfaceName::from("once_by_hand")),
    );
    let kept = tail_of(&arena, body_named(&module, SurfaceName::from("kept")));
    assert!(
        matches!(
            arena.computation(kept),
            Some(&Computation::Bind(bound, _))
                if matches!(arena.computation(bound), Some(Computation::DataCase { .. }))
        ),
        "a match holding no exit binds the rest of its block once"
    );
    assert_accepted(&judged(&module, &mut arena));
}

#[test]
fn an_exit_under_nesting_leaves_its_function()
{
    let source = format!(
        "{NAT}def pick(n : Nat) -> -F Nat {{\n\
         run m <- case n {{\n\
         Zero => return n,\n\
         Succ(p) => {{ run q <- case p {{ Zero => return n, Succ(r) => pure r }} ; pure q }},\n\
         }} ;\n\
         return Succ(m)\n\
         }}\n\
         def pick_by_hand(n : Nat) -> -F Nat {{\n\
         case n {{\n\
         Zero => return n,\n\
         Succ(p) => case p {{ Zero => return n, Succ(r) => return Succ(r) }},\n\
         }}\n\
         }}\n\
         def deep(n : Nat) -> -F Nat {{\n\
         run m <- case n {{ Succ(Succ(q)) => return q, Succ(Zero) => pure n, Zero => pure n }} ;\n\
         return Succ(m)\n\
         }}\n\
         def deep_by_hand(n : Nat) -> -F Nat {{\n\
         case n {{ Succ(Succ(q)) => return q, Succ(Zero) => return Succ(n), Zero => return Succ(n) }}\n\
         }}\n"
    );
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    assert_same_body(
        &module,
        &arena,
        (SurfaceName::from("pick"), SurfaceName::from("pick_by_hand")),
    );
    assert_same_body(
        &module,
        &arena,
        (SurfaceName::from("deep"), SurfaceName::from("deep_by_hand")),
    );
    for name in ["pick", "deep"] {
        let tail = tail_of(&arena, body_named(&module, SurfaceName::from(name)));
        let binds: Vec<ComputationId> = reachable(&arena, tail)
            .into_iter()
            .filter(|&node| matches!(arena.computation(node), Some(&Computation::Bind(..))))
            .collect();
        assert!(
            binds.is_empty(),
            "every exit of `{name}` ends its body, under no bind: {binds:?}"
        );
    }
    assert_accepted(&judged(&module, &mut arena));
}

#[test]
fn code_no_path_reaches_is_refused()
{
    let source = format!(
        "{NAT}def after(n : Nat) -> -F Nat {{ run m <- case n {{ Zero => return n, Succ(p) => return p }} ; run k <- pure m ; return k }}\n\
         def last(n : Nat) -> -F Nat {{ run m <- case n {{ Zero => return n, Succ(p) => return p }} ; return m }}\n\
         def nested(n : Nat) -> -F Nat {{ case n {{ Zero => return n, Succ(p) => {{ run q <- become pure p ; return Succ(q) }} }} }}\n"
    );
    let module = lowered(SourceText::from(source.as_str()), &mut CoreArena::new());
    for (name, unreached) in [
        ("after", "run k <- pure m ; return k"),
        ("last", "return m"),
        ("nested", "return Succ(q)"),
    ] {
        assert_eq!(
            refusal_of(&module, SurfaceName::from(name)),
            LoweringRefusal::Unreachable {
                span: spelled(
                    SourceText::from(source.as_str()),
                    SourceText::from(unreached)
                ),
            },
            "`{name}` is refused at the code after a statement that always exits"
        );
    }
}

#[test]
fn a_path_missing_its_exit_is_refused_where_it_ends()
{
    let source = format!(
        "{NAT}def missing(n : Nat) -> -F Nat {{ case n {{ Zero => return n, Succ(p) => {{ run q <- case p {{ Zero => return p, Succ(r) => pure r }} ; pure q }} }} }}\n\
         def inner(n : Nat) -> -F Nat {{ run m <- case n {{ Zero => return n, Succ(p) => case p {{ Zero => return p, Succ(r) => pure r }} }} ; pure Succ(m) }}\n"
    );
    let module = lowered(SourceText::from(source.as_str()), &mut CoreArena::new());
    for (name, end) in [("missing", "pure q"), ("inner", "pure Succ(m)")] {
        assert_eq!(
            refusal_of(&module, SurfaceName::from(name)),
            LoweringRefusal::MissingExit {
                span: spelled(SourceText::from(source.as_str()), SourceText::from(end)),
            },
            "`{name}` is refused where its path ends, not at a local end of a bound match"
        );
    }
}

#[test]
fn a_match_continuing_its_block_answers_what_the_block_does()
{
    let source = format!(
        "{NAT}def stated(n : Nat) -> -F Nat {{ run m <- case n -> (-F Nat) {{ Zero => return n, Succ(p) => pure p }} ; return m }}\n\
         def taken(n : Nat) -> -F (+U (-F Nat)) {{ run m <- case n {{ Zero => return thunk {{ return n }}, Succ(p) => pure p }} ; return thunk {{ return Succ(m) }} }}\n"
    );
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let refused = refusal_of(&module, SurfaceName::from("stated"));
    let written = spelled(
        SourceText::from(source.as_str()),
        SourceText::from("case n -> (-F Nat)"),
    );
    let answer = span(
        ByteOffset::from(usize::from(written.end()).saturating_sub("(-F Nat)".len())),
        written.end(),
    );
    assert!(
        matches!(
            refused,
            LoweringRefusal::OutOfFragment { span, form, boundary: FragmentBoundary::JoinsBlock, .. }
                if form == FormName::CASE && span == answer
        ),
        "a written answer on a match continuing its block is refused at itself: {refused:?}"
    );
    assert_accepted(&judged(&module, &mut arena));
}
