use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_surface_syntax::SourceText;

use crate::lower::native::tests::assert_accepted;
use crate::lower::native::tests::body_named;
use crate::lower::native::tests::judged;
use crate::lower::native::tests::lowered;
use crate::lower::native::tests::tail_of;
use crate::resolve::SurfaceName;

/// How a conditional's case meets its condition.
#[derive(Clone, Copy, Debug)]
enum Tested
{
    /// The condition, a computation, is bound and the case reads the bound
    /// value.
    Bound,
    /// The condition, a variable's return, is folded into the case.
    Folded,
}

/// The two branches of the case `tests` is, bound to its condition when
/// `tested` says it is, and seen through the answer it is ascribed.
///
/// # Specification
/// trivial.
fn branches(
    arena: &CoreArena,
    tests: ComputationId,
    tested: Tested,
) -> Option<[ComputationId; 2]>
{
    let case = match (tested, arena.computation(tests)) {
        (Tested::Bound, Some(&Computation::Bind(_, case))) => case,
        (Tested::Folded, _) => tests,
        (Tested::Bound, _) => return None,
    };
    let case = match arena.computation(case) {
        Some(&Computation::Ascribe { body, .. }) => body,
        _ => case,
    };
    match arena.computation(case) {
        Some(&Computation::Case { ref branches, .. }) => match **branches {
            [then, otherwise] => Some([then, otherwise]),
            _ => None,
        },
        _ => None,
    }
}

#[test]
fn a_conditional_runs_the_branch_its_condition_selects()
{
    let source =
        include_str!("tests/fixtures/a-conditional-runs-the-branch-its-condition-selects.gandr");
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source), &mut arena);
    for (name, tested) in [
        ("pick", Tested::Folded),
        ("below", Tested::Bound),
        ("answered", Tested::Folded),
        ("literal", Tested::Bound),
    ] {
        let tail = tail_of(&arena, body_named(&module, SurfaceName::from(name)));
        assert!(
            branches(&arena, tail, tested).is_some(),
            "`{name}` cases on its condition over two branches, binding it only when it is a computation: {:?}",
            arena.computation(tail)
        );
    }
    assert_accepted(&judged(&module, &mut arena));
}

#[test]
fn an_else_if_tests_its_own_condition_in_the_false_branch()
{
    let source =
        "def sign(n : Integer) -> -F Integer { if n < 0 { 0 } else if n < 1 { 1 } else { 2 } }\n";
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source), &mut arena);
    let tail = tail_of(&arena, body_named(&module, SurfaceName::from("sign")));
    let Some([_, otherwise]) = branches(&arena, tail, Tested::Bound)
    else {
        panic!(
            "`sign` cases on its first condition: {:?}",
            arena.computation(tail)
        );
    };
    assert!(
        branches(&arena, otherwise, Tested::Bound).is_some(),
        "the false branch binds and cases on the second condition: {:?}",
        arena.computation(otherwise)
    );
    assert_accepted(&judged(&module, &mut arena));
}

#[test]
fn two_else_if_rungs_lower_as_nested_false_branches_6072()
{
    let source = r#"
def rung(n : Integer) -> -F Integer {
    if n < 0 { 0 } else if n < 1 { 1 } else if n < 2 { 2 } else { 3 }
}
"#;
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source), &mut arena);
    let tail = tail_of(&arena, body_named(&module, SurfaceName::from("rung")));
    let Some([_, second]) = branches(&arena, tail, Tested::Bound)
    else {
        panic!(
            "`rung` cases on its first condition: {:?}",
            arena.computation(tail)
        );
    };
    let Some([_, third]) = branches(&arena, second, Tested::Bound)
    else {
        panic!(
            "the first false branch cases on the second condition: {:?}",
            arena.computation(second)
        );
    };
    assert!(
        branches(&arena, third, Tested::Bound).is_some(),
        "the second false branch cases on the third condition: {:?}",
        arena.computation(third)
    );
    assert_accepted(&judged(&module, &mut arena));
}

/// #2089: an `if` that writes its answer has its case ascribed that answer,
/// so it synthesises where nothing states its type, as the computation a
/// `let` binds; one that writes none leaves its case bare.
#[test]
fn a_written_answer_ascribes_the_conditional_2089()
{
    let source =
        include_str!("tests/fixtures/a-written-answer-ascribes-the-conditional-2089.gandr");
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source), &mut arena);
    let tail = tail_of(&arena, body_named(&module, SurfaceName::from("bound")));
    let Some(&Computation::Bind(conditional, _)) = arena.computation(tail)
    else {
        panic!(
            "`bound` runs its conditional: {:?}",
            arena.computation(tail)
        );
    };
    let Some(&Computation::Bind(_, case)) = arena.computation(conditional)
    else {
        panic!(
            "the conditional binds its condition: {:?}",
            arena.computation(conditional)
        );
    };
    assert!(
        matches!(
            arena.computation(case),
            Some(&Computation::Ascribe { body, .. })
                if matches!(arena.computation(body), Some(&Computation::Case { .. }))
        ),
        "the case is ascribed the written answer: {:?}",
        arena.computation(case)
    );
    let stated = tail_of(&arena, body_named(&module, SurfaceName::from("stated")));
    assert!(
        matches!(arena.computation(stated), Some(&Computation::Case { .. })),
        "a conditional writing no answer leaves its case bare: {:?}",
        arena.computation(stated)
    );
    assert_accepted(&judged(&module, &mut arena));
}
