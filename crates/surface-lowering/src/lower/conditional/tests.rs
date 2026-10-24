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
    let source = "def pick(b : Bool) -> -F Integer { if b { return 1 } else { return 2 } }\n\
                  def below(n : Integer) -> -F Integer { if n < 3 { 1 } else { 2 } }\n\
                  def answered(b : Bool) -> -F Integer { if b -> -F Integer { 1 } else { 2 } }\n\
                  def literal() -> -F Integer { if true { return 1 } else { return 2 } }\n";
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

/// #2089: an `if` that writes its answer has its case ascribed that answer,
/// so it synthesises where nothing states its type, as the computation a
/// `run` binds; one that writes none leaves its case bare.
#[test]
fn a_written_answer_ascribes_the_conditional_2089()
{
    let source = "def bound() -> -F Integer {\n  run m <- if true -> -F Integer { pure 1 } else { \
                  pure 2 } ;\n  pure (m + 1)\n}\ndef stated(b : Bool) -> -F Integer { if b { 1 } \
                  else { 2 } }\n";
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
