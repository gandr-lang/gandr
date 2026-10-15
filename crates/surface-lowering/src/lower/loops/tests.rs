use alloc::format;
use alloc::vec::Vec;

use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::Zone;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FixpointEvidence;
use gandr_surface_syntax::SourceText;

use crate::error::FragmentBoundary;
use crate::error::LoopExit;
use crate::error::LoweringRefusal;
use crate::lower::exits::Leaves;
use crate::lower::exits::tests::assert_same_body;
use crate::lower::exits::tests::assert_surveyed;
use crate::lower::exits::tests::reachable;
use crate::lower::exits::tests::spelled;
use crate::lower::exits::tests::spelled_within;
use crate::lower::native::tests::assert_accepted;
use crate::lower::native::tests::body_named;
use crate::lower::native::tests::judged;
use crate::lower::native::tests::lowered;
use crate::lower::native::tests::refusal_of;
use crate::lower::native::tests::tail_of;
use crate::module::LoweredModule;
use crate::resolve::SurfaceName;

/// The naturals every witness matches on, and a computation of unit a loop
/// can run on every pass.
const PRELUDE: &str = "data Nat : Type { Zero : Nat; Succ : (n : Nat) --> Nat; }\n\
                       def tick(n : Nat) -> -F Unit { return unit }\n";

/// The indices of every force of a variable reachable from the body of
/// `name`, in the walk's order.
///
/// # Specification
/// trivial.
fn forced(
    module: &LoweredModule<'_>,
    arena: &CoreArena,
    name: SurfaceName<'_>,
) -> Vec<DeBruijnIndex>
{
    let tail = tail_of(arena, body_named(module, name));
    reachable(arena, tail)
        .into_iter()
        .filter_map(|node| match arena.computation(node) {
            Some(&Computation::Force(forced)) => match arena.value(forced) {
                Some(&Value::Variable {
                    zone: Zone::Intuitionistic,
                    index,
                }) => Some(index),
                _ => None,
            },
            _ => None,
        })
        .collect()
}

#[test]
fn a_loop_lowers_to_a_partial_fixpoint_over_its_body()
{
    let source = format!(
        "{PRELUDE}def first(n : Nat) -> -F Nat {{ loop {{ break(n) }} }}\n\
         def spin(n : Nat) -> -F Nat {{ loop {{ continue }} }}\n\
         def after(n : Nat) -> -F Nat {{ run m <- loop {{ break(Succ(n)) }} ; return Succ(m) }}\n\
         def after_by_hand(n : Nat) -> -F Nat {{ loop {{ return Succ(Succ(n)) }} }}\n"
    );
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let first = tail_of(&arena, body_named(&module, SurfaceName::from("first")));
    assert!(
        matches!(
            arena.computation(first),
            Some(&Computation::Fixpoint { body, evidence: FixpointEvidence::Partial })
                if matches!(arena.computation(body), Some(&Computation::Return(_)))
        ),
        "a loop at a body's end is a partial fixpoint, its `break` the returner it leaves with"
    );
    let spin = tail_of(&arena, body_named(&module, SurfaceName::from("spin")));
    assert!(
        matches!(
            arena.computation(spin),
            Some(&Computation::Fixpoint { body, evidence: FixpointEvidence::Partial })
                if matches!(arena.computation(body), Some(&Computation::Force(_)))
        ),
        "a loop's `continue` forces the loop's own binder"
    );
    assert_eq!(
        forced(&module, &arena, SurfaceName::from("spin")),
        [DeBruijnIndex::from(0_u32)],
        "the loop's own binder is the innermost one around its body"
    );
    assert_same_body(
        &module,
        &arena,
        (
            SurfaceName::from("after"),
            SurfaceName::from("after_by_hand"),
        ),
    );
    assert_accepted(&judged(&module, &mut arena));
}

#[test]
fn a_loop_body_ends_by_its_exits_or_runs_again()
{
    let source = format!(
        "{PRELUDE}def ticking(n : Nat) -> -F Nat {{ loop {{ tick(n) }} }}\n\
         def ticking_stated(n : Nat) -> -F Nat {{ loop {{ tick(n); }} }}\n\
         def ticking_by_hand(n : Nat) -> -F Nat {{ loop {{ tick(n); continue }} }}\n\
         def arms(n : Nat) -> -F Nat {{ loop {{ case n {{ Zero => break(n), Succ(p) => tick(p) }} }} }}\n\
         def arms_by_hand(n : Nat) -> -F Nat {{ loop {{ case n {{ Zero => break(n), Succ(p) => {{ tick(p); continue }} }} }} }}\n\
         def inner(n : Nat) -> -F Nat {{ loop {{ loop {{ break }} }} }}\n\
         def inner_by_hand(n : Nat) -> -F Nat {{ loop {{ loop {{ break }} ; continue }} }}\n\
         def endless(n : Nat) -> -F Nat {{ loop {{ loop {{ continue }} }} }}\n"
    );
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    for (inferred, written) in [
        ("ticking", "ticking_by_hand"),
        ("ticking_stated", "ticking_by_hand"),
        ("arms", "arms_by_hand"),
        ("inner", "inner_by_hand"),
    ] {
        assert_same_body(
            &module,
            &arena,
            (SurfaceName::from(inferred), SurfaceName::from(written)),
        );
    }
    assert_eq!(
        forced(&module, &arena, SurfaceName::from("endless")),
        [DeBruijnIndex::from(0_u32)],
        "a nested loop no path of which ends runs only itself again"
    );
    assert_accepted(&judged(&module, &mut arena));
}

#[test]
fn a_break_continues_what_follows_its_loop()
{
    let source = format!(
        "{PRELUDE}def pick(n : Nat) -> -F Nat {{ run m <- loop {{ case n {{ Zero => break(n), Succ(p) => break(p) }} }} ; return Succ(m) }}\n\
         def pick_by_hand(n : Nat) -> -F Nat {{ loop {{ case n {{ Zero => return Succ(n), Succ(p) => return Succ(p) }} }} }}\n\
         def bare(n : Nat) -> -F Nat {{ run u <- loop {{ break }} ; return n }}\n\
         def bare_by_hand(n : Nat) -> -F Nat {{ loop {{ return n }} }}\n\
         def kept(n : Nat) -> -F Nat {{ run m <- loop {{ run k <- loop {{ break(n) }} ; break(Succ(k)) }} ; return Succ(m) }}\n\
         def kept_by_hand(n : Nat) -> -F Nat {{ loop {{ loop {{ return Succ(Succ(n)) }} }} }}\n"
    );
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    for (broken, written) in [
        ("pick", "pick_by_hand"),
        ("bare", "bare_by_hand"),
        ("kept", "kept_by_hand"),
    ] {
        assert_same_body(
            &module,
            &arena,
            (SurfaceName::from(broken), SurfaceName::from(written)),
        );
    }
    assert_accepted(&judged(&module, &mut arena));
}

#[test]
fn a_continue_runs_its_own_loop_again()
{
    let source = format!(
        "{PRELUDE}def bound(n : Nat) -> -F Nat {{ loop {{ run m <- tick(n) ; continue }} }}\n\
         def armed(n : Nat) -> -F Nat {{ loop {{ case n {{ Zero => continue, Succ(p) => {{ run q <- tick(p) ; continue }} }} }} }}\n\
         def nested(n : Nat) -> -F Nat {{ loop {{ run m <- loop {{ case n {{ Zero => continue, Succ(p) => break(p) }} }} ; continue }} }}\n"
    );
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    for (name, indices) in [
        ("bound", [1_u32].as_slice()),
        ("armed", [0_u32, 2_u32].as_slice()),
        ("nested", [0_u32, 2_u32].as_slice()),
    ] {
        let mut found = forced(&module, &arena, SurfaceName::from(name));
        found.sort_unstable();
        let expected: Vec<DeBruijnIndex> =
            indices.iter().copied().map(DeBruijnIndex::from).collect();
        assert_eq!(
            found, expected,
            "each `continue` of `{name}` forces its own loop past the binders between"
        );
    }
    assert_accepted(&judged(&module, &mut arena));
}

#[test]
fn a_while_tests_its_condition_on_every_pass()
{
    let source = format!(
        "{PRELUDE}def down(n : Integer) -> -F Integer {{ while n > 0 {{ return n }} ; return 0 }}\n\
         def held(b : Bool, n : Nat) -> -F Nat {{ while b {{ tick(n) }} ; return n }}\n"
    );
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let tested = |arena: &CoreArena, tests: ComputationId| matches!(arena.computation(tests), Some(Computation::Case { branches, .. }) if branches.len() == 2);
    for (name, bound) in [("down", true), ("held", false)] {
        let tail = tail_of(&arena, body_named(&module, SurfaceName::from(name)));
        let body = match arena.computation(tail) {
            Some(&Computation::Fixpoint {
                body,
                evidence: FixpointEvidence::Partial,
            }) => body,
            other => panic!("`{name}` lowers to a partial fixpoint: {other:?}"),
        };
        let cases = match arena.computation(body) {
            Some(&Computation::Bind(_, tests)) => bound && tested(&arena, tests),
            _ => !bound && tested(&arena, body),
        };
        assert!(
            cases,
            "`{name}` cases on its condition inside its fixpoint, binding it only when it is a computation: {:?}",
            arena.computation(body)
        );
    }
    assert_accepted(&judged(&module, &mut arena));
}

#[test]
fn a_loop_leaves_where_it_stands_only_through_its_breaks()
{
    let source = format!(
        "{PRELUDE}def f(b : Bool, n : Nat) -> -F Nat {{\n\
         run a <- loop {{ break(n) }} ;\n\
         run c <- loop {{ loop {{ break(Zero) }} }} ;\n\
         run d <- while b {{ tick(n) }} ;\n\
         loop {{ continue }}\n\
         }}\n"
    );
    assert_surveyed(
        SourceText::from(source.as_str()),
        &[
            ("loop { break(n) }", Leaves::Sometimes),
            ("loop { loop { break(Zero) } }", Leaves::Always),
            ("loop { break(Zero) }", Leaves::Sometimes),
            ("while b { tick(n) }", Leaves::Sometimes),
            ("tick(n)", Leaves::Never),
            ("loop { continue }", Leaves::Always),
            ("break(n)", Leaves::Always),
            ("continue", Leaves::Always),
        ]
        .map(|(needle, leaves)| (SourceText::from(needle), leaves)),
    );
}

#[test]
fn a_loop_exit_off_every_loop_body_is_refused_by_name()
{
    let source = format!(
        "{PRELUDE}def stray(n : Nat) -> -F Nat {{ break(n) }}\n\
         def skip(n : Nat) -> -F Nat {{ continue }}\n\
         def held(n : Nat) -> -F Nat {{ loop {{ run t <- pure thunk {{ break(Zero) }} ; continue }} }}\n\
         def stepped(n : Nat) -> -F Nat {{ for x in n {{ tick(x) }} }}\n"
    );
    let text = SourceText::from(source.as_str());
    let module = lowered(text, &mut CoreArena::new());
    for (name, span, exit) in [
        (
            "stray",
            spelled(text, SourceText::from("break(n)")),
            LoopExit::Break,
        ),
        (
            "skip",
            spelled_within(
                text,
                SourceText::from("{ continue }"),
                SourceText::from("continue"),
            ),
            LoopExit::Continue,
        ),
        (
            "held",
            spelled(text, SourceText::from("break(Zero)")),
            LoopExit::Break,
        ),
    ] {
        assert_eq!(
            refusal_of(&module, SurfaceName::from(name)),
            LoweringRefusal::OutsideLoop { span, exit },
            "`{name}` writes a loop exit on no path through a loop's body"
        );
    }
    assert_eq!(
        refusal_of(&module, SurfaceName::from("stepped")),
        LoweringRefusal::ForNeedsListCase {
            span: spelled(text, SourceText::from("for x in n { tick(x) }")),
        },
        "a `for` loop names the list case it waits on"
    );
}

#[test]
fn a_loop_off_every_path_is_refused()
{
    let source =
        format!("{PRELUDE}def nested(n : Nat) -> -F Nat {{ return run loop {{ break(n) }} }}\n");
    let text = SourceText::from(source.as_str());
    let module = lowered(text, &mut CoreArena::new());
    let refused = refusal_of(&module, SurfaceName::from("nested"));
    assert!(
        matches!(
            refused,
            LoweringRefusal::OutOfFragment { span, boundary: FragmentBoundary::NotInTail, .. }
                if span == spelled(text, SourceText::from("loop { break(n) }"))
        ),
        "a loop where no path through a body passes is not in tail: {refused:?}"
    );
}
