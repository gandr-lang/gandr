use alloc::format;
use alloc::vec::Vec;

use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::Zone;
use gandr_core_term::memory::MemoryForm;
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

/// The passes a `for` runs again on, reachable from the body of `name`: the
/// index of the loop's own binder it forces and of the tail it applies that
/// to, in the walk's order.
///
/// # Specification
/// trivial.
fn stepped(
    module: &LoweredModule<'_>,
    arena: &CoreArena,
    name: SurfaceName<'_>,
) -> Vec<(DeBruijnIndex, DeBruijnIndex)>
{
    let tail = tail_of(arena, body_named(module, name));
    let variable = |value| match arena.value(value) {
        Some(&Value::Variable {
            zone: Zone::Intuitionistic,
            index,
        }) => Some(index),
        _ => None,
    };
    reachable(arena, tail)
        .into_iter()
        .filter_map(|node| match arena.computation(node) {
            Some(&Computation::Application(head, remaining)) => match arena.computation(head) {
                Some(&Computation::Force(forced)) => {
                    Some((variable(forced)?, variable(remaining)?))
                },
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
         def arms_stated(n : Nat) -> -F Nat {{ loop {{ case n {{ Zero => break(n), Succ(p) => tick(p) }}; }} }}\n\
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
        ("arms_stated", "arms_by_hand"),
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
fn a_hole_ending_a_loop_body_is_left_to_be_filled()
{
    let source = format!("{PRELUDE}def holed(n : Nat) -> -F Nat {{ loop {{ ?pending }} }}\n");
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let tail = tail_of(&arena, body_named(&module, SurfaceName::from("holed")));
    assert!(
        matches!(
            arena.computation(tail),
            Some(&Computation::Fixpoint { body, .. })
                if matches!(arena.computation(body), Some(&Computation::Hole(_)))
        ),
        "a hole passes the loop's end on to what fills it, so no re-entry follows it: {:?}",
        arena.computation(tail)
    );
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

/// The linear indices a value reads: one for a linear variable, one per
/// component for a tuple of them.
///
/// # Specification
/// trivial.
fn linear(
    arena: &CoreArena,
    value: ValueId,
) -> Vec<DeBruijnIndex>
{
    let read = |value| match arena.value(value) {
        Some(&Value::Variable {
            zone: Zone::Linear,
            index,
        }) => Some(index),
        _ => None,
    };
    match arena.value(value) {
        Some(&Value::Tuple(ref components)) => components
            .iter()
            .filter_map(|&component| read(component))
            .collect(),
        _ => read(value).into_iter().collect(),
    }
}

#[test]
fn a_loop_threads_the_slots_it_names_through_its_passes()
{
    let source = "def one() -> -F Integer { hold n = 3; while n > 0 { access n as v { resume(v, v - 1) } }; pure n }\n\
                  def two() -> -F Integer { hold a = 10; hold b = 1; while b < 4 { access b as v { resume(v, v + 1) }; access a as w { resume(w, w - 1) } }; pure a * 100 + b }\n\
                  def after() -> -F Integer { hold a = 4; hold b = 3; while b > 0 { access b as v { resume(v, v - 1) } }; pure a + 3 }\n\
                  def none() -> -F Integer { hold a = 4; while 1 > 2 { return 1 }; pure 5 }\n";
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source), &mut arena);
    // Each name: the slots the first pass takes, where the loop stands, and
    // the slots each pass end hands on, where it stands.
    for (name, first, again) in [
        ("one", [0_u32].as_slice(), [0_u32].as_slice()),
        ("two", [1, 0].as_slice(), [1, 0].as_slice()),
        ("after", [1, 0].as_slice(), [1, 0].as_slice()),
        ("none", [].as_slice(), [].as_slice()),
    ] {
        let tail = tail_of(&arena, body_named(&module, SurfaceName::from(name)));
        let nodes = reachable(&arena, tail);
        let entered: Vec<Vec<DeBruijnIndex>> = nodes
            .iter()
            .filter_map(|&node| match arena.computation(node) {
                Some(&Computation::Application(head, first))
                    if matches!(arena.computation(head), Some(Computation::Fixpoint { .. })) =>
                {
                    Some(linear(&arena, first))
                },
                _ => None,
            })
            .collect();
        let passed: Vec<Vec<DeBruijnIndex>> = nodes
            .iter()
            .filter_map(|&node| match arena.computation(node) {
                Some(&Computation::Application(head, next))
                    if matches!(arena.computation(head), Some(Computation::Force(_))) =>
                {
                    Some(linear(&arena, next))
                },
                _ => None,
            })
            .collect();
        let expected = |slots: &[u32]| -> Vec<Vec<DeBruijnIndex>> {
            if slots.is_empty() {
                Vec::new()
            }
            else {
                Vec::from([slots.iter().copied().map(DeBruijnIndex::from).collect()])
            }
        };
        assert_eq!(
            entered,
            expected(first),
            "`{name}`'s first pass takes the slots where the loop stands, outermost first"
        );
        assert_eq!(
            passed,
            expected(again),
            "each pass of `{name}` hands the next the slots it holds again"
        );
    }
    let tail = tail_of(&arena, body_named(&module, SurfaceName::from("two")));
    let split =
        reachable(&arena, tail)
            .into_iter()
            .find_map(|node| match arena.computation(node) {
                Some(&Computation::Split { arity, body, .. }) => Some((usize::from(arity), body)),
                _ => None,
            });
    let held = |hold: ComputationId| match arena.computation(hold) {
        Some(&Computation::Memory(MemoryForm::Hold { value, body, .. })) => {
            match arena.value(value) {
                Some(&Value::Variable {
                    zone: Zone::Intuitionistic,
                    index,
                }) => Some((u32::from(index), body)),
                _ => None,
            }
        },
        _ => None,
    };
    let (arity, outer) =
        split.unwrap_or_else(|| panic!("`two`'s passes split the tuple they take"));
    let (first, inner) =
        held(outer).unwrap_or_else(|| panic!("`two` holds the first component again"));
    let (second, _) =
        held(inner).unwrap_or_else(|| panic!("`two` holds the second component again"));
    assert_eq!(
        (arity, first, second),
        (2, 1, 0),
        "the outer slot is held again from the first component, the inner from the second"
    );
    assert_accepted(&judged(&module, &mut arena));
}

#[test]
fn a_for_steps_through_its_list()
{
    let source = format!(
        "{PRELUDE}def each(xs : List(Nat), n : Nat) -> -F Nat {{ for x in xs {{ tick(x) }} ; return n }}\n\
         def skipped(xs : List(Nat)) -> -F Nat {{ for x in xs {{ case x {{ Zero => continue, Succ(p) => return p }} }} ; return Zero }}\n\
         def inner(xs : List(Nat)) -> -F Unit {{ for x in xs {{ loop {{ continue }} }} }}\n"
    );
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    for name in ["each", "skipped", "inner"] {
        let tail = tail_of(&arena, body_named(&module, SurfaceName::from(name)));
        let structural = |head| match arena.computation(head) {
            Some(&Computation::Fixpoint {
                body,
                evidence: FixpointEvidence::StructuralDescent,
            }) => matches!(arena.computation(body), Some(&Computation::Lambda(steps))
                if matches!(arena.computation(steps), Some(Computation::ListCase { .. }))),
            _ => false,
        };
        assert!(
            matches!(arena.computation(tail), Some(&Computation::Application(head, _)) if structural(head)),
            "`{name}` applies a structural fixpoint over the case of the remaining list to its list: {:?}",
            arena.computation(tail)
        );
    }
    for (name, passes) in [
        ("each", [(4_u32, 1_u32)].as_slice()),
        ("skipped", [(3_u32, 0_u32)].as_slice()),
        ("inner", [].as_slice()),
    ] {
        let expected: Vec<(DeBruijnIndex, DeBruijnIndex)> = passes
            .iter()
            .map(|&(own, tail)| (DeBruijnIndex::from(own), DeBruijnIndex::from(tail)))
            .collect();
        assert_eq!(
            stepped(&module, &arena, SurfaceName::from(name)),
            expected,
            "each pass of `{name}` runs its loop again on the tail past the binders between"
        );
    }
    assert_eq!(
        forced(&module, &arena, SurfaceName::from("inner")),
        [DeBruijnIndex::from(0_u32)],
        "a loop inside a `for` runs only itself again"
    );
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
         def held(n : Nat) -> -F Nat {{ loop {{ run t <- pure thunk {{ break(Zero) }} ; continue }} }}\n"
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
