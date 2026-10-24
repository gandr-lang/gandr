use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;

use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::Zone;
use gandr_core_term::memory::AccessMode;
use gandr_core_term::memory::HoldGrade;
use gandr_core_term::memory::MemoryForm;
use gandr_core_term::memory::Place;
use gandr_surface_syntax::SourceText;

use crate::error::FormFault;
use crate::error::FragmentBoundary;
use crate::error::FragmentSort;
use crate::error::LoweringRefusal;
use crate::form::FormName;
use crate::lower::exits::tests::assert_same_body;
use crate::lower::exits::tests::spelled_within;
use crate::lower::native::tests::assert_accepted;
use crate::lower::native::tests::body_named;
use crate::lower::native::tests::judged;
use crate::lower::native::tests::lowered;
use crate::lower::native::tests::refusal_of;
use crate::lower::native::tests::tail_of;
use crate::module::DeclarationOutcome;
use crate::module::LoweredDeclaration;
use crate::resolve::SurfaceName;

/// The counter: a held count, one access that writes back its successor and
/// one that aborts, then a read of the count, with a parameter between.
const COUNTER: &str = r"def counter(n : Integer) -> -F Integer {
  hold c = 0;
  access c as v { resume(v, v + 1) };
  access c as v { abort(v) } unwind { pure unit };
  return c
}
";

/// The temporary-access forms reachable from `tail` through binds, splits,
/// lambdas and memory forms, in source order, one token each: `hold`, or
/// `hold[1]` at grade one, `access @i` or `access shared @i`, followed by
/// `[index]` at a place, `resume @i` and `abort @i` naming each slot's linear
/// index, and `read @i` for a `return` of a linear variable.
///
/// # Specification
/// trivial.
pub(in crate::lower) fn forms(
    arena: &CoreArena,
    tail: ComputationId,
) -> Vec<String>
{
    let mut seen = Vec::new();
    let mut pending = Vec::from([tail]);
    while let Some(next) = pending.pop() {
        match arena.computation(next) {
            Some(&Computation::Bind(first, second)) => pending.extend([second, first]),
            Some(&(Computation::Lambda(under) | Computation::Split { body: under, .. })) => {
                pending.push(under);
            },
            Some(&Computation::Return(value)) => {
                if let Some(&Value::Variable {
                    zone: Zone::Linear,
                    index,
                }) = arena.value(value)
                {
                    seen.push(format!("read @{}", u32::from(index)));
                }
            },
            Some(&Computation::Memory(ref form)) => {
                seen.push(match *form {
                    MemoryForm::Hold {
                        grade: HoldGrade::Many,
                        ..
                    } => String::from("hold"),
                    MemoryForm::Hold {
                        grade: HoldGrade::One,
                        ..
                    } => String::from("hold[1]"),
                    MemoryForm::Access {
                        mode, held, place, ..
                    } => {
                        let shared = match mode {
                            AccessMode::Exclusive { .. } => "",
                            AccessMode::Shared => " shared",
                        };
                        let place = match place {
                            Place::Whole => String::new(),
                            Place::At { index } => format!("[{}]", described(arena, index)),
                        };
                        format!("access{shared} @{}{place}", u32::from(held))
                    },
                    MemoryForm::Resume { view, .. } => format!("resume @{}", u32::from(view)),
                    MemoryForm::Abort { view } => format!("abort @{}", u32::from(view)),
                    MemoryForm::Consume { held } => format!("consume @{}", u32::from(held)),
                });
                pending.extend(form.computations().rev());
            },
            _ => {},
        }
    }
    seen
}

/// An access's index: `@i` for a linear variable, `%i` for an intuitionistic
/// one, `literal` for a literal, and `other` for anything else.
///
/// # Specification
/// trivial.
fn described(
    arena: &CoreArena,
    index: gandr_core_term::ValueId,
) -> String
{
    match arena.value(index) {
        Some(&Value::Variable {
            zone: Zone::Linear,
            index,
        }) => format!("@{}", u32::from(index)),
        Some(&Value::Variable {
            zone: Zone::Intuitionistic,
            index,
        }) => format!("%{}", u32::from(index)),
        Some(&Value::Literal(_)) => String::from("literal"),
        _ => String::from("other"),
    }
}

#[test]
fn the_counter_lowers_to_its_memory_forms()
{
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(COUNTER), &mut arena);
    let tail = tail_of(&arena, body_named(&module, SurfaceName::from("counter")));
    assert_eq!(
        forms(&arena, tail),
        [
            "hold",
            "access @0",
            "resume @0",
            "access @0",
            "abort @0",
            "read @0",
        ],
        "the count is held over the rest of the block, each access lends it past the parameter, \
         each view is the innermost linear slot, and the read after both is the count"
    );
    assert_accepted(&judged(&module, &mut arena));
}

#[test]
fn a_shared_access_lowers_without_an_unwind()
{
    let source = SourceText::from(
        r"def frozen() -> -F Integer {
  hold c = 2;
  access exclusive c as v { resume(v, v + 1) };
  access shared c as w { pure w }
}
def unwound() -> -F Unit {
  hold c = 0;
  access shared c as w { pure unit } unwind { pure unit }
}
",
    );
    let mut arena = CoreArena::new();
    let module = lowered(source, &mut arena);
    let tail = tail_of(&arena, body_named(&module, SurfaceName::from("frozen")));
    assert_eq!(
        forms(&arena, tail),
        [
            "hold",
            "access @0",
            "resume @0",
            "access shared @0",
            "read @0"
        ],
        "`exclusive` spells the default mode, and the shared view is read in its body"
    );
    assert!(
        matches!(
            refusal_of(&module, SurfaceName::from("unwound")),
            LoweringRefusal::MalformedForm { span, fault: FormFault::MisplacedTile, .. }
                if span == spelled_within(
                    source,
                    SourceText::from("unwind { pure unit }"),
                    SourceText::from("unwind")
                )
        ),
        "a shared view ends with its body, so its access takes no unwind"
    );
}

#[test]
fn an_access_of_a_place_lowers_with_its_index()
{
    let source = SourceText::from(
        r"def pair : List(Integer) ;
def pair = cons(1, cons(2, nil)) ;
def second() -> -F Integer {
  hold xs = pair;
  access xs[1] as v { resume(v, v + 1) };
  access shared xs[1] as w { pure w }
}
def indexed(i : Integer) -> -F Integer {
  hold xs = pair;
  access shared xs[i] as w { pure w }
}
",
    );
    let mut arena = CoreArena::new();
    let module = lowered(source, &mut arena);
    let tail = tail_of(&arena, body_named(&module, SurfaceName::from("second")));
    assert_eq!(
        forms(&arena, tail),
        [
            "hold",
            "access @0[literal]",
            "resume @0",
            "access shared @0[literal]",
            "read @0"
        ],
        "each access lends the held list at its index, and its view is the innermost slot"
    );
    let tail = tail_of(&arena, body_named(&module, SurfaceName::from("indexed")));
    assert_eq!(
        forms(&arena, tail),
        ["hold", "access shared @0[%0]", "read @0"],
        "an index names a variable where the access stands"
    );
    assert_accepted(&judged(&module, &mut arena));
}

#[test]
fn a_hold_lowers_at_its_grade()
{
    let source = SourceText::from(
        r"def unique() -> -F Unit {
  hold[1] c = 0;
  access c as v { resume(v, v + 1) }
}
def two() -> -F Unit {
  hold[2] c = 0;
  pure unit
}
",
    );
    let mut arena = CoreArena::new();
    let module = lowered(source, &mut arena);
    let tail = tail_of(&arena, body_named(&module, SurfaceName::from("unique")));
    assert_eq!(
        forms(&arena, tail),
        ["hold[1]", "access @0", "resume @0"],
        "`hold[1]` holds its value at grade one"
    );
    assert_eq!(
        refusal_of(&module, SurfaceName::from("two")),
        LoweringRefusal::GradedBridge {
            span: spelled_within(source, SourceText::from("hold[2]"), SourceText::from("2")),
            grade: SurfaceName::from("2"),
        },
        "a hold has no grade but one and the default ω"
    );
}

#[test]
fn an_access_names_a_held_value_and_an_eliminator_its_view()
{
    let source = SourceText::from(
        r"def lent(n : Integer) -> -F Unit { access n as v { abort(v) } }
def resumed(n : Integer) -> -F Unit { resume(n, 1) }
def aborted(n : Integer) -> -F Unit { abort(n) }
def unbound(n : Integer) -> -F Unit { abort(missing) }
",
    );
    let mut arena = CoreArena::new();
    let module = lowered(source, &mut arena);
    for (name, written, boundary) in [
        ("lent", "access n", FragmentBoundary::Held),
        ("resumed", "resume(n", FragmentBoundary::View),
        ("aborted", "abort(n", FragmentBoundary::View),
    ] {
        assert_eq!(
            refusal_of(&module, SurfaceName::from(name)),
            LoweringRefusal::OutOfFragment {
                span: spelled_within(source, SourceText::from(written), SourceText::from("n")),
                form: FormName::IDENTIFIER,
                sort: FragmentSort::Value,
                boundary,
            },
            "`{name}`: a parameter is no linear slot"
        );
    }
    assert_eq!(
        refusal_of(&module, SurfaceName::from("unbound")),
        LoweringRefusal::UnresolvedName {
            span: spelled_within(
                source,
                SourceText::from("abort(missing)"),
                SourceText::from("missing")
            ),
            name: SurfaceName::from("missing"),
        },
        "a name nothing binds is unresolved"
    );
}

#[test]
fn an_exit_inside_an_access_is_refused()
{
    let source = SourceText::from(
        r"data Nat : Type { Zero : Nat; Succ : (n : Nat) --> Nat; }
def leaves(n : Integer) -> -F Unit { hold c = 0; access c as v { return unit } }
def unwinds(n : Integer) -> -F Unit { hold c = 0; access c as v { abort(v) } unwind { return unit } }
def early(n : Nat) -> -F Integer {
  hold c = 0;
  run m <- case n { Zero => return 5, Succ(p) => pure 1 } ;
  return c
}
def early_by_hand(n : Nat) -> -F Integer {
  hold c = 0;
  case n { Zero => return 5, Succ(p) => return c }
}
",
    );
    let mut arena = CoreArena::new();
    let module = lowered(source, &mut arena);
    for (name, context) in [
        ("leaves", "as v { return unit }"),
        ("unwinds", "unwind { return unit }"),
    ] {
        assert!(
            matches!(
                refusal_of(&module, SurfaceName::from(name)),
                LoweringRefusal::OutOfFragment {
                    span,
                    sort: FragmentSort::Computation,
                    boundary: FragmentBoundary::NotInTail,
                    ..
                } if span == spelled_within(
                    source,
                    SourceText::from(context),
                    SourceText::from("return unit")
                )
            ),
            "`{name}`: an exit would leave the access half done: {:?}",
            refusal_of(&module, SurfaceName::from(name))
        );
    }
    assert_accepted(&judged(&module, &mut arena));
    assert!(
        matches!(
            module
                .declarations()
                .iter()
                .find(|declaration| declaration.name() == SurfaceName::from("early"))
                .map(LoweredDeclaration::outcome),
            Some(DeclarationOutcome::Completed { .. })
        ),
        "an exit in a hold's scope commutes through the hold"
    );
    assert_same_body(
        &module,
        &arena,
        (
            SurfaceName::from("early"),
            SurfaceName::from("early_by_hand"),
        ),
    );
}

/// #1500: a hold in an arm whose ends continue the block leaves the rest
/// reading the slot it named before the hold: the arm's own slot holds the
/// unit, so a rest read off it would not check at `Integer`.
#[test]
fn a_hold_in_a_joined_arm_leaves_the_rest_its_own_slots_1500()
{
    let source = SourceText::from(
        r"data Nat : Type { Zero : Nat; Succ : (n : Nat) --> Nat; }
def joined(n : Nat) -> -F Integer {
  hold c = 100;
  run m <- case n { Zero => return 7, Succ(p) => { hold c = unit; pure 1 } } ;
  pure c
}
def joined_by_hand(n : Nat) -> -F Integer {
  hold c = 100;
  case n { Zero => return 7, Succ(p) => { hold d = unit; pure c } }
}
",
    );
    let mut arena = CoreArena::new();
    let module = lowered(source, &mut arena);
    assert_accepted(&judged(&module, &mut arena));
    assert_same_body(
        &module,
        &arena,
        (
            SurfaceName::from("joined"),
            SurfaceName::from("joined_by_hand"),
        ),
    );
}
