use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;

use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::Zone;
use gandr_core_term::memory::AccessMode;
use gandr_core_term::memory::MemoryForm;
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
/// lambdas and memory forms, in source order, one token each: `hold`,
/// `access @i` or `access shared @i`, `resume @i` and `abort @i` naming each
/// slot's linear index, and `read @i` for a `return` of a linear variable.
///
/// # Specification
/// trivial.
fn forms(
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
                    MemoryForm::Hold { .. } => String::from("hold"),
                    MemoryForm::Access {
                        mode: AccessMode::Exclusive { .. },
                        held,
                        ..
                    } => format!("access @{}", u32::from(held)),
                    MemoryForm::Access {
                        mode: AccessMode::Shared,
                        held,
                        ..
                    } => format!("access shared @{}", u32::from(held)),
                    MemoryForm::Resume { view, .. } => format!("resume @{}", u32::from(view)),
                    MemoryForm::Abort { view } => format!("abort @{}", u32::from(view)),
                });
                pending.extend(form.computations().rev());
            },
            _ => {},
        }
    }
    seen
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
def joined(n : Nat) -> -F Unit {
  run m <- case n { Zero => return unit, Succ(p) => { hold c = 0; pure unit } } ;
  return m
}
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
    assert_eq!(
        refusal_of(&module, SurfaceName::from("joined")),
        LoweringRefusal::OutOfFragment {
            span: spelled_within(
                source,
                SourceText::from("Succ(p) => { hold"),
                SourceText::from("hold")
            ),
            form: FormName::HOLD_STATEMENT,
            sort: FragmentSort::Computation,
            boundary: FragmentBoundary::Unadmitted,
        },
        "the rest an exit continues would sit under the held slot"
    );
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
