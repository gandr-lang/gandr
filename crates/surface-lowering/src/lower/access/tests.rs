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
use crate::fixture::listed;
use crate::fixture::listing;
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
use crate::resolve::Resolution;
use crate::resolve::SurfaceName;

/// The counter: a held count, one access that writes back its successor and
/// one that aborts, then a read of the count, with a parameter between.
const COUNTER: &str = include_str!("tests/fixtures/counter.gandr");

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
    let source = SourceText::from(include_str!(
        "tests/unformatted/a-shared-access-lowers-without-an-unwind.gandr"
    ));
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
                    SourceText::from("unwind { pure *{} }"),
                    SourceText::from("unwind")
                )
        ),
        "a shared view ends with its body, so its access takes no unwind"
    );
}

#[test]
fn an_access_of_a_place_lowers_with_its_index()
{
    let source = listing(include_str!(
        "tests/fixtures/an-access-of-a-place-lowers-with-its-index.gandr"
    ));
    let mut arena = CoreArena::new();
    let module = listed(&source, &mut arena);
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
    let source = SourceText::from(include_str!(
        "tests/fixtures/a-hold-lowers-at-its-grade.gandr"
    ));
    let mut arena = CoreArena::new();
    let module = lowered(source, &mut arena);
    let tail = tail_of(&arena, body_named(&module, SurfaceName::from("unique")));
    assert_eq!(
        forms(&arena, tail),
        ["hold[1]", "access @0", "resume @0"],
        "`var[1]` holds its value at grade one"
    );
    assert_eq!(
        refusal_of(&module, SurfaceName::from("two")),
        LoweringRefusal::GradedBridge {
            span: spelled_within(source, SourceText::from("var[2]"), SourceText::from("2")),
            grade: SurfaceName::from("2"),
        },
        "a hold has no grade but one and the default ω"
    );
}

#[test]
fn an_access_names_a_held_value_and_an_eliminator_its_view()
{
    let source = SourceText::from(include_str!(
        "tests/fixtures/an-access-names-a-held-value-and-an-eliminator-its-view.gandr"
    ));
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
    let source = SourceText::from(include_str!(
        "tests/fixtures/an-exit-inside-an-access-is-refused.gandr"
    ));
    let mut arena = CoreArena::new();
    let module = lowered(source, &mut arena);
    for (name, context) in [
        ("leaves", "as v { return *{} }"),
        ("unwinds", "unwind { return *{} }"),
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
                    SourceText::from("return *{}")
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
    let source = SourceText::from(include_str!(
        "tests/fixtures/a-hold-in-a-joined-arm-leaves-the-rest-its-own-slots-1500.gandr"
    ));
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

#[test]
fn a_place_assignment_writes_through_an_exclusive_view()
{
    let source = listing(include_str!(
        "tests/fixtures/a-place-assignment-writes-through-an-exclusive-view.gandr"
    ));
    let mut arena = CoreArena::new();
    let module = listed(&source, &mut arena);
    let tail = tail_of(&arena, body_named(&module, SurfaceName::from("written")));
    assert_eq!(
        forms(&arena, tail),
        [
            "hold",
            "access @0",
            "resume @0",
            "access @0",
            "resume @0",
            "hold",
            "read @1",
            "access @0[literal]",
            "resume @0",
            "read @1",
        ],
        "each assignment lends its slot exclusively at its place and resumes the view, the right \
         side's value returned before the access, and the slot is read after them"
    );
    assert_accepted(&judged(&module, &mut arena));
}

#[test]
fn an_assignment_writes_only_a_held_place()
{
    let source = SourceText::from(include_str!(
        "tests/fixtures/an-assignment-writes-only-a-held-place.gandr"
    ));
    let mut arena = CoreArena::new();
    let module = lowered(source, &mut arena);
    for (name, written, named) in [("parameter", "n = 3", "n"), ("viewed", "v = 1", "v")] {
        let named = SourceText::from(named);
        assert_eq!(
            refusal_of(&module, SurfaceName::from(name)),
            LoweringRefusal::OutOfFragment {
                span: spelled_within(source, SourceText::from(written), named),
                form: FormName::IDENTIFIER,
                sort: FragmentSort::Value,
                boundary: FragmentBoundary::Held,
            },
            "`{name}`: only a slot a `var` holds is written, never a parameter or a view"
        );
    }
    assert!(
        matches!(
            refusal_of(&module, SurfaceName::from("field")),
            LoweringRefusal::OutOfFragment { span, boundary: FragmentBoundary::Held, .. }
                if span == spelled_within(source, SourceText::from("p.a += 1"), SourceText::from("p.a"))
        ),
        "a field is no place an assignment writes"
    );
}

#[test]
fn a_stated_var_ascribes_its_value_or_holds_a_handle()
{
    let source = listing(include_str!(
        "tests/unformatted/a-stated-var-ascribes-its-value-or-holds-a-handle-1.gandr"
    ));
    let mut arena = CoreArena::new();
    let module = listed(&source, &mut arena);
    let listed = tail_of(&arena, body_named(&module, SurfaceName::from("listed")));
    let Some(&Computation::Memory(MemoryForm::Hold { value, .. })) = arena.computation(listed)
    else {
        panic!(
            "a stated `var` still holds its value: {:?}",
            arena.computation(listed)
        );
    };
    assert!(
        matches!(arena.value(value), Some(&Value::Ascribe { .. })),
        "the held value is ascribed the stated type, so a list reads its type there"
    );
    assert_accepted(&judged(&module, &mut arena));

    // A handle is held only where its world runs, so these are read, not
    // judged: `pointing` in the worlds corpus is judged.
    let source = SourceText::from(include_str!(
        "tests/unformatted/a-stated-var-ascribes-its-value-or-holds-a-handle-2.gandr"
    ));
    let mut arena = CoreArena::new();
    let module = lowered(source, &mut arena);
    let located = tail_of(&arena, body_named(&module, SurfaceName::from("located")));
    let Some(&Computation::Bind(bound, rest)) = arena.computation(located)
    else {
        panic!(
            "a located `var` binds its handle: {:?}",
            arena.computation(located)
        );
    };
    let Some(&Computation::Ascribe { body, .. }) = arena.computation(bound)
    else {
        panic!(
            "the handle is bound at the stated type: {:?}",
            arena.computation(bound)
        );
    };
    assert!(
        matches!(
            arena.computation(body),
            Some(&Computation::World(
                gandr_core_term::world::WorldForm::Hold { .. }
            ))
        ),
        "the handle is the world's hold of the value, not a held slot"
    );
    assert!(
        matches!(arena.computation(rest), Some(&Computation::Return(_))),
        "the rest of the block reads the handle's name"
    );
    assert!(
        matches!(
            refusal_of(&module, SurfaceName::from("graded")),
            LoweringRefusal::MalformedForm { span, fault: FormFault::MisplacedTile, .. }
                if span == spelled_within(source, SourceText::from("h : Integer at seat = 3; pure *{}"), SourceText::from("Integer at seat"))
        ),
        "a handle binds no slot, so a grade has nothing to grade"
    );
}

/// Each name an access, an eliminator, an assignment or an element read
/// writes keeps the binder it resolves to, so the editor finds every use of a
/// held slot and of a view (#5011).
#[test]
fn each_name_a_form_lends_ends_or_writes_keeps_its_binder_5011()
{
    let source = listing(include_str!(
        "tests/fixtures/each-name-a-form-lends-ends-or-writes-keeps-its-binder-5011.gandr"
    ));
    let mut arena = CoreArena::new();
    let module = listed(&source, &mut arena);
    assert_accepted(&judged(&module, &mut arena));
    let text = SourceText::from(source.as_str());
    let at = |context: &str, name: &str| {
        spelled_within(text, SourceText::from(context), SourceText::from(name))
    };
    let kept = |span| {
        module
            .resolutions()
            .iter()
            .find(|&&(used, _)| used == span)
            .map(|&(_, resolution)| resolution)
    };
    let slot = Some(Resolution::Binder(at("var xs", "xs")));
    for (context, name, binder) in [
        ("access xs as v", "xs", slot),
        ("shared xs.#[i] as", "xs", slot),
        ("access xs as u", "xs", slot),
        ("  xs.#[0] += 1", "xs", slot),
        ("y = xs.#[i]", "xs", slot),
        (
            "resume(v,",
            "v",
            Some(Resolution::Binder(at("as v {", "v"))),
        ),
        ("abort(u)", "u", Some(Resolution::Binder(at("as u {", "u")))),
    ] {
        assert_eq!(
            kept(at(context, name)),
            binder,
            "`{name}` in `{context}` keeps the binder it names"
        );
    }
}
