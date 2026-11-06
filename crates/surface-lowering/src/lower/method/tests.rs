use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;

use gandr_core_term::CompType;
use gandr_core_term::Computation;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueType;
use gandr_core_term::Zone;
use gandr_core_term::memory::MemoryForm;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::DeBruijnIndex;
use gandr_surface_syntax::SourceText;

use crate::CandidateCount;
use crate::error::FragmentBoundary;
use crate::error::LoweringRefusal;
use crate::fixture::listed;
use crate::fixture::listing;
use crate::lower::access::tests::forms;
use crate::lower::native::tests::assert_accepted;
use crate::lower::native::tests::body_named;
use crate::lower::native::tests::judged;
use crate::lower::native::tests::lowered;
use crate::lower::native::tests::refusal_of;
use crate::lower::native::tests::tail_of;
use crate::module::DeclarationOutcome;
use crate::resolve::SurfaceName;

/// A counter's methods, one per receiver mode, and a block calling each on
/// one held count.
const COUNTER: &str = include_str!("tests/unformatted/counter.gandr");

#[test]
fn each_mode_lowers_to_its_access()
{
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(COUNTER), &mut arena);
    let tail = tail_of(&arena, body_named(&module, SurfaceName::from("used")));
    assert_eq!(
        forms(&arena, tail),
        [
            "hold",
            "access shared @0",
            "access @0",
            "resume @0",
            "consume @0",
        ],
        "a read lends the count shared, a write lends it and writes back, and a take ends \
         its hold"
    );
    assert_accepted(&judged(&module, &mut arena));
}

#[test]
fn a_written_through_body_returns_its_receiver()
{
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(COUNTER), &mut arena);
    let tail = tail_of(&arena, body_named(&module, SurfaceName::from("bump")));
    assert_eq!(
        forms(&arena, tail),
        ["hold", "access @0", "resume @0"],
        "the body runs under the hold of its receiver, which it lends as a held slot"
    );
    let Some(&Computation::Memory(MemoryForm::Hold { value, .. })) = arena.computation(tail)
    else {
        panic!("the body is a hold")
    };
    assert_eq!(
        arena.value(value),
        Some(&Value::Variable {
            zone: Zone::Intuitionistic,
            index: DeBruijnIndex::from(1_u32),
        }),
        "the hold holds the receiver parameter, one past `by`"
    );
    let Some(declaration) = module
        .declarations()
        .iter()
        .find(|declaration| declaration.name() == SurfaceName::from("bump"))
    else {
        panic!("`bump` is declared")
    };
    let DeclarationOutcome::Completed { declared_type, .. } = declaration.outcome()
    else {
        panic!("`bump` lowers both halves: {:?}", declaration.outcome())
    };
    let mut current = match arena.value_type(declared_type) {
        Some(&ValueType::Thunk(computation)) => computation,
        other => panic!("a thunk type: {other:?}"),
    };
    while let Some(&CompType::Arrow { codomain, .. }) = arena.comp_type(current) {
        current = codomain;
    }
    let Some(&CompType::Returner { result, .. }) = arena.comp_type(current)
    else {
        panic!("a returner past the arrows")
    };
    assert!(
        matches!(arena.value_type(result), Some(ValueType::Product(components)) if components.len() == 2_usize),
        "the result pairs the receiver before the answer: {:?}",
        arena.value_type(result)
    );
}

#[test]
fn a_receiver_not_held_is_passed_or_refused()
{
    let source = format!(
        include_str!("tests/unformatted/a-receiver-not-held-is-passed-or-refused.gandr"),
        COUNTER = COUNTER
    );
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let tail = tail_of(&arena, body_named(&module, SurfaceName::from("passed")));
    assert_eq!(
        forms(&arena, tail),
        Vec::<String>::new(),
        "a receiver no slot holds is read through and taken as a value"
    );
    assert!(
        matches!(
            refusal_of(&module, SurfaceName::from("written")),
            LoweringRefusal::OutOfFragment {
                boundary: FragmentBoundary::Held,
                ..
            }
        ),
        "nothing holds what a write would write back"
    );
}

#[test]
fn a_method_two_modules_declare_is_refused_naming_both()
{
    let source =
        include_str!("tests/fixtures/a-method-two-modules-declare-is-refused-naming-both.gandr");
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source), &mut arena);
    assert!(
        matches!(
            refusal_of(&module, SurfaceName::from("measured")),
            LoweringRefusal::AmbiguousMethod { method, first, second, more, .. }
                if method == SurfaceName::from("size")
                    && first == SurfaceName::from("A")
                    && second == SurfaceName::from("B")
                    && more == CandidateCount::from(0_usize)
        ),
        "the call names both modules: {:?}",
        refusal_of(&module, SurfaceName::from("measured"))
    );
}

#[test]
fn a_mode_word_off_a_receiver_is_refused()
{
    let source = include_str!("tests/fixtures/a-mode-word-off-a-receiver-is-refused.gandr");
    let mut arena = CoreArena::new();
    let source = listing(source);
    let module = listed(&source, &mut arena);
    for (name, mode) in [
        ("top", "shared"),
        ("second", "consumed"),
        ("deduced", "m"),
        ("nested", "m"),
    ] {
        assert!(
            matches!(
                refusal_of(&module, SurfaceName::from(name)),
                LoweringRefusal::StrayReceiverMode { mode: written, .. }
                    if written == SurfaceName::from(mode)
            ),
            "`{name}` writes `{mode}` on a parameter that is no receiver: {:?}",
            refusal_of(&module, SurfaceName::from(name))
        );
    }
    // A type variable alone is a parameter's type, never its mode.
    let _picked = body_named(&module, SurfaceName::from("pick"));
}

#[test]
fn a_mode_variable_off_a_receiver_is_refused_over_its_moded_type_3813()
{
    // `x wit` for `x with`: a type variable beside a type reads as a moded
    // type, so the refusal marks the pair, the misspelt word among it.
    let source = include_str!(
        "tests/fixtures/a-mode-variable-off-a-receiver-is-refused-over-its-moded-type-3813.gandr"
    );
    let mut arena = CoreArena::new();
    let source = listing(source);
    let module = listed(&source, &mut arena);
    for (name, moded) in [("nested", "m Integer"), ("misspelt", "x wit")] {
        let start = source.find(moded).unwrap_or_default();
        let end = start.saturating_add(moded.len());
        let refused = refusal_of(&module, SurfaceName::from(name));
        assert!(
            matches!(
                refused,
                LoweringRefusal::StrayReceiverMode { span, .. }
                    if usize::from(span.start()) == start && usize::from(span.end()) == end
            ),
            "`{name}` is refused over `{moded}`, at {start}..{end}: {refused:?}"
        );
    }
}

#[test]
fn a_receiver_is_a_typed_first_self()
{
    let source = include_str!("tests/fixtures/a-receiver-is-a-typed-first-self.gandr");
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source), &mut arena);
    for name in ["first", "second"] {
        let tail = tail_of(&arena, body_named(&module, SurfaceName::from(name)));
        assert_eq!(
            forms(&arena, tail),
            ["hold"],
            "`{name}` calls no method: nothing lends the count, and the selection reads a field \
             of it"
        );
    }
    assert!(
        matches!(
            refusal_of(&module, SurfaceName::from("third")),
            LoweringRefusal::ImplicitUnsupplied { function, .. }
                if function == SurfaceName::from("generic")
        ),
        "a receiver behind an implicit telescope is a method, called with no implicit: {:?}",
        refusal_of(&module, SurfaceName::from("third"))
    );
}

/// A held list's places: a method answering the first element, one answering
/// the element at an index, and calls lending each to a block that reads it and
/// to one that writes it back.
const PLACES: &str = include_str!("tests/unformatted/places.gandr");

#[test]
fn a_deduced_mode_is_erased_from_the_telescope()
{
    let source = format!(
        include_str!("tests/unformatted/a-deduced-mode-is-erased-from-the-telescope.gandr"),
        PLACES = PLACES
    );
    let mut arena = CoreArena::new();
    let source = listing(&source);
    let module = listed(&source, &mut arena);
    let Some(declaration) = module
        .declarations()
        .iter()
        .find(|declaration| declaration.name() == SurfaceName::from("nth"))
    else {
        panic!("`nth` is declared")
    };
    let DeclarationOutcome::Completed { declared_type, .. } = declaration.outcome()
    else {
        panic!("`nth` states its type: {:?}", declaration.outcome())
    };
    let mut current = match arena.value_type(declared_type) {
        Some(&ValueType::Thunk(computation)) => computation,
        other => panic!("a thunk type: {other:?}"),
    };
    let mut domains = Vec::new();
    while let Some(&CompType::Arrow { domain, codomain }) = arena.comp_type(current) {
        domains.push(arena.value_type(domain).cloned());
        current = codomain;
    }
    assert_eq!(
        domains.len(),
        2_usize,
        "the mode binds nothing: the receiver and the index are the only parameters"
    );
    assert!(
        matches!(
            arena.comp_type(current),
            Some(&CompType::Returner { result, .. })
                if arena.value_type(result) == Some(&ValueType::Base(BaseType::Integer))
        ),
        "the view stands as the place's index: {:?}",
        arena.comp_type(current)
    );
    assert!(
        matches!(
            refusal_of(&module, SurfaceName::from("lost")),
            LoweringRefusal::UnresolvedName { name, .. } if name == SurfaceName::from("k")
        ),
        "a receiver's mode variable names a mode its telescope binds: {:?}",
        refusal_of(&module, SurfaceName::from("lost"))
    );
}

#[test]
fn a_view_method_answers_its_place_index()
{
    let mut arena = CoreArena::new();
    let source = listing(PLACES);
    let module = listed(&source, &mut arena);
    for (name, place) in [("first", "literal"), ("nth", "%0")] {
        let tail = tail_of(&arena, body_named(&module, SurfaceName::from(name)));
        assert_eq!(
            forms(&arena, tail),
            ["hold", &format!("access shared @0[{place}]")],
            "`{name}` holds its receiver and lends it shared at the place it answers"
        );
    }
    assert_accepted(&judged(&module, &mut arena));
}

#[test]
fn a_view_method_answering_no_place_is_refused()
{
    let source = format!(
        include_str!("tests/unformatted/a-view-method-answering-no-place-is-refused.gandr"),
        PLACES = PLACES
    );
    let mut arena = CoreArena::new();
    let source = listing(&source);
    let module = listed(&source, &mut arena);
    for name in ["valued", "computed", "crossed", "stray"] {
        assert!(
            matches!(
                refusal_of(&module, SurfaceName::from(name)),
                LoweringRefusal::ViewNotPlace { .. }
            ),
            "`{name}` answers no place of its receiver: {:?}",
            refusal_of(&module, SurfaceName::from(name))
        );
    }
}

#[test]
fn an_index_reads_its_held_element()
{
    let source = format!(
        include_str!("tests/unformatted/an-index-reads-its-held-element.gandr"),
        PLACES = PLACES
    );
    let mut arena = CoreArena::new();
    let source = listing(&source);
    let module = listed(&source, &mut arena);
    for (name, place) in [("element", "%0"), ("zeroth", "literal")] {
        let tail = tail_of(&arena, body_named(&module, SurfaceName::from(name)));
        assert_eq!(
            forms(&arena, tail),
            ["hold", &format!("access shared @0[{place}]"), "read @0"],
            "`{name}` holds the list and answers the element its shared view sees"
        );
    }
    assert_accepted(&judged(&module, &mut arena));
}

/// #2670: an index of a list no slot holds holds the list for the read
/// alone. The lowering mints the hold a source would write, so the tail
/// is the held read's: a hold, a shared view at the index, and its read.
#[test]
fn an_index_of_an_unheld_list_holds_it_for_the_read_2670()
{
    let source = format!(
        include_str!(
            "tests/unformatted/an-index-of-an-unheld-list-holds-it-for-the-read-2670.gandr"
        ),
        PLACES = PLACES
    );
    let mut arena = CoreArena::new();
    let source = listing(&source);
    let module = listed(&source, &mut arena);
    for (name, place) in [("passed", "%0"), ("declared", "literal")] {
        let tail = tail_of(&arena, body_named(&module, SurfaceName::from(name)));
        assert_eq!(
            forms(&arena, tail),
            ["hold", &format!("access shared @0[{place}]"), "read @0"],
            "`{name}` holds its list for the read and answers the element its view sees"
        );
    }
    assert_accepted(&judged(&module, &mut arena));
}

/// #4944: a bracket after the name of a value holds no static arguments. The
/// lowering refuses an element index without its selector at the bracket.
/// The refusal names `.#[ … ]`. The cases are the body of a view method and
/// an element of a held list.
#[test]
fn a_bare_index_is_refused_naming_the_selector_4944()
{
    let source = format!(
        include_str!("tests/unformatted/a-bare-index-is-refused-naming-the-selector-4944.gandr"),
        PLACES = PLACES
    );
    let mut arena = CoreArena::new();
    let source = listing(&source);
    let module = listed(&source, &mut arena);
    let text = source.as_str();
    for (name, written) in [("zeroth", "self[0]"), ("held", "xs[1]")] {
        let bracket = text
            .find(written)
            .and_then(|at| at.checked_add(written.find('[').unwrap_or_default()))
            .unwrap_or_default();
        assert_eq!(
            refusal_of(&module, SurfaceName::from(name)),
            LoweringRefusal::MalformedForm {
                span: gandr_surface_syntax::ByteSpan::new(
                    gandr_surface_syntax::ByteOffset::from(bracket),
                    gandr_surface_syntax::ByteOffset::from(bracket.saturating_add(1)),
                )
                .expect("a bracket's span"),
                form: crate::FormName::INSTANTIATION,
                fault: crate::FormFault::BareIndex,
            },
            "`{written}` in `{name}` is refused at its bracket"
        );
    }
}

#[test]
fn a_view_block_lends_at_the_mode_it_asks()
{
    let mut arena = CoreArena::new();
    let source = listing(PLACES);
    let module = listed(&source, &mut arena);
    for (name, lent) in [
        (
            "head",
            Vec::from([
                "hold",
                "access shared @0",
                "access shared @0[%0]",
                "read @0",
            ]),
        ),
        (
            "doubled",
            Vec::from(["hold", "access shared @0", "access shared @0[%0]"]),
        ),
        (
            "raised",
            Vec::from(["hold", "access shared @0", "access @0[%0]", "resume @0"]),
        ),
        (
            "untouched",
            Vec::from(["hold", "access shared @0", "access @0[%0]", "abort @0"]),
        ),
    ] {
        let tail = tail_of(&arena, body_named(&module, SurfaceName::from(name)));
        assert_eq!(
            forms(&arena, tail),
            lent,
            "`{name}` asks its place's index shared, then lends the place exclusively only \
             where its block ends the view"
        );
    }
    assert_accepted(&judged(&module, &mut arena));
}

#[test]
fn a_view_block_after_no_place_is_refused()
{
    let source = format!(
        include_str!("tests/unformatted/a-view-block-after-no-place-is-refused.gandr"),
        COUNTER = COUNTER
    );
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    for name in ["viewed", "called"] {
        assert!(
            matches!(
                refusal_of(&module, SurfaceName::from(name)),
                LoweringRefusal::ViewOfNoPlace { .. }
            ),
            "`{name}` lends a view of no method's place: {:?}",
            refusal_of(&module, SurfaceName::from(name))
        );
    }
}
