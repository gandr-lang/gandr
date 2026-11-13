//! Type tables whose reading runs the run stage's engine: a value or a normal
//! form reprinted, or a table judged after its closure. Each test names the
//! engine, so it stands in the `tests` target (#7048).

use gandr_surface_dispatcher::RoundTrip;
use gandr_surface_dispatcher::TypeTable;
use gandr_surface_evaluate::Evaluator;
use gandr_surface_grammar::built_in;
use gandr_surface_pretty::Form;
use gandr_surface_pretty::PageWidth;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

/// The table [`TypeTable::of`] builds for `source`; panics when the grammar
/// or the parse fails.
///
/// # Specification
/// trivial.
fn table(source: SourceText<'_>) -> TypeTable
{
    let grammar = built_in().expect("the built-in grammar builds");
    TypeTable::of(&grammar, source).expect("the source parses")
}

/// #552: a table built over an importer's unit reads its printed values
/// and types back in that unit. Read alone, the importer's import
/// resolves to nothing and every declaration of it — the appended probe
/// among them — is refused with the import.
#[test]
fn an_importer_s_value_reads_back_beside_its_sibling_552()
{
    use gandr_surface_dispatcher::reprinted;
    use gandr_surface_dispatcher::signed;
    use gandr_surface_lowering::ImportTarget;
    use gandr_surface_lowering::SourceIndex;
    use gandr_surface_lowering::Unit;
    use gandr_surface_lowering::UnitSource;
    use gandr_surface_pretty::Name;

    let sibling = include_str!(
        "../src/typed/unformatted/an-importer-s-value-reads-back-beside-its-sibling-552-sibling.gandr"
    );
    let importer = include_str!(
        "typed/unformatted/an-importer-s-value-reads-back-beside-its-sibling-552-importer.gandr"
    );
    let laid = format!(
        include_str!(
            "../src/typed/unformatted/a-name-nothing-declares-is-kept-beside-a-form-refused-as-shadowing-laid.gandr"
        ),
        importer = importer,
        sibling = sibling
    );
    let base = ByteOffset::from(sibling.len().saturating_add(1_usize));
    let unit = Unit::new(vec![
        UnitSource::new(ByteOffset::from(0_usize), Vec::new()),
        UnitSource::new(base, vec![ImportTarget::Source(SourceIndex::from(0_usize))]),
    ])
    .expect("the unit's sources start in order");
    let grammar = built_in().expect("the built-in grammar builds");
    let table = TypeTable::of_unit(&grammar, SourceText::from(laid.as_str()), &unit, base)
        .expect("the unit parses");
    assert_eq!(
        table.reprint_value::<Evaluator>(
            &grammar,
            Maybe::Absent(signed::Absent::Unsigned),
            SourceText::from("Here")
        ),
        Maybe::Present(String::from("Here")),
        "the sibling's constructor reads back as written"
    );
    assert_eq!(
        table.reprint_value::<Evaluator>(
            &grammar,
            Maybe::Absent(signed::Absent::Unsigned),
            SourceText::from("nope")
        ),
        Maybe::Absent(reprinted::Absent::Unlowered),
        "an unsigned value the lowering refuses has no signature to run under"
    );
    assert_eq!(
        table.reprint_value::<Evaluator>(
            &grammar,
            Maybe::Present(Name::from("there")),
            SourceText::from("+{.1 = Here}")
        ),
        Maybe::Present(String::from("+{.1 = Here}")),
        "an injection, which needs its type, reads back run under the declaration's"
    );
    let trips: Vec<(String, RoundTrip)> = table
        .read_back(&grammar, PageWidth::from(80_u32), Form::Sugared.into())
        .into_iter()
        .map(|back| (back.spelled, back.trip))
        .collect();
    assert!(
        !trips.is_empty() && trips.iter().all(|&(_, ref trip)| *trip == RoundTrip::Equal),
        "every printed type of the importer reads back beside its sibling: {trips:?}"
    );
}

/// #669: a `theory`'s stated normal form is a term of the block, which a
/// top-level thunk cannot name. Read back under the block's rules it is
/// itself, and a call reads to the normal form the engine spells.
#[test]
fn a_theory_s_normal_form_reads_back_under_its_rules_669()
{
    use gandr_surface_dispatcher::reprinted;
    use gandr_surface_pretty::Name;

    let source = SourceText::from(include_str!(
        "typed/fixtures/a-theory-s-normal-form-reads-back-under-its-rules-669.gandr"
    ));
    let grammar = built_in().expect("the built-in grammar builds");
    let table = table(source);
    let block = Name::from("Pointed");
    let read = |written: &'static str| {
        table.reprint_normal_form::<Evaluator>(&grammar, block, SourceText::from(written))
    };
    assert_eq!(read("pt"), Maybe::Present(String::from("pt")), "as written");
    assert_eq!(
        read("flip(flip(pt))"),
        Maybe::Present(String::from("pt")),
        "a call to its normal form"
    );
    assert_eq!(
        table.reprint_normal_form::<Evaluator>(
            &grammar,
            Name::from("Absent"),
            SourceText::from("pt")
        ),
        Maybe::Absent(reprinted::Absent::Unlowered),
        "no block of that name"
    );
}

/// #610: a run value of one member of a component reprints under its own
/// declaration's signature. The walk numbers the constants of the whole
/// component — here the base, a sibling that also imports it, then the
/// member — while the member's table numbers only its import closure, so
/// the walk's number of `joined` names another declaration of the table,
/// or none, and the `Cons` that needs its type refused to read back.
#[test]
fn a_member_s_value_reprints_under_its_own_declaration_610()
{
    use core::convert::Infallible;
    use core::ops::ControlFlow;
    use std::path::Path;

    use gandr_kernel_term::ConstantIndex;
    use gandr_surface_dispatcher::Composed;
    use gandr_surface_dispatcher::Evaluation;
    use gandr_surface_dispatcher::Pool;
    use gandr_surface_dispatcher::Step;
    use gandr_surface_dispatcher::Walk;
    use gandr_surface_dispatcher::Width;
    use gandr_surface_dispatcher::fixture::Scratch;
    use gandr_surface_dispatcher::lay_out;
    use gandr_surface_evaluate::Runs as _;
    use gandr_surface_pretty::Name;

    let scratch = Scratch::new(Path::new("member-reprint"));
    scratch.file(
        Path::new("fixture/base.gandr"),
        SourceText::from(include_str!(
            "typed/fixtures/a-member-s-value-reprints-under-its-own-declaration-610-1.gandr"
        )),
    );
    scratch.file(
        Path::new("fixture/a-sibling.gandr"),
        SourceText::from(include_str!(
            "typed/fixtures/a-member-s-value-reprints-under-its-own-declaration-610-2.gandr"
        )),
    );
    scratch.file(
        Path::new("fixture/b-member.gandr"),
        SourceText::from(include_str!("typed/fixtures/member-list.gandr")),
    );
    let grammar = built_in().expect("the built-in grammar builds");
    let mut reprinted = Vec::new();
    let ControlFlow::Continue(_) = Walk::new(vec![scratch.root().join("fixture")])
        .visit::<Evaluator, _, _>(
            &Pool::new(Width::SERIAL),
            |step| -> ControlFlow<Infallible> {
                let Step::Source {
                    path,
                    root,
                    text,
                    base,
                    composed: Composed::Settled { mut program, .. },
                    ..
                } = step
                else {
                    return ControlFlow::Continue(());
                };
                if !path.ends_with("b-member.gandr") {
                    return ControlFlow::Continue(());
                }
                let own =
                    SourceText::from(text.as_ref().get(usize::from(base) ..).unwrap_or_default());
                let laid = lay_out(&grammar, path, root, own);
                let table = TypeTable::of_unit(
                    &grammar,
                    SourceText::from(laid.text.as_str()),
                    &laid.unit,
                    laid.base,
                )
                .expect("the member's unit parses");
                let Maybe::Present(last) = program.last_declared()
                else {
                    panic!("the component declares");
                };
                let mut named = String::new();
                for position in 0_usize ..= usize::from(last) {
                    let constant = ConstantIndex::from(position);
                    let Maybe::Present(name) = program.name(constant)
                    else {
                        continue;
                    };
                    named.clear();
                    core::fmt::Write::write_fmt(&mut named, format_args!("{name}"))
                        .expect("a name writes");
                    if named != "joined" {
                        continue;
                    }
                    let Evaluation::Value(value) = program.evaluate(constant)
                    else {
                        panic!("`joined` runs to a value");
                    };
                    let presentation = value.presentation();
                    let spelled: &str = presentation.as_ref();
                    let reprint = table.reprint_value::<Evaluator>(
                        &grammar,
                        Maybe::Present(Name::from("joined")),
                        SourceText::from(spelled),
                    );
                    reprinted.push((String::from(spelled), reprint));
                }
                ControlFlow::Continue(())
            },
        );
    assert_eq!(
        reprinted,
        [(
            String::from("Cons Zero Nil"),
            Maybe::Present(String::from("Cons Zero Nil"))
        )],
        "the member's value reprints under its own declaration's type"
    );
}

/// #776: a document typed after its judged closure — lowered after the
/// closure's arena, its own declarations typed on the checker's state
/// after the closure's — answers at every byte, for every declaration,
/// every declared name and every printed type read back, as the document
/// typed whole over its unit does. The rose trees import two siblings and
/// write families, recursion through an imported `map`, cases and a mutual
/// block.
#[test]
fn a_document_typed_after_its_closure_types_as_one_typed_whole_776()
{
    use alloc::sync::Arc;

    use gandr_surface_corpus::CorpusRoot;
    use gandr_surface_dispatcher::HostGrant;
    use gandr_surface_dispatcher::JudgedClosure;
    use gandr_surface_dispatcher::LoweringCount;
    use gandr_surface_dispatcher::SourceRoot;
    use gandr_surface_dispatcher::lay_out;
    use gandr_surface_dispatcher::lower_closure;
    use gandr_surface_parser::parse;

    let grammar = Arc::new(built_in().expect("the built-in grammar builds"));
    let path = std::fs::canonicalize(
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../corpus/model/data/rose.gandr"),
    )
    .expect("the rose trees are in the corpus");
    let own = std::fs::read_to_string(&path).expect("the rose trees read");
    let laid = lay_out(
        &grammar,
        &path,
        SourceRoot::Fixture,
        SourceText::from(own.as_str()),
    );
    let closure = Arc::new(
        lower_closure(
            Arc::clone(&grammar),
            String::from(laid.text.get(.. usize::from(laid.base)).unwrap_or_default()),
            laid.unit
                .before_last()
                .expect("the prelude and the siblings make a unit"),
            &mut LoweringCount::default(),
        )
        .expect("the siblings are held"),
    );
    let judged = JudgedClosure::new::<Evaluator>(
        Arc::clone(&closure),
        &HostGrant::UNBOUNDED,
        CorpusRoot::Fixture,
    )
    .expect("the siblings lower to their end");
    let text = SourceText::from(laid.text.as_str());
    let parsed = parse(&grammar, SourceText::from(own.as_str()))
        .expect("the rose trees parse")
        .after(closure.tree(), text)
        .expect("the rose trees lay after their siblings");
    let after = TypeTable::of_parsed_after(&judged, parsed, &laid.unit, laid.base)
        .expect("the rose trees type after their siblings");
    let whole = TypeTable::of_unit(&grammar, text, &laid.unit, laid.base)
        .expect("the rose trees type whole");
    let page = PageWidth::from(80_u32);
    let differing: Vec<usize> = (0 .. own.len())
        .filter(|&offset| {
            let at = ByteOffset::from(offset);
            after.at(at, page, Form::Explicit.into()) != whole.at(at, page, Form::Explicit.into())
        })
        .collect();
    assert!(
        after.spans().nth(100).is_some() && differing.is_empty(),
        "every byte answers alike, over more than a hundred entries: differing at {differing:?}"
    );
    assert!(
        after
            .declarations(page, Form::Explicit.into())
            .eq(whole.declarations(page, Form::Explicit.into())),
        "every declaration answers alike"
    );
    assert_eq!(
        after.declared_names(),
        whole.declared_names(),
        "every declared name is offered alike"
    );
    let read = |table: &TypeTable| -> Vec<(String, RoundTrip)> {
        table
            .read_back(&grammar, page, Form::Sugared.into())
            .into_iter()
            .map(|back| (back.spelled, back.trip))
            .collect()
    };
    assert_eq!(
        read(&after),
        read(&whole),
        "every printed type reads back alike"
    );
}

/// #3617: a match that leaves an arm to a pattern hole is refused in the
/// table typed alone as in the table its judgement keeps, and a match
/// with every arm written is refused in neither.
#[test]
fn a_pattern_hole_refuses_its_match_in_both_tables_3617()
{
    let grammar = built_in().expect("the built-in grammar builds");
    let refusals = |arms: &str| {
        let own = alloc::format!(
            include_str!(
                "typed/unformatted/a-pattern-hole-refuses-its-match-in-both-tables-3617-own.gandr"
            ),
            arms = arms
        );
        let text = SourceText::from(own.as_str());
        let alone = table(text);
        let Ok(gandr_surface_dispatcher::Lowered::Module { module, arena }) =
            gandr_surface_dispatcher::lower_source(
                &grammar,
                text,
                &mut gandr_surface_dispatcher::LoweringCount::default(),
            )
            .map(gandr_surface_dispatcher::Lowering::into_lowered)
        else {
            panic!("the source lowers to a module");
        };
        let (_judged, judged) = gandr_surface_dispatcher::judge_member_tabled::<Evaluator>(
            gandr_surface_corpus::CorpusRoot::Fixture,
            (module, text),
            arena,
            (
                &gandr_surface_dispatcher::HostGrant::UNBOUNDED,
                gandr_surface_dispatcher::Checking::Whole,
            ),
            (
                &gandr_surface_lowering::Unit::single(),
                ByteOffset::from(0_usize),
            ),
        );
        let Maybe::Present(judged) = judged
        else {
            panic!("the judgement keeps its table");
        };
        let read = |typed: &TypeTable| -> Vec<Option<String>> {
            typed
                .declared_keys()
                .map(|key| match typed.refusal(key) {
                    Maybe::Present(refusal) => Some(String::from(<&str>::from(refusal))),
                    Maybe::Absent(_) => None,
                })
                .collect()
        };
        (read(&alone), read(&judged))
    };
    let undecided = Some(String::from(
        "a pattern hole leaves the match's arm undecided",
    ));
    let (alone, judged) = refusals("| Red => return 0 | ? => return 1");
    assert!(
        alone.contains(&undecided) && alone == judged,
        "the match left to a pattern hole is refused alike in both tables: {alone:?} and {judged:?}"
    );
    let (alone, judged) = refusals("| Red => return 0 | Green => return 1 | Blue => return 2");
    assert!(
        alone.iter().all(Option::is_none) && alone == judged,
        "the match with every arm written is refused in neither table: {alone:?} and {judged:?}"
    );
}
