//! The run report's verdicts and counts over real compositions: each
//! composition names the run stage's engine, so these tests stand in the
//! `tests` target (#7048).

use gandr_core_checker::CheckBudget;
use gandr_core_checker::CheckingContext;
use gandr_core_checker::bridge;
use gandr_core_checker::check_module;
use gandr_core_term::CoreArena;
use gandr_core_term::FailureClass;
use gandr_surface_corpus::CorpusRoot;
use gandr_surface_corpus::settle;
use gandr_surface_dispatcher::Composed;
use gandr_surface_dispatcher::Exercised;
use gandr_surface_dispatcher::Goals;
use gandr_surface_dispatcher::LoweringCount;
use gandr_surface_dispatcher::Row;
use gandr_surface_dispatcher::RunReport;
use gandr_surface_dispatcher::RunVerdict;
use gandr_surface_dispatcher::Shown;
use gandr_surface_dispatcher::SourceCount;
use gandr_surface_dispatcher::SourceRoot;
use gandr_surface_dispatcher::Standing;
use gandr_surface_dispatcher::Verb;
use gandr_surface_dispatcher::adapt;
use gandr_surface_dispatcher::compose;
use gandr_surface_dispatcher::fixture;
use gandr_surface_dispatcher::positioned;
use gandr_surface_dispatcher::shown;
use gandr_surface_evaluate::Evaluator;
use gandr_surface_evaluate::Machine;
use gandr_surface_grammar::built_in;
use gandr_surface_lowering::DeclarationCount;
use gandr_surface_lowering::LoweringBudget;
use gandr_surface_lowering::lower_module;
use gandr_surface_lowering::namespace::Recognition;
use gandr_surface_parser::parse;
use gandr_surface_syntax::SourceText;

/// The verbs, every one.
const VERBS: [Verb; 3_usize] = [
    Verb::Check(Goals::Gated),
    Verb::Check(Goals::Reported),
    Verb::Test,
];

#[test]
fn each_verb_shows_its_declarations()
{
    let grammar = built_in().expect("the built-in grammar builds");
    let mut lowerings = LoweringCount::default();
    let Ok(Composed::Settled { report, .. }) = compose::<Evaluator>(
        &grammar,
        CorpusRoot::Fixture,
        SourceText::from(include_str!(
            "report/fixtures/each-verb-shows-its-declarations.gandr"
        )),
        &mut lowerings,
    )
    else {
        panic!("the module settles");
    };
    let rows = [
        ("fixture", [Shown::Counted, Shown::Counted, Shown::Line]),
        ("plain", [Shown::Counted, Shown::Counted, Shown::Counted]),
        ("hole", [Shown::Line, Shown::Goal, Shown::Line]),
        ("broken", [Shown::Line, Shown::Line, Shown::Line]),
    ];
    for ((name, expected), declaration) in rows.into_iter().zip(report.declarations()) {
        assert_eq!(declaration.name().to_string(), name, "admission order");
        for (verb, expected) in VERBS.into_iter().zip(expected) {
            assert_eq!(shown(declaration, verb), expected, "{name} under {verb:?}");
        }
    }
}

#[test]
fn each_count_decides_its_verdict()
{
    let grammar = built_in().expect("the built-in grammar builds");
    let settled_source = |source: &'static str| {
        let mut lowerings = LoweringCount::default();
        let Ok(composed @ Composed::Settled { .. }) = compose::<Evaluator>(
            &grammar,
            CorpusRoot::Fixture,
            SourceText::from(source),
            &mut lowerings,
        )
        else {
            panic!("{source} settles");
        };
        composed
    };
    let read = |source: &'static str, standing: Standing| {
        let composed = settled_source(source);
        let mut report = RunReport::default();
        fixture::read(&mut report, SourceRoot::Fixture, &composed, standing);
        report
    };
    let all = |report: &RunReport| VERBS.map(|verb| report.verdict(verb));

    assert_eq!(
        all(&read("def a = 1 ;", Standing::Settled)),
        [RunVerdict::Settled; 3_usize],
        "a settled run is settled under every verb"
    );
    assert_eq!(
        all(&read("def a : Integer ;", Standing::Unsettled)),
        [
            RunVerdict::Unsettled,
            RunVerdict::Settled,
            RunVerdict::Unsettled
        ],
        "an undeclared obligation is a goal under check --goals alone"
    );
    assert_eq!(
        all(&read(
            "def a : Integer ; def b = missing ;",
            Standing::Unsettled
        )),
        [RunVerdict::Unsettled; 3_usize],
        "one unsettled declaration beyond the goals fails every verb"
    );
    assert_eq!(
        all(&read("def a = 1 ;", Standing::Refused)),
        [RunVerdict::Unsettled; 3_usize],
        "a source refused as a whole fails every verb"
    );
    assert_eq!(
        all(&read("def a = 1 ;", Standing::Lowered)),
        [RunVerdict::Unsettled; 3_usize],
        "a pending source the lowering read fails every verb"
    );
    let mut faulted = read("def a : Integer ;", Standing::Unsettled);
    fixture::fault(&mut faulted);
    assert_eq!(
        all(&faulted),
        [RunVerdict::Faulted; 3_usize],
        "a faulted path faults every verb, over any unsettled declaration"
    );

    let source = SourceText::from(r#"@[ refuses("BudgetExceeded") ] def a = 1 ;"#);
    let tree = parse(&grammar, source).expect("parses").into_tree();
    let mut arena = CoreArena::new();
    let module = lower_module(
        &grammar,
        &tree,
        &mut arena,
        LoweringBudget::DEFAULT,
        Recognition::default(),
    )
    .expect("the module lowers");
    let declarations = adapt(&module, &arena);
    let verdicts = check_module(
        &mut CheckingContext::new(&mut arena, CheckBudget::from(0_usize)),
        &declarations,
    );
    let kernel = bridge::readmit(&mut arena, &verdicts).export(module.structured_names());
    let mut program = fixture::program(&arena, &module, &verdicts);
    let report = settle(
        CorpusRoot::Fixture,
        &arena,
        &module,
        &verdicts,
        &mut Machine::new(&mut program),
    )
    .expect("the verdicts are the module's");
    let composed = Composed::Settled {
        report,
        exercised: Exercised::default(),
        unstatable: Vec::new(),
        kernel: quenchant_shape::shape::Maybe::Present(kernel),
        positions: quenchant_shape::shape::Maybe::Absent(positioned::Absent::Unasked),
        origins: module.into_origins(),
        spellings: gandr_surface_diagnostics::TypeSpellings::default(),
        failures: gandr_surface_diagnostics::Failures::default(),
        shadowed: Vec::new(),
        inferred: Vec::new(),
        runs: Vec::new(),
        deprecated: Vec::new(),
        parted: Vec::new(),
        unused: Vec::new(),
        unreached: Vec::new(),
        program,
    };
    let mut engine = RunReport::default();
    fixture::read(
        &mut engine,
        SourceRoot::Fixture,
        &composed,
        Standing::Settled,
    );
    assert_eq!(
        engine.tally().refusals().count(FailureClass::EngineFault),
        DeclarationCount::from(1_usize),
        "an exhausted allowance is the engine's fault"
    );
    assert_eq!(
        usize::from(engine.tally().declarations().unsettled()),
        0_usize,
        "the declaration states its refusal, so it settles"
    );
    assert_eq!(
        all(&engine),
        [RunVerdict::Faulted; 3_usize],
        "an engine refusal faults every verb, even one a declaration states"
    );
}

#[test]
fn pending_sources_do_not_contribute_declarations_or_goals()
{
    let grammar = built_in().expect("the built-in grammar builds");
    let compose_source = |source: &'static str| {
        let mut lowerings = LoweringCount::default();
        compose::<Evaluator>(
            &grammar,
            CorpusRoot::Fixture,
            SourceText::from(source),
            &mut lowerings,
        )
        .expect("the fixture composes")
    };
    let ordinary = compose_source(
        "def identity : +U (Integer -> -F Integer) ; def identity = thunk { fun (x) { return x } } ; def hole : Integer ;",
    );
    let pending = compose_source(include_str!("report/unformatted/str-pending.gandr"));
    let mut report = RunReport::default();
    fixture::read(
        &mut report,
        SourceRoot::Fixture,
        &ordinary,
        Standing::of(SourceRoot::Fixture, &ordinary),
    );
    assert_eq!(DeclarationCount::from(1_usize), report.goals());
    assert_eq!(
        DeclarationCount::from(1_usize),
        report.exercised().count(Row::LambdaChecks)
    );
    let before = report;
    let standing = Standing::of(SourceRoot::Pending, &pending);
    assert_eq!(Standing::Pending, standing);
    fixture::read(&mut report, SourceRoot::Pending, &pending, standing);
    assert_eq!(before.tally(), report.tally());
    assert_eq!(before.exercised(), report.exercised());
    assert_eq!(before.goals(), report.goals());
    assert_eq!(SourceCount::from(1_usize), report.sources().pending());
    let standing = Standing::of(SourceRoot::Pending, &ordinary);
    assert_eq!(Standing::Lowered, standing);
    fixture::read(&mut report, SourceRoot::Pending, &ordinary, standing);
    assert_eq!(SourceCount::from(2_usize), report.sources().pending());
    assert_eq!(
        SourceCount::from(1_usize),
        report.sources().lowered_pending()
    );
    assert_eq!(DeclarationCount::from(2_usize), report.goals());
    assert_eq!(
        DeclarationCount::from(2_usize),
        report.exercised().count(Row::LambdaChecks)
    );
}
