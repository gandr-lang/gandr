//! Composition through the run stage's engine: each test composes, judges or
//! admits a source, so it stands in the `tests` target (#7048).

use anodized::spec;
use gandr_core_checker::CheckBudget;
use gandr_core_checker::CheckingContext;
use gandr_core_checker::Demand;
use gandr_core_checker::HostGrant;
use gandr_core_checker::ObligationCount;
use gandr_core_checker::Polled;
use gandr_core_checker::Retirement;
use gandr_core_checker::UnadmittedFormer;
use gandr_core_checker::Unretired;
use gandr_core_checker::Verdict;
use gandr_core_checker::bridge;
use gandr_core_checker::check_module;
use gandr_core_checker::worlds::WorldName;
use gandr_core_term::CoreArena;
use gandr_core_term::FailureClass;
use gandr_core_term::TrackingIssue;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::decode;
use gandr_surface_corpus::CorpusRoot;
use gandr_surface_corpus::KernelImage;
use gandr_surface_corpus::Outcome;
use gandr_surface_corpus::Produced;
use gandr_surface_corpus::RefusalName;
use gandr_surface_corpus::Settlement;
use gandr_surface_corpus::settle;
use gandr_surface_dispatcher::ComposeFault;
use gandr_surface_dispatcher::Composed;
use gandr_surface_dispatcher::KernelTier;
use gandr_surface_dispatcher::Lowered;
use gandr_surface_dispatcher::LoweringCount;
use gandr_surface_dispatcher::Unruled;
use gandr_surface_dispatcher::adapt;
use gandr_surface_dispatcher::admitted;
use gandr_surface_dispatcher::compose;
use gandr_surface_dispatcher::fixture;
use gandr_surface_dispatcher::fixture::WHOLE;
use gandr_surface_dispatcher::fixture::alone;
use gandr_surface_dispatcher::fixture::readmitted;
use gandr_surface_dispatcher::judge;
use gandr_surface_dispatcher::judge_module;
use gandr_surface_dispatcher::lower_source;
use gandr_surface_evaluate::Evaluator;
use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::built_in;
use gandr_surface_lowering::DeclarationOutcome;
use gandr_surface_lowering::FragmentBoundary;
use gandr_surface_lowering::LoweringBudget;
use gandr_surface_lowering::LoweringRefusal;
use gandr_surface_lowering::lower_module;
use gandr_surface_lowering::namespace::Recognition;
use gandr_surface_parser::parse;
use gandr_surface_pretty::Form;
use gandr_surface_pretty::PageWidth;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

/// The built-in grammar.
///
/// # Specification
/// - requires: the built-in grammar can be constructed.
/// - ensures: returns that checked grammar, including candidates for the
///   declaration keyword `def`.
/// - fails: never.
/// - panics: if the built-in grammar is invalid.
///
/// # Adequacy
/// - hypothesis: L3 — mixed declarations and a whole-source refusal are
///   interpreted with exact expected outcomes. These fixtures detect an
///   unusable or incompatible grammar, not equivalence over all syntax.
/// - witness: `tests::compose::a_module_settles_every_declaration_once`
/// - witness: `tests::compose::a_root_that_is_no_list_of_declarations_is_refused_whole`
#[spec(ensures: |ref ret|
    !ret.candidates(gandr_surface_grammar::TileLabel("def")).is_empty())]
fn grammar() -> Pbg
{
    built_in().expect("the built-in grammar builds")
}

/// #776: a closure judged once judges each document laid after it as a
/// closure judged fresh for that document does — two revisions in turn,
/// then the first again — down to the composition and the kernel's
/// artifact, each lowering counted by the document's own source; and each
/// reports of its own declarations what the whole unit, lowered and judged
/// whole, reports: their names, spans, statements, debts, waits, the kind
/// of each verdict, each outcome — a run of a closure's constant included —
/// and the spelling of each type a refusal compares, the closure refusing
/// one of its own declarations at its lowering and one at its check; and
/// every node the closure's fold elaborated from a located node is located
/// in the document's table, the document's own nested call carried after
/// its lowering.
#[test]
fn a_closure_judged_once_judges_each_document_alike_776()
{
    use alloc::string::String;
    use alloc::sync::Arc;
    use core::mem::Discriminant;

    use gandr_core_term::Carried;
    use gandr_surface_corpus::Outcome;
    use gandr_surface_corpus::Refusal;
    use gandr_surface_corpus::Stated;
    use gandr_surface_dispatcher::Checking;
    use gandr_surface_dispatcher::Judged;
    use gandr_surface_dispatcher::JudgedClosure;
    use gandr_surface_dispatcher::Lowering;
    use gandr_surface_dispatcher::judge_member;
    use gandr_surface_dispatcher::judge_member_after;
    use gandr_surface_dispatcher::lower_closure;
    use gandr_surface_dispatcher::lower_onto_closure;
    use gandr_surface_dispatcher::lower_parsed_unit;
    use gandr_surface_lowering::ImportTarget;
    use gandr_surface_lowering::LoweredModule;
    use gandr_surface_lowering::SourceIndex;
    use gandr_surface_lowering::SurfaceName;
    use gandr_surface_lowering::Unit;
    use gandr_surface_lowering::UnitSource;
    use gandr_surface_pretty::Spelling;
    use gandr_surface_syntax::ByteOffset;
    use gandr_surface_syntax::ByteSpan;

    /// One declaration's report: its name, span, statement, debt, waits,
    /// the kinds of what it produced and of its verdict, its outcome and
    /// the spellings of the types its refusal compares.
    type Reported<'source> = (
        SurfaceName<'source>,
        ByteSpan,
        Stated,
        ObligationCount,
        Vec<SurfaceName<'source>>,
        (
            Discriminant<Produced<'source>>,
            Option<Discriminant<Verdict>>,
        ),
        (Outcome, Vec<String>),
    );

    /// The module and arena `lowering` lowered to.
    ///
    /// # Specification
    /// trivial.
    fn module(lowering: Lowering<'_>) -> (LoweredModule<'_>, CoreArena)
    {
        match lowering.into_lowered() {
            Lowered::Module { module, arena } => (module, arena),
            Lowered::Refused(refusal) => panic!("refused whole: {refusal}"),
        }
    }

    /// `own`, laid after `judged`'s closure in `text` as `unit` lays it
    /// out from `base`, lowered after `judged`'s arena and judged after
    /// it.
    ///
    /// # Specification
    /// trivial.
    fn after<'held>(
        judged: &'held JudgedClosure,
        (own, text): (SourceText<'held>, SourceText<'held>),
        (unit, base): (&Unit, ByteOffset),
        lowerings: &mut LoweringCount,
    ) -> Judged<'held>
    {
        let closure = judged.lowering();
        let parsed = parse(closure.grammar(), own)
            .expect("the document parses")
            .after(closure.tree(), text)
            .expect("the document lays after its closure");
        let (lowering, checking) = lower_onto_closure(
            judged,
            judged.arena(),
            parsed,
            unit,
            lowerings,
            &mut gandr_surface_lowering::coincide::Decisions::none(),
        )
        .expect("the document lowers");
        assert!(
            matches!(checking, Checking::After(_)),
            "the document is judged after the closure"
        );
        let (module, arena) = module(lowering);
        judge_member_after::<Evaluator>(
            CorpusRoot::Strict,
            (module, text),
            arena,
            (&HostGrant::UNBOUNDED, checking),
            base,
        )
    }

    /// Each declaration `judged` reports, its ids set aside.
    ///
    /// # Specification
    /// trivial.
    fn reported(judged: Judged<'_>) -> Vec<Reported<'_>>
    {
        let Ok(Composed::Settled {
            report, spellings, ..
        }) = judged.into_parts().0
        else {
            panic!("the document settles");
        };
        let spelled = spellings.spelled(Spelling::Unicode);
        report
            .declarations()
            .iter()
            .map(|declaration| {
                let produced = declaration.produced();
                let verdict = match produced {
                    Produced::Judged(verdict) => Some(core::mem::discriminant(&verdict)),
                    Produced::Unlowered(_) | Produced::Guarded(_) => None,
                };
                let compared = match produced.refusal() {
                    Maybe::Present(Refusal::Checking(refusal)) => {
                        let compared = refusal.compared();
                        [compared.expected, compared.found]
                            .into_iter()
                            .map(|side| match side {
                                Maybe::Present(node) => match spelled.get(node) {
                                    Maybe::Present(spelling) => String::from(spelling.as_ref()),
                                    Maybe::Absent(_) => String::from("unspelled"),
                                },
                                Maybe::Absent(_) => String::from("absent"),
                            })
                            .collect()
                    },
                    Maybe::Present(Refusal::Lowering(_) | Refusal::Corpus(_))
                    | Maybe::Absent(_) => Vec::new(),
                };
                (
                    declaration.name(),
                    declaration.span(),
                    declaration.stated().clone(),
                    declaration.owed(),
                    declaration.waits().to_vec(),
                    (core::mem::discriminant(&produced), verdict),
                    (declaration.outcome(), compared),
                )
            })
            .collect()
    }

    let pbg = grammar();
    // The fold's nested calls and `told`'s are elaborated: the closure's
    // nodes are located before the document's lowering, the document's
    // after it.
    let closure_text = include_str!("compose/fixtures/reported-closure-text.gandr");
    let first = include_str!("compose/fixtures/reported-first.gandr");
    let second = include_str!("compose/fixtures/reported-second.gandr");
    let base = ByteOffset::from(closure_text.len());
    let unit = Unit::new(vec![
        UnitSource::new(ByteOffset::from(0_usize), Vec::new()),
        UnitSource::new(base, vec![ImportTarget::Source(SourceIndex::from(0_usize))]),
    ])
    .expect("two sources make a unit");
    let mut lowerings = LoweringCount::default();
    let closure = Arc::new(
        lower_closure(
            Arc::new(grammar()),
            String::from(closure_text),
            Unit::new(vec![UnitSource::new(ByteOffset::from(0_usize), Vec::new())])
                .expect("one source makes a unit"),
            &mut lowerings,
        )
        .expect("the closure is held"),
    );
    let held = JudgedClosure::new::<Evaluator>(
        Arc::clone(&closure),
        &HostGrant::UNBOUNDED,
        CorpusRoot::Strict,
    )
    .expect("the closure lowers to its end");
    for (step, own) in [first, second, first].into_iter().enumerate() {
        let text = format!("{closure_text}{own}");
        let text = SourceText::from(text.as_str());
        let parsed = || {
            parse(&pbg, SourceText::from(own))
                .expect("the document parses")
                .after(closure.tree(), text)
                .expect("the document lays after its closure")
        };
        let judged = after(
            &held,
            (SourceText::from(own), text),
            (&unit, base),
            &mut lowerings,
        );
        assert_eq!(
            lowerings,
            LoweringCount::from(step.saturating_add(2_usize)),
            "each document counts its own source"
        );
        let Ok(Composed::Settled { ref origins, .. }) = *judged.settled()
        else {
            panic!("the document settles");
        };
        let carried = held.carried();
        assert!(!carried.is_empty(), "the closure's fold is elaborated");
        for &pair in carried {
            let (source, minted) = match pair {
                Carried::Value(source, minted) => (origins.value(source), origins.value(minted)),
                Carried::Computation(source, minted) => {
                    (origins.computation(source), origins.computation(minted))
                },
                Carried::ValueType(source, minted) => {
                    (origins.value_type(source), origins.value_type(minted))
                },
                Carried::CompType(source, minted) => {
                    (origins.comp_type(source), origins.comp_type(minted))
                },
            };
            assert!(
                matches!(source, Maybe::Absent(_)) || matches!(minted, Maybe::Present(_)),
                "revision {step} locates {pair:?}, which the closure's fold minted"
            );
        }
        let fresh_closure = JudgedClosure::new::<Evaluator>(
            Arc::clone(&closure),
            &HostGrant::UNBOUNDED,
            CorpusRoot::Strict,
        )
        .expect("the closure lowers to its end");
        let fresh = after(
            &fresh_closure,
            (SourceText::from(own), text),
            (&unit, base),
            &mut LoweringCount::default(),
        );
        assert_eq!(
            judged.settled(),
            fresh.settled(),
            "revision {step} composes as on a fresh judgement of its closure"
        );
        let kernel = judged
            .clone()
            .into_parts()
            .1
            .admit()
            .expect("the kernel readmits the document");
        assert_eq!(
            kernel,
            fresh.into_parts().1.admit().expect("and the fresh one"),
            "to one artifact"
        );
        let (whole_module, whole_arena) = module(
            lower_parsed_unit(
                &pbg,
                parsed(),
                &unit,
                &mut LoweringCount::default(),
                &mut gandr_surface_lowering::coincide::Decisions::none(),
            )
            .expect("the whole unit lowers"),
        );
        let whole = judge_member::<Evaluator>(
            CorpusRoot::Strict,
            (whole_module, text),
            whole_arena,
            &HostGrant::UNBOUNDED,
            base,
        );
        assert_eq!(
            reported(judged),
            reported(whole),
            "revision {step} reports what the whole unit reports"
        );
    }
}

/// `source` composed under `root`, which must settle.
///
/// # Specification
/// - requires: the grammar admits the named fixture declarations and their
///   source composes to a module without an engine fault.
/// - ensures: returns that module's report; every reported name occurs in the
///   supplied source.
/// - fails: never.
/// - panics: if composition faults or refuses the source as a whole.
///
/// # Adequacy
/// - hypothesis: L3 — literal names, outcomes and ledger counts in a mixed
///   fixture separate lost declarations and wrong root policies. The witnesses
///   use explicit simple names, not every naming form or failure.
/// - witness: `tests::compose::a_module_settles_every_declaration_once`
/// - witness: `tests::compose::the_root_decides_what_an_expectation_means`
#[spec(ensures: |ref ret| ret.declarations().iter()
        .all(|declaration| source.as_ref().contains(declaration.name().as_ref())))]
fn settled<'source>(
    grammar: &Pbg,
    root: CorpusRoot,
    source: SourceText<'source>,
) -> gandr_surface_corpus::SettleReport<'source>
{
    let mut lowerings = LoweringCount::default();
    match compose::<Evaluator>(grammar, root, source, &mut lowerings) {
        Ok(Composed::Settled { report, .. }) => report,
        Ok(Composed::Refused(refusal)) => panic!("refused as a whole: {refusal}"),
        Err(fault) => panic!("faulted: {fault}"),
    }
}

#[test]
fn a_module_settles_every_declaration_once()
{
    let grammar = grammar();
    let report = settled(
        &grammar,
        CorpusRoot::Fixture,
        SourceText::from(include_str!(
            "compose/fixtures/a-module-settles-every-declaration-once-report.gandr"
        )),
    );
    let rows: Vec<(String, Settlement, Outcome)> = report
        .declarations()
        .iter()
        .map(|declaration| {
            (
                declaration.name().to_string(),
                declaration.settlement(),
                declaration.outcome(),
            )
        })
        .collect();
    let checks = |owed: usize| Outcome::Checks(gandr_core_checker::ObligationCount::from(owed));
    assert_eq!(
        rows,
        vec![
            ("answer".to_owned(), Settlement::Settled, checks(0)),
            ("copy".to_owned(), Settlement::Settled, checks(0)),
            ("later".to_owned(), Settlement::Settled, checks(1)),
            (
                "broken".to_owned(),
                Settlement::Settled,
                Outcome::Refuses(gandr_surface_corpus::RefusalName::UnresolvedName)
            ),
            (
                "wrong".to_owned(),
                Settlement::Unsettled,
                Outcome::Refuses(gandr_surface_corpus::RefusalName::TypeMismatch)
            ),
        ],
        "one report per declared name, in admission order"
    );
    assert!(
        matches!(
            report.declarations()[0].produced(),
            Produced::Judged(Verdict::Checked { .. })
        ),
        "a signed body checks"
    );
    assert!(
        matches!(
            report.declarations()[1].produced(),
            Produced::Judged(Verdict::Synthesised { .. })
        ),
        "an unsigned body synthesises"
    );
    assert_eq!(
        usize::from(report.ledger()),
        1_usize,
        "the owed signature is the module's one obligation"
    );
}

#[test]
fn a_host_entry_names_the_worlds_a_module_declares()
{
    let grammar = grammar();
    let source = SourceText::from(include_str!(
        "compose/fixtures/a-host-entry-names-the-worlds-a-module-declares.gandr"
    ));
    let moved = |grant: &HostGrant| {
        let Lowered::Module { module, arena } =
            lower_source(&grammar, source, &mut LoweringCount::default())
                .expect("the module lowers")
                .into_lowered()
        else {
            panic!("the module is not refused whole");
        };
        match judge_module::<Evaluator>(CorpusRoot::Fixture, (module, source), arena, grant) {
            Ok(Composed::Settled { report, .. }) => report
                .declarations()
                .last()
                .map(gandr_surface_corpus::DeclarationReport::outcome),
            Ok(Composed::Refused(refusal)) => panic!("refused as a whole: {refusal}"),
            Err(fault) => panic!("faulted: {fault}"),
        }
    };
    let [operator, seat, elsewhere] = ["operator", "seat", "elsewhere"].map(WorldName::from);
    assert_eq!(
        moved(&HostGrant::UNBOUNDED),
        Some(Outcome::Refuses(RefusalName::CapabilityMissing)),
        "without an entry the migration holds no capability"
    );
    assert_eq!(
        moved(&HostGrant::UNBOUNDED.entering(vec![operator.clone(), seat])),
        Some(Outcome::Checks(ObligationCount::from(0_usize))),
        "the host's entry at the operator holds one capability to the seat"
    );
    assert_eq!(
        moved(&HostGrant::UNBOUNDED.entering(vec![operator, elsewhere])),
        Some(Outcome::Refuses(RefusalName::HostWorldUndeclared)),
        "a world the module declares nowhere grants nothing"
    );
}

#[test]
fn an_effectful_declaration_stays_on_the_checkers_side()
{
    let listed = fixture::Listed::hosted(include_str!(
        "compose/fixtures/an-effectful-declaration-stays-on-the-checkers-side-listed.gandr"
    ));
    let Composed::Settled { report, .. } = listed.composed::<Evaluator>(CorpusRoot::Strict)
    else {
        panic!("the source composes");
    };
    let rows: Vec<(String, Settlement)> = report
        .declarations()
        .iter()
        .map(|declaration| (declaration.name().to_string(), declaration.settlement()))
        .collect();
    assert_eq!(
        rows,
        vec![
            ("peek".to_owned(), Settlement::Settled),
            ("quit".to_owned(), Settlement::Settled),
            ("answer".to_owned(), Settlement::Settled),
        ],
        "the kernel's refusal of an exercise and a scope is no disagreement, \
             and the pure declaration beside them is still readmitted"
    );
}

#[test]
fn an_endpoint_loop_settles_with_no_kernel_image_6047()
{
    use gandr_surface_dispatcher::Goals;
    use gandr_surface_dispatcher::Shown;
    use gandr_surface_dispatcher::Verb;
    use gandr_surface_dispatcher::shown;

    let grammar = grammar();
    let mut lowerings = LoweringCount::default();
    let report = match compose::<Evaluator>(
        &grammar,
        CorpusRoot::Fixture,
        SourceText::from(include_str!(
            "compose/fixtures/an-endpoint-loop-settles-with-no-kernel-image-6047.gandr"
        )),
        &mut lowerings,
    ) {
        Ok(Composed::Settled { report, .. }) => report,
        Ok(Composed::Refused(refusal)) => panic!("the source lowers: {refusal}"),
        Err(fault) => panic!("an endpoint loop is no disagreement: {fault}"),
    };
    let declined = KernelImage::Declined {
        former: UnadmittedFormer::EndpointLoop,
        class: FailureClass::Unimplemented(TrackingIssue::KERNEL_ENDPOINT_LOOP),
    };
    let rows: Vec<(String, Settlement, KernelImage, Shown)> = report
        .declarations()
        .iter()
        .map(|declaration| {
            (
                declaration.name().to_string(),
                declaration.settlement(),
                declaration.image(),
                shown(declaration, Verb::Check(Goals::Gated)),
            )
        })
        .collect();
    assert_eq!(
        rows,
        vec![
            (
                "beacon".to_owned(),
                Settlement::Settled,
                declined,
                Shown::Line
            ),
            (
                "asking".to_owned(),
                Settlement::Settled,
                declined,
                Shown::Line
            ),
            (
                "answer".to_owned(),
                Settlement::Settled,
                KernelImage::Offered,
                Shown::Counted
            ),
        ],
        "the send-only loop and the receiving loop each settle with no kernel image, \
             and each has a line under `check`; the plain definition beside them crosses"
    );
    let tally = report.tally();
    assert_eq!(
        (
            usize::from(tally.declarations().settled()),
            usize::from(tally.declarations().declined()),
            usize::from(tally.declarations().unsettled())
        ),
        (1_usize, 2_usize, 0_usize),
        "the two loops count apart from the settled"
    );
}

#[test]
fn a_root_that_is_no_list_of_declarations_is_refused_whole()
{
    let grammar = grammar();
    let mut lowerings = LoweringCount::default();
    let composed = compose::<Evaluator>(
        &grammar,
        CorpusRoot::Fixture,
        SourceText::from("@[ checks ]"),
        &mut lowerings,
    );
    let Ok(Composed::Refused(refusal)) = composed
    else {
        panic!("a root of an attribute block that decorates nothing refuses the module");
    };
    assert!(
        matches!(refusal, LoweringRefusal::OutOfFragment {
            boundary: FragmentBoundary::WrongSort,
            ..
        }),
        "a root child that is no declaration is out of the fragment: {refusal}"
    );
    assert_eq!(
        refusal.classify(),
        FailureClass::MalformedSource,
        "a block that decorates nothing is a stray"
    );
}

#[test]
fn each_composition_lowers_once()
{
    let grammar = grammar();
    let mut lowerings = LoweringCount::default();
    let sources = [
        "def a = 3 ;",
        "pure 3",
        r#"@[ refuses("UnresolvedName") ] def a = b ;"#,
    ];
    for (composed, source) in sources.into_iter().enumerate() {
        let result = compose::<Evaluator>(
            &grammar,
            CorpusRoot::Fixture,
            SourceText::from(source),
            &mut lowerings,
        );
        assert!(result.is_ok(), "{source} composes");
        assert_eq!(
            usize::from(lowerings),
            composed.saturating_add(1_usize),
            "each composition lowers exactly once"
        );
    }
}

#[test]
fn the_root_decides_what_an_expectation_means()
{
    let grammar = grammar();
    let source = SourceText::from(r#"@[ owes(1) ] def later : Integer ;"#);
    let fixture = settled(&grammar, CorpusRoot::Fixture, source);
    let strict = settled(&grammar, CorpusRoot::Strict, source);
    assert_eq!(
        fixture.declarations()[0].settlement(),
        Settlement::Settled,
        "the fixture root reads the expectation"
    );
    assert_eq!(
        strict.declarations()[0].settlement(),
        Settlement::Unsettled,
        "the strict root refuses it"
    );
    assert_eq!(
        strict.declarations()[0].outcome(),
        Outcome::Refuses(gandr_surface_corpus::RefusalName::ExpectationOutsideFixtureRoot),
        "the guard stands in for what the declaration produced"
    );
}

#[test]
fn a_refusal_at_a_declaration_form_is_unstatable()
{
    let grammar = grammar();
    let mut lowerings = LoweringCount::default();
    let composed = compose::<Evaluator>(
        &grammar,
        CorpusRoot::Fixture,
        SourceText::from(include_str!(
            "compose/fixtures/a-refusal-at-a-declaration-form-is-unstatable-composed.gandr"
        )),
        &mut lowerings,
    );
    let Ok(Composed::Settled {
        report, unstatable, ..
    }) = composed
    else {
        panic!("the module lowers");
    };
    assert!(
        matches!(unstatable.as_slice(), [
            LoweringRefusal::UnknownMember { .. }
        ]),
        "the component no member supplies is held with no form keyed, and only it: \
             {unstatable:?}"
    );
    let settlements: Vec<(String, Settlement)> = report
        .declarations()
        .iter()
        .map(|declaration| {
            (
                String::from(declaration.name().as_ref()),
                declaration.settlement(),
            )
        })
        .collect();
    assert_eq!(
        settlements,
        vec![
            (String::from("f"), Settlement::Settled),
            (String::from("g"), Settlement::Settled),
            (String::from("h"), Settlement::Settled),
            (String::from("x"), Settlement::Settled),
            (String::from("z"), Settlement::Unsettled),
        ],
        "a form refused at collection states its refusal (#1798), as a refused body \
             does; the held component cannot"
    );
}

#[test]
fn a_tail_without_a_result_type_lowers_unsigned()
{
    let grammar = grammar();
    let source = SourceText::from("def f(x : Integer) { return x }");
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
    assert!(
        matches!(
            module.declarations().iter().next().unwrap().outcome(),
            DeclarationOutcome::Bodied { .. }
        ),
        "the lowering writes the body alone and refuses nothing"
    );
    assert_eq!(
        settled(&grammar, CorpusRoot::Fixture, source).declarations()[0].outcome(),
        Outcome::Refuses(RefusalName::NotSynthesisable),
        "the checker, not the lowering, refuses the body it cannot type"
    );
}

/// A composite whose first cell is a call to a defined composite, against
/// the composite of that definition's body. One unfolding of the call
/// relates the two, and the kernel re-derives the reflexivity as the
/// checker accepts it.
#[test]
fn a_composite_after_a_call_to_a_defined_composite_replays_4246()
{
    let grammar = grammar();
    let report = settled(
        &grammar,
        CorpusRoot::Strict,
        SourceText::from(include_str!(
            "compose/fixtures/a-composite-after-a-call-to-a-defined-composite-replays-4246-report.gandr"
        )),
    );
    let outcomes: Vec<(String, Outcome)> = report
        .declarations()
        .iter()
        .map(|declaration| (declaration.name().to_string(), declaration.outcome()))
        .collect();
    let checks = Outcome::Checks(gandr_core_checker::ObligationCount::from(0_usize));
    assert_eq!(
        outcomes,
        ["liftLeft", "two", "unfolded"]
            .map(|name| (name.to_owned(), checks.clone()))
            .to_vec(),
        "every definition checks, and the kernel re-derives each"
    );
}

/// A defined 2-path whiskered by the reflexivity at its end, against the
/// 2-path. The whisker unfolds to the lift under a bind into `Path.ap` of
/// `Path.step(q, Path.here(z))`, which reads as the identity, and the
/// kernel re-derives the reflexivity as the checker accepts it.
#[test]
fn a_defined_two_path_whiskered_by_a_reflexivity_replays_4255()
{
    let grammar = grammar();
    let report = settled(
        &grammar,
        CorpusRoot::Strict,
        SourceText::from(include_str!(
            "compose/fixtures/a-defined-two-path-whiskered-by-a-reflexivity-replays-4255-report.gandr"
        )),
    );
    let outcomes: Vec<(String, Outcome)> = report
        .declarations()
        .iter()
        .map(|declaration| (declaration.name().to_string(), declaration.outcome()))
        .collect();
    let checks = Outcome::Checks(gandr_core_checker::ObligationCount::from(0_usize));
    assert_eq!(
        outcomes,
        ["ap", "whiskerRight", "liftRight", "whiskeredByHere"]
            .map(|name| (name.to_owned(), checks.clone()))
            .to_vec(),
        "every definition checks, and the kernel re-derives each"
    );
}

/// Three calls of a defined path composed to the left, against the
/// reflexivity, and the same at a defined 2-path. The inner transport's
/// run returns the middle call, which the outer transport's run takes as
/// its operand, and the kernel runs it as the checker's append does.
#[test]
fn three_defined_paths_composed_replay_4412()
{
    let grammar = grammar();
    let report = settled(
        &grammar,
        CorpusRoot::Strict,
        SourceText::from(include_str!(
            "compose/fixtures/three-defined-paths-composed-replay-4412-report.gandr"
        )),
    );
    let outcomes: Vec<(String, Outcome)> = report
        .declarations()
        .iter()
        .map(|declaration| (declaration.name().to_string(), declaration.outcome()))
        .collect();
    let checks = Outcome::Checks(gandr_core_checker::ObligationCount::from(0_usize));
    assert_eq!(
        outcomes,
        ["p", "three", "r", "threeTwoPaths"]
            .map(|name| (name.to_owned(), checks.clone()))
            .to_vec(),
        "every definition checks, and the kernel re-derives each"
    );
}

/// A whisker, the inverse of an associator and a whisker, composed at
/// reflexivities against the reflexivity's reflexivity. The kernel
/// re-derives the composite the checker accepts.
#[test]
fn a_whisker_an_inverse_associator_and_a_whisker_replay_4413()
{
    let grammar = grammar();
    let report = settled(
        &grammar,
        CorpusRoot::Strict,
        SourceText::from(include_str!(
            "compose/fixtures/a-whisker-an-inverse-associator-and-a-whisker-replay-4413-report.gandr"
        )),
    );
    let outcomes: Vec<(String, Outcome)> = report
        .declarations()
        .iter()
        .map(|declaration| (declaration.name().to_string(), declaration.outcome()))
        .collect();
    let checks = Outcome::Checks(gandr_core_checker::ObligationCount::from(0_usize));
    assert_eq!(
        outcomes,
        ["ap", "whiskerLeft", "whiskerRight", "assoc", "whiskered"]
            .map(|name| (name.to_owned(), checks.clone()))
            .to_vec(),
        "every definition checks, and the kernel re-derives each"
    );
}

/// A defined chain of an associator, a level-two whisker, an inverse
/// associator, a level-two whisker and an associator, called at
/// reflexivities against the reflexivity's reflexivity. The kernel
/// re-derives the call the checker accepts.
#[test]
fn a_defined_chain_of_level_two_whiskers_replays_at_reflexivities_4419()
{
    let grammar = grammar();
    let report = settled(
        &grammar,
        CorpusRoot::Strict,
        SourceText::from(include_str!(
            "compose/unformatted/a-defined-chain-of-level-two-whiskers-replays-at-reflexivities-4419-report.gandr"
        )),
    );
    let outcomes: Vec<(String, Outcome)> = report
        .declarations()
        .iter()
        .map(|declaration| (declaration.name().to_string(), declaration.outcome()))
        .collect();
    let checks = Outcome::Checks(gandr_core_checker::ObligationCount::from(0_usize));
    assert_eq!(
        outcomes,
        [
            "whiskerLeft",
            "whiskerRight",
            "assoc",
            "cylinderComposite2",
            "cylinderCompositeAtHere"
        ]
        .map(|name| (name.to_owned(), checks.clone()))
        .to_vec(),
        "every definition checks, and the kernel re-derives each"
    );
}

/// A stack of two squares, the side-by-side composite of their reversed
/// squares reversed, with the whiskers level-two composites, called at
/// reflexivities: the kernel re-derives the call the checker accepts.
#[test]
fn a_stack_of_level_two_whiskered_squares_replays_at_reflexivities_4435()
{
    let grammar = grammar();
    let report = settled(
        &grammar,
        CorpusRoot::Strict,
        SourceText::from(include_str!(
            "compose/unformatted/a-stack-of-level-two-whiskered-squares-replays-at-reflexivities-4435-report.gandr"
        )),
    );
    let outcomes: Vec<(String, Outcome)> = report
        .declarations()
        .iter()
        .map(|declaration| (declaration.name().to_string(), declaration.outcome()))
        .collect();
    let checks = Outcome::Checks(gandr_core_checker::ObligationCount::from(0_usize));
    assert_eq!(
        outcomes,
        [
            "whiskerLeft",
            "whiskerRight",
            "assoc",
            "cylinderComposite2",
            "cylinderStack2",
            "cylinderStackAtHere"
        ]
        .map(|name| (name.to_owned(), checks.clone()))
        .to_vec(),
        "every definition checks, and the kernel re-derives each"
    );
}

/// A fill whose generator's body is itself a fill, read at reflexivities:
/// the outer fill reaches its base, the generator at the source face, and
/// the inner fill there reaches its own. The kernel re-derives the
/// definition comparing them, as the checker accepts it.
#[test]
fn a_fill_whose_generator_holds_a_fill_replays_at_reflexivities_4186()
{
    let grammar = grammar();
    let report = settled(
        &grammar,
        CorpusRoot::Strict,
        SourceText::from(include_str!(
            "compose/fixtures/a-fill-whose-generator-holds-a-fill-replays-at-reflexivities-4186-report.gandr"
        )),
    );
    let outcomes: Vec<(String, Outcome)> = report
        .declarations()
        .iter()
        .map(|declaration| (declaration.name().to_string(), declaration.outcome()))
        .collect();
    let checks = Outcome::Checks(gandr_core_checker::ObligationCount::from(0_usize));
    assert_eq!(
        outcomes,
        [
            "join",
            "composedCells",
            "selfFill",
            "selfFillOver",
            "liftRight",
            "nestedFill",
            "nestedAtHere"
        ]
        .map(|name| (name.to_owned(), checks.clone()))
        .to_vec(),
        "every definition checks, and the kernel re-derives each"
    );
}

#[test]
fn a_judged_module_renders_before_its_admission()
{
    // The second module applies a static operator at three instances, so
    // its readmission mints their reducts into the arena.
    let sources = [
        r#"def a : Integer ; def a = 1 ; @[ owes(1) ] def later : Integer ; def w : Integer ; def w = "text" ; def r = w ;"#,
        include_str!("../../surface-corpus/strict/classifier/relative-monad.gandr"),
    ];
    let grammar = grammar();
    for source in sources {
        let mut lowerings = LoweringCount::default();
        let lower = |lowerings: &mut LoweringCount| {
            let Lowered::Module { module, arena } =
                lower_source(&grammar, SourceText::from(source), lowerings)
                    .expect("the module lowers")
                    .into_lowered()
            else {
                panic!("the module is not refused whole");
            };
            (module, arena)
        };
        // The order the composition ran before: readmit, then settle.
        let (mut module, mut arena) = lower(&mut lowerings);
        let declarations = adapt(&module, &arena);
        let verdicts = check_module(
            &mut CheckingContext::new(&mut arena, CheckBudget::DEFAULT),
            &declarations,
        );
        let readmission = readmitted(
            &mut arena,
            &verdicts,
            WHOLE,
            (&Unretired, &mut bridge::Untimed),
        )
        .whole()
        .0
        .expect("the kernel re-derives every acceptance");
        let kernel = readmission.export(module.structured_names());
        let mut program = fixture::program(&arena, &module, &verdicts);
        let report = settle(
            CorpusRoot::Fixture,
            &arena,
            &module,
            &verdicts,
            &mut gandr_surface_evaluate::Machine::new(&mut program),
        )
        .expect("the verdicts settle");
        let exercised = fixture::exercised(&arena, &module, &report);
        let unstatable = fixture::unstatable(&module);
        let failures = gandr_surface_diagnostics::Failures::of(&verdicts);
        fixture::located(
            module.origins_mut(),
            &verdicts,
            ConstantIndex::from(0_usize),
        );
        let spellings = gandr_surface_diagnostics::TypeSpellings::of(
            &arena,
            &module,
            &report,
            &failures,
            (module.origins(), SourceText::from(source)),
        );
        let shadowed = module.recognition().shadowed().to_vec();
        let inferred = module.inferred_exits().to_vec();
        let runs = fixture::inferred_runs(&module, &verdicts);
        let deprecated = module.deprecated_uses(&arena);
        let unused = fixture::unused_binders(&arena, &module, &report, |_| true);
        let readmitted_first = Composed::Settled {
            report,
            exercised,
            unstatable,
            origins: module.into_origins(),
            spellings,
            failures,
            shadowed,
            inferred,
            runs,
            deprecated,
            parted: Vec::new(),
            unused,
            unreached: Vec::new(),
            kernel: Maybe::Present(kernel),
            positions: Maybe::Absent(gandr_surface_dispatcher::positioned::Absent::Unasked),
            program,
        };
        let (module, arena) = lower(&mut lowerings);
        let judged = judge::<Evaluator>(
            CorpusRoot::Fixture,
            (module, SourceText::from(source)),
            arena,
            &HostGrant::UNBOUNDED,
        );
        let Ok(
            ref settled @ Composed::Settled {
                kernel: Maybe::Absent(admitted::Absent::Pending),
                ..
            },
        ) = *judged.settled()
        else {
            panic!("the module settles before its admission");
        };
        let Composed::Settled {
            kernel: Maybe::Present(ref kernel),
            ..
        } = readmitted_first
        else {
            panic!("the module settles after its readmission");
        };
        assert_eq!(
            settled.clone().admitted(
                kernel.clone(),
                Maybe::Absent(gandr_surface_dispatcher::positioned::Absent::Unasked),
                &[]
            ),
            readmitted_first,
            "settling before the readmission reads what settling after it read"
        );
        assert!(
            judged
                .admit()
                .is_ok_and(|admitted| admitted == readmitted_first),
            "the admission completes the composition with the same kernel artifact"
        );
    }
}

/// #776: an admission resumed from the record another revision's
/// admission made of the declarations both lead with exports, byte for
/// byte, what a whole admission of the revision exports, crossing only the
/// revision's own declarations.
#[test]
fn a_resumed_admission_exports_what_a_whole_one_does_776()
{
    let grammar = grammar();
    let closure = include_str!(
        "compose/fixtures/a-resumed-admission-exports-what-a-whole-one-does-776-closure.gandr"
    );
    let first = format!("{closure}def three : Integer ; def three = two ;");
    let later = format!(
        include_str!(
            "compose/unformatted/a-resumed-admission-exports-what-a-whole-one-does-776-later.gandr"
        ),
        closure = closure
    );
    let admission = |text: &str| {
        let Lowered::Module { module, arena } = lower_source(
            &grammar,
            SourceText::from(text),
            &mut LoweringCount::default(),
        )
        .expect("the revision lowers")
        .into_lowered()
        else {
            panic!("the revision is not refused whole");
        };
        judge::<Evaluator>(
            CorpusRoot::Fixture,
            (module, SourceText::from(text)),
            arena,
            &HostGrant::UNBOUNDED,
        )
        .into_parts()
        .1
    };
    let recorded = admission(&first).admit_resuming(
        bridge::LeadingCount::from(2_usize),
        Maybe::Absent(bridge::crossed::Absent::Unasked),
    );
    assert!(recorded.artifact.is_ok(), "{:?}", recorded.artifact);
    assert_eq!(
        usize::from(recorded.resumed),
        0_usize,
        "nothing was held to resume"
    );
    let Maybe::Present(ref crossed) = recorded.crossed
    else {
        panic!("the closure is recorded: {:?}", recorded.crossed);
    };
    let whole = admission(&later).admit();
    let resumed = admission(&later)
        .admit_resuming(bridge::LeadingCount::from(2_usize), Maybe::Present(crossed));
    assert_eq!(
        (usize::from(resumed.resumed), usize::from(resumed.judged)),
        (2_usize, 4_usize),
        "the closure's two declarations are resumed, and the revision's own two cross"
    );
    assert_eq!(
        resumed.artifact, whole,
        "the resumed artifact is the whole one, byte for byte"
    );
}

/// A poll that answers wanted a number of times, then retired.
#[repr(transparent)]
struct After(core::cell::Cell<usize>);

impl Retirement for After
{
    type Retired = ();

    /// Wanted while polls are left, then retired.
    ///
    /// # Specification
    /// trivial.
    fn demand(&self) -> Demand<()>
    {
        self.0
            .get()
            .checked_sub(1_usize)
            .map_or(Demand::Retired(()), |left| {
                self.0.set(left);
                Demand::Wanted
            })
    }
}

/// #1547: an admission retired before its third declaration answers the
/// record of the two it crossed, and an admission resumed from that record
/// exports, byte for byte, what a whole admission exports, crossing only
/// the third.
#[test]
fn a_retired_admission_resumes_from_its_record_1547()
{
    let grammar = grammar();
    let text =
        include_str!("compose/fixtures/a-retired-admission-resumes-from-its-record-1547.gandr");
    let admission = || {
        let Lowered::Module { module, arena } = lower_source(
            &grammar,
            SourceText::from(text),
            &mut LoweringCount::default(),
        )
        .expect("the revision lowers")
        .into_lowered()
        else {
            panic!("the revision is not refused whole");
        };
        judge::<Evaluator>(
            CorpusRoot::Fixture,
            (module, SourceText::from(text)),
            arena,
            &HostGrant::UNBOUNDED,
        )
        .into_parts()
        .1
    };
    let Polled::Retired((), Maybe::Present(record)) = admission().admit_retiring(
        bridge::LeadingCount::from(3_usize),
        Maybe::Absent(bridge::crossed::Absent::Unasked),
        &After(core::cell::Cell::new(2_usize)),
    )
    else {
        panic!("the admission is retired before its third declaration with a record");
    };
    assert_eq!(
        usize::from(record.boundary()),
        2_usize,
        "the record holds the two declarations crossed before the retirement"
    );
    let whole = admission().admit();
    let resumed = admission()
        .admit_retiring(
            bridge::LeadingCount::from(3_usize),
            Maybe::Present(&record),
            &Unretired,
        )
        .whole();
    assert_eq!(
        (usize::from(resumed.resumed), usize::from(resumed.judged)),
        (2_usize, 3_usize),
        "the two crossed before the retirement are resumed, and the third crosses"
    );
    assert_eq!(
        resumed.artifact, whole,
        "the resumed artifact is the whole one, byte for byte"
    );
}

/// #2517: an admission keeps one kernel tier per declaration, at its
/// position: a definition replayed, an owed one assumed, one the checker
/// refused unoffered and a use of it withheld behind it; an endpoint loop
/// outside the fragment, with the issue that owes its rule.
#[test]
fn an_admission_keeps_each_declaration_s_kernel_tier_2517()
{
    let grammar = grammar();
    let tiers = |text: &str| -> Vec<(usize, KernelTier)> {
        let Lowered::Module { module, arena } = lower_source(
            &grammar,
            SourceText::from(text),
            &mut LoweringCount::default(),
        )
        .expect("the source lowers")
        .into_lowered()
        else {
            panic!("the source is not refused whole");
        };
        judge::<Evaluator>(
            CorpusRoot::Fixture,
            (module, SourceText::from(text)),
            arena,
            &HostGrant::UNBOUNDED,
        )
        .into_parts()
        .1
        .admit_retiring(
            bridge::LeadingCount::NONE,
            Maybe::Absent(bridge::crossed::Absent::Unasked),
            &Unretired,
        )
        .whole()
        .tiers
        .iter()
        .map(|&(constant, tier)| (usize::from(constant), tier))
        .collect()
    };
    assert_eq!(
        tiers(
            r#"def a : Integer ; def a = 1 ; @[ owes(1) ] def later : Integer ; def w : Integer ; def w = "text" ; def r = w ;"#
        ),
        vec![
            (0_usize, KernelTier::Replayed),
            (1_usize, KernelTier::Assumed),
            (2_usize, KernelTier::Unoffered),
            (3_usize, KernelTier::Withheld {
                behind: ConstantIndex::from(2_usize)
            }),
        ],
        "each declaration keeps its tier at its own position"
    );
    let endpoint_loop = KernelTier::Outside {
        form: Unruled::Former(UnadmittedFormer::EndpointLoop),
        class: FailureClass::Unimplemented(TrackingIssue::KERNEL_ENDPOINT_LOOP),
    };
    assert_eq!(
        tiers(include_str!(
            "compose/fixtures/an-endpoint-loop-settles-with-no-kernel-image-6047.gandr"
        )),
        vec![
            (0_usize, endpoint_loop),
            (1_usize, endpoint_loop),
            (2_usize, KernelTier::Replayed),
        ],
        "the two loops stand outside the fragment, and the definition beside them replays"
    );
}

#[test]
fn the_kernel_artifact_holds_what_crossed_under_its_names()
{
    let grammar = grammar();
    let mut lowerings = LoweringCount::default();
    let Ok(Composed::Settled {
        kernel: Maybe::Present(kernel),
        ..
    }) = compose::<Evaluator>(
        &grammar,
        CorpusRoot::Fixture,
        SourceText::from(
            r#"def a : Integer ; def a = 1 ; @[ owes(1) ] def later : Integer ; def w : Integer ; def w = "text" ; def r = w ;"#,
        ),
        &mut lowerings,
    )
    else {
        panic!("the module settles");
    };
    let decoded = decode(kernel.as_image()).expect("the kernel's own export decodes");
    let names: Vec<Vec<&str>> = decoded
        .declarations()
        .iter()
        .map(|marked| {
            marked
                .declaration()
                .name()
                .segments()
                .iter()
                .map(AsRef::as_ref)
                .collect()
        })
        .collect();
    assert_eq!(
        vec![vec!["a"], vec!["later"]],
        names,
        "the definition and the owed axiom cross under their names; the refused declaration \
             and the one withheld for naming it do not"
    );
}

#[test]
fn a_sealed_module_settles_its_abstract_type()
{
    let grammar = grammar();
    let mut lowerings = LoweringCount::default();
    let Ok(Composed::Settled {
        report,
        kernel: Maybe::Present(kernel),
        ..
    }) = compose::<Evaluator>(
        &grammar,
        CorpusRoot::Fixture,
        SourceText::from(include_str!(
            "compose/fixtures/a-sealed-module-settles-its-abstract-type.gandr"
        )),
        &mut lowerings,
    )
    else {
        panic!("the sealed module settles and crosses");
    };
    let rows: Vec<(String, Settlement, Outcome)> = report
        .declarations()
        .iter()
        .map(|declaration| {
            (
                declaration.name().to_string(),
                declaration.settlement(),
                declaration.outcome(),
            )
        })
        .collect();
    let checks = || Outcome::Checks(gandr_core_checker::ObligationCount::from(0_usize));
    assert_eq!(
        rows,
        vec![
            ("T".to_owned(), Settlement::Settled, checks()),
            ("seed".to_owned(), Settlement::Settled, checks()),
            ("held".to_owned(), Settlement::Settled, checks()),
            (
                "leak".to_owned(),
                Settlement::Unsettled,
                Outcome::Refuses(RefusalName::TypeMismatch)
            ),
        ],
        "the abstract type is admitted first, the member checks at its representation, a \
             client at the atom, and the atom is not its representation outside"
    );
    assert!(
        matches!(
            report.declarations()[0].produced(),
            Produced::Judged(Verdict::Data)
        ),
        "the abstract type is judged as a type former, with no axiom behind it"
    );
    let decoded = decode(kernel.as_image()).expect("the kernel's own export decodes");
    let crossed: Vec<(Vec<&str>, bool)> = decoded
        .declarations()
        .iter()
        .map(|marked| {
            (
                marked
                    .declaration()
                    .name()
                    .segments()
                    .iter()
                    .map(AsRef::as_ref)
                    .collect(),
                matches!(
                    *marked.declaration().content(),
                    gandr_kernel_term::DeclarationContent::AbstractType { .. }
                ),
            )
        })
        .collect();
    assert_eq!(
        crossed,
        vec![
            (vec!["Counter", "T"], true),
            (vec!["Counter", "seed"], false),
            (vec!["held"], false),
        ],
        "the atom crosses as the kernel's abstract type, ahead of the definitions that read \
             it; the leak does not cross"
    );
}

#[test]
fn a_sealed_atom_s_identity_decides_what_its_relation_s_evidence_is()
{
    let grammar = grammar();
    let mut lowerings = LoweringCount::default();
    let sealed = |name: &str, identity: &str| {
        format!(
            "module {name} :> *{{ type T, origin : T, other : T }} where {{ {identity} type T = \
                 Unit ; def origin = *{{}} ; def other = *{{}} ; }}\ndef evidence{name} : \
                 Path[.A = {name}.T]({name}.origin, {name}.other) ;\ndef evidence{name} = *{{}} ;\n"
        )
    };
    let source = [
        "def related(a : Unit, b : Unit) -> -F Type { return Unit }\n".to_owned(),
        "def reflexive(a : Unit) -> -F related(a, a) { return *{} }\n".to_owned(),
        "def contraction(a : Unit, b : Unit, r : related(a, b)) -> -F Path[.A = *{ y : Unit, s : \
             related(a, y) }](*{b, r}, *{a, reflexive a}) { return *{*{}, *{}} }\n"
            .to_owned(),
        sealed(
            "Lawful",
            "@[ identity(*{related, reflexive, contraction}) ]",
        ),
        sealed("Lawless", "@[ identity(*{related, reflexive}) ]"),
        sealed("Bare", ""),
    ]
    .concat();
    let Ok(Composed::Settled { report, .. }) = compose::<Evaluator>(
        &grammar,
        CorpusRoot::Fixture,
        SourceText::from(source.as_str()),
        &mut lowerings,
    )
    else {
        panic!("the three sealed modules settle");
    };
    let mut evidence: Vec<(String, Outcome)> = report
        .declarations()
        .iter()
        .map(|declaration| (declaration.name().to_string(), declaration.outcome()))
        .collect();
    evidence.retain(|&(ref name, _)| name.starts_with("evidence"));
    assert_eq!(
        evidence,
        vec![
            (
                "evidenceLawful".to_owned(),
                Outcome::Checks(gandr_core_checker::ObligationCount::from(0_usize))
            ),
            (
                "evidenceLawless".to_owned(),
                Outcome::Refuses(RefusalName::AtomTransport)
            ),
            (
                "evidenceBare".to_owned(),
                Outcome::Refuses(RefusalName::TypeMismatch)
            ),
        ],
        "the relation's evidence is a path at a lawful atom, refused by name at an atom \
             stating no law, and no path at an atom stating no identity"
    );
}

#[test]
fn each_binder_no_variable_reads_is_unused()
{
    // Each source is laid after `std.list`, which a corpus source naming
    // `List` imports (#4520); a span is read back from the source's base.
    let unused = |written: &str| {
        let listed = fixture::Listed::new(SourceText::from(written));
        let Composed::Settled { unused, .. } = listed.composed::<Evaluator>(CorpusRoot::Fixture)
        else {
            panic!("the source composes");
        };
        let base = usize::from(listed.base);
        unused
            .iter()
            .map(|span| {
                let start = usize::from(span.start()).saturating_sub(base);
                let end = usize::from(span.end()).saturating_sub(base);
                let line = written
                    .get(.. start)
                    .unwrap_or_default()
                    .matches('\n')
                    .count();
                std::format!(
                    "{}:{}",
                    line.saturating_add(1),
                    written.get(start .. end).unwrap_or_default()
                )
            })
            .collect::<Vec<_>>()
    };
    let corpus = |file: &str| {
        std::fs::read_to_string(
            std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("../../corpus")
                .join(file),
        )
        .expect("the corpus source reads")
    };
    // A corpus binder is named by the one line that declares it, so an
    // edit elsewhere in the source moves the expectation with it (#2786).
    let declared = |source: &str, declaration: &str, binder: &str| {
        let mut lines = source
            .lines()
            .enumerate()
            .filter(|&(_, line)| line.contains(declaration));
        let (index, _) = lines.next().expect("the declaration is written");
        assert!(
            lines.next().is_none(),
            "`{declaration}` names one line of the source"
        );
        std::format!("{}:{binder}", index.saturating_add(1))
    };
    assert_eq!(
        unused(include_str!(
            "compose/fixtures/each-binder-no-variable-reads-is-unused-1.gandr"
        )),
        ["5:m", "6:k", "9:p", "13:y"],
        "the unused parameter, `let` binder, pattern variable and lambda binder, the last in \
             the second half of a name declared in two; not the used parameter nor the \
             constructor's telescope binder"
    );
    assert_eq!(
        unused(include_str!(
            "compose/fixtures/each-binder-no-variable-reads-is-unused-2.gandr"
        )),
        [""; 0],
        "a binder read only in a type, or only by a static application, is used"
    );
    assert_eq!(
        unused(include_str!("compose/unformatted/application.gandr")),
        ["1:n"],
        "a fork's unused end is the checker's refusal and no lambda's or bind's, but the \
             refused declaration's unused parameter may be dropped (#1504)"
    );
    assert_eq!(
        unused(&corpus("pathological/control/capability-drop.gandr")),
        [""; 0],
        "an unused consumable capability is the checker's refusal, and its declaration \
             answers nothing"
    );
    let misused = corpus("pathological/completion/buffer-misused.gandr");
    assert_eq!(
        unused(&misused),
        [
            declared(&misused, "let first = r.free", "first"),
            declared(&misused, "let copied : Buf =", "copied")
        ],
        "each misused buffer is refused, yet a `let` binder no use reads may be dropped, \
             even one whose own head the checker refused (#1504)"
    );
    let flow = corpus("surface/control-flow.gandr");
    assert_eq!(
        unused(&flow),
        [declared(&flow, "def tick(n : Nat)", "n")],
        "`tick` leaves its parameter unused; the capability `handled` handles is no lambda's \
             or bind's, and every other binder is used"
    );
}

/// A unit of two sources, the second starting at `base` and importing
/// nothing.
///
/// # Specification
/// trivial.
fn pair(base: gandr_surface_syntax::ByteOffset) -> gandr_surface_lowering::Unit
{
    use gandr_surface_lowering::Unit;
    use gandr_surface_lowering::UnitSource;
    use gandr_surface_syntax::ByteOffset;

    Unit::new(vec![
        UnitSource::new(ByteOffset::from(0_usize), Vec::new()),
        UnitSource::new(base, Vec::new()),
    ])
    .expect("two sources make a unit")
}

/// A poll that retires the work at its `at`th reading, counting every
/// reading.
#[derive(Debug)]
struct RetireAt
{
    /// The reading that retires the work, counted from one.
    at: usize,
    /// How many times the work has been polled.
    readings: core::cell::Cell<usize>,
}

impl Retirement for RetireAt
{
    type Retired = ();

    /// Wanted until the `at`th reading, retired from it on.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one more reading counted; [`Demand::Retired`] once the count
    ///   reaches `at`.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the witness counts the readings a member judgement
    ///   made.
    /// - witness: `tests::compose::a_retired_member_judgement_keeps_nothing_1663`
    #[spec(
            captures: before = self.readings.get(),
            ensures: |ret| self.readings.get() == before.saturating_add(1)
                && matches!(ret, Demand::Retired(())) == (self.readings.get() >= self.at),
        )]
    fn demand(&self) -> Demand<()>
    {
        let reading = self.readings.get().saturating_add(1);
        self.readings.set(reading);
        if reading >= self.at {
            Demand::Retired(())
        }
        else {
            Demand::Wanted
        }
    }
}

/// The built-in grammar with one more rule, a form no source writes: a
/// grammar of another fingerprint, so a tree molded under it is refused
/// under the built-in one.
///
/// # Specification
/// trivial.
fn another_grammar() -> Pbg
{
    use gandr_surface_grammar::PrecName;
    use gandr_surface_grammar::Provenance;
    use gandr_surface_grammar::Regex;
    use gandr_surface_grammar::Rule;
    use gandr_surface_grammar::RuleName;
    use gandr_surface_grammar::Sort;
    use gandr_surface_grammar::TileLabel;
    use gandr_surface_grammar::built_in_prec_table;

    let precs = built_in_prec_table().expect("the band table builds");
    let prec = precs
        .prec(PrecName("expression.atom"))
        .expect("the band is built in");
    let mut rules = grammar().rules().to_vec();
    rules.push(Rule::with_provenance(
        RuleName("escape_sequence"),
        Provenance("escape_sequence"),
        Sort::Expression,
        prec,
        Regex::tile(TileLabel("escape_sequence")),
    ));
    Pbg::build_table(precs, rules).expect("the grammar builds")
}

/// A tree molded under another grammar is the engine's fault on every
/// lowering route — a unit lowered whole, a document resumed on a closure,
/// and one lowered onto a judged closure — raised, never carried as the
/// source's own refusal.
#[test]
fn a_tree_of_another_grammar_faults_every_lowering_route()
{
    use alloc::string::String;
    use alloc::sync::Arc;

    use gandr_surface_dispatcher::JudgedClosure;
    use gandr_surface_dispatcher::lower_closure;
    use gandr_surface_dispatcher::lower_onto_closure;
    use gandr_surface_dispatcher::lower_parsed_unit;
    use gandr_surface_dispatcher::lower_resumed_unit;

    let ours = grammar();
    let theirs = another_grammar();
    assert_ne!(
        ours.fingerprint(),
        theirs.fingerprint(),
        "the grammars differ"
    );
    let foreign = || {
        parse(&theirs, SourceText::from("def one = 1 ;\n"))
            .expect("the source parses under the other grammar")
    };
    let engine = |fault: Option<ComposeFault<'_>>| {
        matches!(fault, Some(ComposeFault::Lowering(refusal))
                if refusal.classify() == FailureClass::EngineFault)
    };
    let mut lowerings = LoweringCount::default();
    assert!(
        engine(
            lower_parsed_unit(
                &ours,
                foreign(),
                &alone(),
                &mut lowerings,
                &mut gandr_surface_lowering::coincide::Decisions::none()
            )
            .err()
        ),
        "lowered whole"
    );
    let closure = Arc::new(
        lower_closure(
            Arc::new(grammar()),
            String::from("def zero = 0 ;\n"),
            alone(),
            &mut lowerings,
        )
        .expect("the closure is held"),
    );
    assert!(
        engine(
            lower_resumed_unit(
                &closure,
                foreign(),
                &alone(),
                &mut lowerings,
                &mut gandr_surface_lowering::coincide::Decisions::none()
            )
            .err()
        ),
        "resumed on a closure, which lowers a tree it does not extend whole"
    );
    let judged =
        JudgedClosure::new::<Evaluator>(closure, &HostGrant::UNBOUNDED, CorpusRoot::Fixture)
            .expect("the closure lowers to its end");
    assert!(
        engine(
            lower_onto_closure(
                &judged,
                judged.arena(),
                foreign(),
                &alone(),
                &mut lowerings,
                &mut gandr_surface_lowering::coincide::Decisions::none()
            )
            .err()
        ),
        "onto a judged closure, which leaves a tree it does not extend whole"
    );
}

/// A source the lowering refuses whole, as the author's and not the
/// engine's, is carried as a refused lowering on every route that resumes
/// a closure: resumed alone, left whole by a judged closure, and laid
/// after a judged closure's own tree.
#[test]
fn a_refused_source_is_carried_on_every_resumed_route()
{
    use alloc::string::String;
    use alloc::sync::Arc;

    use gandr_surface_dispatcher::Checking;
    use gandr_surface_dispatcher::JudgedClosure;
    use gandr_surface_dispatcher::lower_closure;
    use gandr_surface_dispatcher::lower_onto_closure;
    use gandr_surface_dispatcher::lower_resumed_unit;
    use gandr_surface_syntax::ByteOffset;

    let ours = grammar();
    let own = SourceText::from("@[ checks ]");
    let refused = |lowered: &Lowered<'_>| {
        matches!(*lowered, Lowered::Refused(refusal)
                if refusal.classify() != FailureClass::EngineFault)
    };
    let mut lowerings = LoweringCount::default();
    let closure_text = "def zero = 0 ;\n";
    let closure = Arc::new(
        lower_closure(
            Arc::new(grammar()),
            String::from(closure_text),
            alone(),
            &mut lowerings,
        )
        .expect("the closure is held"),
    );
    let alone_parsed = || parse(&ours, own).expect("the source parses");
    let resumed = lower_resumed_unit(
        &closure,
        alone_parsed(),
        &alone(),
        &mut lowerings,
        &mut gandr_surface_lowering::coincide::Decisions::none(),
    )
    .expect("a refusal is no fault")
    .into_lowered();
    assert!(refused(&resumed), "resumed alone: {resumed:?}");
    let judged = JudgedClosure::new::<Evaluator>(
        Arc::clone(&closure),
        &HostGrant::UNBOUNDED,
        CorpusRoot::Fixture,
    )
    .expect("the closure lowers to its end");
    let (whole, checking) = lower_onto_closure(
        &judged,
        judged.arena(),
        alone_parsed(),
        &alone(),
        &mut lowerings,
        &mut gandr_surface_lowering::coincide::Decisions::none(),
    )
    .expect("a refusal is no fault");
    let whole = whole.into_lowered();
    assert!(
        refused(&whole) && matches!(checking, Checking::Whole),
        "left whole by the judged closure: {whole:?}"
    );
    let text = format!("{closure_text}{}", <&str>::from(own));
    let laid = parse(&ours, own)
        .expect("the source parses")
        .after(closure.tree(), SourceText::from(text.as_str()))
        .expect("the source lays after the closure");
    let (after, checking) = lower_onto_closure(
        &judged,
        judged.arena(),
        laid,
        &pair(ByteOffset::from(closure_text.len())),
        &mut lowerings,
        &mut gandr_surface_lowering::coincide::Decisions::none(),
    )
    .expect("a refusal is no fault");
    let after = after.into_lowered();
    assert!(
        refused(&after) && matches!(checking, Checking::Whole),
        "laid after the judged closure: {after:?}"
    );
}

/// A document is judged on its closure's state only where the closure was
/// judged as the document is: a closure judged under another grant, or
/// entering at another entry, is not continued, and the document answers
/// what judging it whole answers — of its own declarations alone.
#[test]
fn a_closure_judged_otherwise_is_not_continued()
{
    use alloc::string::String;
    use alloc::sync::Arc;

    use gandr_core_term::effect::OperationName;
    use gandr_surface_dispatcher::Checking;
    use gandr_surface_dispatcher::Judged;
    use gandr_surface_dispatcher::JudgedClosure;
    use gandr_surface_dispatcher::judge_member_after;
    use gandr_surface_dispatcher::lower_closure;
    use gandr_surface_dispatcher::lower_onto_closure;
    use gandr_surface_dispatcher::lower_parsed_unit;
    use gandr_surface_syntax::ByteOffset;

    /// The name and outcome of each declaration `judged` reports.
    ///
    /// # Specification
    /// trivial.
    fn outcomes(judged: Judged<'_>) -> Vec<(String, Outcome)>
    {
        let Ok(Composed::Settled { report, .. }) = judged.into_parts().0
        else {
            panic!("the document settles");
        };
        report
            .declarations()
            .iter()
            .map(|declaration| (declaration.name().to_string(), declaration.outcome()))
            .collect()
    }

    /// What the document `own`, laid after `closure_text`, reports judged
    /// under `grant`: after the closure judged under `closure_grant`, and
    /// whole.
    ///
    /// # Specification
    /// trivial.
    fn judged(
        (closure_text, own): (SourceText<'_>, SourceText<'_>),
        (closure_grant, grant): (&HostGrant, &HostGrant),
    ) -> [Vec<(String, Outcome)>; 2]
    {
        let grammar = grammar();
        let mut lowerings = LoweringCount::default();
        let closure = Arc::new(
            lower_closure(
                Arc::new(grammar.clone()),
                String::from(<&str>::from(closure_text)),
                alone(),
                &mut lowerings,
            )
            .expect("the closure is held"),
        );
        let held = JudgedClosure::new::<Evaluator>(
            Arc::clone(&closure),
            closure_grant,
            CorpusRoot::Fixture,
        )
        .expect("the closure lowers to its end");
        let text = format!("{}{}", <&str>::from(closure_text), <&str>::from(own));
        let text = SourceText::from(text.as_str());
        let base = ByteOffset::from(<&str>::from(closure_text).len());
        let unit = pair(base);
        let laid = parse(&grammar, own)
            .expect("the document parses")
            .after(closure.tree(), text)
            .expect("the document lays after its closure");
        let (lowering, checking) = lower_onto_closure(
            &held,
            held.arena(),
            laid,
            &unit,
            &mut lowerings,
            &mut gandr_surface_lowering::coincide::Decisions::none(),
        )
        .expect("the document lowers");
        assert!(
            matches!(checking, Checking::After(_)),
            "the document is lowered after the closure"
        );
        let Lowered::Module { module, arena } = lowering.into_lowered()
        else {
            panic!("the document is not refused whole");
        };
        let after = judge_member_after::<Evaluator>(
            CorpusRoot::Fixture,
            (module, text),
            arena,
            (grant, checking),
            base,
        );
        let Lowered::Module { module, arena } = lower_parsed_unit(
            &grammar,
            parse(&grammar, text).expect("the unit parses"),
            &unit,
            &mut lowerings,
            &mut gandr_surface_lowering::coincide::Decisions::none(),
        )
        .expect("the unit lowers")
        .into_lowered()
        else {
            panic!("the unit is not refused whole");
        };
        let whole = judge_member_after::<Evaluator>(
            CorpusRoot::Fixture,
            (module, text),
            arena,
            (grant, Checking::Whole),
            base,
        );
        [outcomes(after), outcomes(whole)]
    }

    let reading =
        HostGrant::within([&OperationName::from("read")]).expect("the host offers `read`");
    let [after, whole] = judged(
        (
            SourceText::from("def zero = 0 ;\n"),
            SourceText::from("def fs : Cap {read, write} ;\n"),
        ),
        (&HostGrant::UNBOUNDED, &reading),
    );
    assert_eq!(
        after, whole,
        "after a closure granted otherwise, the document is judged whole"
    );
    assert!(
        matches!(whole.as_slice(), [(name, outcome)]
                if name == "fs" && *outcome != Outcome::Checks(ObligationCount::from(1_usize))),
        "a capability beyond the grant is not owed, and the closure's own declaration is not \
             reported: {whole:?}"
    );

    let [operator, seat] = ["operator", "seat"].map(WorldName::from);
    let entering = HostGrant::UNBOUNDED.entering(vec![operator, seat]);
    let [after, whole] = judged(
        (
            SourceText::from("def zero = 0 ;\n"),
            SourceText::from(include_str!(
                "compose/fixtures/a-host-entry-names-the-worlds-a-module-declares.gandr"
            )),
        ),
        (&entering, &entering),
    );
    assert_eq!(
        after, whole,
        "after a closure that enters at another entry, the document is judged whole"
    );
    assert_eq!(
        whole.last().map(|&(_, ref outcome)| outcome.clone()),
        Some(Outcome::Checks(ObligationCount::from(0_usize))),
        "the document's own worlds hold the entry's capability"
    );
}

/// Each source of a component judged once reports its own declarations,
/// the obligations they owe and the builtins they shadow, and none of its
/// neighbour's.
#[test]
fn each_source_of_a_component_reports_its_own_share()
{
    use gandr_surface_dispatcher::SpellingCount;
    use gandr_surface_dispatcher::fixture::Keeping;
    use gandr_surface_dispatcher::fixture::Member;
    use gandr_surface_dispatcher::fixture::judge_component;
    use gandr_surface_dispatcher::lower_parsed_unit;
    use gandr_surface_syntax::ByteOffset;

    let grammar = grammar();
    let first = "def one : Integer ;";
    let second = include_str!(
        "compose/unformatted/each-source-of-a-component-reports-its-own-share-second.gandr"
    );
    // A component joins its sources with a newline, as the walk lays them.
    let text = format!(
        include_str!("compose/unformatted/each-source-of-a-component-reports-its-own-share.gandr"),
        first = first,
        second = second
    );
    let base = ByteOffset::from(first.len().saturating_add(1_usize));
    let members = [
        Member {
            start: ByteOffset::from(0_usize),
            end: ByteOffset::from(first.len()),
            root: CorpusRoot::Fixture,
        },
        Member {
            start: base,
            end: ByteOffset::from(text.len()),
            root: CorpusRoot::Fixture,
        },
    ];
    let lowering = lower_parsed_unit(
        &grammar,
        parse(&grammar, SourceText::from(text.as_str())).expect("the component parses"),
        &pair(base),
        &mut LoweringCount::default(),
        &mut gandr_surface_lowering::coincide::Decisions::none(),
    )
    .expect("the component lowers");
    let shares: Vec<(Vec<String>, usize, usize)> = judge_component::<Evaluator>(
        (lowering, SourceText::from(text.as_str())),
        (
            &HostGrant::UNBOUNDED,
            gandr_surface_dispatcher::Checking::Whole,
        ),
        (&members, &mut SpellingCount::default()),
        (
            Keeping::Composed,
            gandr_surface_dispatcher::Positioning::Unpositioned,
        ),
    )
    .0
    .into_iter()
    .map(|composed| match composed {
        Ok(Composed::Settled {
            report, shadowed, ..
        }) => (
            report
                .declarations()
                .iter()
                .map(|declaration| declaration.name().to_string())
                .collect(),
            usize::from(report.ledger()),
            shadowed.len(),
        ),
        Ok(Composed::Refused(refusal)) => panic!("refused whole: {refusal}"),
        Err(fault) => panic!("faulted: {fault}"),
    })
    .collect();
    assert_eq!(
        shares,
        [
            (Vec::from([String::from("one")]), 1_usize, 0_usize),
            (
                Vec::from([
                    String::from("two"),
                    String::from("three"),
                    String::from("add")
                ]),
                2_usize,
                1_usize
            ),
        ],
        "each source reports its own declarations, debts and shadowed builtins"
    );
}

/// An importer reading one base and not another reports the other's
/// import alone; an importer whose own declaration the lowering refused
/// reports none, its names past the refusal never read.
#[test]
fn an_import_no_lookup_reaches_is_unreached()
{
    use gandr_surface_dispatcher::SpellingCount;
    use gandr_surface_dispatcher::fixture::Keeping;
    use gandr_surface_dispatcher::fixture::Member;
    use gandr_surface_dispatcher::fixture::judge_component;
    use gandr_surface_dispatcher::lower_parsed_unit;
    use gandr_surface_lowering::ImportTarget;
    use gandr_surface_lowering::SourceIndex;
    use gandr_surface_lowering::Unit;
    use gandr_surface_lowering::UnitSource;
    use gandr_surface_syntax::ByteOffset;

    let grammar = grammar();
    let sources = [
        include_str!("compose/fixtures/an-import-no-lookup-reaches-is-unreached-sources.gandr"),
        include_str!("compose/fixtures/an-import-no-lookup-reaches-is-unreached-1.gandr"),
        include_str!("compose/fixtures/an-import-no-lookup-reaches-is-unreached-2.gandr"),
        include_str!("compose/fixtures/an-import-no-lookup-reaches-is-unreached-3.gandr"),
    ];
    // A component joins its sources with a newline, as the walk lays them.
    let text = sources.join("\n");
    let mut members = Vec::new();
    let mut start = 0_usize;
    for source in sources {
        let end = start.saturating_add(source.len());
        members.push(Member {
            start: ByteOffset::from(start),
            end: ByteOffset::from(end),
            root: CorpusRoot::Fixture,
        });
        start = end.saturating_add(1_usize);
    }
    let on = |source: usize| ImportTarget::Source(SourceIndex::from(source));
    let unit = Unit::new(
        members
            .iter()
            .zip([
                Vec::new(),
                Vec::new(),
                vec![on(0_usize), on(1_usize)],
                vec![on(1_usize)],
            ])
            .map(|(member, imports)| UnitSource::new(member.start, imports))
            .collect(),
    )
    .expect("four sources make a unit");
    let lowering = lower_parsed_unit(
        &grammar,
        parse(&grammar, SourceText::from(text.as_str())).expect("the component parses"),
        &unit,
        &mut LoweringCount::default(),
        &mut gandr_surface_lowering::coincide::Decisions::none(),
    )
    .expect("the component lowers");
    let unreached: Vec<Vec<&str>> = judge_component::<Evaluator>(
        (lowering, SourceText::from(text.as_str())),
        (
            &HostGrant::UNBOUNDED,
            gandr_surface_dispatcher::Checking::Whole,
        ),
        (&members, &mut SpellingCount::default()),
        (
            Keeping::Composed,
            gandr_surface_dispatcher::Positioning::Unpositioned,
        ),
    )
    .0
    .into_iter()
    .map(|composed| match composed {
        Ok(Composed::Settled { unreached, .. }) => unreached
            .iter()
            .map(|span| {
                text.get(usize::from(span.start()) .. usize::from(span.end()))
                    .unwrap_or_default()
            })
            .collect(),
        Ok(Composed::Refused(refusal)) => panic!("refused whole: {refusal}"),
        Err(fault) => panic!("faulted: {fault}"),
    })
    .collect();
    assert_eq!(
        unreached,
        [
            Vec::new(),
            Vec::new(),
            Vec::from(["import \"./eight.gandr\";"]),
            Vec::new()
        ],
        "the importer reports the import it reads nothing through; the refused one none"
    );
}

/// #1663: a member judgement polled to retirement before its second
/// declaration answers retired, and so does one the poll after its last
/// declaration retires before the settle; one whose poll never retires it
/// reads the poll once before each declaration and once before the settle,
/// and answers what the judgement nobody polls answers, its table too.
#[test]
fn a_retired_member_judgement_keeps_nothing_1663()
{
    use gandr_surface_dispatcher::Checking;
    use gandr_surface_dispatcher::Recording;
    use gandr_surface_dispatcher::Supporting;
    use gandr_surface_dispatcher::judge_member_after;
    use gandr_surface_dispatcher::judge_member_after_retiring;
    use gandr_surface_dispatcher::judge_member_tabled;
    use gandr_surface_dispatcher::judge_member_tabled_retiring;
    use gandr_surface_syntax::ByteOffset;

    let grammar = grammar();
    let source = SourceText::from(include_str!(
        "compose/unformatted/a-retired-member-judgement-keeps-nothing-1663.gandr"
    ));
    let lowered = || {
        let Lowered::Module { module, arena } =
            lower_source(&grammar, source, &mut LoweringCount::default())
                .expect("the module lowers")
                .into_lowered()
        else {
            panic!("the module is read");
        };
        (module, arena)
    };
    let base = ByteOffset::from(0_usize);
    let judged = |at| {
        let poll = RetireAt {
            at,
            readings: core::cell::Cell::new(0),
        };
        let (module, arena) = lowered();
        let answer = judge_member_after_retiring::<Evaluator, _>(
            CorpusRoot::Strict,
            (module, source),
            arena,
            (&HostGrant::UNBOUNDED, Checking::Whole),
            base,
            (&poll, Recording::Unrecorded, Supporting::Unkept),
        );
        (answer, poll.readings.get())
    };
    let (second, read) = judged(2);
    assert!(
        matches!(second, Polled::Retired((), ())),
        "the poll before the second declaration retires the judgement"
    );
    assert_eq!(read, 2, "and the third declaration is never polled for");
    let (settling, read) = judged(4);
    assert!(
        matches!(settling, Polled::Retired((), ())),
        "the poll after the last declaration retires it before the settle"
    );
    assert_eq!(read, 4, "the fourth reading is the settle's");
    let (never, read) = judged(5);
    let Polled::Whole(polled) = never
    else {
        panic!("a poll never retired answers whole");
    };
    assert_eq!(
        read, 4,
        "polled once before each of the three declarations and once before the settle"
    );
    assert!(
        matches!(*polled.settled(), Ok(Composed::Settled { .. })),
        "the module settles"
    );
    let (module, arena) = lowered();
    let whole = judge_member_after::<Evaluator>(
        CorpusRoot::Strict,
        (module, source),
        arena,
        (&HostGrant::UNBOUNDED, Checking::Whole),
        base,
    );
    assert_eq!(
        polled.settled(),
        whole.settled(),
        "and answers what the judgement nobody polls answers"
    );

    let unit = alone();
    let tabled = |at| {
        let poll = RetireAt {
            at,
            readings: core::cell::Cell::new(0),
        };
        let (module, arena) = lowered();
        let answer = judge_member_tabled_retiring::<Evaluator, _>(
            CorpusRoot::Strict,
            (module, source),
            arena,
            (&HostGrant::UNBOUNDED, Checking::Whole),
            (&unit, base),
            (&poll, Supporting::Unkept),
        );
        (answer, poll.readings.get())
    };
    let (second, read) = tabled(2);
    assert!(
        matches!(second, Polled::Retired((), ())) && read == 2,
        "the tabled judgement is retired alike"
    );
    let (never, read) = tabled(5);
    let Polled::Whole((polled, polled_table)) = never
    else {
        panic!("a tabled judgement never retired answers whole");
    };
    assert_eq!(read, 4, "and is polled as the untabled one is");
    assert!(
        matches!(polled_table, Maybe::Present(_)),
        "its table is made"
    );
    let (module, arena) = lowered();
    let (whole, whole_table) = judge_member_tabled::<Evaluator>(
        CorpusRoot::Strict,
        (module, source),
        arena,
        (&HostGrant::UNBOUNDED, Checking::Whole),
        (&unit, base),
    );
    assert_eq!(
        (polled.into_parts().0, polled_table),
        (whole.into_parts().0, whole_table),
        "and answers what the tabled judgement nobody polls answers"
    );
}

/// #3671: a module whose last mutual block is refused keeps, in its
/// judgement's table, the entries its table typed alone keeps. The block
/// is closed before the table reads its typings, so no family of the block
/// still reads as forming.
#[test]
fn a_refused_last_block_tables_as_typed_alone_3671()
{
    use gandr_surface_dispatcher::Checking;
    use gandr_surface_dispatcher::judge_member_tabled;
    use gandr_surface_syntax::ByteOffset;

    let grammar = grammar();
    let source = SourceText::from(include_str!(
        "compose/unformatted/a-refused-last-block-tables-as-typed-alone-3671.gandr"
    ));
    let typed =
        gandr_surface_dispatcher::TypeTable::of(&grammar, source).expect("the source types");
    let Lowered::Module { module, arena } =
        lower_source(&grammar, source, &mut LoweringCount::default())
            .expect("the module lowers")
            .into_lowered()
    else {
        panic!("the module is read");
    };
    let (_judged, table) = judge_member_tabled::<Evaluator>(
        CorpusRoot::Strict,
        (module, source),
        arena,
        (&HostGrant::UNBOUNDED, Checking::Whole),
        (&alone(), ByteOffset::from(0_usize)),
    );
    let Maybe::Present(table) = table
    else {
        panic!("the judgement keeps its table");
    };
    let page = PageWidth::from(80_u32);
    let style = Form::Explicit.into();
    assert_eq!(
        table.entries(page, style).collect::<Vec<_>>(),
        typed.entries(page, style).collect::<Vec<_>>(),
        "the judgement's table holds the entries of the table typed alone"
    );
}

/// #2102: a revision whose lowering moves no node — a comment above every
/// declaration — takes the verdicts the judgement before it holds, reading
/// its poll once rather than before each declaration, and settles as a
/// whole judgement of its own text, its spans moved; a revision changing a
/// value a later declaration reads is judged again and refused as a whole
/// judgement refuses it.
#[test]
fn a_revision_moving_no_lowered_node_is_not_judged_again_2102()
{
    use gandr_surface_dispatcher::Checking;
    use gandr_surface_dispatcher::Recorded;
    use gandr_surface_dispatcher::Recording;
    use gandr_surface_dispatcher::Supporting;
    use gandr_surface_dispatcher::judge_member_after;
    use gandr_surface_dispatcher::judge_member_after_retiring;
    use gandr_surface_syntax::ByteOffset;

    let grammar = grammar();
    let base = ByteOffset::from(0_usize);
    let lowered = |source| {
        let Lowered::Module { module, arena } =
            lower_source(&grammar, source, &mut LoweringCount::default())
                .expect("the module lowers")
                .into_lowered()
        else {
            panic!("the module is read");
        };
        (module, arena)
    };
    let mut recorded = Recorded::default();
    let mut judged = |source: SourceText<'static>| {
        let poll = RetireAt {
            at: usize::MAX,
            readings: core::cell::Cell::new(0),
        };
        let (module, arena) = lowered(source);
        let Polled::Whole(answer) = judge_member_after_retiring::<Evaluator, _>(
            CorpusRoot::Strict,
            (module, source),
            arena,
            (&HostGrant::UNBOUNDED, Checking::Whole),
            base,
            (
                &poll,
                Recording::Recorded(&mut recorded),
                Supporting::Unkept,
            ),
        )
        else {
            panic!("a poll never retired answers whole");
        };
        let (module, arena) = lowered(source);
        let whole = judge_member_after::<Evaluator>(
            CorpusRoot::Strict,
            (module, source),
            arena,
            (&HostGrant::UNBOUNDED, Checking::Whole),
            base,
        );
        assert_eq!(
            answer.settled(),
            whole.settled(),
            "{source:?} settles as a whole judgement of its text"
        );
        (answer.into_parts().0, poll.readings.get())
    };
    let (first, read) = judged(SourceText::from(include_str!(
        "compose/unformatted/a-revision-moving-no-lowered-node-is-not-judged-again-2102-1.gandr"
    )));
    assert_eq!(
        read, 3,
        "a first revision is judged, polled before each declaration"
    );
    let (commented, read) = judged(SourceText::from(include_str!(
        "compose/unformatted/a-revision-moving-no-lowered-node-is-not-judged-again-2102-2.gandr"
    )));
    assert_eq!(
        read, 1,
        "a comment moves no lowered node: the verdicts are taken, polled before the \
             settle alone"
    );
    assert_ne!(
        commented, first,
        "and the settle is made again at the spans the comment moved"
    );
    let (changed, read) = judged(SourceText::from(include_str!(
        "compose/unformatted/a-revision-moving-no-lowered-node-is-not-judged-again-2102-3.gandr"
    )));
    assert_eq!(read, 3, "a value changed is judged again");
    assert_ne!(
        changed, commented,
        "and the path reading it is refused, as the whole judgement refuses it"
    );
}

/// #5748: the readmission of `model/desc/record-faces.gandr` crosses one
/// formation record for `Config` at the secure port, whose six brackets
/// fix `.port = 443` and `.tls = true` by its fields or by its face
/// `secure`. That record is the one kernel definition declared at the
/// record of `port` and `tls` alone.
#[test]
fn the_secure_brackets_of_record_faces_cross_one_formation_5748()
{
    let grammar = grammar();
    let source = SourceText::from(include_str!(
        "../../../corpus/model/desc/record-faces.gandr"
    ));
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
    let report = check_module(
        &mut CheckingContext::new(&mut arena, CheckBudget::DEFAULT),
        &declarations,
    );
    let readmission = bridge::readmit(&mut arena, &report);
    let environment = readmission.environment();
    let label = |name: &str| gandr_kernel_term::FieldLabel::from(alloc::string::String::from(name));
    let secure = [label("port"), label("tls")];
    let formations = environment
            .entries()
            .iter()
            .filter(|entry| {
                let gandr_kernel_term::DeclarationContent::Def { declared, .. } =
                    *entry.declaration().content()
                else {
                    return false;
                };
                matches!(
                    environment.arena().value_type(declared),
                    Some(gandr_kernel_term::ValueType::Record(fields)) if fields.keys().eq(secure.iter())
                )
            })
            .count();
    assert_eq!(
        formations, 1,
        "the six secure brackets cross one formation record"
    );
}
