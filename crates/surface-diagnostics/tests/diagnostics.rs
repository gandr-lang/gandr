//! The diagnostics model over real compositions.
//!
//! Each case composes its source through the dispatcher — a walk over a
//! scratch tree, or the composition itself where a case needs a fixed path —
//! and asserts the diagnostics its step yields: their classes, their spans,
//! their annotations, their contexts and their words.
//!
//! The cases, in a `cfg(test)` module so the crate's lint wall reads them as
//! test code rather than as shipping code.

use core::convert::Infallible;
use core::ops::ControlFlow;
use std::path::Path;
use std::path::PathBuf;

use anodized::spec;
use gandr_core_checker::CheckRefusal;
use gandr_core_checker::FrameRole;
use gandr_core_checker::Mismatch;
use gandr_core_checker::TermNode;
use gandr_core_checker::TypeNode;
use gandr_core_term::FailureClass;
use gandr_core_term::Value;
use gandr_surface_corpus::Refusal;
use gandr_surface_corpus::Settlement;
use gandr_surface_diagnostics::AnnotationKind;
use gandr_surface_diagnostics::Class;
use gandr_surface_diagnostics::Diagnostic;
use gandr_surface_diagnostics::Failures;
use gandr_surface_diagnostics::Families;
use gandr_surface_diagnostics::Fix;
use gandr_surface_diagnostics::Identifier;
use gandr_surface_diagnostics::Lint;
use gandr_surface_diagnostics::Severity;
use gandr_surface_diagnostics::Subject;
use gandr_surface_diagnostics::Unsettlement;
use gandr_surface_diagnostics::Verbosity;
use gandr_surface_diagnostics::constant_names;
use gandr_surface_diagnostics::diagnose;
use gandr_surface_diagnostics::report_identifier;
use gandr_surface_diagnostics::report_span;
use gandr_surface_diagnostics::upstream;
use gandr_surface_dispatcher::Composed;
use gandr_surface_dispatcher::Goals;
use gandr_surface_dispatcher::Lints;
use gandr_surface_dispatcher::Lowered;
use gandr_surface_dispatcher::LoweringCount;
use gandr_surface_dispatcher::SourceRoot;
use gandr_surface_dispatcher::Standing;
use gandr_surface_dispatcher::Step;
use gandr_surface_dispatcher::Verb;
use gandr_surface_dispatcher::Walk;
use gandr_surface_dispatcher::Width;
use gandr_surface_dispatcher::compose;
use gandr_surface_dispatcher::entries;
use gandr_surface_dispatcher::lower_source;
use gandr_surface_grammar::built_in;
use gandr_surface_lowering::DeclarationOutcome;
use gandr_surface_lowering::FormFault;
use gandr_surface_lowering::LoweringRefusal;
use gandr_surface_lowering::OriginTable;
use gandr_surface_pretty::CoreNode;
use gandr_surface_pretty::CoreSource;
use gandr_surface_pretty::Fidelity;
use gandr_surface_pretty::Form;
use gandr_surface_pretty::Name;
use gandr_surface_pretty::Notation;
use gandr_surface_pretty::PageWidth;
use gandr_surface_pretty::Spelling;
use gandr_surface_pretty::Unspelled;
use gandr_surface_pretty::present_computation;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

/// A declaration whose definition synthesises a type its signature does
/// not convert to.
const MISMATCH: &str = "def wrong : Integer ;\ndef wrong = \"text\" ;\n";

/// A force of an integer, inside a thunk.
const FORCE: &str = "def a : +U (-F Integer) ;\ndef a = thunk { become force 1 } ;\n";

/// An application whose head is a return, not a function.
const APPLICATION: &str = "def b : +U (-F Integer) ;\ndef b = thunk { become (pure 1)(2) } \
                               ;\n";

/// A mismatch under a `run` binder.
const BOUND: &str = "def id(x: Integer) -> -F Integer { return x }\ndef f(n: Integer) -> -F \
                         String { run m <- id(n) ; return m }\n";

/// A fresh scratch directory, removed when dropped.
#[repr(transparent)]
struct Scratch(PathBuf);

impl Scratch
{
    /// An empty directory named for `test` and this process.
    ///
    /// # Specification
    /// - requires: `test` is one file-name component, owned by this test.
    /// - ensures: the returned path is an empty directory.
    /// - provides: isolated storage for walk witnesses.
    /// - fails: never returns a failure.
    /// - panics: if an existing directory cannot be removed or creation fails.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a fresh owned directory holds exactly the sources the
    ///   walk witnesses write; stale entries would add diagnostics.
    /// - witness: `tests::diagnostics::each_verb_prints_its_entries`
    #[spec(
            requires: test.file_name() == Some(test.as_os_str()),
            ensures: |ref ret| std::fs::read_dir(&ret.0).is_ok_and(|mut entries| entries.next().is_none()),
        )]
    fn new(test: &Path) -> Self
    {
        let root = std::env::temp_dir().join(format!(
            "gandr-diagnostics-{}-{}",
            test.display(),
            std::process::id()
        ));
        if root.exists() {
            std::fs::remove_dir_all(&root).expect("a stale scratch directory is removed");
        }
        std::fs::create_dir_all(&root).expect("the scratch directory is created");
        Self(root)
    }

    /// Write `text` at `relative`, creating its directories.
    ///
    /// # Specification
    /// - requires: `relative` names a file through normal components within
    ///   this exclusively owned scratch directory.
    /// - ensures: the file under the scratch root holds `text`.
    /// - provides: a source for a real filesystem walk.
    /// - fails: never returns a failure.
    /// - panics: if the parent directories or the file cannot be written.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each written source is read back through a real walk
    ///   and reports at its own path.
    /// - witness: `tests::diagnostics::each_verb_prints_its_entries`
    #[spec(
            requires: relative.file_name().is_some() && relative.components().all(|component|
                matches!(component, std::path::Component::Normal(_))),
            ensures: std::fs::read_to_string(self.0.join(relative)).is_ok_and(|held| held == text.as_ref()),
        )]
    fn file(
        &self,
        relative: &Path,
        text: SourceText<'_>,
    )
    {
        let path = self.0.join(relative);
        std::fs::create_dir_all(path.parent().expect("a file has a parent"))
            .expect("the directories are created");
        std::fs::write(&path, text.as_ref()).expect("the file is written");
    }
}

impl Drop for Scratch
{
    /// Remove the directory and everything under it.
    ///
    /// # Specification
    /// - requires: this test exclusively owns the scratch path.
    /// - ensures: the directory and its descendants no longer exist.
    /// - provides: cleanup at the end of the fixture scope.
    /// - fails: never returns a failure.
    /// - panics: if removal fails.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the walk witness leaves no tree behind.
    /// - witness: `tests::diagnostics::each_verb_prints_its_entries`
    #[spec(ensures: matches!(self.0.try_exists(), Ok(false)))]
    fn drop(&mut self)
    {
        let removed = std::fs::remove_dir_all(&self.0);
        assert!(removed.is_ok(), "the scratch directory is removed");
    }
}

/// The step of a source at `path` under `root` whose text is `text`,
/// standing unsettled.
///
/// # Specification
/// - requires: `text` composes within the built-in limits.
/// - ensures: an unsettled source step borrowing `path` and `text` under
///   `root`.
/// - provides: a source step for diagnostic observations.
/// - fails: never returns a failure.
/// - panics: if grammar construction or composition fails.
///
/// # Adequacy
/// - hypothesis: L3 — strict refusals and fixture expectations build different
///   diagnostics at their own spans; a wrong root or source changes those
///   observations.
/// - witness: `tests::diagnostics::a_type_mismatch_is_located_at_its_term`
/// - witness: `tests::diagnostics::the_settle_note_says_what_was_expected_in_words`
#[spec(ensures: |ref ret| matches!(*ret,
        Step::Source { path: held, root: actual, standing: Standing::Unsettled, .. }
            if core::ptr::eq(core::ptr::from_ref(held), core::ptr::from_ref(path)) && actual == root))]
fn unsettled<'step>(
    path: &'step Path,
    root: SourceRoot,
    text: SourceText<'step>,
) -> Step<'step>
{
    let grammar = built_in().expect("the built-in grammar builds");
    Step::Source {
        path,
        root,
        text,
        base: gandr_surface_syntax::ByteOffset::from(0_usize),
        composed: compose(
            &grammar,
            root.corpus_root(),
            text,
            &mut LoweringCount::default(),
        )
        .expect("the source composes"),
        standing: Standing::Unsettled,
    }
}

/// The diagnostics a source at `path` under `root` with `text` prints
/// under `verb`.
///
/// # Specification
/// trivial.
fn printed(
    path: &Path,
    root: SourceRoot,
    text: SourceText<'_>,
    verb: Verb,
) -> Vec<Diagnostic>
{
    let step = unsettled(path, root, text);
    entries(&step, verb).collect()
}

/// The one diagnostic a strict source with `text` prints under plain
/// `check`.
///
/// # Specification
/// - requires: the source prints exactly one diagnostic.
/// - ensures: that diagnostic.
/// - provides: the subject of most cases.
/// - fails: never returns a failure.
/// - panics: if the source prints another number of diagnostics.
///
/// # Adequacy
/// - hypothesis: L3 — every single-refusal source prints one diagnostic; a
///   source printing two fails loudly rather than asserting the wrong one.
/// - witness: `tests::diagnostics::a_refusal_names_the_rules_it_stood_inside`
#[spec(ensures: |ref ret| ret.path.as_path() == path)]
fn only(
    path: &Path,
    text: SourceText<'_>,
) -> Diagnostic
{
    let mut printed = printed(path, SourceRoot::Strict, text, Verb::Check(Goals::Gated));
    assert_eq!(printed.len(), 1_usize, "one diagnostic: {printed:?}");
    printed.remove(0)
}

/// The bytes of each appearance of `needle` in `text`, in order.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the span of every occurrence, first to last.
/// - provides: an independent expected locus, indexed by occurrence.
/// - fails: never returns a failure.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — repeated equal siblings are told apart by their
///   occurrence index.
/// - witness: `tests::diagnostics::repeated_equal_siblings_point_at_the_right_occurrence`
#[spec(ensures: |ref ret| ret.iter().all(|&span| text.fragment(span).is_ok_and(|fragment| fragment.as_ref() == needle.as_ref())))]
fn nth(
    text: SourceText<'_>,
    needle: SourceText<'_>,
) -> Vec<ByteSpan>
{
    text.as_ref()
        .match_indices(needle.as_ref())
        .map(|(start, _)| {
            ByteSpan::new(
                ByteOffset::from(start),
                ByteOffset::from(start.saturating_add(needle.as_ref().len())),
            )
            .expect("the span is ordered")
        })
        .collect()
}

/// Each context `diagnostic` carries, as the source text of its bytes
/// (empty when unlocated) and its label.
///
/// # Specification
/// trivial.
fn contexts(
    text: SourceText<'_>,
    diagnostic: &Diagnostic,
) -> Vec<(String, String)>
{
    diagnostic
        .contexts
        .iter()
        .map(|context| match context.locus {
            Maybe::Present(locus) => (
                String::from(
                    text.fragment(locus.span)
                        .expect("a context lies inside the text")
                        .as_ref(),
                ),
                context.label(),
            ),
            Maybe::Absent(_) => (String::new(), context.note()),
        })
        .collect()
}

/// What an origin table cut down for the unlocated cases keeps.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Kept
{
    /// The primary node alone.
    Primary,
    /// Nothing.
    Nothing,
}

/// The force refusal built over an origin table cut down to `kept`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the force refusal's diagnostic, located at its operand when the
///   primary node is kept, unlocated otherwise; every rule it stood inside
///   names a node the table records nothing for, as a node the checker minted
///   does.
/// - provides: the subject of the unlocated cases.
/// - fails: never returns a failure.
/// - panics: if the force source does not refuse with a shape mismatch.
///
/// # Adequacy
/// - hypothesis: L3 — one table keeps the primary node alone, the other
///   nothing; the rules lose their loci in both.
/// - witness: `tests::diagnostics::an_unlocated_rule_becomes_a_note`
/// - witness: `tests::diagnostics::an_unlocated_report_claims_no_span`
#[spec(ensures: |ref ret| matches!(ret.span, Maybe::Present(_)) == (kept == Kept::Primary))]
fn force_without_rules(kept: Kept) -> Diagnostic
{
    let text = SourceText::from(FORCE);
    let step = unsettled(Path::new("force.gandr"), SourceRoot::Strict, text);
    let Step::Source {
        path,
        composed:
            Composed::Settled {
                ref report,
                ref origins,
                ref spellings,
                ref failures,
                ..
            },
        ..
    } = step
    else {
        panic!("the force source settles");
    };
    let declaration = report
        .declarations()
        .iter()
        .find(|declaration| matches!(declaration.produced().refusal(), Maybe::Present(_)))
        .expect("one declaration refuses");
    let Maybe::Present(refusal @ Refusal::Checking(CheckRefusal::ShapeMismatch { at, .. })) =
        declaration.produced().refusal()
    else {
        panic!("the force refuses its operand's shape");
    };
    let TermNode::Value(value) = at
    else {
        panic!("the operand is a value");
    };
    let mut table = OriginTable::new();
    if kept == Kept::Primary {
        let Maybe::Present(origin) = origins.value(value)
        else {
            panic!("the operand is recorded");
        };
        table.record_value(value, origin);
    }
    diagnose(path, text, Subject::Refused {
        declaration,
        refusal,
        origins: &table,
        spellings: spellings.spelled(Spelling::Unicode),
        failure: failures.get(declaration.constant()),
        upstream: Maybe::Absent(upstream::Absent::Own),
    })
}

#[test]
fn a_type_mismatch_is_located_at_its_term()
{
    let diagnostic = only(Path::new("mismatch.gandr"), SourceText::from(MISMATCH));
    assert_eq!(diagnostic.severity, Severity::Error);
    assert_eq!(
        diagnostic.detail.class,
        Class::Refusal(FailureClass::MalformedSource),
        "a type mismatch is malformed source"
    );
    assert_eq!(
        diagnostic.span,
        Maybe::Present(nth(SourceText::from(MISMATCH), SourceText::from("\"text\""))[0]),
        "the checker's refusal is located at the mismatched term through the origin table"
    );
    let primary = match diagnostic.primary() {
        Maybe::Present(primary) => primary,
        Maybe::Absent(reason) => panic!("the mismatch is located: {reason:?}"),
    };
    assert_eq!(
        (primary.locus.line, primary.locus.column),
        (2_usize, 13_usize)
    );
    assert_eq!(
        (
            diagnostic.message.text.as_str(),
            diagnostic.detail.title.as_str()
        ),
        (
            "mismatched types",
            "the type this term synthesises does not convert to the type it is checked against"
        ),
        "the message is plain; the checker's own words stay the title"
    );
    assert_eq!(
        diagnostic.expression,
        Maybe::Present(String::from("\"text\""))
    );
}

#[test]
fn a_mismatch_label_spells_both_types()
{
    let label = |diagnostic: &Diagnostic| match diagnostic.primary() {
        Maybe::Present(primary) => primary.label.clone(),
        Maybe::Absent(reason) => panic!("a located refusal carries a label: {reason:?}"),
    };
    let mismatch = only(Path::new("spelled.gandr"), SourceText::from(MISMATCH));
    assert_eq!(
        (
            mismatch.detail.compared.expected.clone(),
            mismatch.detail.compared.found.clone()
        ),
        (
            Maybe::Present(String::from("Integer")),
            Maybe::Present(String::from("String"))
        ),
        "a mismatch expects its signature's type and found its body's"
    );
    assert_eq!(
        label(&mismatch),
        "its type does not convert: expected `Integer`, found `String`"
    );
    assert_eq!(
        label(&only(Path::new("spelled.gandr"), SourceText::from(FORCE))),
        "its type is not of the required shape: found `Integer`",
        "a shape mismatch expects a former, which its title names, and spells what it found"
    );
    let head = label(&only(
        Path::new("spelled.gandr"),
        SourceText::from("def f(xs: Vec(Integer)) -> -F Integer {\n  pure 1\n}\n"),
    ));
    assert!(
        !head.contains(": "),
        "a refusal that compares no types carries none: {head}"
    );
}

#[test]
fn a_mismatch_spells_the_constructors_its_type_mentions()
{
    let mismatch = only(
        Path::new("constructed.gandr"),
        SourceText::from(
            "data Box : Type {\n  Wrap : (n : Integer) --> Box;\n}\ndef wrapped : Path(Box, \
                 Wrap(4), Wrap(5)) ;\ndef wrapped = 1 ;\n",
        ),
    );
    assert_eq!(
        mismatch.detail.compared.expected,
        Maybe::Present(String::from("Path(Box, Wrap(4), Wrap(5))")),
        "a constructor value is spelled by the name its declaration writes"
    );
}

#[test]
fn a_word_spells_by_its_letters()
{
    let mismatch = only(
        Path::new("worded.gandr"),
        SourceText::from(
            "data Circle : Type {\n  Base : Circle;\n  loop : Base <-> Base;\n}\ndef wound : \
                 Path(Path(Circle, Base, Base), back(loop) ∷ here(Base), here(Base)) ;\ndef \
                 wound = 1 ;\n",
        ),
    );
    assert_eq!(
        mismatch.detail.compared.expected,
        Maybe::Present(String::from(
            "Path(Path(Circle, Base, Base), back(loop) ∷ here(Base), here(Base))"
        )),
        "a word's type is its path type, a letter conses before the rest, and the empty \
             word is `here` at the point"
    );
    let preceded = only(
        Path::new("preceded.gandr"),
        SourceText::from(
            "data Other : Type {\n  Spot : Other;\n}\ndata Circle : Type {\n  Base : Circle;\n  \
                 loop : Base <-> Base;\n}\ndef wound : Path(Path(Circle, Base, Base), back(loop) \
                 ∷ here(Base), here(Base)) ;\ndef wound = 1 ;\n",
        ),
    );
    assert_eq!(
        preceded.detail.compared.expected,
        Maybe::Present(String::from(
            "Path(Path(Circle, Base, Base), back(loop) ∷ here(Base), here(Base))"
        )),
        "the point is spelled by its own family's constructors, not an earlier family's"
    );
}

#[test]
fn a_body_names_its_match_arms_by_their_constructors_809()
{
    let grammar = built_in().expect("the built-in grammar builds");
    let text = SourceText::from(
        "data Nat : Type {\n  Zero : Nat;\n  Succ : (p : Nat) --> Nat;\n}\ndef rec down(n : Nat) \
         -> -F Nat {\n  case n {\n    Zero => return n,\n    Succ(p) => become down[<](p)\n  \
         }\n}\n",
    );
    let Lowered::Module { module, arena } =
        lower_source(&grammar, text, &mut LoweringCount::default())
            .expect("the source lowers")
            .into_lowered()
    else {
        panic!("the source is one module");
    };
    let body = module
        .declarations()
        .iter()
        .find(|declaration| declaration.name().as_ref() == "down")
        .and_then(|declaration| match declaration.outcome() {
            DeclarationOutcome::Bodied { body } | DeclarationOutcome::Completed { body, .. } => {
                arena.value(body)
            },
            DeclarationOutcome::Uncompleted { .. }
            | DeclarationOutcome::Data(_)
            | DeclarationOutcome::Abstract(_)
            | DeclarationOutcome::World
            | DeclarationOutcome::Refused(_) => None,
        });
    let Some(&Value::Thunk(computation)) = body
    else {
        panic!("`down` is defined by a thunk");
    };
    let spelled = constant_names(&module);
    let names: Vec<Name<'_>> = spelled
        .iter()
        .map(|name| Name::from(name.as_str()))
        .collect();
    let families = Families::of(&module);
    let constructors = families.naming(&names);
    let source = CoreSource::new(&arena, &names).naming(&constructors);
    let presentation = present_computation(
        &source,
        CoreNode::Computation(computation),
        PageWidth::from(100_u32),
        Form::Sugared.into(),
    )
    .expect("the body lays out");
    // The anonymous fixpoint has no surface form, so the body is approximate
    // as a whole and names that notation; its arms leave nothing unspelled.
    assert_eq!(
        (
            presentation.to_string(),
            presentation.unspelled().iter().copied().collect::<Vec<_>>()
        ),
        (
            String::from("rec a { fn (b) { case b { Zero => b, Succ(c) => a(c) } } }"),
            vec![Unspelled::Notation(Notation::Fixpoint)]
        ),
        "each arm is written under the constructor it matches: {:?}",
        presentation.unspelled()
    );
}

/// A match over a family with a loop writes the loop's arm under the loop's
/// name: the lowering appends a branch per loop after the constructors', and a
/// table naming the constructors alone printed that arm `?` (#813, #823).
#[test]
fn a_loop_arm_is_named_by_its_loop_823()
{
    let grammar = built_in().expect("the built-in grammar builds");
    let text = SourceText::from(
        "data Circle : Type {\n  Base : Circle;\n  loop : Base <-> Base;\n}\ndef invLooper(x : \
         Circle) -> -F Circle {\n  case x {\n    Base => Base,\n    loop => back(loop)\n  }\n}\n",
    );
    let Lowered::Module { module, arena } =
        lower_source(&grammar, text, &mut LoweringCount::default())
            .expect("the source lowers")
            .into_lowered()
    else {
        panic!("the source is one module");
    };
    let body = module
        .declarations()
        .iter()
        .find(|declaration| declaration.name().as_ref() == "invLooper")
        .and_then(|declaration| match declaration.outcome() {
            DeclarationOutcome::Bodied { body } | DeclarationOutcome::Completed { body, .. } => {
                arena.value(body)
            },
            DeclarationOutcome::Uncompleted { .. }
            | DeclarationOutcome::Data(_)
            | DeclarationOutcome::Abstract(_)
            | DeclarationOutcome::World
            | DeclarationOutcome::Refused(_) => None,
        });
    let Some(&Value::Thunk(computation)) = body
    else {
        panic!("`invLooper` is defined by a thunk");
    };
    let spelled = constant_names(&module);
    let names: Vec<Name<'_>> = spelled
        .iter()
        .map(|name| Name::from(name.as_str()))
        .collect();
    let families = Families::of(&module);
    let constructors = families.naming(&names);
    let source = CoreSource::new(&arena, &names).naming(&constructors);
    let presentation = present_computation(
        &source,
        CoreNode::Computation(computation),
        PageWidth::from(100_u32),
        Form::Sugared.into(),
    )
    .expect("the body lays out");
    assert_eq!(
        (
            presentation.to_string(),
            presentation.fidelity(),
            presentation.unspelled().is_empty()
        ),
        (
            String::from(
                "fn (a) { case a { Base => Base, loop => transport(\\b. Path(Circle, b, Base), \
                 loop, here(Base)) } }"
            ),
            Fidelity::Faithful,
            true
        ),
        "the loop arm is written under its loop: {:?}",
        presentation.unspelled()
    );
}

#[test]
fn a_refusal_keeps_its_failure_and_spells_its_types()
{
    let text = SourceText::from(MISMATCH);
    let step = unsettled(Path::new("kept.gandr"), SourceRoot::Strict, text);
    let Step::Source {
        composed:
            Composed::Settled {
                ref report,
                ref failures,
                ..
            },
        ..
    } = step
    else {
        panic!("the source settles");
    };
    let refused = report
        .declarations()
        .iter()
        .find(|declaration| matches!(declaration.produced().refusal(), Maybe::Present(_)))
        .expect("one declaration refuses");
    let Maybe::Present(failure) = failures.get(refused.constant())
    else {
        panic!("the refused body keeps its failure");
    };
    assert!(
        !failure.obligations().is_empty(),
        "the failure keeps the rules it stood inside"
    );
    let clean = unsettled(
        Path::new("clean.gandr"),
        SourceRoot::Strict,
        SourceText::from("def a = 1 ;\n"),
    );
    let Step::Source {
        composed: Composed::Settled { ref failures, .. },
        ..
    } = clean
    else {
        panic!("the clean source settles");
    };
    assert_eq!(
        *failures,
        Failures::default(),
        "a module that refuses nothing keeps no failure"
    );
}

#[test]
fn a_sealed_type_is_spelled_by_its_path()
{
    let step = unsettled(
        Path::new("sealed.gandr"),
        SourceRoot::Strict,
        SourceText::from(
            "module Counter :> #{ type T, zero : T } { type T = Integer ; def zero = 0 ; }\ndef \
                 leaked : Integer ;\ndef leaked = Counter.zero ;\n",
        ),
    );
    let Step::Source {
        composed:
            Composed::Settled {
                ref report,
                ref spellings,
                ..
            },
        ..
    } = step
    else {
        panic!("the module settles");
    };
    let Some(Maybe::Present(Refusal::Checking(CheckRefusal::TypeMismatch(Mismatch::Value {
        synthesised,
        expected,
        ..
    })))) = report
        .declarations()
        .last()
        .map(|declaration| declaration.produced().refusal())
    else {
        panic!("the leak is a value mismatch");
    };
    let spelled = |node| match spellings.spelled(Spelling::Unicode).get(node) {
        Maybe::Present(presentation) => presentation.as_ref().to_owned(),
        Maybe::Absent(reason) => format!("{reason:?}"),
    };
    assert_eq!(
        (
            spelled(TypeNode::Value(expected)),
            spelled(TypeNode::Value(synthesised))
        ),
        ("Integer".to_owned(), "Counter.T".to_owned()),
        "the atom is named as a client writes it"
    );
}

/// The types a refusal compares are spelled in each spelling while the arena
/// is at hand, and a face reads the one its reader chose (#782).
#[test]
fn a_refusal_spells_its_types_in_either_spelling_782()
{
    for (source, unicode, ascii) in [
        (
            "def r : Integer ≃ String ;\ndef r = 1 ;\n",
            "Integer ≃ String",
            "Integer <~> String",
        ),
        (
            "def r : Integer ≅ String ;\ndef r = 1 ;\n",
            "Integer ≅ String",
            "Iso(Integer, String)",
        ),
    ] {
        let step = unsettled(
            Path::new("relations.gandr"),
            SourceRoot::Strict,
            SourceText::from(source),
        );
        let Step::Source {
            composed:
                Composed::Settled {
                    ref report,
                    ref spellings,
                    ..
                },
            ..
        } = step
        else {
            panic!("the module settles");
        };
        let Some(Maybe::Present(Refusal::Checking(CheckRefusal::TypeMismatch(Mismatch::Value {
            synthesised,
            expected,
            ..
        })))) = report
            .declarations()
            .last()
            .map(|declaration| declaration.produced().refusal())
        else {
            panic!("the literal is a value mismatch");
        };
        let spelled = |spelling, node| match spellings.spelled(spelling).get(node) {
            Maybe::Present(presentation) => presentation.as_ref().to_owned(),
            Maybe::Absent(reason) => format!("{reason:?}"),
        };
        for (spelling, relation) in [(Spelling::Unicode, unicode), (Spelling::Ascii, ascii)] {
            assert_eq!(
                [
                    spelled(spelling, TypeNode::Value(expected)),
                    spelled(spelling, TypeNode::Value(synthesised))
                ],
                [String::from(relation), String::from("Integer")],
                "{source:?} in {spelling:?}"
            );
        }
    }
}

#[test]
fn a_refusal_names_the_rules_it_stood_inside()
{
    assert_eq!(
        contexts(
            SourceText::from(FORCE),
            &only(Path::new("force.gandr"), SourceText::from(FORCE))
        ),
        [
            (
                String::from("thunk { become force 1 }"),
                String::from(
                    "checked against `() => Integer`; while checking the body of this thunk"
                )
            ),
            (
                String::from("force 1"),
                String::from("checked against `-F Integer`; while forcing this")
            ),
        ],
        "the force of an integer stands inside the thunk, outermost first"
    );
    let application = only(
        Path::new("application.gandr"),
        SourceText::from(APPLICATION),
    );
    assert_eq!(
        contexts(SourceText::from(APPLICATION), &application),
        [
            (
                String::from("thunk { become (pure 1)(2) }"),
                String::from(
                    "checked against `() => Integer`; while checking the body of this thunk"
                )
            ),
            (
                String::from("(pure 1)(2)"),
                String::from(
                    "checked against `-F Integer`; while synthesising the function this \
                         applies"
                )
            ),
        ],
        "the head that is not a function stands inside the application and the thunk"
    );
    assert_eq!(
        application
            .contexts
            .iter()
            .map(|context| context.role)
            .collect::<Vec<_>>(),
        [FrameRole::ThunkBody, FrameRole::ApplicationHead],
        "each context keeps its rule's stable name"
    );
    assert_eq!(
        contexts(
            SourceText::from(MISMATCH),
            &only(Path::new("mismatch.gandr"), SourceText::from(MISMATCH))
        ),
        Vec::new(),
        "a body refused where it stands has no rule beyond its primary locus"
    );
}

#[test]
fn a_mismatch_under_a_binder_names_it()
{
    let diagnostic = only(Path::new("bound.gandr"), SourceText::from(BOUND));
    let named = contexts(SourceText::from(BOUND), &diagnostic);
    assert!(
        named.contains(&(
            String::from("run"),
            String::from(
                "checked against `-F String`; while checking the body under this binding; \
                     binds m : Integer"
            )
        )),
        "the run names the binder it opened and its type: {named:?}"
    );
    assert_eq!(
        diagnostic
            .hypotheses
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>(),
        ["n : Integer", "m : Integer"],
        "the hypotheses in scope are the parameter and the run's binder, outermost first"
    );
    assert_eq!(
        diagnostic.span,
        Maybe::Present(nth(SourceText::from(BOUND), SourceText::from("m"))[1]),
        "the mismatch is the returned binder"
    );
}

/// A refusal spells a type under the binders in scope by the names the
/// source wrote, never `?`, and the declared type a frame names by the
/// parameters the declaration writes, never fresh letters (#418).
#[test]
fn a_refusal_spells_its_binders_by_name_418()
{
    let text = SourceText::from(
        "data Theory : Type {\n  Monoid : Theory;\n  Group : Theory;\n}\ndef counted_at(s : Theory) -> \
             -F Type {\n  case s {\n    Monoid => return Integer,\n    Group => return \
             String\n  }\n}\ndef moved(presented : Theory, other : Theory, n : counted_at(presented)) \
             -> -F counted_at(other) {\n  n\n}\n",
    );
    let diagnostic = only(Path::new("moved.gandr"), text);
    assert_eq!(
        (
            diagnostic.detail.compared.expected.clone(),
            diagnostic.detail.compared.found.clone()
        ),
        (
            Maybe::Present(String::from("counted_at(other)")),
            Maybe::Present(String::from("counted_at(presented)"))
        ),
        "the mismatch names the two binders it is over"
    );
    assert_eq!(
        diagnostic
            .hypotheses
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>(),
        [
            "presented : Theory",
            "other : Theory",
            "n : counted_at(presented)"
        ],
        "a hypothesis's type names the binders before it"
    );
    let notes: Vec<String> = contexts(text, &diagnostic)
        .into_iter()
        .map(|(_, note)| note)
        .collect();
    assert!(
        notes.iter().any(|note| {
            note.contains(
                "(presented : Theory) -> (other : Theory) -> counted_at(presented) -> -F \
                     counted_at(other)",
            )
        }),
        "the declared type a frame names binds the declaration's parameters: {notes:?}"
    );
}

#[test]
fn an_unlocated_rule_becomes_a_note()
{
    let diagnostic = force_without_rules(Kept::Primary);
    assert!(
        diagnostic
            .contexts
            .iter()
            .all(|context| matches!(context.locus, Maybe::Absent(_))),
        "a rule whose node the table records nothing for marks no bytes"
    );
    assert_eq!(
        contexts(SourceText::from(FORCE), &diagnostic)
            .into_iter()
            .map(|(_, note)| note)
            .collect::<Vec<_>>(),
        [
            "while checking the body of this thunk",
            "while comparing the type this synthesises with the one it is checked against",
            "while forcing this",
        ],
        "each unlocated rule reads as its sentence, outermost first"
    );
    assert!(
        diagnostic
            .annotations
            .iter()
            .all(|annotation| annotation.kind == AnnotationKind::Primary),
        "an unlocated rule adds no annotation"
    );
}

#[test]
fn an_unlocated_report_claims_no_span()
{
    let diagnostic = force_without_rules(Kept::Nothing);
    assert_eq!(
        diagnostic.span,
        Maybe::Absent(report_span::Absent::Unrecorded),
        "a node the table records nothing for is no locus"
    );
    assert!(matches!(diagnostic.primary(), Maybe::Absent(_)));
    assert!(
        diagnostic.annotations.is_empty(),
        "an unlocated report marks nothing"
    );
    assert!(
        matches!(diagnostic.excerpt, Maybe::Absent(_)),
        "and quotes no line"
    );
    assert!(
        matches!(diagnostic.expression, Maybe::Absent(_)),
        "and names no expression"
    );
}

#[test]
fn a_return_position_failure_points_at_the_returned_value()
{
    let text = "def g(v: Integer) -> -F String { return v }\n";
    let diagnostic = only(Path::new("returned.gandr"), SourceText::from(text));
    assert_eq!(
        diagnostic.span,
        Maybe::Present(nth(SourceText::from(text), SourceText::from("v"))[1]),
        "the mismatch is the value returned, not the return or the function"
    );
    assert_eq!(
        diagnostic.contexts.last().map(|context| context.role),
        Some(FrameRole::ReturnValue),
        "the innermost rule is the return's"
    );
}

#[test]
fn repeated_equal_siblings_point_at_the_right_occurrence()
{
    let text = "def h(a: String, b: Integer) -> -F Integer { return b }\ndef k(u: Integer) \
                    -> -F Integer { become h(\"no\", \"no\") }\n";
    assert_eq!(
        only(Path::new("siblings.gandr"), SourceText::from(text)).span,
        Maybe::Present(nth(SourceText::from(text), SourceText::from("\"no\""))[1]),
        "the second of two equal arguments is the one that mismatches"
    );
}

#[test]
fn a_shadowed_builtin_is_a_warning()
{
    let text = "def add : Integer ;\ndef add = 1 ;\ndef f(int: Integer) -> -F Integer { return \
                    int }\ndef g : Integer ;\ndef g = missing ;\n";
    let checked = printed(
        Path::new("shadow.gandr"),
        SourceRoot::Strict,
        SourceText::from(text),
        Verb::Check(Goals::Gated),
    );
    assert_eq!(
        checked
            .iter()
            .map(|diagnostic| (
                diagnostic.severity,
                diagnostic.detail.class,
                diagnostic.span
            ))
            .collect::<Vec<_>>(),
        [
            (
                Severity::Warning,
                Class::Warning,
                Maybe::Present(nth(SourceText::from(text), SourceText::from("add"))[0])
            ),
            (
                Severity::Warning,
                Class::Warning,
                Maybe::Present(nth(SourceText::from(text), SourceText::from("int"))[0])
            ),
            (
                Severity::Error,
                Class::Refusal(FailureClass::MalformedSource),
                Maybe::Present(nth(SourceText::from(text), SourceText::from("missing"))[0])
            ),
        ],
        "each shadowed builtin is a warning at its name, printed before the declarations"
    );
    for warning in &checked[.. 2] {
        assert!(
            matches!(warning.identifier, Maybe::Present(ref spelling) if spelling.as_ref() == "ShadowedBuiltin"),
            "a warning is named as the refusal the reject policy files"
        );
        assert_eq!(
            warning
                .annotations
                .first()
                .map(|primary| primary.label.as_str()),
            Some("shadows a builtin")
        );
    }
    assert_eq!(
        checked[1].message.text,
        "`int` shadows a builtin name; the source's binding wins"
    );
    assert!(
        printed(
            Path::new("shadow.gandr"),
            SourceRoot::Strict,
            SourceText::from(text),
            Verb::Test
        )
        .iter()
        .all(|diagnostic| diagnostic.severity != Severity::Warning),
        "`test` prints settlements, never a warning"
    );
    assert!(
        printed(
            Path::new("shadow.gandr"),
            SourceRoot::Strict,
            SourceText::from("def add : Integer ;\ndef add = 1 ;\n"),
            Verb::Check(Goals::Gated),
        )
        .iter()
        .all(|diagnostic| diagnostic.severity == Severity::Warning),
        "a warning unsettles nothing"
    );
}

#[test]
fn an_inferred_exit_is_a_finding_whose_fix_writes_its_keyword()
{
    let text = "@[ explicit_exits ]\ndef kept(n: Integer) -> -F Integer { n }\ndef called(n: \
                    Integer) -> -F Integer { kept(n) }\n";
    let path = Path::new("exits.gandr");
    let tail = |needle: &str| {
        let start = text
            .find(needle)
            .expect("the tail is written")
            .saturating_add(2);
        let end = start.saturating_add(needle.len()).saturating_sub(4);
        (
            ByteSpan::new(ByteOffset::from(start), ByteOffset::from(end))
                .expect("the tail is ordered"),
            ByteSpan::new(ByteOffset::from(start), ByteOffset::from(start))
                .expect("an insertion is ordered"),
        )
    };
    let (returned, before_returned) = tail("{ n }");
    let (called, before_called) = tail("{ kept(n) }");
    let finding = |diagnostic: &Diagnostic| {
        (
            diagnostic.severity,
            diagnostic.detail.class,
            diagnostic.identifier,
            diagnostic.span,
            diagnostic
                .annotations
                .first()
                .map(|primary| primary.label.clone()),
            diagnostic.fix.clone(),
        )
    };
    let lint = (
        Severity::Warning,
        Class::Lint(Lint::ExplicitExits),
        Maybe::Present(Identifier::Lint(Lint::ExplicitExits)),
    );
    let asked = printed(
        path,
        SourceRoot::Strict,
        SourceText::from(text),
        Verb::Check(Goals::Gated),
    );
    assert_eq!(
        asked.iter().map(finding).collect::<Vec<_>>(),
        [(
            lint.0,
            lint.1,
            lint.2,
            Maybe::Present(returned),
            Some(String::from("exits by an inferred `return`")),
            Maybe::Present(Fix {
                span: before_returned,
                replacement: String::from("return "),
            }),
        )],
        "the attribute asks for the exit its declaration's body left out, and nowhere else"
    );
    let step = unsettled(path, SourceRoot::Strict, SourceText::from(text));
    let everywhere: Vec<Diagnostic> = entries(&step, Verb::Check(Goals::Gated))
        .linting(Lints::enabling([Lint::ExplicitExits]))
        .collect();
    assert_eq!(
        everywhere.iter().map(finding).collect::<Vec<_>>(),
        [
            (
                lint.0,
                lint.1,
                lint.2,
                Maybe::Present(returned),
                Some(String::from("exits by an inferred `return`")),
                Maybe::Present(Fix {
                    span: before_returned,
                    replacement: String::from("return "),
                }),
            ),
            (
                lint.0,
                lint.1,
                lint.2,
                Maybe::Present(called),
                Some(String::from("exits by an inferred `become`")),
                Maybe::Present(Fix {
                    span: before_called,
                    replacement: String::from("become "),
                }),
            ),
        ],
        "the lint enabled by the run finds every elided exit, each in source order"
    );
    assert!(
        entries(&step, Verb::Test)
            .linting(Lints::enabling([Lint::ExplicitExits]))
            .all(|diagnostic| diagnostic.severity != Severity::Warning),
        "`test` prints settlements, never a lint's finding"
    );
    let mut fixed = String::from(text);
    for diagnostic in everywhere.iter().rev() {
        if let Maybe::Present(ref fix) = diagnostic.fix {
            fixed.replace_range(
                usize::from(fix.span.start()) .. usize::from(fix.span.end()),
                &fix.replacement,
            );
        }
    }
    assert_eq!(
        fixed,
        "@[ explicit_exits ]\ndef kept(n: Integer) -> -F Integer { return n }\ndef called(n: \
             Integer) -> -F Integer { become kept(n) }\n"
    );
    let rechecked = unsettled(path, SourceRoot::Strict, SourceText::from(fixed.as_str()));
    assert_eq!(
        entries(&rechecked, Verb::Check(Goals::Gated))
            .linting(Lints::enabling([Lint::ExplicitExits]))
            .collect::<Vec<_>>(),
        [],
        "the fixed source settles and the lint finds nothing in it"
    );
}

#[test]
fn an_inferred_run_is_a_finding_whose_fix_writes_its_keyword()
{
    let text = "def id(n: Integer) -> -F Integer { n }\n@[ explicit_runs ]\ndef nested(n: \
                    Integer) -> -F Integer { id(id(n)) }\ndef returned(n: Integer) -> -F Integer \
                    { return id(n) }\ndef leading(n: Integer) -> -F Integer { id(n) + 1 }\ndef \
                    grouped(n: Integer) -> -F Integer { return n + 1 }\n";
    let path = Path::new("runs.gandr");
    let call = |context: &str, offset: usize| {
        let start = text
            .find(context)
            .expect("the call is written")
            .saturating_add(offset);
        (
            ByteSpan::new(
                ByteOffset::from(start),
                ByteOffset::from(start.saturating_add(5_usize)),
            )
            .expect("the call is ordered"),
            ByteSpan::new(ByteOffset::from(start), ByteOffset::from(start))
                .expect("an insertion is ordered"),
        )
    };
    let (inner, before_inner) = call("{ id(id(n)) }", 5_usize);
    let (returned, before_returned) = call("{ return id(n) }", 9_usize);
    let (leading, _) = call("{ id(n) + 1 }", 2_usize);
    let (grouped, _) = call("{ return n + 1 }", 9_usize);
    let finding = |diagnostic: &Diagnostic| {
        (
            diagnostic.severity,
            diagnostic.detail.class,
            diagnostic.identifier,
            diagnostic.span,
            diagnostic
                .annotations
                .first()
                .map(|primary| primary.label.clone()),
            diagnostic.fix.clone(),
        )
    };
    let found = |span: ByteSpan, fix: (ByteSpan, &str)| {
        (
            Severity::Warning,
            Class::Lint(Lint::ExplicitRuns),
            Maybe::Present(Identifier::Lint(Lint::ExplicitRuns)),
            Maybe::Present(span),
            Some(String::from("runs by an inferred `run`")),
            Maybe::Present(Fix {
                span: fix.0,
                replacement: String::from(fix.1),
            }),
        )
    };
    let asked = printed(
        path,
        SourceRoot::Strict,
        SourceText::from(text),
        Verb::Check(Goals::Gated),
    );
    assert_eq!(
        asked.iter().map(finding).collect::<Vec<_>>(),
        [found(inner, (before_inner, "run "))],
        "the attribute asks for the run its declaration's body left out, and nowhere else"
    );
    assert_eq!(
        asked
            .first()
            .map(|diagnostic| diagnostic.message.text.as_str()),
        Some(
            "this computation stands where a value is read; the checker infers `run`, which \
                 the `explicit-runs` lint asks to be written"
        )
    );
    let step = unsettled(path, SourceRoot::Strict, SourceText::from(text));
    let everywhere: Vec<Diagnostic> = entries(&step, Verb::Check(Goals::Gated))
        .linting(Lints::enabling([Lint::ExplicitRuns]))
        .collect();
    assert_eq!(
        everywhere.iter().map(finding).collect::<Vec<_>>(),
        [
            found(inner, (before_inner, "run ")),
            found(returned, (before_returned, "run ")),
            found(leading, (leading, "(run id(n))")),
            found(grouped, (grouped, "run (n + 1)")),
        ],
        "the lint enabled by the run finds every inferred run, each in source order; one \
             that begins a block's tail is written parenthesised, where a bare `run` would begin \
             a bind, and an operator call is grouped after `run`, which would otherwise run its \
             first operand alone"
    );
    let mut fixed = String::from(text);
    for diagnostic in everywhere.iter().rev() {
        if let Maybe::Present(ref fix) = diagnostic.fix {
            fixed.replace_range(
                usize::from(fix.span.start()) .. usize::from(fix.span.end()),
                &fix.replacement,
            );
        }
    }
    assert_eq!(
        fixed,
        "def id(n: Integer) -> -F Integer { n }\n@[ explicit_runs ]\ndef nested(n: Integer) \
             -> -F Integer { id(run id(n)) }\ndef returned(n: Integer) -> -F Integer { return run \
             id(n) }\ndef leading(n: Integer) -> -F Integer { (run id(n)) + 1 }\ndef grouped(n: \
             Integer) -> -F Integer { return run (n + 1) }\n"
    );
    let rechecked = unsettled(path, SourceRoot::Strict, SourceText::from(fixed.as_str()));
    assert_eq!(
        entries(&rechecked, Verb::Check(Goals::Gated))
            .linting(Lints::enabling([Lint::ExplicitRuns]))
            .collect::<Vec<_>>(),
        [],
        "the fixed source settles and the lint finds nothing in it"
    );
}

#[test]
fn refusals_of_one_class_label_what_their_locus_is()
{
    let mismatch = only(Path::new("mismatch.gandr"), SourceText::from(MISMATCH));
    let head = only(
        Path::new("head.gandr"),
        SourceText::from("def f(xs: Vec(Integer)) -> -F Integer {\n  pure 1\n}\n"),
    );
    assert_eq!(
        (mismatch.detail.class, head.detail.class),
        (
            Class::Refusal(FailureClass::MalformedSource),
            Class::Refusal(FailureClass::MalformedSource)
        ),
        "both refusals are the author's mistake"
    );
    let label = |diagnostic: &Diagnostic| match diagnostic.primary() {
        Maybe::Present(primary) => primary.label.clone(),
        Maybe::Absent(reason) => panic!("a located refusal carries a label: {reason:?}"),
    };
    assert_ne!(
        label(&mismatch),
        label(&head),
        "a term whose type does not convert and a head nothing answers are different loci"
    );
    for diagnostic in [&mismatch, &head] {
        assert_ne!(
            label(diagnostic),
            diagnostic.detail.class.to_string(),
            "the underline says what the bytes are, not the class"
        );
        assert!(
            !diagnostic.detail.title.contains(".."),
            "the annotation locates the refusal; the title repeats no byte range"
        );
    }
}

#[test]
fn a_report_exposes_the_context_it_marks()
{
    let marked = |diagnostic: &Diagnostic| -> Vec<(ByteSpan, String)> {
        diagnostic
            .annotations
            .iter()
            .filter(|annotation| annotation.kind == AnnotationKind::Context)
            .map(|annotation| (annotation.locus.span, annotation.label.clone()))
            .collect()
    };
    assert_eq!(
        marked(&only(
            Path::new("mismatch.gandr"),
            SourceText::from(MISMATCH)
        )),
        [(
            nth(SourceText::from(MISMATCH), SourceText::from("Integer"))[0],
            String::from("the type it is checked against")
        )],
        "the signature stands as the expected type; the synthesised type has no origin"
    );
    let duplicate = "def a : Integer ;\ndef a : Integer ;\ndef a = 1 ;\n";
    assert_eq!(
        marked(&only(
            Path::new("duplicate.gandr"),
            SourceText::from(duplicate)
        )),
        [(
            nth(
                SourceText::from(duplicate),
                SourceText::from("def a : Integer ;")
            )[0],
            String::from("first written here")
        )],
        "the first signature is the duplicate's one context locus"
    );
    let goals = printed(
        Path::new("hole.gandr"),
        SourceRoot::Strict,
        SourceText::from("def hole : Integer ;\n"),
        Verb::Check(Goals::Reported),
    );
    let [ref goal] = *goals.as_slice()
    else {
        panic!("one goal");
    };
    assert_eq!(goal.severity, Severity::Goal);
    assert_eq!(marked(goal), Vec::new(), "a goal names no context");
}

#[test]
fn a_suspended_goal_names_the_hole_it_waits_on()
{
    let goals = printed(
        Path::new("suspended.gandr"),
        SourceRoot::Strict,
        SourceText::from("def code : Type ;\ndef three : code ;\ndef three = 3 ;\n"),
        Verb::Check(Goals::Reported),
    );
    let [ref hole, ref waiting] = *goals.as_slice()
    else {
        panic!("the hole and the declaration waiting on it are goals: {goals:?}");
    };
    assert_eq!(
        (hole.severity, waiting.severity),
        (Severity::Goal, Severity::Goal),
        "a suspension is an obligation, not a refusal"
    );
    assert_eq!(
        waiting.message.text,
        "`three` states checks owing 0; produced checks owing 1; it waits on `code`"
    );
    assert!(
        !hole.message.text.contains("waits on"),
        "the hole itself waits on nothing: {}",
        hole.message.text
    );
}

#[test]
fn a_labeled_context_retains_its_locus_and_cause()
{
    let duplicate = "def a : Integer ;\ndef a : Integer ;\ndef a = 1 ;\n";
    let diagnostic = only(Path::new("duplicate.gandr"), SourceText::from(duplicate));
    assert_eq!(
        diagnostic
            .annotations
            .iter()
            .map(|annotation| (annotation.kind, annotation.locus.line))
            .collect::<Vec<_>>(),
        [
            (AnnotationKind::Primary, 2_usize),
            (AnnotationKind::Context, 1_usize)
        ],
        "the duplicate is primary on its own line; the first signature is context on its own"
    );
    assert!(
        diagnostic
            .annotations
            .iter()
            .all(|annotation| !annotation.label.is_empty()),
        "each annotation says what its bytes are"
    );
}

#[test]
fn a_report_preserves_refusal_identity_and_title_payloads()
{
    let cases = [
        (
            MISMATCH,
            Verb::Check(Goals::Gated),
            Maybe::Present("TypeMismatch"),
            &[][..],
            &[][..],
        ),
        (
            "def broken = missing ;\n",
            Verb::Check(Goals::Gated),
            Maybe::Present("UnresolvedName"),
            &[][..],
            &["missing"][..],
        ),
        (
            "@[ owes(0) ] def hole : Integer ;\n",
            Verb::Check(Goals::Reported),
            Maybe::Absent(report_identifier::Absent::Statement),
            &[0_usize, 1_usize][..],
            &["hole"][..],
        ),
    ];
    for (source, verb, identifier, numbers, names) in cases {
        let held = printed(
            Path::new("named.gandr"),
            SourceRoot::Fixture,
            SourceText::from(source),
            verb,
        );
        let [ref diagnostic] = *held.as_slice()
        else {
            panic!("one diagnostic for {source:?}");
        };
        let named = match diagnostic.identifier {
            Maybe::Present(ref spelling) => Maybe::Present(spelling.to_string()),
            Maybe::Absent(reason) => Maybe::Absent(reason),
        };
        let expected = match identifier {
            Maybe::Present(spelling) => Maybe::Present(spelling.to_owned()),
            Maybe::Absent(reason) => Maybe::Absent(reason),
        };
        assert_eq!(named, expected, "stable refusal identity for {source:?}");
        let title = &diagnostic.detail.title;
        for name in names {
            assert!(title.contains(name), "source name in {title}");
        }
        assert!(
            title
                .split(|character: char| !character.is_ascii_digit())
                .filter_map(|digits| digits.parse::<usize>().ok())
                .eq(numbers.iter().copied()),
            "the title keeps its numeric roles without core addresses: {title}"
        );
    }
}

#[test]
fn the_settle_note_says_what_was_expected_in_words()
{
    for (source, note) in [
        (
            "@[ owes(0) ] def a = missing ;\n",
            "`a` is expected to check, and this refusal leaves it unsettled",
        ),
        (
            "@[ owes(3) ] def b = missing ;\n",
            "`b` is expected to check owing 3 obligations, and this refusal leaves it \
                 unsettled; surviving obligations: 0 undeclared, 3 unproduced",
        ),
        (
            "@[ refuses(\"TypeMismatch\") ] def c = missing ;\n",
            "`c` is expected to be refused with TypeMismatch, and this refusal is not that \
                 one",
        ),
    ] {
        let held = printed(
            Path::new("noted.gandr"),
            SourceRoot::Fixture,
            SourceText::from(source),
            Verb::Check(Goals::Gated),
        );
        let [ref diagnostic] = *held.as_slice()
        else {
            panic!("one refusal for {source:?}");
        };
        assert_eq!(
            diagnostic.note,
            Maybe::Present(String::from(note)),
            "the note says what was expected and why it did not happen"
        );
    }
}

#[test]
fn a_refused_declaration_is_located()
{
    let text = "def answer = 42 ;\ndef broken = missing ;\ndef wrong : Integer ;\ndef wrong = \
                    \"text\" ;\n@[ owes(1) ] def later : Integer ;\n";
    let malformed = Class::Refusal(FailureClass::MalformedSource);
    for verb in [
        Verb::Check(Goals::Gated),
        Verb::Check(Goals::Reported),
        Verb::Test,
    ] {
        assert_eq!(
            printed(
                Path::new("refused.gandr"),
                SourceRoot::Strict,
                SourceText::from(text),
                verb
            )
            .iter()
            .map(|diagnostic| (diagnostic.detail.class, diagnostic.span))
            .collect::<Vec<_>>(),
            [
                (
                    malformed,
                    Maybe::Present(nth(SourceText::from(text), SourceText::from("missing"))[0])
                ),
                (
                    malformed,
                    Maybe::Present(nth(SourceText::from(text), SourceText::from("\"text\""))[0])
                ),
                (
                    malformed,
                    Maybe::Present(nth(SourceText::from(text), SourceText::from("owes(1)"))[0])
                ),
            ],
            "the lowering's, the checker's and the corpus root's refusals each sit at their \
                 own span under {verb:?}"
        );
    }
}

#[test]
fn an_importer_s_refusal_is_located_in_its_own_text()
{
    let scratch = Scratch::new(Path::new("importer"));
    let user = "import \"./base.gandr\" ;\ndef two : Integer ;\ndef two = missing ;\n";
    scratch.file(
        Path::new("strict/base.gandr"),
        SourceText::from("def one : Integer ;\ndef one = 1 ;\n"),
    );
    scratch.file(Path::new("strict/user.gandr"), SourceText::from(user));
    let mut found = Vec::new();
    let ControlFlow::Continue(_report) = Walk::new(vec![scratch.0.clone()]).visit(
        Width::SERIAL,
        |step| -> ControlFlow<Infallible> {
            found.extend(
                entries(&step, Verb::Check(Goals::Reported))
                    .filter(|diagnostic| diagnostic.path.ends_with("user.gandr")),
            );
            ControlFlow::Continue(())
        },
    );
    let [ref refusal] = *found.as_slice()
    else {
        panic!("the importer reports its one refusal: {found:?}");
    };
    assert_eq!(
        refusal.span,
        Maybe::Present(nth(SourceText::from(user), SourceText::from("missing"))[0]),
        "the span is measured in the importer's own text, not the unit's"
    );
    let Maybe::Present(primary) = refusal.primary()
    else {
        panic!("the refusal is located");
    };
    assert_eq!(
        (primary.locus.line, primary.locus.column),
        (3_usize, 11_usize),
        "its line and column are the importer's own"
    );
    let Maybe::Present(ref excerpt) = refusal.excerpt
    else {
        panic!("the refusal quotes its line");
    };
    assert_eq!(
        (excerpt.line, excerpt.text.lines().next()),
        (3_usize, Some("def two = missing ;")),
        "the excerpt is the importer's line, not the sibling's"
    );
}

#[test]
fn one_refusal_details_each_verbosity()
{
    let diagnostic = only(Path::new("force.gandr"), SourceText::from(FORCE));
    let names = |verbosity| {
        diagnostic
            .details(verbosity)
            .into_iter()
            .map(|detail| detail.name)
            .collect::<Vec<_>>()
    };
    assert_eq!(names(Verbosity::User), Vec::<&str>::new());
    assert_eq!(names(Verbosity::Json), Vec::<&str>::new());
    assert_eq!(names(Verbosity::Detailed), [
        "class",
        "detail",
        "expression"
    ]);
    assert_eq!(names(Verbosity::Debug), [
        "class",
        "detail",
        "expression",
        "spans",
        "rules",
        "refusal"
    ]);
    let bound = only(Path::new("bound.gandr"), SourceText::from(BOUND));
    assert!(
        bound
            .details(Verbosity::Detailed)
            .iter()
            .any(|detail| detail.name == "hypotheses"
                && detail.text == "`n : Integer`, `m : Integer`"),
        "the hypotheses show from the detailed level"
    );
    let image: serde_json::Value =
        serde_json::from_str(&diagnostic.json()).expect("the JSON image parses");
    assert_eq!(image["name"], "ShapeMismatch");
    assert_eq!(image["message"], diagnostic.message.text.as_str());
    assert_eq!(image["title"], diagnostic.detail.title.as_str());
    assert_eq!(
        (&image["primary"]["line"], &image["primary"]["column"]),
        (&serde_json::json!(2_u64), &serde_json::json!(30_u64)),
        "the primary locus is where the terminal points"
    );
    assert_eq!(
        image["contexts"].as_array().map(Vec::len),
        Some(diagnostic.contexts.len()),
        "every context is in the image"
    );
}

#[test]
fn each_verb_prints_its_entries()
{
    let scratch = Scratch::new(Path::new("entries"));
    for (relative, text) in [
        ("fixture/hole.gandr", "def hole : Integer ;\n"),
        ("fixture/pending/lowered.gandr", "def a = 1 ;\n"),
        ("fixture/pending/whole.gandr", "pure 3\n"),
        (
            "fixture/settled.gandr",
            "@[ owes(1) ] def later : Integer ;\n",
        ),
        (
            "fixture/unproduced.gandr",
            "@[ refuses(\"UnresolvedName\") ] def answer = 42 ;\n",
        ),
        ("strict/whole.gandr", "pure 3\n"),
    ] {
        scratch.file(Path::new(relative), SourceText::from(text));
    }
    let printed = |verb: Verb| {
        let mut printed = Vec::new();
        let mut line = String::new();
        let ControlFlow::Continue(_report) = Walk::new(vec![scratch.0.clone()]).visit(
            Width::SERIAL,
            |step| -> ControlFlow<Infallible> {
                for diagnostic in entries(&step, verb) {
                    if diagnostic.severity == Severity::Ledger {
                        let image: serde_json::Value = serde_json::from_str(&diagnostic.json())
                            .expect("a ledger line's JSON image parses");
                        assert_eq!(image["level"], "line");
                        line.clear();
                        core::fmt::Write::write_fmt(
                            &mut line,
                            format_args!(
                                "{}: {}",
                                diagnostic.path.display(),
                                diagnostic.message.text
                            ),
                        )
                        .expect("a ledger line writes");
                        assert_eq!(
                            image["line"],
                            line.as_str(),
                            "the JSON image carries the line as the terminal prints it"
                        );
                    }
                    printed.push((
                        diagnostic
                            .path
                            .strip_prefix(&scratch.0)
                            .expect("within scratch")
                            .to_path_buf(),
                        diagnostic.severity,
                        diagnostic.detail.class,
                    ));
                }
                ControlFlow::Continue(())
            },
        );
        printed
    };
    let check = |hole: Severity, class: Class| {
        vec![
            (PathBuf::from("fixture/hole.gandr"), hole, class),
            (
                PathBuf::from("fixture/pending/lowered.gandr"),
                Severity::Ledger,
                Class::Ledger,
            ),
            (
                PathBuf::from("fixture/unproduced.gandr"),
                Severity::Error,
                Class::Unsettled(Unsettlement::Unproduced),
            ),
            (
                PathBuf::from("strict/whole.gandr"),
                Severity::Error,
                Class::Refusal(FailureClass::Unrepresentable),
            ),
        ]
    };
    assert_eq!(
        printed(Verb::Check(Goals::Gated)),
        check(Severity::Error, Class::Unsettled(Unsettlement::Obligations))
    );
    assert_eq!(
        printed(Verb::Check(Goals::Reported)),
        check(Severity::Goal, Class::Goal)
    );
    assert_eq!(printed(Verb::Test), vec![
        (
            PathBuf::from("fixture/hole.gandr"),
            Severity::Error,
            Class::Unsettled(Unsettlement::Obligations)
        ),
        (
            PathBuf::from("fixture/pending/lowered.gandr"),
            Severity::Ledger,
            Class::Ledger
        ),
        (
            PathBuf::from("fixture/pending/whole.gandr"),
            Severity::Ledger,
            Class::Ledger
        ),
        (
            PathBuf::from("fixture/settled.gandr"),
            Severity::Ledger,
            Class::Ledger
        ),
        (
            PathBuf::from("fixture/unproduced.gandr"),
            Severity::Error,
            Class::Unsettled(Unsettlement::Unproduced)
        ),
        (
            PathBuf::from("strict/whole.gandr"),
            Severity::Error,
            Class::Refusal(FailureClass::Unrepresentable)
        ),
    ]);
}

#[test]
fn a_declaration_naming_a_refused_one_is_a_note()
{
    let text = SourceText::from(
        "def a() -> Integer {\n  return 1 ~ 2\n}\n\ndef b() -> Integer {\n  return a()\n}\n\ndef \
             c() -> Integer {\n  return 1\n}\n\ndef d() -> Integer {\n  return c()\n}\n",
    );
    let printed = printed(
        Path::new("cascade.gandr"),
        SourceRoot::Strict,
        text,
        Verb::Check(Goals::Gated),
    );
    let called = nth(text, SourceText::from("a()"))[1];
    let call = ByteSpan::new(
        called.start(),
        ByteOffset::from(usize::from(called.start()) + 1),
    )
    .expect("ordered");
    assert_eq!(
        printed
            .iter()
            .map(|diagnostic| (diagnostic.severity, diagnostic.span))
            .collect::<Vec<_>>(),
        vec![
            (
                Severity::Error,
                Maybe::Present(nth(text, SourceText::from("~"))[0])
            ),
            (Severity::Note, Maybe::Present(call)),
        ],
        "the refused declaration is the one error; the one calling it is a note at the \
             call, and the one calling a declaration that checks prints nothing"
    );
    let Maybe::Present(ref note) = printed[1].note
    else {
        panic!("the note closes with what leaves it unsettled");
    };
    assert_eq!(
        note, "`b` is expected to check, and the refusal of `a` leaves it unsettled",
        "a declaration expected to check owing nothing is told what leaves it unsettled"
    );
    let owing = SourceText::from(
        "def a() -> Integer {\n  return 1 ~ 2\n}\n\n@[ owes(1) ]\ndef b() -> Integer {\n  \
             return a()\n}\n",
    );
    let owing_printed = self::printed(
        Path::new("owing.gandr"),
        SourceRoot::Fixture,
        owing,
        Verb::Check(Goals::Gated),
    );
    let notes: Vec<_> = owing_printed
        .iter()
        .filter(|diagnostic| diagnostic.severity == Severity::Note)
        .map(|diagnostic| diagnostic.note.clone())
        .collect();
    assert_eq!(
        notes,
        [Maybe::Present(String::from(
            "`b` is expected to check owing 1 obligations, and this refusal leaves it \
                 unsettled; surviving obligations: 0 undeclared, 1 unproduced; it rests on `a`, \
                 which is refused"
        ))],
        "a declaration expected to owe is told its own expectation, then what it rests on"
    );
}

/// The malformed-form sweep: each pathological fixture cut short at every
/// word of its own text (an importer's, not its closure's), each cut's
/// malformed form reporting its parse error alone.
mod sweeps
{
    use alloc::collections::BTreeSet;

    use gandr_workflow_sweep::Sample;
    use gandr_workflow_sweep::SampleName;
    use gandr_workflow_sweep::SampleSize;
    use gandr_workflow_sweep::Sweep;

    use super::*;

    /// The sample: twenty sources under `fixture/pathological`, ranked by
    /// their BLAKE3 digest under this name, and every one the change adds
    /// or modifies (`gandr-workflow-sweep`). The `sweeps` profile
    /// cuts every pathological source.
    const SAMPLE: Sample = Sample {
        name: SampleName("a_malformed_form_reports_its_parse_error_alone"),
        size: SampleSize(20),
    };

    #[test]
    fn a_malformed_form_reports_its_parse_error_alone()
    {
        let grammar = built_in().expect("the built-in grammar builds");
        let candidates: Vec<_> = gandr_workflow_sweep::corpus::sources()
            .expect("the corpus reads")
            .into_iter()
            .filter(|source| source.name.as_ref().starts_with("fixture/pathological/"))
            .collect();
        let sweep = Sweep::asked().expect("the run's sweep resolves");
        let visited: BTreeSet<_> = sweep
            .visit(SAMPLE, &candidates)
            .into_iter()
            .map(|source| source.path)
            .collect();
        assert!(
            visited.len() >= SAMPLE.size.0,
            "the sample is drawn: {}",
            visited.len()
        );
        let root = gandr_workflow_sweep::corpus::directory()
            .expect("the corpus is checked out beside this crate")
            .join("fixture/pathological");
        let mut repaired = 0_usize;
        let mut severities = Vec::new();
        let ControlFlow::Continue(_report) =
            Walk::new(vec![root]).visit(Width::SERIAL, |step| -> ControlFlow<Infallible> {
                let Step::Source {
                    path, text, base, ..
                } = step
                else {
                    return ControlFlow::Continue(());
                };
                if !visited.contains(path) {
                    return ControlFlow::Continue(());
                }
                let whole = <&str>::from(text)
                    .get(usize::from(base) ..)
                    .expect("an importer's own text starts at its base");
                let cuts = whole
                    .match_indices([' ', '\n'])
                    .map(|(at, _)| at.saturating_add(1_usize))
                    .chain([whole.len()]);
                for cut in cuts {
                    let typed =
                        SourceText::from(whole.get(.. cut).expect("a cut at an ASCII byte"));
                    let Ok(composed) = compose(
                        &grammar,
                        SourceRoot::Fixture.corpus_root(),
                        typed,
                        &mut LoweringCount::default(),
                    )
                    else {
                        continue;
                    };
                    let step = Step::Source {
                        path,
                        root: SourceRoot::Fixture,
                        text: typed,
                        base: gandr_surface_syntax::ByteOffset::from(0_usize),
                        composed,
                        standing: Standing::Unsettled,
                    };
                    let Step::Source {
                        composed: Composed::Settled { ref report, .. },
                        ..
                    } = step
                    else {
                        continue;
                    };
                    let unsettled = || {
                        report
                            .declarations()
                            .iter()
                            .filter(|declaration| declaration.settlement() == Settlement::Unsettled)
                    };
                    severities.clear();
                    severities.extend(
                        entries(&step, Verb::Check(Goals::Gated))
                            .map(|diagnostic| diagnostic.severity)
                            .filter(|&severity| {
                                matches!(severity, Severity::Error | Severity::Note)
                            }),
                    );
                    assert_eq!(
                        severities.len(),
                        unsettled().count(),
                        "one entry per unsettled declaration"
                    );
                    for malformed in unsettled() {
                        if !matches!(
                            malformed.produced().refusal(),
                            Maybe::Present(Refusal::Lowering(LoweringRefusal::MalformedForm {
                                fault: FormFault::Repaired(_),
                                ..
                            }))
                        ) {
                            continue;
                        }
                        repaired = repaired.saturating_add(1_usize);
                        let mut errors = 0_usize;
                        let mut unsupported = false;
                        for (declaration, &severity) in unsettled()
                            .zip(&severities)
                            .filter(|&(declaration, _)| declaration.name() == malformed.name())
                        {
                            if severity == Severity::Error {
                                errors = errors.saturating_add(1_usize);
                            }
                            unsupported |= matches!(
                                declaration.produced().refusal(),
                                Maybe::Present(Refusal::Lowering(
                                    LoweringRefusal::OutOfFragment { .. }
                                ))
                            );
                        }
                        assert_eq!(
                            errors,
                            1_usize,
                            "{} cut at {cut}: `{}` reports its parse error alone",
                            path.display(),
                            malformed.name()
                        );
                        assert!(
                            !unsupported,
                            "{} cut at {cut}: `{}` is malformed, never unsupported",
                            path.display(),
                            malformed.name()
                        );
                    }
                }
                ControlFlow::Continue(())
            });
        assert!(
            repaired > 0_usize,
            "typing the corpus meets malformed forms"
        );
    }
}
