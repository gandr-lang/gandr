//! Trials: candidate revisions judged against a session without submitting
//! any, each as a fresh session judges it, ranked, and the session left as it
//! was.

use core::num::NonZeroUsize;
use std::path::Path;

use anodized::spec;
use gandr_core_incremental::MemoryCheckpointStore;
use gandr_storage_records::InMemoryBlockStore;
use gandr_surface_diagnostics::Verbosity;
use gandr_surface_dispatcher::Goals;
use gandr_surface_dispatcher::SourceRoot;
use gandr_surface_dispatcher::Threads;
use gandr_surface_dispatcher::Verb;
use gandr_surface_dispatcher::Width;
use gandr_surface_dispatcher::entries;
use gandr_surface_render_terminal::RenderStyle;
use gandr_surface_render_terminal::render;
use gandr_surface_session::Session;
use gandr_surface_session::Submission;
use gandr_surface_session::resumed;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use crate::common::session;
use crate::common::submit;

/// The revision every trial starts from: one definition and one declaration
/// owed its body.
const BASE: &str = "def a = 1 ;\ndef f : Integer ;\n";

/// Candidate revisions of [`BASE`], each filling `f` differently, in the
/// order a trial is given them.
const CANDIDATES: [&str; 5] = [
    // A body of the wrong type: `f` is refused.
    "def a = 1 ;\ndef f : Integer ;\ndef f = \"one\" ;\n",
    // A body that checks: every declaration settles.
    "def a = 1 ;\ndef f : Integer ;\ndef f = a ;\n",
    // No body: `f` stays owed.
    "def a = 1 ;\ndef f : Integer ;\n",
    // A revision that declares nothing: the lowering refuses it whole.
    "@[ checks ]\n",
    // The checking body again.
    "def a = 1 ;\ndef f : Integer ;\ndef f = a ;\n",
];

/// What a face shows of a submission: its standing, its parse repairs and
/// every report `check --goals` renders, plainly.
#[repr(transparent)]
#[derive(Debug, Eq, PartialEq)]
struct Shown(String);

/// What a face shows of `submission`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: spells the submission's standing, its completion obligations and
///   each entry `check --goals` gives its step, reports rendered plainly, in
///   order.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the trial witnesses compare candidates whose standings,
///   reports and repairs differ; a field left out would let two of them agree.
/// - witness: `tests::trial::each_candidate_is_judged_as_a_fresh_session_judges_it`
#[spec(ensures: |ret| ret.0.starts_with(&format!("{:?}", submission.standing())))]
fn shown(submission: &Submission<'_>) -> Shown
{
    let mut text = format!(
        "{:?}\n{:?}\n",
        submission.standing(),
        submission.obligations()
    );
    let step = submission.clone().into_step(Path::new("candidate.gandr"));
    for diagnostic in entries(&step, Verb::Check(Goals::Reported)) {
        text.push_str(render(&diagnostic, RenderStyle::Plain, Verbosity::User).as_ref());
        text.push('\n');
    }
    Shown(text)
}

/// A session under the strict root that has accepted [`BASE`], judging on
/// `width`.
///
/// # Specification
/// - requires: [`BASE`] submits without a fault.
/// - ensures: the session's latest accepted revision is [`BASE`].
/// - panics: when [`BASE`] faults.
///
/// # Adequacy
/// - hypothesis: L3 — both trial witnesses start from it at one thread and at
///   several.
/// - witness: `tests::trial::a_trial_leaves_the_session_as_it_was`
#[spec(ensures: |ret| matches!(ret.last(), Maybe::Present(_)))]
fn based(width: Width) -> Session<MemoryCheckpointStore, InMemoryBlockStore>
{
    let mut session = session(SourceRoot::Strict).with_width(width);
    let _base = submit(&mut session, BASE);
    session
}

/// The widths every trial runs at: one thread, and four.
///
/// # Specification
/// trivial.
fn widths() -> [Width; 2]
{
    [
        Width::SERIAL,
        Width::Threads(Threads::from(
            NonZeroUsize::new(4).expect("four is not zero"),
        )),
    ]
}

#[test]
fn each_candidate_is_judged_as_a_fresh_session_judges_it()
{
    let candidates = CANDIDATES.map(SourceText::from);
    for width in widths() {
        let base = based(width);
        let trials = base.trial(&candidates);
        let order: Vec<usize> = trials
            .iter()
            .map(|trial| usize::from(trial.candidate()))
            .collect();
        assert_eq!(
            order,
            [1, 4, 2, 0, 3],
            "settled first, in the candidates' order; then owed; then refused; then refused whole"
        );
        for trial in trials {
            let index = usize::from(trial.candidate());
            let Ok(ref tried) = *trial.outcome()
            else {
                panic!("candidate {index} faulted");
            };
            assert!(
                matches!(tried.resumed(), Maybe::Absent(resumed::Absent::Tried))
                    && matches!(tried.edits(), Maybe::Absent(resumed::Absent::Tried)),
                "a trial resumes nothing and diffs nothing"
            );
            let mut fresh = session(SourceRoot::Strict);
            let judged = fresh
                .judge(candidates[index])
                .expect("a fresh session judges the candidate");
            let handed = trial
                .into_outcome()
                .expect("the candidate's submission is handed on");
            assert_eq!(
                shown(&handed),
                shown(&judged),
                "candidate {index} is judged as a fresh session judges it"
            );
        }
    }
}

#[test]
fn a_trial_leaves_the_session_as_it_was()
{
    let next = "def a = 2 ;\ndef f : Integer ;\ndef f = a ;\n";
    for width in widths() {
        let mut tried = based(width);
        let mut untried = based(width);
        let (snapshot, lowerings) = (tried.snapshot().clone(), tried.lowerings());
        let _trials = tried.trial(&CANDIDATES.map(SourceText::from));
        assert_eq!(
            (tried.snapshot(), tried.lowerings()),
            (&snapshot, lowerings),
            "the trial changes neither the snapshot nor the lowering count"
        );
        let after = submit(&mut tried, next);
        let plain = submit(&mut untried, next);
        assert_eq!(
            (after.forms(), after.resumed(), after.edits()),
            (plain.forms(), plain.resumed(), plain.edits()),
            "the next submission molds, resumes and diffs as if no trial ran"
        );
        assert_eq!(shown(&after), shown(&plain));
    }
}
