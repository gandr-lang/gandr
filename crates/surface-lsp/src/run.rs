//! Runs: a lens over each declaration of an open document that runs applied
//! to nothing, and the command it names, which runs the declaration as `gandr
//! run` does and shows the line `gandr run` prints.
//!
//! Where a run starts is the type table's ([`TypeTable::runs`]): a declaration
//! the document names, read whole and not refused by the checker, whose type
//! is a value that takes no argument and is no type. The lens decides it from
//! the declared type rather than from the outline's role, which does not
//! separate `def f()` from `def f(x)`, nor from the verdict, which the table
//! does not read: a declaration the checker owes for a hole it waits on stands
//! a lens, and its run declines.
//!
//! The command judges the document's text again, over the closure its latest
//! recheck laid out — a text the session last judged judges no item — and runs
//! the declaration at the constant the table names
//! ([`Submission::evaluate`]): the run is the program's own, under its own
//! budget, so a run that stops short of a value shows the line that names
//! why.
//!
//! [`TypeTable::runs`]: gandr_surface_dispatcher::TypeTable::runs
//! [`Submission::evaluate`]: gandr_surface_session::Submission::evaluate

use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;

use anodized::spec;
use gandr_surface_dispatcher::Evaluation;
use gandr_surface_dispatcher::Laid;
use gandr_surface_dispatcher::laid;
use gandr_surface_render_remote::LineIndex;
use gandr_surface_session::ClosureSlot;
use gandr_surface_session::evaluation;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use crate::goto::ranged;
use crate::hover::Hovering;
use crate::position::Position;
use crate::position::Range;
use crate::protocol::MessageType;
use crate::recheck::DocumentSession;

/// Why a run lens's command shows no line.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Unran
{
    /// No declaration that runs is named at the position: the document
    /// changed since the lens was offered.
    Unnamed,
    /// The declaration did not reach a run: why, as a sentence.
    Declined(String),
}

/// The ranges of the names of the declarations of `text`, whose copy keeps
/// `hovering`, that a run can start at, ascending.
///
/// # Specification
/// - requires: `hovering` holds the type table of `text`.
/// - ensures: one range per run the table answers, in its order, which is
///   ascending; none for a name whose span has no range.
/// - provides: where a run lens stands.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a value and a computation applied to nothing each stand a
///   lens, and a function, a type and a family none.
/// - witness: `server::tests::a_run_lens_runs_its_declaration_1818`
#[spec(ensures: |ret| ret.is_sorted() && ret.len() <= hovering.table().runs().len())]
#[must_use]
pub fn runs(
    text: SourceText<'_>,
    hovering: &Hovering,
) -> Vec<Range>
{
    let index = LineIndex::new(<&str>::from(text).into());
    hovering
        .table()
        .runs()
        .iter()
        .filter_map(|&(referent, _)| ranged(&index, referent.named()))
        .collect()
}

/// What running the declaration named at `position` of `text`, whose copy
/// keeps `hovering` and which `session` judges laid out as `laid`, shows: how
/// the line reads, and the line `gandr run` prints of the run.
///
/// # Specification
/// - requires: `hovering` holds the type table of `text`; `laid` is the lay-out
///   of `text` its latest recheck judged, or the one a recheck would make now.
/// - ensures: [`Unran::Unnamed`] when no run the table answers is named at the
///   position, a position just past the name included. Otherwise `text` is
///   judged again over `laid` — alone when it is laid out alone — and the
///   declaration evaluated at the constant the table names: a value, a sealed
///   one among them, reads as information and any other evaluation as a
///   warning, beside its [`Evaluation`]'s one spelling; a session whose grammar
///   did not build, a judgement that faulted, an owed declaration and one the
///   checker did not accept each decline with a sentence naming why.
/// - provides: the run lens's command.
/// - fails: every refusal is an [`Unran`].
/// - panics: none.
///
/// # Errors
/// [`Unran::Unnamed`] when nothing that runs is named at the position, and
/// [`Unran::Declined`] when the declaration does not reach a run.
///
/// # Adequacy
/// - hypothesis: L3 — a value and a nullary computation run to their lines, a
///   run that reaches a hole is a warning, an owed declaration declines, and a
///   position naming nothing that runs is unnamed.
/// - witness: `server::tests::a_run_lens_runs_its_declaration_1818`
#[spec(ensures: |ret| match ret {
    Ok((kind, ref line)) => (kind == MessageType::INFO || kind == MessageType::WARNING) && !line.is_empty(),
    Err(Unran::Unnamed) => true,
    Err(Unran::Declined(ref why)) => !why.is_empty(),
})]
pub fn run(
    session: &mut DocumentSession,
    (text, laid): (SourceText<'_>, &Maybe<Laid, laid::Absent>),
    hovering: &Hovering,
    position: Position,
) -> Result<(MessageType, String), Unran>
{
    let index = LineIndex::new(<&str>::from(text).into());
    let at = ByteOffset::from(usize::from(position.byte(&index)));
    let Some(&(_, constant)) = hovering.table().runs().iter().find(|&&(referent, _)| {
        let named = referent.named();
        named.start() <= at && at <= named.end()
    })
    else {
        return Err(Unran::Unnamed);
    };
    let Ok(ref mut session) = *session
    else {
        return Err(Unran::Declined(String::from(
            "gandr's grammar did not build, so nothing runs",
        )));
    };
    let slot = ClosureSlot::new();
    let judged = match *laid {
        Maybe::Present(ref laid) => session.judge_unit_reading(
            SourceText::from(laid.text.as_str()),
            &laid.unit,
            laid.base,
            &slot,
            |_tree| {},
        ),
        Maybe::Absent(_) => session.judge(text),
    };
    let mut submission = judged.map_err(|fault| {
        Unran::Declined(format!(
            "the document did not judge, so nothing runs: {fault}"
        ))
    })?;
    match submission.evaluate(constant) {
        Maybe::Present(evaluation) => Ok((
            match evaluation {
                Evaluation::Value(_) | Evaluation::Sealed(_) => MessageType::INFO,
                Evaluation::Blamed(_)
                | Evaluation::Holed { .. }
                | Evaluation::Stuck(_)
                | Evaluation::Unfinished(_)
                | Evaluation::Unrunnable(_) => MessageType::WARNING,
            },
            evaluation.to_string(),
        )),
        Maybe::Absent(evaluation::Absent::Holed) => Err(Unran::Declined(String::from(
            "the declaration is owed a hole, so it does not run",
        ))),
        Maybe::Absent(evaluation::Absent::Unaccepted) => Err(Unran::Declined(String::from(
            "the checker did not accept the declaration, so it does not run",
        ))),
    }
}
