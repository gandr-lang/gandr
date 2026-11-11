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
//! The command takes what the run reads while the workspace is locked
//! ([`Prepared`]): the copy's session and the closure its latest recheck laid
//! out, both shared, its text, and the constant the table names. The run then
//! goes on the hub's pool with no lock of the workspace. It holds the copy's
//! session for one judgement of the text over that closure — a text the
//! session last judged judges no item — and runs the declaration with no lock
//! at all ([`Submission::evaluate`]): the run is the program's own, under its
//! own budget, so a run that stops short of a value shows the line that names
//! why. A keystroke during a run thus waits for no part of it.
//!
//! [`TypeTable::runs`]: gandr_surface_dispatcher::TypeTable::runs
//! [`Submission::evaluate`]: gandr_surface_session::Submission::evaluate

use alloc::format;
use alloc::string::String;
use alloc::sync::Arc;
use alloc::vec::Vec;
use core::fmt;
use std::sync::Mutex;

use anodized::spec;
use gandr_kernel_term::ConstantIndex;
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
use crate::protocol::DocumentVersion;
use crate::protocol::MessageType;
use crate::recheck::DocumentSession;
use crate::server::locked;

/// Why a run shows no line.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Unran
{
    /// The hub holds no copy of the document, so nothing in it runs.
    Unheld,
    /// No declaration that runs is named at the position: the document
    /// changed since the lens was offered.
    Unnamed,
    /// The declaration did not reach a run: why, as a sentence.
    Declined(String),
}

impl fmt::Display for Unran
{
    /// Write why the run shows no line, as one sentence.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::Unheld => f.write_str("the document is not open, so nothing in it runs"),
            Self::Unnamed => f.write_str(
                "nothing that runs is named there: the document changed since the lens was offered",
            ),
            Self::Declined(ref why) => f.write_str(why),
        }
    }
}

/// What a run of one declaration reads, taken while the workspace is locked.
///
/// It shares the copy's session and the closure its latest recheck laid out,
/// and it copies the text, the version and the constant of the declaration.
///
/// # Specification
/// - provides: a run of the declaration with no lock of the workspace
///   ([`Prepared::run`]).
/// - panics: none.
/// - executable: none — a value; [`taken`] and [`Prepared::run`] carry the
///   clauses.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Prepared::run`].
/// - witness: `server::tests::a_run_lens_runs_its_declaration_1818`
#[derive(Debug)]
pub struct Prepared
{
    /// The copy's session, which the run holds for its judgement alone.
    session: Arc<Mutex<DocumentSession>>,
    /// The copy's text.
    text: String,
    /// The closure the text is judged over, or why it is judged alone.
    laid: Arc<Maybe<Laid, laid::Absent>>,
    /// The constant of the declaration that runs.
    constant: ConstantIndex,
    /// The version of the copy.
    version: DocumentVersion,
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

/// What a run of the declaration named at `position` of `text` reads, from
/// a copy at `version` that keeps `hovering`, whose session is `session` and
/// whose text is laid out as `laid`.
///
/// # Specification
/// - requires: `hovering` holds the type table of `text`; `laid` is the lay-out
///   of `text` its latest recheck judged, or the one a recheck would make now.
/// - ensures: [`Unran::Unnamed`] when no run the table answers is named at the
///   position, a position just past the name included. Otherwise a run of the
///   constant the table names, which shares `session` and `laid` and owns a
///   copy of `text`.
/// - provides: the half of a run that the lock of the workspace covers.
/// - fails: [`Unran::Unnamed`] only.
/// - panics: none.
///
/// # Errors
/// [`Unran::Unnamed`] when nothing that runs is named at the position.
///
/// # Adequacy
/// - hypothesis: L3 — a position naming nothing that runs is unnamed, and a
///   value runs from just past its name.
/// - witness: `server::tests::a_run_lens_runs_its_declaration_1818`
#[spec(ensures: |ret| matches!(ret, Ok(_) | Err(Unran::Unnamed)))]
pub fn taken(
    (session, laid): (&Arc<Mutex<DocumentSession>>, Arc<Maybe<Laid, laid::Absent>>),
    (text, version): (SourceText<'_>, DocumentVersion),
    hovering: &Hovering,
    position: Position,
) -> Result<Prepared, Unran>
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
    Ok(Prepared {
        session: Arc::clone(session),
        text: String::from(<&str>::from(text)),
        laid,
        constant,
        version,
    })
}

impl Prepared
{
    /// The version of the copy the run reads.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn version(&self) -> DocumentVersion
    {
        self.version
    }

    /// What the run shows: how the line reads, and the line `gandr run`
    /// prints of the run.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the text is judged again over its closure — alone when it is
    ///   laid out alone — while the copy's session is held, and the session is
    ///   let go before the declaration is evaluated at its constant. A value, a
    ///   sealed one among them, reads as information and any other evaluation
    ///   as a warning, beside its [`Evaluation`]'s one spelling; a session
    ///   whose grammar did not build, a judgement that faulted, an owed
    ///   declaration and one the checker did not accept each decline with a
    ///   sentence naming why.
    /// - provides: the run lens's command and the toolset's `run`, off the lock
    ///   of the workspace.
    /// - fails: every refusal is an [`Unran::Declined`].
    /// - panics: none.
    ///
    /// # Errors
    /// [`Unran::Declined`] when the declaration does not reach a run.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a value and a nullary computation run to their lines,
    ///   a run that reaches a hole is a warning, and an owed declaration
    ///   declines.
    /// - witness: `server::tests::a_run_lens_runs_its_declaration_1818`
    #[spec(ensures: |ret| match ret {
        Ok((kind, ref line)) => (kind == MessageType::INFO || kind == MessageType::WARNING) && !line.is_empty(),
        Err(Unran::Declined(ref why)) => !why.is_empty(),
        Err(Unran::Unheld | Unran::Unnamed) => false,
    })]
    #[inline]
    pub fn run(&self) -> Result<(MessageType, String), Unran>
    {
        let slot = ClosureSlot::new();
        let mut held = locked(&self.session);
        let Ok(ref mut session) = *held
        else {
            return Err(Unran::Declined(String::from(
                "gandr's grammar did not build, so nothing runs",
            )));
        };
        let judged = match *self.laid {
            Maybe::Present(ref laid) => session.judge_unit_reading(
                SourceText::from(laid.text.as_str()),
                &laid.unit,
                laid.base,
                &slot,
                |_tree| {},
            ),
            Maybe::Absent(_) => session.judge(SourceText::from(self.text.as_str())),
        };
        let judged = judged.map_err(|fault| {
            Unran::Declined(format!(
                "the document did not judge, so nothing runs: {fault}"
            ))
        });
        // The submission owns what the judgement made, so the run holds the
        // session no longer than its judgement.
        drop(held);
        let mut submission = judged?;
        match submission.evaluate(self.constant) {
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
}
