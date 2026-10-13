//! Model proposals: fills a model offers for a range of an open document,
//! kept once they check and withdrawn by the document's next edit.
//!
//! The server never calls a model. A model hands a proposal to the hub, the
//! hub judges it as a trial of the document with the fill applied, and only a
//! fill that checks is kept beside the document. The editor then reads the
//! kept proposals through four surfaces: ghost text at the cursor, a lens
//! counting the checked fills of a range, an action applying one, and a hover
//! carrying the model's explanation.
//!
//! # Model proposals reach the editor once they check
//!
//! **Choice.** The server never calls a model. A model hands a fill of a range
//! to the hub (`Workspace::propose`, the Model Context Protocol server's
//! `propose` tool), naming the version it read. The hub refuses a version the
//! document has moved past, tries the document with the fill applied as a trial
//! does, and keeps the fill beside the document only when it checks: the trial
//! judged the filled document and it carries no error, or fewer errors than the
//! document's published diagnostics. A kept proposal reaches the editor four
//! ways — ghost text at a cursor inside its range, ahead of the parser's
//! expected syntax; a code lens over its range counting the checked fills
//! there; a quick-fix code action replacing the range; and, when the model
//! explained it, a note under the hover. The document's next synchronisation,
//! whatever it changes, withdraws every proposal kept for it. The document's
//! text, session and published diagnostics are never touched by a proposal.
//!
//! **Alternatives.** Keeping a proposal whose fill leaves the document no worse
//! would show fills that do nothing; requiring the filled document to carry no
//! error at all would keep nothing in a document with an unrelated refusal
//! elsewhere. Moving a kept proposal's range through an edit, rather than
//! withdrawing it, would show a fill checked against a text that no longer
//! exists. Pushing `workspace/codeLens/refresh` to the editors when a proposal
//! is kept would show the lens at once, at the cost of a server-to-client
//! request the relay and every client must answer; the editor asks for lenses
//! again on its own triggers, and ghost text and actions are pulled at the
//! cursor. Lenses run no command: applying a fill is the code action's, and a
//! lens command would need a client command the extension registers.
//!
//! **Reversal.** A proposal that should survive an edit far from its range
//! moves with the edit and is checked again; an editor measured to show stale
//! lenses for long gets the refresh request.

use alloc::collections::BTreeMap;
use alloc::string::String;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;

use crate::position::Position;
use crate::position::Range;
use crate::protocol::CodeAction;
use crate::protocol::CodeLens;
use crate::protocol::Command;
use crate::protocol::Diagnostic;
use crate::protocol::DocumentUri;
use crate::protocol::DocumentVersion;
use crate::protocol::InlineCompletionItem;
use crate::protocol::Severity;
use crate::protocol::StringValue;
use crate::protocol::TextEdit;
use crate::protocol::WorkspaceEdit;
use crate::recheck::Reached;
use crate::recheck::Tried;

/// A fill a model proposed and gandr checked: the text replacing a range of
/// the document at the version it was checked against.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Proposal
{
    /// The range the text replaces.
    pub range: Range,
    /// The text replacing it.
    pub text: String,
    /// What the model says the fill does, when it said anything.
    pub explanation: Option<String>,
}

/// Why a proposal was not kept.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ProposalRefusal
{
    /// No connection holds the document open.
    NotHeld,
    /// The proposal names a version the document has moved past.
    Stale
    {
        /// The version the document is at.
        held: DocumentVersion,
    },
    /// The fill does not check: the diagnostics its trial published.
    Unchecked
    {
        /// What the trial of the document with the fill applied published.
        diagnostics: Vec<Diagnostic>,
    },
}

impl fmt::Display for ProposalRefusal
{
    /// Say why the proposal was not kept.
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
            | Self::NotHeld => f.write_str("the document is not open in the hub"),
            | Self::Stale { held } => write!(f, "the document is at version {held}"),
            | Self::Unchecked { ref diagnostics } => write!(
                f,
                "the fill does not check: {} error(s)",
                errors(diagnostics)
            ),
        }
    }
}

/// How many errors a set of diagnostics carries.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
struct ErrorCount(usize);

impl fmt::Display for ErrorCount
{
    /// Write the count.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        self.0.fmt(f)
    }
}

/// How many of `diagnostics` are errors.
///
/// # Specification
/// trivial.
fn errors(diagnostics: &[Diagnostic]) -> ErrorCount
{
    ErrorCount(
        diagnostics
            .iter()
            .filter(|diagnostic| diagnostic.severity == Severity::ERROR)
            .count(),
    )
}

/// The diagnostics of `tried`, the trial of a fill, when it checks against a
/// document whose published diagnostics are `published`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the trial's diagnostics exactly when it judged the filled
///   document and they carry no error, or fewer errors than `published`: a fill
///   that settles a hole adds none, and a fill that repairs one refusal of
///   several removes one. A fill refused whole or faulted never checks, and is
///   refused as [`ProposalRefusal::Unchecked`] with its trial's diagnostics.
/// - provides: the gate every proposal passes before the editor sees it.
/// - fails: [`ProposalRefusal::Unchecked`] for a fill that does not check.
/// - panics: none.
///
/// # Errors
/// [`ProposalRefusal::Unchecked`] for a fill that does not check.
///
/// # Adequacy
/// - hypothesis: L3 — a fill that settles the document, one that leaves its
///   refusal, and one refused whole are kept, refused and refused.
/// - witness: `server::tests::a_proposal_is_kept_only_once_it_checks`
#[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|kept| {
    let after = errors(kept);
    after == ErrorCount::default() || after < errors(published)
}))]
pub fn check(
    tried: Tried,
    published: &[Diagnostic],
) -> Result<Vec<Diagnostic>, ProposalRefusal>
{
    let after = errors(&tried.diagnostics);
    if tried.reached == Reached::Judged
        && (after == ErrorCount::default() || after < errors(published))
    {
        Ok(tried.diagnostics)
    }
    else {
        Err(ProposalRefusal::Unchecked {
            diagnostics: tried.diagnostics,
        })
    }
}

/// The proposals of `proposals` whose range holds `position`, its ends
/// included, in the order kept.
///
/// # Specification
/// trivial.
fn holding(
    proposals: &[Proposal],
    position: Position,
) -> impl Iterator<Item = &Proposal>
{
    proposals
        .iter()
        .filter(move |proposal| proposal.range.start <= position && position <= proposal.range.end)
}

/// The text of `proposal` escaped for the protocol's snippet syntax: every
/// `\`, `$` and `}` read as itself.
///
/// # Specification
/// trivial.
fn snippet(proposal: &Proposal) -> String
{
    let mut escaped = String::with_capacity(proposal.text.len());
    for character in proposal.text.chars() {
        if matches!(character, '\\' | '$' | '}') {
            escaped.push('\\');
        }
        escaped.push(character);
    }
    escaped
}

/// The ghost text of each of `proposals` whose range holds `position`: its
/// text replacing its range.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one item per proposal whose range holds the position, in the
///   order kept, each replacing that proposal's range with its text escaped as
///   a snippet.
/// - provides: the proposals' share of `textDocument/inlineCompletion`.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a cursor inside a proposal's range sees it before the
///   parser's expected syntax, and one outside sees only the latter.
/// - witness: `server::tests::kept_proposals_reach_every_editor_surface`
#[spec(ensures: |ret| ret.len() <= proposals.len()
    && ret.iter().all(|item| item.range.start <= position && position <= item.range.end))]
#[must_use]
pub fn ghosts(
    proposals: &[Proposal],
    position: Position,
) -> Vec<InlineCompletionItem>
{
    holding(proposals, position)
        .map(|proposal| InlineCompletionItem {
            insert_text: StringValue {
                kind: "snippet",
                value: snippet(proposal),
            },
            range: proposal.range,
        })
        .collect()
}

/// One lens per range `proposals` fill, counting its checked fills.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one lens per distinct range, in range order, titled with the
///   number of proposals for it; the lens runs no command.
/// - provides: the answer to `textDocument/codeLens`.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — two proposals for one range and one for another show two
///   lenses counting two and one.
/// - witness: `server::tests::kept_proposals_reach_every_editor_surface`
#[spec(ensures: |ret| ret.len() <= proposals.len()
    && ret.is_sorted_by(|earlier, later| earlier.range < later.range))]
#[must_use]
pub fn lenses(proposals: &[Proposal]) -> Vec<CodeLens>
{
    let mut counts: BTreeMap<Range, usize> = BTreeMap::new();
    for proposal in proposals {
        let count = counts.entry(proposal.range).or_default();
        *count = count.saturating_add(1);
    }
    counts
        .into_iter()
        .map(|(range, count)| CodeLens {
            range,
            command: Command {
                title: if count == 1 {
                    String::from("1 checked fill")
                }
                else {
                    alloc::format!("{count} checked fills")
                },
                command: "",
            },
        })
        .collect()
}

/// One action per proposal of the document at `uri` whose range meets
/// `asked`: the edit applying it.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one quick fix per proposal whose range meets the asked range
///   (neither ends before the other starts), in the order kept, each the one
///   edit replacing that proposal's range with its text.
/// - provides: the answer to `textDocument/codeAction`.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a range over a proposal offers its edit; a range
///   elsewhere offers nothing.
/// - witness: `server::tests::kept_proposals_reach_every_editor_surface`
#[spec(ensures: |ret| ret.len() <= proposals.len()
    && ret.iter().all(|action| action.kind == "quickfix" && action.edit.changes.len() == 1))]
#[must_use]
pub fn actions(
    uri: &DocumentUri,
    proposals: &[Proposal],
    asked: Range,
) -> Vec<CodeAction>
{
    proposals
        .iter()
        .filter(|proposal| proposal.range.start <= asked.end && asked.start <= proposal.range.end)
        .map(|proposal| CodeAction {
            title: alloc::format!(
                "Apply the checked fill `{}`",
                proposal.text.lines().next().unwrap_or_default()
            ),
            kind: "quickfix",
            edit: WorkspaceEdit {
                changes: BTreeMap::from([(
                    uri.clone(),
                    Vec::from([TextEdit {
                        range: proposal.range,
                        new_text: proposal.text.clone(),
                    }]),
                )]),
            },
        })
        .collect()
}

/// The notes of each of `proposals` whose range holds `position` and that
/// carries an explanation, as markdown, and the range of the first.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `None` when no proposal at the position explains itself;
///   otherwise one paragraph per such proposal, its fill then its explanation,
///   and the first one's range.
/// - provides: the proposals' share of `textDocument/hover`.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a hover inside an explained proposal carries its note,
///   beside a declaration's type or alone.
/// - witness: `server::tests::kept_proposals_reach_every_editor_surface`
#[spec(ensures: |ret| ret.as_ref().is_none_or(|&(range, _)|
    range.start <= position && position <= range.end))]
#[must_use]
pub fn notes(
    proposals: &[Proposal],
    position: Position,
) -> Option<(Range, String)>
{
    let mut explained =
        holding(proposals, position).filter(|proposal| proposal.explanation.is_some());
    let first = explained.next()?;
    let mut markdown = note(first);
    for proposal in explained {
        markdown.push_str("\n\n");
        markdown.push_str(&note(proposal));
    }
    Some((first.range, markdown))
}

/// The note of `proposal`: its fill's first line, then its explanation.
///
/// # Specification
/// trivial.
fn note(proposal: &Proposal) -> String
{
    alloc::format!(
        "**Checked fill** `{}`: {}",
        proposal.text.lines().next().unwrap_or_default(),
        proposal.explanation.as_deref().unwrap_or_default()
    )
}
