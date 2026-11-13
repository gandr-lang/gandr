//! The handlers of five navigation requests, generic over the workspace that
//! they ask: highlights, linked editing, inlay hints, the resolution of an
//! inlay hint and the copied sources.
//!
//! Each handler asks the workspace for one copy through
//! [`Context::view`], and reads the copy through [`Held`]. The server
//! implements both traits and calls each handler, so each handler compiles
//! in the server, for the server's workspace.

use gandr_surface_lsp_base::peer::Peer;
use gandr_surface_lsp_core::context::Context;
use gandr_surface_lsp_core::context::Held;
use gandr_surface_render_remote::LineIndex;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;

use crate::inlay::hint_at;
use crate::inlay::hints;
use crate::paste::copied;
use crate::position::Position;
use crate::position::Range;
use crate::protocol::Answer;
use crate::protocol::DocumentUri;
use crate::protocol::InlayHint;
use crate::protocol::ResolvesHintLocations;
use crate::uses::highlights;
use crate::uses::mirrored;

/// What a highlight request at `position` of the copy of the document at
/// `uri` that `peer` is answered from answers.
///
/// # Specification
/// - requires: nothing; an unknown URI and any position are admitted.
/// - ensures: an unknown document, and one whose session holds no grammar,
///   yields Nothing; otherwise the highlights [`highlights`] answers off the
///   copy's text and what it keeps for its hovers.
/// - fails: never.
/// - panics: none.
#[inline]
pub fn highlight<Workspace>(
    workspace: &Workspace,
    uri: &DocumentUri,
    peer: Peer,
    position: Position,
) -> Answer
where
    Workspace: Context,
{
    let Some(copy) = workspace.view(uri, peer)
    else {
        return Answer::Nothing;
    };
    copy.hovering().map_or(Answer::Nothing, |hovering| {
        highlights(copy.source(), hovering, position)
    })
}

/// What a linked-editing request at `position` of the copy of the document
/// at `uri` that `peer` is answered from answers.
///
/// # Specification
/// - requires: nothing; an unknown URI and any position are admitted.
/// - ensures: an unknown document, and one whose session holds no grammar,
///   yields Nothing; otherwise what [`mirrored`] answers off the copy's text
///   and what it keeps for its hovers.
/// - fails: never.
/// - panics: none.
#[inline]
pub fn linked_editing<Workspace>(
    workspace: &Workspace,
    uri: &DocumentUri,
    peer: Peer,
    position: Position,
) -> Answer
where
    Workspace: Context,
{
    let Some(copy) = workspace.view(uri, peer)
    else {
        return Answer::Nothing;
    };
    copy.hovering().map_or(Answer::Nothing, |hovering| {
        mirrored(copy.source(), hovering, position)
    })
}

/// The inlay hints over `range` of the copy of the document at `uri` that
/// `peer` is answered from, each type spelled in `style`, each label's
/// locations left to a resolution when `deferring` holds.
///
/// # Specification
/// - requires: nothing; an unknown URI and any range are admitted.
/// - ensures: an unknown document yields Nothing; a held document whose session
///   did not build, and an empty or inverted range, yield no hint; otherwise
///   the hints [`hints`] answers over the range.
/// - fails: never.
/// - panics: none.
#[inline]
pub fn inlay_hints<Workspace>(
    workspace: &Workspace,
    uri: &DocumentUri,
    peer: Peer,
    range: Range,
    (style, deferring): (gandr_surface_pretty::Style, ResolvesHintLocations),
) -> Answer
where
    Workspace: Context,
{
    let Some(copy) = workspace.view(uri, peer)
    else {
        return Answer::Nothing;
    };
    let index = LineIndex::new(<&str>::from(copy.source()).into());
    let window = ByteSpan::new(
        ByteOffset::from(usize::from(range.start.byte(&index))),
        ByteOffset::from(usize::from(range.end.byte(&index))),
    );
    Answer::Hints(match (copy.hovering(), window) {
        (Some(hovering), Ok(window)) if window.start() < window.end() => hints(
            (hovering, copy.reading().tiles()),
            (uri, &index),
            window,
            (style, deferring),
        ),
        (Some(_) | None, Ok(_) | Err(_)) => Vec::new(),
    })
}

/// The inlay hint drawn at `position` of the copy of the document at `uri`
/// that `peer` is answered from, its type spelled in `style` and every name
/// its label writes located.
///
/// # Specification
/// - requires: nothing; an unknown URI and any position are admitted.
/// - ensures: none for an unknown document or one whose session did not build;
///   otherwise what [`hint_at`] answers at `position`.
/// - fails: never.
/// - panics: none.
#[inline]
pub fn resolve_hint<Workspace>(
    workspace: &Workspace,
    uri: &DocumentUri,
    peer: Peer,
    position: Position,
    style: gandr_surface_pretty::Style,
) -> Option<InlayHint>
where
    Workspace: Context,
{
    let copy = workspace.view(uri, peer)?;
    let hovering = copy.hovering()?;
    let index = LineIndex::new(<&str>::from(copy.source()).into());
    hint_at(
        (hovering, copy.reading().tiles()),
        (uri, &index),
        position,
        style,
    )
}

/// The sources declaring what `ranges` of the copy of the document at `uri`
/// that `peer` is answered from name.
///
/// # Specification
/// - requires: nothing; an unknown URI and any ranges are admitted.
/// - ensures: an unknown document yields Nothing; a held document whose session
///   did not build yields none; otherwise the sources [`copied`] answers over
///   the ranges.
/// - fails: never.
/// - panics: none.
#[inline]
pub fn copied_sources<Workspace>(
    workspace: &Workspace,
    uri: &DocumentUri,
    peer: Peer,
    ranges: &[Range],
) -> Answer
where
    Workspace: Context,
{
    let Some(copy) = workspace.view(uri, peer)
    else {
        return Answer::Nothing;
    };
    let index = LineIndex::new(<&str>::from(copy.source()).into());
    Answer::Sources(
        copy.hovering()
            .map_or_else(Vec::new, |hovering| copied(hovering, (uri, &index), ranges)),
    )
}
