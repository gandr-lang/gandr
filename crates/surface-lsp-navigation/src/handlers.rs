//! The handlers of five navigation requests: highlights, linked editing,
//! inlay hints, the resolution of an inlay hint and the copied sources.
//!
//! Each handler is a thin generic shim of one statement. It asks the
//! workspace for one copy through [`Context::view`], reads the parts of the
//! copy that its body needs through [`Held`], and forwards them to a body
//! with no generic parameter. So only the shims compile in the server, and
//! each body compiles once, in this crate.

use gandr_surface_lsp_base::peer::Peer;
use gandr_surface_lsp_core::context::Context;
use gandr_surface_lsp_core::context::Held;
use gandr_surface_lsp_core::hover::Hovering;
use gandr_surface_lsp_core::reading::Reading;
use gandr_surface_render_remote::LineIndex;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::SourceText;

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
/// - ensures: as [`highlight_in`], over the copy's text and what it keeps for
///   its hovers.
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
    highlight_in(
        workspace
            .view(uri, peer)
            .as_ref()
            .map(|copy| (copy.source(), copy.hovering())),
        position,
    )
}

/// What a highlight request at `position` answers, over `copy`: none when
/// no copy is held, and the copy's text with what its hovers read otherwise.
///
/// # Specification
/// - requires: nothing.
/// - ensures: Nothing with no copy and with no hovering; otherwise the
///   highlights [`highlights`] answers.
/// - fails: never.
/// - panics: none.
#[must_use]
pub fn highlight_in(
    copy: Option<(SourceText<'_>, Option<&Hovering>)>,
    position: Position,
) -> Answer
{
    let Some((source, hovering)) = copy
    else {
        return Answer::Nothing;
    };
    hovering.map_or(Answer::Nothing, |hovering| {
        highlights(source, hovering, position)
    })
}

/// What a linked-editing request at `position` of the copy of the document
/// at `uri` that `peer` is answered from answers.
///
/// # Specification
/// - requires: nothing; an unknown URI and any position are admitted.
/// - ensures: as [`linked_editing_in`], over the copy's text and what it keeps
///   for its hovers.
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
    linked_editing_in(
        workspace
            .view(uri, peer)
            .as_ref()
            .map(|copy| (copy.source(), copy.hovering())),
        position,
    )
}

/// What a linked-editing request at `position` answers, over `copy`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: Nothing with no copy and with no hovering; otherwise what
///   [`mirrored`] answers.
/// - fails: never.
/// - panics: none.
#[must_use]
pub fn linked_editing_in(
    copy: Option<(SourceText<'_>, Option<&Hovering>)>,
    position: Position,
) -> Answer
{
    let Some((source, hovering)) = copy
    else {
        return Answer::Nothing;
    };
    hovering.map_or(Answer::Nothing, |hovering| {
        mirrored(source, hovering, position)
    })
}

/// The inlay hints over `range` of the copy of the document at `uri` that
/// `peer` is answered from, each type spelled in `style`, each label's
/// locations left to a resolution when `deferring` holds.
///
/// # Specification
/// - requires: nothing; an unknown URI and any range are admitted.
/// - ensures: as [`inlay_hints_in`], over the copy's text, what it keeps for
///   its hovers and its reading.
/// - fails: never.
/// - panics: none.
#[inline]
pub fn inlay_hints<Workspace>(
    workspace: &Workspace,
    uri: &DocumentUri,
    peer: Peer,
    range: Range,
    shape: (gandr_surface_pretty::Style, ResolvesHintLocations),
) -> Answer
where
    Workspace: Context,
{
    inlay_hints_in(
        workspace.view(uri, peer).as_ref().map(|copy| {
            (
                copy.source(),
                copy.hovering().map(|hovering| (hovering, copy.reading())),
            )
        }),
        uri,
        range,
        shape,
    )
}

/// The inlay hints over `range` of `copy`, the copy of the document at
/// `uri`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: Nothing with no copy; no hint with no hovering, and over an empty
///   or inverted range; otherwise the hints [`hints`] answers over the range.
/// - fails: never.
/// - panics: none.
#[must_use]
pub fn inlay_hints_in(
    copy: Option<(SourceText<'_>, Option<(&Hovering, &Reading)>)>,
    uri: &DocumentUri,
    range: Range,
    (style, deferring): (gandr_surface_pretty::Style, ResolvesHintLocations),
) -> Answer
{
    let Some((source, read)) = copy
    else {
        return Answer::Nothing;
    };
    let index = LineIndex::new(<&str>::from(source).into());
    let window = ByteSpan::new(
        ByteOffset::from(usize::from(range.start.byte(&index))),
        ByteOffset::from(usize::from(range.end.byte(&index))),
    );
    Answer::Hints(match (read, window) {
        (Some((hovering, reading)), Ok(window)) if window.start() < window.end() => hints(
            (hovering, reading.tiles()),
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
/// - ensures: as [`resolve_hint_in`], over the copy's text, what it keeps for
///   its hovers and its reading.
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
    resolve_hint_in(
        workspace
            .view(uri, peer)
            .as_ref()
            .and_then(|copy| Some((copy.source(), copy.hovering()?, copy.reading()))),
        uri,
        position,
        style,
    )
}

/// The inlay hint drawn at `position` of `copy`, the copy of the document
/// at `uri`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: none with no copy; otherwise what [`hint_at`] answers.
/// - fails: never.
/// - panics: none.
#[must_use]
pub fn resolve_hint_in(
    copy: Option<(SourceText<'_>, &Hovering, &Reading)>,
    uri: &DocumentUri,
    position: Position,
    style: gandr_surface_pretty::Style,
) -> Option<InlayHint>
{
    let (source, hovering, reading) = copy?;
    let index = LineIndex::new(<&str>::from(source).into());
    hint_at((hovering, reading.tiles()), (uri, &index), position, style)
}

/// The sources declaring what `ranges` of the copy of the document at `uri`
/// that `peer` is answered from name.
///
/// # Specification
/// - requires: nothing; an unknown URI and any ranges are admitted.
/// - ensures: as [`copied_sources_in`], over what the copy keeps for its
///   hovers.
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
    copied_sources_in(
        workspace
            .view(uri, peer)
            .as_ref()
            .map(|copy| (copy.source(), copy.hovering())),
        uri,
        ranges,
    )
}

/// The sources declaring what `ranges` of `copy`, the copy of the document
/// at `uri`, name.
///
/// # Specification
/// - requires: nothing.
/// - ensures: Nothing with no copy; none with no hovering; otherwise the
///   sources [`copied`] answers over the ranges.
/// - fails: never.
/// - panics: none.
#[must_use]
pub fn copied_sources_in(
    copy: Option<(SourceText<'_>, Option<&Hovering>)>,
    uri: &DocumentUri,
    ranges: &[Range],
) -> Answer
{
    let Some((source, hovering)) = copy
    else {
        return Answer::Nothing;
    };
    let index = LineIndex::new(<&str>::from(source).into());
    Answer::Sources(
        hovering.map_or_else(Vec::new, |hovering| copied(hovering, (uri, &index), ranges)),
    )
}
