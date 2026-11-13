//! The handlers of five navigation requests: highlights, linked editing,
//! inlay hints, the resolution of an inlay hint and the copied sources.
//!
//! Each handler takes the workspace by address. It asks for one copy and
//! for the parts of the copy that its body needs through functions that the
//! server defines, and the linker binds each ask to its definition. So each
//! handler compiles once, in this crate, with no generic and no trait
//! object.

use gandr_surface_lsp_base::peer::Peer;
use gandr_surface_lsp_core::context::Erased;
use gandr_surface_lsp_core::context::Viewed;
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

// The server defines each function (`#[unsafe(no_mangle)]`), and the linker
// binds each ask to its definition.
unsafe extern "Rust" {
    /// The copy of the document at `uri` that `peer` is answered from, in
    /// `workspace`; none when no connection holds the document. The server
    /// defines it.
    safe fn gandr_surface_lsp_view<'context>(
        workspace: Erased<'context>,
        uri: &'context DocumentUri,
        peer: Peer,
    ) -> Option<Viewed<'context>>;

    /// The text of `copy`. The server defines it.
    safe fn gandr_surface_lsp_source<'context>(copy: Viewed<'context>) -> SourceText<'context>;

    /// The reading of the text of `copy`. The server defines it.
    safe fn gandr_surface_lsp_reading<'context>(copy: Viewed<'context>) -> &'context Reading;

    /// What the hovers of `copy` read; none when its session did not build.
    /// The server defines it.
    safe fn gandr_surface_lsp_hovering<'context>(
        copy: Viewed<'context>
    ) -> Option<&'context Hovering>;
}

/// The text of `copy` and what its hovers read.
///
/// # Specification
/// trivial.
fn read(copy: Viewed<'_>) -> (SourceText<'_>, Option<&Hovering>)
{
    (
        gandr_surface_lsp_source(copy),
        gandr_surface_lsp_hovering(copy),
    )
}

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
pub fn highlight(
    workspace: Erased<'_>,
    uri: &DocumentUri,
    peer: Peer,
    position: Position,
) -> Answer
{
    highlight_in(
        gandr_surface_lsp_view(workspace, uri, peer).map(read),
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
pub fn linked_editing(
    workspace: Erased<'_>,
    uri: &DocumentUri,
    peer: Peer,
    position: Position,
) -> Answer
{
    linked_editing_in(
        gandr_surface_lsp_view(workspace, uri, peer).map(read),
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
pub fn inlay_hints(
    workspace: Erased<'_>,
    uri: &DocumentUri,
    peer: Peer,
    range: Range,
    shape: (gandr_surface_pretty::Style, ResolvesHintLocations),
) -> Answer
{
    inlay_hints_in(
        gandr_surface_lsp_view(workspace, uri, peer).map(|copy| {
            (
                gandr_surface_lsp_source(copy),
                gandr_surface_lsp_hovering(copy)
                    .map(|hovering| (hovering, gandr_surface_lsp_reading(copy))),
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
pub fn resolve_hint(
    workspace: Erased<'_>,
    uri: &DocumentUri,
    peer: Peer,
    position: Position,
    style: gandr_surface_pretty::Style,
) -> Option<InlayHint>
{
    resolve_hint_in(
        gandr_surface_lsp_view(workspace, uri, peer).and_then(|copy| {
            Some((
                gandr_surface_lsp_source(copy),
                gandr_surface_lsp_hovering(copy)?,
                gandr_surface_lsp_reading(copy),
            ))
        }),
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
pub fn copied_sources(
    workspace: Erased<'_>,
    uri: &DocumentUri,
    peer: Peer,
    ranges: &[Range],
) -> Answer
{
    copied_sources_in(
        gandr_surface_lsp_view(workspace, uri, peer).map(read),
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
