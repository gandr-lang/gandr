//! The code fragments of a comment: the text between two backquotes, coloured
//! as gandr when it reads as gandr.
//!
//! A comment names code between backquotes, such as `apply` or `count[<]`. The
//! editor's grammar gives each such fragment a code style. The server then
//! colours a fragment that lexes and parses clean with the roles the
//! highlighter gives it. Any other fragment keeps the comment role, so only
//! the grammar's code style marks it. A hover writes such a fragment of
//! documentation as code in the same colours, for a client that renders HTML.
//!
//! A fragment lexes when the labeler gives it no unknown byte. It parses clean
//! when it stands as a term, `def h = <fragment> ;`, or as a type,
//! `def h : <fragment> ;`, and the parse leaves no obligation. The term comes
//! first. The roles are the highlighter's roles over the fragment in that
//! host, so a fragment takes the colours that the same text takes in code.
//!
//! A fragment holds no line break. A run of two or more backquotes pairs with
//! nothing, so a fragment never starts or ends inside such a run.
//!
//! - Alternatives: an embedded gandr grammar inside the fragment, which colours
//!   ten keywords and also colours words in paths. A fragment read alone, with
//!   no host, which reads few terms.
//! - Reversal: when a fragment's names take what the document declares under
//!   them, the roles come from the judgement and not from a host.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use anodized::spec;
use gandr_surface_parser::Lexeme;
use gandr_surface_parser::label;
use gandr_surface_parser::parse;
use gandr_surface_render_remote::ByteOffset;
use gandr_surface_render_remote::ByteRange;
use gandr_surface_render_remote::HlRole;
use gandr_surface_render_remote::HlSpan;
use gandr_surface_syntax::SourceFragment;
use gandr_surface_syntax::SourceText;

use crate::markup::Host;
use crate::recheck::grammar;
use crate::recheck::roles;

/// The byte range of each fragment of `text`, between its backquotes.
///
/// # Specification
/// - requires: nothing.
/// - ensures: in order, the bytes between two single backquotes that pair, the
///   backquotes left out. A single backquote opens a fragment, and the next
///   single backquote closes it. A run of two or more backquotes closes no
///   fragment and opens none, and it drops a fragment that it interrupts. A
///   fragment that is empty or that holds a line break is left out, but its
///   backquotes still pair.
/// - provides: the fragments that a comment and a hover colour.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — two fragments on a line, an empty pair, a double
///   backquote, a fragment across a line break and a backquote left open are
///   each asserted at their exact ranges.
/// - witness: `fragment::tests::fragments_pair_single_backquotes`
#[spec(ensures: |ret| ret.iter().all(|range| range.start() < range.end()
    && <&str>::from(text).get(usize::from(range.start()) .. usize::from(range.end()))
        .is_some_and(|inner| !inner.contains(['\n', '\r', '`']))))]
pub fn fragments(text: SourceText<'_>) -> Vec<ByteRange>
{
    let text = <&str>::from(text);
    let bytes = text.as_bytes();
    let mut found = Vec::new();
    let mut open: Option<usize> = None;
    let mut at = 0_usize;
    while let Some(&byte) = bytes.get(at) {
        if byte != b'`' {
            at = at.saturating_add(1);
            continue;
        }
        let run = bytes.get(at ..).map_or(0, |rest| {
            rest.iter().take_while(|&&next| next == b'`').count()
        });
        if run > 1 {
            open = None;
        }
        else if let Some(start) = open.take() {
            if text
                .get(start .. at)
                .is_some_and(|inner| !inner.is_empty() && !inner.contains(['\n', '\r']))
                && let Ok(range) = ByteRange::new(start.into(), at.into())
            {
                found.push(range);
            }
        }
        else {
            open = Some(at.saturating_add(1));
        }
        at = at.saturating_add(run.max(1));
    }
    found
}

/// The highlighter's spans over `fragment`, relative to it, when it lexes and
/// parses clean.
///
/// # Specification
/// - requires: nothing; any text is admitted.
/// - ensures: none when the labeler gives `fragment` an unknown byte, or when
///   the grammar does not build. Else the spans of the first host, term then
///   type, whose parse leaves no obligation: each span that lies inside the
///   fragment and whose role is not [`HlRole::Other`], shifted to the fragment,
///   in order. None when neither host parses clean.
/// - provides: the colours of one fragment.
/// - fails: never.
/// - panics: none.
/// - intension: one labelling and at most two parses.
///
/// # Adequacy
/// - hypothesis: L3 — a name, a call with a field and a type each take their
///   roles. A path, a Greek letter and an ellipsis each take none.
/// - witness: `fragment::tests::a_fragment_is_coloured_when_it_reads_as_gandr`
#[spec(ensures: |ret| ret.as_ref().is_none_or(|spans| spans.iter().all(|span|
    usize::from(span.range.end()) <= <&str>::from(fragment).len() && span.role != HlRole::Other)))]
pub fn coloured(fragment: SourceText<'_>) -> Option<Vec<HlSpan>>
{
    if label(SourceFragment::from(<&str>::from(fragment)))
        .iter()
        .any(|token| token.lexeme == Lexeme::Unknown)
    {
        return None;
    }
    let (Ok(grammar), Ok(roles)) = (grammar(), roles())
    else {
        return None;
    };
    [Host::Term, Host::Type].into_iter().find_map(|host| {
        let (hosted, at) = host.host(fragment);
        let parsed = parse(grammar, SourceText::from(hosted.as_str())).ok()?;
        if !parsed.obligations().is_empty() {
            return None;
        }
        let at = usize::from(at);
        let end = at.saturating_add(<&str>::from(fragment).len());
        let spans = roles.highlight(parsed.tree()).ok()?;
        Some(
            spans
                .into_iter()
                .filter_map(|span| {
                    let (start, stop) = (
                        usize::from(span.range.start()),
                        usize::from(span.range.end()),
                    );
                    if span.role == HlRole::Other || start < at || stop > end {
                        return None;
                    }
                    let range = ByteRange::new(
                        start.saturating_sub(at).into(),
                        stop.saturating_sub(at).into(),
                    )
                    .ok()?;
                    Some(HlSpan {
                        range,
                        role: span.role,
                    })
                })
                .collect(),
        )
    })
}

/// `spans`, the highlighter's spans over `text`, with each comment span split
/// at its fragments that read as gandr.
///
/// # Specification
/// - requires: `spans` are sorted and disjoint, on character boundaries of
///   `text`.
/// - ensures: each span that is not a comment, as it is. Each comment span
///   split at each of its fragments that [`coloured`] colours: the comment role
///   over the bytes before, between and after such fragments, and the
///   fragment's spans, shifted to `text`, over the fragment. A fragment that
///   [`coloured`] does not colour keeps the comment role. The result is sorted
///   and disjoint.
/// - provides: the spans that the semantic tokens of a text send.
/// - fails: never.
/// - panics: none.
/// - intension: one scan of each comment, and one call of [`coloured`] for each
///   distinct fragment.
///
/// # Adequacy
/// - hypothesis: L3 — a comment with a name, a path and a call keeps the
///   comment role around each fragment and over the path, and its name and call
///   take their roles. A span of code is unchanged.
/// - witness: `fragment::tests::a_comment_is_split_at_its_coloured_fragments`
/// - witness: `tests::session::sweeps::corpus_tokens_cover_the_highlighted_bytes`
#[spec(ensures: |ret| ret.iter().zip(ret.iter().skip(1))
    .all(|(first, second)| first.range.end() <= second.range.start()))]
#[inline]
#[must_use]
pub fn comments_coloured(
    text: SourceText<'_>,
    spans: Vec<HlSpan>,
) -> Vec<HlSpan>
{
    let text = <&str>::from(text);
    let mut read: BTreeMap<&str, Option<Vec<HlSpan>>> = BTreeMap::new();
    let mut split = Vec::with_capacity(spans.len());
    for span in spans {
        let (start, end) = (span.range.start(), span.range.end());
        let Some(comment) = text
            .get(usize::from(start) .. usize::from(end))
            .filter(|_| span.role == HlRole::Comment)
        else {
            split.push(span);
            continue;
        };
        let mut cursor = start;
        for fragment in fragments(SourceText::from(comment)) {
            let Some(inner) =
                comment.get(usize::from(fragment.start()) .. usize::from(fragment.end()))
            else {
                continue;
            };
            let Some(roles) = read
                .entry(inner)
                .or_insert_with(|| coloured(SourceText::from(inner)))
                .as_ref()
            else {
                continue;
            };
            let shifted = |offset: ByteOffset| {
                ByteOffset::from(usize::from(start).saturating_add(usize::from(offset)))
            };
            let from = shifted(fragment.start());
            push_comment(&mut split, cursor, from);
            split.extend(roles.iter().filter_map(|role| {
                Some(HlSpan {
                    range: ByteRange::new(
                        ByteOffset::from(
                            usize::from(from).saturating_add(usize::from(role.range.start())),
                        ),
                        ByteOffset::from(
                            usize::from(from).saturating_add(usize::from(role.range.end())),
                        ),
                    )
                    .ok()?,
                    role: role.role,
                })
            }));
            cursor = shifted(fragment.end());
        }
        push_comment(&mut split, cursor, end);
    }
    split
}

/// Push a comment span over the bytes from `start` up to `end`, when they are
/// not empty.
///
/// # Specification
/// trivial.
fn push_comment(
    spans: &mut Vec<HlSpan>,
    start: ByteOffset,
    end: ByteOffset,
)
{
    if start < end
        && let Ok(range) = ByteRange::new(start, end)
    {
        spans.push(HlSpan {
            range,
            role: HlRole::Comment,
        });
    }
}

#[cfg(test)]
mod tests
{
    use alloc::vec::Vec;

    use gandr_surface_render_remote::ByteRange;
    use gandr_surface_render_remote::HlRole;
    use gandr_surface_render_remote::HlSpan;
    use gandr_surface_syntax::SourceText;

    use super::coloured;
    use super::comments_coloured;
    use super::fragments;

    #[test]
    fn fragments_pair_single_backquotes()
    {
        let ranges = |text: &str| {
            fragments(SourceText::from(text))
                .iter()
                .map(|range| (usize::from(range.start()), usize::from(range.end())))
                .collect::<Vec<_>>()
        };
        let text = "see `apply` and `count[<]`";
        assert_eq!(ranges(text), [(5, 10), (17, 25)], "two fragments on a line");
        assert_eq!(
            ranges("an empty `` pair, then `x`"),
            [(24, 25)],
            "a double backquote pairs with nothing"
        );
        assert_eq!(
            ranges("a `b` then `c`` d`"),
            [(3, 4)],
            "a double backquote drops the fragment it interrupts"
        );
        assert_eq!(
            ranges(include_str!(
                "fragment/unformatted/fragments-pair-single-backquotes.gandr"
            )),
            [(20, 21)],
            "a fragment across a line break is left out, and its backquotes still pair"
        );
        assert_eq!(
            ranges("left `open"),
            Vec::<(usize, usize)>::new(),
            "an open backquote closes nothing"
        );
    }

    #[test]
    fn a_fragment_is_coloured_when_it_reads_as_gandr()
    {
        let roles = |fragment: &'static str| {
            coloured(SourceText::from(fragment)).map(|spans| {
                spans
                    .iter()
                    .map(|span| {
                        (
                            fragment
                                .get(
                                    usize::from(span.range.start())
                                        .. usize::from(span.range.end()),
                                )
                                .unwrap_or_default(),
                            span.role,
                        )
                    })
                    .collect::<Vec<_>>()
            })
        };
        assert_eq!(
            roles("apply"),
            Some(Vec::from([("apply", HlRole::Variable)]))
        );
        assert_eq!(
            roles("applyAt[.i = j]").map(|spans| spans.len()),
            Some(3_usize),
            "a call with a field takes each name's role"
        );
        assert!(
            roles("Integer -> -F Integer").is_some(),
            "a type parses clean as a type"
        );
        assert_eq!(roles("../../data/x.gandr"), None, "a path does not lex");
        assert_eq!(roles("#spec{ … }"), None, "an ellipsis does not lex");
    }

    #[test]
    fn a_comment_is_split_at_its_coloured_fragments()
    {
        let text =
            include_str!("fragment/unformatted/a-comment-is-split-at-its-coloured-fragments.gandr");
        let span = |start: usize, end: usize, role| HlSpan {
            range: ByteRange::new(start.into(), end.into()).expect("an ordered range"),
            role,
        };
        let code = span(31, 34, HlRole::Keyword);
        let split = comments_coloured(
            SourceText::from(text),
            Vec::from([span(0, 30, HlRole::Comment), code]),
        );
        assert_eq!(
            split,
            [
                span(0, 8, HlRole::Comment),
                span(8, 13, HlRole::Variable),
                span(13, 30, HlRole::Comment),
                code,
            ],
            "the name takes its role, the path keeps the comment role, and code is unchanged"
        );
    }
}
