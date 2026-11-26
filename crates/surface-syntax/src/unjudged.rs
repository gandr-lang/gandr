//! The text of a source with its declaration of features read as spaces.
//!
//! A source can declare its language features in an inner attribute block at
//! its head, and the lowering refuses a source whose declaration differs
//! from what the source uses. A tool that lowers a text which it built from a
//! source lowers [`unjudged`] of the source: the declaration of the source
//! does not speak for the text of the tool.

use alloc::string::String;
use alloc::vec::Vec;
use core::ops::Range;

use anodized::spec;

use crate::span::SourceText;

/// `source` with each block of its head that declares the features of the
/// source read as spaces, or nothing when the head has no such block.
///
/// The head of a source is its lines before the first line that is not
/// blank, not a line comment, not the shebang and not a line of an inner
/// attribute block. A block declares the features when it holds the
/// attribute `features` alone. A block that holds a second attribute keeps
/// its text, and the lowering judges it.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `Some` exactly when the head holds such a block. The answer has
///   the length of `source` in bytes and each line break of `source`. Each
///   other byte of such a block is a space, and each byte outside such a block
///   is the byte of `source`.
/// - provides: a text whose declarations stand at the offsets of `source`, and
///   whose declaration of features the lowering does not judge. The formatter,
///   each reader that compares two spellings of one source, and each tool that
///   puts declarations of its own after the text of a source lower it.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a block of four lines becomes spaces with its three line
///   breaks, and the text above and below it stands; a block that holds a
///   second attribute gives nothing. A rewrite that changes the features of a
///   declared source enters each declaration of the source: with the block
///   judged, the lowering refuses the first declaration of the rewritten text.
/// - witness: `unjudged::tests::a_block_of_features_alone_is_read_as_spaces`
/// - witness: `gandr-surface-format::tests::rewrite::a_rewrite_enters_a_source_that_declares_its_features`
#[spec(ensures: |ret| ret.as_ref().is_none_or(|held| held.len() == <&str>::from(source).len()))]
#[inline]
#[must_use]
pub fn unjudged(source: SourceText<'_>) -> Option<String>
{
    let text = <&str>::from(source);
    let mut blocks: Vec<Range<usize>> = Vec::new();
    let mut at = 0_usize;
    while let Some(rest) = text.get(at ..).filter(|rest| !rest.is_empty()) {
        let line = rest.split_inclusive('\n').next().unwrap_or(rest);
        let content = line.trim();
        if content.is_empty() || content.starts_with("//") || (at == 0 && content.starts_with("#!"))
        {
            at = at.saturating_add(line.len());
            continue;
        }
        let Some(length) = line.starts_with("@![").then(|| inner_block(rest)).flatten()
        else {
            break;
        };
        let end = at.saturating_add(length);
        if text
            .get(at.saturating_add(3) .. end.saturating_sub(1))
            .is_some_and(features_alone)
        {
            blocks.push(at .. end);
        }
        at = text
            .get(end ..)
            .and_then(|after| after.find('\n'))
            .map_or(text.len(), |ahead| {
                end.saturating_add(ahead).saturating_add(1)
            });
    }
    if blocks.is_empty() {
        return None;
    }
    let mut out = String::with_capacity(text.len());
    for (offset, glyph) in text.char_indices() {
        if !matches!(glyph, '\n' | '\r') && blocks.iter().any(|block| block.contains(&offset)) {
            out.extend(core::iter::repeat_n(' ', glyph.len_utf8()));
        }
        else {
            out.push(glyph);
        }
    }
    Some(out)
}

/// The length in bytes of the inner attribute block that `text` opens on, as
/// far as the bracket that closes it.
///
/// # Specification
/// - requires: `text` starts with `@![`.
/// - ensures: the offset after the bracket that closes the block, where a
///   bracket inside a quoted text closes nothing; nothing when no bracket
///   closes it.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`unjudged`], over a block of four lines.
/// - witness: `unjudged::tests::a_block_of_features_alone_is_read_as_spaces`
fn inner_block(text: &str) -> Option<usize>
{
    let mut depth = 0_usize;
    let mut quoted = false;
    let mut escaped = false;
    for (at, glyph) in text.char_indices() {
        match glyph {
            _ if escaped => escaped = false,
            '\\' if quoted => escaped = true,
            '"' => quoted = !quoted,
            '[' if !quoted => depth = depth.saturating_add(1),
            ']' if !quoted => {
                depth = depth.saturating_sub(1);
                if depth == 0 {
                    return Some(at.saturating_add(1));
                }
            },
            _ => {},
        }
    }
    None
}

/// Whether `inner`, the text between the brackets of an inner attribute
/// block, is the attribute `features` with its payload and no second
/// attribute.
///
/// # Specification
/// - requires: nothing.
/// - ensures: true exactly when `inner` is the word `features`, one
///   parenthesised payload, and at most one comma after it, with white space
///   between them.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`unjudged`]; a block that holds a second attribute
///   keeps its text.
/// - witness: `unjudged::tests::a_block_of_features_alone_is_read_as_spaces`
fn features_alone(inner: &str) -> bool
{
    let Some(payload) = inner
        .trim()
        .strip_prefix("features")
        .map(str::trim_start)
        .filter(|payload| payload.starts_with('('))
    else {
        return false;
    };
    let mut depth = 0_usize;
    let mut quoted = false;
    let mut escaped = false;
    for (at, glyph) in payload.char_indices() {
        match glyph {
            _ if escaped => escaped = false,
            '\\' if quoted => escaped = true,
            '"' => quoted = !quoted,
            '(' if !quoted => depth = depth.saturating_add(1),
            ')' if !quoted => {
                depth = depth.saturating_sub(1);
                if depth == 0 {
                    return payload
                        .get(at.saturating_add(1) ..)
                        .is_some_and(|after| matches!(after.trim(), "" | ","));
                }
            },
            _ => {},
        }
    }
    false
}

#[cfg(test)]
mod tests
{
    use super::unjudged;
    use crate::span::SourceText;

    #[test]
    fn a_block_of_features_alone_is_read_as_spaces()
    {
        let source = include_str!("fixtures/a-source-under-a-declaration-of-four-lines.gandr");
        let read = unjudged(SourceText::from(source)).expect("the head declares the features");
        let (above, rest) = source.split_once("@![").expect("the source has the block");
        let (_, below) = rest.split_once(']').expect("the block closes");
        assert_eq!(read.len(), source.len(), "each offset stands");
        assert!(read.starts_with(above), "the text above the block stands");
        assert!(read.ends_with(below), "the text below the block stands");
        let block = read
            .get(above.len() .. read.len().saturating_sub(below.len()))
            .expect("the block is between them");
        assert!(
            block.chars().all(|glyph| matches!(glyph, ' ' | '\n')),
            "the block is spaces and line breaks: {block:?}"
        );
        assert_eq!(
            block.matches('\n').count(),
            3,
            "the block keeps its three line breaks"
        );

        let beside =
            include_str!("fixtures/a-source-under-a-declaration-beside-an-attribute.gandr");
        assert_eq!(
            unjudged(SourceText::from(beside)),
            None,
            "a block that holds a second attribute keeps its text"
        );
        assert_eq!(
            unjudged(SourceText::from(below)),
            None,
            "a source with no block is not read again"
        );
    }
}
