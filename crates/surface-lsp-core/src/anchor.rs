//! Where a line of a corpus source stands, read off the declarations
//! written in it, so a test's expectation over a corpus source follows an
//! edit made elsewhere in that source (#2786).
//!
//! The `fixture` feature opens the module to the tests of the crates above
//! the core. A fixture panics where the test misread its input. The module is
//! built for a test or for the feature, and in each build it expects the
//! panic lint.
#![expect(
    clippy::expect_used,
    reason = "a fixture refuses loudly a source the test did not mean, and its specification states each panic"
)]

use alloc::format;
use alloc::string::String;

/// A corpus source's text.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct Source<'text>(pub &'text str);

/// Text written on one line of a source.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct Held<'text>(pub &'text str);

/// A zero-based line of a source.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct Row(pub u32);

/// The line of `source` that holds `held`, which exactly one line holds.
///
/// # Panics
///
/// When no line, or more than one, holds `held`.
///
/// # Specification
/// trivial.
#[must_use]
#[inline]
pub fn line_of(
    source: Source<'_>,
    held: Held<'_>,
) -> Row
{
    let mut lines = source
        .0
        .lines()
        .enumerate()
        .filter(|&(_, line)| line.contains(held.0));
    let (index, _) = lines.next().expect("a line holds the text");
    assert!(lines.next().is_none(), "`{}` is held by one line", held.0);
    Row(u32::try_from(index).expect("a source's line count fits a position"))
}

/// Line `row` of `source`, named by the declaration that it stands in.
///
/// The name starts with the head of the nearest declaration at or above the
/// line: the words that its line starts with before its parameters, type or
/// body. Then it gives how many lines below that head the line stands, as
/// `def rec minus+5`. A line above every declaration takes its name from the
/// start of the source, as `+3`.
///
/// # Specification
/// trivial.
#[must_use]
#[inline]
pub fn anchored(
    source: Source<'_>,
    row: Row,
) -> String
{
    let line = usize::try_from(row.0).unwrap_or(usize::MAX);
    let (head, below) = source
        .0
        .lines()
        .take(line.saturating_add(1))
        .enumerate()
        .filter(|&(_, text)| text.starts_with(|first: char| first.is_ascii_lowercase()))
        .last()
        .map_or(("", line), |(at, text)| {
            let end = text
                .find(['(', ':', '=', '{', '[', ';'])
                .unwrap_or(text.len());
            (
                text.get(.. end).unwrap_or(text).trim_end(),
                line.saturating_sub(at),
            )
        });
    format!("{head}+{below}")
}
