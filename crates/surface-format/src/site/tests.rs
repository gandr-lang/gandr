//! The sites of two texts compared through the map of a rewrite.

use alloc::vec::Vec;

use gandr_surface_parser::parse;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::SourceFragment;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use super::Placement;
use super::Sites;
use super::Unplaced;
use crate::Layout;
use crate::Piece;
use crate::leaf;
use crate::leaf::Leaf;

/// Two declarations, each naming a name that nothing declares.
const BEFORE: &str = "def a : Integer = x;\ndef b : Integer = y;\n";

/// [`BEFORE`] with blank lines between its pieces and spaces inside its
/// second piece.
const RESPACED: &str = "def a : Integer = x;\n\n\ndef b : Integer =   y;\n";

/// [`BEFORE`] with its two names exchanged.
const EXCHANGED: &str = "def a : Integer = y;\ndef b : Integer = x;\n";

/// The first declaration of [`BEFORE`] as a signature and a definition.
const SPLIT: &str = "def a : Integer;\ndef a = x;\n";

/// The leaves of `text`.
///
/// # Specification
/// trivial.
fn leaves(text: &str) -> Vec<Leaf<'_>>
{
    let grammar = gandr_surface_grammar::built_in().expect("the built-in grammar builds");
    let parsed = parse(&grammar, SourceText::from(text)).expect("the text parses");
    leaf::flatten(&grammar, parsed.tree(), parsed.obligations()).leaves
}

/// The material leaves of `leaves`, as the formatter writes them.
///
/// # Specification
/// trivial.
fn tokens<'source>(leaves: &[Leaf<'source>]) -> Vec<Leaf<'source>>
{
    crate::material_leaves(leaves).copied().collect()
}

/// The span of the first `needle` in `text` at or after `from`.
///
/// # Specification
/// trivial.
fn span(
    text: &str,
    needle: &str,
    from: usize,
) -> ByteSpan
{
    let start = text
        .get(from ..)
        .and_then(|rest| rest.find(needle))
        .map(|at| at.saturating_add(from))
        .expect("the text holds the needle");
    ByteSpan::new(
        ByteOffset::from(start),
        ByteOffset::from(start.saturating_add(needle.len())),
    )
    .expect("a span")
}

/// The pieces of two texts: each text's lines that are not blank, paired in
/// order.
///
/// # Specification
/// trivial.
fn pieces(
    before: &str,
    candidate: &str,
) -> Vec<Piece>
{
    let lines = |text: &str| -> Vec<ByteSpan> {
        let mut spans = Vec::new();
        let mut start = 0_usize;
        for line in text.split_inclusive('\n') {
            let body = line.trim_end_matches('\n');
            if !body.is_empty() {
                spans.push(
                    ByteSpan::new(
                        ByteOffset::from(start),
                        ByteOffset::from(start.saturating_add(body.len())),
                    )
                    .expect("a span"),
                );
            }
            start = start.saturating_add(line.len());
        }
        spans
    };
    lines(before)
        .into_iter()
        .zip(lines(candidate))
        .map(|(source, formatted)| Piece {
            source,
            formatted,
            layout: Layout::Formatted,
        })
        .collect()
}

/// Blank lines between pieces and spaces inside a piece move each raw span
/// after them, and keep each site: a name in the second piece, and the empty
/// span at the end of the first piece.
#[test]
fn a_respaced_piece_keeps_each_site_of_its_leaves()
{
    let (before, candidate) = (leaves(BEFORE), leaves(RESPACED));
    let pieces = pieces(BEFORE, RESPACED);
    let sites = Sites::new(&pieces, (&before, &before, &candidate));
    let (left, right) = (span(BEFORE, "y", 0), span(RESPACED, "y", 0));
    assert_ne!(left, right);
    assert_eq!(sites.spanned(left, right), Placement::Same);
    let end = |text: &str| {
        let at = span(text, ";", 0).end();
        ByteSpan::new(at, at).expect("an empty span")
    };
    assert_eq!(sites.spanned(end(BEFORE), end(RESPACED)), Placement::Same);
    assert_eq!(sites.spanned(span(BEFORE, "x", 0), right), Placement::Moved);
}

/// A rewrite that writes one declaration as a signature and a definition
/// moves the name after it, and the candidate's leaf copies the name. So the
/// name keeps its site. The `;` the rewrite writes itself copies no leaf, so
/// it has no site.
#[test]
fn a_respelled_piece_keeps_the_site_of_a_copied_leaf()
{
    let source = "def a : Integer = x;\n";
    let before = leaves(source);
    let copied = tokens(&before);
    let &[def, name, colon, integer, equals, x, semicolon] = copied.as_slice()
    else {
        panic!("seven tokens: {copied:?}");
    };
    let written_semicolon = Leaf {
        span: ByteSpan::new(def.span.start(), def.span.start()).expect("an empty span"),
        text: SourceFragment::from(";"),
        ..semicolon
    };
    let written = [
        def,
        name,
        colon,
        integer,
        written_semicolon,
        def,
        name,
        equals,
        x,
        semicolon,
    ];
    let candidate = leaves(SPLIT);
    assert_eq!(
        tokens(&candidate)
            .iter()
            .map(|leaf| <&str>::from(leaf.text))
            .collect::<Vec<_>>(),
        written
            .iter()
            .map(|leaf| <&str>::from(leaf.text))
            .collect::<Vec<_>>()
    );
    let pieces = [Piece {
        source: ByteSpan::new(def.span.start(), semicolon.span.end()).expect("a span"),
        formatted: ByteSpan::new(
            ByteOffset::from(0_usize),
            ByteOffset::from(SPLIT.trim_end().len()),
        )
        .expect("a span"),
        layout: Layout::Formatted,
    }];
    let sites = Sites::new(&pieces, (&before, &written, &candidate));
    let (left, right) = (span(source, "x", 0), span(SPLIT, "x", 0));
    assert_ne!(left, right);
    assert_eq!(sites.spanned(left, right), Placement::Same);
    assert_eq!(
        sites.candidate(span(SPLIT, ";", 0)),
        Maybe::Absent(Unplaced::Written)
    );
}

/// A name that stands in the first piece before the rewrite, and in the
/// second piece after it, is moved, though it copies the same leaf.
#[test]
fn a_site_in_another_piece_is_moved()
{
    let before = leaves(BEFORE);
    let copied = tokens(&before);
    let ordinal = |needle: &str| {
        copied
            .iter()
            .position(|leaf| <&str>::from(leaf.text) == needle)
            .expect("the token")
    };
    let (x, y) = (ordinal("x"), ordinal("y"));
    let mut written = copied.clone();
    written.swap(x, y);
    let candidate = leaves(EXCHANGED);
    let pieces = pieces(BEFORE, EXCHANGED);
    let sites = Sites::new(&pieces, (&before, &written, &candidate));
    assert_eq!(
        sites.spanned(span(BEFORE, "x", 0), span(EXCHANGED, "x", 0)),
        Placement::Moved
    );
    assert_eq!(
        sites.spanned(span(BEFORE, "x", 0), span(EXCHANGED, "y", 0)),
        Placement::Moved
    );
    assert_eq!(
        sites.spanned(span(BEFORE, "Integer", 0), span(EXCHANGED, "Integer", 0)),
        Placement::Same
    );
}

/// A span between two pieces has no site, so it compares equal to no span,
/// itself included. Under a base, a span that ends before it compares by its
/// bytes, and two absent spans compare by their reasons.
#[test]
fn a_site_between_pieces_has_no_place()
{
    let before = leaves(BEFORE);
    let pieces = pieces(BEFORE, BEFORE);
    let sites = Sites::new(&pieces, (&before, &before, &before));
    let gap = span(BEFORE, "\n", 0);
    assert_eq!(sites.before(gap), Maybe::Absent(Unplaced::Between));
    assert_eq!(sites.spanned(gap, gap), Placement::Moved);
    let base = ByteOffset::from(4_usize);
    let import = span(BEFORE, "def", 0);
    assert_eq!(
        sites.placed::<()>(base, (Maybe::Present(import), Maybe::Present(import))),
        Placement::Same
    );
    assert_eq!(
        sites.placed::<()>(
            base,
            (
                Maybe::Present(import),
                Maybe::Present(span(BEFORE, "def", 1))
            )
        ),
        Placement::Moved
    );
    assert_eq!(
        sites.placed(base, (Maybe::Absent(1_u8), Maybe::Absent(1_u8))),
        Placement::Same
    );
    assert_eq!(
        sites.placed(base, (Maybe::Absent(1_u8), Maybe::Absent(2_u8))),
        Placement::Moved
    );
    assert_eq!(
        sites.placed(base, (Maybe::Present(import), Maybe::Absent(1_u8))),
        Placement::Moved
    );
}
