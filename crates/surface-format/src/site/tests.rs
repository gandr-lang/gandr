//! The sites of two texts compared through the map of a pass.

use alloc::vec::Vec;

use gandr_surface_parser::parse;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::SourceFragment;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use super::Placement;
use super::Sites;
use crate::leaf;
use crate::leaf::Leaf;
use crate::leaf::Origin;

/// Two declarations, each naming a name that nothing declares.
const BEFORE: &str = "def a : Integer = x;\ndef b : Integer = y;\n";

/// [`BEFORE`] with blank lines between its declarations and spaces inside
/// the second.
const RESPACED: &str = "def a : Integer = x;\n\n\ndef b : Integer =   y;\n";

/// [`BEFORE`] with its two names exchanged.
const EXCHANGED: &str = "def a : Integer = y;\ndef b : Integer = x;\n";

/// A declaration whose type a rewrite respells, with a name after it.
const PRODUCT: &str = "def p : *{Integer, String} = x;\n";

/// [`PRODUCT`] with its type in the sugared spelling.
const SUGARED: &str = "def p : Integer * String = x;\n";

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

/// The span from the start of `first` to the end of `last`.
///
/// # Specification
/// trivial.
fn joined(
    first: ByteSpan,
    last: ByteSpan,
) -> ByteSpan
{
    ByteSpan::new(first.start(), last.end()).expect("a span")
}

/// Blank lines between forms and spaces inside a form move each raw span
/// after them, and keep each site: a name, the empty span at the end of a
/// `;`, and a span inside a copied leaf.
#[test]
fn a_respaced_text_keeps_each_site_of_a_copied_leaf()
{
    let before = leaves(BEFORE);
    let sites = Sites::new(&before, &leaves(RESPACED));
    let (left, right) = (span(BEFORE, "y", 0), span(RESPACED, "y", 0));
    assert_ne!(left, right);
    assert_eq!(sites.spanned(left, right), Placement::Same);
    let end = |text: &str| {
        let at = span(text, ";", 21).end();
        ByteSpan::new(at, at).expect("an empty span")
    };
    assert_eq!(sites.spanned(end(BEFORE), end(RESPACED)), Placement::Same);
    let inner = |text: &str| {
        let integer = span(text, "Integer", 21);
        ByteSpan::new(
            ByteOffset::from(usize::from(integer.start()).saturating_add(2)),
            integer.end(),
        )
        .expect("a span")
    };
    assert_eq!(
        sites.spanned(inner(BEFORE), inner(RESPACED)),
        Placement::Same
    );
    assert_eq!(sites.spanned(span(BEFORE, "x", 0), right), Placement::Moved);
}

/// A rewrite that writes `*{Integer, String}` as `Integer * String` copies
/// the two operands and writes the `*`. The respelled form maps its ends to
/// the ends of its leaves, so a site that is the form keeps its site. The
/// name after the form, a copied leaf, keeps its site too. An end inside a
/// tile the pass replaces has no image.
#[test]
fn a_respelled_form_maps_its_ends_to_its_leaves()
{
    let before = leaves(PRODUCT);
    let tokens: Vec<Leaf<'_>> = crate::material_leaves(&before).copied().collect();
    let position = |needle: &str| {
        tokens
            .iter()
            .position(|leaf| <&str>::from(leaf.text) == needle)
            .expect("the token")
    };
    let open = position("*{");
    let close = position("}");
    let form = joined(span(PRODUCT, "*{", 0), span(PRODUCT, "}", 0));
    let star = Leaf {
        span: ByteSpan::new(form.start(), form.start()).expect("an empty span"),
        text: SourceFragment::from("*"),
        origin: Origin::Rewrite(form),
        ..tokens[open]
    };
    let mut written: Vec<Leaf<'_>> = tokens.get(.. open).expect("the head").to_vec();
    written.extend([
        tokens[position("Integer")],
        star,
        tokens[position("String")],
    ]);
    written.extend(tokens.get(close.saturating_add(1) ..).expect("the rest"));
    let sites = Sites::new(&written, &leaves(SUGARED));
    let sugared = joined(span(SUGARED, "Integer", 0), span(SUGARED, "String", 0));
    assert_eq!(sites.spanned(form, sugared), Placement::Same);
    let (left, right) = (span(PRODUCT, "x", 0), span(SUGARED, "x", 0));
    assert_ne!(left, right);
    assert_eq!(sites.spanned(left, right), Placement::Same);
    assert_eq!(
        sites.spanned(span(PRODUCT, ",", 0), span(SUGARED, "*", 0)),
        Placement::Moved
    );
}

/// A site at the bytes where the text before held a name, but whose leaf the
/// pass copied from another name, is moved. So is a site with an end in
/// layout. A span that ends before the base compares by its bytes.
#[test]
fn a_site_at_another_copy_or_in_layout_is_moved()
{
    let before = leaves(BEFORE);
    let mut written = before.clone();
    let at = |needle: &str| {
        written
            .iter()
            .position(|leaf| <&str>::from(leaf.text) == needle)
            .expect("the token")
    };
    let (x, y) = (at("x"), at("y"));
    written.swap(x, y);
    let sites = Sites::new(&written, &leaves(EXCHANGED));
    assert_eq!(span(BEFORE, "x", 0), span(EXCHANGED, "y", 0));
    assert_eq!(
        sites.spanned(span(BEFORE, "x", 0), span(EXCHANGED, "y", 0)),
        Placement::Moved
    );
    assert_eq!(
        sites.spanned(span(BEFORE, "x", 0), span(EXCHANGED, "x", 21)),
        Placement::Same
    );
    let respaced = leaves(RESPACED);
    let kept = Sites::new(&respaced, &respaced);
    let equals = span(RESPACED, "=", 21).end();
    let layout = ByteOffset::from(usize::from(equals).saturating_add(2));
    let blank = ByteSpan::new(layout, layout).expect("an empty span");
    assert_eq!(kept.spanned(blank, blank), Placement::Moved);
    let reaching = ByteSpan::new(layout, span(RESPACED, "y", 0).end()).expect("a span");
    assert_eq!(kept.spanned(reaching, reaching), Placement::Moved);
    let named = span(RESPACED, "y", 0);
    assert_eq!(kept.spanned(named, named), Placement::Same);
    let kept = Sites::new(&before, &before);
    let base = ByteOffset::from(4_usize);
    let import = span(BEFORE, "def", 0);
    assert_eq!(
        kept.placed::<()>(base, (Maybe::Present(import), Maybe::Present(import))),
        Placement::Same
    );
    assert_eq!(
        kept.placed::<()>(
            base,
            (
                Maybe::Present(import),
                Maybe::Present(span(BEFORE, "def", 1))
            )
        ),
        Placement::Moved
    );
    assert_eq!(
        kept.placed(base, (Maybe::Absent(1_u8), Maybe::Absent(1_u8))),
        Placement::Same
    );
    assert_eq!(
        kept.placed(base, (Maybe::Absent(1_u8), Maybe::Absent(2_u8))),
        Placement::Moved
    );
}
