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
///
/// # Specification
/// trivial.
fn before() -> SourceText<'static>
{
    SourceText::from(include_str!("../unformatted/two-unbound-names.gandr"))
}

/// [`before`] with blank lines between its declarations and spaces inside
/// the second.
///
/// # Specification
/// trivial.
fn respaced() -> SourceText<'static>
{
    SourceText::from(include_str!(
        "../unformatted/two-unbound-names-respaced.gandr"
    ))
}

/// [`before`] with its two names exchanged.
///
/// # Specification
/// trivial.
fn exchanged() -> SourceText<'static>
{
    SourceText::from(include_str!(
        "../unformatted/two-unbound-names-exchanged.gandr"
    ))
}

/// A declaration whose type a rewrite respells, with a name after it.
///
/// # Specification
/// trivial.
fn product() -> SourceText<'static>
{
    SourceText::from("def p : *{Integer, String} = x;\n")
}

/// [`product`] with its type in the sugared spelling.
///
/// # Specification
/// trivial.
fn sugared() -> SourceText<'static>
{
    SourceText::from("def p : Integer * String = x;\n")
}

/// The leaves of `text`.
///
/// # Specification
/// trivial.
fn leaves(text: SourceText<'_>) -> Vec<Leaf<'_>>
{
    let grammar = gandr_surface_grammar::built_in().expect("the built-in grammar builds");
    let parsed = parse(&grammar, text).expect("the text parses");
    leaf::flatten(&grammar, parsed.tree(), parsed.obligations()).leaves
}

/// The span of the first `needle` in `text` at or after `from`.
///
/// # Specification
/// trivial.
fn span(
    text: SourceText<'_>,
    needle: SourceFragment<'_>,
    from: ByteOffset,
) -> ByteSpan
{
    let (text, needle, from) = (<&str>::from(text), <&str>::from(needle), usize::from(from));
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

/// The span of the first `needle` in `text`.
///
/// # Specification
/// trivial.
fn first(
    text: SourceText<'_>,
    needle: SourceFragment<'_>,
) -> ByteSpan
{
    span(text, needle, ByteOffset::from(0_usize))
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
    let read = leaves(before());
    let sites = Sites::new(&read, &leaves(respaced()));
    let y = SourceFragment::from("y");
    let (left, right) = (first(before(), y), first(respaced(), y));
    assert_ne!(left, right);
    assert_eq!(sites.spanned(left, right), Placement::Same);
    let second = ByteOffset::from(21_usize);
    let end = |text: SourceText<'_>| {
        let at = span(text, SourceFragment::from(";"), second).end();
        ByteSpan::new(at, at).expect("an empty span")
    };
    assert_eq!(
        sites.spanned(end(before()), end(respaced())),
        Placement::Same
    );
    let inner = |text: SourceText<'_>| {
        let integer = span(text, SourceFragment::from("Integer"), second);
        ByteSpan::new(
            ByteOffset::from(usize::from(integer.start()).saturating_add(2)),
            integer.end(),
        )
        .expect("a span")
    };
    assert_eq!(
        sites.spanned(inner(before()), inner(respaced())),
        Placement::Same
    );
    assert_eq!(
        sites.spanned(first(before(), SourceFragment::from("x")), right),
        Placement::Moved
    );
}

/// A rewrite that writes `*{Integer, String}` as `Integer * String` copies
/// the two operands and writes the `*`. The respelled form maps its ends to
/// the ends of its leaves, so a site that is the form keeps its site. The
/// name after the form, a copied leaf, keeps its site too. An end inside a
/// tile the pass replaces has no image.
#[test]
fn a_respelled_form_maps_its_ends_to_its_leaves()
{
    let before = leaves(product());
    let tokens: Vec<Leaf<'_>> = crate::material_leaves(&before).copied().collect();
    let position = |needle: &str| {
        tokens
            .iter()
            .position(|leaf| <&str>::from(leaf.text) == needle)
            .expect("the token")
    };
    let open = position("*{");
    let close = position("}");
    let form = joined(
        first(product(), SourceFragment::from("*{")),
        first(product(), SourceFragment::from("}")),
    );
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
    let sites = Sites::new(&written, &leaves(sugared()));
    let whole = joined(
        first(sugared(), SourceFragment::from("Integer")),
        first(sugared(), SourceFragment::from("String")),
    );
    assert_eq!(sites.spanned(form, whole), Placement::Same);
    let x = SourceFragment::from("x");
    let (left, right) = (first(product(), x), first(sugared(), x));
    assert_ne!(left, right);
    assert_eq!(sites.spanned(left, right), Placement::Same);
    assert_eq!(
        sites.spanned(
            first(product(), SourceFragment::from(",")),
            first(sugared(), SourceFragment::from("*"))
        ),
        Placement::Moved
    );
}

/// A site at the bytes where the text before held a name, but whose leaf the
/// pass copied from another name, is moved. So is a site with an end in
/// layout. A span that ends before the base compares by its bytes.
#[test]
fn a_site_at_another_copy_or_in_layout_is_moved()
{
    let read = leaves(before());
    let mut written = read.clone();
    let at = |needle: &str| {
        written
            .iter()
            .position(|leaf| <&str>::from(leaf.text) == needle)
            .expect("the token")
    };
    let (x, y) = (at("x"), at("y"));
    written.swap(x, y);
    let sites = Sites::new(&written, &leaves(exchanged()));
    let (x, y) = (SourceFragment::from("x"), SourceFragment::from("y"));
    let source = before();
    assert_eq!(first(source, x), first(exchanged(), y));
    assert_eq!(
        sites.spanned(first(source, x), first(exchanged(), y)),
        Placement::Moved
    );
    assert_eq!(
        sites.spanned(
            first(source, x),
            span(exchanged(), x, ByteOffset::from(21_usize))
        ),
        Placement::Same
    );
    let respaced_leaves = leaves(respaced());
    let kept = Sites::new(&respaced_leaves, &respaced_leaves);
    let equals = span(
        respaced(),
        SourceFragment::from("="),
        ByteOffset::from(21_usize),
    )
    .end();
    let layout = ByteOffset::from(usize::from(equals).saturating_add(2));
    let blank = ByteSpan::new(layout, layout).expect("an empty span");
    assert_eq!(kept.spanned(blank, blank), Placement::Moved);
    let reaching = ByteSpan::new(layout, first(respaced(), y).end()).expect("a span");
    assert_eq!(kept.spanned(reaching, reaching), Placement::Moved);
    let named = first(respaced(), y);
    assert_eq!(kept.spanned(named, named), Placement::Same);
    let kept = Sites::new(&read, &read);
    let base = ByteOffset::from(4_usize);
    let def = SourceFragment::from("def");
    let import = first(source, def);
    assert_eq!(
        kept.placed::<()>(base, (Maybe::Present(import), Maybe::Present(import))),
        Placement::Same
    );
    assert_eq!(
        kept.placed::<()>(
            base,
            (
                Maybe::Present(import),
                Maybe::Present(span(source, def, ByteOffset::from(1_usize)))
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
