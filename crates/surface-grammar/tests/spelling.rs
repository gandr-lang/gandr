//! The spelling table: every glyph tile has an ASCII spelling, written as
//! asked, and an ASCII token stands for its glyph.

use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use gandr_surface_grammar::Ascii;
use gandr_surface_grammar::LabelText;
use gandr_surface_grammar::RegexShape;
use gandr_surface_grammar::RegexView;
use gandr_surface_grammar::SPELLED;
use gandr_surface_grammar::Spelling;
use gandr_surface_grammar::Sym;
use gandr_surface_grammar::TileLabel;
use gandr_surface_grammar::Unspelled;
use gandr_surface_grammar::aliased;
use gandr_surface_grammar::built_in;
use gandr_surface_grammar::spelled;

/// Every tile label `regex` names, into `labels`.
///
/// # Specification
/// trivial.
fn tiles(
    regex: RegexView<'_>,
    labels: &mut BTreeSet<TileLabel>,
)
{
    let mut pending = Vec::from([regex]);
    while let Some(view) = pending.pop() {
        match view.shape() {
            RegexShape::Sym(Sym::Tile(tile)) => {
                let _new = labels.insert(TileLabel(tile.label));
            },
            RegexShape::Sym(_) | RegexShape::Empty => {},
            RegexShape::Seq(children) | RegexShape::Alt(children) => pending.extend(children),
            RegexShape::Optional(child) | RegexShape::Repeat(child) => pending.push(child),
        }
    }
}

/// #3135: a spelling reads from the name a `[presentation]` table writes it
/// by, and no other name reads.
#[test]
fn a_spelling_reads_from_its_name_3135()
{
    assert_eq!(["unicode", "ascii"].map(str::parse::<Spelling>), [
        Ok(Spelling::Unicode),
        Ok(Spelling::Ascii)
    ]);
    for name in ["Unicode", "", "latin"] {
        assert_eq!(name.parse::<Spelling>(), Err(Unspelled), "`{name}`");
    }
}

#[test]
fn every_glyph_tile_of_the_grammar_has_an_ascii_spelling()
{
    let grammar = built_in().expect("the built-in grammar builds");
    let mut labels = BTreeSet::new();
    for rule in grammar.rules() {
        tiles(rule.regex().view(), &mut labels);
    }
    let glyphs: BTreeSet<TileLabel> = labels
        .iter()
        .copied()
        .filter(|label| !label.0.is_ascii())
        .collect();
    for &glyph in &glyphs {
        let entry = spelled(glyph)
            .unwrap_or_else(|| panic!("the glyph tile `{}` has no ASCII spelling", glyph.0));
        let ascii = entry.written(Spelling::Ascii);
        assert!(
            ascii.0.is_ascii() && !ascii.0.is_empty(),
            "`{}` is spelled `{}` in ASCII",
            glyph.0,
            ascii.0
        );
    }
    let tabled: BTreeSet<TileLabel> = SPELLED.iter().map(|entry| entry.tile).collect();
    assert_eq!(
        tabled, glyphs,
        "the table names the grammar's glyph tiles and nothing else"
    );
}

#[test]
fn each_glyph_is_written_in_the_spelling_asked()
{
    for (glyph, ascii) in [
        ("≃", "<~>"),
        ("⇝", "~~>"),
        ("≅", "Iso"),
        ("∷", "::"),
        ("ω", "inf"),
    ] {
        let entry = spelled(TileLabel(glyph)).expect("the glyph is tabled");
        assert_eq!(
            (
                entry.written(Spelling::Unicode),
                entry.written(Spelling::Ascii)
            ),
            (LabelText(glyph), LabelText(ascii)),
            "`{glyph}`"
        );
    }
    assert_eq!(Spelling::default(), Spelling::Unicode, "Unicode by default");
    assert_eq!(spelled(TileLabel("->")), None, "an ASCII tile is no glyph");
}

#[test]
fn an_ascii_token_stands_for_its_glyph_and_a_head_for_none()
{
    for entry in SPELLED {
        match entry.ascii {
            Ascii::Token(token) => {
                assert_eq!(aliased(token), Some(entry.tile), "`{}`", token.0);
            },
            Ascii::Head(head) => {
                assert_eq!(
                    aliased(head),
                    None,
                    "`{}` is a call the lowering reads",
                    head.0
                );
            },
        }
        assert_eq!(
            aliased(LabelText(entry.tile.0)),
            None,
            "a glyph is no alias"
        );
    }
    assert_eq!(aliased(LabelText("~>")), None, "nor is another token");
}
