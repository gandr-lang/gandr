//! The outline that a reading answers: its symbols, its folding ranges and
//! its selection ranges, each read through [`Reading`] over a held text.

use gandr_surface_render_remote::LineIndex;
use gandr_surface_syntax::SourceText;
use serde_json::Value;

use crate::position::Character;
use crate::position::Line;
use crate::position::Position;
use crate::position::Range;
use crate::protocol::DocumentSymbols;
use crate::protocol::SelectionRange;
use crate::reading::Reading;

/// `range` spelled `line:character-line:character`.
///
/// # Specification
/// trivial.
fn spelled(range: Range) -> String
{
    let at = |position: Position| {
        let value = serde_json::to_value(position).expect("a position encodes");
        let read = |field| value.get(field).and_then(Value::as_u64).unwrap_or(u64::MAX);
        format!("{}:{}", read("line"), read("character"))
    };
    format!("{}-{}", at(range.start), at(range.end))
}

/// The position at `line` and `character`.
///
/// # Specification
/// trivial.
fn at(
    line: Line,
    character: Character,
) -> Position
{
    Position { line, character }
}

/// Every symbol of `symbols` in order, one line each: its depth, name,
/// kind, range and selection range.
///
/// # Specification
/// trivial.
fn outline(symbols: &DocumentSymbols) -> Vec<String>
{
    let mut depths: Vec<usize> = Vec::new();
    let mut lines = Vec::new();
    for symbol in &symbols.0 {
        let depth = symbol
            .holder
            .and_then(|holder| depths.get(holder))
            .map_or(0_usize, |depth| depth.saturating_add(1));
        depths.push(depth);
        let kind = serde_json::to_value(symbol.kind).expect("a kind encodes");
        lines.push(format!(
            "{}{} {kind} {} at {}",
            "  ".repeat(depth),
            symbol.name,
            spelled(symbol.range),
            spelled(symbol.selection_range),
        ));
    }
    lines
}

/// The ranges of `selection`, innermost first.
///
/// # Specification
/// trivial.
fn chain(selection: &SelectionRange) -> Vec<String>
{
    selection.ranges.iter().copied().map(spelled).collect()
}

/// A root form that declares nothing is an `Event` symbol named by what it
/// writes: a final expression over its attribute block and its `;`, a
/// stray, and a run of attribute blocks no form follows; an import and
/// a `rec` group writing a declaration are none (#2073).
#[test]
fn a_root_form_that_declares_nothing_is_a_symbol_2073()
{
    let targeted = include_str!(
        "outline/unformatted/a-root-form-that-declares-nothing-is-a-symbol-2073-targeted.gandr"
    );
    let answered = Reading::of(SourceText::from(targeted)).symbols();
    assert_eq!(outline(&answered), [
        "a 12 0:0-0:11 at 0:4-0:5",
        "thunk { … } 24 1:0-4:3 at 2:0-4:1",
    ]);
    assert_eq!(
        answered
            .0
            .iter()
            .map(|symbol| symbol.deprecated)
            .collect::<Vec<_>>(),
        [false, true],
        "the block before the final expression marks it"
    );
    let strays = include_str!(
        "outline/unformatted/a-root-form-that-declares-nothing-is-a-symbol-2073-strays.gandr"
    );
    assert_eq!(outline(&Reading::of(SourceText::from(strays)).symbols()), [
        "1 24 1:0-1:3 at 1:0-1:1",
        "b 12 3:2-3:13 at 3:6-3:7",
        "b 24 5:0-5:3 at 5:0-5:1",
        "@[checks] 24 6:0-7:11 at 6:0-6:11",
    ]);
}

/// A family and a theory written as layout blocks hold their members as
/// their braced spellings do, and a word at column zero after the block
/// is no member of it.
#[test]
fn a_layout_block_holds_its_members_4853()
{
    // Each symbol's nesting, name and kind, its ranges left out: the two
    // spellings place them at different bytes.
    let held = |source: &str| -> Vec<String> {
        outline(&Reading::of(SourceText::from(source)).symbols())
            .iter()
            .map(|line| {
                let indent = line.len() - line.trim_start().len();
                let mut words = line.split_whitespace();
                let name = words.next().unwrap_or_default();
                let kind = words.next().unwrap_or_default();
                format!("{}{name} {kind}", " ".repeat(indent))
            })
            .collect()
    };
    for (layout, braced) in [
        (
            include_str!("outline/unformatted/a-layout-block-holds-its-members-4853-1.gandr"),
            include_str!("outline/unformatted/a-layout-block-holds-its-members-4853-2.gandr"),
        ),
        (
            include_str!("outline/unformatted/a-layout-block-holds-its-members-4853-3.gandr"),
            include_str!("outline/unformatted/a-layout-block-holds-its-members-4853-4.gandr"),
        ),
    ] {
        let braced_symbols = held(braced);
        assert!(
            braced_symbols.len() > 3,
            "the braced spelling holds its members: {braced_symbols:?}"
        );
        assert_eq!(held(layout), braced_symbols, "{layout}");
    }
}

#[test]
fn declarations_nest_as_symbols()
{
    let source = include_str!("outline/fixtures/nested.gandr");
    let answered = Reading::of(SourceText::from(source)).symbols();
    assert_eq!(outline(&answered), [
        "twice 12 1:0-3:10 at 2:4-2:9",
        "answer 12 4:0-4:16 at 4:4-4:10",
        "Color 10 5:0-6:41 at 6:5-6:10",
        "  Red 9 6:28-6:39 at 6:28-6:31",
        "Outer 2 7:0-10:17 at 7:7-7:12",
        "  inner 12 8:2-8:16 at 8:6-8:11",
        "  Nested 2 9:2-10:17 at 9:9-9:15",
        "    deep 12 10:4-10:17 at 10:8-10:12",
        "seat 14 11:0-11:11 at 11:6-11:10",
    ]);
    // The wire tree: each held symbol under its holder's `children`.
    let wire = serde_json::to_value(&answered).expect("the symbols encode");
    let names = |value: &Value| -> Vec<String> {
        value.as_array().map_or_default(|symbols| {
            symbols
                .iter()
                .filter_map(|symbol| symbol.get("name").and_then(Value::as_str))
                .map(str::to_owned)
                .collect()
        })
    };
    let outer = wire.get(3_usize);
    let nested = outer
        .and_then(|outer| outer.get("children"))
        .and_then(|children| children.get(1_usize));
    assert_eq!(names(&wire), ["twice", "answer", "Color", "Outer", "seat"]);
    assert_eq!(
        outer.and_then(|outer| outer.get("children")).map(names),
        Some(vec!["inner".to_owned(), "Nested".to_owned()])
    );
    assert_eq!(
        nested.and_then(|nested| nested.get("children")).map(names),
        Some(vec!["deep".to_owned()])
    );
    assert!(
        wire.get(0_usize)
            .is_some_and(|twice| twice.get("children").is_none()),
        "a symbol holding none writes no children"
    );
}

/// A declaration an attribute block before it marks `deprecated` is
/// tagged so on the wire, whichever block names it and whatever its
/// payload; a `deprecated` word inside another attribute's payload marks
/// nothing, and neither does a module member's block mark its holder.
#[test]
fn a_deprecated_declaration_is_tagged()
{
    let source = include_str!("outline/unformatted/a-deprecated-declaration-is-tagged.gandr");
    let answered = Reading::of(SourceText::from(source)).symbols();
    assert_eq!(
        answered
            .0
            .iter()
            .map(|symbol| (symbol.name.as_str(), symbol.deprecated))
            .collect::<Vec<_>>(),
        [
            ("bare", true),
            ("recorded", true),
            ("named", false),
            ("Holder", false),
            ("member", true),
            ("plain", false),
        ]
    );
    let wire = serde_json::to_value(&answered).expect("the symbols encode");
    assert_eq!(
        wire.pointer("/0/tags"),
        Some(&serde_json::json!([1_u8])),
        "a deprecated symbol carries the protocol's `Deprecated` tag"
    );
    assert_eq!(
        wire.pointer("/3/children/0/tags"),
        Some(&serde_json::json!([1_u8])),
        "a member is tagged where it nests"
    );
    assert!(
        wire.pointer("/2/tags").is_none(),
        "an unmarked symbol carries no tags"
    );
}

/// Each declaration carries what it writes between its name and its body
/// or definition, its layout collapsed and a leading `:` dropped; one
/// that writes nothing there, a member among them, carries none. A dotted
/// name is the symbol's whole name (#2687).
#[test]
fn each_symbol_carries_what_it_writes_after_its_name()
{
    let source = include_str!("outline/fixtures/details.gandr");
    let details: Vec<(String, Option<String>)> = Reading::of(SourceText::from(source))
        .symbols()
        .0
        .into_iter()
        .map(|symbol| (symbol.name, symbol.detail))
        .collect();
    let row = |name: &str, detail: Option<&str>| (name.to_owned(), detail.map(str::to_owned));
    assert_eq!(details, [
        row("twice", Some("(x : Integer) -> -F Integer")),
        row("answer", None),
        row("later", Some("Integer")),
        row("Color", Some("Type")),
        row("Red", Some("Color")),
        row("Shapes", None),
        row("M", Some("Type")),
        row("mul", Some("(x : M, y : M) --> M")),
        row("spin", Some("(data s : M) ==> (out : M)")),
        row("Plain", None),
        row("one", None),
        row("seat", None),
        row("Kit.Tools", Some("*{two : Integer}")),
        row("two", None),
    ]);
}

/// A theory's members nest under it, one of each kind with its own kind;
/// a name list's braces and `;` stay inside its boundary or face; an
/// `include` is no member; and a codata declaration's observations nest
/// under it.
#[test]
fn a_theory_holds_its_members()
{
    let source = include_str!("outline/unformatted/a-theory-holds-its-members.gandr");
    assert_eq!(outline(&Reading::of(SourceText::from(source)).symbols()), [
        "Shapes 11 0:0-9:1 at 0:7-0:13",
        "  M 26 1:2-1:16 at 1:7-1:8",
        "  Unit 9 2:2-2:16 at 2:7-2:11",
        "  mul 6 3:2-3:34 at 3:7-3:10",
        "  size 8 4:2-4:27 at 4:6-4:10",
        "  assoc 7 5:2-5:51 at 5:7-5:12",
        "  Square 26 6:2-6:37 at 6:11-6:17",
        "  left 8 7:2-7:25 at 7:7-7:11",
        "  Cell 26 8:2-8:31 at 8:6-8:10",
        "Monoid 11 10:0-13:1 at 10:7-10:13",
        "  one 6 12:2-12:22 at 12:7-12:10",
        "Stream 23 14:0-17:1 at 14:7-14:13",
        "  head 8 15:2-15:11 at 15:2-15:6",
        "  tail 8 16:2-16:16 at 16:2-16:6",
    ]);
}

#[test]
fn multi_line_forms_and_documentation_fold()
{
    let source = include_str!("outline/unformatted/multi-line-forms-and-documentation-fold.gandr");
    let answered: Vec<(u64, u64, Option<&str>, Option<String>)> =
        Reading::of(SourceText::from(source))
            .folds()
            .iter()
            .map(|fold| {
                let value = serde_json::to_value(fold).expect("a fold encodes");
                let line = |field| value.get(field).and_then(Value::as_u64).unwrap_or(u64::MAX);
                let text = value
                    .get("collapsedText")
                    .and_then(Value::as_str)
                    .map(str::to_owned);
                (line("startLine"), line("endLine"), fold.kind, text)
            })
            .collect();
    let shown = |text: &str| Some(text.to_owned());
    assert_eq!(
        answered,
        [
            (0, 1, Some("comment"), None),
            (2, 4, None, shown("def f(x : Integer) -> -F Integer { … }")),
            (6, 7, Some("comment"), None),
            (9, 16, None, shown("theory T where { … }")),
            (11, 13, None, shown("  boundary Square { … }")),
            (14, 15, None, shown("  oper mul : (M, M) --> M;")),
            (17, 18, None, shown("def k = …;")),
        ],
        "documentation, the function, the block comment, the theory, its multi-line \
             members and a definition after `=` fold, each form showing what it writes \
             before its body; the one-line forms and members do not"
    );
}

/// A form whose block follows its tile holds the block as a form of its
/// own, and folds at that block's `{` as at its own.
#[test]
fn a_form_folds_at_the_brace_of_its_shared_block()
{
    let source =
        include_str!("outline/unformatted/a-form-folds-at-the-brace-of-its-shared-block.gandr");
    let answered: Vec<(u64, u64, Option<String>)> = Reading::of(SourceText::from(source))
        .folds()
        .iter()
        .map(|fold| {
            let value = serde_json::to_value(fold).expect("a fold encodes");
            let line = |field| value.get(field).and_then(Value::as_u64).unwrap_or(u64::MAX);
            let text = value
                .get("collapsedText")
                .and_then(Value::as_str)
                .map(str::to_owned);
            (line("startLine"), line("endLine"), text)
        })
        .collect();
    assert_eq!(
        answered,
        [
            (0, 3, Some("def f = …;".to_owned())),
            (1, 3, Some("  thunk { … }".to_owned())),
        ],
        "the thunk shows what it writes before its block's brace"
    );
}

#[test]
fn a_selection_grows_from_the_innermost_form()
{
    let source = SourceText::from("def f = g (10) ;\n");
    let answered = Reading::of(source).selections(&LineIndex::new(source.as_ref().into()), &[
        at(Line::from(0), Character::from(12)),
        at(Line::from(0), Character::from(5)),
    ]);
    let chains: Vec<Vec<String>> = answered.iter().map(chain).collect();
    assert_eq!(
        chains.first().map(|first| first.first().cloned()),
        Some(Some("0:11-0:13".to_owned())),
        "inside the argument, the number is selected first: {chains:?}"
    );
    assert_eq!(
        chains.get(1).map(|second| second.first().cloned()),
        Some(Some("0:4-0:5".to_owned())),
        "at the end of a name, the name is selected first: {chains:?}"
    );
    for ranges in &chains {
        assert_eq!(
            ranges.last().map(String::as_str),
            Some("0:0-1:0"),
            "every chain ends at the whole document: {chains:?}"
        );
        assert!(
            ranges.windows(2).all(|pair| pair.first() != pair.get(1)),
            "no range is given twice: {chains:?}"
        );
    }
    let between = Reading::of(source).selections(&LineIndex::new(source.as_ref().into()), &[at(
        Line::from(0),
        Character::from(13),
    )]);
    assert_eq!(
        between
            .iter()
            .map(chain)
            .next()
            .and_then(|chain| chain.first().cloned()),
        Some("0:13-0:14".to_owned()),
        "where one token ends and the next starts, the one starting is selected"
    );
    let theory = SourceText::from(include_str!(
        "outline/unformatted/a-selection-grows-from-the-innermost-form-theory.gandr"
    ));
    let member = Reading::of(theory).selections(&LineIndex::new(theory.as_ref().into()), &[at(
        Line::from(2),
        Character::from(8),
    )]);
    assert_eq!(
        member.iter().map(chain).next(),
        Some(vec![
            "2:7-2:10".to_owned(),
            "2:2-2:27".to_owned(),
            "0:0-3:1".to_owned(),
            "0:0-4:0".to_owned()
        ]),
        "a theory member's name grows to its member before the theory"
    );
}
