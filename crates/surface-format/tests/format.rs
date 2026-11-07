//! The formatter through its public surface: the corpus kept and formatted
//! once at three page widths — a sample on every pull request, every source
//! under the `sweeps` profile — and each layout rule pinned by a golden at
//! the narrow page (40 columns) and the wide page (100 columns).
//!
//! Regenerate the goldens with `UPDATE_EXPECT=1` and review the diff.

use std::path::Path;

use expect_test::expect_file;
use gandr_surface_format::Form;
use gandr_surface_format::FormatOptions;
use gandr_surface_format::Formatted;
use gandr_surface_format::Layout;
use gandr_surface_format::PageWidth;
use gandr_surface_format::declared_form;
use gandr_surface_format::format;
use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::built_in;
use gandr_surface_parser::parse;
use gandr_surface_syntax::SourceText;

/// The narrow page.
const NARROW: u32 = 40;

/// The wide page.
const WIDE: u32 = 100;

/// The built-in grammar.
///
/// # Specification
/// trivial.
fn grammar() -> Pbg
{
    built_in().expect("the built-in grammar builds")
}

/// `source` formatted at a page of `width` columns.
///
/// # Specification
/// trivial.
fn formatted<'text>(
    grammar: &Pbg,
    source: impl Into<SourceText<'text>>,
    width: impl Into<PageWidth>,
) -> Formatted
{
    let parsed = parse(grammar, source.into()).expect("every source parses");
    let options = FormatOptions {
        page: width.into(),
        ..FormatOptions::default()
    };
    format(grammar, &parsed, options).expect("the source formats")
}

/// The text of `source` formatted at a page of `width` columns.
///
/// # Specification
/// trivial.
fn text<'text>(
    grammar: &Pbg,
    source: impl Into<SourceText<'text>>,
    width: impl Into<PageWidth>,
) -> String
{
    formatted(grammar, source, width).into_text()
}
/// The words in a comment sequence.
///
/// # Specification
///
/// trivial.
#[repr(transparent)]
#[derive(Debug, Eq, PartialEq)]
struct CommentWords<'source>(Vec<&'source str>);

/// Collect the words in comment lines.
///
/// # Specification
///
/// trivial.
fn comment_words(source: SourceText<'_>) -> CommentWords<'_>
{
    let source = <&str>::from(source);
    let mut words = Vec::new();
    for line in source.lines() {
        let line = line.trim_start();
        let body = ["//!", "///", "//"]
            .into_iter()
            .find_map(|marker| line.strip_prefix(marker))
            .unwrap_or_default();
        words.extend(body.strip_prefix(' ').unwrap_or(body).split_whitespace());
    }
    CommentWords(words)
}
/// Find Gandr sources below `roots`.
///
/// # Specification
/// trivial.
fn sources_below(roots: &[&Path]) -> Vec<std::path::PathBuf>
{
    let mut pending: Vec<std::path::PathBuf> =
        roots.iter().map(|root| (*root).to_path_buf()).collect();
    let mut sources = Vec::new();
    while let Some(path) = pending.pop() {
        let entries = std::fs::read_dir(&path).expect("a source directory is readable");
        for entry in entries {
            let entry = entry.expect("a source directory entry is readable");
            let path = entry.path();
            let kind = entry.file_type().expect("a source entry has a type");
            if kind.is_dir() {
                pending.push(path);
            }
            else if !kind.is_dir()
                && path
                    .extension()
                    .is_some_and(|extension| extension == "gandr")
            {
                sources.push(path);
            }
        }
    }
    sources.sort_unstable();
    sources
}

/// The unformatted input `name`, and its goldens at both pages.
///
/// # Specification
/// trivial.
fn golden(name: &Path)
{
    let grammar = grammar();
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests");
    let source =
        std::fs::read_to_string(root.join("unformatted").join(name).with_extension("gandr"))
            .expect("the fixture is readable");
    for (width, page) in [(NARROW, "narrow"), (WIDE, "wide")] {
        let laid = text(&grammar, source.as_str(), width);
        assert_eq!(
            text(&grammar, laid.as_str(), width),
            laid,
            "{} formats once at {width}",
            name.display()
        );
        expect_file![
            root.join("golden")
                .join(format!("{}.{page}.txt", name.display()))
        ]
        .assert_eq(&laid);
    }
}

#[test]
fn a_long_declaration_breaks_its_parameters_before_its_type()
{
    golden(Path::new("declarations"));
}

#[test]
fn a_block_breaks_one_item_per_line_when_it_does_not_fit()
{
    golden(Path::new("blocks"));
}

#[test]
fn attributes_and_documentation_keep_their_lines()
{
    golden(Path::new("attributes"));
}

#[test]
fn a_block_members_documentation_stays_before_its_member()
{
    golden(Path::new("members"));
}

#[test]
fn the_arity_shaped_formers_keep_their_written_spelling()
{
    golden(Path::new("arity"));
}

#[test]
fn the_loop_forms_keep_their_written_spelling()
{
    golden(Path::new("loops"));
    let source = std::fs::read_to_string(
        Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/unformatted/loops.gandr"),
    )
    .expect("the fixture is readable");
    assert_eq!(
        text(&grammar(), source.as_str(), WIDE),
        source,
        "`loop`, `while`, `for`, `break`, `break(v)` and `continue` are their own canonical form"
    );
}

#[test]
fn top_level_forms_and_comments_keep_their_lines()
{
    let grammar = grammar();
    let source =
        include_str!("format/unformatted/top-level-forms-and-comments-keep-their-lines.gandr");
    assert_eq!(
        text(&grammar, source, WIDE),
        "#!/usr/bin/env gandr\n\n// head\ndef a = 1;\ndef b = 2; // trailing\n\n/* own */\n(f a);\n(g b);\n",
        "forms take a line each, a trailing comment stays, a blank line is kept once, and a statement keeps its separator"
    );
    assert_eq!(text(&grammar, "", WIDE), "", "an empty source stays empty");
}

#[test]
fn a_bulleted_head_comment_keeps_its_lines_2918()
{
    let grammar = grammar();
    let source =
        include_str!("format/unformatted/a-bulleted-head-comment-keeps-its-lines-2918.gandr");
    for page in [NARROW, WIDE] {
        assert_eq!(
            text(&grammar, source, page),
            source,
            "a head's `- see:` lines and their indented continuations are never reflowed"
        );
    }
}
#[test]
fn comment_runs_wrap_at_eighty_columns_3589()
{
    let grammar = grammar();
    let source = include_str!("format/unformatted/comment-runs-wrap-at-eighty-columns-3589.gandr");
    let laid = text(&grammar, source, NARROW);
    assert_eq!(
        text(&grammar, laid.as_str(), NARROW),
        laid,
        "comment runs format once"
    );
    assert_eq!(
        comment_words(SourceText::from(source)),
        comment_words(SourceText::from(laid.as_str())),
        "comment runs keep their word sequence"
    );
    assert!(
        laid.lines().any(
            |line| line.starts_with("// The formatter") && line.chars().nth(40_usize).is_some()
        ),
        "comments use their 80-column width beside the narrow page"
    );
    assert!(
        laid.lines()
            .filter(|line| line.trim_start().starts_with("//"))
            .all(|line| {
                line.chars().nth(80_usize).is_none()
                    || line.contains("fenced sentence")
                    || line.contains('|')
                    || line.contains("- see:")
                    || line.contains("- cites:")
                    || line.contains("]:")
            }),
        "each reflowable comment line fits the comment width"
    );
    for continuation in [
        "// fixed comment width.\n",
        "/// fixed comment width.\n",
        "//! fixed comment width.\n",
    ] {
        assert!(
            laid.contains(continuation),
            "each carried piece holds three words"
        );
    }
    assert!(
        laid.contains("//   "),
        "a list continuation uses a hanging indent"
    );
    for data in [
        "// - see: #3589 — The formatter preserves this recorded data line when it exceeds the fixed comment width.\n",
        "// - cites: https://example.invalid/a-very-long-citation-target-that-stays-data \"Author, A Long Citation Title\"\n",
        "// [long-book]: https://example.invalid/a-very-long-reference-target-that-stays-data-and-never-wraps\n",
    ] {
        assert!(
            laid.contains(data),
            "line-oriented comment data stays unchanged"
        );
    }
    assert!(
        laid.contains("// token\n"),
        "a one-token comment line stays unchanged"
    );
    assert!(
        laid.contains(
            r"// ```text
// The formatter keeps this fenced sentence unchanged when the source line extends beyond the fixed comment width.
// ```
"
        ),
        "a fence keeps its lines"
    );
    assert!(
        laid.contains(
            "// | The formatter | keeps this table row | when its source line extends beyond the fixed comment width |\n"
        ),
        "a table row stays unchanged"
    );
}
#[test]
fn corpus_and_std_comment_words_keep_their_sequence_3589()
{
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let paths = [
        root.join("corpus/classifier"),
        root.join("corpus/fragment"),
        root.join("corpus/model"),
        root.join("corpus/pathological"),
        root.join("corpus/pending"),
        root.join("corpus/surface"),
        root.join("library/std"),
    ];
    let roots: Vec<&Path> = paths.iter().map(std::path::PathBuf::as_path).collect();
    let grammar = grammar();
    for path in sources_below(&roots) {
        let source = std::fs::read_to_string(&path).expect("a corpus source is readable");
        let laid = text(&grammar, source.as_str(), WIDE);
        assert_eq!(
            comment_words(SourceText::from(source.as_str())),
            comment_words(SourceText::from(laid.as_str())),
            "{} keeps its comment word sequence",
            path.display()
        );
    }
}

#[test]
fn a_rule_s_freshness_conditions_stay_on_its_line()
{
    let grammar = grammar();
    let source =
        include_str!("format/unformatted/a-rule-s-freshness-conditions-stay-on-its-line.gandr");
    assert_eq!(
        text(&grammar, source, WIDE),
        "theory Gc where {\n  sort Name : Atom;\n  sort Proc : Type;\n  oper nu : (p : bind (a : Name). Proc) --> Proc;\n  rule gc : nu (bind a. q) <=> q where { | a # q | a # q };\n}\n",
        "a theory's members end at `;`, so the comma between two conditions keeps them on the rule's line"
    );
}

#[test]
fn a_clause_s_patterns_stay_on_its_line()
{
    let grammar = grammar();
    let source = include_str!("format/unformatted/a-clause-s-patterns-stay-on-its-line.gandr");
    assert_eq!(
        text(&grammar, source, WIDE),
        source,
        "a bar opens each clause, so the comma between two patterns keeps them on the clause's line"
    );
}

#[test]
fn a_form_written_against_the_one_before_starts_its_own_line()
{
    let grammar = grammar();
    assert_eq!(
        text(&grammar, "def a = 1 ;def b = 2 ;", WIDE),
        "def a = 1;\ndef b = 2;\n",
        "only a separator touches the form it ends"
    );
}

#[test]
fn the_printer_decides_every_inner_space()
{
    let grammar = grammar();
    let source = include_str!("format/unformatted/the-printer-decides-every-inner-space.gandr");
    assert_eq!(
        text(&grammar, source, WIDE),
        "@[ checks ]\n\
         def f(x : Integer, y : Integer) -> -F Integer { return x + y; }\n\
         def p = *{a = 1, b = - 2};\n\
         def q : +{A : Integer, B : Unit};\n\
         def g[r : Row](k : Integer) -> [Partial | r] Unit { pure *{} }\n\
         def l = fun (x) { x };\n\
         def c = thunk { fun (x) { x } };\n\
         def m = r.a[0];\n\
         module M :> *{ type T } where { type T = Integer; }\n\
         theory S where { boundary Q { p, q }; face left = {p, q}; }\n\
         theory Kit.Shape where { sort T : Type; }\n\
         module Kit.Made : Model(Kit.Shape) where { type T = Integer; }\n",
        "each space inside a line is the printer's, whatever the source wrote"
    );
}

#[test]
fn a_terminator_touches_the_form_it_ends()
{
    let grammar = grammar();
    let source = include_str!("format/unformatted/a-terminator-touches-the-form-it-ends.gandr");
    assert_eq!(
        text(&grammar, source, WIDE),
        "import \"./base.gandr\" as prelude;\n\
         world seat;\n\
         def a = 1;\n\
         def f(a : Type, y : a) -> -F a {\n  let x : a = same a y;\n  loop { break };\n  return x\n}\n\
         def t = *{1, 2};\n",
        "no space stands before a `;`, whatever ends the form it closes"
    );
}

#[test]
fn a_separator_written_on_the_next_line_joins_its_statement()
{
    let grammar = grammar();
    assert_eq!(
        text(
            &grammar,
            include_str!(
                "format/unformatted/a-separator-written-on-the-next-line-joins-its-statement.gandr"
            ),
            WIDE
        ),
        "(f a);\n(g b);\n",
        "a separator after a break or a blank line ends the statement on its line"
    );
}

#[test]
fn a_continuation_line_indents_under_its_statement()
{
    let grammar = grammar();
    let source =
        include_str!("format/unformatted/a-continuation-line-indents-under-its-statement.gandr");
    assert_eq!(
        text(&grammar, source, WIDE),
        "def f(x : Integer) -> -F Integer {\n  let y = inc x\n    ;\n  let z = inc y;\n  return z\n}\n",
        "a line indented past its statement continues it; one after a separator starts a statement"
    );
}

/// #2950: before the fix, a block opening with a comment at column 0 read its
/// first member, indented deeper than the comment, as the comment's
/// continuation, and laid it two columns too deep.
#[test]
fn a_member_after_a_column_zero_comment_starts_a_statement_2950()
{
    let grammar = grammar();
    for (source, expected) in [
        (
            include_str!(
                "format/unformatted/a-member-after-a-column-zero-comment-starts-a-statement-2950-1.gandr"
            ),
            "/// T.\ntheory T where {\n  /// The state.\n  sort S : Type+;\n  oper get : (k : S) --> S;\n}\n",
        ),
        (
            include_str!(
                "format/unformatted/a-member-after-a-column-zero-comment-starts-a-statement-2950-2.gandr"
            ),
            "/// N.\ndata N : Type where {\n  /// Zero.\n  | Z : N\n  | S : (n : N) --> N\n}\n",
        ),
    ] {
        assert_eq!(
            text(&grammar, source, WIDE),
            expected,
            "the first member stands at the block's indentation, under its comment"
        );
    }
}

/// #5202: before the fix, a juxtaposed spine that did not fit the page stood
/// on one line past the page, or broke inside a bracket of an operand. Now a
/// spine that does not fit stands as its head and then each operand on a line
/// of its own, two columns deeper than the head. A spine that fits stays on
/// one line, and a bracket in an operand stays whole on the operand's line.
#[test]
fn a_juxtaposed_spine_breaks_one_operand_a_line_5202()
{
    let grammar = grammar();
    for (source, expected, why) in [
        (
            "def a = f x y;\n",
            "def a = f x y;\n",
            "a spine that fits stays on one line",
        ),
        (
            "def spine = compose alpha beta gamma delta epsilon;\n",
            "def spine = compose\n  alpha\n  beta\n  gamma\n  delta\n  epsilon;\n",
            "a spine that does not fit breaks before each operand",
        ),
        (
            "def nested = f (compose[4, 9] alpha beta) (gamma delta epsilon zeta);\n",
            "def nested = f\n  (compose[4, 9] alpha beta)\n  (gamma delta epsilon zeta);\n",
            "a bracket in an operand stays whole on the operand's line",
        ),
        (
            include_str!(
                "format/unformatted/a-juxtaposed-spine-breaks-one-operand-a-line-5202.gandr"
            ),
            "def go() -> -F Integer =\n  become apply\n    alpha\n    beta\n    gamma\n    delta\n    epsilon\n",
            "in a layout block the operands stand deeper than the block's column",
        ),
    ] {
        let laid = text(&grammar, source, NARROW);
        assert_eq!(laid, expected, "{why}");
        assert_eq!(
            text(&grammar, laid.as_str(), NARROW),
            laid,
            "{why}, and formats once"
        );
    }
}

/// #5326: a type's juxtaposition broke as an expression's spine does, so a
/// signature's type stood broken at the column of the body after it, and the
/// formatter refused the source as changed in meaning. Now a type's spine
/// keeps its line, as the brackets around its operands do.
#[test]
fn a_type_s_spine_keeps_its_line_in_a_signature_5326()
{
    let grammar = grammar();
    let source =
        include_str!("format/unformatted/a-type-s-spine-keeps-its-line-in-a-signature-5326.gandr");
    let laid = text(&grammar, source, NARROW);
    assert_eq!(
        laid, source,
        "the type's spine and the body keep their lines"
    );
    assert_eq!(
        text(&grammar, laid.as_str(), NARROW),
        laid,
        "and the layout formats once"
    );
}

/// #5665: a postfix form after a call in call form takes the whole call, so
/// the formatter keeps the call's group against its head there. A space
/// would give the postfix form the group alone. A call that no postfix form
/// takes is spaced as a juxtaposition is, and a group after a space stays an
/// argument of its own. A broken spine keeps the call's group on the line of
/// its operand.
#[test]
fn a_call_in_call_form_keeps_its_group_before_a_postfix_form_5665()
{
    let grammar = grammar();
    for (source, expected, why) in [
        (
            "def a = mk(x).l;\n",
            "def a = mk(x).l;\n",
            "the projection's call keeps its group against its head",
        ),
        (
            "def a = mk (x).l;\n",
            "def a = mk (x).l;\n",
            "a group after a space stays an argument of its own",
        ),
        (
            "def a = mk(x);\n",
            "def a = mk (x);\n",
            "a call that no postfix form takes is spaced",
        ),
        (
            "def a = g  mk(x).#[i];\n",
            "def a = g mk(x).#[i];\n",
            "in a spine only the call form's tile touches",
        ),
        (
            "def spine = compose alpha beta gamma(delta).l;\n",
            "def spine = compose\n  alpha\n  beta\n  gamma(delta).l;\n",
            "a broken spine keeps the group on its operand's line",
        ),
    ] {
        let laid = text(&grammar, source, NARROW);
        assert_eq!(laid, expected, "{why}");
        assert_eq!(
            text(&grammar, laid.as_str(), NARROW),
            laid,
            "{why}, and formats once"
        );
    }
}

/// #5528: before the fix, a spine broke before its operands, but its head
/// kept a bracket whole on one line past the page. A second pass read the
/// operand's line as a continuation, and broke the bracket. Now the broken
/// spine's head breaks a bracket that does not fit, so the layout formats once.
#[test]
fn a_broken_spine_s_head_breaks_a_bracket_past_the_page_5528()
{
    let grammar = grammar();
    let source = "def twiceRun() -> Integer { twice[.m = Integer, .combine = Adding.plus] 3 }\n";
    let laid = text(&grammar, source, NARROW);
    assert_eq!(
        laid,
        "def twiceRun() -> Integer {\n  twice[\n    .m = Integer,\n    .combine = Adding.plus\n  ]\n    3\n}\n",
        "the head's bracket breaks one field a line, and the operand stands deeper"
    );
    assert_eq!(
        text(&grammar, laid.as_str(), NARROW),
        laid,
        "and the layout formats once"
    );
}

#[test]
fn strings_shell_blocks_and_holes_are_copied_as_written()
{
    let grammar = grammar();
    let source = include_str!(
        "format/unformatted/strings-shell-blocks-and-holes-are-copied-as-written.gandr"
    );
    assert_eq!(
        text(&grammar, source, NARROW),
        "def s = \"a  ${  b }\tc\";\ndef h = #!{\n    printf 'hi'\n};\ndef k = (?hole);\n",
        "a string's, a shell block's and a hole's bytes are their own"
    );
}

#[test]
fn a_repaired_form_is_copied_as_written()
{
    let grammar = grammar();
    let source = include_str!("format/unformatted/a-repaired-form-is-copied-as-written.gandr");
    let formatted = formatted(&grammar, source, WIDE);
    assert_eq!(
        <&str>::from(formatted.text()),
        "def z = 0;\ndef   a = (1 ;\ndef b = 2;\n",
        "the repaired form keeps its bytes and its neighbours on either side are laid out"
    );
    let layouts: Vec<Layout> = formatted
        .pieces()
        .iter()
        .map(|piece| piece.layout)
        .collect();
    assert_eq!(layouts, [
        Layout::Formatted,
        Layout::Repaired,
        Layout::Formatted
    ]);
}

#[test]
fn the_source_line_ending_is_kept()
{
    let grammar = grammar();
    let source = include_str!("format/unformatted/the-source-line-ending-is-kept.gandr");
    assert_eq!(
        text(&grammar, source, NARROW),
        "def f() -> -F Integer {\r\n  return 1\r\n}\r\n",
        "carriage returns stay with their line feeds"
    );
}

#[test]
fn a_source_split_evenly_between_endings_keeps_line_feeds()
{
    let grammar = grammar();
    assert_eq!(
        text(
            &grammar,
            include_str!(
                "format/unformatted/a-source-split-evenly-between-endings-keeps-line-feeds.gandr"
            ),
            WIDE
        ),
        "def a = 1;\ndef b = 2;\n",
        "carriage returns win only when most breaks carry them"
    );
}

#[test]
fn pieces_place_each_top_level_form()
{
    let grammar = grammar();
    let source = include_str!("format/unformatted/pieces-place-each-top-level-form.gandr");
    let formatted = formatted(&grammar, source, WIDE);
    let text = <&str>::from(formatted.text());
    let spans: Vec<(&str, &str)> = formatted
        .pieces()
        .iter()
        .map(|piece| {
            let source_span = usize::from(piece.source.start()) .. usize::from(piece.source.end());
            let formatted_span =
                usize::from(piece.formatted.start()) .. usize::from(piece.formatted.end());
            (
                source.get(source_span).unwrap_or_default(),
                text.get(formatted_span).unwrap_or_default(),
            )
        })
        .collect();
    assert_eq!(
        spans,
        [
            ("def  a = 1 ;  // note", "def a = 1; // note"),
            ("def b = 2 ;", "def b = 2;")
        ],
        "a form's piece runs from its first token to its trailing comment"
    );
}

/// A source in the core's explicit spelling, its head declaring it:
/// every run, force and thunk written out.
const EXPLICIT: &str = include_str!("format/unformatted/explicit.gandr");

/// #492: the gate's invariant made visible. The formatter keeps every
/// token, so a source spelled in the explicit form comes back in the
/// explicit form, laid out, under every option: its declaration wins over
/// an option asking for the sugared form. A source that opens with a `rec`
/// group declares it on the group's first declaration, where a block before
/// `rec` would refuse the module.
#[test]
fn an_explicit_source_keeps_its_explicit_spelling()
{
    let grammar = grammar();
    let kept = "@[ form(explicit) ]\ndef shown : +U (-F Integer);\ndef shown = thunk { let n = \
                force one; become read n };\n";
    let imported = "import \"./base.gandr\" ;\n";
    let imported_kept = "import \"./base.gandr\";\n";
    let grouped = include_str!(
        "format/unformatted/an-explicit-source-keeps-its-explicit-spelling-grouped.gandr"
    );
    let grouped_kept = "rec {\n  @[ form(explicit) ]\n  def shown : +U (-F Integer);\n  def \
                        shown = thunk { let n = force one; become read n };\n}\n";
    for (written, expected) in [
        (String::from(EXPLICIT), String::from(kept)),
        (
            format!("{imported}{EXPLICIT}"),
            format!("{imported_kept}{kept}"),
        ),
        (
            format!("{imported}{grouped}"),
            format!("{imported_kept}{grouped_kept}"),
        ),
    ] {
        let parsed =
            parse(&grammar, SourceText::from(written.as_str())).expect("the source parses");
        assert_eq!(
            declared_form(&grammar, &parsed),
            Some(Form::Explicit),
            "the head declares the explicit form"
        );
        for form in [Form::Source, Form::Explicit, Form::Sugared] {
            let options = FormatOptions {
                form,
                ..FormatOptions::default()
            };
            assert_eq!(
                format(&grammar, &parsed, options).map(Formatted::into_text),
                Ok(expected.clone()),
                "{form}: the explicit spelling is kept, its declaration after any import"
            );
        }
    }
    let sugared = include_str!(
        "format/unformatted/an-explicit-source-keeps-its-explicit-spelling-sugared.gandr"
    );
    for (written, declared) in [
        (sugared, Some(Form::Sugared)),
        ("def shown : () -> Integer ;\n", None),
    ] {
        let parsed = parse(&grammar, SourceText::from(written)).expect("the source parses");
        assert_eq!(declared_form(&grammar, &parsed), declared, "{written}");
    }
    assert_eq!(
        [Form::Source, Form::Explicit, Form::Sugared].map(|form| form.to_string()),
        ["source", "explicit", "sugared"],
        "each form is named as the option and the declaration spell it"
    );
}

/// The formatter's sweep: every corpus source keeps its meaning and
/// formats once at three page widths.
mod sweeps
{
    use gandr_workflow_sweep::Sample;
    use gandr_workflow_sweep::SampleName;
    use gandr_workflow_sweep::SampleSize;
    use gandr_workflow_sweep::Sweep;
    use gandr_workflow_sweep::corpus;

    use super::NARROW;
    use super::WIDE;
    use super::grammar;
    use super::text;

    /// The sample: sixty-four sources, ranked by their BLAKE3 digest
    /// under this name, at least one of each corpus class — `strict` and
    /// each directory below `fixture` — and, in the companion, the sources
    /// the change adds or modifies beside them (`gandr-workflow-sweep`). The
    /// `sweeps` profile formats every source.
    const SAMPLE: Sample = Sample {
        name: SampleName("every_source_keeps_its_meaning_and_formats_once"),
        size: SampleSize(64),
    };

    #[test]
    fn every_source_keeps_its_meaning_and_formats_once()
    {
        formats_once(&Sweep::asked().expect("the run's sweep resolves"));
    }

    /// The change's sources beside the fixed set (#4654).
    #[test]
    fn every_source_keeps_its_meaning_and_formats_once_changed()
    {
        formats_once(&Sweep::asked().expect("the run's sweep resolves").changed());
    }

    /// Every source `sweep` visits formats once at each width, keeping its
    /// meaning.
    ///
    /// # Specification
    /// trivial.
    fn formats_once(sweep: &Sweep)
    {
        let grammar = grammar();
        let sources = sweep.visit(SAMPLE, &corpus::sources().expect("the corpus reads"));
        assert!(
            sources.len() >= sweep.drawn(SAMPLE).0,
            "the sample is drawn: {}",
            sources.len()
        );
        for source in sources {
            let text_of =
                std::fs::read_to_string(&source.path).expect("a corpus source is readable");
            for width in [NARROW, 80, WIDE] {
                // The formatter itself refuses a text whose digest, tokens
                // or comments differ from the source's.
                let once = text(&grammar, text_of.as_str(), width);
                assert_eq!(
                    text(&grammar, once.as_str(), width),
                    once,
                    "{} formats once at {width}",
                    source.name
                );
            }
        }
    }
}
