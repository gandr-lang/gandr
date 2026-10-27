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

/// The fixture `name`, and its goldens at both pages.
///
/// # Specification
/// trivial.
fn golden(name: &Path)
{
    let grammar = grammar();
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests");
    let source = std::fs::read_to_string(root.join("fixtures").join(name).with_extension("gandr"))
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
        Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/loops.gandr"),
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
    let source = "#!/usr/bin/env gandr\n\n\n// leading\ndef a = 1 ; def b = 2 ; // trailing\n\n\n\n/* own */\nf(a)   ;\ng(b);";
    assert_eq!(
        text(&grammar, source, WIDE),
        "#!/usr/bin/env gandr\n\n// leading\ndef a = 1;\ndef b = 2; // trailing\n\n/* own */\nf(a);\ng(b);\n",
        "forms take a line each, a trailing comment stays, a blank line is kept once, and a statement keeps its separator"
    );
    assert_eq!(text(&grammar, "", WIDE), "", "an empty source stays empty");
}

#[test]
fn a_bulleted_head_comment_keeps_its_lines_2918()
{
    let grammar = grammar();
    let source = "// Pairs sum their halves, read back by every reader of the corpus.\n//\n// Why.\n//\n// How.\n//\n// - see: #1 — not implemented: a long clause that runs past the narrow page\n//   and wraps onto an indented line\n// - see: `pathological/a.gandr` — the refusal\n\n/// The pair. Its sum.\ndef a = 1;\n";
    for page in [NARROW, WIDE] {
        assert_eq!(
            text(&grammar, source, page),
            source,
            "a head's `- see:` lines and their indented continuations are never reflowed"
        );
    }
}

#[test]
fn a_rule_s_freshness_conditions_stay_on_its_line()
{
    let grammar = grammar();
    let source = "theory Gc {\n  sort Name : Atom;\n  sort Proc : Type;\n  oper nu : (p : bind (a : Name) . Proc) --> Proc;\n  rule gc : nu(bind a . q) <=> q where a # q, a # q;\n}\n";
    assert_eq!(
        text(&grammar, source, WIDE),
        "theory Gc {\n  sort Name : Atom;\n  sort Proc : Type;\n  oper nu : (p : bind (a : Name). Proc) --> Proc;\n  rule gc : nu(bind a. q) <=> q where a # q, a # q;\n}\n",
        "a theory's members end at `;`, so the comma between two conditions keeps them on the rule's line"
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
    let source = "@[checks]\n\
                  def  f ( x:Integer , y : Integer ) -> -F Integer{ return x+y ;}\n\
                  def p = #{ a = 1 , b = - 2 } ;\n\
                  def q : +{ A : Integer , B : Unit } ;\n\
                  def g @[ r : Row ]( k : Integer ) -> [ Div | r ] Unit { pure unit }\n\
                  def l = \\ x . x ;\n\
                  def c = thunk { fn( x ) { x } } ;\n\
                  def m = r . a [ 0 ] ;\n\
                  module M :> #{type T} { type T = Integer ; }\n\
                  theory S { shape Q : 2 {left = { 0 , 1 } ;} ; }\n\
                  theory Kit . Shape { sort T : Type ; }\n\
                  module Kit . Made : Model( Kit . Shape ) { type T = Integer ; }\n";
    assert_eq!(
        text(&grammar, source, WIDE),
        "@[ checks ]\n\
         def f(x : Integer, y : Integer) -> -F Integer { return x + y; }\n\
         def p = #{a = 1, b = -2};\n\
         def q : +{A : Integer, B : Unit};\n\
         def g @[r : Row] (k : Integer) -> [Div | r] Unit { pure unit }\n\
         def l = \\x. x;\n\
         def c = thunk { fn (x) { x } };\n\
         def m = r.a[0];\n\
         module M :> #{ type T } { type T = Integer; }\n\
         theory S { shape Q : 2 { left = {0, 1}; }; }\n\
         theory Kit.Shape { sort T : Type; }\n\
         module Kit.Made : Model(Kit.Shape) { type T = Integer; }\n",
        "each space inside a line is the printer's, whatever the source wrote"
    );
}

#[test]
fn a_terminator_touches_the_form_it_ends()
{
    let grammar = grammar();
    let source = "import \"./base.gandr\" as prelude ;\n\
                  world seat ;\n\
                  def a = 1 ;\n\
                  def f(a : Type, y : a) -> -F a {\n  run x : a <- same(a, y) ;\n  loop { break } ;\n  return x\n}\n\
                  def t = (1, 2) ;\n";
    assert_eq!(
        text(&grammar, source, WIDE),
        "import \"./base.gandr\" as prelude;\n\
         world seat;\n\
         def a = 1;\n\
         def f(a : Type, y : a) -> -F a {\n  run x : a <- same(a, y);\n  loop { break };\n  return x\n}\n\
         def t = (1, 2);\n",
        "no space stands before a `;`, whatever ends the form it closes"
    );
}

#[test]
fn a_separator_written_on_the_next_line_joins_its_statement()
{
    let grammar = grammar();
    assert_eq!(
        text(&grammar, "f(a)\n;\ng(b)\n\n;", WIDE),
        "f(a);\ng(b);\n",
        "a separator after a break or a blank line ends the statement on its line"
    );
}

#[test]
fn a_continuation_line_indents_under_its_statement()
{
    let grammar = grammar();
    let source = "def f(x : Integer) -> -F Integer {\nrun y <- inc(x)\n      ;\n         run z <- inc(y);\n  return z\n}\n";
    assert_eq!(
        text(&grammar, source, WIDE),
        "def f(x : Integer) -> -F Integer {\n  run y <- inc(x)\n    ;\n  run z <- inc(y);\n  return z\n}\n",
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
            "/// T.\ntheory T {\n/// The state.\n  sort S : Type+;\n  oper get : (k : S) --> S;\n}\n",
            "/// T.\ntheory T {\n  /// The state.\n  sort S : Type+;\n  oper get : (k : S) --> S;\n}\n",
        ),
        (
            "/// N.\ndata N : Type {\n/// Zero.\n  Z : N;\n  S : (n : N) --> N;\n}\n",
            "/// N.\ndata N : Type {\n  /// Zero.\n  Z : N;\n  S : (n : N) --> N;\n}\n",
        ),
    ] {
        assert_eq!(
            text(&grammar, source, WIDE),
            expected,
            "the first member stands at the block's indentation, under its comment"
        );
    }
}

#[test]
fn strings_shell_blocks_and_holes_are_copied_as_written()
{
    let grammar = grammar();
    let source =
        "def s = \"a  ${  b }\tc\" ;\ndef h = #!{\n    printf 'hi'\n} ;\ndef k = (  ?hole  ) ;\n";
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
    let source = "def   z = 0 ;\ndef   a = (1 ;\ndef   b = 2 ;\n";
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
    let source = "def f() -> -F Integer {\r\n\r\n  return 1\r\n}\r\n";
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
        text(&grammar, "def a = 1 ;\r\ndef b = 2 ;\n", WIDE),
        "def a = 1;\ndef b = 2;\n",
        "carriage returns win only when most breaks carry them"
    );
}

#[test]
fn pieces_place_each_top_level_form()
{
    let grammar = grammar();
    let source = "def  a = 1 ;  // note\ndef b = 2 ;\n";
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
const EXPLICIT: &str = "@[ form(explicit) ]\ndef  shown : +U (-F Integer) ;\ndef shown = \
                            thunk {   run n <- force one ;  become read(n) } ;\n";

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
    let kept = "@[ form(explicit) ]\ndef shown : +U (-F Integer);\ndef shown = thunk { run n <- \
                force one; become read(n) };\n";
    let imported = "import \"./base.gandr\" ;\n";
    let imported_kept = "import \"./base.gandr\";\n";
    let grouped = "rec {\n@[ form(explicit) ]\ndef shown : +U (-F Integer) ;\ndef shown = \
                   thunk {   run n <- force one ;  become read(n) } ;\n}\n";
    let grouped_kept = "rec {\n  @[ form(explicit) ]\n  def shown : +U (-F Integer);\n  def \
                        shown = thunk { run n <- force one; become read(n) };\n}\n";
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
    let sugared = "@[ form(sugared) ]\ndef shown : () => Integer ;\n";
    for (written, declared) in [
        (sugared, Some(Form::Sugared)),
        ("def shown : () => Integer ;\n", None),
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
    /// each directory below `fixture` — and every source the change adds
    /// or modifies (`gandr-workflow-sweep`). The `sweeps` profile formats
    /// every source.
    const SAMPLE: Sample = Sample {
        name: SampleName("every_source_keeps_its_meaning_and_formats_once"),
        size: SampleSize(64),
    };

    #[test]
    fn every_source_keeps_its_meaning_and_formats_once()
    {
        let grammar = grammar();
        let sweep = Sweep::asked().expect("the run's sweep resolves");
        let sources = sweep.visit(SAMPLE, &corpus::sources().expect("the corpus reads"));
        assert!(
            sources.len() >= SAMPLE.size.0,
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
