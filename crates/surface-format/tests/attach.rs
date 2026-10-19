//! Comment attachment through the public surface: each comment read beside
//! the node it belongs to and its role there, and each kept with that node
//! when a layout breaks or joins the group around it.

use gandr_surface_format::Comment;
use gandr_surface_format::CommentKind;
use gandr_surface_format::FormatOptions;
use gandr_surface_format::PageWidth;
use gandr_surface_format::Role;
use gandr_surface_format::comments;
use gandr_surface_format::format;
use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::built_in;
use gandr_surface_parser::parse;
use gandr_surface_syntax::NodeLabel;
use gandr_surface_syntax::SourceText;
use gandr_surface_syntax::SyntaxTree;

/// The built-in grammar.
///
/// # Specification
/// trivial.
fn grammar() -> Pbg
{
    built_in().expect("the built-in grammar builds")
}

/// One comment as a witness reads it: its text, kind and role, and the
/// grammar rule its owner realises — `<root>` for the root.
type Read = (String, CommentKind, Role, String);

/// The comment `comment` of `tree`, as a witness reads it.
///
/// # Specification
/// trivial.
fn read(
    grammar: &Pbg,
    tree: &SyntaxTree<'_>,
    comment: &Comment<'_>,
) -> Read
{
    let owner = match tree
        .node(comment.owner)
        .map(gandr_surface_syntax::Node::label)
    {
        Some(NodeLabel::Meld(mold)) => grammar
            .rule_of(mold)
            .map(|rule| String::from(rule.name().0))
            .unwrap_or_default(),
        Some(_) | None => String::from("<root>"),
    };
    (
        String::from(comment.text.as_ref()),
        comment.kind,
        comment.role,
        owner,
    )
}

/// The comments of `source`, as a witness reads them.
///
/// # Specification
/// trivial.
fn attached<'text>(
    grammar: &Pbg,
    source: impl Into<SourceText<'text>>,
) -> Vec<Read>
{
    let parsed = parse(grammar, source.into()).expect("the source parses");
    let tree = parsed.tree();
    comments(tree)
        .iter()
        .map(|comment| read(grammar, tree, comment))
        .collect()
}

/// `source` formatted at a page of `width` columns.
///
/// # Specification
/// trivial.
fn laid<'text>(
    grammar: &Pbg,
    source: impl Into<SourceText<'text>>,
    width: impl Into<PageWidth>,
) -> String
{
    let parsed = parse(grammar, source.into()).expect("the source parses");
    let options = FormatOptions {
        page: width.into(),
        ..FormatOptions::default()
    };
    format(grammar, &parsed, options)
        .expect("the source formats")
        .into_text()
}

/// The comment `read` names, as a witness expects it.
///
/// # Specification
/// trivial.
fn expected(
    text: impl Into<String>,
    kind: CommentKind,
    role: Role,
    owner: impl Into<String>,
) -> Read
{
    (text.into(), kind, role, owner.into())
}

/// A body a narrow page breaks one statement per line, a comment of each
/// role inside it: the definition owns its block's statements, whose
/// keywords are its own tiles, and a call owns what its brackets hold.
const BODY: &str = "def f(x : Integer) -> -F Integer {\n  // first\n  run y <- inc(x) ; /* \
                    after y */\n  run z <- inc(\n    // why\n    y) ;\n  z\n  // done\n}\n";

#[test]
fn a_comment_on_its_own_line_leads_the_form_below_it()
{
    let grammar = grammar();
    let found = attached(&grammar, BODY);
    assert_eq!(
        (found.first(), found.get(2)),
        (
            Some(&expected(
                "// first",
                CommentKind::Line,
                Role::Leading,
                "def_value"
            )),
            Some(&expected(
                "// why",
                CommentKind::Line,
                Role::Leading,
                "call_expression"
            )),
        ),
        "a comment on its own line before material leads it, in the form holding that \
         material: {found:#?}"
    );
}

#[test]
fn a_comment_after_material_on_its_line_trails_it()
{
    let grammar = grammar();
    let found = attached(&grammar, BODY);
    assert_eq!(
        found.get(1),
        Some(&expected(
            "/* after y */",
            CommentKind::Block,
            Role::Trailing,
            "def_value"
        )),
        "a comment after a separator on its line trails it: {found:#?}"
    );
}

#[test]
fn a_comment_before_a_closing_bracket_dangles_on_its_block()
{
    let grammar = grammar();
    let found = attached(&grammar, BODY);
    assert_eq!(
        found.get(3),
        Some(&expected(
            "// done",
            CommentKind::Line,
            Role::Dangling,
            "def_value"
        )),
        "a comment with nothing of its form after it but the closer dangles: {found:#?}"
    );
    assert_eq!(
        attached(&grammar, "def e = [\n  /* none */\n] ;\n").first(),
        Some(&expected(
            "/* none */",
            CommentKind::Block,
            Role::Dangling,
            "list_expression"
        )),
        "a comment alone in a bracket dangles on it"
    );
}

#[test]
fn documentation_and_the_root_keep_their_owners()
{
    let grammar = grammar();
    let found = attached(
        &grammar,
        "/// One.\n/// Two.\ndef one = 1 ;\n\n// alone\n\ndef two = 2 ;\n",
    );
    assert_eq!(
        found,
        [
            expected(
                "/// One.",
                CommentKind::Documentation,
                Role::Leading,
                "def_value"
            ),
            expected(
                "/// Two.",
                CommentKind::Documentation,
                Role::Leading,
                "def_value"
            ),
            expected("// alone", CommentKind::Line, Role::Leading, "<root>"),
        ],
        "documentation leads the form after it; a comment set apart by blank lines belongs to \
         the root"
    );
}

#[test]
fn a_layout_that_breaks_or_joins_a_group_keeps_each_comment_with_its_owner()
{
    let grammar = grammar();
    let written = attached(&grammar, BODY);
    for width in [24_u32, 40, 100] {
        let once = laid(&grammar, BODY, width);
        assert_eq!(
            attached(&grammar, once.as_str()),
            written,
            "at {width} columns each comment keeps its owner and role:\n{once}"
        );
    }
    let joined = "def g(x : Integer) -> -F Integer { run y <- inc(x) ; /* kept */ y }\n";
    let broken = laid(&grammar, joined, 24_u32);
    assert!(
        broken.lines().count() > 1,
        "the narrow page breaks the body:\n{broken}"
    );
    assert_eq!(
        attached(&grammar, broken.as_str()),
        attached(&grammar, joined),
        "a break added keeps the comment trailing its statement:\n{broken}"
    );
}
