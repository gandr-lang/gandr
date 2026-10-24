//! The grammar contracts only a parse can witness: a type-operator chain the
//! precedence table declares right-associative molds clean, every recursion
//! marker instantiation molds clean, a chain mixing incomparable set
//! operators is refused a clean reading, and every spelling of the universe
//! and of a type operator molds clean wherever a type stands.
//!
//! They live with the parser rather than the grammar because the dependency
//! points from the parser to the grammar; the grammar's own suite keeps the
//! contracts it can state without parsing.

use core::error::Error;

use anodized::spec;
use gandr_surface_parser::parse;
use gandr_surface_syntax::SourceText;

use crate::common::built;

/// The name a contract case is reported under.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct CaseName(&'static str);

#[test]
fn right_associative_type_operator_chains_parse_cleanly() -> Result<(), Box<dyn Error>>
{
    let cases = [
        ("three-member product", "def f : A * B * C;"),
        ("four-member product", "def f : A * B * C * D;"),
        ("three-member sum", "def f : A + B + C;"),
        ("four-member sum", "def f : A + B + C + D;"),
        ("three-member lazy product", "def f : -F A & -F B & -F C;"),
        (
            "four-member lazy product",
            "def f : -F A & -F B & -F C & -F D;",
        ),
        ("three-member union", "def f : A | B | C;"),
        ("four-member union", "def f : A | B | C | D;"),
        ("three-member value function space", "def f : A => B => C;"),
        ("mixed arrows", "def f : A => +U (B -> -F C) => D;"),
    ];
    for (case, source) in cases {
        assert_parses_clean(CaseName(case), SourceText::from(source))?;
    }
    Ok(())
}

#[test]
fn recursion_marker_instantiations_parse_cleanly() -> Result<(), Box<dyn Error>>
{
    let cases = [
        ("descending recursion marker", "def rec f() { f[<]() }"),
        ("productive recursion marker", "def rec f() { f[>]() }"),
        (
            "productive copattern marker",
            "def rec n() { .head => 0, .tail => n[>]() }",
        ),
        ("combined recursion markers", "def rec f() { f[<, >]() }"),
        ("reserved named measure", "def rec f() { f[n <]() }"),
        ("reserved explicit resident", "def rec f() { f[n = 1]() }"),
        ("reserved explicit size", "def rec f() { f[size = 1]() }"),
        ("reserved cost bound", "def rec f() { f[cost = 1]() }"),
        ("reserved tail resident", "def rec f() { f[tail]() }"),
        ("qualified outer reference", "def rec f() { (outer.f)() }"),
    ];
    for (case, source) in cases {
        assert_parses_clean(CaseName(case), SourceText::from(source))?;
    }
    Ok(())
}

#[test]
fn mixed_set_type_operators_require_parentheses() -> Result<(), Box<dyn Error>>
{
    let cases = [
        ("union before lazy product", "def f : A | B & C;"),
        ("lazy product before union", "def f : A & B | C;"),
    ];
    for (case, source) in cases {
        let result = parse(built(), SourceText::from(source))?;
        assert!(
            !result.obligations().is_empty(),
            "{case} must require a completion obligation"
        );
        assert!(
            !bool::from(result.is_clean()),
            "{case} must not parse cleanly"
        );
    }
    Ok(())
}

/// The universe is `Type` with an optional bracket naming its sort by sign and
/// optionally its level; each spelling molds clean as a declared type, as a
/// binder's type and under an arrow. Which of them the lowering admits is the
/// lowering's to say.
#[test]
fn every_universe_spelling_reads_cleanly() -> Result<(), Box<dyn Error>>
{
    let cases = [
        ("bare", "def f : Type;"),
        ("value sort", "def f : Type[+];"),
        ("computation sort", "def f : Type[-];"),
        ("value sort and level", "def f : Type[+, 1];"),
        ("computation sort and level", "def f : Type[-, 0];"),
        ("bare binder", "def f(a : Type, x : a) -> -F a { return x }"),
        ("under an arrow", "def f : +U (Type[+, 1] -> -F Type);"),
    ];
    for (case, source) in cases {
        assert_parses_clean(CaseName(case), SourceText::from(source))?;
    }
    Ok(())
}

/// A type operator is a static abstraction `\A. T`, applied as `T(A)`, and the
/// value function space is `A => B` or `(A, B) => C`; each molds clean as a
/// declared type, as a definition's value and as an operator's argument, the
/// n-ary alias with its binders as a call's argument too, and a case arm's
/// `=>` still molds beside them.
#[test]
fn every_type_operator_spelling_reads_cleanly() -> Result<(), Box<dyn Error>>
{
    let cases = [
        (
            "declared operator",
            "def f : (Type -> Type[-]) -> Type -> Type;",
        ),
        ("one binder", r"def f = \X. -F (X * X);"),
        ("nested binders", r"def f = \T. \A. \b. +U (A -> T(A)) * b;"),
        (
            "abstraction argument",
            r"def f : G(\X. -F (X * X), Integer);",
        ),
        ("unary alias", "def f : Integer => Integer * Integer;"),
        ("n-ary alias", "def f : (A, B => C) => D;"),
        ("alias in a product", "def f : (A => B) * ((C, D) => E);"),
        (
            "alias in a binder",
            "def f(k : A => B) -> -F B { become force k }",
        ),
        (
            "case arm beside the alias",
            "def f : A => B; def g(c : C) -> -F Integer { case c { Red => pure 0, _ => pure 1 } }",
        ),
        (
            "telescope as a call's argument",
            "def f = g((y : A, z : P(y)) => B(y, z), x);",
        ),
        (
            "domain list as a call's argument",
            "def f = g((y : A, P(y)) => B, (x : A));",
        ),
    ];
    for (case, source) in cases {
        assert_parses_clean(CaseName(case), SourceText::from(source))?;
    }
    Ok(())
}

/// #2255: where a value is read, a `(` whose group closes before `=>` molds
/// as the value-function alias's domain list, and one whose group closes
/// before anything else as the parenthesized expression it was: an
/// ascription, a tuple and the unit keep their reading.
#[test]
fn a_group_before_the_value_function_arrow_molds_as_its_domains_2255() -> Result<(), Box<dyn Error>>
{
    let cases = [
        ("def f = g((y : A, z : P(y)) => B);", "parenthesized_type"),
        ("def f = g((A, B) => C);", "parenthesized_type"),
        ("def f = g(((A)) => C);", "parenthesized_type"),
        ("def f = g((x : A), y);", "parenthesized_expression"),
        ("def f = g((x, y), z);", "parenthesized_expression"),
        ("def f = g((), z);", "parenthesized_expression"),
    ];
    let grammar = built();
    for (source, expected) in cases {
        let tree = parse(grammar, SourceText::from(source))?.into_tree();
        let first = tree
            .positions()
            .filter_map(|position| tree.node(position))
            .filter_map(|node| match node.label() {
                gandr_surface_syntax::NodeLabel::Tile(mold) => grammar.rule_of(mold).ok(),
                gandr_surface_syntax::NodeLabel::Wald
                | gandr_surface_syntax::NodeLabel::Meld(_)
                | gandr_surface_syntax::NodeLabel::Grout { .. }
                | gandr_surface_syntax::NodeLabel::GhostClose { .. }
                | gandr_surface_syntax::NodeLabel::Space
                | gandr_surface_syntax::NodeLabel::Doc => None,
            })
            .find(|rule| rule.name().0.starts_with("parenthesized_"))
            .map(|rule| rule.name().0);
        assert_eq!(
            first,
            Some(expected),
            "`{source}`: the first group's reading"
        );
    }
    Ok(())
}

/// Each ASCII token of the spelling table molds as its glyph's tile: a source
/// written with it is the tree the glyph's source is, mold for mold (#782).
#[test]
fn each_ascii_spelling_molds_as_its_glyph_782() -> Result<(), Box<dyn Error>>
{
    let cases = [
        ("def e : A ≃ B;", "def e : A <~> B;"),
        ("def e : A ⇝ B;", "def e : A ~~> B;"),
        ("def w = loop ∷ here(Base);", "def w = loop :: here(Base);"),
        (
            "def f(p : Path(Circle, Base, Base)) -> -F Integer {\n  case p {\n    loop ∷ q => \
             1\n  }\n}",
            "def f(p : Path(Circle, Base, Base)) -> -F Integer {\n  case p {\n    loop :: q => \
             1\n  }\n}",
        ),
        ("def g : +U[ω] (A -> -F B);", "def g : +U[inf] (A -> -F B);"),
    ];
    for (glyph, ascii) in cases {
        assert_parses_clean(CaseName(ascii), SourceText::from(ascii))?;
        let molds =
            |source: &'static str| -> Result<Vec<gandr_surface_syntax::NodeLabel>, Box<dyn Error>> {
                let tree = parse(built(), SourceText::from(source))?.into_tree();
                Ok(tree
                    .positions()
                    .filter_map(|position| tree.node(position))
                    .map(gandr_surface_syntax::Node::label)
                    .filter(|label| !matches!(label, gandr_surface_syntax::NodeLabel::Space))
                    .collect())
            };
        assert_eq!(molds(glyph)?, molds(ascii)?, "`{ascii}` molds as `{glyph}`");
    }
    Ok(())
}

/// Parse `source` under the built-in grammar and require a clean reading.
///
/// # Specification
/// - ensures: successful return means the parse has no obligations.
/// - fails: propagates the original typed melder error.
/// - panics: when the reading carries an obligation, naming case.
///
/// # Errors
/// The melder's refusal at commit, which a whole source never meets.
///
/// # Adequacy
/// - hypothesis: L3 — clean type-operator chains, recursion markers and
///   universe forms exercise the discarded parse result through its clean
///   assertion. Mixed set operators additionally distinguish the
///   required-parenthesis refusal. These valid sources do not force an internal
///   melder error; the predicate guards its concrete identity if it occurs.
/// - witness: `tests::grammar::right_associative_type_operator_chains_parse_cleanly`
/// - witness: `tests::grammar::recursion_marker_instantiations_parse_cleanly`
/// - witness: `tests::grammar::mixed_set_type_operators_require_parentheses`
/// - witness: `tests::grammar::every_universe_spelling_reads_cleanly`
#[spec(ensures: |ret| ret.as_ref().map_or_else(|error| error.downcast_ref::<gandr_surface_parser::MeldError>().is_some(), |&()| true))]
fn assert_parses_clean(
    case: CaseName,
    source: SourceText<'_>,
) -> Result<(), Box<dyn Error>>
{
    let result = parse(built(), source)?;
    assert!(
        bool::from(result.is_clean()),
        "{} must parse cleanly; obligations: {:?}",
        case.0,
        result
            .obligations()
            .iter()
            .map(|obligation| (obligation.class, obligation.span))
            .collect::<Vec<_>>()
    );
    Ok(())
}
