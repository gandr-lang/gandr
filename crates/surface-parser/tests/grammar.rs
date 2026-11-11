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
        (
            "three-member value function space",
            "def f : A -> (B -> C);",
        ),
        ("mixed arrows", "def f : A -> (+U (B -> -F C) -> D);"),
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
        ("descending recursion marker", "def rec f() { f[<] () }"),
        ("productive recursion marker", "def rec f() { f[>] () }"),
        (
            "productive copattern marker",
            "def rec n() { .head => 0, .tail => n[>] () }",
        ),
        ("combined recursion markers", "def rec f() { f[<, >] () }"),
        ("reserved named measure", "def rec f() { f[.n <] () }"),
        ("reserved explicit resident", "def rec f() { f[.n = 1] () }"),
        ("punned explicit resident", "def rec f() { f[.n] () }"),
        ("reserved explicit size", "def rec f() { f[.size = 1] () }"),
        ("reserved cost bound", "def rec f() { f[.cost = 1] () }"),
        ("reserved tail resident", "def rec f() { f[tail] () }"),
        ("qualified outer reference", "def rec f() { (outer.f) () }"),
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

/// A type operator is a static abstraction `fun (A) { T }`, applied as `T(A)`,
/// and the value function space is `A => B` or `(A, B) => C`; each molds clean
/// as a declared type, as a definition's value and as an operator's argument,
/// the n-ary alias with its binders as a call's argument too, and a case arm's
/// `=>` still molds beside them.
#[test]
fn every_type_operator_spelling_reads_cleanly() -> Result<(), Box<dyn Error>>
{
    let cases = [
        (
            "declared operator",
            "def f : (Type -> Type[-]) -> Type -> Type;",
        ),
        ("one binder", r"def f = fun (X) { -F (X * X) };"),
        (
            "nested binders",
            r"def f = fun (T) { fun (A) { fun (b) { type(+U (A -> T(A)) * b) } } };",
        ),
        (
            "abstraction argument",
            r"def f : G(fun (X) { -F (X * X) }, Integer);",
        ),
        ("unary alias", "def f : Integer -> Integer * Integer;"),
        ("n-ary alias", "def f : *{A, B -> C} -> D;"),
        ("alias in a product", "def f : (A -> B) * (*{C, D} -> E);"),
        (
            "alias in a binder",
            "def f(k : A -> B) -> -F B { become force k }",
        ),
        (
            "case arm beside the alias",
            "def f : A -> B; def g(c : C) -> -F Integer { match c { | Red => pure 0 | _ => pure 1 } }",
        ),
        (
            "telescope as a call's argument",
            "def f = g ((y : A, z : P(y)) -> B(y, z)) x;",
        ),
        (
            "domain list as a call's argument",
            "def f = g ((y : A, P(y)) -> B) (x : A);",
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
        (
            "def f = g type((y : A, z : P(y)) -> B);",
            "parenthesized_type",
        ),
        ("def f = g type((A, B) -> C);", "parenthesized_type"),
        ("def f = g type(((A)) -> C);", "parenthesized_type"),
        ("def f = g (x : A) y;", "parenthesized_expression"),
        ("def f = g (x, y) z;", "parenthesized_expression"),
        ("def f = g () z;", "parenthesized_expression"),
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

/// #4853: an expression operand right after an expression operand applies
/// it, `f x`, through one zero-width tile per argument. A shell block's words
/// stay flat, and a block-like statement ends at its brace.
#[test]
fn juxtaposition_applies_outside_a_shell_form_4853() -> Result<(), Box<dyn Error>>
{
    let cases = [
        ("def f = g x y;", 2_usize),
        ("def f = g x.y;", 1),
        ("def f = - g x;", 1),
        ("def f = g x + h y;", 2),
        ("def f = #!{ echo a b };", 0),
        ("def f() -> Integer { if c { a } else { b } x }", 0),
        ("def f = g *{} x;", 2),
        ("def f = g +{.l = a} *{.x = b} y;", 3),
        ("def f = g &{ .l => a } x;", 2),
    ];
    let grammar = built();
    for (source, expected) in cases {
        let tree = parse(grammar, SourceText::from(source))?.into_tree();
        let applied = tree
            .positions()
            .filter_map(|position| tree.node(position))
            .filter(|node| match node.label() {
                gandr_surface_syntax::NodeLabel::Tile(mold) => grammar
                    .rule_of(mold)
                    .is_ok_and(|rule| rule.name().0 == "application_expression"),
                gandr_surface_syntax::NodeLabel::Wald
                | gandr_surface_syntax::NodeLabel::Meld(_)
                | gandr_surface_syntax::NodeLabel::Grout { .. }
                | gandr_surface_syntax::NodeLabel::GhostClose { .. }
                | gandr_surface_syntax::NodeLabel::Space
                | gandr_surface_syntax::NodeLabel::Doc => false,
            })
            .count();
        assert_eq!(applied, expected, "`{source}`: the applications it reads");
        if expected > 0 {
            assert_parses_clean(CaseName(source), SourceText::from(source))?;
        }
    }
    Ok(())
}

/// #5326: a type operand right after a type operand applies it, `Vec A n`,
/// through one zero-width tile per argument. The band binds tighter than the
/// returner and the arrow, so `-F Maybe A` returns the application, and the
/// call form `Vec(A, n)` keeps its reading. A form such as `+U A` is an
/// argument as it stands. The returner `-F` is a prefix of a looser band, so
/// it is an argument only in parentheses. A lowercase argument before a
/// spaced group is an argument as a type name is, `Vec a (Succ n)`, and a
/// lowercase word that heads its type keeps the moded type, `m (T)`.
#[test]
fn a_type_applies_its_family_by_juxtaposition_5326() -> Result<(), Box<dyn Error>>
{
    let cases = [
        ("def x : Maybe A;", 1_usize),
        ("def x : Vec A n;", 2),
        ("def x : Var (Extend g n) n;", 4),
        ("def x : Vec A (Succ n) -> -F B;", 3),
        ("def opt : Type -> Type[-] = fun (A) { -F Maybe A };", 1),
        ("def x : Maybe(A);", 0),
        ("def x : Vec(A, n);", 0),
        ("def x : Vec a n;", 2),
        ("def x : Vec a (Succ n);", 3),
        ("def x : Sub d (g);", 2),
        ("def x : Sub D (g);", 2),
        ("def x : Vec a(n);", 1),
        ("def x : m (T);", 0),
        ("def x : Vec Integer plus(m, Zero);", 2),
        ("def x : Vec a plus(m, Zero);", 2),
        ("def x : m plus(m, k);", 0),
        ("def x : el[<](a);", 0),
        ("def x : m T;", 0),
        ("def x : (m n : Integer) -> Integer;", 0),
        ("def x : Vec +U Integer;", 1),
        ("def x : Vec (-F Integer);", 1),
    ];
    let grammar = built();
    for (source, expected) in cases {
        let tree = parse(grammar, SourceText::from(source))?.into_tree();
        let applied = tree
            .positions()
            .filter_map(|position| tree.node(position))
            .filter(|node| match node.label() {
                gandr_surface_syntax::NodeLabel::Tile(mold) => grammar
                    .rule_of(mold)
                    .is_ok_and(|rule| rule.name().0 == "type_application.juxtaposed"),
                gandr_surface_syntax::NodeLabel::Wald
                | gandr_surface_syntax::NodeLabel::Meld(_)
                | gandr_surface_syntax::NodeLabel::Grout { .. }
                | gandr_surface_syntax::NodeLabel::GhostClose { .. }
                | gandr_surface_syntax::NodeLabel::Space
                | gandr_surface_syntax::NodeLabel::Doc => false,
            })
            .count();
        assert_eq!(
            applied, expected,
            "`{source}`: the type applications it reads"
        );
        assert_parses_clean(CaseName(source), SourceText::from(source))?;
    }
    Ok(())
}

/// #6121: `Path` reads as `Bridge` reads. Before a `(` or a `[` written
/// straight after it, each keeps its own form, whose endpoints are
/// expressions, so `Path(Path.walk f p v, w)` reads its endpoint as a
/// transport. Anywhere else each is a type name that the juxtaposition
/// applies, `Path a b`, and a spaced `(` opens a group. A carrier supplied in
/// brackets ends the former's own form, and the juxtaposition applies it,
/// `Path[.A = Integer] a a`.
#[test]
fn a_called_former_keeps_its_own_opener_6121() -> Result<(), Box<dyn Error>>
{
    let cases = [
        ("def x : Path a b;", 0_usize, 2_usize),
        ("def x : Bridge a b;", 0, 2),
        ("def x : Path(a, b);", 1, 0),
        ("def x : Bridge(a, b);", 1, 0),
        ("def x : Path(Path.walk f p v, w);", 1, 0),
        ("def x : Path (g(a)) (g(a));", 0, 2),
        ("def x : Path[.A = Integer] a a;", 1, 2),
        ("def x : Bridge[.A = Integer] a a;", 1, 2),
        ("def x : Path[.A = Integer](a, a);", 1, 0),
        ("def x : Path a a -> Path a a;", 0, 4),
    ];
    let grammar = built();
    for (source, own, applied) in cases {
        let tree = parse(grammar, SourceText::from(source))?.into_tree();
        let rules = tree
            .positions()
            .filter_map(|position| tree.node(position))
            .filter_map(|node| match node.label() {
                gandr_surface_syntax::NodeLabel::Tile(mold) => {
                    let label = grammar.mold(mold).ok()?.label;
                    Some((grammar.rule_of(mold).ok()?.name().0, label))
                },
                gandr_surface_syntax::NodeLabel::Wald
                | gandr_surface_syntax::NodeLabel::Meld(_)
                | gandr_surface_syntax::NodeLabel::Grout { .. }
                | gandr_surface_syntax::NodeLabel::GhostClose { .. }
                | gandr_surface_syntax::NodeLabel::Space
                | gandr_surface_syntax::NodeLabel::Doc => None,
            })
            .collect::<Vec<_>>();
        let heads = rules
            .iter()
            .filter(|&&(rule, label)| {
                matches!(rule, "path_type" | "bridge_type") && matches!(label, "Path" | "Bridge")
            })
            .count();
        let juxtaposed = rules
            .iter()
            .filter(|&&(rule, _)| rule == "type_application.juxtaposed")
            .count();
        assert_eq!(
            (heads, juxtaposed),
            (own, applied),
            "`{source}`: the own forms and the type applications it reads"
        );
        assert_parses_clean(CaseName(source), SourceText::from(source))?;
    }
    Ok(())
}

/// #6093: a packed or forgotten model's type ends its form, and a type operand
/// after it applies that type, `pack M at Model T`, as a value call applies
/// its function. The call form `Model(T)` keeps its reading.
#[test]
fn a_packed_model_s_type_applies_by_juxtaposition_6093() -> Result<(), Box<dyn Error>>
{
    let cases = [
        (
            "def site : Model(Site) = pack Site at Model Site;",
            "pack_model_expression",
            "Model Site",
            1_usize,
        ),
        (
            "def f() -> Integer { pack Site at Model Site }",
            "pack_model_expression",
            "Model Site",
            1,
        ),
        (
            "def x = (pack Site at Pair Site Site);",
            "pack_model_expression",
            "Pair Site Site",
            2,
        ),
        (
            "def x = forget[sort C = Integer](m) at Model Counter;",
            "forget_model_expression",
            "Model Counter",
            1,
        ),
        (
            "def site : Model(Site) = pack Site at Model(Site);",
            "pack_model_expression",
            "Model(Site)",
            0,
        ),
    ];
    let grammar = built();
    for (source, rule, model, applied) in cases {
        assert_parses_clean(CaseName(source), SourceText::from(source))?;
        let tree = parse(grammar, SourceText::from(source))?.into_tree();
        let form = tree.positions().find(|&position| {
            tree.node(position).is_some_and(|node| {
                matches!(node.label(), gandr_surface_syntax::NodeLabel::Meld(mold)
                    if grammar.rule_of(mold).is_ok_and(|found| found.name().0 == rule))
            })
        });
        let read = form
            .and_then(|position| {
                tree.children(position)
                    .filter(|&child| {
                        tree.node(child).is_some_and(|node| {
                            !matches!(node.label(), gandr_surface_syntax::NodeLabel::Space)
                        })
                    })
                    .last()
            })
            .and_then(|child| tree.fragment(child))
            .map(<&str>::from);
        assert_eq!(read, Some(model), "`{source}`: the type its {rule} ends in");
        let applications = tree
            .positions()
            .filter_map(|position| tree.node(position))
            .filter(|node| match node.label() {
                gandr_surface_syntax::NodeLabel::Tile(mold) => grammar
                    .rule_of(mold)
                    .is_ok_and(|found| found.name().0 == "type_application.juxtaposed"),
                gandr_surface_syntax::NodeLabel::Wald
                | gandr_surface_syntax::NodeLabel::Meld(_)
                | gandr_surface_syntax::NodeLabel::Grout { .. }
                | gandr_surface_syntax::NodeLabel::GhostClose { .. }
                | gandr_surface_syntax::NodeLabel::Space
                | gandr_surface_syntax::NodeLabel::Doc => false,
            })
            .count();
        assert_eq!(
            applications, applied,
            "`{source}`: the type applications it reads"
        );
    }
    Ok(())
}

/// #6093: after an observation's type operand, a `(` opens the type's
/// argument, `tail : Twisted (Twisted a)`, not the parameter list that only
/// the `:` takes. The parameter list right after the `:` keeps its reading,
/// and a data block's next member after a constructor's type continues the
/// block.
#[test]
fn an_observation_s_type_applies_a_parenthesized_argument_6093() -> Result<(), Box<dyn Error>>
{
    let cases = [
        (
            include_str!(
                "grammar/fixtures/an-observation-s-type-applies-a-parenthesized-argument-6093-1.gandr"
            ),
            2_usize,
        ),
        (
            include_str!(
                "grammar/fixtures/an-observation-s-type-applies-a-parenthesized-argument-6093-2.gandr"
            ),
            2,
        ),
        (
            include_str!(
                "grammar/fixtures/an-observation-s-type-applies-a-parenthesized-argument-6093-3.gandr"
            ),
            0,
        ),
        (
            include_str!(
                "grammar/fixtures/an-observation-s-type-applies-a-parenthesized-argument-6093-4.gandr"
            ),
            0,
        ),
    ];
    let grammar = built();
    for (source, applied) in cases {
        assert_parses_clean(CaseName(source), SourceText::from(source))?;
        let tree = parse(grammar, SourceText::from(source))?.into_tree();
        let applications = tree
            .positions()
            .filter_map(|position| tree.node(position))
            .filter(|node| match node.label() {
                gandr_surface_syntax::NodeLabel::Tile(mold) => grammar
                    .rule_of(mold)
                    .is_ok_and(|rule| rule.name().0 == "type_application.juxtaposed"),
                gandr_surface_syntax::NodeLabel::Wald
                | gandr_surface_syntax::NodeLabel::Meld(_)
                | gandr_surface_syntax::NodeLabel::Grout { .. }
                | gandr_surface_syntax::NodeLabel::GhostClose { .. }
                | gandr_surface_syntax::NodeLabel::Space
                | gandr_surface_syntax::NodeLabel::Doc => false,
            })
            .count();
        assert_eq!(
            applications, applied,
            "`{source}`: the type applications it reads"
        );
    }
    Ok(())
}

/// #5665: a postfix form after a call in call form, a head with a group
/// written straight after it, takes the whole call as its target. A group
/// after a space is an argument of its own, and a projection binds tighter
/// than juxtaposition, so `mk (x).l` and `mk x.l` project the argument. In
/// a spine the call is the whole spine, and a looser operator keeps its own
/// operands.
#[test]
fn a_postfix_form_after_a_call_in_call_form_takes_the_call_5665() -> Result<(), Box<dyn Error>>
{
    let cases = [
        ("def f = mk(x).l;", "projection_expression", "mk(x)"),
        ("def f = mk (x).l;", "projection_expression", "(x)"),
        ("def f = mk x.l;", "projection_expression", "x"),
        ("def f = g mk(x).l;", "projection_expression", "g mk(x)"),
        ("def f = a + mk(x).l;", "projection_expression", "mk(x)"),
        ("def f = mk(x)(y).l;", "projection_expression", "mk(x)(y)"),
        ("def f = s.first().l;", "projection_expression", "s.first()"),
        ("def f = mk(x).l.m;", "projection_expression", "mk(x).l"),
        ("def f = mk(x).#[i];", "index_expression", "mk(x)"),
        (
            "def f = mk(x).*{.a};",
            "record_selection_expression",
            "mk(x)",
        ),
        ("def f = mk(x)[T];", "instantiation_expression", "mk(x)"),
        ("def f = mk(x) as w { pure w };", "view_expression", "mk(x)"),
    ];
    let grammar = built();
    for (source, rule, target) in cases {
        assert_parses_clean(CaseName(source), SourceText::from(source))?;
        let tree = parse(grammar, SourceText::from(source))?.into_tree();
        let formed = |position| {
            tree.node(position).is_some_and(|node| {
                matches!(node.label(), gandr_surface_syntax::NodeLabel::Meld(mold)
                    if grammar.rule_of(mold).is_ok_and(|found| found.name().0 == rule))
            })
        };
        // The outermost form of `rule` is the one whose text is longest.
        let form = tree
            .positions()
            .filter(|&position| formed(position))
            .max_by_key(|&position| {
                tree.fragment(position)
                    .map_or(0, |text| <&str>::from(text).len())
            });
        let read = form
            .and_then(|position| tree.children(position).next())
            .and_then(|child| tree.fragment(child))
            .map(<&str>::from);
        assert_eq!(read, Some(target), "`{source}`: the target of its {rule}");
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
        (
            "def w = loop ∷ Path.here Base;",
            "def w = loop :: Path.here Base;",
        ),
        (
            include_str!("grammar/fixtures/each-ascii-spelling-molds-as-its-glyph-782-1.gandr"),
            include_str!("grammar/fixtures/each-ascii-spelling-molds-as-its-glyph-782-2.gandr"),
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

/// #6130: the last hole of a type form at the application band takes a
/// juxtaposed application as its operand, whatever tile precedes that hole.
/// So `+U T Integer` thunks `T Integer` as `-F T Integer` returns it, with a
/// grade or without one. A row before the returned type keeps that reading,
/// as `-F [Partial] Maybe Integer` and the result form `[Partial] Maybe
/// Integer` show. The application band is tighter than the band of `+U`, so
/// `Vec +U A B` applies `Vec` to the thunk of `A B`.
#[test]
fn a_type_form_s_last_hole_takes_a_juxtaposed_application_6130() -> Result<(), Box<dyn Error>>
{
    let cases = [
        ("def x : +U T Integer;", "u_type", "+U T Integer"),
        ("def x : +U Maybe Integer;", "u_type", "+U Maybe Integer"),
        (
            "def x : +U[1] Maybe Integer;",
            "u_type",
            "+U[1] Maybe Integer",
        ),
        ("def x : Vec +U A B;", "u_type", "+U A B"),
        ("def x : -F T Integer;", "f_type", "-F T Integer"),
        (
            "def x : -F [Partial] Maybe Integer;",
            "f_type.row",
            "-F [Partial] Maybe Integer",
        ),
        (
            "def f() -> [Partial] Maybe Integer { pure 1 }",
            "f_type.result",
            "[Partial] Maybe Integer",
        ),
        (
            "def again(T : Type -> Type[-], m : +U T Integer) -> T Integer { force m }",
            "u_type",
            "+U T Integer",
        ),
    ];
    let grammar = built();
    for (source, rule, formed) in cases {
        assert_parses_clean(CaseName(source), SourceText::from(source))?;
        let tree = parse(grammar, SourceText::from(source))?.into_tree();
        let read = tree
            .positions()
            .find(|&position| {
                tree.node(position).is_some_and(|node| {
                    matches!(node.label(), gandr_surface_syntax::NodeLabel::Meld(mold)
                        if grammar.rule_of(mold).is_ok_and(|found| found.name().0 == rule))
                })
            })
            .and_then(|position| tree.fragment(position))
            .map(<&str>::from);
        assert_eq!(read, Some(formed), "`{source}`: the type its {rule} forms");
    }
    Ok(())
}
