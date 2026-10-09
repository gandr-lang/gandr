//! The grammar contracts only a parse can witness: a type-operator chain the
//! precedence table declares right-associative molds clean, every recursion
//! marker instantiation molds clean, a chain mixing incomparable set
//! operators is refused a clean reading, and every spelling of the universe
//! molds clean wherever a type stands.
//!
//! They live with the parser rather than the grammar because the dependency
//! points from the parser to the grammar; the grammar's own suite keeps the
//! contracts it can state without parsing.

use core::error::Error;

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
        ("three-member intersection", r"def f : A /\ B /\ C;"),
        ("four-member intersection", r"def f : A /\ B /\ C /\ D;"),
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
        ("union before intersection", r"def f : A | B /\ C;"),
        ("intersection before union", r"def f : A /\ B | C;"),
        ("union before lazy product", "def f : A | B & C;"),
        ("lazy product before union", "def f : A & B | C;"),
        ("intersection before lazy product", r"def f : A /\ B & C;"),
        ("lazy product before intersection", r"def f : A & B /\ C;"),
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
        ("bare binder", "def f(a : Type, x : a) -> -F a { ret x }"),
        ("under an arrow", "def f : +U (Type[+, 1] -> -F Type);"),
    ];
    for (case, source) in cases {
        assert_parses_clean(CaseName(case), SourceText::from(source))?;
    }
    Ok(())
}

/// Parse `source` under the built-in grammar and require a clean reading.
///
/// # Specification
/// - panics: when the reading carries an obligation, naming `case`.
///
/// # Errors
/// The melder's refusal at commit, which a whole source never meets.
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
