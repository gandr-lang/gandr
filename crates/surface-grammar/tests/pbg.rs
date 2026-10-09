//! Grammar construction: the header checks and the three gates, each refusing
//! a minimal violation and accepting the nearest legal shape.

use core::error::Error;

use gandr_surface_grammar::Adaptation;
use gandr_surface_grammar::AdaptationReason;
use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::PbgError;
use gandr_surface_grammar::Regex;
use gandr_surface_grammar::Rule;
use gandr_surface_grammar::RuleName;
use gandr_surface_grammar::Sort;
use gandr_surface_grammar::SurfaceForm;
use gandr_surface_grammar::TileLabel;
use gandr_surface_grammar::validate_assumption_3;
use gandr_surface_grammar::validate_unique_tiles;
use gandr_theory_graphs::Assoc;
use gandr_theory_graphs::Prec;
use gandr_theory_graphs::PrecDag;
use gandr_theory_graphs::PrecIndex;
use gandr_theory_graphs::PrecSpec;

/// A DAG of one non-associative group, `base`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: returns the DAG and its one group.
/// - fails: never for one group.
/// - panics: none.
fn one_node_dag() -> Result<(PrecDag, Prec), Box<dyn Error>>
{
    let mut spec = PrecSpec::new();
    let base = spec.insert("base", Assoc::Non)?;
    let dag = PrecDag::build(&spec)?;
    Ok((dag, base))
}

/// The refusal [`Pbg::build`] reports for `rules` over [`one_node_dag`].
///
/// # Specification
/// - requires: `rules` violate a header check or a gate.
/// - ensures: returns the refusal.
/// - fails: the DAG cannot be built.
/// - panics: when the build succeeds.
fn exact_error(rules: Vec<Rule>) -> Result<PbgError, Box<dyn Error>>
{
    let (dag, _base) = one_node_dag()?;
    match Pbg::build(dag, rules) {
        | Ok(_pbg) => panic!("the build must refuse"),
        | Err(error) => Ok(error),
    }
}

#[test]
fn pbg_rejects_direct_adjacent_sorts_in_sequence() -> Result<(), Box<dyn Error>>
{
    let (_dag, base) = one_node_dag()?;
    let error = exact_error(vec![Rule::new(
        RuleName("direct-adjacent"),
        Sort::Expression,
        base,
        Regex::seq([Regex::sort(Sort::Item), Regex::sort(Sort::Pattern)]),
    )])?;

    assert_eq!(
        PbgError::AdjacentSorts {
            rule: "direct-adjacent",
            left: Sort::Item,
            right: Sort::Pattern,
        },
        error
    );
    Ok(())
}

#[test]
fn pbg_rejects_adjacency_exposed_by_nullable_sequence_paths() -> Result<(), Box<dyn Error>>
{
    let (_dag, base) = one_node_dag()?;
    let cases = [
        (
            RuleName("optional-gap"),
            Regex::seq([
                Regex::sort(Sort::Item),
                Regex::optional(Regex::tile(TileLabel("maybe-comma"))),
                Regex::sort(Sort::Pattern),
            ]),
            Sort::Item,
            Sort::Pattern,
        ),
        (
            RuleName("empty-gap"),
            Regex::seq([
                Regex::sort(Sort::Pattern),
                Regex::empty(),
                Regex::sort(Sort::Expression),
            ]),
            Sort::Pattern,
            Sort::Expression,
        ),
        (
            RuleName("repeat-gap"),
            Regex::seq([
                Regex::sort(Sort::Expression),
                Regex::repeat(Regex::tile(TileLabel("zero-or-more-sep"))),
                Regex::sort(Sort::Type),
            ]),
            Sort::Expression,
            Sort::Type,
        ),
        (
            RuleName("alt-empty-gap"),
            Regex::seq([
                Regex::sort(Sort::Type),
                Regex::alt([Regex::tile(TileLabel("alt-sep")), Regex::empty()]),
                Regex::sort(Sort::Item),
            ]),
            Sort::Type,
            Sort::Item,
        ),
    ];

    for (name, regex, left, right) in cases {
        let error = exact_error(vec![Rule::new(name, Sort::Expression, base, regex)])?;
        assert_eq!(
            PbgError::AdjacentSorts {
                rule: name.0,
                left,
                right,
            },
            error
        );
    }
    Ok(())
}

#[test]
fn pbg_accepts_terminal_separators_between_sort_uses() -> Result<(), Box<dyn Error>>
{
    let (dag, base) = one_node_dag()?;
    let pbg = Pbg::build(dag, vec![
        Rule::new(
            RuleName("literal-separator"),
            Sort::Expression,
            base,
            Regex::seq([
                Regex::sort(Sort::Item),
                Regex::tile(TileLabel("comma")),
                Regex::sort(Sort::Pattern),
            ]),
        ),
        Rule::new(
            RuleName("alt-literal-separator"),
            Sort::Type,
            base,
            Regex::seq([
                Regex::sort(Sort::Expression),
                Regex::alt([
                    Regex::tile(TileLabel("fat-arrow")),
                    Regex::tile(TileLabel("thin-arrow")),
                ]),
                Regex::sort(Sort::Type),
            ]),
        ),
    ])?;

    assert_eq!(2, pbg.rules().len());
    assert!(pbg.rule_names().contains("literal-separator"));
    assert!(pbg.rule_names().contains("alt-literal-separator"));
    Ok(())
}

#[test]
fn pbg_rejects_invalid_operator_form_even_with_adaptation() -> Result<(), Box<dyn Error>>
{
    let (_dag, base) = one_node_dag()?;
    let error = exact_error(vec![Rule::with_adaptation(
        RuleName("adapted-but-invalid"),
        Sort::Expression,
        base,
        Regex::seq([Regex::sort(Sort::Pattern), Regex::sort(Sort::Type)]),
        Adaptation::new(
            RuleName("adapted-but-invalid"),
            SurfaceForm("pattern type"),
            AdaptationReason("documented but still not an operator-form separator"),
        ),
    )])?;

    assert_eq!(
        PbgError::AdjacentSorts {
            rule: "adapted-but-invalid",
            left: Sort::Pattern,
            right: Sort::Type,
        },
        error
    );
    Ok(())
}

#[test]
fn unique_tiles_contract()
{
    let base = Prec::new(PrecIndex::from(0));
    // Identical alternation branches intern two occurrences of one tile to
    // one context.
    let redundant = vec![Rule::new(
        RuleName("identical-branches"),
        Sort::Expression,
        base,
        Regex::alt([
            Regex::tile(TileLabel("shared")),
            Regex::tile(TileLabel("shared")),
        ]),
    )];
    assert_eq!(
        Err(PbgError::DuplicateTile {
            label: "shared",
            sort: Sort::Expression,
            prec: base,
            first_rule: "identical-branches",
            second_rule: "identical-branches",
        }),
        validate_unique_tiles(&redundant)
    );

    // Distinct positions receive distinct contexts, so a repeated element is
    // not a duplicate.
    let cloned = vec![Rule::new(
        RuleName("cloned-element"),
        Sort::Expression,
        base,
        Regex::seq([
            Regex::tile(TileLabel("id")),
            Regex::repeat(Regex::seq([
                Regex::tile(TileLabel(",")),
                Regex::tile(TileLabel("id")),
            ])),
        ]),
    )];
    assert_eq!(Ok(()), validate_unique_tiles(&cloned));
}

#[test]
fn pbg_rejects_duplicate_rctx_tile() -> Result<(), Box<dyn Error>>
{
    let (_dag, base) = one_node_dag()?;
    let error = exact_error(vec![Rule::new(
        RuleName("identical-branches"),
        Sort::Expression,
        base,
        Regex::alt([
            Regex::tile(TileLabel("shared")),
            Regex::tile(TileLabel("shared")),
        ]),
    )])?;

    assert_eq!(
        PbgError::DuplicateTile {
            label: "shared",
            sort: Sort::Expression,
            prec: base,
            first_rule: "identical-branches",
            second_rule: "identical-branches",
        },
        error
    );
    Ok(())
}

#[test]
fn pbg_accepts_same_label_at_distinct_contexts() -> Result<(), Box<dyn Error>>
{
    let (dag, base) = one_node_dag()?;
    let pbg = Pbg::build(dag, vec![
        // One label at two sequence positions: distinct contexts.
        Rule::new(
            RuleName("delimited"),
            Sort::Expression,
            base,
            Regex::seq([
                Regex::tile(TileLabel("bracket")),
                Regex::sort(Sort::Expression),
                Regex::tile(TileLabel("bracket")),
            ]),
        ),
        // The same label in another rule: contexts are scoped to their rule.
        Rule::new(
            RuleName("bare"),
            Sort::Type,
            base,
            Regex::tile(TileLabel("bracket")),
        ),
    ])?;

    assert_eq!(2, pbg.rules().len());
    assert_eq!(3, pbg.candidates(TileLabel("bracket")).len());
    Ok(())
}

#[test]
fn assumption_3_contract()
{
    let base = Prec::new(PrecIndex::from(0));
    // An expression form begins with a type hole and a type form ends with an
    // expression hole: `r ≠ s`, `s ∈ FIRST(G(r, p))`, `r ∈ LAST(G(s, q))`.
    let conflict = vec![
        Rule::new(
            RuleName("expr-begins-type"),
            Sort::Expression,
            base,
            Regex::seq([Regex::sort(Sort::Type), Regex::tile(TileLabel("x"))]),
        ),
        Rule::new(
            RuleName("type-ends-expr"),
            Sort::Type,
            base,
            Regex::seq([Regex::tile(TileLabel("y")), Regex::sort(Sort::Expression)]),
        ),
    ];
    assert_eq!(
        Err(PbgError::Assumption3Conflict {
            first_sort: Sort::Expression,
            second_sort: Sort::Type,
        }),
        validate_assumption_3(&conflict)
    );

    // A type form that ends with a type hole instead: no pair, accepted.
    let accepted = vec![
        Rule::new(
            RuleName("expr-begins-type-only"),
            Sort::Expression,
            base,
            Regex::seq([Regex::sort(Sort::Type), Regex::tile(TileLabel("x"))]),
        ),
        Rule::new(
            RuleName("type-begins-tile"),
            Sort::Type,
            base,
            Regex::seq([Regex::tile(TileLabel("y")), Regex::sort(Sort::Type)]),
        ),
    ];
    assert_eq!(Ok(()), validate_assumption_3(&accepted));
}

#[test]
fn pbg_rejects_duplicate_rule_names_deterministically() -> Result<(), Box<dyn Error>>
{
    let (_dag, base) = one_node_dag()?;
    let error = exact_error(vec![
        Rule::new(
            RuleName("repeated-rule"),
            Sort::Expression,
            base,
            Regex::tile(TileLabel("first-label")),
        ),
        Rule::new(
            RuleName("repeated-rule"),
            Sort::Type,
            base,
            Regex::tile(TileLabel("second-label")),
        ),
    ])?;

    assert_eq!(
        PbgError::DuplicateRule {
            name: "repeated-rule",
        },
        error
    );
    Ok(())
}

#[test]
fn pbg_rejects_invalid_prec_before_later_header_errors() -> Result<(), Box<dyn Error>>
{
    let invalid = Prec::new(PrecIndex::from(1));
    let error = exact_error(vec![
        Rule::new(
            RuleName("invalid-before-duplicate"),
            Sort::Expression,
            invalid,
            Regex::tile(TileLabel("invalid-prec-label")),
        ),
        Rule::new(
            RuleName("invalid-before-duplicate"),
            Sort::Type,
            Prec::new(PrecIndex::from(0)),
            Regex::tile(TileLabel("duplicate-name-label")),
        ),
    ])?;

    assert_eq!(
        PbgError::InvalidPrec {
            rule: "invalid-before-duplicate",
            prec: invalid,
        },
        error
    );
    Ok(())
}
