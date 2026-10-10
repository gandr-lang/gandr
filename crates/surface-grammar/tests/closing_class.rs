//! The closing-class derivation: a property of a form's completion paths, not
//! of the tile that carries it, computed per rule on the condensation of the
//! rule's tile graph.

use core::error::Error;

use anodized::spec;
use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::Regex;
use gandr_surface_grammar::Rule;
use gandr_surface_grammar::RuleName;
use gandr_surface_grammar::Sort;
use gandr_surface_grammar::TileLabel;
use gandr_surface_grammar::built_in;
use gandr_surface_syntax::ClosingClass;
use gandr_theory_graphs::Assoc;
use gandr_theory_graphs::PrecDag;
use gandr_theory_graphs::PrecSpec;

/// A grammar of one item rule with form `regex`.
///
/// # Specification
/// - requires: `regex` passes the gates.
/// - ensures: returns the grammar.
/// - fails: a gate refuses `regex`.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For the finite completion-path fixtures, L2 closing-class
///   observations catch wrong rule assembly and lost gate errors. The predicate
///   observes the one-rule header or its concrete construction error; arbitrary
///   regexes and resource exhaustion are not exhausted.
/// - witness: `tests::closing_class::closing_class_is_form_level`
/// - witness: `tests::closing_class::closing_class_repeat_with_exit_shares_its_component_answer`
#[spec(ensures: |ret| ret.as_ref().map_or_else(|error| error.downcast_ref::<gandr_surface_grammar::PbgError>().is_some(), |pbg| pbg.rules().len() == 1 && pbg.rules().first().is_some_and(|rule| rule.name().0 == "only" && rule.sort() == Sort::Item && pbg.dag().name(rule.prec()).is_some_and(|name| name == "atom"))))]
fn one_rule(regex: Regex) -> Result<Pbg, Box<dyn Error>>
{
    let mut spec = PrecSpec::new();
    let atom = spec.insert("atom", Assoc::Non)?;
    let dag = PrecDag::build(&spec)?;
    Ok(Pbg::build(dag, vec![Rule::new(
        RuleName("only"),
        Sort::Item,
        atom,
        regex,
    )])?)
}

/// Three ways the derivation can be wrong, one obligation each. A repeat
/// stays interior, so a container member reaching `}` only after any number
/// of further members still derives `Brace`. A form whose completions end at
/// something that closes nothing derives nothing, which keeps `def name = E ;`
/// unclassed. And the count of unclassed item braces is pinned, so a
/// container family that stops deriving its class moves it.
#[test]
fn closing_class_is_form_level() -> Result<(), Box<dyn Error>>
{
    let pbg = built_in()?;
    let braces = pbg.candidates(TileLabel("{"));

    // A brace derives `Brace` or nothing, never another family.
    for &mold in braces {
        assert!(
            matches!(pbg.closing_class(mold), Some(ClosingClass::Brace) | None),
            "a `{{` never derives a family it does not close, mold {mold:?}"
        );
    }

    // Every module body derives `Brace`: members are held by reference, and
    // a member force-closed on its own must name the closer it stands in for.
    let mut module_bodies = 0_usize;
    for &mold in braces {
        if pbg.mold(mold)?.sort == Sort::ModuleMember {
            assert_eq!(Some(ClosingClass::Brace), pbg.closing_class(mold));
            module_bodies = module_bodies.checked_add(1).expect("the count fits");
        }
    }
    assert!(module_bodies > 0);

    // Exactly two braces derive nothing, both item-sort.
    let unclassed: Vec<Sort> = braces
        .iter()
        .filter(|&&mold| pbg.closing_class(mold).is_none())
        .map(|&mold| pbg.mold(mold).map(|def| def.sort))
        .collect::<Result<_, _>>()?;
    assert_eq!(vec![Sort::Item, Sort::Item], unclassed);

    // A module member's `=` reaches `}` across the member repeat; a
    // definition's `=` completes at `;`.
    let equals: Vec<Option<ClosingClass>> = pbg
        .candidates(TileLabel("="))
        .iter()
        .map(|&mold| pbg.closing_class(mold))
        .collect();
    assert!(equals.contains(&Some(ClosingClass::Brace)), "{equals:?}");
    assert!(equals.contains(&None), "{equals:?}");

    // A statement's `;` is its form's terminal and closes nothing; a
    // container member's `;` is mid-form and completes into the `}`.
    let semis: Vec<Option<ClosingClass>> = pbg
        .candidates(TileLabel(";"))
        .iter()
        .map(|&mold| pbg.closing_class(mold))
        .collect();
    assert!(semis.contains(&None), "{semis:?}");
    assert!(semis.contains(&Some(ClosingClass::Brace)), "{semis:?}");
    assert!(
        semis
            .iter()
            .all(|class| matches!(class, None | Some(ClosingClass::Brace))),
        "{semis:?}"
    );

    // Divergent alternatives intersect to nothing: one tail closes the
    // bracket, the other ends at a tile that closes nothing.
    let divergent = one_rule(Regex::seq([
        Regex::tile(TileLabel("(")),
        Regex::alt([Regex::tile(TileLabel(")")), Regex::tile(TileLabel("!"))]),
    ]))?;
    for &mold in divergent.candidates(TileLabel("(")) {
        assert_eq!(None, divergent.closing_class(mold));
    }

    // A closer the rule never opens is unpaired.
    let unopened = one_rule(Regex::seq([
        Regex::tile(TileLabel("x")),
        Regex::tile(TileLabel("}")),
    ]))?;
    for &mold in unopened.candidates(TileLabel("x")) {
        assert_eq!(None, unopened.closing_class(mold));
    }

    // Past the table there is no class.
    let past = gandr_surface_syntax::MoldId::try_from(pbg.mold_count().0)?;
    assert_eq!(None, pbg.closing_class(past));
    Ok(())
}

/// A repeat with an exit, `a → b`, `b → a`, `b → )`, separates the
/// condensation fold from a per-node memo with a visiting set: entered at
/// `a`, such a memo records `b` before the exit's family is known, and a
/// later query from `b` reads the incomplete entry. Every tile of the
/// bracketed repeat must derive the bracket's family.
#[test]
fn closing_class_repeat_with_exit_shares_its_component_answer() -> Result<(), Box<dyn Error>>
{
    let pbg = one_rule(Regex::seq([
        Regex::tile(TileLabel("(")),
        Regex::repeat(Regex::seq([
            Regex::tile(TileLabel("a")),
            Regex::tile(TileLabel("b")),
        ])),
        Regex::tile(TileLabel(")")),
    ]))?;
    for label in ["(", "a", "b"] {
        for &mold in pbg.candidates(TileLabel(label)) {
            assert_eq!(
                Some(ClosingClass::Paren),
                pbg.closing_class(mold),
                "{label} reaches the `)` exit"
            );
        }
    }
    Ok(())
}
