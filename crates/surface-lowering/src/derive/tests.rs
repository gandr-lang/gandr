//! A rule a theory's completion derives, planned as the proof its rewriting
//! is.

use alloc::borrow::ToOwned as _;
use alloc::collections::BTreeSet;
use alloc::string::ToString;
use alloc::vec::Vec;

use gandr_surface_parser::parse;
use gandr_surface_syntax::SourceText;
use gandr_theory_levitation::FreeTerm;
use gandr_theory_levitation::Name;
use quenchant_shape::shape::Maybe;

use super::DeriveFault;
use super::Fired;
use super::Lemma;
use super::plan;
use crate::coincide::Decisions;
use crate::desc_cells::elaborate_desc_cells;
use crate::description::elaborate_descriptions;
use crate::fixture::grammar;
use crate::model::ModelFault;
use crate::model::ModelForm;
use crate::unit::Unit;

/// A group presented by its left unit, associativity and left inverse.
const GROUP: &str = "theory Grp {
  sort G : Type;
  oper e : G;
  oper inv : (x : G) --> G;
  oper mul : (x : G, y : G) --> G;
  rule unitL : mul(e(), x) <=> x;
  rule assoc : mul(mul(x, y), z) <=> mul(x, mul(y, z));
  rule invL : mul(inv(x), x) <=> e();
}";

/// [`plan`] of `left <=> right` in the group, named `r`.
///
/// # Specification
/// trivial.
fn planned(
    left: &FreeTerm,
    right: &FreeTerm,
) -> Result<Vec<Lemma>, DeriveFault>
{
    let grammar = grammar();
    let Ok(parsed) = parse(&grammar, SourceText::from(GROUP))
    else {
        panic!("the group parses")
    };
    let tree = parsed.into_tree();
    let Ok(report) = elaborate_descriptions(&grammar, &tree, &Unit::single())
    else {
        panic!("the group elaborates")
    };
    let cells = elaborate_desc_cells(&report.declarations, &mut Decisions::none());
    let (&[ref theory], &[ref theory_cells]) = (
        report.declarations.as_slice(),
        cells.declarations.as_slice(),
    )
    else {
        panic!("one theory, with its cells")
    };
    let Maybe::Present(ref presentation) = theory.presentation
    else {
        panic!("the theory presents its members")
    };
    plan(
        (&Name::from("r"), theory.at),
        (left, right),
        presentation,
        theory_cells,
    )
}

#[test]
fn a_derived_rule_states_its_law_over_the_theory()
{
    let (x, y) = (FreeTerm::var("x"), FreeTerm::var("y"));
    let left = FreeTerm::op("inv", [FreeTerm::op("mul", [x.clone(), y.clone()])]);
    let right = FreeTerm::op("mul", [FreeTerm::op("inv", [y]), FreeTerm::op("inv", [x])]);
    let lemmas = planned(&left, &right).expect("completion derives the inverse of a product");
    let Some((statement, earlier)) = lemmas.split_last()
    else {
        panic!("a plan holds its statement")
    };
    let ModelForm::Law {
        ref telescope,
        left: ref stated_left,
        right: ref stated_right,
        ..
    } = statement.law
    else {
        panic!("the statement is a law")
    };
    assert_eq!(
        (stated_left, stated_right),
        (&left, &right),
        "the statement states its sides"
    );
    assert_eq!(
        telescope
            .iter()
            .map(|binder| binder.name.to_string())
            .collect::<BTreeSet<_>>(),
        BTreeSet::from(["x".to_owned(), "y".to_owned()]),
        "the statement binds its variables"
    );
    assert!(
        !earlier.is_empty(),
        "the inverse of a product rests on rules completion derived"
    );
    assert_eq!(
        statement.legs.each_ref().map(|leg| (&leg.from, leg.back)),
        [(&left, false), (&right, true)],
        "the statement rewrites its left side to the normal form, then its right side back"
    );
    for (place, lemma) in lemmas.iter().enumerate() {
        for step in lemma.legs.iter().flat_map(|leg| &leg.steps) {
            if let Fired::Lemma(fired) = step.fired {
                assert!(
                    fired.0 < place,
                    "lemma {place} fires lemma {} before it is proved",
                    fired.0
                );
            }
        }
    }
}

#[test]
fn sides_the_completion_keeps_apart_are_refused()
{
    let (x, y) = (FreeTerm::var("x"), FreeTerm::var("y"));
    let left = FreeTerm::op("mul", [x.clone(), y.clone()]);
    let right = FreeTerm::op("mul", [y, x]);
    assert_eq!(planned(&left, &right), Err(DeriveFault::Apart));
}

#[test]
fn a_side_naming_no_operation_is_refused()
{
    let left = FreeTerm::op("square", [FreeTerm::var("x")]);
    assert_eq!(
        planned(&left, &FreeTerm::var("x")),
        Err(DeriveFault::Unsorted(ModelFault::UnknownHead))
    );
}

#[test]
fn each_derive_fault_reads_as_its_own_clause()
{
    let faults = [
        DeriveFault::Apart,
        DeriveFault::Incoherent,
        DeriveFault::Indexed,
        DeriveFault::Unstated(ModelFault::Circuit),
        DeriveFault::Unsorted(ModelFault::Circuit),
        DeriveFault::Erased,
        DeriveFault::Undecided,
    ];
    let clauses: BTreeSet<_> = faults.iter().map(ToString::to_string).collect();
    assert_eq!(clauses.len(), faults.len(), "{clauses:?}");
}
