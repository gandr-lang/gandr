//! Witnesses for a theory read as an effect interface.

use alloc::collections::BTreeMap;
use alloc::vec;
use alloc::vec::Vec;

use gandr_core_term::Binders;
use gandr_core_term::effect::OperationName;
use gandr_core_term::handler::subject::SubjectRule;
use gandr_kernel_term::RuleIndex;
use gandr_surface_parser::parse;
use gandr_surface_syntax::NodeIndex;
use gandr_surface_syntax::SourceText;
use gandr_theory_levitation::Name;
use gandr_theory_levitation::RuleTurn;
use quenchant_shape::shape::Maybe;

use super::TheoryOperation;
use super::laws;
use super::operations;
use super::rules;
use crate::description::elaborate_descriptions;
use crate::fixture::grammar;
use crate::model::InterfaceFault;
use crate::model::Members;
use crate::unit::Unit;

/// The state theory: a value sort the handler fixes, the carrier, and an
/// operation reading the value and one writing it.
const STATE: &str = r"theory State {
  sort S : Type+;
  sort C : Type;
  oper get : (k : pi+ (s : S) . C) --> C;
  oper put : (s : S, k : C) --> C;
}";

/// A cost theory: the cost sort the handler fixes, the carrier, a charge, and
/// the cost monoid's unit and sum, with decalf's two laws.
const COST: &str = r"theory Cost {
  sort N : Type+;
  sort C : Type;
  oper charge : (c : N, k : C) --> C;
  oper zero : N;
  oper plus : (a : N, b : N) --> N;
  rule chargeZero : charge(zero(), k) <=> k;
  rule chargeTwice : charge(a, charge(b, k)) <=> charge(plus(a, b), k);
}";

/// The members of the one theory `source` declares.
///
/// # Specification
/// trivial.
fn members(source: SourceText<'_>) -> Members
{
    let grammar = grammar();
    let tree = parse(&grammar, source).unwrap().into_tree();
    let report = elaborate_descriptions(&grammar, &tree, &Unit::single()).unwrap();
    let [ref theory] = *report.declarations.as_slice()
    else {
        panic!("one theory declared");
    };
    let Maybe::Present(ref presentation) = theory.presentation
    else {
        panic!("a theory presents its members");
    };
    presentation.members().unwrap()
}

/// A manifest fixing each of `sorts` at a type node of its own, in order.
///
/// # Specification
/// trivial.
fn fixing(sorts: impl IntoIterator<Item = Name>) -> BTreeMap<Name, NodeIndex>
{
    sorts
        .into_iter()
        .enumerate()
        .map(|(position, sort)| (sort, NodeIndex::from(position.saturating_add(100))))
        .collect()
}

#[test]
fn state_reads_as_a_get_and_a_put_2272()
{
    let fixed = fixing([Name::from("S")]);
    let integer = NodeIndex::from(100_usize);
    let read = operations(&members(SourceText::from(STATE)), &fixed).unwrap();
    assert_eq!(
        vec![
            TheoryOperation {
                name: OperationName::from("get"),
                payload: Vec::new(),
                reply: vec![integer],
            },
            TheoryOperation {
                name: OperationName::from("put"),
                payload: vec![integer],
                reply: Vec::new(),
            },
        ],
        read.effects
    );
    assert!(read.values.is_empty(), "state has no value operation");
}

/// A cost theory's `zero` and `plus` take and return the fixed cost sort, so
/// they read as value operations apart from `charge`, and both laws, each
/// applying one, are the model's to state; State's laws, which apply none,
/// are read as before beside the same value operations (#2288).
#[test]
fn a_value_operation_is_read_apart_from_the_effects_2288()
{
    let fixed = fixing([Name::from("N")]);
    let cost = NodeIndex::from(100_usize);
    let members_of = members(SourceText::from(COST));
    let read = operations(&members_of, &fixed).unwrap();
    assert_eq!(
        vec![TheoryOperation {
            name: OperationName::from("charge"),
            payload: vec![cost],
            reply: Vec::new(),
        }],
        read.effects
    );
    assert_eq!(
        read.values
            .iter()
            .map(|value| value.name.clone())
            .collect::<Vec<Name>>(),
        [Name::from("zero"), Name::from("plus")],
        "the unit and the sum, in the theory's order"
    );
    assert!(
        laws(&members_of, &read.effects, &read.values)
            .unwrap()
            .is_empty(),
        "each law applies a value operation, which no clause answers"
    );
    let state_fixed = fixing([Name::from("S")]);
    let state = members(SourceText::from(PUT_LAWS));
    let state_read = operations(&state, &state_fixed).unwrap();
    assert_eq!(
        laws(&state, &state_read.effects, &read.values)
            .unwrap()
            .len(),
        2,
        "a law applying no value operation is read for the clauses"
    );
}

#[test]
fn each_member_out_of_shape_is_refused_by_its_fault_2272()
{
    let cases: [(&str, &[&str], &str, InterfaceFault); 6] = [
        (
            r"theory Ix {
  sort C : Type;
  sort V(c : C) : Type;
  oper get : (k : pi+ (s : C) . C) --> C;
}",
            &["V"],
            "V",
            InterfaceFault::Indexed,
        ),
        (STATE, &["S", "C"], "C", InterfaceFault::Fixed),
        (STATE, &[], "S", InterfaceFault::Unfixed),
        (
            r"theory Peek {
  sort S : Type+;
  sort C : Type;
  oper get : (k : pi+ (s : S) . C) --> C;
  oper peek : (k : C) --> S;
}",
            &["S"],
            "peek",
            InterfaceFault::Carrier,
        ),
        (
            r"theory Ends {
  sort S : Type+;
  sort C : Type;
  oper get : (k : pi+ (s : S) . C) --> C;
  oper put : (k : C, s : S) --> C;
}",
            &["S"],
            "put",
            InterfaceFault::Continuation,
        ),
        (
            r"theory Twice {
  sort S : Type+;
  sort C : Type;
  oper get : (k : pi+ (s : S) . C) --> C;
  oper or : (l : C, r : C) --> C;
}",
            &["S"],
            "or",
            InterfaceFault::Payload,
        ),
    ];
    for (source, fixed, member, fault) in cases {
        let fixed = fixing(fixed.iter().map(|&sort| Name::from(sort)));
        let Err((named, refused)) = operations(&members(SourceText::from(source)), &fixed)
        else {
            panic!("{member} is out of shape in {source}");
        };
        assert_eq!(fault, refused, "{member}'s fault");
        assert_eq!(
            Some(member),
            source.get(usize::from(named.span.start()) .. usize::from(named.span.end())),
            "the refusal stands at {member}'s name"
        );
    }
}

/// The state theory with both store laws: put-get and put-put.
const PUT_LAWS: &str = r"theory StatePutLaws {
  sort S : Type+;
  sort C : Type;
  oper get : (k : pi+ (s : S) . C) --> C;
  oper put : (s : S, k : C) --> C;
  rule putGet : put(s, get(bind t . k(t))) <=> put(s, k(s));
  rule putPut : put(s, put(u, k)) <=> put(u, k);
}";

/// Each law of a theory reads for its handler at its place among the
/// theory's rules, over the metavariables it names; a law storing what a
/// metavariable makes of a value is no term a clause reads, and is refused at
/// its name.
#[test]
fn a_theory_s_laws_read_for_its_handler_2272()
{
    let fixed = fixing([Name::from("S")]);
    let members_of = members(SourceText::from(PUT_LAWS));
    let read_of = operations(&members_of, &fixed).unwrap();
    let read = laws(&members_of, &read_of.effects, &read_of.values).unwrap();
    let placed: Vec<(RuleIndex, Binders)> = read
        .iter()
        .map(|law| (law.rule, law.read.metavariables))
        .collect();
    assert_eq!(
        placed,
        [
            (RuleIndex::from(0_usize), Binders::from(2_u32)),
            (RuleIndex::from(1_usize), Binders::from(3_u32)),
        ],
        "put-get over `s` and `k`, put-put over `s`, `u` and `k`, in order"
    );
    let odd = r"theory Odd {
  sort S : Type+;
  sort C : Type;
  oper get : (k : pi+ (s : S) . C) --> C;
  oper put : (s : S, k : C) --> C;
  rule putPut : put(s, put(f(s), k)) <=> put(f(s), k);
}";
    let members_of = members(SourceText::from(odd));
    let read_of = operations(&members_of, &fixed).unwrap();
    let Err((named, fault)) = laws(&members_of, &read_of.effects, &read_of.values)
    else {
        panic!("a law storing `f(s)` is no term a clause reads");
    };
    assert_eq!(fault, InterfaceFault::Law);
    assert_eq!(
        Some("putPut"),
        odd.get(usize::from(named.span.start()) .. usize::from(named.span.end())),
        "the refusal stands at the law's name"
    );
}

/// The theory's laws read as rewrites of a scope's subject, each from the side
/// its orientation puts above: get-get, put-get and put-put read at their
/// places, and a law reordering a put and a get is left out; get-get marked
/// turned is read from its right side, which grows, and is left out too
/// (#2272).
#[test]
fn a_theory_s_laws_rewrite_its_scope_s_subject_2272()
{
    let fixed = fixing([Name::from("S")]);
    let laws_of = r"theory StateLaws {
  sort S : Type+;
  sort C : Type;
  oper get : (k : pi+ (s : S) . C) --> C;
  oper put : (s : S, k : C) --> C;
  rule getGet : get(bind s . get(bind t . k(s, t))) <=> get(bind s . k(s, s));
  rule swap : put(s, get(bind t . k(t))) <=> get(bind t . put(s, k(t)));
  rule putGet : put(s, get(bind t . k(t))) <=> put(s, k(s));
  rule putPut : put(s, put(u, k)) <=> put(u, k);
}";
    let members_of = members(SourceText::from(laws_of));
    let operations_of = operations(&members_of, &fixed).unwrap();
    let read = |turns: &[RuleTurn]| -> Vec<RuleIndex> {
        rules(&members_of, &operations_of.effects, turns)
            .iter()
            .map(SubjectRule::rule)
            .collect()
    };
    assert_eq!(
        read(&[]),
        [0_usize, 2, 3].map(RuleIndex::from),
        "get-get, put-get and put-put, the reordering left out"
    );
    assert_eq!(
        read(&[
            RuleTurn::Turned,
            RuleTurn::AsWritten,
            RuleTurn::AsWritten,
            RuleTurn::AsWritten,
        ]),
        [2_usize, 3].map(RuleIndex::from),
        "get-get read from its right side grows"
    );
}
