//! Witnesses for a theory read as an effect interface.

use alloc::collections::BTreeMap;
use alloc::vec;
use alloc::vec::Vec;

use gandr_core_term::effect::OperationName;
use gandr_surface_parser::parse;
use gandr_surface_syntax::NodeIndex;
use gandr_surface_syntax::SourceText;
use gandr_theory_levitation::Name;
use quenchant_shape::shape::Maybe;

use super::TheoryOperation;
use super::operations;
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
        read
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
