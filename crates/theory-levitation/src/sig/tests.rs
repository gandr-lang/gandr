use alloc::vec;
use alloc::vec::Vec;

use super::SigFault;
use super::SigOperation;
use super::SigParts;
use super::SigPort;
use super::SigRule;
use super::SigSort;
use super::SigValue;
use super::Tag;
use super::sig_desc;
use crate::boundary::ConstructorTag;
use crate::code::CodeView;
use crate::code::Name;
use crate::code::PrimTy;
use crate::code::ValueTypeRef;
use crate::generic::DescValue;
use crate::generic::Payload;
use crate::rule::FreeTerm;
use crate::test_support::Grade;
use crate::wellformed::check_desc;

/// A port of the given name at a sort over index terms.
///
/// # Specification
/// trivial.
fn port<Named, Sorted, Indices>(
    name: Named,
    sort: Sorted,
    indices: Indices,
) -> SigPort
where
    Named: Into<Name>,
    Sorted: Into<Name>,
    Indices: IntoIterator<Item = FreeTerm>,
{
    SigPort {
        name: name.into(),
        sort: sort.into(),
        indices: indices.into_iter().collect(),
    }
}

/// A presentation exercising every constructor of the code: an indexed sort,
/// an unnamed output, a two-output operation and rules whose sides apply an
/// operation, a constructor and a results tuple.
///
/// # Specification
/// trivial.
fn cat_like() -> SigParts
{
    let x = || FreeTerm::var("x");
    SigParts {
        sorts: vec![
            SigSort {
                name: Name::from("Ob"),
                indices: Vec::new(),
            },
            SigSort {
                name: Name::from("Hom"),
                indices: vec![port("dom", "Ob", []), port("cod", "Ob", [])],
            },
        ],
        operations: vec![
            SigOperation {
                name: Name::from("id"),
                inputs: vec![port("a", "Ob", [])],
                outputs: vec![port("", "Hom", [FreeTerm::var("a"), FreeTerm::var("a")])],
            },
            SigOperation {
                name: Name::from("split"),
                inputs: vec![port("m", "Ob", [])],
                outputs: vec![port("q", "Ob", []), port("r", "Ob", [])],
            },
        ],
        rules: vec![
            SigRule {
                name: Name::from("unitL"),
                left: FreeTerm::op("comp", [
                    FreeTerm::op("id", [FreeTerm::var("a")]),
                    FreeTerm::var("f"),
                ]),
                right: FreeTerm::var("f"),
            },
            SigRule {
                name: Name::from("halves"),
                left: FreeTerm::op("split", [FreeTerm::ctor("Pair", [x(), x()])]),
                right: FreeTerm::results([x(), x()]),
            },
        ],
    }
}

#[test]
fn the_code_is_one_data_sort_of_eleven_constructors()
{
    let desc = sig_desc(Grade::One);
    assert_eq!(
        check_desc(&desc),
        [],
        "the code is a well-formed description"
    );
    let string = ValueTypeRef::prim(PrimTy::StringTy);
    let fields: Vec<(&str, Vec<&str>)> = desc
        .ctors
        .iter()
        .map(|ctor| {
            let mut leaves = Vec::new();
            let mut pending = vec![ctor.code.to_node()];
            while let Some(node) = pending.pop() {
                match node.view() {
                    | CodeView::Prod(mut factors) => {
                        let (left, right) = (factors.next(), factors.next());
                        pending.extend(right);
                        pending.extend(left);
                    },
                    | CodeView::Field { ty, grade, .. } => {
                        assert_eq!((ty, *grade), (&string, Grade::One));
                        leaves.push("String");
                    },
                    | CodeView::Var(sort) => {
                        assert_eq!(sort.as_ref(), "Sig");
                        leaves.push("Sig");
                    },
                    | CodeView::Unit => {},
                    | CodeView::Sum(_) | CodeView::Bind { .. } => {
                        panic!("the code has no sum and no binder");
                    },
                }
            }
            (ctor.name.as_ref(), leaves)
        })
        .collect();
    assert_eq!(fields, [
        ("Presents", vec!["Sig", "Sig", "Sig"]),
        ("End", vec![]),
        ("Sort", vec!["String", "Sig", "Sig"]),
        ("Oper", vec!["String", "Sig", "Sig", "Sig"]),
        ("Port", vec!["String", "String", "Sig", "Sig"]),
        ("Rule", vec!["String", "Sig", "Sig", "Sig"]),
        ("Var", vec!["String"]),
        ("App", vec!["String", "Sig"]),
        ("Con", vec!["String", "Sig"]),
        ("Tuple", vec!["Sig"]),
        ("Arg", vec!["Sig", "Sig"]),
    ]);
}

#[test]
fn a_presentation_round_trips_through_its_value()
{
    let parts = cat_like();
    let value = SigValue::encode(&parts);
    assert_eq!(value.decode(), Ok(parts.clone()), "every member reads back");
    let mut dropped = parts.clone();
    dropped.operations.truncate(1);
    assert_ne!(
        SigValue::encode(&dropped),
        value,
        "a dropped operation is another value"
    );
    let mut reordered = parts;
    reordered.sorts.reverse();
    assert_ne!(
        SigValue::encode(&reordered),
        value,
        "the order of the sorts is part of the value"
    );
}

#[test]
fn a_presentation_encodes_to_its_exact_identity_bytes()
{
    let one_sort = SigParts {
        sorts: vec![SigSort {
            name: Name::from("M"),
            indices: Vec::new(),
        }],
        operations: Vec::new(),
        rules: Vec::new(),
    };
    assert_eq!(
        SigValue::encode(&one_sort).identity().as_ref(),
        [
            0, 0, 0, 0, // Presents
            2, 0, 0, 0, // Sort
            1, 0, 0, 0, b'M', // its name
            1, 0, 0, 0, // End: no indices
            1, 0, 0, 0, // End: no further sort
            1, 0, 0, 0, // End: no operation
            1, 0, 0, 0, // End: no rule
        ],
        "the tag of each constructor, then its fields left to right"
    );
    let parts = cat_like();
    assert_eq!(
        SigValue::encode(&parts).identity(),
        SigValue::encode(&cat_like()).identity(),
        "one presentation has one identity"
    );
    let mut renamed = parts.clone();
    if let Some(operation) = renamed.operations.first_mut()
        && let Some(input) = operation.inputs.first_mut()
    {
        input.name = Name::from("b");
    }
    assert_ne!(
        SigValue::encode(&renamed).identity(),
        SigValue::encode(&parts).identity(),
        "a renamed port is another presentation"
    );
}

/// A value of the constructor `tag` over the payload `payload`.
///
/// # Specification
/// trivial.
fn node(
    tag: Tag,
    payload: Payload,
) -> DescValue
{
    DescValue::new(tag.constructor(), payload)
}

/// The empty chain.
///
/// # Specification
/// trivial.
fn end() -> Payload
{
    Payload::rec(node(Tag::End, Payload::unit()))
}

/// A presentation whose sort chain is `sorts` and whose other chains are
/// empty.
///
/// # Specification
/// trivial.
fn presenting(sorts: DescValue) -> SigValue
{
    SigValue::from_value(node(
        Tag::Presents,
        Payload::pair(Payload::rec(sorts), Payload::pair(end(), end())),
    ))
}

/// The variable `x`.
///
/// # Specification
/// trivial.
fn var() -> Payload
{
    Payload::rec(node(Tag::Var, Payload::leaf(&b"x"[..])))
}

#[test]
fn a_value_outside_the_grammar_is_refused_by_name()
{
    assert_eq!(
        SigValue::from_value(node(Tag::End, Payload::unit())).decode(),
        Err(SigFault::Misplaced(ConstructorTag::from(1_usize))),
        "an `End` root presents nothing"
    );
    assert_eq!(
        SigValue::from_value(node(Tag::Presents, Payload::unit())).decode(),
        Err(SigFault::Payload),
        "a root without its three chains"
    );
    let rule = |left: Payload| {
        node(
            Tag::Rule,
            Payload::pair(
                Payload::leaf(&b"r"[..]),
                Payload::pair(left, Payload::pair(var(), end())),
            ),
        )
    };
    assert_eq!(
        presenting(rule(var())).decode(),
        Err(SigFault::Misplaced(ConstructorTag::from(5_usize))),
        "a rule in the sort chain"
    );
    let port_as_term = Payload::rec(node(
        Tag::Port,
        Payload::pair(
            Payload::leaf(&b"p"[..]),
            Payload::pair(Payload::leaf(&b"Ob"[..]), Payload::pair(end(), end())),
        ),
    ));
    let rules_holding_a_port = SigValue::from_value(node(
        Tag::Presents,
        Payload::pair(
            end(),
            Payload::pair(end(), Payload::rec(rule(port_as_term))),
        ),
    ));
    assert_eq!(
        rules_holding_a_port.decode(),
        Err(SigFault::Misplaced(ConstructorTag::from(4_usize))),
        "a port where a term stands"
    );
    let unreadable = node(
        Tag::Sort,
        Payload::pair(Payload::leaf(&[0xFF_u8][..]), Payload::pair(end(), end())),
    );
    assert_eq!(
        presenting(unreadable).decode(),
        Err(SigFault::Text),
        "a name that is not UTF-8"
    );
}
