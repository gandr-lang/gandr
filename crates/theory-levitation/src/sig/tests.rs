use alloc::vec;
use alloc::vec::Vec;

use quenchant_shape::shape::Maybe;

use super::SigBinder;
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
use crate::boundary::ShapePoint;
use crate::boundary::ShapeSize;
use crate::code::CodeView;
use crate::code::Name;
use crate::code::PrimTy;
use crate::code::ValueTypeRef;
use crate::desc::Representability;
use crate::desc::ShapeFace;
use crate::desc::SignShape;
use crate::desc::shape_parameter;
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
        bindings: Vec::new(),
    }
}

/// An unindexed binder of the given name at a sort.
///
/// # Specification
/// trivial.
fn binder<Named, Sorted>(
    name: Named,
    sort: Sorted,
) -> SigBinder
where
    Named: Into<Name>,
    Sorted: Into<Name>,
{
    SigBinder {
        name: name.into(),
        sort: sort.into(),
        indices: Vec::new(),
    }
}

/// An unindexed sort of the given name and representability.
///
/// # Specification
/// trivial.
fn sort<Named>(
    name: Named,
    representability: Representability,
) -> SigSort
where
    Named: Into<Name>,
{
    SigSort {
        name: name.into(),
        indices: Vec::new(),
        representability,
    }
}

/// Pure λ-calculus syntax as a second-order presentation: a representable
/// sort of terms, an abstraction whose body binds a term, and an application.
///
/// # Specification
/// trivial.
fn lambda() -> SigParts
{
    let mut body = port("t", "Tm", []);
    body.bindings = vec![binder("x", "Tm")];
    SigParts {
        sorts: vec![sort("Tm", Representability::Representable)],
        operations: vec![
            SigOperation {
                name: Name::from("lam"),
                inputs: vec![body],
                outputs: vec![port("", "Tm", [])],
            },
            SigOperation {
                name: Name::from("app"),
                inputs: vec![port("t", "Tm", []), port("u", "Tm", [])],
                outputs: vec![port("", "Tm", [])],
            },
        ],
        rules: Vec::new(),
        ..SigParts::default()
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
        sorts: vec![sort("Ob", Representability::Ordinary), SigSort {
            name: Name::from("Hom"),
            indices: vec![port("dom", "Ob", []), port("cod", "Ob", [])],
            representability: Representability::Ordinary,
        }],
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
        ..SigParts::default()
    }
}

#[test]
fn the_code_is_one_data_sort_of_fifteen_constructors()
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
                    CodeView::Prod(mut factors) => {
                        let (left, right) = (factors.next(), factors.next());
                        pending.extend(right);
                        pending.extend(left);
                    },
                    CodeView::Field { ty, grade, .. } => {
                        assert_eq!((ty, *grade), (&string, Grade::One));
                        leaves.push("String");
                    },
                    CodeView::Var(sort) => {
                        assert_eq!(sort.as_ref(), "Sig");
                        leaves.push("Sig");
                    },
                    CodeView::Unit => {},
                    CodeView::Sum(_) | CodeView::Bind { .. } => {
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
        ("Representable", vec!["String", "Sig", "Sig"]),
        ("Bound", vec!["String", "String", "Sig", "Sig", "Sig"]),
        ("Shape", vec!["String", "String", "Sig", "Sig"]),
        ("Face", vec!["String", "String", "Sig"]),
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
        sorts: vec![sort("M", Representability::Ordinary)],
        ..SigParts::default()
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

#[test]
fn a_second_order_presentation_encodes_its_binders()
{
    let parts = lambda();
    let value = SigValue::encode(&parts);
    assert_eq!(
        value.decode(),
        Ok(parts.clone()),
        "the representable sort and the binder read back"
    );
    assert_eq!(
        value.identity().as_ref(),
        [
            0, 0, 0, 0, // Presents
            11, 0, 0, 0, // Representable
            2, 0, 0, 0, b'T', b'm', // its name
            1, 0, 0, 0, // End: no indices
            1, 0, 0, 0, // End: no further sort
            3, 0, 0, 0, // Oper
            3, 0, 0, 0, b'l', b'a', b'm', // its name
            12, 0, 0, 0, // Bound: its first input
            1, 0, 0, 0, b't', // the port's name
            2, 0, 0, 0, b'T', b'm', // its sort
            1, 0, 0, 0, // End: no index argument
            4, 0, 0, 0, // Port: the binder
            1, 0, 0, 0, b'x', // the binder's name
            2, 0, 0, 0, b'T', b'm', // its sort
            1, 0, 0, 0, // End: no index argument
            1, 0, 0, 0, // End: no further binder
            1, 0, 0, 0, // End: no further input
            4, 0, 0, 0, // Port: the output
            0, 0, 0, 0, // unnamed
            2, 0, 0, 0, b'T', b'm', // its sort
            1, 0, 0, 0, // End: no index argument
            1, 0, 0, 0, // End: no further output
            3, 0, 0, 0, // Oper
            3, 0, 0, 0, b'a', b'p', b'p', // its name
            4, 0, 0, 0, // Port
            1, 0, 0, 0, b't', // its name
            2, 0, 0, 0, b'T', b'm', // its sort
            1, 0, 0, 0, // End: no index argument
            4, 0, 0, 0, // Port
            1, 0, 0, 0, b'u', // its name
            2, 0, 0, 0, b'T', b'm', // its sort
            1, 0, 0, 0, // End: no index argument
            1, 0, 0, 0, // End: no further input
            4, 0, 0, 0, // Port: the output
            0, 0, 0, 0, // unnamed
            2, 0, 0, 0, b'T', b'm', // its sort
            1, 0, 0, 0, // End: no index argument
            1, 0, 0, 0, // End: no further output
            1, 0, 0, 0, // End: no further operation
            1, 0, 0, 0, // End: no rule
        ],
        "a representable sort and a bound port take their own tags"
    );
    let mut ordinary = parts.clone();
    if let Some(only) = ordinary.sorts.first_mut() {
        only.representability = Representability::Ordinary;
    }
    assert_ne!(
        SigValue::encode(&ordinary),
        value,
        "representability is part of the value"
    );
    let mut unbound = parts.clone();
    if let Some(lam) = unbound.operations.first_mut()
        && let Some(body) = lam.inputs.first_mut()
    {
        body.bindings.clear();
    }
    assert_ne!(
        SigValue::encode(&unbound),
        value,
        "a binder is part of the value"
    );
    let mut twice = parts;
    if let Some(app) = twice.operations.get_mut(1)
        && let Some(function) = app.inputs.first_mut()
    {
        function.bindings = vec![binder("y", "Tm"), binder("z", "Tm")];
    }
    assert_eq!(
        SigValue::encode(&twice).decode(),
        Ok(twice.clone()),
        "a telescope of two binders reads back outermost first"
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

#[test]
fn a_shaped_presentation_codes_its_faces()
{
    let points = |raw: &[usize]| {
        raw.iter()
            .copied()
            .map(ShapePoint::from)
            .collect::<Vec<_>>()
    };
    let shaped = SigParts {
        shape: Maybe::Present(SignShape::new("Square", ShapeSize::from(4_usize), [
            ShapeFace::new("left", points(&[2, 0])),
            ShapeFace::new("none", []),
        ])),
        sorts: vec![sort("M", Representability::Ordinary)],
        ..SigParts::default()
    };
    let value = SigValue::encode(&shaped);
    assert_eq!(
        value.decode(),
        Ok(shaped.clone()),
        "the shape and its faces read back"
    );
    assert_eq!(
        value.identity().as_ref(),
        [
            0, 0, 0, 0, // Presents
            13, 0, 0, 0, // Shape
            6, 0, 0, 0, b'S', b'q', b'u', b'a', b'r', b'e', // its name
            1, 0, 0, 0, b'4', // its size
            14, 0, 0, 0, // Face
            4, 0, 0, 0, b'l', b'e', b'f', b't', // its name
            3, 0, 0, 0, b'0', b',', b'2', // its points, ascending
            14, 0, 0, 0, // Face
            4, 0, 0, 0, b'n', b'o', b'n', b'e', // its name
            0, 0, 0, 0, // no point
            1, 0, 0, 0, // End: no further face
            2, 0, 0, 0, // Sort
            1, 0, 0, 0, b'M', // its name
            1, 0, 0, 0, // End: no indices
            1, 0, 0, 0, // End: no further sort
            1, 0, 0, 0, // End: no operation
            1, 0, 0, 0, // End: no rule
        ],
        "the shape heads the sort chain, each face its points' one spelling"
    );
    let unshaped = SigParts {
        shape: Maybe::Absent(shape_parameter::Absent::Unshaped),
        ..shaped
    };
    assert_ne!(
        SigValue::encode(&unshaped).identity(),
        value.identity(),
        "a shape is part of the presentation"
    );
    let shape = |size: &[u8], faces: Payload, rest: Payload| {
        node(
            Tag::Shape,
            Payload::pair(
                Payload::leaf(&b"S"[..]),
                Payload::pair(Payload::leaf(size), Payload::pair(faces, rest)),
            ),
        )
    };
    let face = |spelled: &[u8]| {
        Payload::rec(node(
            Tag::Face,
            Payload::pair(
                Payload::leaf(&b"f"[..]),
                Payload::pair(Payload::leaf(spelled), end()),
            ),
        ))
    };
    assert_eq!(
        presenting(shape(b"2", face(b"0,1"), end()))
            .decode()
            .map(|parts| parts.shape),
        Ok(Maybe::Present(SignShape::new(
            "S",
            ShapeSize::from(2_usize),
            [ShapeFace::new("f", points(&[0, 1]))]
        ))),
        "a hand-built shape reads"
    );
    assert_eq!(
        presenting(shape(b"2", end(), Payload::rec(shape(b"2", end(), end())))).decode(),
        Err(SigFault::Misplaced(ConstructorTag::from(13_usize))),
        "a second shape is misplaced"
    );
    for size in [&b"2,3"[..], b"", b"02", b"+2", b"two"] {
        assert_eq!(
            presenting(shape(size, end(), end())).decode(),
            Err(SigFault::Numeral),
            "a size is one numeral in its one spelling: {size:?}"
        );
    }
    for spelled in [&b"1,0"[..], b"0,0", b"0,", b",1", b"00"] {
        assert_eq!(
            presenting(shape(b"2", face(spelled), end())).decode(),
            Err(SigFault::Numeral),
            "a face's points ascend once each in their one spelling: {spelled:?}"
        );
    }
}

/// A `Bound` port named `t` at `Tm`, under the binder chain `binders`,
/// before `rest`.
///
/// # Specification
/// trivial.
fn bound(
    binders: Payload,
    rest: Payload,
) -> DescValue
{
    node(
        Tag::Bound,
        Payload::pair(
            Payload::leaf(&b"t"[..]),
            Payload::pair(
                Payload::leaf(&b"Tm"[..]),
                Payload::pair(end(), Payload::pair(binders, rest)),
            ),
        ),
    )
}

/// A plain port named `x` at `Tm`, before `rest`.
///
/// # Specification
/// trivial.
fn plain(rest: Payload) -> Payload
{
    Payload::rec(node(
        Tag::Port,
        Payload::pair(
            Payload::leaf(&b"x"[..]),
            Payload::pair(Payload::leaf(&b"Tm"[..]), Payload::pair(end(), rest)),
        ),
    ))
}

/// A presentation of one operation `f` whose inputs are the chain `inputs`
/// and which has no output.
///
/// # Specification
/// trivial.
fn operating(inputs: DescValue) -> SigValue
{
    let operation = node(
        Tag::Oper,
        Payload::pair(
            Payload::leaf(&b"f"[..]),
            Payload::pair(Payload::rec(inputs), Payload::pair(end(), end())),
        ),
    );
    SigValue::from_value(node(
        Tag::Presents,
        Payload::pair(end(), Payload::pair(Payload::rec(operation), end())),
    ))
}

#[test]
fn a_binder_outside_an_operation_port_is_misplaced()
{
    let bound_tag = ConstructorTag::from(12_usize);
    assert_eq!(
        operating(bound(plain(end()), end())).decode().map(|parts| {
            parts
                .operations
                .into_iter()
                .flat_map(|operation| operation.inputs)
                .map(|input| input.bindings.len())
                .collect::<Vec<_>>()
        }),
        Ok(vec![1]),
        "an operation's port binds"
    );
    let binding_index = node(
        Tag::Sort,
        Payload::pair(
            Payload::leaf(&b"S"[..]),
            Payload::pair(Payload::rec(bound(plain(end()), end())), end()),
        ),
    );
    assert_eq!(
        presenting(binding_index).decode(),
        Err(SigFault::Misplaced(bound_tag)),
        "a sort's index port binds nothing"
    );
    assert_eq!(
        operating(bound(Payload::rec(bound(plain(end()), end())), end())).decode(),
        Err(SigFault::Misplaced(bound_tag)),
        "a binder binds nothing of its own"
    );
    assert_eq!(
        operating(bound(end(), end())).decode(),
        Err(SigFault::Misplaced(ConstructorTag::from(1_usize))),
        "a bound port binds at least one variable"
    );
}
