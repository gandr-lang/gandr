use alloc::vec;
use alloc::vec::Vec;

use quenchant_shape::shape::Maybe;

use super::DerivedFace;
use super::DerivedPeak;
use super::IncludeClash;
use super::OperationKind;
use super::RuleCertificate;
use super::RuleTurn;
use super::SidePlace;
use super::Tag;
use super::TheoryBinder;
use super::TheoryFault;
use super::TheoryOperation;
use super::TheoryParts;
use super::TheoryPort;
use super::TheoryRule;
use super::TheorySort;
use super::TheoryValue;
use super::theory_desc;
use crate::boundary::ConstructorTag;
use crate::boundary::RuleIndex;
use crate::boundary::ShapePoint;
use crate::boundary::ShapeSize;
use crate::code::CodeView;
use crate::code::Name;
use crate::code::PrimTy;
use crate::code::ValueTypeRef;
use crate::desc::Representability;
use crate::desc::ShapeFace;
use crate::desc::TheoryShape;
use crate::desc::shape_parameter;
use crate::generic::DescValue;
use crate::generic::Payload;
use crate::rule::FreeTerm;
use crate::termination::Rank;
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
) -> TheoryPort
where
    Named: Into<Name>,
    Sorted: Into<Name>,
    Indices: IntoIterator<Item = FreeTerm>,
{
    TheoryPort {
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
) -> TheoryBinder
where
    Named: Into<Name>,
    Sorted: Into<Name>,
{
    TheoryBinder {
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
) -> TheorySort
where
    Named: Into<Name>,
{
    TheorySort {
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
fn lambda() -> TheoryParts
{
    let mut body = port("t", "Tm", []);
    body.bindings = vec![binder("x", "Tm")];
    TheoryParts {
        sorts: vec![sort("Tm", Representability::Representable)],
        operations: vec![
            TheoryOperation {
                name: Name::from("lam"),
                kind: OperationKind::Operation,
                inputs: vec![body],
                outputs: vec![port("", "Tm", [])],
            },
            TheoryOperation {
                name: Name::from("app"),
                kind: OperationKind::Operation,
                inputs: vec![port("t", "Tm", []), port("u", "Tm", [])],
                outputs: vec![port("", "Tm", [])],
            },
        ],
        rules: Vec::new(),
        ..TheoryParts::default()
    }
}

/// A presentation exercising every constructor of the code: an indexed sort,
/// an unnamed output, a two-output operation, an observation between two
/// operations and rules whose sides apply an operation, a constructor and a
/// results tuple.
///
/// # Specification
/// trivial.
fn cat_like() -> TheoryParts
{
    let x = || FreeTerm::var("x");
    TheoryParts {
        sorts: vec![sort("Ob", Representability::Ordinary), TheorySort {
            name: Name::from("Hom"),
            indices: vec![port("dom", "Ob", []), port("cod", "Ob", [])],
            representability: Representability::Ordinary,
        }],
        operations: vec![
            TheoryOperation {
                name: Name::from("id"),
                kind: OperationKind::Operation,
                inputs: vec![port("a", "Ob", [])],
                outputs: vec![port("", "Hom", [FreeTerm::var("a"), FreeTerm::var("a")])],
            },
            TheoryOperation {
                name: Name::from("dom"),
                kind: OperationKind::Observation,
                inputs: vec![port("f", "Hom", [FreeTerm::var("a"), FreeTerm::var("b")])],
                outputs: vec![port("", "Ob", [])],
            },
            TheoryOperation {
                name: Name::from("split"),
                kind: OperationKind::Operation,
                inputs: vec![port("m", "Ob", [])],
                outputs: vec![port("q", "Ob", []), port("r", "Ob", [])],
            },
        ],
        rules: vec![
            TheoryRule {
                name: Name::from("unitL"),
                left: FreeTerm::op("comp", [
                    FreeTerm::op("id", [FreeTerm::var("a")]),
                    FreeTerm::var("f"),
                ]),
                right: FreeTerm::var("f"),
            },
            TheoryRule {
                name: Name::from("halves"),
                left: FreeTerm::op("split", [FreeTerm::ctor("Pair", [x(), x()])]),
                right: FreeTerm::results([x(), x()]),
            },
        ],
        ..TheoryParts::default()
    }
}

#[test]
fn the_code_is_one_data_sort_of_twenty_constructors()
{
    let desc = theory_desc(Grade::One);
    assert_eq!(
        check_desc(&desc),
        [],
        "the code is a well-formed description"
    );
    let string = ValueTypeRef::prim(PrimTy::StringTy);
    let mut pending = Vec::new();
    let fields: Vec<(&str, Vec<&str>)> = desc
        .ctors
        .iter()
        .map(|ctor| {
            let mut leaves = Vec::new();
            pending.push(ctor.code.to_node());
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
                        assert_eq!(sort.as_ref(), "Theory");
                        leaves.push("Theory");
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
        ("Presents", vec!["Theory", "Theory", "Theory"]),
        ("End", vec![]),
        ("Sort", vec!["String", "Theory", "Theory"]),
        ("Oper", vec!["String", "Theory", "Theory", "Theory"]),
        ("Port", vec!["String", "String", "Theory", "Theory"]),
        ("Rule", vec!["String", "Theory", "Theory", "Theory"]),
        ("Var", vec!["String"]),
        ("App", vec!["String", "Theory"]),
        ("Con", vec!["String", "Theory"]),
        ("Tuple", vec!["Theory"]),
        ("Arg", vec!["Theory", "Theory"]),
        ("Representable", vec!["String", "Theory", "Theory"]),
        ("Bound", vec![
            "String", "String", "Theory", "Theory", "Theory"
        ]),
        ("Shape", vec!["String", "String", "Theory", "Theory"]),
        ("Face", vec!["String", "String", "Theory"]),
        ("Obs", vec!["String", "Theory", "Theory", "Theory"]),
        ("Turned", vec!["String", "Theory", "Theory", "Theory"]),
        ("Derived", vec![
            "String", "String", "String", "Theory", "Theory", "Theory"
        ]),
        ("Rank", vec!["String", "String", "Theory"]),
        ("Const", vec!["String", "Theory", "Theory", "Theory"]),
    ]);
    let counted: Vec<(usize, usize)> = fields
        .iter()
        .map(|&(_, ref leaves)| {
            let strings = leaves.iter().filter(|&&leaf| leaf == "String").count();
            (strings, leaves.len() - strings)
        })
        .collect();
    assert_eq!(
        counted,
        gandr_kernel_term::PRESENTATION_CODE,
        "the kernel recognises the code by this table"
    );
}

#[test]
fn a_certified_presentation_carries_its_rule_certificate()
{
    let parts = cat_like();
    let certificate = RuleCertificate {
        turns: vec![RuleTurn::AsWritten, RuleTurn::Turned],
        derived: vec![DerivedFace {
            left: FreeTerm::op("comp", [FreeTerm::var("g"), FreeTerm::var("f")]),
            right: FreeTerm::var("g"),
            peak: DerivedPeak {
                outer: RuleIndex::from(1_usize),
                position: SidePlace::from(1_usize),
                inner: RuleIndex::from(0_usize),
            },
        }],
        ranks: vec![
            (Name::from("comp"), Rank::from(2_usize)),
            (Name::from("id"), Rank::from(1_usize)),
        ],
    };
    let value = TheoryValue::encode_certified(&parts, &certificate);
    assert_eq!(value.certificate(), Ok(certificate));
    assert_eq!(
        value.decode(),
        Ok(parts.clone()),
        "the written rules decode"
    );
    let plain = TheoryValue::encode(&parts);
    assert_eq!(
        plain.certificate().map(|read| read.turns),
        Ok(vec![RuleTurn::AsWritten; 2]),
        "an uncertified value reads every rule as written"
    );
    assert_ne!(plain, value, "the certificate is part of the value");
    let derived = |outer: &'static [u8], rest: Payload| {
        node(
            Tag::Derived,
            Payload::pair(
                Payload::leaf(outer),
                Payload::pair(
                    Payload::leaf(&b"0"[..]),
                    Payload::pair(
                        Payload::leaf(&b"0"[..]),
                        Payload::pair(var(), Payload::pair(var(), rest)),
                    ),
                ),
            ),
        )
    };
    let rules_of = |chain: DescValue| {
        TheoryValue::from_value(node(
            Tag::Presents,
            Payload::pair(end(), Payload::pair(end(), Payload::rec(chain))),
        ))
    };
    assert_eq!(
        rules_of(derived(&b"01"[..], end())).certificate(),
        Err(TheoryFault::Numeral),
        "a padded peak numeral"
    );
    let rank_first = node(
        Tag::Rank,
        Payload::pair(
            Payload::leaf(&b"comp"[..]),
            Payload::pair(
                Payload::leaf(&b"1"[..]),
                Payload::rec(derived(&b"0"[..], end())),
            ),
        ),
    );
    assert_eq!(
        rules_of(rank_first).certificate(),
        Err(TheoryFault::Misplaced(ConstructorTag::from(17_usize))),
        "a rank before a derived rule"
    );
}

#[test]
fn a_presentation_round_trips_through_its_value()
{
    let parts = cat_like();
    let value = TheoryValue::encode(&parts);
    assert_eq!(value.decode(), Ok(parts.clone()), "every member reads back");
    let mut dropped = parts.clone();
    dropped.operations.truncate(1);
    assert_ne!(
        TheoryValue::encode(&dropped),
        value,
        "a dropped operation is another value"
    );
    let mut reordered = parts.clone();
    reordered.sorts.reverse();
    assert_ne!(
        TheoryValue::encode(&reordered),
        value,
        "the order of the sorts is part of the value"
    );
    let mut constructive = parts;
    for operation in &mut constructive.operations {
        operation.kind = OperationKind::Operation;
    }
    assert_ne!(
        TheoryValue::encode(&constructive),
        value,
        "an observation is not the operation of the same ports"
    );
}

#[test]
fn a_presentation_encodes_to_its_exact_identity_bytes()
{
    let one_sort = TheoryParts {
        sorts: vec![sort("M", Representability::Ordinary)],
        ..TheoryParts::default()
    };
    assert_eq!(
        TheoryValue::encode(&one_sort).identity().as_ref(),
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
        TheoryValue::encode(&parts).identity(),
        TheoryValue::encode(&cat_like()).identity(),
        "one presentation has one identity"
    );
    let mut renamed = parts.clone();
    if let Some(operation) = renamed.operations.first_mut()
        && let Some(input) = operation.inputs.first_mut()
    {
        input.name = Name::from("b");
    }
    assert_ne!(
        TheoryValue::encode(&renamed).identity(),
        TheoryValue::encode(&parts).identity(),
        "a renamed port is another presentation"
    );
}

#[test]
fn a_second_order_presentation_encodes_its_binders()
{
    let parts = lambda();
    let value = TheoryValue::encode(&parts);
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
        TheoryValue::encode(&ordinary),
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
        TheoryValue::encode(&unbound),
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
        TheoryValue::encode(&twice).decode(),
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
fn presenting(sorts: DescValue) -> TheoryValue
{
    TheoryValue::from_value(node(
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
        TheoryValue::from_value(node(Tag::End, Payload::unit())).decode(),
        Err(TheoryFault::Misplaced(ConstructorTag::from(1_usize))),
        "an `End` root presents nothing"
    );
    assert_eq!(
        TheoryValue::from_value(node(Tag::Presents, Payload::unit())).decode(),
        Err(TheoryFault::Payload),
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
        Err(TheoryFault::Misplaced(ConstructorTag::from(5_usize))),
        "a rule in the sort chain"
    );
    let port_as_term = Payload::rec(node(
        Tag::Port,
        Payload::pair(
            Payload::leaf(&b"p"[..]),
            Payload::pair(Payload::leaf(&b"Ob"[..]), Payload::pair(end(), end())),
        ),
    ));
    let rules_holding_a_port = TheoryValue::from_value(node(
        Tag::Presents,
        Payload::pair(
            end(),
            Payload::pair(end(), Payload::rec(rule(port_as_term))),
        ),
    ));
    assert_eq!(
        rules_holding_a_port.decode(),
        Err(TheoryFault::Misplaced(ConstructorTag::from(4_usize))),
        "a port where a term stands"
    );
    let unreadable = node(
        Tag::Sort,
        Payload::pair(Payload::leaf(&[0xFF_u8][..]), Payload::pair(end(), end())),
    );
    assert_eq!(
        presenting(unreadable).decode(),
        Err(TheoryFault::Text),
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
    let shaped = TheoryParts {
        shape: Maybe::Present(TheoryShape::new("Square", ShapeSize::from(4_usize), [
            ShapeFace::new("left", points(&[2, 0])),
            ShapeFace::new("none", []),
        ])),
        sorts: vec![sort("M", Representability::Ordinary)],
        ..TheoryParts::default()
    };
    let value = TheoryValue::encode(&shaped);
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
    let unshaped = TheoryParts {
        shape: Maybe::Absent(shape_parameter::Absent::Unshaped),
        ..shaped
    };
    assert_ne!(
        TheoryValue::encode(&unshaped).identity(),
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
        Ok(Maybe::Present(TheoryShape::new(
            "S",
            ShapeSize::from(2_usize),
            [ShapeFace::new("f", points(&[0, 1]))]
        ))),
        "a hand-built shape reads"
    );
    assert_eq!(
        presenting(shape(b"2", end(), Payload::rec(shape(b"2", end(), end())))).decode(),
        Err(TheoryFault::Misplaced(ConstructorTag::from(13_usize))),
        "a second shape is misplaced"
    );
    for size in [&b"2,3"[..], b"", b"02", b"+2", b"two"] {
        assert_eq!(
            presenting(shape(size, end(), end())).decode(),
            Err(TheoryFault::Numeral),
            "a size is one numeral in its one spelling: {size:?}"
        );
    }
    for spelled in [&b"1,0"[..], b"0,0", b"0,", b",1", b"00"] {
        assert_eq!(
            presenting(shape(b"2", face(spelled), end())).decode(),
            Err(TheoryFault::Numeral),
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
fn operating(inputs: DescValue) -> TheoryValue
{
    let operation = node(
        Tag::Oper,
        Payload::pair(
            Payload::leaf(&b"f"[..]),
            Payload::pair(Payload::rec(inputs), Payload::pair(end(), end())),
        ),
    );
    TheoryValue::from_value(node(
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
        Err(TheoryFault::Misplaced(bound_tag)),
        "a sort's index port binds nothing"
    );
    assert_eq!(
        operating(bound(Payload::rec(bound(plain(end()), end())), end())).decode(),
        Err(TheoryFault::Misplaced(bound_tag)),
        "a binder binds nothing of its own"
    );
    assert_eq!(
        operating(bound(end(), end())).decode(),
        Err(TheoryFault::Misplaced(ConstructorTag::from(1_usize))),
        "a bound port binds at least one variable"
    );
}

/// A magma: one sort and one binary operation, associative by its one rule.
///
/// # Specification
/// trivial.
fn semigroup() -> TheoryParts
{
    let m = |name: &str| port(name, "M", []);
    let mul = |left: FreeTerm, right: FreeTerm| FreeTerm::op("mul", [left, right]);
    let v = FreeTerm::var;
    TheoryParts {
        sorts: vec![sort("M", Representability::Ordinary)],
        operations: vec![TheoryOperation {
            name: Name::from("mul"),
            kind: OperationKind::Operation,
            inputs: vec![m("x"), m("y")],
            outputs: vec![m("")],
        }],
        rules: vec![TheoryRule {
            name: Name::from("assoc"),
            left: mul(mul(v("x"), v("y")), v("z")),
            right: mul(v("x"), mul(v("y"), v("z"))),
        }],
        ..TheoryParts::default()
    }
}

/// One nullary operation on `M` of the given name, and the rule of the given
/// name making it a left unit of `mul`.
///
/// # Specification
/// trivial.
fn unit_named(
    operation: Name,
    rule: Name,
) -> (TheoryOperation, TheoryRule)
{
    (
        TheoryOperation {
            name: operation.clone(),
            kind: OperationKind::Operation,
            inputs: Vec::new(),
            outputs: vec![port("", "M", [])],
        },
        TheoryRule {
            name: rule,
            left: FreeTerm::op("mul", [FreeTerm::op(operation, []), FreeTerm::var("x")]),
            right: FreeTerm::var("x"),
        },
    )
}

#[test]
fn an_extension_restricts_to_what_it_includes()
{
    let (one, unit_left) = unit_named(Name::from("one"), Name::from("unitL"));
    let mut monoid = TheoryParts {
        operations: vec![one.clone()],
        rules: vec![unit_left.clone()],
        ..TheoryParts::default()
    };
    let included = semigroup();
    let inclusion = monoid.include(&included).unwrap();
    assert_eq!(monoid.restrict(&inclusion), included);
    assert_eq!(
        monoid.sorts, included.sorts,
        "the included sort is appended"
    );
    assert_eq!(
        monoid.operations,
        [one, included.operations[0].clone()],
        "the included operation follows the parts' own"
    );
    assert_eq!(monoid.rules, [unit_left, included.rules[0].clone()]);
    let positions = |list: &[super::MemberPosition]| {
        list.iter()
            .map(|&position| usize::from(position))
            .collect::<Vec<_>>()
    };
    assert_eq!(positions(&inclusion.sorts), [0]);
    assert_eq!(positions(&inclusion.operations), [1]);
    assert_eq!(positions(&inclusion.rules), [1]);
    let value = TheoryValue::encode(&monoid);
    assert_eq!(
        value.decode().unwrap().restrict(&inclusion),
        included,
        "the extension's value restricts as its parts do"
    );
}

#[test]
fn two_extensions_of_one_presentation_meet_along_it()
{
    let (one, unit_left) = unit_named(Name::from("one"), Name::from("unitL"));
    let (zero, zero_left) = unit_named(Name::from("zero"), Name::from("zeroL"));
    let mut pointed = semigroup();
    pointed.operations.push(one);
    pointed.rules.push(unit_left);
    let mut copointed = semigroup();
    copointed.operations.push(zero);
    copointed.rules.push(zero_left);
    let mut both = TheoryParts::default();
    let first = both.include(&pointed).unwrap();
    let second = both.include(&copointed).unwrap();
    assert_eq!(both.sorts.len(), 1, "the shared sort is one sort");
    assert_eq!(
        both.operations
            .iter()
            .map(|operation| operation.name.as_ref())
            .collect::<Vec<_>>(),
        ["mul", "one", "zero"]
    );
    assert_eq!(
        both.rules
            .iter()
            .map(|rule| rule.name.as_ref())
            .collect::<Vec<_>>(),
        ["assoc", "unitL", "zeroL"]
    );
    assert_eq!(both.restrict(&first), pointed);
    assert_eq!(both.restrict(&second), copointed);
    assert_eq!(
        first.operations.first(),
        second.operations.first(),
        "both inclusions send the shared operation to one position"
    );
}

#[test]
fn a_member_defined_twice_blocks_the_extension_by_name()
{
    let mut other = semigroup();
    other.rules[0].right = FreeTerm::var("x");
    let mut parts = semigroup();
    assert_eq!(
        parts.include(&other),
        Err(IncludeClash::Rule(Name::from("assoc")))
    );
    assert_eq!(parts, semigroup(), "a refused extension leaves the parts");
    let mut indexed = semigroup();
    indexed.sorts[0].indices = vec![port("n", "M", [])];
    assert_eq!(
        parts.include(&indexed),
        Err(IncludeClash::Sort(Name::from("M")))
    );
    let mut shaped = semigroup();
    shaped.shape = Maybe::Present(TheoryShape::new("Line", ShapeSize::from(2_usize), []));
    assert_eq!(parts.include(&shaped), Err(IncludeClash::Shaped));
    assert_eq!(parts, semigroup());
}
