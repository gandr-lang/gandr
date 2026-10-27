use alloc::boxed::Box;

use gandr_kernel_strata::Level;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Magnitude;
use gandr_kernel_term::Summand;

use super::*;
use crate::boundary::ProducerArity;
use crate::il::CopatternArm;
use crate::il::CovariableIndex;
use crate::il::PatternArm;

/// `⟨() |+ ★⟩` renders as itself.
#[test]
fn renders_terminal_cut()
{
    let mut arena = CommandArena::new();
    let unit = arena
        .mint_producer(ProducerNode::Constructor {
            tag: ConstructorTag::Tuple(ProducerArity::ZERO),
            producers: Box::from([]),
            consumers: Box::from([]),
        })
        .expect("a leaf mints");
    let top = arena
        .mint_consumer(ConsumerNode::Top)
        .expect("a leaf mints");
    let cut = arena
        .mint_cut(Polarity::Positive, unit, top)
        .expect("children resolve");
    assert_eq!("⟨() |+ ★⟩", render_command(&arena, cut), "the terminal cut");
}

/// `λ. return x` focused against `★` renders its copattern object at a
/// negative cut.
#[test]
fn renders_lambda_cocase()
{
    let mut arena = CommandArena::new();
    let variable = arena
        .mint_producer(ProducerNode::Variable {
            zone: Zone::Intuitionistic,
            index: 0_u32.into(),
        })
        .expect("a leaf mints");
    let back = arena
        .mint_consumer(ConsumerNode::Covariable(CovariableIndex::from(0_u32)))
        .expect("a leaf mints");
    let body = arena
        .mint_cut(Polarity::Positive, variable, back)
        .expect("children resolve");
    let object = arena
        .mint_producer(ProducerNode::Cocase {
            arms: Box::from([CopatternArm {
                destructor: DestructorTag::Apply,
                body,
            }]),
        })
        .expect("the body resolves");
    let top = arena
        .mint_consumer(ConsumerNode::Top)
        .expect("a leaf mints");
    let cut = arena
        .mint_cut(Polarity::Negative, object, top)
        .expect("children resolve");
    assert_eq!(
        "⟨cocase {apply(x; α) ⇒ ⟨x0 |+ α0⟩} |− ★⟩",
        render_command(&arena, cut),
        "the function cut"
    );
}

/// Every structural head renders in its notation: the constructors, a
/// thunk, a capture, the frames, a match, a value binder and a string.
#[test]
fn renders_structural_heads()
{
    let mut arena = CommandArena::new();
    let digits = Magnitude::from_decimal_text(String::from("42")).expect("decimal digits");
    let integer = arena
        .mint_producer(ProducerNode::Literal(Literal::Integer(
            IntegerLiteral::new(Sign::Negative, digits),
        )))
        .expect("a leaf mints");
    let string = arena
        .mint_producer(ProducerNode::Literal(Literal::Text(
            gandr_kernel_term::StringLiteral::new(String::from("a\"b")),
        )))
        .expect("a leaf mints");
    let pair = arena
        .mint_producer(ProducerNode::Constructor {
            tag: ConstructorTag::Tuple(ProducerArity::TWO),
            producers: Box::from([integer, string]),
            consumers: Box::from([]),
        })
        .expect("fields resolve");
    let right = arena
        .mint_producer(ProducerNode::Constructor {
            tag: ConstructorTag::Injection(Summand::from(1_usize)),
            producers: Box::from([pair]),
            consumers: Box::from([]),
        })
        .expect("fields resolve");
    let lifted = arena
        .mint_producer(ProducerNode::Constructor {
            tag: ConstructorTag::Lift(Level::zero()),
            producers: Box::from([right]),
            consumers: Box::from([]),
        })
        .expect("fields resolve");
    assert_eq!(
        "lift(inr(pair(-42, \"a\\\"b\")))",
        render_producer(&arena, lifted),
        "the constructors and literals"
    );

    let triple = arena
        .mint_producer(ProducerNode::Constructor {
            tag: ConstructorTag::Tuple(ProducerArity::from(3_usize)),
            producers: Box::from([integer, string, integer]),
            consumers: Box::from([]),
        })
        .expect("fields resolve");
    let third = arena
        .mint_producer(ProducerNode::Constructor {
            tag: ConstructorTag::Injection(Summand::from(2_usize)),
            producers: Box::from([triple]),
            consumers: Box::from([]),
        })
        .expect("fields resolve");
    assert_eq!(
        "inj[2](tuple(-42, \"a\\\"b\", -42))",
        render_producer(&arena, third),
        "a tuple and an injection past the binary ones"
    );

    let top = arena
        .mint_consumer(ConsumerNode::Top)
        .expect("a leaf mints");
    let constant = arena
        .mint_producer(ProducerNode::Constant(3_usize.into()))
        .expect("a leaf mints");
    let returned = arena
        .mint_cut(Polarity::Positive, constant, top)
        .expect("children resolve");
    let binder = arena
        .mint_consumer(ConsumerNode::MuTilde { body: returned })
        .expect("the body resolves");
    let apply = arena
        .mint_consumer(ConsumerNode::Destructor {
            tag: DestructorTag::Apply,
            producers: Box::from([constant]),
            consumers: Box::from([binder]),
        })
        .expect("children resolve");
    let force = arena
        .mint_consumer(ConsumerNode::Destructor {
            tag: DestructorTag::Force,
            producers: Box::from([]),
            consumers: Box::from([apply]),
        })
        .expect("children resolve");
    assert_eq!(
        "force(apply(c3; μ̃x. ⟨c3 |+ ★⟩))",
        render_consumer(&arena, force),
        "the frames and the value binder"
    );

    let matcher = arena
        .mint_consumer(ConsumerNode::Case {
            arms: Box::from([
                PatternArm {
                    constructor: ConstructorTag::Injection(Summand::from(0_usize)),
                    body: returned,
                },
                PatternArm {
                    constructor: ConstructorTag::Injection(Summand::from(1_usize)),
                    body: returned,
                },
                PatternArm {
                    constructor: ConstructorTag::Injection(Summand::from(2_usize)),
                    body: returned,
                },
                PatternArm {
                    constructor: ConstructorTag::Tuple(ProducerArity::from(3_usize)),
                    body: returned,
                },
            ]),
        })
        .expect("the arms resolve");
    let thunk = arena
        .mint_producer(ProducerNode::Thunk { body: returned })
        .expect("the body resolves");
    let capture = arena
        .mint_producer(ProducerNode::Mu { body: returned })
        .expect("the body resolves");
    let matched = arena
        .mint_cut(Polarity::Positive, thunk, matcher)
        .expect("children resolve");
    let captured = arena
        .mint_cut(Polarity::Positive, capture, top)
        .expect("children resolve");
    assert_eq!(
        "⟨{force(α) ⇒ ⟨c3 |+ ★⟩} |+ case {inl(x) ⇒ ⟨c3 |+ ★⟩ | inr(x) ⇒ ⟨c3 |+ ★⟩ | inj[2](x) ⇒ ⟨c3 |+ ★⟩ | tuple(x, x, x) ⇒ ⟨c3 |+ ★⟩}⟩",
        render_command(&arena, matched),
        "the thunk and the match"
    );
    assert_eq!(
        "⟨μα. ⟨c3 |+ ★⟩ |+ ★⟩",
        render_command(&arena, captured),
        "the capture"
    );
    assert_eq!(
        "<dangling>",
        render_command(&arena, CommandId::from(99_u32)),
        "a dangling root"
    );
}

/// A record writes its labels after its head and its fields in their
/// order, the record of none apart from the unit; a selection writes the
/// component or the label it reads and the continuation it returns to; a
/// structural arm on a record names its labels and binds one field each.
#[test]
fn renders_records_and_selections()
{
    let mut arena = CommandArena::new();
    let label = |name: &str| gandr_kernel_term::FieldLabel::from(String::from(name));
    let first = arena
        .mint_producer(ProducerNode::Constant(1_usize.into()))
        .expect("a leaf mints");
    let second = arena
        .mint_producer(ProducerNode::Constant(2_usize.into()))
        .expect("a leaf mints");
    let record = arena
        .mint_producer(ProducerNode::Constructor {
            tag: ConstructorTag::Record(alloc::sync::Arc::from([label("a"), label("b")])),
            producers: Box::from([second, first]),
            consumers: Box::from([]),
        })
        .expect("fields resolve");
    assert_eq!(
        "record{a, b}(c2, c1)",
        render_producer(&arena, record),
        "the labels, then the fields in their order"
    );
    let empty = arena
        .mint_producer(ProducerNode::Constructor {
            tag: ConstructorTag::Record(alloc::sync::Arc::from([])),
            producers: Box::from([]),
            consumers: Box::from([]),
        })
        .expect("a leaf mints");
    assert_eq!(
        "record{}()",
        render_producer(&arena, empty),
        "the record of no labels is not the unit"
    );

    let top = arena
        .mint_consumer(ConsumerNode::Top)
        .expect("a leaf mints");
    let by_label = arena
        .mint_consumer(ConsumerNode::Select {
            selector: Selector::Label(label("b")),
            then: top,
        })
        .expect("the continuation resolves");
    let by_position = arena
        .mint_consumer(ConsumerNode::Select {
            selector: Selector::Component(2_usize.into()),
            then: by_label,
        })
        .expect("the continuation resolves");
    assert_eq!(
        "select[2](select[.b](★))",
        render_consumer(&arena, by_position),
        "each selection's field, then its continuation"
    );

    let returned = arena
        .mint_cut(Polarity::Positive, first, top)
        .expect("children resolve");
    let matcher = arena
        .mint_consumer(ConsumerNode::Case {
            arms: Box::from([PatternArm {
                constructor: ConstructorTag::Record(alloc::sync::Arc::from([
                    label("a"),
                    label("b"),
                ])),
                body: returned,
            }]),
        })
        .expect("the arm resolves");
    assert_eq!(
        "case {record{a, b}(x, x) ⇒ ⟨c1 |+ ★⟩}",
        render_consumer(&arena, matcher),
        "a record arm binds one field per label"
    );
}

/// A datatype constructor writes its ordinal after its head, a nominal
/// match its branches and continuation, a structural arm on a datatype
/// constructor one binder per field, and a recursive thunk its evidence.
#[test]
fn renders_datatype_heads_nominal_matches_and_recursive_thunks()
{
    let mut arena = CommandArena::new();
    let zero = arena
        .mint_producer(ProducerNode::Constructor {
            tag: ConstructorTag::Data {
                tag: gandr_kernel_term::ConstructorTag::from(0_usize),
                arity: ProducerArity::ZERO,
                family: None,
            },
            producers: Box::from([]),
            consumers: Box::from([]),
        })
        .expect("a leaf mints");
    let constant = arena
        .mint_producer(ProducerNode::Constant(3_usize.into()))
        .expect("a leaf mints");
    let cons = arena
        .mint_producer(ProducerNode::Constructor {
            tag: ConstructorTag::Data {
                tag: gandr_kernel_term::ConstructorTag::from(1_usize),
                arity: ProducerArity::TWO,
                family: None,
            },
            producers: Box::from([constant, zero]),
            consumers: Box::from([]),
        })
        .expect("fields resolve");
    assert_eq!(
        "ctor[1](c3, ctor[0]())",
        render_producer(&arena, cons),
        "the ordinals and the fields in order"
    );

    let top = arena
        .mint_consumer(ConsumerNode::Top)
        .expect("a leaf mints");
    let returned = arena
        .mint_cut(Polarity::Positive, constant, top)
        .expect("children resolve");
    let branch = arena
        .mint_producer(ProducerNode::Thunk { body: returned })
        .expect("the body resolves");
    let nominal = arena
        .mint_consumer(ConsumerNode::DataCase {
            branches: Box::from([branch, constant]),
            arities: Box::from([
                gandr_kernel_term::FieldCount::from(0_usize),
                gandr_kernel_term::FieldCount::from(0_usize),
            ]),
            then: top,
        })
        .expect("children resolve");
    assert_eq!(
        "datacase({force(α) ⇒ ⟨c3 |+ ★⟩}, c3; ★)",
        render_consumer(&arena, nominal),
        "the branches in order, then the continuation"
    );

    let structural = arena
        .mint_consumer(ConsumerNode::Case {
            arms: Box::from([PatternArm {
                constructor: ConstructorTag::Data {
                    tag: gandr_kernel_term::ConstructorTag::from(2_usize),
                    arity: ProducerArity::TWO,
                    family: None,
                },
                body: returned,
            }]),
        })
        .expect("the arm resolves");
    assert_eq!(
        "case {ctor[2](x, x) ⇒ ⟨c3 |+ ★⟩}",
        render_consumer(&arena, structural),
        "one binder per field"
    );

    for (evidence, expected) in [
        (FixpointEvidence::Partial, "fix{x; force(α) ⇒ ⟨c3 |+ ★⟩}"),
        (
            FixpointEvidence::StructuralDescent,
            "fix[<]{x; force(α) ⇒ ⟨c3 |+ ★⟩}",
        ),
    ] {
        let recursive = arena
            .mint_producer(ProducerNode::Fixpoint {
                body: returned,
                evidence,
            })
            .expect("the body resolves");
        assert_eq!(
            expected,
            render_producer(&arena, recursive),
            "the evidence {evidence:?}"
        );
    }
}

/// Elision precedes lookup at the limit, while shallower missing addresses
/// stay visible.
#[test]
fn depth_limits_and_dangling_nodes_are_distinct()
{
    assert_eq!(RenderDepth(1), RenderDepth::ROOT.child());
    assert_eq!(
        RenderDepth(u32::MAX),
        RenderDepth(u32::MAX.saturating_sub(1)).child()
    );
    assert_eq!(RenderDepth(u32::MAX), RenderDepth(u32::MAX).child());
    let mut arena = CommandArena::new();
    let unit = arena
        .mint_producer(ProducerNode::Constructor {
            tag: ConstructorTag::Tuple(ProducerArity::ZERO),
            producers: Box::from([]),
            consumers: Box::from([]),
        })
        .expect("leaf");
    let top = arena.mint_consumer(ConsumerNode::Top).expect("leaf");
    let command = arena
        .mint_cut(Polarity::Positive, unit, top)
        .expect("children resolve");
    let missing_producer = ProducerId::from(u32::MAX);
    let missing_consumer = ConsumerId::from(u32::MAX);
    let missing_command = CommandId::from(u32::MAX);
    assert_eq!("<dangling>", render_producer(&arena, missing_producer));
    assert_eq!("<dangling>", render_consumer(&arena, missing_consumer));
    assert_eq!("<dangling>", render_command(&arena, missing_command));
    for piece in [
        Piece::Producer(unit, RenderDepth::LIMIT),
        Piece::Consumer(top, RenderDepth::LIMIT),
        Piece::Command(command, RenderDepth::LIMIT),
        Piece::Producer(missing_producer, RenderDepth::LIMIT),
        Piece::Consumer(missing_consumer, RenderDepth::LIMIT),
        Piece::Command(missing_command, RenderDepth::LIMIT),
    ] {
        assert_eq!("…", render(&arena, piece));
    }
    let below = RenderDepth(RenderDepth::LIMIT.0.saturating_sub(1));
    assert_eq!(
        "<dangling>",
        render(&arena, Piece::Producer(missing_producer, below))
    );
    let limit = usize::try_from(RenderDepth::LIMIT.0).expect("small fixed rendering limit");
    let mut nested = unit;
    let mut expected = String::new();
    for depth in 1_usize ..= limit.saturating_add(1) {
        nested = arena
            .mint_producer(ProducerNode::Constructor {
                tag: ConstructorTag::Injection(Summand::from(0_usize)),
                producers: Box::from([nested]),
                consumers: Box::from([]),
            })
            .expect("child resolves");
        if depth >= limit.saturating_sub(1) {
            let visible = depth.min(limit);
            let leaf = if depth < limit { "()" } else { "…" };
            expected.clear();
            for _ in 0 .. visible {
                expected.push_str("inl(");
            }
            expected.push_str(leaf);
            for _ in 0 .. visible {
                expected.push(')');
            }
            assert_eq!(expected, render_producer(&arena, nested));
        }
    }
    let mut broken = CommandArena::new();
    let leaf = broken
        .mint_producer(ProducerNode::Constructor {
            tag: ConstructorTag::Tuple(ProducerArity::ZERO),
            producers: Box::from([]),
            consumers: Box::from([]),
        })
        .expect("leaf");
    let pair = broken
        .mint_producer(ProducerNode::Constructor {
            tag: ConstructorTag::Tuple(ProducerArity::TWO),
            producers: Box::from([leaf, leaf]),
            consumers: Box::from([]),
        })
        .expect("children resolve");
    let terminal = broken.mint_consumer(ConsumerNode::Top).expect("leaf");
    let root = broken
        .mint_cut(Polarity::Positive, pair, terminal)
        .expect("children resolve");
    let mut prefix = CommandArena::new();
    let one = prefix
        .mint_producer(ProducerNode::Constructor {
            tag: ConstructorTag::Tuple(ProducerArity::ZERO),
            producers: Box::from([]),
            consumers: Box::from([]),
        })
        .expect("leaf");
    let end = prefix.mint_consumer(ConsumerNode::Top).expect("leaf");
    prefix
        .mint_cut(Polarity::Positive, one, end)
        .expect("children resolve");
    broken.truncate_to(prefix.watermark());
    assert_eq!("⟨<dangling> |+ ★⟩", render_command(&broken, root));
}

/// Unequal children expose punctuation and order in every list and arm
/// boundary case.
#[test]
fn structural_rendering_preserves_fields_arms_and_separators()
{
    let mut arena = CommandArena::new();
    let unit = arena
        .mint_producer(ProducerNode::Constructor {
            tag: ConstructorTag::Tuple(ProducerArity::ZERO),
            producers: Box::from([]),
            consumers: Box::from([]),
        })
        .expect("leaf");
    let variable = arena
        .mint_producer(ProducerNode::Variable {
            zone: Zone::Intuitionistic,
            index: 7_u32.into(),
        })
        .expect("leaf");
    let linear = arena
        .mint_producer(ProducerNode::Variable {
            zone: Zone::Linear,
            index: 9_u32.into(),
        })
        .expect("leaf");
    assert_eq!("l9", render_producer(&arena, linear));
    let top = arena.mint_consumer(ConsumerNode::Top).expect("leaf");
    let covariable = arena
        .mint_consumer(ConsumerNode::Covariable(1_u32.into()))
        .expect("leaf");
    assert_eq!("α1", render_consumer(&arena, covariable));
    for (producers, consumers, expected) in [
        ([].as_slice(), [].as_slice(), "pair()"),
        ([unit, variable].as_slice(), [].as_slice(), "pair((), x7)"),
        ([].as_slice(), [top, covariable].as_slice(), "pair(★, α1)"),
        (
            [unit, variable].as_slice(),
            [top, covariable].as_slice(),
            "pair((), x7; ★, α1)",
        ),
    ] {
        let producer = arena
            .mint_producer(ProducerNode::Constructor {
                tag: ConstructorTag::Tuple(ProducerArity::TWO),
                producers: Box::from(producers),
                consumers: Box::from(consumers),
            })
            .expect("references resolve even when arity does not");
        assert_eq!(expected, render_producer(&arena, producer));
    }
    let applied_unit = arena
        .mint_producer(ProducerNode::Constructor {
            tag: ConstructorTag::Tuple(ProducerArity::ZERO),
            producers: Box::from([unit]),
            consumers: Box::from([]),
        })
        .expect("child resolves");
    assert_eq!("unit(())", render_producer(&arena, applied_unit));
    let body = arena
        .mint_cut(Polarity::Positive, unit, top)
        .expect("children resolve");
    for (constructor, expected) in [
        (
            ConstructorTag::Tuple(ProducerArity::ZERO),
            "case {() ⇒ ⟨() |+ ★⟩}",
        ),
        (
            ConstructorTag::Tuple(ProducerArity::TWO),
            "case {pair(x, x) ⇒ ⟨() |+ ★⟩}",
        ),
        (
            ConstructorTag::Lift(Level::zero()),
            "case {lift(x) ⇒ ⟨() |+ ★⟩}",
        ),
        (ConstructorTag::ListNil, "case {nil ⇒ ⟨() |+ ★⟩}"),
        (ConstructorTag::ListCons, "case {cons(x, x) ⇒ ⟨() |+ ★⟩}"),
        (
            ConstructorTag::Recorded(alloc::sync::Arc::from([
                gandr_core_term::session::RecordedMove::Sent(()),
                gandr_core_term::session::RecordedMove::Selected(
                    gandr_kernel_term::FieldLabel::from(String::from("l")),
                ),
                gandr_core_term::session::RecordedMove::Offered(
                    gandr_kernel_term::FieldLabel::from(String::from("m")),
                ),
                gandr_core_term::session::RecordedMove::Received(()),
                gandr_core_term::session::RecordedMove::Closed,
            ])),
            "case {recorded[sent, selected(l), offered(m), received, closed](x, x) ⇒ ⟨() |+ ★⟩}",
        ),
    ] {
        let matcher = arena
            .mint_consumer(ConsumerNode::Case {
                arms: Box::from([PatternArm { constructor, body }]),
            })
            .expect("body resolves");
        assert_eq!(expected, render_consumer(&arena, matcher));
    }
    let empty_case = arena
        .mint_consumer(ConsumerNode::Case {
            arms: Box::from([]),
        })
        .expect("empty arms");
    assert_eq!("case {}", render_consumer(&arena, empty_case));
    let empty_object = arena
        .mint_producer(ProducerNode::Cocase {
            arms: Box::from([]),
        })
        .expect("empty arms");
    assert_eq!("cocase {}", render_producer(&arena, empty_object));
    let object = arena
        .mint_producer(ProducerNode::Cocase {
            arms: Box::from([
                CopatternArm {
                    destructor: DestructorTag::Apply,
                    body,
                },
                CopatternArm {
                    destructor: DestructorTag::Force,
                    body,
                },
            ]),
        })
        .expect("bodies resolve");
    assert_eq!(
        "cocase {apply(x; α) ⇒ ⟨() |+ ★⟩ | force(α) ⇒ ⟨() |+ ★⟩}",
        render_producer(&arena, object)
    );
}

/// Numeric fractions and escaped text preserve their payload and kind
/// distinction.
#[test]
fn literal_spelling_preserves_fraction_and_escaped_content()
{
    use gandr_kernel_term::CharacterLiteral;
    use gandr_kernel_term::FractionDigits;
    use gandr_kernel_term::NumericLiteral;
    use gandr_kernel_term::StringLiteral;

    let whole = Magnitude::from_decimal_text(String::from("12")).expect("digits");
    let fraction = FractionDigits::from_decimal_text(String::from("03")).expect("digits");
    for (literal, expected) in [
        (
            Literal::Integer(IntegerLiteral::new(Sign::NonNegative, Magnitude::zero())),
            "0",
        ),
        (
            Literal::Numeric(NumericLiteral::new(
                Sign::NonNegative,
                whole.clone(),
                fraction.clone(),
            )),
            "12.03",
        ),
        (
            Literal::Numeric(NumericLiteral::new(Sign::Negative, whole.clone(), fraction)),
            "-12.03",
        ),
        (
            Literal::Numeric(NumericLiteral::new(
                Sign::NonNegative,
                whole,
                FractionDigits::none(),
            )),
            "12.",
        ),
        (
            Literal::Text(StringLiteral::new(String::from("λ\n\t\"\\\0"))),
            r#""λ\n\t\"\\\0""#,
        ),
        (Literal::Character(CharacterLiteral::from('λ')), "'λ'"),
        (Literal::Character(CharacterLiteral::from('\'')), r"'\''"),
        (Literal::Character(CharacterLiteral::from('\\')), r"'\\'"),
        (Literal::Character(CharacterLiteral::from('\n')), r"'\n'"),
        (
            Literal::Fixed(gandr_kernel_term::FixedInteger::I32(-1)),
            "-1i32",
        ),
        (
            Literal::Fixed(gandr_kernel_term::FixedInteger::U64(u64::MAX)),
            "18446744073709551615u64",
        ),
        (
            Literal::Fixed(gandr_kernel_term::FixedInteger::U32(0)),
            "0u32",
        ),
        (
            Literal::Fixed(gandr_kernel_term::FixedInteger::I64(i64::MIN)),
            "-9223372036854775808i64",
        ),
    ] {
        let mut arena = CommandArena::new();
        let producer = arena
            .mint_producer(ProducerNode::Literal(literal))
            .expect("leaf");
        assert_eq!(expected, render_producer(&arena, producer));
    }
}

/// Every effect, control and memory command renders in its notation: a
/// request by the nearest handler and through a capability, both handlers,
/// the stack's resumption and abandonment, the delimiters, and each memory
/// form at each grade, mode and place.
#[test]
fn renders_effect_control_and_memory_commands()
{
    use gandr_core_term::control::EffectClause;
    use gandr_core_term::effect::EffectOp;
    use gandr_core_term::effect::EffectSig;
    use gandr_core_term::memory::AccessMode;
    use gandr_core_term::memory::HoldGrade;
    use gandr_core_term::memory::MemoryForm;
    use gandr_core_term::memory::Place;

    use crate::il::Introduces;
    use crate::il::Route;

    let mut arena = CommandArena::new();
    let value = arena
        .mint_producer(ProducerNode::Constructor {
            tag: ConstructorTag::Tuple(ProducerArity::ZERO),
            producers: Box::from([]),
            consumers: Box::from([]),
        })
        .expect("a leaf mints");
    let capability = arena
        .mint_producer(ProducerNode::Variable {
            zone: Zone::Intuitionistic,
            index: 0_u32.into(),
        })
        .expect("a leaf mints");
    let top = arena
        .mint_consumer(ConsumerNode::Top)
        .expect("a leaf mints");
    let body = arena
        .mint_cut(Polarity::Positive, value, top)
        .expect("children resolve");
    let ty = arena.annotations_mut().value_type_unit();
    let signature = EffectSig::new("E".into(), [EffectOp {
        name: "op".into(),
        payload: ty,
        reply: ty,
    }])
    .expect("one operation");
    let held = DeBruijnIndex::from(0_u32);
    let commands = [
        CommandNode::Perform {
            signature: signature.clone(),
            operation: "op".into(),
            route: Route::Nearest,
            payload: value,
            continuation: top,
        },
        CommandNode::Perform {
            signature: signature.clone(),
            operation: "op".into(),
            route: Route::Capability(capability),
            payload: value,
            continuation: top,
        },
        CommandNode::Handle {
            signature: signature.clone(),
            introduces: Introduces::Nothing,
            subject: body,
            on_return: body,
            clauses: alloc::sync::Arc::from([EffectClause {
                operation: "op".into(),
                body,
            }]),
            continuation: top,
        },
        CommandNode::Handle {
            signature,
            introduces: Introduces::Capability,
            subject: body,
            on_return: body,
            clauses: alloc::sync::Arc::from([]),
            continuation: top,
        },
        CommandNode::Resume {
            stack: capability,
            body,
            continuation: top,
        },
        CommandNode::Abandon {
            stack: capability,
            continuation: top,
        },
        CommandNode::Reset {
            body,
            continuation: top,
        },
        CommandNode::Shift {
            body,
            continuation: top,
        },
        CommandNode::Memory {
            form: MemoryForm::Hold {
                value,
                body,
                grade: HoldGrade::Many,
            },
            continuation: top,
        },
        CommandNode::Memory {
            form: MemoryForm::Hold {
                value,
                body,
                grade: HoldGrade::One,
            },
            continuation: top,
        },
        CommandNode::Memory {
            form: MemoryForm::Access {
                mode: AccessMode::Exclusive { unwind: body },
                held,
                place: Place::At { index: value },
                body,
            },
            continuation: top,
        },
        CommandNode::Memory {
            form: MemoryForm::Access {
                mode: AccessMode::Shared,
                held,
                place: Place::Whole,
                body,
            },
            continuation: top,
        },
        CommandNode::Memory {
            form: MemoryForm::Resume { view: held, value },
            continuation: top,
        },
        CommandNode::Memory {
            form: MemoryForm::Abort { view: held },
            continuation: top,
        },
        CommandNode::Memory {
            form: MemoryForm::Consume { held },
            continuation: top,
        },
    ];
    let rendered: Vec<String> = commands
        .into_iter()
        .map(|command| {
            let id = arena.mint_command(command).expect("children resolve");
            render_command(&arena, id)
        })
        .collect();
    assert_eq!(rendered, [
        "perform \"E\".\"op\"((); ★)",
        "exercise x0 \"E\".\"op\"((); ★)",
        "handle \"E\" { ⟨() |+ ★⟩ | return(x; α) ⇒ ⟨() |+ ★⟩ | \"op\"(payload, k; α) ⇒ ⟨() |+ \
         ★⟩ }; ★",
        "scope \"E\" { (c) ⇒ ⟨() |+ ★⟩ | return(x; α) ⇒ ⟨() |+ ★⟩ }; ★",
        "resume(x0; ⟨() |+ ★⟩; ★)",
        "abandon(x0; ★)",
        "reset(⟨() |+ ★⟩; ★)",
        "shift(k; ⟨() |+ ★⟩; ★)",
        "hold((); (l; α) ⇒ ⟨() |+ ★⟩; ★)",
        "hold[1]((); (l; α) ⇒ ⟨() |+ ★⟩; ★)",
        "access(l0[()]; (l; α) ⇒ ⟨() |+ ★⟩ | unwind(α) ⇒ ⟨() |+ ★⟩; ★)",
        "access_shared(l0; (l; α) ⇒ ⟨() |+ ★⟩; ★)",
        "writeback(l0, (); ★)",
        "abort(l0; ★)",
        "consume(l0; ★)",
    ]);
}

/// The remaining heads render in their notation: a reified stack's three
/// frames, a primitive, a constant, a fixpoint staged at a position, the
/// force and projection arms of a copattern object, a recorded run, a list
/// fold and the projection and force destructors.
#[test]
fn renders_frames_primitives_folds_and_projections()
{
    use gandr_core_term::control::StackFrame;
    use gandr_core_term::primitive::Arguments;
    use gandr_core_term::primitive::PRELUDE;
    use gandr_kernel_term::Component;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::FixpointEvidence;
    use gandr_kernel_term::StagedPosition;

    let mut arena = CommandArena::new();
    let value = arena
        .mint_producer(ProducerNode::Variable {
            zone: Zone::Intuitionistic,
            index: 0_u32.into(),
        })
        .expect("a leaf mints");
    let top = arena
        .mint_consumer(ConsumerNode::Top)
        .expect("a leaf mints");
    let body = arena
        .mint_cut(Polarity::Positive, value, top)
        .expect("children resolve");
    let unary = PRELUDE
        .iter()
        .copied()
        .find(|primitive| primitive.arguments().len() == 1)
        .expect("a unary primitive");
    let producers = [
        ProducerNode::Reify(alloc::sync::Arc::from([
            StackFrame::Apply(value),
            StackFrame::Bind(body),
            StackFrame::Project(Component::from(1_usize)),
        ])),
        ProducerNode::Primitive {
            primitive: unary,
            arguments: Arguments::Unary(value),
        },
        ProducerNode::Constant(ConstantIndex::from(7_usize)),
        ProducerNode::Fixpoint {
            body,
            evidence: FixpointEvidence::Staged {
                position: StagedPosition::from(2_usize),
            },
        },
        ProducerNode::Cocase {
            arms: Box::from([
                CopatternArm {
                    destructor: DestructorTag::Force,
                    body,
                },
                CopatternArm {
                    destructor: DestructorTag::Project(Component::from(1_usize)),
                    body,
                },
            ]),
        },
        ProducerNode::Constructor {
            tag: ConstructorTag::Recorded(alloc::sync::Arc::from([
                gandr_core_term::session::RecordedMove::Sent(()),
                gandr_core_term::session::RecordedMove::Closed,
            ])),
            producers: Box::from([value]),
            consumers: Box::from([]),
        },
    ]
    .map(|node| {
        let id = arena.mint_producer(node).expect("children resolve");
        render_producer(&arena, id)
    });
    assert_eq!(producers, [
        "reify [apply(x0); bind(x; α) ⇒ ⟨x0 |+ ★⟩; project[1]]",
        "prim.id(x0)",
        "c7",
        "fix[<2]{x; force(α) ⇒ ⟨x0 |+ ★⟩}",
        "cocase {force(α) ⇒ ⟨x0 |+ ★⟩ | project[1](α) ⇒ ⟨x0 |+ ★⟩}",
        "recorded[sent, closed](x0)",
    ]);
    let element = arena.annotations_mut().value_type_unit();
    let consumers = [
        ConsumerNode::ListFold {
            element,
            result: element,
            on_nil: body,
            on_cons: body,
            continuation: top,
        },
        ConsumerNode::Destructor {
            tag: DestructorTag::Project(Component::from(1_usize)),
            producers: Box::from([]),
            consumers: Box::from([top]),
        },
        ConsumerNode::Destructor {
            tag: DestructorTag::Force,
            producers: Box::from([]),
            consumers: Box::from([top]),
        },
    ]
    .map(|node| {
        let id = arena.mint_consumer(node).expect("children resolve");
        render_consumer(&arena, id)
    });
    assert_eq!(consumers, [
        "fold {nil ⇒ ⟨x0 |+ ★⟩ | cons(head, result) ⇒ ⟨x0 |+ ★⟩}; ★",
        "project[1](★)",
        "force(★)",
    ]);
}

/// A closure writes its environment values, outermost first, then its code
/// after the separator; over the empty environment it writes the separator
/// and the code alone.
#[test]
fn renders_abstract_closures()
{
    let mut arena = CommandArena::new();
    let [outer, inner] = [1_u32, 0_u32].map(|index| {
        arena
            .mint_producer(ProducerNode::Variable {
                zone: Zone::Intuitionistic,
                index: index.into(),
            })
            .expect("a leaf mints")
    });
    let back = arena
        .mint_consumer(ConsumerNode::Covariable(CovariableIndex::from(0_u32)))
        .expect("a leaf mints");
    let body = arena
        .mint_cut(Polarity::Positive, inner, back)
        .expect("children resolve");
    let code = arena
        .mint_producer(ProducerNode::Cocase {
            arms: Box::from([CopatternArm {
                destructor: DestructorTag::Apply,
                body,
            }]),
        })
        .expect("the body resolves");
    let closures = [Box::from([]), Box::from([outer, inner])].map(|environment| {
        let closure = arena
            .mint_producer(ProducerNode::Closure { environment, code })
            .expect("children resolve");
        render_producer(&arena, closure)
    });
    assert_eq!(closures, [
        "{; cocase {apply(x; α) ⇒ ⟨x0 |+ α0⟩}}",
        "{x1, x0; cocase {apply(x; α) ⇒ ⟨x0 |+ α0⟩}}",
    ]);
}
