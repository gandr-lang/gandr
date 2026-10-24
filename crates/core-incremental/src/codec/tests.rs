#[test]
fn native_names_and_operand_order_survive_persistence()
{
    use gandr_core_term::primitive::Arguments;
    use gandr_core_term::primitive::PRELUDE;
    let sub = PRELUDE
        .iter()
        .copied()
        .find(|primitive| primitive.name().as_ref() == "sub")
        .unwrap();
    let neg = PRELUDE
        .iter()
        .copied()
        .find(|primitive| primitive.name().as_ref() == "neg")
        .unwrap();
    for node in [
        ContentNode::PrimitiveValue(sub),
        ContentNode::Primitive(
            sub,
            Arguments::Binary([NodeIndex::from(4_usize), NodeIndex::from(2_usize)]),
        ),
        ContentNode::Primitive(neg, Arguments::Unary(NodeIndex::from(3_usize))),
    ] {
        let mut bytes = CheckpointBytes::default();
        super::write_node(&mut Writer { sink: &mut bytes }, &node).unwrap();
        let mut reader = Reader {
            bytes: bytes.as_ref(),
            cursor: 0,
        };
        assert_eq!(super::read_node(&mut reader), Ok(node));
        assert_eq!(reader.finish(), Ok(()));
    }
    let mut bytes = CheckpointBytes::default();
    let mut writer = Writer { sink: &mut bytes };
    writer.tag(Tag(0x0d));
    writer.bytes(Bytes(b"not-a-native-row")).unwrap();
    let mut reader = Reader {
        bytes: bytes.as_ref(),
        cursor: 0,
    };
    assert_eq!(super::read_node(&mut reader), Err(CodecError::Corrupt));
}

#[test]
fn holes_marks_and_the_unknown_types_round_trip()
{
    use gandr_core_term::hole::HoleId;
    use gandr_core_term::hole::MarkIndex;
    let nodes = [
        ContentNode::Hole(HoleId::from(0x0102_0304_u32)),
        ContentNode::ValueMark {
            mark: MarkIndex::from(7_u32),
            body: NodeIndex::from(3_usize),
        },
        ContentNode::ComputationHole(HoleId::from(u32::MAX)),
        ContentNode::ComputationMark {
            mark: MarkIndex::from(0_u32),
            body: NodeIndex::from(1_usize),
        },
        ContentNode::UnknownType,
        ContentNode::BufferType,
        ContentNode::UnknownComputationType,
    ];
    let mut tags = BTreeSet::new();
    for node in nodes {
        let mut bytes = CheckpointBytes::default();
        super::write_node(&mut Writer { sink: &mut bytes }, &node).unwrap();
        assert!(
            tags.insert(bytes.as_ref().first().copied()),
            "each former has its own tag: {node:?}"
        );
        let mut reader = Reader {
            bytes: bytes.as_ref(),
            cursor: 0,
        };
        assert_eq!(
            super::read_node(&mut reader),
            Ok(node),
            "the node reads back"
        );
        assert_eq!(reader.finish(), Ok(()), "and nothing is left over");
    }
    let mut bytes = CheckpointBytes::default();
    super::write_node(
        &mut Writer { sink: &mut bytes },
        &ContentNode::Hole(HoleId::from(9_u32)),
    )
    .unwrap();
    let truncated = bytes.as_ref().get(.. 3).unwrap();
    let mut reader = Reader {
        bytes: truncated,
        cursor: 0,
    };
    assert!(
        super::read_node(&mut reader).is_err(),
        "a hole's name cut short does not decode"
    );
}

#[test]
#[expect(
    clippy::many_single_char_names,
    reason = "the five child nodes are placeholders each former's slots are filled from"
)]
fn every_node_former_round_trips_under_its_own_frame()
{
    use alloc::collections::BTreeMap;

    use gandr_core_term::Component;
    use gandr_core_term::ComponentCount;
    use gandr_core_term::FieldLabel;
    use gandr_core_term::control::StackFrame;
    use gandr_core_term::memory::AccessMode;
    use gandr_core_term::memory::MemoryForm;
    use gandr_core_term::session::RecordedMove;
    use gandr_core_term::session::SessionRelation;

    use super::DeBruijnIndex;
    use super::Level;
    use super::Summand;
    use super::Zone;

    let [a, b, c, d, e] = [1_usize, 2, 3, 4, 5].map(NodeIndex::from);
    let label = |text: &str| FieldLabel::from(alloc::string::String::from(text));
    let fields = BTreeMap::from([(label("x"), a), (label("y"), b)]);
    let slot = DeBruijnIndex::from(2_u32);
    let reference = Reference::Item {
        key: ItemKey::from([4].as_slice()),
        occurrence: Occurrence::from(1_usize),
    };
    let level = Level::zero();
    let mut nodes = vec![
        ContentNode::Data {
            declaration: reference.clone(),
            arguments: vec![a, b],
        },
        ContentNode::RecordType(fields.clone()),
        ContentNode::Constructor {
            datatype: a,
            tag: gandr_core_term::ConstructorTag::from(1_usize),
            fields: vec![b, c],
        },
        ContentNode::Record(fields),
        ContentNode::DataCase {
            scrutinee: a,
            motive: b,
            branches: vec![c, d],
            arities: [0_usize, 2]
                .map(gandr_kernel_term::FieldCount::from)
                .to_vec(),
            equations: gandr_kernel_term::EquationCount::NONE,
        },
        ContentNode::DataCase {
            scrutinee: a,
            motive: b,
            branches: vec![c, d],
            arities: [0_usize, 2]
                .map(gandr_kernel_term::FieldCount::from)
                .to_vec(),
            equations: gandr_kernel_term::EquationCount::from(1_usize),
        },
        ContentNode::RecordProjection(a, label("x")),
        ContentNode::TupleProjection(a, Component::from(1_usize)),
        ContentNode::Reify(alloc::sync::Arc::from([
            StackFrame::Apply(a),
            StackFrame::Bind(b),
            StackFrame::Project(Component::from(0_usize)),
            StackFrame::Project(Component::from(2_usize)),
        ])),
        ContentNode::Stack {
            input: a,
            output: b,
        },
        ContentNode::WithType(vec![]),
        ContentNode::WithType(vec![a]),
        ContentNode::WithType(vec![a, b, c]),
        ContentNode::Resume(a, b),
        ContentNode::Abandon(a),
        ContentNode::Split(a, ComponentCount::from(2_usize), b),
        ContentNode::DependentSplit {
            scrutinee: a,
            arity: ComponentCount::from(2_usize),
            motive: b,
            body: c,
        },
        ContentNode::Reset(a),
        ContentNode::Shift(a),
        ContentNode::With(vec![]),
        ContentNode::With(vec![a]),
        ContentNode::With(vec![a, b, c]),
        ContentNode::Ascribe { body: a, ty: b },
        ContentNode::ValueAscribe { value: a, ty: b },
        ContentNode::Project(Component::from(0_usize), a),
        ContentNode::Project(Component::from(2_usize), a),
        ContentNode::PathUniverse(a, b),
        ContentNode::PathRefl(a),
        ContentNode::PathProduct(a, b),
        ContentNode::Funext(a, b),
        ContentNode::Equiv(a, b),
        ContentNode::Univalence(a, b),
        ContentNode::Transport(a, b),
        ContentNode::PathType {
            carrier: a,
            left: b,
            right: c,
        },
        ContentNode::Here(a),
        ContentNode::Returned(a),
        ContentNode::Nested(a),
        ContentNode::Run(a),
        ContentNode::RecordUpdate(a, b),
        ContentNode::ElementTransport {
            motive: a,
            path: b,
            value: c,
        },
        ContentNode::TelescopeTransport {
            motive: a,
            path: b,
            start: c,
            over: d,
            value: e,
        },
        ContentNode::Stay(a),
        ContentNode::Then(a, b),
        ContentNode::Forward(a),
        ContentNode::FunctionFlow(a, b),
        ContentNode::FlowProduct(a, b),
        ContentNode::Recorded(alloc::sync::Arc::from([
            RecordedMove::Sent(a),
            RecordedMove::Received(b),
            RecordedMove::Selected(label("go")),
            RecordedMove::Offered(label("stop")),
            RecordedMove::Closed,
        ])),
        ContentNode::Dialogue(alloc::sync::Arc::from([
            gandr_core_term::session::DialogueMove {
                endpoint: gandr_core_term::session::Endpoint::Left,
                movement: RecordedMove::Sent(a),
            },
            gandr_core_term::session::DialogueMove {
                endpoint: gandr_core_term::session::Endpoint::Right,
                movement: RecordedMove::Received(b),
            },
            gandr_core_term::session::DialogueMove {
                endpoint: gandr_core_term::session::Endpoint::Right,
                movement: RecordedMove::Selected(label("go")),
            },
            gandr_core_term::session::DialogueMove {
                endpoint: gandr_core_term::session::Endpoint::Left,
                movement: RecordedMove::Offered(label("go")),
            },
        ])),
        ContentNode::Web(alloc::sync::Arc::from([
            gandr_core_term::session::WebPiece::Series(2),
            gandr_core_term::session::WebPiece::Parallel(2),
            gandr_core_term::session::WebPiece::Event {
                endpoint: gandr_core_term::session::Endpoint::Left,
                index: 0,
            },
            gandr_core_term::session::WebPiece::Event {
                endpoint: gandr_core_term::session::Endpoint::Right,
                index: 0,
            },
            gandr_core_term::session::WebPiece::Prime(1),
            gandr_core_term::session::WebPiece::Event {
                endpoint: gandr_core_term::session::Endpoint::Left,
                index: 1,
            },
        ])),
        ContentNode::Decompose(a),
        ContentNode::Ride {
            motive: a,
            flow: b,
            value: c,
        },
        ContentNode::FlowType {
            carrier: a,
            source: b,
            target: c,
        },
        ContentNode::RunType(a),
        ContentNode::PrefixType(a),
        ContentNode::DialogueType(a),
        ContentNode::WebType,
        ContentNode::Variable {
            zone: Zone::Intuitionistic,
            index: slot,
        },
        ContentNode::Variable {
            zone: Zone::Linear,
            index: slot,
        },
        ContentNode::Constant(reference.clone()),
        ContentNode::Tuple(vec![a, b]),
        ContentNode::ListNil,
        ContentNode::ListCons(a, b),
        ContentNode::Injection(Summand::from(1_usize), a),
        ContentNode::Thunk(a),
        ContentNode::ValueLift {
            target: level.clone(),
            body: a,
        },
        ContentNode::Quote(a),
        ContentNode::QuoteComputation(a),
        ContentNode::StaticLambda(a),
        ContentNode::StaticApplication(a, b),
        ContentNode::Lambda(a),
        ContentNode::Application(a, b),
        ContentNode::Return(a),
        ContentNode::Bind(a, b),
        ContentNode::Force(a),
        ContentNode::Case {
            scrutinee: a,
            branches: vec![b, c],
        },
        ContentNode::ListFold {
            element: a,
            result: b,
            list: c,
            on_nil: d,
            on_cons: e,
        },
        ContentNode::ListCase {
            list: a,
            on_nil: b,
            on_cons: c,
        },
        ContentNode::Base(BaseType::Integer),
        ContentNode::Product(vec![a, b]),
        ContentNode::Sum(vec![a, b]),
        ContentNode::List(a),
        ContentNode::ThunkType(a),
        ContentNode::TypeLift {
            inner: a,
            target: level.clone(),
        },
        ContentNode::Element {
            code: a,
            target: level.clone(),
        },
        ContentNode::StaticPi {
            domain: a,
            codomain: b,
        },
        ContentNode::Sigma {
            first: a,
            second: b,
        },
        ContentNode::Abstract(reference),
        ContentNode::Arrow {
            domain: a,
            codomain: b,
        },
        ContentNode::Pi {
            domain: a,
            codomain: b,
        },
        ContentNode::ComputationElement {
            code: a,
            target: level,
        },
    ];
    nodes.extend(
        [SessionRelation::Equivalence, SessionRelation::Subtyping].map(|relation| {
            ContentNode::SessionRelated {
                relation,
                source: a,
                target: b,
                payloads: c,
            }
        }),
    );
    nodes.extend(
        [
            MemoryForm::Hold {
                value: a,
                body: b,
                grade: gandr_core_term::memory::HoldGrade::Many,
            },
            MemoryForm::Hold {
                value: a,
                body: b,
                grade: gandr_core_term::memory::HoldGrade::One,
            },
            MemoryForm::Access {
                mode: AccessMode::Exclusive { unwind: b },
                held: slot,
                place: gandr_core_term::memory::Place::Whole,
                body: a,
            },
            MemoryForm::Access {
                mode: AccessMode::Shared,
                held: slot,
                place: gandr_core_term::memory::Place::Whole,
                body: a,
            },
            MemoryForm::Access {
                mode: AccessMode::Exclusive { unwind: b },
                held: slot,
                place: gandr_core_term::memory::Place::At { index: b },
                body: a,
            },
            MemoryForm::Access {
                mode: AccessMode::Shared,
                held: slot,
                place: gandr_core_term::memory::Place::At { index: b },
                body: a,
            },
            MemoryForm::Resume {
                view: slot,
                value: a,
            },
            MemoryForm::Abort { view: slot },
            MemoryForm::Consume { held: slot },
        ]
        .map(ContentNode::Memory),
    );
    let mut encodings = BTreeSet::new();
    for node in nodes {
        let mut bytes = CheckpointBytes::default();
        super::write_node(&mut Writer { sink: &mut bytes }, &node).expect("a portable node");
        assert!(
            encodings.insert(bytes.as_ref().to_vec()),
            "{node:?} keeps its own encoding"
        );
        let mut reader = Reader {
            bytes: bytes.as_ref(),
            cursor: 0,
        };
        assert_eq!(super::read_node(&mut reader), Ok(node));
        assert_eq!(reader.finish(), Ok(()));
    }
}

#[test]
fn every_footprint_stance_and_answer_round_trips()
{
    use super::Answer;
    use super::Footprint;
    use super::HoleMark;
    use super::Opacity;

    let mut encodings = BTreeSet::new();
    for opacity in [Opacity::Transparent, Opacity::Opaque] {
        for hole in [HoleMark::Filled, HoleMark::Hole] {
            let footprint = Footprint::from_parts(BTreeSet::new(), BTreeSet::new(), opacity, hole);
            let mut bytes = CheckpointBytes::default();
            super::write_footprint(&mut Writer { sink: &mut bytes }, &footprint)
                .expect("a portable footprint");
            assert!(encodings.insert(bytes.as_ref().to_vec()));
            let mut reader = Reader {
                bytes: bytes.as_ref(),
                cursor: 0,
            };
            assert_eq!(super::read_footprint(&mut reader), Ok(footprint));
            assert_eq!(reader.finish(), Ok(()));
        }
    }
    let ty = crate::fixture::type_content(&[ContentNode::Product(Vec::new())]);
    for answer in [
        Answer::Untyped,
        Answer::Typed(ty),
        Answer::Data(None),
        Answer::Codata,
    ] {
        let mut bytes = CheckpointBytes::default();
        super::write_answer(&mut Writer { sink: &mut bytes }, &answer).expect("a portable answer");
        assert!(encodings.insert(bytes.as_ref().to_vec()));
        let mut reader = Reader {
            bytes: bytes.as_ref(),
            cursor: 0,
        };
        assert_eq!(super::read_answer(&mut reader), Ok(answer));
        assert_eq!(reader.finish(), Ok(()));
    }
}

use gandr_kernel_term::BaseType;

use super::Answer;
use super::Answered;
use super::BTreeSet;
use super::Bytes;
use super::CheckBudget;
use super::CheckpointBytes;
use super::Checkpoints;
use super::CodecError;
use super::ContentNode;
use super::ConversionCount;
use super::Count;
use super::Footprint;
use super::HoleMark;
use super::ItemCheckpoint;
use super::ItemKey;
use super::Maybe;
use super::NodeIndex;
use super::Occurrence;
use super::Opacity;
use super::Reader;
use super::Reference;
use super::Refusal;
use super::Sink;
use super::Site;
use super::Sort;
use super::Tag;
use super::TypeContent;
use super::Typing;
use super::UnsupportedPersistence;
use super::Word;
use super::Writer;
use super::check_discovery;
use super::decode_checkpoints;
use super::encode_checkpoints;
use super::read_listed;
use super::read_narrow;
use super::read_reference;
use super::read_type;
use super::reference_bytes;
use super::root_of_sort;
use super::signature;
use super::write_listed;
use super::write_program;

#[test]
fn primitive_frames_have_known_bytes_and_digest()
{
    let expected = [
        0xaa, 0x7f, 8, 7, 6, 5, 4, 3, 2, 1, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0xff, 0x80,
    ];
    let mut bytes = CheckpointBytes::from(vec![0xaa]);
    let mut writer = Writer { sink: &mut bytes };
    writer.tag(Tag(0x7f));
    writer.word(Word(0x0102_0304_0506_0708));
    writer
        .bytes(Bytes(&[0, 0xff, 0x80]))
        .expect("representable payload");
    assert_eq!(bytes.as_ref(), expected);

    let mut hasher = blake3::Hasher::new();
    Sink::put(&mut hasher, Bytes(&[0xaa]));
    let mut writer = Writer { sink: &mut hasher };
    writer.tag(Tag(0x7f));
    writer.word(Word(0x0102_0304_0506_0708));
    writer
        .bytes(Bytes(&[0, 0xff, 0x80]))
        .expect("representable payload");
    assert_eq!(hasher.count(), 21);
    assert_eq!(hasher.finalize(), blake3::hash(&expected));
}

#[test]
fn primitive_reads_preserve_cursor_on_extent_failure()
{
    let bytes = [1, 2, 3, 4, 5, 6, 7, 8, 0x7f];
    let mut reader = Reader {
        bytes: &bytes,
        cursor: 0,
    };
    assert_eq!(reader.finish(), Err(CodecError::Corrupt));
    assert_eq!(reader.cursor, 0);
    assert_eq!(reader.word(), Ok(Word(0x0807_0605_0403_0201)));
    assert_eq!(reader.cursor, 8);
    assert_eq!(reader.tag(), Ok(Tag(0x7f)));
    assert_eq!(reader.finish(), Ok(()));
    assert_eq!(reader.take(Count(0)), Ok(Bytes(&[])));
    assert_eq!(reader.cursor, 9);
    assert_eq!(reader.tag(), Err(CodecError::Corrupt));
    assert_eq!(reader.cursor, 9);

    let mut short = Reader {
        bytes: &[1, 2, 3, 4, 5, 6, 7],
        cursor: 0,
    };
    assert_eq!(short.word(), Err(CodecError::Corrupt));
    assert_eq!(short.cursor, 0);
    let mut overflow = Reader {
        bytes: &[],
        cursor: usize::MAX,
    };
    assert_eq!(overflow.take(Count(1)), Err(CodecError::Corrupt));
    assert_eq!(overflow.cursor, usize::MAX);
}

#[test]
fn effect_rows_persist_operation_types_and_canonical_identity()
{
    use gandr_core_term::effect::EffectName;
    use gandr_core_term::effect::EffectOp;
    use gandr_core_term::effect::EffectRow;
    use gandr_core_term::effect::EffectSig;
    use gandr_core_term::effect::OperationName;
    let index = NodeIndex::from;
    let rows = [index(1_usize), index(2_usize)].map(|reply| {
        let effects = EffectRow::from_signatures([
            EffectSig::new(EffectName::from("Z"), [EffectOp {
                name: OperationName::from("get"),
                payload: index(1_usize),
                reply,
            }])
            .expect("distinct operations"),
            EffectSig::new(EffectName::from("A"), [EffectOp {
                name: OperationName::from("put"),
                payload: index(2_usize),
                reply: index(1_usize),
            }])
            .expect("distinct operations"),
        ])
        .expect("distinct interfaces");
        crate::fixture::type_content(&[
            ContentNode::Returner {
                result: index(1_usize),
                effects,
            },
            ContentNode::Product(Vec::new()),
            ContentNode::Base(BaseType::String),
        ])
    });
    let [first, second] = rows;
    let mut first_bytes = CheckpointBytes::from(Vec::new());
    let mut second_bytes = CheckpointBytes::from(Vec::new());
    super::write_type(
        &mut Writer {
            sink: &mut first_bytes,
        },
        &first,
    )
    .expect("portable row");
    super::write_type(
        &mut Writer {
            sink: &mut second_bytes,
        },
        &second,
    )
    .expect("portable row");
    assert_ne!(
        first_bytes.as_ref(),
        second_bytes.as_ref(),
        "an operation's reply type contributes to content identity"
    );
    assert_ne!(
        blake3::hash(first_bytes.as_ref()),
        blake3::hash(second_bytes.as_ref())
    );
    let refusal = super::Refusal::EffectSignatureConflict {
        at: super::Site::Node(index(9_usize)),
        first,
        second,
    };
    let mut bytes = CheckpointBytes::from(Vec::new());
    super::write_refusal(&mut Writer { sink: &mut bytes }, &refusal).expect("portable refusal");
    let mut reader = Reader {
        bytes: bytes.as_ref(),
        cursor: 0,
    };
    assert_eq!(super::read_refusal(&mut reader), Ok(refusal));
    assert_eq!(reader.finish(), Ok(()));
}

/// A split persists its scrutinee, arity and body in place: splits that
/// differ only in arity, or in which child is the scrutinee, encode
/// apart, and the empty split survives.
#[test]
fn a_split_persists_its_arity_between_its_children()
{
    use gandr_core_term::ComponentCount;
    let index = NodeIndex::from;
    let nodes = [
        ContentNode::Split(
            index(1_usize),
            ComponentCount::from(2_usize),
            index(2_usize),
        ),
        ContentNode::Split(
            index(1_usize),
            ComponentCount::from(3_usize),
            index(2_usize),
        ),
        ContentNode::Split(
            index(2_usize),
            ComponentCount::from(2_usize),
            index(1_usize),
        ),
        ContentNode::Split(index(1_usize), ComponentCount::default(), index(2_usize)),
    ];
    let mut encodings = alloc::collections::BTreeSet::new();
    for node in nodes {
        let mut bytes = CheckpointBytes::default();
        super::write_node(&mut Writer { sink: &mut bytes }, &node).expect("portable split");
        assert!(encodings.insert(bytes.as_ref().to_vec()), "distinct splits");
        let mut reader = Reader {
            bytes: bytes.as_ref(),
            cursor: 0,
        };
        assert_eq!(super::read_node(&mut reader), Ok(node));
        assert_eq!(reader.finish(), Ok(()));
    }
}

#[test]
fn control_nodes_persist_names_frames_and_branch_order()
{
    use gandr_core_term::control::EffectClause;
    use gandr_core_term::control::StackFrame;
    use gandr_core_term::effect::EffectOp;
    use gandr_core_term::effect::EffectSig;
    use gandr_core_term::effect::capability::CapabilityGrade;
    use gandr_core_term::effect::capability::Region;
    use gandr_core_term::effect::capability::RegionBinder;
    use gandr_core_term::effect::capability::RegionDepth;
    use gandr_kernel_term::Component;
    let index = NodeIndex::from;
    let signature = EffectSig::new("State".into(), [
        EffectOp {
            name: "first".into(),
            payload: index(3_usize),
            reply: index(4_usize),
        },
        EffectOp {
            name: "second".into(),
            payload: index(4_usize),
            reply: index(3_usize),
        },
    ])
    .expect("distinct operations");
    let clauses = alloc::sync::Arc::from([
        EffectClause {
            operation: "second".into(),
            body: index(5_usize),
        },
        EffectClause {
            operation: "first".into(),
            body: index(6_usize),
        },
    ]);
    let authority =
        gandr_core_term::effect::EffectRow::from_signatures([EffectSig::new("State".into(), [
            EffectOp {
                name: "first".into(),
                payload: index(3_usize),
                reply: index(4_usize),
            },
        ])
        .expect("one operation")])
        .expect("one restriction");
    let nodes = [
        ContentNode::Reify(alloc::sync::Arc::from([
            StackFrame::Apply(index(1_usize)),
            StackFrame::Bind(index(2_usize)),
            StackFrame::Project(Component::from(1_usize)),
            StackFrame::Apply(index(3_usize)),
        ])),
        ContentNode::Stack {
            input: index(1_usize),
            output: index(2_usize),
        },
        ContentNode::WithType(vec![index(1_usize), index(2_usize)]),
        ContentNode::Perform {
            signature: signature.clone(),
            operation: "second".into(),
            payload: index(1_usize),
        },
        ContentNode::Handle {
            signature: signature.clone(),
            subject: index(1_usize),
            on_return: index(2_usize),
            clauses: alloc::sync::Arc::clone(&clauses),
        },
        ContentNode::Scope {
            signature: signature.clone(),
            subject: index(1_usize),
            on_return: index(2_usize),
            clauses,
        },
        ContentNode::Exercise {
            capability: index(1_usize),
            signature,
            operation: "second".into(),
            payload: index(2_usize),
        },
        ContentNode::Capability {
            authority: authority.clone(),
            grade: CapabilityGrade::Durable,
            region: Region::Held,
        },
        ContentNode::Capability {
            authority: authority.clone(),
            grade: CapabilityGrade::Durable,
            region: Region::Scoped(RegionDepth::from(2_u32)),
        },
        ContentNode::Capability {
            authority: authority.clone(),
            grade: CapabilityGrade::Durable,
            region: Region::Bound(RegionBinder::from(2_u32)),
        },
        ContentNode::Capability {
            authority,
            grade: CapabilityGrade::Consumable,
            region: Region::Held,
        },
        ContentNode::KeptType {
            value: index(1_usize),
            region: Region::Scoped(RegionDepth::from(0_u32)),
        },
        ContentNode::KeptType {
            value: index(1_usize),
            region: Region::Scoped(RegionDepth::from(2_u32)),
        },
        ContentNode::KeptType {
            value: index(1_usize),
            region: Region::Bound(RegionBinder::from(2_u32)),
        },
        ContentNode::Resume(index(1_usize), index(2_usize)),
        ContentNode::Abandon(index(1_usize)),
        ContentNode::Reset(index(1_usize)),
        ContentNode::Shift(index(1_usize)),
        ContentNode::With(vec![index(1_usize), index(2_usize)]),
        ContentNode::Project(Component::from(0_usize), index(1_usize)),
    ];
    let mut encodings = alloc::collections::BTreeSet::new();
    for node in nodes {
        let mut bytes = CheckpointBytes::default();
        super::write_node(&mut Writer { sink: &mut bytes }, &node).expect("portable control node");
        assert!(
            encodings.insert(bytes.as_ref().to_vec()),
            "distinct control identities"
        );
        let mut reader = Reader {
            bytes: bytes.as_ref(),
            cursor: 0,
        };
        assert_eq!(super::read_node(&mut reader), Ok(node));
        assert_eq!(reader.finish(), Ok(()));
    }
    let at = super::Site::Node(index(7_usize));
    let typed = crate::fixture::type_content(&[ContentNode::Product(Vec::new())]);
    for refusal in [
        super::Refusal::UnknownOperation { at },
        super::Refusal::HandlerCoverage { at },
        super::Refusal::ShiftWithoutReset { at },
        super::Refusal::DependentStack {
            at,
            synthesised: typed.clone(),
        },
        super::Refusal::CapabilityForged {
            at,
            expected: typed.clone(),
        },
        super::Refusal::CapabilityAmplified {
            at,
            synthesised: typed.clone(),
            expected: typed.clone(),
        },
        super::Refusal::CapabilityOutsideAuthority {
            at,
            capability: typed.clone(),
        },
        super::Refusal::CapabilityEscaped { at, found: typed },
        super::Refusal::CapabilityConsumable(at),
        super::Refusal::CapabilityUngranted(at),
        super::Refusal::NotSynthesisable {
            form: super::Form::Scope(at),
        },
        super::Refusal::NotSynthesisable {
            form: super::Form::Reify(at),
        },
        super::Refusal::NotSynthesisable {
            form: super::Form::Handle(at),
        },
        super::Refusal::NotSynthesisable {
            form: super::Form::Reset(at),
        },
        super::Refusal::NotSynthesisable {
            form: super::Form::Shift(at),
        },
        super::Refusal::NotSynthesisable {
            form: super::Form::With(at),
        },
    ] {
        let mut bytes = CheckpointBytes::default();
        super::write_refusal(&mut Writer { sink: &mut bytes }, &refusal)
            .expect("portable control refusal");
        let mut reader = Reader {
            bytes: bytes.as_ref(),
            cursor: 0,
        };
        assert_eq!(super::read_refusal(&mut reader), Ok(refusal));
        assert_eq!(reader.finish(), Ok(()));
    }
}

#[test]
fn session_nodes_persist_their_protocol_and_children()
{
    use alloc::collections::BTreeMap;
    use alloc::sync::Arc;

    use gandr_core_term::session::PayloadCount;
    use gandr_core_term::session::PayloadSlot;
    use gandr_core_term::session::Protocol;
    use gandr_core_term::session::ProtocolState;
    use gandr_core_term::session::ProtocolSyntax;
    use gandr_core_term::session::RecursionIndex;
    use gandr_core_term::session::SessionAction;
    use gandr_core_term::session::SessionType;
    use gandr_kernel_term::DeBruijnIndex;
    let index = NodeIndex::from;
    let state = ProtocolState::from;
    let label = |text: &str| gandr_core_term::FieldLabel::from(alloc::string::String::from(text));
    // ?A. mu t. +{ report : !B. &{ next : t, retire : end }, handoff : !A. end }
    let protocol = Protocol::new(
        vec![
            ProtocolSyntax::Receive {
                payload: PayloadSlot::from(0_usize),
                next: state(1),
            },
            ProtocolSyntax::Mu(state(2)),
            ProtocolSyntax::Select(BTreeMap::from([
                (label("handoff"), state(6)),
                (label("report"), state(3)),
            ])),
            ProtocolSyntax::Send {
                payload: PayloadSlot::from(1_usize),
                next: state(4),
            },
            ProtocolSyntax::Offer(BTreeMap::from([
                (label("next"), state(5)),
                (label("retire"), state(7)),
            ])),
            ProtocolSyntax::Recur(RecursionIndex::from(0_usize)),
            ProtocolSyntax::Send {
                payload: PayloadSlot::from(0_usize),
                next: state(8),
            },
            ProtocolSyntax::End,
            ProtocolSyntax::End,
        ],
        state(0),
        PayloadCount::from(2_usize),
    )
    .expect("a contractive protocol");
    let at_root = SessionType::new(
        Arc::new(protocol),
        Arc::from([index(1_usize), index(2_usize)]),
    )
    .expect("two payloads");
    let inside = at_root.at(state(4)).expect("a state of the protocol");
    let endpoint = DeBruijnIndex::from(1_u32);
    let nodes = [
        ContentNode::SessionType(at_root.clone()),
        ContentNode::SessionType(inside),
        ContentNode::SessionType(at_root.dual()),
        ContentNode::Session(SessionAction::Send {
            endpoint,
            payload: index(1_usize),
        }),
        ContentNode::Session(SessionAction::Receive {
            endpoint,
            body: index(2_usize),
        }),
        ContentNode::Session(SessionAction::Select {
            endpoint,
            label: label("report"),
        }),
        ContentNode::Session(SessionAction::Offer {
            endpoint,
            arms: BTreeMap::from([
                (label("next"), index(1_usize)),
                (label("retire"), index(2_usize)),
            ]),
        }),
        ContentNode::Session(SessionAction::Close { endpoint }),
        ContentNode::Session(SessionAction::Fork {
            protocol: index(1_usize),
            child: index(2_usize),
            parent: index(3_usize),
        }),
    ];
    let mut encodings = alloc::collections::BTreeSet::new();
    for node in nodes {
        let mut bytes = CheckpointBytes::default();
        super::write_node(&mut Writer { sink: &mut bytes }, &node).expect("portable session node");
        assert!(
            encodings.insert(bytes.as_ref().to_vec()),
            "distinct session identities, a state and a dual included"
        );
        let mut reader = Reader {
            bytes: bytes.as_ref(),
            cursor: 0,
        };
        assert_eq!(super::read_node(&mut reader), Ok(node));
        assert_eq!(reader.finish(), Ok(()));
    }

    // mu t. t, written by hand: the reader validates and refuses it.
    let mut bytes = CheckpointBytes::default();
    let mut writer = Writer { sink: &mut bytes };
    writer.tag(Tag(0x60));
    writer.count(Count(2)).expect("two nodes");
    writer.tag(Tag(5));
    writer.count(Count(1)).expect("the mu's body");
    writer.tag(Tag(6));
    writer.count(Count(0)).expect("the variable's binder");
    writer.count(Count(0)).expect("the root");
    writer.count(Count(0)).expect("the state");
    super::write_indices(&mut writer, &[]).expect("no payloads");
    let mut reader = Reader {
        bytes: bytes.as_ref(),
        cursor: 0,
    };
    assert_eq!(
        super::read_node(&mut reader),
        Err(CodecError::Corrupt),
        "a non-contractive protocol is refused at the one constructor"
    );
}

#[test]
fn session_refusals_round_trip_with_their_endpoints()
{
    use gandr_core_checker::session::Capture;
    use gandr_core_checker::session::ForkSide;
    use gandr_core_checker::session::ProtocolDefect;
    use gandr_core_term::session::ActionKind;
    use gandr_kernel_term::DeBruijnIndex;

    use super::EndpointSite;
    use super::Linearity;
    let at = Site::Node(NodeIndex::from(3_usize));
    let child = EndpointSite {
        fork: Site::Node(NodeIndex::from(1_usize)),
        side: ForkSide::Child,
    };
    let parent = EndpointSite {
        side: ForkSide::Parent,
        ..child
    };
    let received = EndpointSite {
        side: ForkSide::Received,
        ..child
    };
    let state = || crate::fixture::type_content(&[ContentNode::Product(Vec::new())]);
    let mut refusals = vec![
        Refusal::SessionMismatch {
            at,
            endpoint: parent,
            state: state(),
            defect: ProtocolDefect::Action {
                expected: ActionKind::Send,
                observed: ActionKind::Receive,
            },
        },
        Refusal::SessionMismatch {
            at,
            endpoint: child,
            state: state(),
            defect: ProtocolDefect::Label,
        },
        Refusal::SessionMismatch {
            at,
            endpoint: child,
            state: state(),
            defect: ProtocolDefect::Arms,
        },
        Refusal::NotSynthesisable {
            form: super::Form::Offer(at),
        },
        Refusal::ShapeMismatch {
            at,
            wanted: super::ExpectedShape::Session,
            found: state(),
        },
    ];
    for defect in [
        Linearity::Residue {
            endpoint: child,
            state: state(),
        },
        Linearity::Closed { endpoint: parent },
        Linearity::UsedTwice { endpoint: child },
        Linearity::Captured {
            endpoint: child,
            by: Capture::Continuation,
        },
        Linearity::AsValue { endpoint: parent },
        Linearity::Closed { endpoint: received },
        Linearity::ArmsDisagree {
            endpoint: child,
            first: Site::Node(NodeIndex::from(4_usize)),
            other: Site::Unreached,
        },
        Linearity::Unrestricted,
        Linearity::Unbound {
            index: DeBruijnIndex::from(2_u32),
        },
        Linearity::BufferUnreturned {
            site: Site::Node(NodeIndex::from(5_usize)),
        },
        Linearity::BufferReturnedTwice {
            site: Site::Node(NodeIndex::from(5_usize)),
        },
        Linearity::BufferRead {
            site: Site::Unreached,
        },
        Linearity::ContinuationUnspent {
            clause: Site::Node(NodeIndex::from(6_usize)),
        },
        Linearity::ContinuationUsedTwice {
            clause: Site::Node(NodeIndex::from(6_usize)),
        },
        Linearity::ContinuationCaptured {
            clause: Site::Unreached,
            by: Capture::Thunk,
        },
        Linearity::ContinuationAsValue {
            clause: Site::Node(NodeIndex::from(7_usize)),
        },
    ] {
        refusals.push(Refusal::Linearity { at, defect });
    }
    let mut encodings = alloc::collections::BTreeSet::new();
    for refusal in refusals {
        let mut bytes = CheckpointBytes::default();
        super::write_refusal(&mut Writer { sink: &mut bytes }, &refusal)
            .expect("portable session refusal");
        assert!(
            encodings.insert(bytes.as_ref().to_vec()),
            "each defect and side keeps its own encoding"
        );
        let mut reader = Reader {
            bytes: bytes.as_ref(),
            cursor: 0,
        };
        assert_eq!(super::read_refusal(&mut reader), Ok(refusal));
        assert_eq!(reader.finish(), Ok(()));
    }
}

#[test]
fn located_refusals_round_trip_with_their_worlds()
{
    use gandr_core_checker::session::Capture;
    use gandr_core_checker::worlds::Crossed;
    use gandr_core_checker::worlds::Predicate;

    use super::Located;
    use super::Place;
    let at = Site::Node(NodeIndex::from(3_usize));
    let seat = Reference::Item {
        key: ItemKey::from([5].as_slice()),
        occurrence: Occurrence::from(0_usize),
    };
    let operator = Reference::Item {
        key: ItemKey::from([6].as_slice()),
        occurrence: Occurrence::from(0_usize),
    };
    let thunk = || crate::fixture::type_content(&[ContentNode::Product(Vec::new())]);
    let integer =
        || crate::fixture::type_content(&[ContentNode::Base(gandr_kernel_term::BaseType::Integer)]);
    let mut defects = Vec::new();
    for crossed in [Crossed::Result, Crossed::Constant] {
        for predicate in [Predicate::Mobile, Predicate::Open] {
            defects.push(Located::Immobile {
                crossed,
                ty: thunk(),
                former: integer(),
                predicate,
            });
        }
    }
    for world in [
        Place::Host,
        Place::Declared(seat.clone()),
        Place::Declared(operator),
    ] {
        defects.extend([
            Located::CapabilityMissing {
                world: world.clone(),
            },
            Located::CapabilityCaptured {
                world: world.clone(),
                by: Capture::Thunk,
            },
            Located::Elsewhere {
                bound: world.clone(),
            },
            Located::HoldElsewhere { wanted: world },
        ]);
    }
    defects.extend([
        Located::CapabilityCaptured {
            world: Place::Host,
            by: Capture::Continuation,
        },
        Located::Unlocated,
        Located::UndeclaredWorld {
            world: seat.clone(),
        },
        Located::HostWorldUndeclared,
        Located::MarkUnfounded {
            atom: seat.clone(),
            former: thunk(),
            predicate: Predicate::Open,
        },
        Located::EntryNamed {
            constant: seat.clone(),
        },
        Located::EntryUngranted { constant: seat },
        Located::NotAHandle { found: integer() },
    ]);
    let mut encodings = alloc::collections::BTreeSet::new();
    for defect in defects {
        let refusal = Refusal::Located { at, defect };
        let mut bytes = CheckpointBytes::default();
        super::write_refusal(&mut Writer { sink: &mut bytes }, &refusal)
            .expect("portable located refusal");
        assert!(
            encodings.insert(bytes.as_ref().to_vec()),
            "each defect, world, crossing and predicate keeps its own encoding: {refusal:?}"
        );
        let mut reader = Reader {
            bytes: bytes.as_ref(),
            cursor: 0,
        };
        assert_eq!(super::read_refusal(&mut reader), Ok(refusal));
        assert_eq!(reader.finish(), Ok(()));
    }
}

#[test]
fn an_absurd_case_s_refusal_round_trips_with_its_reason()
{
    use gandr_kernel_term::Apartness;
    use gandr_kernel_term::RuleIndex;
    let at = Site::Node(NodeIndex::from(3_usize));
    let mut encodings = alloc::collections::BTreeSet::new();
    for reason in [
        Apartness::Apart,
        Apartness::Agree,
        Apartness::Open,
        Apartness::Leaf,
        Apartness::Diverges {
            outer: RuleIndex::from(1_usize),
            inner: RuleIndex::from(0_usize),
        },
        Apartness::Diverges {
            outer: RuleIndex::from(0_usize),
            inner: RuleIndex::from(1_usize),
        },
        Apartness::Undecided,
    ] {
        let refusal = Refusal::NotApart { at, reason };
        let mut bytes = CheckpointBytes::default();
        super::write_refusal(&mut Writer { sink: &mut bytes }, &refusal).expect("portable refusal");
        assert!(
            encodings.insert(bytes.as_ref().to_vec()),
            "each reason, and each order of a divergent pair, keeps its own encoding"
        );
        let mut reader = Reader {
            bytes: bytes.as_ref(),
            cursor: 0,
        };
        assert_eq!(super::read_refusal(&mut reader), Ok(refusal));
        assert_eq!(reader.finish(), Ok(()));
    }
}

#[test]
fn a_loop_refusal_round_trips_with_its_reason_464()
{
    use gandr_core_checker::LoopRespect;
    let at = Site::Node(NodeIndex::from(3_usize));
    let cell = gandr_kernel_term::CellIndex::from(1_usize);
    let mut encodings = alloc::collections::BTreeSet::new();
    for reason in [LoopRespect::Apart, LoopRespect::NotPresentedSet] {
        let refusal = Refusal::LoopNotRespected { at, cell, reason };
        let mut bytes = CheckpointBytes::default();
        super::write_refusal(&mut Writer { sink: &mut bytes }, &refusal).expect("portable refusal");
        assert!(
            encodings.insert(bytes.as_ref().to_vec()),
            "each reason keeps its own encoding"
        );
        let mut reader = Reader {
            bytes: bytes.as_ref(),
            cursor: 0,
        };
        assert_eq!(super::read_refusal(&mut reader), Ok(refusal));
        assert_eq!(reader.finish(), Ok(()));
    }
}

#[test]
fn a_stage_refusal_round_trips_with_where_it_stood()
{
    use gandr_kernel_term::Stage;
    use gandr_kernel_term::StageDepth;
    use gandr_kernel_term::StageId;
    use gandr_kernel_term::Standing;
    let at = Site::Node(NodeIndex::from(3_usize));
    let root = StageId::from(0_usize);
    let below = Stage::Below {
        anchor: root,
        depth: StageDepth::ONE,
    };
    let mut encodings = alloc::collections::BTreeSet::new();
    for (found, bound) in [
        (Standing::Top, below),
        (Standing::Staged(Stage::At(root)), below),
        (
            Standing::Staged(Stage::At(StageId::from(1_usize))),
            Stage::Below {
                anchor: root,
                depth: StageDepth::ONE.deeper(),
            },
        ),
        (Standing::Staged(below), Stage::At(root)),
    ] {
        let refusal = Refusal::StageNotBelow { at, found, bound };
        let mut bytes = CheckpointBytes::default();
        super::write_refusal(&mut Writer { sink: &mut bytes }, &refusal).expect("portable refusal");
        assert!(
            encodings.insert(bytes.as_ref().to_vec()),
            "each standing and bound keeps its own encoding"
        );
        let mut reader = Reader {
            bytes: bytes.as_ref(),
            cursor: 0,
        };
        assert_eq!(super::read_refusal(&mut reader), Ok(refusal));
        assert_eq!(reader.finish(), Ok(()));
    }
    let disagreement = Refusal::StagesDisagree {
        at,
        binder: gandr_kernel_term::StageBinder::from(1_usize),
    };
    let mut bytes = CheckpointBytes::default();
    super::write_refusal(&mut Writer { sink: &mut bytes }, &disagreement)
        .expect("portable refusal");
    let mut reader = Reader {
        bytes: bytes.as_ref(),
        cursor: 0,
    };
    assert_eq!(
        super::read_refusal(&mut reader),
        Ok(disagreement),
        "a disagreement keeps its site and binder"
    );
    assert_eq!(reader.finish(), Ok(()));
    // A bound zero steps below its anchor is no bound.
    let mut zero = Reader {
        bytes: &[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        cursor: 0,
    };
    assert_eq!(super::read_stage(&mut zero), Err(CodecError::Corrupt));
}

#[test]
fn fixpoint_evidence_round_trips_with_its_staged_position()
{
    use gandr_kernel_term::FixpointEvidence;
    use gandr_kernel_term::StagedPosition;
    for (evidence, expected) in [
        (FixpointEvidence::Partial, vec![0_u8]),
        (FixpointEvidence::StructuralDescent, vec![1]),
        (
            FixpointEvidence::Staged {
                position: StagedPosition::from(3_usize),
            },
            vec![2, 3, 0, 0, 0, 0, 0, 0, 0],
        ),
    ] {
        let mut bytes = CheckpointBytes::default();
        super::write_evidence(&mut Writer { sink: &mut bytes }, evidence)
            .expect("evidence encodes");
        assert_eq!(bytes.as_ref(), expected.as_slice(), "{evidence:?}");
        let mut reader = Reader {
            bytes: bytes.as_ref(),
            cursor: 0,
        };
        assert_eq!(super::read_evidence(&mut reader), Ok(evidence));
        assert_eq!(reader.finish(), Ok(()));
    }
    let mut past = Reader {
        bytes: &[3],
        cursor: 0,
    };
    assert_eq!(super::read_evidence(&mut past), Err(CodecError::Corrupt));
}

#[test]
fn effect_rows_reject_duplicate_and_noncanonical_names()
{
    for names in [["State", "State"], ["State", "IO"]] {
        let mut bytes = CheckpointBytes::from(Vec::new());
        let mut writer = Writer { sink: &mut bytes };
        writer.count(Count(2)).expect("count");
        for name in names {
            writer.bytes(Bytes(name.as_bytes())).expect("name");
            writer.count(Count(0)).expect("count");
        }
        assert_eq!(
            super::read_effect_row(&mut Reader {
                bytes: bytes.as_ref(),
                cursor: 0
            }),
            Err(CodecError::Corrupt)
        );
    }
    for names in [["put", "put"], ["put", "get"]] {
        let mut bytes = CheckpointBytes::from(Vec::new());
        let mut writer = Writer { sink: &mut bytes };
        writer.count(Count(1)).expect("count");
        writer.bytes(Bytes(b"State")).expect("name");
        writer.count(Count(2)).expect("count");
        for name in names {
            writer.bytes(Bytes(name.as_bytes())).expect("name");
            super::write_index(&mut writer, NodeIndex::from(0_usize)).expect("payload");
            super::write_index(&mut writer, NodeIndex::from(1_usize)).expect("reply");
        }
        assert_eq!(
            super::read_effect_row(&mut Reader {
                bytes: bytes.as_ref(),
                cursor: 0
            }),
            Err(CodecError::Corrupt)
        );
    }
    let mut bytes = CheckpointBytes::from(Vec::new());
    let mut writer = Writer { sink: &mut bytes };
    writer.tag(Tag(0x70));
    super::write_index(&mut writer, NodeIndex::from(0_usize)).expect("result");
    writer.count(Count(0)).expect("empty row");
    assert_eq!(
        super::read_node(&mut Reader {
            bytes: bytes.as_ref(),
            cursor: 0
        }),
        Err(CodecError::Corrupt),
        "an empty row uses the pure returner tag"
    );
}

#[test]
fn framed_failures_retain_consumed_prefixes()
{
    let mut short = Reader {
        bytes: &[3, 0, 0, 0, 0, 0, 0, 0, 0xab, 0xcd],
        cursor: 0,
    };
    assert_eq!(short.bytes(), Err(CodecError::Corrupt));
    assert_eq!(short.cursor, 8);
    assert_eq!(short.tag(), Ok(Tag(0xab)));

    let mut invalid = Reader {
        bytes: &[1, 0, 0, 0, 0, 0, 0, 0, 0xff, 0x7f],
        cursor: 0,
    };
    assert_eq!(invalid.text(), Err(CodecError::Corrupt));
    assert_eq!(invalid.cursor, 9);
    assert_eq!(invalid.tag(), Ok(Tag(0x7f)));
    assert_eq!(invalid.finish(), Ok(()));

    let mut text = Reader {
        bytes: &[2, 0, 0, 0, 0, 0, 0, 0, 0xc3, 0xa9, 0, 0, 0, 0, 0, 0, 0, 0],
        cursor: 0,
    };
    assert_eq!(text.text().as_deref(), Ok("é"));
    assert_eq!(text.cursor, 10);
    assert_eq!(text.text().as_deref(), Ok(""));
    assert_eq!(text.finish(), Ok(()));
}

#[test]
fn reference_frames_preserve_binary_keys_and_occurrences()
{
    let occupied = Reference::Item {
        key: ItemKey::from([0, 0xff].as_slice()),
        occurrence: Occurrence::from(2_usize),
    };
    let expected = [1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0xff, 2, 0, 0, 0, 0, 0, 0, 0];
    assert_eq!(reference_bytes(&occupied).as_ref(), expected);
    let mut reader = Reader {
        bytes: &expected,
        cursor: 0,
    };
    assert_eq!(read_reference(&mut reader), Ok(occupied));
    assert_eq!(reader.finish(), Ok(()));
    assert_eq!(reference_bytes(&Reference::Unoccupied).as_ref(), [0]);
    let mut empty = Reader {
        bytes: &[0],
        cursor: 0,
    };
    assert_eq!(read_reference(&mut empty), Ok(Reference::Unoccupied));
    assert_eq!(empty.finish(), Ok(()));
    let mut unknown = Reader {
        bytes: &[2],
        cursor: 0,
    };
    assert_eq!(read_reference(&mut unknown), Err(CodecError::Corrupt));
    assert_eq!(unknown.cursor, 1);
}

/// Write `formers` as a closed supported table: every scope empty, so no
/// edge has an index to write. Child extents and sorts are left as given, so
/// a malformed table reaches the reader.
///
/// # Specification
/// trivial.
fn write_closed(
    bytes: &mut CheckpointBytes,
    formers: &[ContentNode],
)
{
    let closed = super::Scope::new(
        gandr_core_term::BinderDepth::from(0_usize),
        gandr_core_term::BinderDepth::from(0_usize),
    );
    let mut writer = Writer { sink: bytes };
    writer.count(Count(formers.len())).expect("count");
    for former in formers {
        super::write_node(&mut writer, former).expect("former");
        super::write_scope(&mut writer, closed).expect("scope");
    }
}

#[test]
fn discovery_accepts_repeated_roots_and_empty_tables()
{
    assert_eq!(check_discovery(&[], core::iter::empty()), Ok(()));
    let ty = crate::fixture::type_content(&[
        ContentNode::Product(vec![NodeIndex::from(1_usize), NodeIndex::from(1_usize)]),
        ContentNode::Product(Vec::new()),
    ]);
    assert_eq!(
        check_discovery(
            ty.nodes(),
            [NodeIndex::from(0_usize), NodeIndex::from(0_usize)].into_iter()
        ),
        Ok(())
    );
    assert_eq!(
        check_discovery(ty.nodes(), [NodeIndex::from(1_usize)].into_iter()),
        Err(CodecError::NonCanonical),
        "a table numbered from another root is refused"
    );
    assert_eq!(
        check_discovery(ty.nodes(), [NodeIndex::from(usize::MAX)].into_iter()),
        Err(CodecError::Corrupt)
    );
}

#[test]
fn type_tables_validate_roots_child_extents_and_sorts()
{
    let ty = crate::fixture::type_content(&[ContentNode::Product(Vec::new())]);
    assert_eq!(
        root_of_sort(ty.nodes(), NodeIndex::from(0_usize), Sort::ValueType),
        Ok(())
    );
    assert_eq!(
        root_of_sort(ty.nodes(), NodeIndex::from(0_usize), Sort::Value),
        Err(CodecError::Corrupt)
    );
    assert_eq!(
        root_of_sort(ty.nodes(), NodeIndex::from(usize::MAX), Sort::ValueType),
        Err(CodecError::Corrupt)
    );
    let decode = |formers: &[ContentNode]| {
        let mut bytes = CheckpointBytes::default();
        write_closed(&mut bytes, formers);
        read_type(&mut Reader {
            bytes: bytes.as_ref(),
            cursor: 0,
        })
    };
    assert_eq!(decode(&[]), Err(CodecError::Corrupt));
    assert_eq!(
        decode(&[ContentNode::Tuple(Vec::new())]),
        Err(CodecError::Corrupt)
    );
    assert_eq!(
        decode(&[ContentNode::Product(vec![
            NodeIndex::from(1_usize),
            NodeIndex::from(0_usize)
        ])]),
        Err(CodecError::Corrupt)
    );
    assert_eq!(
        decode(&[
            ContentNode::Product(vec![NodeIndex::from(1_usize), NodeIndex::from(1_usize)]),
            ContentNode::Tuple(Vec::new()),
        ]),
        Err(CodecError::Corrupt)
    );
    assert_eq!(
        decode(&[ContentNode::Product(vec![NodeIndex::from(0_usize)])]),
        Err(CodecError::Corrupt),
        "a cycle is refused"
    );
    let computation = decode(&[
        ContentNode::Returner {
            result: NodeIndex::from(1_usize),
            effects: gandr_core_term::effect::EffectRow::EMPTY,
        },
        ContentNode::Product(Vec::new()),
    ])
    .expect("closed computation type");
    assert_eq!(
        computation
            .nodes()
            .first()
            .map(crate::support::SupportedNode::sort),
        Some(Sort::CompType)
    );
}

#[test]
fn enumeration_tags_use_first_matches_and_enforce_byte_width()
{
    let mut bytes = CheckpointBytes::default();
    write_listed(&mut Writer { sink: &mut bytes }, &[3_u16, 8, 3], &3).expect("first match fits");
    let table: Vec<u16> = (0 ..= 256).collect();
    write_listed(&mut Writer { sink: &mut bytes }, &table, &255).expect("last byte index");
    assert_eq!(
        write_listed(&mut Writer { sink: &mut bytes }, &table, &256),
        Err(CodecError::Unrepresentable)
    );
    assert_eq!(
        write_listed(&mut Writer { sink: &mut bytes }, &[3_u16, 8], &9),
        Err(CodecError::Unrepresentable)
    );
    assert_eq!(bytes.as_ref(), [0, 0xff]);
    let mut last = Reader {
        bytes: &[0xff],
        cursor: 0,
    };
    assert_eq!(read_listed(&mut last, &table), Ok(255));
    assert_eq!(last.cursor, 1);
    let mut invalid = Reader {
        bytes: &[2],
        cursor: 0,
    };
    assert_eq!(
        read_listed(&mut invalid, &[3_u16, 8]),
        Err(CodecError::Corrupt)
    );
    assert_eq!(invalid.cursor, 1);
}

#[test]
fn narrow_fields_refuse_out_of_range_words_after_consuming_them()
{
    let mut reader = Reader {
        bytes: &[0xff, 0xff, 0xff, 0xff, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
        cursor: 0,
    };
    assert_eq!(read_narrow::<u32>(&mut reader), Ok(u32::MAX));
    assert_eq!(reader.cursor, 8);
    assert_eq!(read_narrow::<u32>(&mut reader), Err(CodecError::Corrupt));
    assert_eq!(reader.cursor, 16);
    assert_eq!(reader.finish(), Ok(()));
}

#[test]
fn empty_envelopes_preserve_budget_and_separate_formats()
{
    let checkpoints = Checkpoints::new(CheckBudget::from(0x0102_0304_usize), vec![]);
    let expected = [
        b'G', b'C', b'K', b'P', b'T', 0, 0, 16, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    ];
    assert_eq!(
        encode_checkpoints(&checkpoints)
            .expect("empty checkpoint")
            .as_ref(),
        expected
    );
    assert_eq!(decode_checkpoints(Bytes(&expected)), Ok(checkpoints));
    let mut wrong_version = expected;
    *wrong_version.get_mut(7).expect("version byte") = 15;
    assert_eq!(
        decode_checkpoints(Bytes(&wrong_version)),
        Err(CodecError::Corrupt)
    );
    let mut program = CheckpointBytes::default();
    write_program::<_, crate::content::ItemContent>(&mut program, &[]).expect("empty program");
    assert_eq!(program.as_ref(), b"GPROG\0\0\x0a\0\0\0\0\0\0\0\0");
    assert_eq!(
        decode_checkpoints(Bytes(program.as_ref())),
        Err(CodecError::Corrupt)
    );
}

#[test]
fn checkpoint_encoding_reports_the_first_unresolved_plane()
{
    let unresolved = |sort| crate::fixture::type_content(&[ContentNode::Unresolved(sort)]);
    let mismatch = |synthesised, expected| {
        Typing::Refused(Refusal::TypeMismatch {
            at: Site::Unreached,
            synthesised,
            expected,
        })
    };
    let encode = |nodes: Vec<ContentNode>, answer, typing| {
        let content = crate::fixture::item_content(
            Reference::Unoccupied,
            &crate::content::DeclarationRoots::Value {
                signature: Maybe::Absent(signature::Absent::Unsigned),
                body: Maybe::Present(NodeIndex::from(0_usize)),
                laws: Vec::new(),
                rules: Vec::new(),
                stages: Vec::new(),
                supplies: Vec::new(),
                models: Vec::new(),
            },
            &nodes,
        );
        let footprint = Footprint::from_parts(
            BTreeSet::new(),
            BTreeSet::new(),
            Opacity::Transparent,
            HoleMark::Filled,
        );
        let item = ItemCheckpoint::new(
            content,
            footprint,
            vec![Answered::new(Reference::Unoccupied, answer)],
            typing,
        );
        let checkpoints = Checkpoints::new(CheckBudget::DEFAULT, vec![item]);
        let validated = encode_checkpoints(&checkpoints).map(|_bytes| ());
        let raw = super::checkpoint_frame(&checkpoints).map(|_bytes| ());
        assert_eq!(validated, raw);
        validated
    };
    let unsupported = |sort| {
        Err(CodecError::Unsupported(UnsupportedPersistence::Dangling(
            sort,
        )))
    };
    assert_eq!(
        encode(
            vec![ContentNode::Unresolved(Sort::Value)],
            Answer::Typed(unresolved(Sort::ValueType)),
            Typing::Synthesised {
                produced: unresolved(Sort::CompType),
                conversions: ConversionCount::from(0_usize)
            },
        ),
        unsupported(Sort::Value),
    );
    assert_eq!(
        encode(
            vec![ContentNode::Tuple(Vec::new())],
            Answer::Typed(unresolved(Sort::ValueType)),
            Typing::Synthesised {
                produced: unresolved(Sort::CompType),
                conversions: ConversionCount::from(0_usize)
            },
        ),
        unsupported(Sort::ValueType),
    );
    assert_eq!(
        encode(
            vec![ContentNode::Tuple(Vec::new())],
            Answer::Untyped,
            Typing::Synthesised {
                produced: unresolved(Sort::CompType),
                conversions: ConversionCount::from(0_usize)
            },
        ),
        unsupported(Sort::CompType),
    );
    assert_eq!(
        encode(
            vec![ContentNode::Tuple(Vec::new())],
            Answer::Untyped,
            mismatch(unresolved(Sort::CompType), unresolved(Sort::Computation)),
        ),
        unsupported(Sort::CompType),
    );
    assert_eq!(
        encode(
            vec![ContentNode::Tuple(Vec::new())],
            Answer::Untyped,
            mismatch(
                crate::fixture::type_content(&[ContentNode::Product(Vec::new())]),
                unresolved(Sort::Computation)
            ),
        ),
        unsupported(Sort::Computation),
    );
}

#[test]
fn decoders_reject_unknown_tags_before_payloads()
{
    type TagDecoder = for<'bytes> fn(&mut Reader<'bytes>) -> Result<(), CodecError>;
    let mut malformed = [0_u8; 65];
    *malformed.first_mut().expect("tag") = u8::MAX;
    let decoders: [TagDecoder; 7] = [
        |reader| super::read_sign(reader).map(|_value| ()),
        |reader| super::read_literal(reader).map(|_value| ()),
        |reader| super::read_node(reader).map(|_value| ()),
        |reader| super::read_site(reader).map(|_value| ()),
        |reader| super::read_refusal(reader).map(|_value| ()),
        |reader| super::read_typing(reader).map(|_value| ()),
        |reader| super::read_answer(reader).map(|_value| ()),
    ];
    for decode in decoders {
        let mut reader = Reader {
            bytes: &malformed,
            cursor: 0,
        };
        assert_eq!(decode(&mut reader), Err(CodecError::Corrupt));
        assert_eq!(reader.cursor, 1, "unknown tags stop before any payload");
    }

    for (tag, invalid_field) in [(0x01, 2), (0x20, 9)] {
        let mut bytes = [0_u8; 10];
        *bytes.first_mut().expect("node tag") = tag;
        *bytes.get_mut(1).expect("field tag") = invalid_field;
        let mut reader = Reader {
            bytes: &bytes,
            cursor: 0,
        };
        assert_eq!(super::read_node(&mut reader), Err(CodecError::Corrupt));
        assert_eq!(reader.cursor, 2, "zone and base tags reject at their field");
    }

    for (prefix, consumed) in [(&[2, 0xFF][..], 2), (&[5, 1, 2][..], 3)] {
        let mut bytes = prefix.to_vec();
        bytes.extend_from_slice(&[0; 16]);
        let mut reader = Reader {
            bytes: &bytes,
            cursor: 0,
        };
        assert_eq!(super::read_refusal(&mut reader), Err(CodecError::Corrupt));
        assert_eq!(
            reader.cursor, consumed,
            "form and zone tags stop at their field"
        );
    }

    for (opacity, hole, consumed) in [(2, 0, 17), (0, 2, 18)] {
        let mut bytes = [0_u8; 18];
        *bytes.get_mut(16).expect("opacity flag") = opacity;
        *bytes.get_mut(17).expect("hole flag") = hole;
        let mut reader = Reader {
            bytes: &bytes,
            cursor: 0,
        };
        assert_eq!(super::read_footprint(&mut reader), Err(CodecError::Corrupt));
        assert_eq!(
            reader.cursor, consumed,
            "each footprint flag has its own boundary"
        );
    }

    let mut bytes = CheckpointBytes::from(Vec::new());
    assert_eq!(
        super::write_site(&mut Writer { sink: &mut bytes }, Site::Unreached),
        Ok(())
    );
    assert_eq!(bytes.as_ref(), &[1]);
    let mut reader = Reader {
        bytes: &[1, 0xff],
        cursor: 0,
    };
    assert_eq!(super::read_site(&mut reader), Ok(Site::Unreached));
    assert_eq!(reader.cursor, 1);
}

#[test]
fn encoding_bounds_levels_in_every_node_family_and_plane()
{
    let mut level = super::Level::var(super::LevelVar::new(super::LevelVarIndex::from(0_u32)));
    for _ in 0 .. super::MAX_DECODED_LEVEL_OFFSET {
        level = level.succ().expect("representable offset");
    }
    let unit = || vec![ContentNode::Tuple(Vec::new())];
    let valid_type = || crate::fixture::type_content(&[ContentNode::Product(Vec::new())]);
    let at = Site::Unreached;
    let cases = [
        (
            vec![
                ContentNode::ValueLift {
                    target: level.clone(),
                    body: NodeIndex::from(1_usize),
                },
                ContentNode::Tuple(Vec::new()),
            ],
            Answer::Untyped,
            Typing::Owed,
        ),
        (
            unit(),
            Answer::Typed(crate::fixture::type_content(&[
                ContentNode::TypeLift {
                    inner: NodeIndex::from(1_usize),
                    target: level.clone(),
                },
                ContentNode::Product(Vec::new()),
            ])),
            Typing::Owed,
        ),
        (unit(), Answer::Untyped, Typing::Synthesised {
            produced: crate::fixture::type_content(&[
                ContentNode::Element {
                    code: NodeIndex::from(1_usize),
                    target: level.clone(),
                },
                ContentNode::Tuple(Vec::new()),
            ]),
            conversions: ConversionCount::from(0_usize),
        }),
        (
            unit(),
            Answer::Untyped,
            Typing::Refused(Refusal::TypeMismatch {
                at,
                synthesised: crate::fixture::type_content(&[ContentNode::Universe {
                    sort: super::TypeSort::Ground(super::GroundSort::Value),
                    level: level.clone(),
                }]),
                expected: valid_type(),
            }),
        ),
        (
            unit(),
            Answer::Untyped,
            Typing::Refused(Refusal::TypeMismatch {
                at,
                synthesised: valid_type(),
                expected: crate::fixture::type_content(&[
                    ContentNode::ComputationElement {
                        code: NodeIndex::from(1_usize),
                        target: level,
                    },
                    ContentNode::Tuple(Vec::new()),
                ]),
            }),
        ),
    ];
    for (nodes, answer, typing) in cases {
        let content = crate::fixture::item_content(
            Reference::Unoccupied,
            &crate::content::DeclarationRoots::Value {
                signature: Maybe::Absent(signature::Absent::Unsigned),
                body: Maybe::Present(NodeIndex::from(0_usize)),
                laws: Vec::new(),
                rules: Vec::new(),
                stages: Vec::new(),
                supplies: Vec::new(),
                models: Vec::new(),
            },
            &nodes,
        );
        let item = ItemCheckpoint::new(
            content,
            Footprint::from_parts(
                BTreeSet::new(),
                BTreeSet::new(),
                Opacity::Transparent,
                HoleMark::Filled,
            ),
            vec![Answered::new(Reference::Unoccupied, answer)],
            typing,
        );
        let checkpoints = Checkpoints::new(CheckBudget::DEFAULT, vec![item]);
        assert_eq!(
            encode_checkpoints(&checkpoints),
            Err(CodecError::LevelOffsetTooLarge {
                offset: super::LevelOffset::from(super::MAX_DECODED_LEVEL_OFFSET)
            })
        );
    }
}

#[test]
fn encoding_bounds_levels_in_every_auxiliary_type_table()
{
    type Mismatch = fn(TypeContent, TypeContent) -> Refusal;
    let mut level = super::Level::var(super::LevelVar::new(super::LevelVarIndex::from(0_u32)));
    for _ in 0 .. super::MAX_DECODED_LEVEL_OFFSET {
        level = level.succ().expect("representable offset");
    }
    let capped = || {
        crate::fixture::type_content(&[ContentNode::Universe {
            sort: super::TypeSort::Ground(super::GroundSort::Value),
            level: level.clone(),
        }])
    };
    let valid = || crate::fixture::type_content(&[ContentNode::Product(Vec::new())]);
    let at = Site::Unreached;
    let mismatches: [Mismatch; 4] = [
        |synthesised, expected| Refusal::TypeMismatch {
            at: Site::Unreached,
            synthesised,
            expected,
        },
        |synthesised, expected| Refusal::SortMismatch {
            at: Site::Unreached,
            synthesised,
            expected,
        },
        |synthesised, expected| Refusal::LevelMismatch {
            at: Site::Unreached,
            synthesised,
            expected,
        },
        |synthesised, expected| Refusal::FamilyArgumentClassifier {
            at: Site::Unreached,
            position: super::ArgumentPosition::from(0_u32),
            synthesised,
            expected,
        },
    ];
    let mut cases = vec![
        (Answer::Typed(capped()), Typing::Owed),
        (Answer::Untyped, Typing::Synthesised {
            produced: capped(),
            conversions: ConversionCount::from(0_usize),
        }),
        (
            Answer::Untyped,
            Typing::Refused(Refusal::ShapeMismatch {
                at,
                wanted: super::ExpectedShape::Product,
                found: capped(),
            }),
        ),
        (
            Answer::Untyped,
            Typing::Refused(Refusal::DependentBind {
                at,
                synthesised: capped(),
            }),
        ),
        (
            Answer::Untyped,
            Typing::Refused(Refusal::StaticClassifierExpected {
                at,
                found: capped(),
            }),
        ),
    ];
    for mismatch in mismatches {
        cases.push((
            Answer::Untyped,
            Typing::Refused(mismatch(capped(), valid())),
        ));
        cases.push((
            Answer::Untyped,
            Typing::Refused(mismatch(valid(), capped())),
        ));
    }
    for (answer, typing) in cases {
        let content = crate::fixture::item_content(
            Reference::Unoccupied,
            &crate::content::DeclarationRoots::Value {
                signature: Maybe::Absent(signature::Absent::Unsigned),
                body: Maybe::Present(NodeIndex::from(0_usize)),
                laws: Vec::new(),
                rules: Vec::new(),
                stages: Vec::new(),
                supplies: Vec::new(),
                models: Vec::new(),
            },
            &[ContentNode::Tuple(Vec::new())],
        );
        let item = ItemCheckpoint::new(
            content,
            Footprint::from_parts(
                BTreeSet::new(),
                BTreeSet::new(),
                Opacity::Transparent,
                HoleMark::Filled,
            ),
            vec![Answered::new(Reference::Unoccupied, answer)],
            typing,
        );
        let checkpoints = Checkpoints::new(CheckBudget::DEFAULT, vec![item]);
        assert_eq!(
            encode_checkpoints(&checkpoints),
            Err(CodecError::LevelOffsetTooLarge {
                offset: super::LevelOffset::from(super::MAX_DECODED_LEVEL_OFFSET)
            })
        );
    }
}

#[test]
fn a_lawful_value_root_round_trips_and_its_law_order_is_content()
{
    let law = |key: u8| Reference::Item {
        key: ItemKey::from([key].as_slice()),
        occurrence: Occurrence::from(0_usize),
    };
    let checkpoints = |laws: Vec<Reference>| {
        let content = crate::fixture::item_content(
            Reference::Unoccupied,
            &crate::content::DeclarationRoots::Value {
                signature: Maybe::Absent(signature::Absent::Unsigned),
                body: Maybe::Present(NodeIndex::from(0_usize)),
                laws,
                rules: Vec::new(),
                stages: Vec::new(),
                supplies: Vec::new(),
                models: Vec::new(),
            },
            &[ContentNode::Tuple(Vec::new())],
        );
        let item = ItemCheckpoint::new(
            content,
            Footprint::from_parts(
                BTreeSet::new(),
                BTreeSet::new(),
                Opacity::Transparent,
                HoleMark::Filled,
            ),
            vec![Answered::new(Reference::Unoccupied, Answer::Untyped)],
            Typing::Owed,
        );
        Checkpoints::new(CheckBudget::DEFAULT, vec![item])
    };
    let lawful = checkpoints(vec![law(1), law(2)]);
    let bytes = encode_checkpoints(&lawful).expect("a lawful root encodes");
    assert_eq!(
        decode_checkpoints(Bytes(bytes.as_ref())),
        Ok(lawful),
        "and decodes to itself, its laws in the order the fold names them"
    );
    let crossed = encode_checkpoints(&checkpoints(vec![law(2), law(1)]))
        .expect("a crossed lawful root encodes");
    assert_ne!(
        bytes.as_ref(),
        crossed.as_ref(),
        "reordering the laws changes the content"
    );
    let lawless = encode_checkpoints(&checkpoints(Vec::new())).expect("a lawless root encodes");
    assert_ne!(
        bytes.as_ref(),
        lawless.as_ref(),
        "and so does dropping them"
    );
}

#[test]
fn a_run_target_s_reason_round_trips_and_is_content_1105()
{
    // A run target's root states why it carries no signature, and a decoded
    // root that lost the reason would be judged as an unsigned thunk.
    let checkpoints = |signature| {
        let content = crate::fixture::item_content(
            Reference::Unoccupied,
            &crate::content::DeclarationRoots::Value {
                signature: Maybe::Absent(signature),
                body: Maybe::Present(NodeIndex::from(0_usize)),
                laws: Vec::new(),
                rules: Vec::new(),
                stages: Vec::new(),
                supplies: Vec::new(),
                models: Vec::new(),
            },
            &[ContentNode::Tuple(Vec::new())],
        );
        let item = ItemCheckpoint::new(
            content,
            Footprint::from_parts(
                BTreeSet::new(),
                BTreeSet::new(),
                Opacity::Transparent,
                HoleMark::Filled,
            ),
            vec![Answered::new(Reference::Unoccupied, Answer::Untyped)],
            Typing::Owed,
        );
        Checkpoints::new(CheckBudget::DEFAULT, vec![item])
    };
    let target = checkpoints(signature::Absent::RunTarget);
    let bytes = encode_checkpoints(&target).expect("a run target's root encodes");
    assert_eq!(
        decode_checkpoints(Bytes(bytes.as_ref())),
        Ok(target),
        "and decodes to itself, a run target still"
    );
    let unsigned = encode_checkpoints(&checkpoints(signature::Absent::Unsigned))
        .expect("an unsigned root encodes");
    assert_ne!(bytes.as_ref(), unsigned.as_ref(), "the reason is content");
}

#[test]
fn a_ruled_value_root_round_trips_and_its_rules_are_content()
{
    use crate::content::RuleRoot;
    use crate::content::RuleRoots;
    let item = |key: u8| Reference::Item {
        key: ItemKey::from([key].as_slice()),
        occurrence: Occurrence::from(0_usize),
    };
    // `f(Zero) ==> Zero`, `f` at item 1 and `Zero` constructor 0 of item 2;
    // the twin's right side is constructor 1 instead.
    let rule = |tag: usize| RuleRoots {
        left: vec![
            RuleRoot::Operation {
                callee: item(1),
                arity: gandr_kernel_term::FieldCount::from(1_usize),
            },
            RuleRoot::Constructor {
                family: item(2),
                tag: gandr_kernel_term::ConstructorTag::from(0_usize),
            },
        ],
        right: vec![
            RuleRoot::Constructor {
                family: item(2),
                tag: gandr_kernel_term::ConstructorTag::from(tag),
            },
            RuleRoot::Results(gandr_kernel_term::FieldCount::from(0_usize)),
            RuleRoot::Variable(gandr_kernel_term::RuleVariable::from(7_u32)),
        ],
    };
    let checkpoints = |rules: Vec<RuleRoots>| {
        let content = crate::fixture::item_content(
            Reference::Unoccupied,
            &crate::content::DeclarationRoots::Value {
                signature: Maybe::Absent(signature::Absent::Unsigned),
                body: Maybe::Present(NodeIndex::from(0_usize)),
                laws: Vec::new(),
                rules,
                stages: Vec::new(),
                supplies: Vec::new(),
                models: Vec::new(),
            },
            &[ContentNode::Tuple(Vec::new())],
        );
        let item = ItemCheckpoint::new(
            content,
            Footprint::from_parts(
                BTreeSet::new(),
                BTreeSet::new(),
                Opacity::Transparent,
                HoleMark::Filled,
            ),
            vec![Answered::new(Reference::Unoccupied, Answer::Untyped)],
            Typing::Owed,
        );
        Checkpoints::new(CheckBudget::DEFAULT, vec![item])
    };
    let ruled = checkpoints(vec![rule(0)]);
    let bytes = encode_checkpoints(&ruled).expect("a ruled root encodes");
    assert_eq!(
        decode_checkpoints(Bytes(bytes.as_ref())),
        Ok(ruled),
        "and decodes to itself, every node of both sides in order"
    );
    let changed = encode_checkpoints(&checkpoints(vec![rule(1)])).expect("a changed rule encodes");
    assert_ne!(
        bytes.as_ref(),
        changed.as_ref(),
        "changing a rule's right side changes the content"
    );
    let unruled = encode_checkpoints(&checkpoints(Vec::new())).expect("an unruled root encodes");
    assert_ne!(
        bytes.as_ref(),
        unruled.as_ref(),
        "and so does dropping the rules"
    );
}

#[test]
fn an_atom_interface_round_trips_with_and_without_its_law()
{
    use crate::content::AbstractRoots;
    use crate::content::InterfaceRoots;
    let checkpoints = |law: Maybe<NodeIndex, gandr_core_checker::law::Absent>| {
        let content = crate::fixture::item_content(
            Reference::Unoccupied,
            &crate::content::DeclarationRoots::Abstract(AbstractRoots {
                kind: NodeIndex::from(0_usize),
                representation: NodeIndex::from(1_usize),
                extent: gandr_kernel_term::SealExtent::from(0_usize),
                site: gandr_core_checker::SealSite::new(
                    gandr_core_checker::SealingSite::from(0_usize),
                    gandr_core_checker::ComponentOrdinal::from(0_usize),
                ),
                mobility: gandr_core_checker::worlds::Mobility::Immobile,
                interface: Maybe::Present(InterfaceRoots {
                    relation: NodeIndex::from(2_usize),
                    reflexivity: NodeIndex::from(3_usize),
                    law,
                }),
            }),
            &[
                ContentNode::Product(Vec::new()),
                ContentNode::Base(BaseType::Integer),
                ContentNode::Tuple(Vec::new()),
                ContentNode::Tuple(vec![NodeIndex::from(2_usize)]),
                ContentNode::Tuple(vec![NodeIndex::from(2_usize), NodeIndex::from(3_usize)]),
            ],
        );
        let item = ItemCheckpoint::new(
            content,
            Footprint::from_parts(
                BTreeSet::new(),
                BTreeSet::new(),
                Opacity::Transparent,
                HoleMark::Filled,
            ),
            vec![Answered::new(Reference::Unoccupied, Answer::Untyped)],
            Typing::Owed,
        );
        Checkpoints::new(CheckBudget::DEFAULT, vec![item])
    };
    let lawful = checkpoints(Maybe::Present(NodeIndex::from(4_usize)));
    let lawless = checkpoints(Maybe::Absent(gandr_core_checker::law::Absent::Unstated));
    let round_trip = |checkpoints: &Checkpoints, which: &str| {
        let bytes = encode_checkpoints(checkpoints).expect("an interfaced atom encodes");
        assert_eq!(
            decode_checkpoints(Bytes(bytes.as_ref())),
            Ok(checkpoints.clone()),
            "{which} decodes to itself"
        );
        bytes
    };
    let lawful_bytes = round_trip(&lawful, "a lawful interface");
    let lawless_bytes = round_trip(&lawless, "a lawless one");
    assert_ne!(
        lawful_bytes.as_ref(),
        lawless_bytes.as_ref(),
        "dropping the law changes the content"
    );
}

#[test]
fn a_quantified_value_root_round_trips_and_its_bounds_are_content()
{
    use gandr_kernel_term::StageBinder;
    use gandr_kernel_term::StageBound;
    let checkpoints = |stages: Vec<StageBound>| {
        let content = crate::fixture::item_content(
            Reference::Unoccupied,
            &crate::content::DeclarationRoots::Value {
                signature: Maybe::Absent(signature::Absent::Unsigned),
                body: Maybe::Present(NodeIndex::from(0_usize)),
                laws: Vec::new(),
                rules: Vec::new(),
                stages,
                supplies: Vec::new(),
                models: Vec::new(),
            },
            &[ContentNode::Tuple(Vec::new())],
        );
        let item = ItemCheckpoint::new(
            content,
            Footprint::from_parts(
                BTreeSet::new(),
                BTreeSet::new(),
                Opacity::Transparent,
                HoleMark::Filled,
            ),
            vec![Answered::new(Reference::Unoccupied, Answer::Untyped)],
            Typing::Owed,
        );
        Checkpoints::new(CheckBudget::DEFAULT, vec![item])
    };
    // `@[i : Size, j < i]`, then `@[i : Size, j : Size]`.
    let bounded = checkpoints(vec![
        StageBound::Unbounded,
        StageBound::Below(StageBinder::from(0_usize)),
    ]);
    let bytes = encode_checkpoints(&bounded).expect("a quantified root encodes");
    assert_eq!(
        decode_checkpoints(Bytes(bytes.as_ref())),
        Ok(bounded),
        "and decodes to itself, each binder with its bound"
    );
    let unbounded = encode_checkpoints(&checkpoints(vec![
        StageBound::Unbounded,
        StageBound::Unbounded,
    ]))
    .expect("an unbounded root encodes");
    assert_ne!(
        bytes.as_ref(),
        unbounded.as_ref(),
        "changing a bound changes the content"
    );
    let plain = encode_checkpoints(&checkpoints(Vec::new())).expect("a plain root encodes");
    assert_ne!(
        bytes.as_ref(),
        plain.as_ref(),
        "and so does dropping the binders"
    );
}

#[test]
fn a_supplying_value_root_round_trips_and_its_supplies_are_content_1227()
{
    use gandr_kernel_term::Stage;
    use gandr_kernel_term::StageBinder;
    use gandr_kernel_term::StageBound;
    use gandr_kernel_term::StageId;
    let checkpoints = |supplies: Vec<(NodeIndex, StageBinder, Stage)>| {
        let content = crate::fixture::item_content(
            Reference::Unoccupied,
            &crate::content::DeclarationRoots::Value {
                signature: Maybe::Absent(signature::Absent::Unsigned),
                body: Maybe::Present(NodeIndex::from(0_usize)),
                laws: Vec::new(),
                rules: Vec::new(),
                stages: vec![StageBound::Unbounded, StageBound::Unbounded],
                supplies,
                models: Vec::new(),
            },
            &[ContentNode::Tuple(Vec::new())],
        );
        let item = ItemCheckpoint::new(
            content,
            Footprint::from_parts(
                BTreeSet::new(),
                BTreeSet::new(),
                Opacity::Transparent,
                HoleMark::Filled,
            ),
            vec![Answered::new(Reference::Unoccupied, Answer::Untyped)],
            Typing::Owed,
        );
        Checkpoints::new(CheckBudget::DEFAULT, vec![item])
    };
    let supply = |stage: usize| {
        (
            NodeIndex::from(0_usize),
            StageBinder::from(0_usize),
            Stage::At(StageId::from(stage)),
        )
    };
    // `f[i = j]` in a body quantified `@[j : Size, k : Size]`, then
    // `f[i = k]`.
    let supplied = checkpoints(vec![supply(0)]);
    let bytes = encode_checkpoints(&supplied).expect("a supplying root encodes");
    assert_eq!(
        decode_checkpoints(Bytes(bytes.as_ref())),
        Ok(supplied),
        "and decodes to itself, each supply at its head"
    );
    let other = encode_checkpoints(&checkpoints(vec![supply(1)])).expect("another supply encodes");
    assert_ne!(
        bytes.as_ref(),
        other.as_ref(),
        "supplying another stage changes the content"
    );
    let unsupplied =
        encode_checkpoints(&checkpoints(Vec::new())).expect("an unsupplied root encodes");
    assert_ne!(
        bytes.as_ref(),
        unsupplied.as_ref(),
        "and so does dropping the supply"
    );
}

#[test]
fn a_modelled_value_root_round_trips_and_its_candidates_are_content_739()
{
    // A body `(?a)` whose call omits a one-component slot `?a`, answered by
    // candidates passing `1` and `2`.
    let hole = gandr_core_term::hole::HoleId::nominated(
        gandr_core_term::hole::NominationIndex::from(0_u32),
    )
    .expect("the first nominated name");
    let checkpoints = |second: &'static str, models: bool| {
        let models = if models {
            vec![crate::content::ModelRoots {
                holes: vec![NodeIndex::from(3_usize)],
                fixed: Vec::new(),
                candidates: vec![vec![NodeIndex::from(1_usize)], vec![NodeIndex::from(
                    2_usize,
                )]],
            }]
        }
        else {
            Vec::new()
        };
        let content = crate::fixture::item_content(
            Reference::Unoccupied,
            &crate::content::DeclarationRoots::Value {
                signature: Maybe::Absent(signature::Absent::Unsigned),
                body: Maybe::Present(NodeIndex::from(0_usize)),
                laws: Vec::new(),
                rules: Vec::new(),
                stages: Vec::new(),
                supplies: Vec::new(),
                models,
            },
            &[
                ContentNode::Tuple(vec![NodeIndex::from(3_usize)]),
                ContentNode::Literal(crate::fixture::integer(crate::fixture::Digits("1"))),
                ContentNode::Literal(crate::fixture::integer(crate::fixture::Digits(second))),
                ContentNode::Hole(hole),
            ],
        );
        let item = ItemCheckpoint::new(
            content,
            Footprint::from_parts(
                BTreeSet::new(),
                BTreeSet::new(),
                Opacity::Transparent,
                HoleMark::Filled,
            ),
            vec![Answered::new(Reference::Unoccupied, Answer::Untyped)],
            Typing::Owed,
        );
        Checkpoints::new(CheckBudget::DEFAULT, vec![item])
    };
    let modelled = checkpoints("2", true);
    let bytes = encode_checkpoints(&modelled).expect("a modelled root encodes");
    assert_eq!(
        decode_checkpoints(Bytes(bytes.as_ref())),
        Ok(modelled),
        "and decodes to itself, each candidate's components at their roots"
    );
    let other = encode_checkpoints(&checkpoints("3", true)).expect("another candidate encodes");
    assert_ne!(
        bytes.as_ref(),
        other.as_ref(),
        "changing a candidate changes the content"
    );
    let unmodelled = encode_checkpoints(&checkpoints("2", false));
    assert!(
        unmodelled.is_ok_and(|unmodelled| unmodelled.as_ref() != bytes.as_ref()),
        "and so does dropping the slot"
    );
}

#[test]
fn a_type_of_words_round_trips_its_cells()
{
    use gandr_core_term::RuleNode;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::ConstructorTag;
    use gandr_kernel_term::FreeCell;
    use gandr_kernel_term::FreeCells;

    let point = |tag: usize| -> alloc::boxed::Box<[RuleNode]> {
        [RuleNode::Constructor(ConstructorTag::from(tag))].into()
    };
    let checkpoints = |presentation: gandr_core_term::Presentation| {
        let content = crate::fixture::item_content(
            Reference::Unoccupied,
            &crate::content::DeclarationRoots::Data(crate::content::DataRoots {
                parameters: Vec::new(),
                indices: Vec::new(),
                results: Vec::new(),
                constructors: vec![Vec::new(), vec![NodeIndex::from(0_usize)], vec![
                    NodeIndex::from(0_usize),
                ]],
                kind: NodeIndex::from(0_usize),
                presentation,
            }),
            &[ContentNode::Product(Vec::new())],
        );
        let item = ItemCheckpoint::new(
            content,
            Footprint::from_parts(
                BTreeSet::new(),
                BTreeSet::new(),
                Opacity::Transparent,
                HoleMark::Filled,
            ),
            vec![Answered::new(Reference::Unoccupied, Answer::Untyped)],
            Typing::Owed,
        );
        Checkpoints::new(CheckBudget::DEFAULT, vec![item])
    };
    let cells = |tag: usize| {
        FreeCells::new(ConstantIndex::from(3_usize), vec![FreeCell::new(
            point(tag),
            point(tag),
        )])
    };
    let words = checkpoints(gandr_core_term::Presentation::words(cells(0)));
    let bytes = encode_checkpoints(&words).expect("a type of words encodes");
    assert_eq!(
        decode_checkpoints(Bytes(bytes.as_ref())),
        Ok(words),
        "and decodes to itself, its cells beside its rules"
    );
    let elsewhere =
        encode_checkpoints(&checkpoints(gandr_core_term::Presentation::words(cells(1))))
            .expect("words at another point encode");
    assert_ne!(
        bytes.as_ref(),
        elsewhere.as_ref(),
        "the point the cells loop at is content"
    );
    let bare = encode_checkpoints(&checkpoints(gandr_core_term::Presentation::new(
        cells(0).cancellations(),
    )))
    .expect("the same rules with no cell encode");
    assert_ne!(
        bytes.as_ref(),
        bare.as_ref(),
        "and so is whether the rules were minted from cells"
    );
}

#[test]
fn an_indexed_family_round_trips_its_indices()
{
    // A family over one index whose two constructors state the nodes at
    // `stated`.
    let checkpoints = |indices: Vec<NodeIndex>, stated: [usize; 2]| {
        let results = if indices.is_empty() {
            Vec::new()
        }
        else {
            stated
                .iter()
                .map(|&node| vec![NodeIndex::from(node)])
                .collect()
        };
        let content = crate::fixture::item_content(
            Reference::Unoccupied,
            &crate::content::DeclarationRoots::Data(crate::content::DataRoots {
                parameters: Vec::new(),
                indices,
                constructors: vec![Vec::new(), vec![NodeIndex::from(0_usize)]],
                results,
                kind: NodeIndex::from(0_usize),
                presentation: gandr_core_term::Presentation::new(Vec::new()),
            }),
            &[
                ContentNode::Product(Vec::new()),
                ContentNode::Tuple(Vec::new()),
            ],
        );
        let item = ItemCheckpoint::new(
            content,
            Footprint::from_parts(
                BTreeSet::new(),
                BTreeSet::new(),
                Opacity::Transparent,
                HoleMark::Filled,
            ),
            vec![Answered::new(Reference::Unoccupied, Answer::Untyped)],
            Typing::Owed,
        );
        Checkpoints::new(CheckBudget::DEFAULT, vec![item])
    };
    let indexed = checkpoints(vec![NodeIndex::from(0_usize)], [1, 1]);
    let bytes = encode_checkpoints(&indexed).expect("an indexed family encodes");
    assert_eq!(
        decode_checkpoints(Bytes(bytes.as_ref())),
        Ok(indexed),
        "and decodes to itself, its indices beside its constructors"
    );
    let restated = encode_checkpoints(&checkpoints(vec![NodeIndex::from(0_usize)], [1, 0]))
        .expect("other stated indices encode");
    assert_ne!(
        bytes.as_ref(),
        restated.as_ref(),
        "the index a constructor states is content"
    );
    let free = encode_checkpoints(&checkpoints(Vec::new(), [1, 1]))
        .expect("the same table with no index encodes");
    assert_ne!(bytes.as_ref(), free.as_ref(), "and so is the index itself");
}

/// One refusal of every kind, and of every nested reason a kind carries:
/// each form, zone, access defect, run fault, occurrence site, stratum and
/// translator defect.
///
/// # Specification
/// trivial.
fn every_refusal() -> Vec<Refusal>
{
    use gandr_core_checker::ComponentOrdinal;
    use gandr_core_checker::LoopRespect;
    use gandr_core_checker::SealSite;
    use gandr_core_checker::SealingSite;
    use gandr_core_checker::ua::StratumDefect;
    use gandr_core_checker::ua::UaDefect;
    use gandr_core_checker::ua::Way;
    use gandr_kernel_term::Apartness;
    use gandr_kernel_term::CellIndex;
    use gandr_kernel_term::RuleIndex;
    use gandr_kernel_term::RuleRefusal;
    use gandr_theory_sites::ElementIndex;
    use gandr_theory_sites::ShapeIndex;

    use super::AccessDefect;
    use super::ArgumentPosition;
    use super::BinderDepth;
    use super::CheckBudget;
    use super::ConstructorTag;
    use super::DeBruijnIndex;
    use super::FieldPosition;
    use super::Form;
    use super::OccurrenceSite;
    use super::ParameterPosition;
    use super::RunFault;
    use super::RunStep;
    use super::StaticArity;
    use super::Zone;

    let at = Site::Node(NodeIndex::from(3_usize));
    let other = Site::Node(NodeIndex::from(5_usize));
    let ty = || crate::fixture::type_content(&[ContentNode::Product(Vec::new())]);
    let reference = Reference::Item {
        key: ItemKey::from([1].as_slice()),
        occurrence: Occurrence::from(0_usize),
    };
    let rule = RuleIndex::from(1_usize);
    let cell = CellIndex::from(2_usize);
    let mut refusals = vec![
        Refusal::NotADataType(reference.clone()),
        Refusal::DataKindNotUniverse(at),
        Refusal::DataFieldLevel {
            field: at,
            kind: ty(),
        },
        Refusal::RuleNotPresentable {
            kind: at,
            refusal: RuleRefusal {
                rule,
                fault: super::RULE_FAULTS[1],
            },
        },
        Refusal::RuleNotRespected { at, rule },
        Refusal::NotApart {
            at,
            reason: Apartness::Agree,
        },
        Refusal::LoopNotRespected {
            at,
            cell,
            reason: LoopRespect::Apart,
        },
        Refusal::LoopUndecided { at, cell },
        Refusal::DataArgumentArity(at),
        Refusal::UnknownConstructor {
            at,
            tag: ConstructorTag::from(2_usize),
        },
        Refusal::ConstructorArity(at),
        Refusal::NonExhaustiveDataCase(at),
        Refusal::AbsentRecordField(at),
        Refusal::AbsentTupleComponent(at),
        Refusal::MissingRecordField { at, expected: ty() },
        Refusal::AbstractKindNotUniverse(at),
        Refusal::RepresentationAboveKind {
            representation: at,
            kind: ty(),
        },
        Refusal::NotAnAbstractType(reference.clone()),
        Refusal::AtomTransport {
            at,
            atom: reference.clone(),
        },
        Refusal::SealSiteRepeated(SealSite::new(
            SealingSite::from(1_usize),
            ComponentOrdinal::from(2_usize),
        )),
        Refusal::TypeMismatch {
            at,
            synthesised: ty(),
            expected: ty(),
        },
        Refusal::ShapeMismatch {
            at,
            wanted: super::SHAPES[2],
            found: ty(),
        },
        Refusal::UnknownConstant {
            at,
            constant: reference.clone(),
        },
        Refusal::OutOfFragment {
            at,
            former: super::FORMERS[3],
        },
        Refusal::BudgetExceeded {
            budget: CheckBudget::from(9_usize),
        },
        Refusal::DanglingNode { at },
        Refusal::AdmissionOrder,
        Refusal::MachineInvariant,
        Refusal::SortMismatch {
            at,
            synthesised: ty(),
            expected: ty(),
        },
        Refusal::LevelMismatch {
            at,
            synthesised: ty(),
            expected: ty(),
        },
        Refusal::DependentBind {
            at,
            synthesised: ty(),
        },
        Refusal::Undecided { at },
        Refusal::FamilyArity {
            at,
            expected: StaticArity::from(1_u32),
            actual: StaticArity::from(2_u32),
        },
        Refusal::FamilyArgumentClassifier {
            at,
            position: ArgumentPosition::from(1_u32),
            synthesised: ty(),
            expected: ty(),
        },
        Refusal::StaticLambdaArgument { at },
        Refusal::StaticClassifierExpected { at, found: ty() },
        Refusal::PathCode(at),
        Refusal::EndpointMismatch {
            at,
            left: Site::Unreached,
            right: other,
        },
        Refusal::CompoundEndpoint {
            at,
            synthesised: ty(),
        },
        Refusal::FunextUnsupported {
            at,
            classifier: ty(),
        },
        Refusal::PointwiseDistinct(at),
        Refusal::EquivUnsupported {
            at,
            classifier: ty(),
        },
        Refusal::UncertifiedStratum { at, code: ty() },
        Refusal::RoundTripDistinct(at),
        Refusal::NotOver {
            at,
            synthesised: ty(),
            expected: ty(),
        },
        Refusal::UnenclosedRun { at },
        Refusal::ImplicitUnsolved {
            at,
            reason: gandr_core_checker::Unsolved::Escape,
        },
        Refusal::ModelUnanswered { at },
        Refusal::ModelAmbiguous {
            at,
            survivors: [0_usize, 2, 70]
                .into_iter()
                .map(gandr_core_term::model::CandidatePlace::from)
                .fold(
                    gandr_core_term::model::Survivors::default(),
                    gandr_core_term::model::Survivors::with,
                ),
        },
        Refusal::CapabilityForged { at, expected: ty() },
        Refusal::CapabilityAmplified {
            at,
            synthesised: ty(),
            expected: ty(),
        },
        Refusal::CapabilityOutsideAuthority {
            at,
            capability: ty(),
        },
        Refusal::CapabilityEscaped { at, found: ty() },
        Refusal::CapabilityConsumable(at),
        Refusal::CapabilityUngranted(at),
        Refusal::SessionNotEquivalent(at),
        Refusal::SessionNotSubtype(at),
        Refusal::SessionCodeExpected(at),
        Refusal::OpenSessionPayload(at),
        Refusal::NonCovariantMotive(at),
        Refusal::RideUnsupported(at),
        Refusal::ForwardUnsupported(at),
        Refusal::Boundary(at),
        Refusal::EffectSignatureConflict {
            at,
            first: ty(),
            second: ty(),
        },
        Refusal::UnknownOperation { at },
        Refusal::HandlerCoverage { at },
        Refusal::ShiftWithoutReset { at },
        Refusal::DependentStack {
            at,
            synthesised: ty(),
        },
    ];
    refusals.extend(
        [
            Form::Thunk(at),
            Form::Lambda(at),
            Form::Hole,
            Form::StaticLambda(at),
            Form::Injection(at),
            Form::Case(at),
            Form::Fixpoint(at),
            Form::List(at),
            Form::Reify(at),
            Form::Handle(at),
            Form::Reset(at),
            Form::Shift(at),
            Form::With(at),
            Form::Nested(at),
            Form::Offer(at),
            Form::Scope(at),
            Form::Run(at),
        ]
        .map(|form| Refusal::NotSynthesisable { form }),
    );
    refusals.extend(
        [Zone::Intuitionistic, Zone::Linear].map(|zone| Refusal::UnboundIndex {
            at,
            zone,
            index: DeBruijnIndex::from(4_u32),
            depth: BinderDepth::from(2_usize),
        }),
    );
    refusals.extend(
        [
            AccessDefect::NotHeld,
            AccessDefect::Lent,
            AccessDefect::HeldCaptured {
                by: super::CAPTURES[1],
            },
            AccessDefect::Escaped {
                by: super::CAPTURES[2],
            },
            AccessDefect::Unended,
            AccessDefect::Spent,
            AccessDefect::NotAView,
            AccessDefect::ReadOnly,
            AccessDefect::UnwindEffect,
            AccessDefect::Unindexed,
            AccessDefect::HeldShared,
            AccessDefect::HeldCopied,
            AccessDefect::Moved,
            AccessDefect::Kept,
            AccessDefect::KeptEscaped,
            AccessDefect::Consumed,
        ]
        .map(|defect| Refusal::Access { at, defect }),
    );
    refusals.extend(
        [
            gandr_core_checker::codata::CodataFault::Undeclared,
            gandr_core_checker::codata::CodataFault::KindNotUniverse,
            gandr_core_checker::codata::CodataFault::WithoutObservations,
            gandr_core_checker::codata::CodataFault::Occurrence,
            gandr_core_checker::codata::CodataFault::ObservationLevel,
            gandr_core_checker::codata::CodataFault::Arity,
        ]
        .map(|fault| Refusal::Codata { at, fault }),
    );
    let step = RunStep::from(2_u32);
    refusals.extend(
        [
            RunFault::WrongDirection(step),
            RunFault::WrongLabel(step),
            RunFault::ResumeAfterEnd(step),
            RunFault::Incomplete(step),
            RunFault::OfferNarrowed,
        ]
        .map(|fault| Refusal::RunNotAdmitted { at, fault }),
    );
    refusals.extend([
        Refusal::DialogueUnmatched { at, step },
        Refusal::DialogueInverted {
            at,
            earlier: RunStep::from(1_u32),
            later: step,
        },
    ]);
    for site in [
        OccurrenceSite::Parameter(ParameterPosition::from(1_usize)),
        OccurrenceSite::Field {
            tag: ConstructorTag::from(1_usize),
            field: FieldPosition::from(0_usize),
        },
    ] {
        refusals.extend([
            Refusal::NegativeOccurrence(site),
            Refusal::NestedOccurrence(site),
            Refusal::IndexOccurrence(site),
            Refusal::NonUniformOccurrence(site),
            Refusal::CrossBlockReference {
                site,
                index: reference.clone(),
            },
        ]);
    }
    refusals.extend(
        [
            StratumDefect::Degree {
                degree: gandr_theory_sites::Degree::from(1_usize),
            },
            StratumDefect::Condition {
                degree: gandr_theory_sites::Degree::from(2_usize),
            },
            StratumDefect::Allowance {
                bound: gandr_theory_sites::ShapeSize::from(3_usize),
            },
        ]
        .map(|stratum| Refusal::UaUncertified { at, stratum }),
    );
    let corolla = ShapeIndex::from(1_usize);
    let element = ElementIndex::from(2_usize);
    refusals.extend(
        [
            UaDefect::UnknownGenerator { way: Way::Forward },
            UaDefect::UnknownGenerator { way: Way::Backward },
            UaDefect::PastTheBound {
                profile: gandr_theory_sites::Profile {
                    inputs: gandr_theory_sites::PortCount::from(1_usize),
                    outputs: gandr_theory_sites::PortCount::from(2_usize),
                },
            },
            UaDefect::Cardinality { corolla },
            UaDefect::Tables { corolla },
            UaDefect::NotInverse { corolla, element },
            UaDefect::NotNatural { corolla, element },
            UaDefect::Stuck { corolla, element },
        ]
        .map(|defect| Refusal::UaInequivalent { at, defect }),
    );
    refusals
}

#[test]
fn every_refusal_round_trips_under_its_own_encoding()
{
    let mut encodings = alloc::collections::BTreeSet::new();
    for refusal in every_refusal() {
        let mut bytes = CheckpointBytes::default();
        super::write_refusal(&mut Writer { sink: &mut bytes }, &refusal).expect("portable refusal");
        assert!(
            encodings.insert(bytes.as_ref().to_vec()),
            "{refusal:?} keeps its own encoding"
        );
        let mut reader = Reader {
            bytes: bytes.as_ref(),
            cursor: 0,
        };
        assert_eq!(super::read_refusal(&mut reader), Ok(refusal));
        assert_eq!(reader.finish(), Ok(()));
    }
}

#[test]
fn an_offer_narrowed_fault_is_read_only_at_step_zero()
{
    let refusal = Refusal::RunNotAdmitted {
        at: Site::Unreached,
        fault: super::RunFault::OfferNarrowed,
    };
    let mut bytes = CheckpointBytes::default();
    super::write_refusal(&mut Writer { sink: &mut bytes }, &refusal).expect("portable refusal");
    let mut stepped = bytes.as_ref().to_vec();
    // The step is the frame's last word, written little-endian.
    let low = stepped
        .len()
        .checked_sub(8)
        .and_then(|start| stepped.get_mut(start))
        .expect("a step word ends the frame");
    assert_eq!(0, *low, "the fault is written at step zero");
    *low = 1;
    let mut reader = Reader {
        bytes: &stepped,
        cursor: 0,
    };
    assert_eq!(
        super::read_refusal(&mut reader),
        Err(CodecError::NonCanonical)
    );
}

/// Read `bytes` as a supported table.
///
/// # Specification
/// trivial.
fn read_table(bytes: &CheckpointBytes) -> Result<Vec<crate::support::SupportedNode>, CodecError>
{
    super::read_nodes(&mut Reader {
        bytes: bytes.as_ref(),
        cursor: 0,
    })
}

/// Write `parts` as a table, each former with the scope and cover given,
/// whatever they claim: the formers and scopes, then every edge's indices.
///
/// # Specification
/// trivial.
fn write_parts(parts: &[(ContentNode, super::Scope, Vec<super::Thinning>)]) -> CheckpointBytes
{
    let mut bytes = CheckpointBytes::default();
    let mut writer = Writer { sink: &mut bytes };
    writer.count(Count(parts.len())).expect("count");
    for &(ref former, scope, _) in parts {
        super::write_node(&mut writer, former).expect("former");
        super::write_scope(&mut writer, scope).expect("scope");
    }
    for &(_, _, ref cover) in parts {
        for edge in cover {
            super::write_selection(&mut writer, edge);
        }
    }
    bytes
}

#[test]
fn supported_tables_round_trip_and_reject_forged_support()
{
    use gandr_core_term::BinderDepth;
    use gandr_core_term::Zone;
    use gandr_kernel_term::DeBruijnIndex;

    use super::Scope;
    use super::Thinning;
    let index = NodeIndex::from;
    let named = Reference::Item {
        key: ItemKey::from("named"),
        occurrence: Occurrence::from(0_usize),
    };
    // El (λx. (x, named, v1, v2, ℓ0)): the lambda's free variables sit in
    // both zones, two of them intuitionistic, and its tuple reads a constant.
    let ty = crate::fixture::type_content(&[
        ContentNode::Element {
            code: index(1_usize),
            target: super::Level::zero(),
        },
        ContentNode::StaticLambda(index(2_usize)),
        ContentNode::Tuple(vec![
            index(3_usize),
            index(4_usize),
            index(5_usize),
            index(6_usize),
            index(7_usize),
        ]),
        ContentNode::Variable {
            zone: Zone::Intuitionistic,
            index: DeBruijnIndex::from(0_u32),
        },
        ContentNode::Constant(named.clone()),
        ContentNode::Variable {
            zone: Zone::Intuitionistic,
            index: DeBruijnIndex::from(2_u32),
        },
        ContentNode::Variable {
            zone: Zone::Intuitionistic,
            index: DeBruijnIndex::from(3_u32),
        },
        ContentNode::Variable {
            zone: Zone::Linear,
            index: DeBruijnIndex::from(0_u32),
        },
    ]);
    let mut bytes = CheckpointBytes::default();
    super::write_type(&mut Writer { sink: &mut bytes }, &ty).expect("a resolved type");
    let read = read_type(&mut Reader {
        bytes: bytes.as_ref(),
        cursor: 0,
    })
    .expect("the written type reads back");
    assert_eq!(
        read, ty,
        "covers, scopes, the root support and the rebuilt reads survive"
    );
    assert!(
        read.nodes()
            .first()
            .is_some_and(|root| root.type_reads().eq([&named])),
        "the reader rebuilds the references no byte carries"
    );

    // A signature whose field is scoped under its parameter: the field's root
    // support selects the parameter, so the placements carry bytes.
    let data = crate::content::DataContent::tabulated(
        &crate::content::DataRoots {
            parameters: vec![index(1_usize)],
            indices: Vec::new(),
            results: Vec::new(),
            constructors: vec![vec![index(2_usize)]],
            kind: index(4_usize),
            presentation: gandr_core_term::Presentation::new(Vec::new()),
        },
        &[
            ContentNode::Base(BaseType::String),
            ContentNode::Base(BaseType::Integer),
            ContentNode::Element {
                code: index(3_usize),
                target: super::Level::zero(),
            },
            ContentNode::Variable {
                zone: Zone::Intuitionistic,
                index: DeBruijnIndex::from(0_u32),
            },
            ContentNode::Product(Vec::new()),
        ],
    );
    assert!(
        data.placements()
            .iter()
            .any(|support| support.indices(Zone::Intuitionistic).len() != 0),
        "the field's support is not empty"
    );
    let mut bytes = CheckpointBytes::default();
    super::write_data_content(&mut Writer { sink: &mut bytes }, &data)
        .expect("a resolved signature");
    assert_eq!(
        super::read_data_content(&mut Reader {
            bytes: bytes.as_ref(),
            cursor: 0,
        }),
        Ok(data),
        "a signature's root supports survive"
    );

    let width = |intuitionistic: usize, linear: usize| {
        Scope::new(BinderDepth::from(intuitionistic), BinderDepth::from(linear))
    };
    let select = |indices: &[u32]| {
        Thinning::from_ascending(
            &indices
                .iter()
                .copied()
                .map(DeBruijnIndex::from)
                .collect::<Vec<_>>(),
            &[],
        )
        .expect("ascending")
    };
    let variable = ContentNode::Variable {
        zone: Zone::Intuitionistic,
        index: DeBruijnIndex::from(0_u32),
    };
    // λx. x over a free v0 beside it: the lambda's scope is one wide and
    // its edge keeps the bound slot and the free one.
    let tuple = ContentNode::Tuple(vec![index(2_usize), index(2_usize)]);
    let honest = [
        (
            ContentNode::StaticLambda(index(1_usize)),
            width(1, 0),
            vec![select(&[0, 1])],
        ),
        (tuple, width(2, 0), vec![select(&[0]), select(&[1])]),
        (variable.clone(), width(1, 0), Vec::new()),
    ];
    assert!(
        read_table(&write_parts(&honest)).is_ok(),
        "the honest table the forgeries alter is admitted"
    );
    let forged = |at: usize, part: (ContentNode, Scope, Vec<Thinning>)| {
        let mut parts = honest.to_vec();
        if let Some(slot) = parts.get_mut(at) {
            *slot = part;
        }
        read_table(&write_parts(&parts))
    };
    for (case, outcome) in [
        (
            "a widened scope leaves a slot unused",
            forged(
                0,
                (
                    ContentNode::StaticLambda(index(1_usize)),
                    width(2, 0),
                    vec![select(&[0, 1])],
                ),
            ),
        ),
        (
            "an edge past its node's scope",
            forged(
                0,
                (
                    ContentNode::StaticLambda(index(1_usize)),
                    width(1, 0),
                    vec![select(&[0, 5])],
                ),
            ),
        ),
        (
            "a cycle",
            forged(
                0,
                (
                    ContentNode::StaticLambda(index(0_usize)),
                    width(1, 0),
                    vec![select(&[1])],
                ),
            ),
        ),
    ] {
        assert_eq!(outcome, Err(CodecError::Corrupt), "{case}");
    }
    let mut duplicated = honest.to_vec();
    duplicated.push((variable, width(1, 0), Vec::new()));
    assert_eq!(
        read_table(&write_parts(&duplicated)),
        Err(CodecError::NonCanonical),
        "a node listed twice"
    );
    let root_support = |words: [u64; 2]| {
        let mut typed = CheckpointBytes::default();
        let mut writer = Writer { sink: &mut typed };
        super::write_nodes(&mut writer, ty.nodes()).expect("a resolved table");
        for word in words {
            writer.word(Word(word));
        }
        writer.word(Word(0_u64));
        read_type(&mut Reader {
            bytes: typed.as_ref(),
            cursor: 0,
        })
    };
    assert_eq!(
        ty.root().indices(Zone::Intuitionistic).collect::<Vec<_>>(),
        [DeBruijnIndex::from(1_u32), DeBruijnIndex::from(2_u32)],
        "the root support the forgeries reorder"
    );
    assert!(root_support([1, 2]).is_ok(), "the honest root support");
    assert_eq!(
        root_support([2, 1]),
        Err(CodecError::Corrupt),
        "a root support out of order"
    );
    assert_eq!(
        root_support([1, u64::from(u32::MAX) + 1]),
        Err(CodecError::Corrupt),
        "a root support index past u32"
    );

    let checkpoints =
        crate::fixture::checked(&mut crate::fixture::every_former(crate::fixture::Noise(0)));
    let bytes = encode_checkpoints(&checkpoints).expect("a complete fixture");
    assert_eq!(decode_checkpoints(Bytes(bytes.as_ref())), Ok(checkpoints));
    let mut previous = bytes.as_ref().to_vec();
    *previous.get_mut(7).expect("version byte") = 11;
    assert_eq!(
        decode_checkpoints(Bytes(&previous)),
        Err(CodecError::Corrupt),
        "the previous version is refused, not reinterpreted"
    );
}
