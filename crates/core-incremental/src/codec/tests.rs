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
use super::ItemContent;
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
use super::write_nodes;
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
        super::TypeContent::from_nodes(vec![
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
    use gandr_core_term::effect::capability::RegionDepth;
    use gandr_kernel_term::Side;
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
            StackFrame::Project(Side::Right),
            StackFrame::Apply(index(3_usize)),
        ])),
        ContentNode::Stack {
            input: index(1_usize),
            output: index(2_usize),
        },
        ContentNode::WithType(index(1_usize), index(2_usize)),
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
            authority,
            grade: CapabilityGrade::Consumable,
            region: Region::Held,
        },
        ContentNode::Resume(index(1_usize), index(2_usize)),
        ContentNode::Reset(index(1_usize)),
        ContentNode::Shift(index(1_usize)),
        ContentNode::With(index(1_usize), index(2_usize)),
        ContentNode::Project(Side::Left, index(1_usize)),
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
    let typed = super::TypeContent::from_nodes(vec![ContentNode::Product(Vec::new())]);
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
        ContentNode::Session(SessionAction::Receive { endpoint }),
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
    let state = || TypeContent::from_nodes(vec![ContentNode::Product(Vec::new())]);
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
        Linearity::Delegated,
        Linearity::AsValue { endpoint: parent },
        Linearity::ArmsDisagree {
            endpoint: child,
            first: Site::Node(NodeIndex::from(4_usize)),
            other: Site::Unreached,
        },
        Linearity::Unrestricted,
        Linearity::Unbound {
            index: DeBruijnIndex::from(2_u32),
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
fn an_absurd_case_s_refusal_round_trips_with_its_reason()
{
    use gandr_kernel_term::Apartness;
    use gandr_kernel_term::RuleIndex;
    let at = Site::Node(NodeIndex::from(3_usize));
    let mut encodings = alloc::collections::BTreeSet::new();
    for reason in [
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

#[test]
fn discovery_accepts_cycles_repeated_roots_and_empty_tables()
{
    assert_eq!(check_discovery(&[], core::iter::empty()), Ok(()));
    let nodes = [
        ContentNode::Product(vec![NodeIndex::from(0_usize), NodeIndex::from(1_usize)]),
        ContentNode::Product(Vec::new()),
    ];
    assert_eq!(
        check_discovery(
            &nodes,
            [NodeIndex::from(0_usize), NodeIndex::from(0_usize)].into_iter()
        ),
        Ok(())
    );
    assert_eq!(
        check_discovery(&nodes, [NodeIndex::from(usize::MAX)].into_iter()),
        Err(CodecError::Corrupt)
    );
}

#[test]
fn type_tables_validate_roots_child_extents_and_sorts()
{
    let nodes = [ContentNode::Product(Vec::new())];
    assert_eq!(
        root_of_sort(&nodes, NodeIndex::from(0_usize), Sort::ValueType),
        Ok(())
    );
    assert_eq!(
        root_of_sort(&nodes, NodeIndex::from(0_usize), Sort::Value),
        Err(CodecError::Corrupt)
    );
    assert_eq!(
        root_of_sort(&nodes, NodeIndex::from(usize::MAX), Sort::ValueType),
        Err(CodecError::Corrupt)
    );
    let decode = |nodes: Vec<ContentNode>| {
        let mut bytes = CheckpointBytes::default();
        write_nodes(&mut Writer { sink: &mut bytes }, &nodes).expect("raw table encodes");
        read_type(&mut Reader {
            bytes: bytes.as_ref(),
            cursor: 0,
        })
    };
    assert_eq!(decode(vec![]), Err(CodecError::Corrupt));
    assert_eq!(
        decode(vec![ContentNode::Tuple(Vec::new())]),
        Err(CodecError::Corrupt)
    );
    assert_eq!(
        decode(vec![ContentNode::Product(vec![
            NodeIndex::from(1_usize),
            NodeIndex::from(0_usize)
        ]),]),
        Err(CodecError::Corrupt)
    );
    assert_eq!(
        decode(vec![
            ContentNode::Product(vec![NodeIndex::from(1_usize), NodeIndex::from(1_usize)]),
            ContentNode::Tuple(Vec::new()),
        ]),
        Err(CodecError::Corrupt)
    );
    let computation = decode(vec![
        ContentNode::Returner {
            result: NodeIndex::from(1_usize),
            effects: gandr_core_term::effect::EffectRow::EMPTY,
        },
        ContentNode::Product(Vec::new()),
    ])
    .expect("closed computation type");
    assert_eq!(
        computation.nodes().first().map(ContentNode::sort),
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
        b'G', b'C', b'K', b'P', b'T', 0, 0, 10, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    ];
    assert_eq!(
        encode_checkpoints(&checkpoints)
            .expect("empty checkpoint")
            .as_ref(),
        expected
    );
    assert_eq!(decode_checkpoints(Bytes(&expected)), Ok(checkpoints));
    let mut wrong_version = expected;
    *wrong_version.get_mut(7).expect("version byte") = 9;
    assert_eq!(
        decode_checkpoints(Bytes(&wrong_version)),
        Err(CodecError::Corrupt)
    );
    let mut program = CheckpointBytes::default();
    write_program(&mut program, &[]).expect("empty program");
    assert_eq!(program.as_ref(), b"GPROG\0\0\x07\0\0\0\0\0\0\0\0");
    assert_eq!(
        decode_checkpoints(Bytes(program.as_ref())),
        Err(CodecError::Corrupt)
    );
}

#[test]
fn checkpoint_encoding_reports_the_first_unresolved_plane()
{
    let unresolved = |sort| TypeContent::from_nodes(vec![ContentNode::Unresolved(sort)]);
    let mismatch = |synthesised, expected| {
        Typing::Refused(Refusal::TypeMismatch {
            at: Site::Unreached,
            synthesised,
            expected,
        })
    };
    let encode = |nodes: Vec<ContentNode>, answer, typing| {
        let content = ItemContent::from_parts(
            Reference::Unoccupied,
            crate::content::DeclarationRoots::Value {
                signature: Maybe::Absent(signature::Absent::Unsigned),
                body: Maybe::Present(NodeIndex::from(0_usize)),
                laws: Vec::new(),
            },
            nodes,
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
                TypeContent::from_nodes(vec![ContentNode::Product(Vec::new())]),
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

    for (tag, invalid_field) in [(0x01, 2), (0x20, 3)] {
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
    let valid_type = || TypeContent::from_nodes(vec![ContentNode::Product(Vec::new())]);
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
            Answer::Typed(TypeContent::from_nodes(vec![
                ContentNode::TypeLift {
                    inner: NodeIndex::from(1_usize),
                    target: level.clone(),
                },
                ContentNode::Product(Vec::new()),
            ])),
            Typing::Owed,
        ),
        (unit(), Answer::Untyped, Typing::Synthesised {
            produced: TypeContent::from_nodes(vec![
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
                synthesised: TypeContent::from_nodes(vec![ContentNode::Universe {
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
                expected: TypeContent::from_nodes(vec![
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
        let content = ItemContent::from_parts(
            Reference::Unoccupied,
            crate::content::DeclarationRoots::Value {
                signature: Maybe::Absent(signature::Absent::Unsigned),
                body: Maybe::Present(NodeIndex::from(0_usize)),
                laws: Vec::new(),
            },
            nodes,
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
        TypeContent::from_nodes(vec![ContentNode::Universe {
            sort: super::TypeSort::Ground(super::GroundSort::Value),
            level: level.clone(),
        }])
    };
    let valid = || TypeContent::from_nodes(vec![ContentNode::Product(Vec::new())]);
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
        let content = ItemContent::from_parts(
            Reference::Unoccupied,
            crate::content::DeclarationRoots::Value {
                signature: Maybe::Absent(signature::Absent::Unsigned),
                body: Maybe::Present(NodeIndex::from(0_usize)),
                laws: Vec::new(),
            },
            vec![ContentNode::Tuple(Vec::new())],
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
        let content = ItemContent::from_parts(
            Reference::Unoccupied,
            crate::content::DeclarationRoots::Value {
                signature: Maybe::Absent(signature::Absent::Unsigned),
                body: Maybe::Present(NodeIndex::from(0_usize)),
                laws,
            },
            vec![ContentNode::Tuple(Vec::new())],
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
        let content = ItemContent::from_parts(
            Reference::Unoccupied,
            crate::content::DeclarationRoots::Data(crate::content::DataRoots {
                parameters: Vec::new(),
                constructors: vec![Vec::new(), vec![NodeIndex::from(0_usize)], vec![
                    NodeIndex::from(0_usize),
                ]],
                kind: NodeIndex::from(0_usize),
                presentation,
            }),
            vec![ContentNode::Product(Vec::new())],
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
