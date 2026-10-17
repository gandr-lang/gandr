use alloc::string::String;
use alloc::vec;

use anodized::spec;
use gandr_core_checker::CheckBudget;
use gandr_core_checker::CheckingContext;
use gandr_core_checker::Declaration;
use gandr_core_checker::OriginToken;
use gandr_core_checker::UnadmittedFormer;
use gandr_core_checker::Verdict;
use gandr_core_checker::body;
use gandr_core_checker::check_declaration_supported;
use gandr_core_checker::signature;
use gandr_core_term::BinderDepth;
use gandr_core_term::CoreArena;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Magnitude;
use gandr_kernel_term::Sign;
use gandr_kernel_term::StringLiteral;
use quenchant_shape::shape::Maybe;

use super::Form;
use super::Projection;
use super::Refusal;
use super::Site;
use super::Typing;
use crate::boundary::ItemOrdinal;
use crate::boundary::NodeIndex;
use crate::content::ContentNode;
use crate::content::TypeContent;
use crate::content::encode_item;
use crate::region::Item;
use crate::region::ItemKey;
use crate::region::Program;
use crate::region::Reference;

/// A one-item program's verdict and its projection, judged under
/// `budget` in a fresh context.
///
/// # Specification
/// - requires: finite arena input; supplied ids are interpreted in it,
///   including unresolved ids that the checker must refuse by name.
/// - ensures: a fresh one-item judgement and its coordinate-free typing are
///   returned under the supplied budget; verdict class and conversion counts
///   agree between the two results.
/// - panics: only if the fixed one-item construction loses its declaration or
///   violates the program's ordering invariant.
///
/// # Adequacy
/// - hypothesis: L3 — checked, synthesised, owed and refused one-item inputs
///   exercise the fresh-context path, including zero budget and unknown names.
///   The fixture does not model multi-item admission or resumed state.
/// - witness: `typing::tests::each_verdict_projects_to_its_typing`
/// - witness: `typing::tests::each_refusal_projects_its_payload`
#[spec(ensures: |ret| match ret.0 {
        Verdict::Data => matches!(ret.1,Typing::Data),
        | Verdict::Checked { evidence, .. } => {
            matches!(ret.1, Typing::Checked { conversions } if conversions == evidence.conversions())
        },
        | Verdict::Synthesised { synthesised, .. } => {
            matches!(ret.1, Typing::Synthesised { conversions, .. } if conversions == synthesised.conversions())
        },
        | Verdict::Owed(_) => matches!(ret.1, Typing::Owed),
        | Verdict::Refused(_) => matches!(ret.1, Typing::Refused(_)),
    })]
fn judged(
    arena: CoreArena,
    signature: Maybe<ValueTypeId, signature::Absent>,
    body: Maybe<ValueId, body::Absent>,
    budget: CheckBudget,
) -> (Verdict, Typing)
{
    let mut program = Program::new(arena, vec![Item::new(
        ItemKey::from("it"),
        Declaration::new(
            ConstantIndex::from(0_usize),
            signature,
            body,
            OriginToken::from(0_usize),
        ),
    )])
    .expect("one item ascends");
    let declarations = program.declarations();
    let encoded = encode_item(
        program.arena(),
        program.layout(),
        ItemOrdinal::from(0_usize),
    );
    let (arena, layout) = program.parts_mut();
    let mut context = CheckingContext::new(arena, budget);
    let Some(declaration) = declarations.first()
    else {
        panic!("one declaration");
    };
    let verdict = check_declaration_supported(&mut context, declaration).verdict();
    let projection = Projection {
        arena: context.arena(),
        layout,
        sites: &encoded.sites,
        types: &crate::content::TypeMemo::default(),
    };
    let typing = projection.typing(&verdict);
    (verdict, typing)
}

/// The type table of one base type.
///
/// # Specification
/// trivial.
fn base(base: BaseType) -> TypeContent
{
    crate::fixture::type_content(&[ContentNode::Base(base)])
}

/// The integer literal zero.
///
/// # Specification
/// trivial.
fn zero() -> Literal
{
    Literal::Integer(IntegerLiteral::new(Sign::NonNegative, Magnitude::zero()))
}

#[test]
fn each_verdict_projects_to_its_typing()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let literal = arena.value_literal(zero());
    let (verdict, typing) = judged(
        arena,
        Maybe::Present(integer),
        Maybe::Present(literal),
        CheckBudget::DEFAULT,
    );
    let Verdict::Checked { evidence, .. } = verdict
    else {
        panic!("a literal checks against its base type: {verdict:?}");
    };
    assert_eq!(
        typing,
        Typing::Checked {
            conversions: evidence.conversions(),
        },
        "a checked verdict keeps its conversion count"
    );

    let mut arena = CoreArena::new();
    let literal = arena.value_literal(zero());
    let (verdict, typing) = judged(
        arena,
        Maybe::Absent(signature::Absent::Unsigned),
        Maybe::Present(literal),
        CheckBudget::DEFAULT,
    );
    let Verdict::Synthesised { synthesised, .. } = verdict
    else {
        panic!("an unsigned literal synthesises: {verdict:?}");
    };
    assert_eq!(
        typing,
        Typing::Synthesised {
            produced: base(BaseType::Integer),
            conversions: synthesised.conversions(),
        },
        "a synthesised verdict carries its type as content"
    );

    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let (_verdict, typing) = judged(
        arena,
        Maybe::Present(integer),
        Maybe::Absent(body::Absent::Hole),
        CheckBudget::DEFAULT,
    );
    assert_eq!(typing, Typing::Owed, "a signed hole is owed");

    let (_verdict, typing) = judged(
        CoreArena::new(),
        Maybe::Absent(signature::Absent::Unsigned),
        Maybe::Absent(body::Absent::Hole),
        CheckBudget::DEFAULT,
    );
    assert_eq!(
        typing,
        Typing::Refused(Refusal::NotSynthesisable { form: Form::Hole }),
        "an unsigned hole is refused"
    );
}

#[test]
fn each_refusal_projects_its_payload()
{
    let unsigned = || Maybe::Absent(signature::Absent::Unsigned);
    let first = Site::Node(NodeIndex::from(0_usize));

    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let text = arena.value_literal(Literal::Text(StringLiteral::new(String::from("a"))));
    let (_verdict, typing) = judged(
        arena,
        Maybe::Present(integer),
        Maybe::Present(text),
        CheckBudget::DEFAULT,
    );
    assert_eq!(
        typing,
        Typing::Refused(Refusal::TypeMismatch {
            at: Site::Node(NodeIndex::from(1_usize)),
            synthesised: base(BaseType::String),
            expected: base(BaseType::Integer),
        }),
        "a mismatch names the body's root and both types"
    );

    let mut arena = CoreArena::new();
    let dangling = arena.value_constant(ConstantIndex::from(5_usize));
    let (_verdict, typing) = judged(
        arena,
        unsigned(),
        Maybe::Present(dangling),
        CheckBudget::DEFAULT,
    );
    assert_eq!(
        typing,
        Typing::Refused(Refusal::UnknownConstant {
            at: first,
            constant: Reference::Unoccupied,
        }),
        "an unknown constant names what its position resolves to"
    );

    let mut arena = CoreArena::new();
    let unformed = arena.value_type_base(gandr_kernel_term::BaseType::Numeric);
    let (_verdict, typing) = judged(
        arena,
        Maybe::Present(unformed),
        Maybe::Absent(body::Absent::Hole),
        CheckBudget::DEFAULT,
    );
    assert_eq!(
        typing,
        Typing::Refused(Refusal::OutOfFragment {
            at: first,
            former: UnadmittedFormer::NumericAtom,
        }),
        "a former without a rule names the node carrying it"
    );

    let mut arena = CoreArena::new();
    let literal = arena.value_literal(zero());
    let returned = arena.computation_return(literal);
    let thunk = arena.value_thunk(returned);
    let (_verdict, typing) = judged(
        arena,
        unsigned(),
        Maybe::Present(thunk),
        CheckBudget::DEFAULT,
    );
    assert_eq!(
        typing,
        Typing::Refused(Refusal::NotSynthesisable {
            form: Form::Thunk(first),
        }),
        "a checking-only form names its site"
    );

    let mut arena = CoreArena::new();
    let variable = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let (_verdict, typing) = judged(
        arena,
        unsigned(),
        Maybe::Present(variable),
        CheckBudget::DEFAULT,
    );
    assert_eq!(
        typing,
        Typing::Refused(Refusal::UnboundIndex {
            at: first,
            zone: Zone::Intuitionistic,
            index: DeBruijnIndex::from(0_u32),
            depth: BinderDepth::from(0_usize),
        }),
        "an unbound variable names its zone, index and depth"
    );

    let mut arena = CoreArena::new();
    let literal = arena.value_literal(zero());
    let exhausted = CheckBudget::from(0_usize);
    let (_verdict, typing) = judged(arena, unsigned(), Maybe::Present(literal), exhausted);
    assert_eq!(
        typing,
        Typing::Refused(Refusal::BudgetExceeded { budget: exhausted }),
        "an exhausted allowance is named"
    );
}

#[test]
fn refusal_payloads_use_item_coordinates_and_type_content()
{
    let mut arena = crate::fixture::noisy(crate::fixture::Noise(9));
    let unit = arena.value_unit();
    let returned = arena.computation_return(unit);
    let thunk = arena.value_thunk(returned);
    let unit_type = arena.value_type_unit();
    let returner = arena.comp_type_returner(unit_type);
    let thunk_type = arena.value_type_thunk(returner);
    let quote = arena.value_quote(thunk_type);
    let root = arena.value_tuple(&[quote, thunk]);
    let integer = arena.value_type_base(BaseType::Integer);
    let integer_returner = arena.comp_type_returner(integer);
    let unreached = arena.value_unit();
    let program = Program::new(arena, vec![Item::new(
        ItemKey::from("it"),
        Declaration::new(
            ConstantIndex::from(17_usize),
            Maybe::Absent(signature::Absent::Unsigned),
            Maybe::Present(root),
            OriginToken::from(0_usize),
        ),
    )])
    .expect("one item ascends");
    let encoded = encode_item(
        program.arena(),
        program.layout(),
        ItemOrdinal::from(0_usize),
    );
    let projection = Projection {
        arena: program.arena(),
        layout: program.layout(),
        sites: &encoded.sites,
        types: &crate::content::TypeMemo::default(),
    };
    // The specified breadth-first walk is pair, quote, thunk, thunk type,
    // return, returner, unit value, unit type. Arena noise is not a site.
    let value_site = Site::Node(NodeIndex::from(6_usize));
    let computation_site = Site::Node(NodeIndex::from(4_usize));
    let type_site = Site::Node(NodeIndex::from(7_usize));
    let comp_type_site = Site::Node(NodeIndex::from(5_usize));
    let unit_content = || crate::fixture::type_content(&[ContentNode::Product(Vec::new())]);
    let returner_content = || {
        crate::fixture::type_content(&[
            ContentNode::Returner {
                result: NodeIndex::from(1_usize),
                effects: gandr_core_term::effect::EffectRow::EMPTY,
            },
            ContentNode::Product(Vec::new()),
        ])
    };
    let cases = [
        (
            super::CheckRefusal::PathCode(unit),
            Refusal::PathCode(value_site),
        ),
        (
            super::CheckRefusal::NotSynthesisable {
                form: super::CheckingForm::Injection(unit),
            },
            Refusal::NotSynthesisable {
                form: Form::Injection(value_site),
            },
        ),
        (
            super::CheckRefusal::NotSynthesisable {
                form: super::CheckingForm::Case(returned),
            },
            Refusal::NotSynthesisable {
                form: Form::Case(computation_site),
            },
        ),
        (
            super::CheckRefusal::TypeMismatch(super::Mismatch::Computation {
                at: returned,
                synthesised: returner,
                expected: integer_returner,
            }),
            Refusal::TypeMismatch {
                at: computation_site,
                synthesised: returner_content(),
                expected: crate::fixture::type_content(&[
                    ContentNode::Returner {
                        result: NodeIndex::from(1_usize),
                        effects: gandr_core_term::effect::EffectRow::EMPTY,
                    },
                    ContentNode::Base(BaseType::Integer),
                ]),
            },
        ),
        (
            super::CheckRefusal::ShapeMismatch {
                at: super::TermNode::Computation(returned),
                wanted: super::ExpectedShape::Arrow,
                found: super::TypeNode::Computation(returner),
            },
            Refusal::ShapeMismatch {
                at: computation_site,
                wanted: super::ExpectedShape::Arrow,
                found: returner_content(),
            },
        ),
        (
            super::CheckRefusal::NotSynthesisable {
                form: super::CheckingForm::Lambda(returned),
            },
            Refusal::NotSynthesisable {
                form: Form::Lambda(computation_site),
            },
        ),
        (
            super::CheckRefusal::NotSynthesisable {
                form: super::CheckingForm::Return(returned),
            },
            Refusal::NotSynthesisable {
                form: Form::Return(computation_site),
            },
        ),
        (
            super::CheckRefusal::NotSynthesisable {
                form: super::CheckingForm::StaticLambda(unit),
            },
            Refusal::NotSynthesisable {
                form: Form::StaticLambda(value_site),
            },
        ),
        (
            super::CheckRefusal::UnknownConstant {
                at: unit,
                constant: ConstantIndex::from(17_usize),
            },
            Refusal::UnknownConstant {
                at: value_site,
                constant: Reference::Item {
                    key: ItemKey::from("it"),
                    occurrence: crate::boundary::Occurrence::from(0_usize),
                },
            },
        ),
        (
            super::CheckRefusal::OutOfFragment {
                at: super::CoreNode::Type(super::TypeNode::Computation(returner)),
                former: UnadmittedFormer::NumericAtom,
            },
            Refusal::OutOfFragment {
                at: comp_type_site,
                former: UnadmittedFormer::NumericAtom,
            },
        ),
        (
            super::CheckRefusal::DanglingNode {
                node: super::CoreNode::Term(super::TermNode::Value(unreached)),
            },
            Refusal::DanglingNode {
                at: Site::Unreached,
            },
        ),
        (
            super::CheckRefusal::SortMismatch {
                at: unit,
                synthesised: unit_type,
                expected: integer,
            },
            Refusal::SortMismatch {
                at: value_site,
                synthesised: unit_content(),
                expected: base(BaseType::Integer),
            },
        ),
        (
            super::CheckRefusal::LevelMismatch {
                at: unit,
                synthesised: integer,
                expected: unit_type,
            },
            Refusal::LevelMismatch {
                at: value_site,
                synthesised: base(BaseType::Integer),
                expected: unit_content(),
            },
        ),
        (
            super::CheckRefusal::DependentBind {
                at: returned,
                synthesised: returner,
            },
            Refusal::DependentBind {
                at: computation_site,
                synthesised: returner_content(),
            },
        ),
        (
            super::CheckRefusal::Undecided { at: unit },
            Refusal::Undecided { at: value_site },
        ),
        (
            super::CheckRefusal::FamilyArity {
                at: unit,
                expected: super::StaticArity::from(2_u32),
                actual: super::StaticArity::from(5_u32),
            },
            Refusal::FamilyArity {
                at: value_site,
                expected: super::StaticArity::from(2_u32),
                actual: super::StaticArity::from(5_u32),
            },
        ),
        (
            super::CheckRefusal::FamilyArgumentClassifier {
                at: unit,
                position: super::ArgumentPosition::from(3_u32),
                synthesised: unit_type,
                expected: integer,
            },
            Refusal::FamilyArgumentClassifier {
                at: value_site,
                position: super::ArgumentPosition::from(3_u32),
                synthesised: unit_content(),
                expected: base(BaseType::Integer),
            },
        ),
        (
            super::CheckRefusal::StaticLambdaArgument { at: unit },
            Refusal::StaticLambdaArgument { at: value_site },
        ),
        (
            super::CheckRefusal::StaticClassifierExpected {
                at: unit_type,
                found: integer,
            },
            Refusal::StaticClassifierExpected {
                at: type_site,
                found: base(BaseType::Integer),
            },
        ),
    ];
    for (refusal, expected) in cases {
        assert_eq!(projection.refusal(refusal), expected);
    }
}

#[test]
fn session_refusals_project_their_endpoints_and_states()
{
    use alloc::collections::BTreeMap;
    use alloc::sync::Arc;

    use gandr_core_checker::session::ForkSide;
    use gandr_core_term::session::PayloadCount;
    use gandr_core_term::session::Protocol;
    use gandr_core_term::session::ProtocolState;
    use gandr_core_term::session::ProtocolSyntax;
    use gandr_core_term::session::SessionAction;
    use gandr_core_term::session::SessionType;

    use super::EndpointSite;
    use super::Linearity;
    let label = |text: &str| gandr_core_term::FieldLabel::from(String::from(text));
    let session = |syntax: Vec<ProtocolSyntax>| {
        let protocol = Protocol::new(
            syntax,
            ProtocolState::from(0_usize),
            PayloadCount::default(),
        )
        .expect("a protocol without payloads");
        SessionType::new(Arc::new(protocol), Arc::from([])).expect("no payloads")
    };
    let close = |arena: &mut CoreArena| {
        arena.computation_session(SessionAction::Close {
            endpoint: DeBruijnIndex::from(0_u32),
        })
    };
    let suspended = |arena: &mut CoreArena| {
        let unit = arena.value_type_unit();
        let returner = arena.comp_type_returner(unit);
        arena.value_type_thunk(returner)
    };

    // A child that never closes its `end`.
    let ended = session(vec![ProtocolSyntax::End]);
    let mut arena = CoreArena::new();
    let protocol = arena.value_type_session(ended.clone());
    let unit = arena.value_unit();
    let idle = arena.computation_return(unit);
    let closed = close(&mut arena);
    let fork = arena.computation_session(SessionAction::Fork {
        protocol,
        child: idle,
        parent: closed,
    });
    let body = arena.value_thunk(fork);
    let signature = suspended(&mut arena);
    let (_, typing) = judged(
        arena,
        Maybe::Present(signature),
        Maybe::Present(body),
        CheckBudget::DEFAULT,
    );
    let Typing::Refused(Refusal::Linearity {
        at,
        defect:
            Linearity::Residue {
                endpoint: EndpointSite { fork, side },
                ref state,
            },
    }) = typing
    else {
        panic!("a residue, not {typing:?}");
    };
    assert!(
        matches!(at, Site::Node(_)) && at == fork,
        "the residue stands at the fork that bound the endpoint"
    );
    assert_eq!(side, ForkSide::Child, "the child left it open");
    assert_eq!(
        state.debruijn(),
        Ok(vec![ContentNode::SessionType(
            ended
                .try_relocate(|_| Ok::<NodeIndex, core::convert::Infallible>(NodeIndex::default()))
                .unwrap_or_else(|never| match never {})
        )]),
        "the state is its own type table"
    );

    // An offer whose arms leave the endpoint closed and open.
    let choice = session(vec![
        ProtocolSyntax::Offer(BTreeMap::from([
            (label("a"), ProtocolState::from(1_usize)),
            (label("b"), ProtocolState::from(2_usize)),
        ])),
        ProtocolSyntax::End,
        ProtocolSyntax::End,
    ]);
    let mut arena = CoreArena::new();
    let protocol = arena.value_type_session(choice);
    let unit = arena.value_unit();
    let left_open = arena.computation_return(unit);
    let closed = close(&mut arena);
    let offer = arena.computation_session(SessionAction::Offer {
        endpoint: DeBruijnIndex::from(0_u32),
        arms: BTreeMap::from([(label("a"), closed), (label("b"), left_open)]),
    });
    let parent_closed = close(&mut arena);
    let select = arena.computation_session(SessionAction::Select {
        endpoint: DeBruijnIndex::from(0_u32),
        label: label("a"),
    });
    let parent = arena.computation_bind(select, parent_closed);
    let fork = arena.computation_session(SessionAction::Fork {
        protocol,
        child: offer,
        parent,
    });
    let body = arena.value_thunk(fork);
    let signature = suspended(&mut arena);
    let (_, typing) = judged(
        arena,
        Maybe::Present(signature),
        Maybe::Present(body),
        CheckBudget::DEFAULT,
    );
    let Typing::Refused(Refusal::Linearity {
        at,
        defect:
            Linearity::ArmsDisagree {
                endpoint: EndpointSite { side, .. },
                first,
                other,
            },
    }) = typing
    else {
        panic!("an arm disagreement, not {typing:?}");
    };
    assert_eq!(side, ForkSide::Child, "the offer acts on the child's end");
    assert!(
        matches!((first, other), (Site::Node(_), Site::Node(_))) && first != other,
        "both arms are item sites, distinct"
    );
    assert_eq!(at, other, "the refusal stands at the disagreeing arm");
}

#[test]
fn a_located_refusal_projects_its_worlds_and_types()
{
    use gandr_core_checker::AbstractType;
    use gandr_core_checker::ComponentOrdinal;
    use gandr_core_checker::SealSite;
    use gandr_core_checker::SealingSite;
    use gandr_core_checker::worlds::Mobility;
    use gandr_core_checker::worlds::Predicate;
    use gandr_core_term::Sort;
    use gandr_core_term::world::World;
    use gandr_core_term::world::WorldForm;
    use gandr_kernel_strata::Level;
    use gandr_kernel_term::GroundSort;
    use gandr_kernel_term::SealExtent;

    use super::Located;
    use super::Place;
    use crate::content::ArenaNode;
    // `world seat ;`, a declaration migrating to it with no capability, and
    // an abstract type marked mobile over a thunk.
    let mut arena = CoreArena::new();
    let string = arena.value_type_base(BaseType::String);
    let returns = arena.comp_type_returner(string);
    let thunk = arena.value_type_thunk(returns);
    let small = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let report = arena.value_literal(Literal::Text(StringLiteral::new(String::from("report"))));
    let returned = arena.computation_return(report);
    let migration = arena.computation_world(WorldForm::Migrate {
        world: World::Declared(ConstantIndex::from(0_usize)),
        body: returned,
    });
    let body = arena.value_thunk(migration);
    let promised = AbstractType::new(
        small,
        thunk,
        SealExtent::from(0_usize),
        SealSite::new(SealingSite::from(0_usize), ComponentOrdinal::from(0_usize)),
    )
    .marked(Mobility::Mobile);
    let mut program = Program::new(arena, vec![
        Item::new(
            ItemKey::from("seat"),
            Declaration::world(ConstantIndex::from(0_usize), OriginToken::from(0_usize)),
        ),
        Item::new(
            ItemKey::from("migrating"),
            Declaration::new(
                ConstantIndex::from(1_usize),
                Maybe::Present(thunk),
                Maybe::Present(body),
                OriginToken::from(1_usize),
            ),
        ),
        Item::new(
            ItemKey::from("promised"),
            Declaration::abstract_type(
                ConstantIndex::from(2_usize),
                promised,
                OriginToken::from(2_usize),
            ),
        ),
    ])
    .expect("three items ascend");
    let declarations = program.declarations();
    let encoded: alloc::vec::Vec<_> = (0_usize .. declarations.len())
        .map(|ordinal| {
            encode_item(
                program.arena(),
                program.layout(),
                ItemOrdinal::from(ordinal),
            )
        })
        .collect();
    let (arena, layout) = program.parts_mut();
    let mut context = CheckingContext::new(arena, CheckBudget::DEFAULT);
    let typings: alloc::vec::Vec<Typing> = declarations
        .iter()
        .zip(&encoded)
        .map(|(declaration, encoded)| {
            let verdict = check_declaration_supported(&mut context, declaration).verdict();
            Projection {
                arena: context.arena(),
                layout,
                sites: &encoded.sites,
                types: &crate::content::TypeMemo::default(),
            }
            .typing(&verdict)
        })
        .collect();
    let seat = layout.resolve(ConstantIndex::from(0_usize));
    let migrated = match encoded[1].sites.of(ArenaNode::Computation(migration)) {
        Maybe::Present(index) => Site::Node(index),
        Maybe::Absent(_) => Site::Unreached,
    };
    let representation = match encoded[2].sites.of(ArenaNode::ValueType(thunk)) {
        Maybe::Present(index) => Site::Node(index),
        Maybe::Absent(_) => Site::Unreached,
    };
    assert_eq!(
        typings,
        [
            Typing::Data,
            Typing::Refused(Refusal::Located {
                at: migrated,
                defect: Located::CapabilityMissing {
                    world: Place::Declared(seat),
                },
            }),
            Typing::Refused(Refusal::Located {
                at: representation,
                defect: Located::MarkUnfounded {
                    atom: layout.resolve(ConstantIndex::from(2_usize)),
                    former: Projection {
                        arena: context.arena(),
                        layout,
                        sites: &encoded[2].sites,
                        types: &crate::content::TypeMemo::default(),
                    }
                    .value_type(thunk),
                    predicate: Predicate::Mobile,
                },
            }),
        ],
        "the world projects to its declaration's reference, the atom to its own, and the former to its own type table"
    );
    assert!(
        matches!(migrated, Site::Node(_)) && matches!(representation, Site::Node(_)),
        "both refusals stand at nodes their items reached"
    );
}
