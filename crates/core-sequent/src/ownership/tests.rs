use alloc::boxed::Box;
use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use gandr_theory_cell_complexes::Polarity;

use super::*;
use crate::boundary::ProducerArity;
use crate::il::ConstructorTag;
use crate::il::ConsumerId;
use crate::il::CopatternArm;
use crate::il::CovariableIndex;
use crate::il::PatternArm;

/// The variable `index` of `zone`.
///
/// # Specification
/// trivial.
fn variable(
    arena: &mut CommandArena,
    zone: Zone,
    index: DeBruijnIndex,
) -> ProducerId
{
    arena
        .mint_producer(ProducerNode::Variable { zone, index })
        .expect("a leaf")
}

/// The innermost binder, `x0`.
///
/// # Specification
/// trivial.
fn x0() -> DeBruijnIndex
{
    DeBruijnIndex::from(0_u32)
}

/// The binder one out, `x1`.
///
/// # Specification
/// trivial.
fn x1() -> DeBruijnIndex
{
    DeBruijnIndex::from(1_u32)
}

/// The binder two out, `x2`.
///
/// # Specification
/// trivial.
fn x2() -> DeBruijnIndex
{
    DeBruijnIndex::from(2_u32)
}

/// The tuple of `fields`.
///
/// # Specification
/// trivial.
fn tuple(
    arena: &mut CommandArena,
    fields: &[ProducerId],
) -> ProducerId
{
    arena
        .mint_producer(ProducerNode::Constructor {
            tag: ConstructorTag::Tuple(ProducerArity::from(fields.len())),
            producers: Box::from(fields),
            consumers: Box::from([]),
        })
        .expect("the fields resolve")
}

/// The innermost covariable, `α0`.
///
/// # Specification
/// trivial.
fn alpha0(arena: &mut CommandArena) -> ConsumerId
{
    arena
        .mint_consumer(ConsumerNode::Covariable(CovariableIndex::from(0_u32)))
        .expect("a leaf")
}

/// `⟨value |+ consumer⟩`.
///
/// # Specification
/// trivial.
fn cut(
    arena: &mut CommandArena,
    value: ProducerId,
    consumer: ConsumerId,
) -> CommandId
{
    arena
        .mint_cut(Polarity::Positive, value, consumer)
        .expect("the children resolve")
}

/// The reading of `node`.
///
/// # Specification
/// trivial.
fn entry(
    ownership: &Ownership,
    node: NodeAddress,
) -> Entry<'_>
{
    ownership.entry(node).expect("the node was reached")
}

/// The ownership of `roots`, read over their walk.
///
/// # Specification
/// trivial.
fn read(
    arena: &CommandArena,
    roots: &[NodeAddress],
) -> Ownership
{
    let mut reached = Vec::new();
    reach(arena, roots, &mut BTreeSet::new(), &mut reached).expect("held");
    Ownership::of(arena, roots, &reached).expect("held")
}

/// A tuple naming `x0` twice and `x1` once duplicates `x0` once and `x1`
/// never; the cut that sends it consumes each once.
#[test]
fn a_name_two_children_use_is_duplicated_once()
{
    let mut arena = CommandArena::new();
    let twice = variable(&mut arena, Zone::Intuitionistic, x0());
    let once = variable(&mut arena, Zone::Intuitionistic, x1());
    let pair = tuple(&mut arena, &[twice, twice, once]);
    let top = arena.mint_consumer(ConsumerNode::Top).expect("a leaf");
    let root = cut(&mut arena, pair, top);

    let ownership = read(&arena, &[NodeAddress::Command(root)]);

    assert_eq!(
        entry(&ownership, NodeAddress::Producer(pair)).dups,
        [x0()].as_slice()
    );
    assert!(
        entry(&ownership, NodeAddress::Command(root))
            .dups
            .is_empty()
    );
}

/// A `μ̃` whose body ignores its bound name drops it on entry; one whose
/// body names it drops nothing.
#[test]
fn an_ignored_binder_is_dropped_on_entry()
{
    let mut arena = CommandArena::new();
    let top = arena.mint_consumer(ConsumerNode::Top).expect("a leaf");
    let unit = tuple(&mut arena, &[]);
    let bound = variable(&mut arena, Zone::Intuitionistic, x0());
    for (value, dropped) in [(unit, Vec::from([x0()])), (bound, Vec::new())] {
        let body = cut(&mut arena, value, top);
        let binder = arena
            .mint_consumer(ConsumerNode::MuTilde { body })
            .expect("the body resolves");
        let root = cut(&mut arena, unit, binder);

        let ownership = read(&arena, &[NodeAddress::Command(root)]);

        assert_eq!(
            entry(&ownership, NodeAddress::Command(body)).drops,
            dropped.as_slice()
        );
    }
}

/// Of two arms over `x0`, the one naming it drops nothing it received, and
/// the one ignoring it drops it beside the fields it binds and ignores; the
/// match consumes `x0` once.
#[test]
fn an_arm_drops_what_its_sibling_uses()
{
    let mut arena = CommandArena::new();
    let top = arena.mint_consumer(ConsumerNode::Top).expect("a leaf");
    let unit = tuple(&mut arena, &[]);
    let outer = variable(&mut arena, Zone::Intuitionistic, x0());
    let names = cut(&mut arena, outer, top);
    let ignores = cut(&mut arena, unit, top);
    let matched = arena
        .mint_consumer(ConsumerNode::Case {
            arms: Box::from([
                PatternArm {
                    constructor: ConstructorTag::ListNil,
                    body: names,
                },
                PatternArm {
                    constructor: ConstructorTag::ListCons,
                    body: ignores,
                },
            ]),
        })
        .expect("the arms resolve");
    let scrutinee = variable(&mut arena, Zone::Intuitionistic, x1());
    let root = cut(&mut arena, scrutinee, matched);

    let ownership = read(&arena, &[NodeAddress::Command(root)]);

    let reading = entry(&ownership, NodeAddress::Consumer(matched));
    assert!(reading.dups.is_empty());
    let drops = [names, ignores].map(|arm| entry(&ownership, NodeAddress::Command(arm)).drops);
    let none: &[DeBruijnIndex] = &[];
    assert_eq!(drops, [none, [x0(), x1(), x2()].as_slice()]);
}

/// A thunk that is a root may be forced many times: its body duplicates the
/// capture it names on entry. The same thunk cut against a force runs once,
/// and its body owns the capture.
#[test]
fn a_kept_body_duplicates_its_captures_on_entry()
{
    for forced in [false, true] {
        let mut arena = CommandArena::new();
        let capture = variable(&mut arena, Zone::Intuitionistic, x0());
        let returned = alpha0(&mut arena);
        let body = cut(&mut arena, capture, returned);
        let thunk = arena
            .mint_producer(ProducerNode::Thunk { body })
            .expect("the body resolves");
        let root = if forced {
            let top = arena.mint_consumer(ConsumerNode::Top).expect("a leaf");
            let force = arena
                .mint_consumer(ConsumerNode::Destructor {
                    tag: DestructorTag::Force,
                    producers: Box::from([]),
                    consumers: Box::from([top]),
                })
                .expect("the frame resolves");
            NodeAddress::Command(
                arena
                    .mint_cut(Polarity::Negative, thunk, force)
                    .expect("the children resolve"),
            )
        }
        else {
            NodeAddress::Producer(thunk)
        };

        let ownership = read(&arena, &[root]);

        let (runs, entered) = if forced {
            (Runs::Once, Vec::new())
        }
        else {
            (Runs::Many, Vec::from([x0()]))
        };
        assert_eq!(ownership.runs(thunk), runs);
        assert_eq!(
            entry(&ownership, NodeAddress::Command(body)).entered,
            entered.as_slice()
        );
    }
}

/// A reified stack's bind frame owns its capture as any child does: the stack
/// is the keeper, and each resumption copies the frame's window out of it
/// with a reference of its own, so the body duplicates nothing on entry. An
/// applied argument and a projection mark nothing either.
#[test]
fn a_reified_bind_body_owns_its_captures()
{
    let mut arena = CommandArena::new();
    let argument = tuple(&mut arena, &[]);
    let capture = variable(&mut arena, Zone::Intuitionistic, x1());
    let returned = alpha0(&mut arena);
    let body = cut(&mut arena, capture, returned);
    let stack = arena
        .mint_producer(ProducerNode::Reify(alloc::sync::Arc::from([
            gandr_core_term::control::StackFrame::Apply(argument),
            gandr_core_term::control::StackFrame::Project(gandr_kernel_term::Component::from(
                1_usize,
            )),
            gandr_core_term::control::StackFrame::Bind(body),
        ])))
        .expect("the frames resolve");

    let ownership = read(&arena, &[NodeAddress::Producer(stack)]);

    assert_eq!(
        entry(&ownership, NodeAddress::Command(body)).entered,
        [].as_slice(),
        "the resumption's copy holds the reference the body consumes"
    );
}

/// A match on the unit that builds the unit pairs nothing: a nullary head
/// has no cell to write into.
#[test]
fn a_nullary_match_reuses_nothing()
{
    let mut arena = CommandArena::new();
    let top = arena.mint_consumer(ConsumerNode::Top).expect("a leaf");
    let unit = tuple(&mut arena, &[]);
    let body = cut(&mut arena, unit, top);
    let matched = arena
        .mint_consumer(ConsumerNode::Case {
            arms: Box::from([PatternArm {
                constructor: ConstructorTag::Tuple(ProducerArity::ZERO),
                body,
            }]),
        })
        .expect("the arm resolves");
    let scrutinee = variable(&mut arena, Zone::Intuitionistic, x0());
    let root = cut(&mut arena, scrutinee, matched);

    let ownership = read(&arena, &[NodeAddress::Command(root)]);

    assert!(ownership.reuses().is_empty());
}

/// A linear name two children read is never duplicated: only `Γ` is counted.
#[test]
fn a_linear_name_is_never_counted()
{
    let mut arena = CommandArena::new();
    let held = variable(&mut arena, Zone::Linear, x0());
    let pair = tuple(&mut arena, &[held, held]);
    let top = arena.mint_consumer(ConsumerNode::Top).expect("a leaf");
    let root = cut(&mut arena, pair, top);

    let ownership = read(&arena, &[NodeAddress::Command(root)]);

    assert!(
        entry(&ownership, NodeAddress::Producer(pair))
            .dups
            .is_empty()
    );
}

/// The point step, as lowered: `⟨x0 |+ datacase({force(α) ⇒ ⟨cocase
/// {apply(x; α) ⇒ ⟨cocase {apply(x; α) ⇒ ⟨P(x0, x1) |+ α0⟩} |− α0⟩} |−
/// α0⟩}; ★)⟩`. The branch and its curried objects run once, and the branch
/// rebuilds a constructor of the scrutinee's two fields where the scrutinee
/// is dead, so the two pair. A branch that names its scrutinee, and a
/// constructor inside a body that may run many times, pair nothing.
#[test]
fn a_branch_rebuilding_its_scrutinee_reuses_the_cell()
{
    for case in ["dead", "named", "kept"] {
        let mut arena = CommandArena::new();
        let top = arena.mint_consumer(ConsumerNode::Top).expect("a leaf");
        let returned = alpha0(&mut arena);
        let second = variable(&mut arena, Zone::Intuitionistic, x0());
        let first = match case {
            // reason: under the branch's two field binders the scrutinee is
            // `x2`.
            "named" => variable(&mut arena, Zone::Intuitionistic, x2()),
            _ => variable(&mut arena, Zone::Intuitionistic, x1()),
        };
        let point = arena
            .mint_producer(ProducerNode::Constructor {
                tag: ConstructorTag::Data {
                    tag: gandr_kernel_term::ConstructorTag::from(0_usize),
                    arity: ProducerArity::TWO,
                    family: None,
                },
                producers: Box::from([second, first]),
                consumers: Box::from([]),
            })
            .expect("the fields resolve");
        let mut body = cut(&mut arena, point, returned);
        if case == "kept" {
            let kept = arena
                .mint_producer(ProducerNode::Thunk { body })
                .expect("the body resolves");
            body = cut(&mut arena, kept, returned);
        }
        for _field in 0_u8 .. 2_u8 {
            let object = arena
                .mint_producer(ProducerNode::Cocase {
                    arms: Box::from([CopatternArm {
                        destructor: DestructorTag::Apply,
                        body,
                    }]),
                })
                .expect("the arm resolves");
            body = arena
                .mint_cut(Polarity::Negative, object, returned)
                .expect("the children resolve");
        }
        let branch = arena
            .mint_producer(ProducerNode::Thunk { body })
            .expect("the body resolves");
        let matched = arena
            .mint_consumer(ConsumerNode::DataCase {
                branches: Box::from([branch]),
                then: top,
            })
            .expect("the branch resolves");
        let scrutinee = variable(&mut arena, Zone::Intuitionistic, x0());
        let root = cut(&mut arena, scrutinee, matched);

        let ownership = read(&arena, &[NodeAddress::Command(root)]);

        assert_eq!(ownership.runs(branch), Runs::Once, "{case}");
        let expected = match case {
            "dead" => Vec::from([Reuse {
                matched: root,
                branch: NodeCount::from(0_usize),
                built: point,
            }]),
            _ => Vec::new(),
        };
        assert_eq!(ownership.reuses(), expected.as_slice(), "{case}");
    }
}
