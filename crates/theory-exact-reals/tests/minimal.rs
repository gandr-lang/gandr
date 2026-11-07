//! Witnesses of the plan graph and its minimal form: the empty core of every
//! generated plan, the core of a recursive system, the key of a respelled
//! plan, the key against an independent unfolding of two plans, the classes
//! against a brute-force bisimulation of generated recursive systems, and
//! the builder's refusals by name.

use gandr_theory_discrete_morse::Faults;
use gandr_theory_exact_reals::Cut;
use gandr_theory_exact_reals::Domain;
use gandr_theory_exact_reals::DomainId;
use gandr_theory_exact_reals::GraphBuilder;
use gandr_theory_exact_reals::GraphError;
use gandr_theory_exact_reals::GraphNode;
use gandr_theory_exact_reals::Label;
use gandr_theory_exact_reals::LabelBytes;
use gandr_theory_exact_reals::Node;
use gandr_theory_exact_reals::Open;
use gandr_theory_exact_reals::OpenId;
use gandr_theory_exact_reals::Operands;
use gandr_theory_exact_reals::Plan;
use gandr_theory_exact_reals::PlanBuilder;
use gandr_theory_exact_reals::PlanGraph;
use gandr_theory_exact_reals::Quantifier;
use gandr_theory_exact_reals::Real;
use gandr_theory_exact_reals::RealId;
use gandr_theory_exact_reals::Root;
use proptest::prelude::*;

use crate::plan::Step;
use crate::plan::build;
use crate::plan::step;

/// A node of a plan rebuilt in another builder, by its sort.
#[derive(Clone, Copy, Debug)]
enum Fresh
{
    Real(RealId),
    Open(OpenId),
    Domain(DomainId),
}

/// Whether a rebuilt sum, product, meet or join keeps its operands in order.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Turn
{
    Keep,
    Swap,
}

/// `plan` built again node by node, each sum, product, meet and join with
/// its operands in the order that `choose` gives.
///
/// # Specification
/// trivial.
fn rebuild<Choose>(
    plan: &Plan,
    mut choose: Choose,
) -> Plan
where
    Choose: FnMut(&PlanBuilder, Root, Root) -> Turn,
{
    let mut builder = PlanBuilder::new();
    let mut fresh: Vec<Option<Fresh>> = vec![None; usize::from(plan.node_count())];
    let real = |fresh: &[Option<Fresh>], id: RealId| match fresh[usize::from(id.node())] {
        Some(Fresh::Real(new)) => new,
        ref other => panic!("a real child, not {other:?}"),
    };
    let open = |fresh: &[Option<Fresh>], id: OpenId| match fresh[usize::from(id.node())] {
        Some(Fresh::Open(new)) => new,
        ref other => panic!("an open child, not {other:?}"),
    };
    let domain = |fresh: &[Option<Fresh>], id: DomainId| match fresh[usize::from(id.node())] {
        Some(Fresh::Domain(new)) => new,
        ref other => panic!("a domain child, not {other:?}"),
    };
    for (id, node) in plan.nodes() {
        let made = match *node {
            Node::Real(ref form) => {
                let form = match *form {
                    Real::Bound(index) => Real::Bound(index),
                    Real::Constant(ref value) => Real::Constant(value.clone()),
                    Real::Pi => Real::Pi,
                    Real::Add(left, right) | Real::Mul(left, right) => {
                        let (mut left, mut right) = (real(&fresh, left), real(&fresh, right));
                        if choose(&builder, Root::Real(left), Root::Real(right)) == Turn::Swap {
                            core::mem::swap(&mut left, &mut right);
                        }
                        if matches!(*form, Real::Add(..)) {
                            Real::Add(left, right)
                        }
                        else {
                            Real::Mul(left, right)
                        }
                    },
                    Real::Sub(left, right) => Real::Sub(real(&fresh, left), real(&fresh, right)),
                    Real::Div {
                        numerator,
                        denominator,
                        nonzero,
                    } => Real::Div {
                        numerator: real(&fresh, numerator),
                        denominator: real(&fresh, denominator),
                        nonzero,
                    },
                    Real::Power(base, power) => Real::Power(real(&fresh, base), power),
                    Real::Cut(ref cut) => Real::Cut(Cut {
                        hull: cut.hull.clone(),
                        lower: open(&fresh, cut.lower),
                        upper: open(&fresh, cut.upper),
                        laws: cut.laws,
                    }),
                    Real::Cos(argument) => Real::Cos(real(&fresh, argument)),
                    Real::Sin(argument) => Real::Sin(real(&fresh, argument)),
                    Real::Arg(x, y) => Real::Arg(real(&fresh, x), real(&fresh, y)),
                };
                Fresh::Real(builder.real(form).unwrap())
            },
            Node::Open(ref form) => {
                let form = match *form {
                    Open::Top => Open::Top,
                    Open::Bottom => Open::Bottom,
                    Open::Less(left, right) => Open::Less(real(&fresh, left), real(&fresh, right)),
                    Open::LowerCut(cut, point) => {
                        Open::LowerCut(real(&fresh, cut), real(&fresh, point))
                    },
                    Open::UpperCut(cut, point) => {
                        Open::UpperCut(real(&fresh, cut), real(&fresh, point))
                    },
                    Open::Meet(left, right) | Open::Join(left, right) => {
                        let (mut left, mut right) = (open(&fresh, left), open(&fresh, right));
                        if choose(&builder, Root::Open(left), Root::Open(right)) == Turn::Swap {
                            core::mem::swap(&mut left, &mut right);
                        }
                        if matches!(*form, Open::Meet(..)) {
                            Open::Meet(left, right)
                        }
                        else {
                            Open::Join(left, right)
                        }
                    },
                    Open::Exists(quantifier) => Open::Exists(Quantifier {
                        domain: domain(&fresh, quantifier.domain),
                        body: open(&fresh, quantifier.body),
                        ..quantifier
                    }),
                    Open::Forall(quantifier) => Open::Forall(Quantifier {
                        domain: domain(&fresh, quantifier.domain),
                        body: open(&fresh, quantifier.body),
                        ..quantifier
                    }),
                };
                Fresh::Open(builder.open(form).unwrap())
            },
            Node::Domain(ref form) => {
                let form = match *form {
                    Domain::Interval {
                        ref hull,
                        overt,
                        compact,
                    } => Domain::Interval {
                        hull: hull.clone(),
                        overt,
                        compact,
                    },
                    Domain::Product {
                        left,
                        right,
                        evidence,
                    } => Domain::Product {
                        left: domain(&fresh, left),
                        right: domain(&fresh, right),
                        evidence,
                    },
                    Domain::Subdomain {
                        parent,
                        classifier,
                        evidence,
                    } => Domain::Subdomain {
                        parent: domain(&fresh, parent),
                        classifier: open(&fresh, classifier),
                        evidence,
                    },
                };
                Fresh::Domain(builder.domain(form).unwrap())
            },
        };
        fresh[usize::from(id)] = Some(made);
    }
    let root = match plan.root() {
        Root::Real(id) => Root::Real(real(&fresh, id)),
        Root::Open(id) => Root::Open(open(&fresh, id)),
    };
    return builder.finish(root).unwrap();
}

/// The independent unfolding of `plan`: each sum, product, meet and join
/// with the operand of the smaller canonical bytes first, so two plans unfold
/// alike exactly when this gives one plan.
///
/// # Specification
/// trivial.
fn unfolded(plan: &Plan) -> Plan
{
    return rebuild(plan, |builder, left, right| {
        let bytes = |root: Root| builder.clone().finish(root).unwrap().encode();
        if bytes(left).as_ref() > bytes(right).as_ref() {
            Turn::Swap
        }
        else {
            Turn::Keep
        }
    });
}

/// The kinds of node of a generated recursive system.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Kind
{
    /// No operand.
    Leaf,
    /// Two operands in order.
    Pair,
    /// Two operands as a multiset.
    Sum,
    /// One operand: `2^-x`.
    Power,
}

/// The label of `kind`.
///
/// # Specification
/// trivial.
fn label(kind: Kind) -> Label
{
    let (bytes, operands): (&[u8], Operands) = match kind {
        Kind::Leaf => (b"leaf", Operands::Ordered),
        Kind::Pair => (b"pair", Operands::Ordered),
        Kind::Sum => (b"sum", Operands::Unordered),
        Kind::Power => (b"two to the minus", Operands::Ordered),
    };
    return Label::new(LabelBytes::from(bytes), operands);
}

/// One node of a generated recursive system: its kind and the draws of its
/// operands, each taken modulo the count of the nodes.
#[derive(Clone, Copy, Debug)]
struct Draft
{
    kind: Kind,
    left: usize,
    right: usize,
}

/// The strategy of one node.
///
/// # Specification
/// trivial.
fn draft() -> impl Strategy<Value = Draft>
{
    let kind = prop_oneof![
        Just(Kind::Leaf),
        Just(Kind::Pair),
        Just(Kind::Sum),
        Just(Kind::Power)
    ];
    return (kind, 0_usize .. 64, 0_usize .. 64).prop_map(|(kind, left, right)| Draft {
        kind,
        left,
        right,
    });
}

/// The operands of one node of a generated system.
#[derive(Clone, Copy, Debug)]
enum Taken
{
    None,
    One(Place),
    Two(Place, Place),
}

/// The operands of the node at `index` of `drafts`.
///
/// # Specification
/// trivial.
fn taken(
    drafts: &[Draft],
    index: Place,
) -> Taken
{
    let count = drafts.len();
    let node = drafts[index.0];
    let left = Place(node.left.checked_rem(count).unwrap());
    let right = Place(node.right.checked_rem(count).unwrap());
    return match node.kind {
        Kind::Leaf => Taken::None,
        Kind::Power => Taken::One(left),
        Kind::Pair | Kind::Sum => Taken::Two(left, right),
    };
}

/// A place in a list of drafts.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Place(usize);

/// The graph of `drafts`, rooted at the first.
///
/// # Specification
/// trivial.
fn system(drafts: &[Draft]) -> PlanGraph
{
    let mut builder = GraphBuilder::new();
    let nodes: Vec<GraphNode> = drafts.iter().map(|_| builder.reserve().unwrap()).collect();
    let mut named: Vec<GraphNode> = Vec::with_capacity(2);
    for (index, draft) in drafts.iter().enumerate() {
        named.clear();
        match taken(drafts, Place(index)) {
            Taken::None => {},
            Taken::One(only) => named.push(nodes[only.0]),
            Taken::Two(left, right) => named.extend([nodes[left.0], nodes[right.0]]),
        }
        builder
            .define(nodes[index], label(draft.kind), &named)
            .unwrap();
    }
    return builder.finish(nodes[0]).unwrap();
}

/// The bisimulation of `drafts` by brute force: the greatest fixed point
/// from the relation of equal kinds, a pair dropped while its operands fail
/// to relate in order, or as a multiset for a sum.
struct Relation
{
    count: usize,
    related: Vec<bool>,
}

impl Relation
{
    /// The relation of `drafts`.
    ///
    /// # Specification
    /// trivial.
    fn of(drafts: &[Draft]) -> Self
    {
        let count = drafts.len();
        let at = |one: Place, two: Place| {
            one.0
                .checked_mul(count)
                .unwrap()
                .checked_add(two.0)
                .unwrap()
        };
        let mut related = vec![false; count.checked_mul(count).unwrap()];
        for one in 0 .. count {
            for two in 0 .. count {
                related[at(Place(one), Place(two))] = drafts[one].kind == drafts[two].kind;
            }
        }
        loop {
            let mut changed = false;
            for one in 0 .. count {
                for two in 0 .. count {
                    if !related[at(Place(one), Place(two))] {
                        continue;
                    }
                    let holds = |left: Place, right: Place| related[at(left, right)];
                    let kept = match (taken(drafts, Place(one)), taken(drafts, Place(two))) {
                        (Taken::Two(a, b), Taken::Two(c, d)) => {
                            (holds(a, c) && holds(b, d))
                                || (drafts[one].kind == Kind::Sum && holds(a, d) && holds(b, c))
                        },
                        (Taken::One(a), Taken::One(c)) => holds(a, c),
                        (Taken::None, Taken::None) => true,
                        (
                            Taken::None | Taken::One(_) | Taken::Two(..),
                            Taken::None | Taken::One(_) | Taken::Two(..),
                        ) => false,
                    };
                    if !kept {
                        related[at(Place(one), Place(two))] = false;
                        changed = true;
                    }
                }
            }
            if !changed {
                return Self { count, related };
            }
        }
    }
}

/// `drafts` written twice, each operand of each copy pointing into the copy
/// that `picks` chooses. Each node is bisimilar to its original.
///
/// # Specification
/// trivial.
fn doubled(
    drafts: &[Draft],
    picks: &[Turn],
) -> Vec<Draft>
{
    let count = drafts.len();
    let mut pick = picks.iter().cycle();
    let mut shift = |place: usize| {
        let base = place.checked_rem(count).unwrap();
        return match pick.next() {
            Some(&Turn::Swap) => base.checked_add(count).unwrap(),
            Some(&Turn::Keep) | None => base,
        };
    };
    let mut twice = Vec::with_capacity(count.checked_mul(2).unwrap());
    for _copy in 0_u8 .. 2_u8 {
        for draft in drafts {
            twice.push(Draft {
                kind: draft.kind,
                left: shift(draft.left),
                right: shift(draft.right),
            });
        }
    }
    return twice;
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    /// Every generated plan reads as a graph whose matching leaves no node
    /// with operands critical, and the check finds no fault.
    #[test]
    fn a_plan_has_an_empty_core(steps in prop::collection::vec(step(), 0 .. 48))
    {
        let (builder, root) = build(&steps);
        let plan = builder.finish(root).unwrap();
        let core = PlanGraph::from(&plan).core().unwrap();
        prop_assert!(core.nodes().is_empty(), "{:?}", core.nodes());
        prop_assert_eq!(core.faults(), Faults::default());
    }

    /// A plan whose sums, products, meets and joins take their operands in
    /// other orders keeps its key, and its classes count the nodes of its
    /// independent unfolding.
    #[test]
    fn a_respelled_plan_keeps_its_key(
        steps in prop::collection::vec(step(), 0 .. 48),
        flips in prop::collection::vec(prop_oneof![Just(Turn::Keep), Just(Turn::Swap)], 1 .. 16),
    )
    {
        let (builder, root) = build(&steps);
        let plan = builder.finish(root).unwrap();
        let mut flip = flips.iter().cycle();
        let respelled = rebuild(&plan, |_, _, _| *flip.next().unwrap());
        let form = PlanGraph::from(&plan).minimal();
        prop_assert_eq!(form.key(), PlanGraph::from(&respelled).minimal().key());
        let unfolding = unfolded(&plan);
        prop_assert_eq!(&unfolding, &unfolded(&respelled));
        prop_assert_eq!(usize::from(form.class_count()), usize::from(unfolding.node_count()));
    }

    /// Two plans share a key exactly when their independent unfoldings are
    /// one plan.
    #[test]
    fn two_plans_share_a_key_exactly_when_they_unfold_alike(
        first in prop::collection::vec(step(), 0 .. 6),
        second in prop::collection::vec(step(), 0 .. 6),
        respell in prop_oneof![Just(Turn::Keep), Just(Turn::Swap)],
    )
    {
        let finish = |steps: &[Step]| {
            let (builder, root) = build(steps);
            builder.finish(root).unwrap()
        };
        let one = finish(&first);
        let two = if respell == Turn::Swap {
            rebuild(&one, |_, _, _| Turn::Swap)
        }
        else {
            finish(&second)
        };
        let shared = PlanGraph::from(&one).minimal().key() == PlanGraph::from(&two).minimal().key();
        prop_assert_eq!(shared, unfolded(&one) == unfolded(&two));
    }

    /// On generated recursive systems, two nodes share a class exactly when
    /// the brute-force bisimulation relates them, and two systems share a key
    /// exactly when it relates their roots. A system written twice keeps its
    /// key.
    #[test]
    fn classes_are_the_bisimulation_of_a_recursive_system(
        first in prop::collection::vec(draft(), 1 .. 8),
        second in prop::collection::vec(draft(), 1 .. 8),
        picks in prop::collection::vec(prop_oneof![Just(Turn::Keep), Just(Turn::Swap)], 1 .. 16),
    )
    {
        let graph = system(&first);
        let form = graph.minimal();
        let relation = Relation::of(&first);
        for one in 0 .. first.len() {
            for two in 0 .. first.len() {
                let (left, right) = (
                    form.class(GraphNode::from(u32::try_from(one).unwrap())),
                    form.class(GraphNode::from(u32::try_from(two).unwrap())),
                );
                if let (Ok(left), Ok(right)) = (left, right) {
                    let related = relation.related[one.checked_mul(relation.count).unwrap().checked_add(two).unwrap()];
                    prop_assert_eq!(left == right, related, "nodes {} and {}", one, two);
                }
            }
        }
        prop_assert_eq!(form.key(), system(&doubled(&first, &picks)).minimal().key());
        // The two systems side by side: each draw reduced modulo its own
        // system, the second's places shifted past the first's.
        let placed = |drafts: &[Draft], offset: usize| {
            let count = drafts.len();
            let place = move |draw: usize| draw.checked_rem(count).unwrap().checked_add(offset).unwrap();
            return drafts
                .iter()
                .map(move |draft| Draft {
                    kind: draft.kind,
                    left: place(draft.left),
                    right: place(draft.right),
                })
                .collect::<Vec<Draft>>();
        };
        let offset = first.len();
        let mut both = placed(&first, 0);
        both.extend(placed(&second, offset));
        let union = Relation::of(&both);
        let roots = union.related[offset];
        prop_assert_eq!(form.key() == system(&second).minimal().key(), roots);
    }
}

#[test]
fn a_recursive_system_keeps_its_cycle_in_the_core()
{
    // `x = 2^-x`, a leaf, and `y = 1 + x` above them.
    let mut builder = GraphBuilder::new();
    let x = builder.reserve().unwrap();
    builder.define(x, label(Kind::Power), &[x]).unwrap();
    let one = builder.node(label(Kind::Leaf), &[]).unwrap();
    let y = builder.node(label(Kind::Sum), &[one, x]).unwrap();
    let graph = builder.finish(y).unwrap();
    let core = graph.core().unwrap();
    assert_eq!(core.nodes(), &[x, y]);
    assert_eq!(core.faults(), Faults::default());
    // `a = 2^-b` and `b = 2^-a` unfold as `x` does: one class, one key.
    let mut builder = GraphBuilder::new();
    let a = builder.reserve().unwrap();
    let b = builder.node(label(Kind::Power), &[a]).unwrap();
    builder.define(a, label(Kind::Power), &[b]).unwrap();
    let cycle = builder.finish(a).unwrap();
    let mut builder = GraphBuilder::new();
    let x = builder.reserve().unwrap();
    builder.define(x, label(Kind::Power), &[x]).unwrap();
    let omega = builder.finish(x).unwrap();
    assert_eq!(cycle.minimal().key(), omega.minimal().key());
    assert_eq!(usize::from(cycle.minimal().class_count()), 1);
    assert_eq!(cycle.core().unwrap().nodes(), &[a, b]);
    // The same nodes with no cycle: `a = 2^-b` over a leaf `b`.
    let mut builder = GraphBuilder::new();
    let leaf = builder.node(label(Kind::Leaf), &[]).unwrap();
    let a = builder.node(label(Kind::Power), &[leaf]).unwrap();
    assert!(
        builder
            .finish(a)
            .unwrap()
            .core()
            .unwrap()
            .nodes()
            .is_empty()
    );
}

#[test]
fn the_builder_refuses_by_name()
{
    let mut builder = GraphBuilder::new();
    let x = builder.reserve().unwrap();
    assert_eq!(
        builder.define(GraphNode::from(5_u32), label(Kind::Leaf), &[]),
        Err(GraphError::UnknownNode)
    );
    let wide = vec![x; 65];
    assert_eq!(
        builder.define(x, label(Kind::Pair), &wide),
        Err(GraphError::Wide)
    );
    builder.define(x, label(Kind::Sum), &wide).unwrap();
    assert_eq!(
        builder.define(x, label(Kind::Leaf), &[]),
        Err(GraphError::Redefined)
    );
    let mut undefined = builder.clone();
    let _left = undefined.reserve().unwrap();
    assert_eq!(undefined.finish(x), Err(GraphError::Undefined));
    let mut foreign = builder.clone();
    let _named = foreign
        .node(label(Kind::Power), &[GraphNode::from(99_u32)])
        .unwrap();
    assert_eq!(foreign.finish(x), Err(GraphError::UnknownNode));
    assert_eq!(
        builder.clone().finish(GraphNode::from(1_u32)),
        Err(GraphError::UnknownNode)
    );
    let apart = builder.node(label(Kind::Leaf), &[]).unwrap();
    let form = builder.finish(x).unwrap().minimal();
    assert_eq!(form.class(apart), Err(GraphError::Unreached));
    assert_eq!(
        form.class(GraphNode::from(2_u32)),
        Err(GraphError::UnknownNode)
    );
}
