//! The modular decomposition read through the public surface: named shapes,
//! a generated order read back pair by pair, and two dialogue webs.

use gandr_theory_cell_complexes::CellStore;
use gandr_theory_cell_complexes_tools::Toy;
use gandr_theory_coherent_resolutions::CellApp;
use gandr_theory_deep_inference::DecompositionRefusal;
use gandr_theory_deep_inference::DependenceBits;
use gandr_theory_deep_inference::ModularNode;
use gandr_theory_deep_inference::ModularTree;
use gandr_theory_deep_inference::ModuleId;
use gandr_theory_deep_inference::WebRelation;
use gandr_theory_deep_inference::WebVertex;
use gandr_theory_deep_inference::WebVertexCount;
use gandr_theory_deep_inference::causal_web;
use gandr_theory_deep_inference::event_order;
use gandr_theory_deep_inference::module_lookup;
use proptest::prelude::*;
use quenchant_shape::shape::Maybe;

use crate::fixture::f_cell;

/// The vertices written, in order.
macro_rules! vertices {
    ($($vertex:literal),* $(,)?) => {
        vec![$({
            let vertex: usize = $vertex;
            WebVertex::from(vertex)
        }),*]
    };
}

/// The strict order the direct edges written generate over `count` events.
macro_rules! order {
    ($count:literal; $(($earlier:literal, $later:literal)),* $(,)?) => {{
        let count: usize = $count;
        let edges: Vec<(WebVertex, WebVertex)> = vec![$({
            let (earlier, later): (usize, usize) = ($earlier, $later);
            (WebVertex::from(earlier), WebVertex::from(later))
        }),*];
        DependenceBits::closure(WebVertexCount::from(count), &edges)
    }};
}

/// The node at `id`, which the tree must hold.
///
/// # Specification
/// trivial.
fn node(
    tree: &ModularTree,
    id: ModuleId,
) -> &ModularNode
{
    match tree.node(id) {
        Maybe::Present(node) => node,
        Maybe::Absent(reason) => panic!("the tree holds node {id:?}: {reason:?}"),
    }
}

/// The root of a tree over at least one event.
///
/// # Specification
/// trivial.
fn root(tree: &ModularTree) -> &ModularNode
{
    match tree.root() {
        Maybe::Present(id) => node(tree, id),
        Maybe::Absent(reason) => panic!("the tree has a root: {reason:?}"),
    }
}

/// The events of `ids`, each of which must be a leaf.
///
/// # Specification
/// trivial.
fn events(
    tree: &ModularTree,
    ids: &[ModuleId],
) -> Vec<WebVertex>
{
    ids.iter()
        .map(|&id| match *node(tree, id) {
            ModularNode::Event(vertex) => vertex,
            ModularNode::Par(_) | ModularNode::Seq(_) | ModularNode::Prime { .. } => {
                panic!("node {id:?} is an event")
            },
        })
        .collect()
}

/// The order's relation between two distinct vertices.
///
/// # Specification
/// trivial.
fn relation(
    bits: &DependenceBits,
    left: WebVertex,
    right: WebVertex,
) -> WebRelation
{
    if bool::from(bits.contains(left, right)) {
        WebRelation::Precedes
    }
    else if bool::from(bits.contains(right, left)) {
        WebRelation::Follows
    }
    else {
        WebRelation::Independent
    }
}

#[test]
fn the_empty_order_has_no_root()
{
    let tree = order!(0; ).decompose().expect("the empty order decomposes");
    assert_eq!(Maybe::Absent(module_lookup::Absent::Empty), tree.root());
    assert_eq!(
        Maybe::Absent(module_lookup::Absent::OutOfRange),
        tree.node(ModuleId::from(0_usize))
    );
}

#[test]
fn a_chain_is_one_series_node()
{
    let bits = order!(3; (0, 1), (1, 2));
    let tree = bits.decompose().expect("a chain decomposes");
    let ModularNode::Seq(ref factors) = *root(&tree)
    else {
        panic!("a chain is a series node: {tree:?}");
    };
    assert_eq!(vertices![0, 1, 2], events(&tree, factors));
    assert_eq!(0, usize::from(tree.prime_count()));
    assert_eq!(
        WebRelation::Precedes,
        tree.relation(WebVertex::from(0_usize), WebVertex::from(2_usize))
    );
    assert_eq!(
        WebRelation::Missing,
        tree.relation(WebVertex::from(1_usize), WebVertex::from(1_usize))
    );
    assert_eq!(
        WebRelation::Missing,
        tree.relation(WebVertex::from(0_usize), WebVertex::from(3_usize))
    );
}

#[test]
fn series_and_parallel_alternate()
{
    // Two events, then two more after both, then one after all four: the
    // series node holds two parallel pairs and the last event.
    let bits = order!(5; (0, 2), (0, 3), (1, 2), (1, 3), (2, 4), (3, 4));
    let tree = bits.decompose().expect("an alternation decomposes");
    let ModularNode::Seq(ref factors) = *root(&tree)
    else {
        panic!("the root is a series node: {tree:?}");
    };
    let [first, second, last] = factors[..]
    else {
        panic!("three series factors: {tree:?}");
    };
    for (pair, expected) in [(first, vertices![0, 1]), (second, vertices![2, 3])] {
        let ModularNode::Par(ref inner) = *node(&tree, pair)
        else {
            panic!("a parallel pair: {tree:?}");
        };
        assert_eq!(expected, events(&tree, inner));
    }
    assert_eq!(vertices![4], events(&tree, &[last]));
    assert_eq!(0, usize::from(tree.prime_count()));
}

#[test]
fn the_n_shape_is_prime()
{
    // a < c, b < c, b < d: no proper union of its events is a module.
    let bits = order!(4; (0, 2), (1, 2), (1, 3));
    let tree = bits.decompose().expect("the N-shape decomposes");
    let ModularNode::Prime {
        ref factors,
        ref quotient,
    } = *root(&tree)
    else {
        panic!("the N-shape is prime: {tree:?}");
    };
    assert_eq!(vertices![0, 1, 2, 3], events(&tree, factors));
    assert_eq!(&bits, quotient);
    assert_eq!(1, usize::from(tree.prime_count()));
}

#[test]
fn twins_fall_in_one_module()
{
    // The N-shape with its top-left event doubled: the twins relate alike to
    // every other event, so they are one factor of the prime node.
    let bits = order!(5; (0, 2), (1, 2), (1, 3), (0, 4), (1, 4));
    let tree = bits.decompose().expect("the doubled N-shape decomposes");
    let ModularNode::Prime {
        ref factors,
        ref quotient,
    } = *root(&tree)
    else {
        panic!("the doubled N-shape is prime: {tree:?}");
    };
    let [a, b, twins, d] = factors[..]
    else {
        panic!("four prime factors: {tree:?}");
    };
    assert_eq!(vertices![0, 1, 3], events(&tree, &[a, b, d]));
    let ModularNode::Par(ref pair) = *node(&tree, twins)
    else {
        panic!("the twins are one parallel factor: {tree:?}");
    };
    assert_eq!(vertices![2, 4], events(&tree, pair));
    assert_eq!(&order!(4; (0, 2), (1, 2), (1, 3)), quotient);
}

#[test]
fn a_cycle_is_refused_by_its_first_vertex()
{
    assert_eq!(
        Err(DecompositionRefusal::Cyclic {
            vertex: WebVertex::from(1_usize)
        }),
        order!(4; (0, 1), (1, 2), (2, 1), (2, 3)).decompose()
    );
}

#[test]
fn a_tracelet_web_decomposes_over_its_events()
{
    let mut store = CellStore::new();
    let cell = store.insert(f_cell());
    let peak = Toy::add(Toy::succ(Toy::zero()), Toy::succ(Toy::zero()));
    let path = [CellApp { cell, at: at![0] }, CellApp { cell, at: at![1] }];
    let web = causal_web(&event_order(&store, &peak, &path).expect("the fixture replays"));
    let tree = web.decompose().expect("a tracelet web decomposes");
    let ModularNode::Par(ref factors) = *root(&tree)
    else {
        panic!("two independent firings are one parallel node: {tree:?}");
    };
    assert_eq!(vertices![0, 1], events(&tree, factors));
    let mut emptied = web;
    emptied.events = Box::new([]);
    assert_eq!(Err(DecompositionRefusal::Malformed), emptied.decompose());
}

#[test]
fn a_synchronous_exchange_is_series_parallel()
{
    // Each endpoint sends, then receives the other's message: the two sends
    // are independent, the two receipts are independent, and every send
    // precedes every receipt.
    // Left: 0 sends a, 1 receives b. Right: 2 sends b, 3 receives a.
    let bits = order!(4; (0, 1), (2, 3), (0, 3), (2, 1));
    let tree = bits.decompose().expect("the exchange decomposes");
    assert_eq!(0, usize::from(tree.prime_count()));
    let ModularNode::Seq(ref factors) = *root(&tree)
    else {
        panic!("the exchange is sends then receipts: {tree:?}");
    };
    let [sends, receipts] = factors[..]
    else {
        panic!("two series factors: {tree:?}");
    };
    for (pair, expected) in [(sends, vertices![0, 2]), (receipts, vertices![1, 3])] {
        let ModularNode::Par(ref inner) = *node(&tree, pair)
        else {
            panic!("a parallel pair: {tree:?}");
        };
        assert_eq!(expected, events(&tree, inner));
    }
}

#[test]
fn a_move_before_a_crossing_receipt_leaves_a_prime_node()
{
    // Left: 0 sends a, 1 receives b. Right: 2 sends b, 3 moves on its own,
    // 4 receives a. Right's own move is after its send and independent of
    // Left's send: the N-shape 0 < 1 > 2 < 3, with no module short of the
    // whole.
    let bits = order!(5; (0, 1), (2, 3), (3, 4), (0, 4), (2, 1));
    let tree = bits.decompose().expect("the dialogue decomposes");
    assert_eq!(1, usize::from(tree.prime_count()));
    let ModularNode::Prime { ref factors, .. } = *root(&tree)
    else {
        panic!("the dialogue's root is prime: {tree:?}");
    };
    assert_eq!(vertices![0, 1, 2, 3, 4], events(&tree, factors));
}

prop_compose! {
    /// A strict order over up to nine events: each forward pair an edge or
    /// not, closed.
    ///
    /// # Specification
    /// trivial.
    fn generated()(count in 1_usize ..= 9)
        (edges in proptest::collection::vec(any::<bool>(), count.saturating_mul(count)), count in Just(count))
        -> (WebVertexCount, DependenceBits)
    {
        let direct: Vec<(WebVertex, WebVertex)> = (0 .. count)
            .flat_map(|earlier| (earlier.saturating_add(1) .. count).map(move |later| (earlier, later)))
            .filter(|&(earlier, later)| edges[earlier.saturating_mul(count).saturating_add(later)])
            .map(|(earlier, later)| (WebVertex::from(earlier), WebVertex::from(later)))
            .collect();
        let count = WebVertexCount::from(count);
        (count, DependenceBits::closure(count, &direct))
    }
}

proptest! {
    #[test]
    fn the_tree_reads_back_the_order((count, bits) in generated())
    {
        let tree = bits.decompose().expect("a closed acyclic order decomposes");
        let count = usize::from(count);
        for left in (0 .. count).map(WebVertex::from) {
            for right in (0 .. count).map(WebVertex::from) {
                if left != right {
                    prop_assert_eq!(relation(&bits, left, right), tree.relation(left, right));
                }
            }
        }
        for index in 0 .. usize::from(tree.node_count()) {
            match *node(&tree, ModuleId::from(index)) {
                ModularNode::Event(_) => {},
                ModularNode::Par(ref factors) => {
                    prop_assert!(factors.len() >= 2);
                    for &factor in factors {
                        prop_assert!(!matches!(node(&tree, factor), &ModularNode::Par(_)));
                    }
                },
                ModularNode::Seq(ref factors) => {
                    prop_assert!(factors.len() >= 2);
                    for &factor in factors {
                        prop_assert!(!matches!(node(&tree, factor), &ModularNode::Seq(_)));
                    }
                },
                ModularNode::Prime { ref factors, ref quotient } => {
                    let width = factors.len();
                    prop_assert!(width >= 4);
                    // No subset of two or more factors short of all of them
                    // relates alike to every factor outside it.
                    for subset in 1_u32 .. (1_u32 << width).saturating_sub(1) {
                        let marked = |factor: usize| subset & (1_u32 << factor) != 0;
                        let Some(first) = (0 .. width).find(|&factor| marked(factor))
                        else {
                            continue;
                        };
                        if subset.count_ones() < 2 {
                            continue;
                        }
                        let uniform = (0 .. width).filter(|&outside| !marked(outside)).all(|outside| {
                            let outside = WebVertex::from(outside);
                            let expected = relation(quotient, outside, WebVertex::from(first));
                            (0 .. width)
                                .filter(|&member| marked(member))
                                .all(|member| relation(quotient, outside, WebVertex::from(member)) == expected)
                        });
                        prop_assert!(!uniform, "{:b} is a module of a prime quotient", subset);
                    }
                },
            }
        }
    }
}
