//! The source-body boundary into actual diagram matching, and into the spider
//! canon.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use gandr_theory_circuit_algebras::Edge;
use gandr_theory_circuit_algebras::MatchCount;
use gandr_theory_circuit_algebras::SpiderTrials;
use gandr_theory_levitation::CircuitFrame;
use gandr_theory_levitation::CircuitRedex;
use gandr_theory_levitation::Name;
use quenchant_shape::shape::Maybe;

use super::*;

/// One operation with one named input and one named output.
///
/// # Specification
/// trivial.
fn operation(
    head: impl Into<Name>,
    input: impl Into<Name>,
    output: impl Into<Name>,
) -> CircuitNode
{
    CircuitNode::Frame(CircuitFrame::new(
        FrameHead::Op(head.into()),
        [FreeTerm::var(input)],
        output,
    ))
}

/// One operation `h` that reads `left` and `right` and binds `output`.
///
/// # Specification
/// trivial.
fn joined(
    left: impl Into<Name>,
    right: impl Into<Name>,
    output: impl Into<Name>,
) -> CircuitNode
{
    CircuitNode::Frame(CircuitFrame::new(
        FrameHead::Op("h".into()),
        [FreeTerm::var(left), FreeTerm::var(right)],
        output,
    ))
}

/// The names that `ports` spell, in order.
///
/// # Specification
/// trivial.
fn names<P, I>(ports: I) -> Vec<Name>
where
    I: IntoIterator<Item = P>,
    P: Into<Name>,
{
    ports.into_iter().map(Into::into).collect()
}

/// Each of `wires` marked with the sort `Q`.
///
/// # Specification
/// trivial.
fn marked<W, I>(wires: I) -> BTreeMap<Name, Name>
where
    I: IntoIterator<Item = W>,
    W: Into<Name>,
{
    wires
        .into_iter()
        .map(|wire| (wire.into(), Name::from("Q")))
        .collect()
}

/// An operation generator for a hand-built wiring.
///
/// # Specification
/// trivial.
fn generator<N, S, T>(
    name: N,
    sort: GeneratorSort,
    sources: S,
    targets: T,
) -> Generator
where
    N: Into<gandr_theory_circuit_algebras::GeneratorName>,
    S: IntoIterator<Item = Wire>,
    T: IntoIterator<Item = Wire>,
{
    Generator::new(
        GeneratorLabel::new(name, sort),
        sources.into_iter().collect::<Vec<_>>(),
        targets.into_iter().collect::<Vec<_>>(),
    )
}

/// The wires that `positions` number.
///
/// # Specification
/// trivial.
fn wires<I>(positions: I) -> Vec<Wire>
where
    I: IntoIterator<Item = usize>,
{
    positions.into_iter().map(Wire::from).collect()
}

/// A nonzero matching allowance for these finite diagrams.
///
/// # Specification
/// trivial.
fn budget() -> MatchBudget
{
    MatchBudget::from(4096_usize)
}

/// A spider allowance that no tie of these diagrams exhausts.
///
/// # Specification
/// trivial.
fn spider_budget() -> SpiderBudget
{
    SpiderBudget::from(64_usize)
}

#[test]
fn a_two_line_body_reads_as_a_diagram_with_one_internal_wire()
{
    let body = CircuitBody::new(
        [
            operation("f", "input", "middle"),
            operation("g", "middle", "result"),
        ],
        "result",
    );
    let (inputs, marks) = (names(["input"]), BTreeMap::new());
    let wiring =
        circuit_wiring(CircuitReading::new(&body, &inputs, &marks)).expect("a two-step chain");
    assert_eq!(wiring.wire_count(), WireCount::from(3_usize));
    assert_eq!(wiring.boundary().inputs(), [Wire::from(0_usize)]);
    assert_eq!(wiring.boundary().outputs(), [Wire::from(2_usize)]);
    assert_eq!(
        wiring.producer_of(Wire::from(1_usize)),
        Maybe::Present(Edge::from(0_usize))
    );
    assert_eq!(
        wiring.consumer_of(Wire::from(1_usize)),
        Maybe::Present(Edge::from(1_usize))
    );
    assert_eq!(wiring.generators()[0].sources(), [Wire::from(0_usize)]);
    assert_eq!(wiring.generators()[1].targets(), [Wire::from(2_usize)]);
}

#[test]
fn a_ground_argument_names_no_wire()
{
    let body = CircuitBody::new(
        [CircuitNode::Frame(CircuitFrame::new(
            FrameHead::Op("f".into()),
            [FreeTerm::ctor("Zero", [])],
            "out",
        ))],
        "out",
    );
    let marks = BTreeMap::new();
    assert_eq!(
        circuit_wiring(CircuitReading::new(&body, &[], &marks)),
        Err(CircuitWiringError::ArgumentIsNotAPort("Zero".into()))
    );
}

#[test]
fn a_body_binding_one_port_twice_is_not_a_wiring()
{
    // With no mark, the merge on `shared` and the split on `middle` keep the
    // refusals of the monogamous fragment, at those wires.
    let merge = CircuitBody::new(
        [
            operation("f", "left", "shared"),
            operation("g", "right", "shared"),
        ],
        "shared",
    );
    let (inputs, marks) = (names(["left", "right"]), BTreeMap::new());
    assert_eq!(
        circuit_wiring(CircuitReading::new(&merge, &inputs, &marks)),
        Err(CircuitWiringError::NotAWiring(WiringObstruction::FanIn {
            wire: Wire::from(2_usize),
            first: Edge::from(0_usize),
            second: Edge::from(1_usize),
        }))
    );
    let split = CircuitBody::rooted(
        [
            operation("f", "input", "middle"),
            operation("g", "middle", "left"),
            operation("k", "middle", "right"),
        ],
        names(["left", "right"]),
    );
    let inputs = names(["input"]);
    assert_eq!(
        circuit_wiring(CircuitReading::new(&split, &inputs, &marks)),
        Err(CircuitWiringError::NotAWiring(WiringObstruction::FanOut {
            wire: Wire::from(1_usize),
            first: Edge::from(1_usize),
            second: Edge::from(2_usize),
        }))
    );
}

#[test]
fn a_marked_merge_and_split_read_as_spiders_5800()
{
    // `node : f(x) --> (z); node : g(y) --> (z);` with `z` marked: one spider
    // merges the two producers into the declared output.
    let marks = marked(["z"]);
    let merge = CircuitBody::new([operation("f", "x", "z"), operation("g", "y", "z")], "z");
    let inputs = names(["x", "y"]);
    let wiring =
        circuit_wiring(CircuitReading::new(&merge, &inputs, &marks)).expect("a marked merge");
    let [ref f, ref g, ref spider] = *wiring.generators()
    else {
        panic!("the two nodes and one spider: {:?}", wiring.generators())
    };
    assert_eq!(
        spider.label(),
        &GeneratorLabel::new("Q", GeneratorSort::Spider),
        "the sort of the wire names the spider"
    );
    assert_eq!(spider.sources(), [f.targets()[0], g.targets()[0]]);
    assert_eq!(spider.targets(), wiring.boundary().outputs());
    // `node : f(x) --> (z); node : g(z) --> (a); node : k(z) --> (b);`: one
    // spider splits the producer into the two consumers.
    let split = CircuitBody::rooted(
        [
            operation("f", "x", "z"),
            operation("g", "z", "a"),
            operation("k", "z", "b"),
        ],
        names(["a", "b"]),
    );
    let inputs = names(["x"]);
    let wiring =
        circuit_wiring(CircuitReading::new(&split, &inputs, &marks)).expect("a marked split");
    let [ref f, ref g, ref k, ref spider] = *wiring.generators()
    else {
        panic!("the three nodes and one spider: {:?}", wiring.generators())
    };
    assert_eq!(spider.sources(), f.targets());
    assert_eq!(spider.targets(), [g.sources()[0], k.sources()[0]]);
    // A marked wire with one producer and one consumer stays a plain wire.
    let chain = CircuitBody::new([operation("f", "x", "z"), operation("g", "z", "o")], "o");
    let wiring =
        circuit_wiring(CircuitReading::new(&chain, &inputs, &marks)).expect("a marked chain");
    assert_eq!(wiring.generators().len(), 2, "no spider on a plain wire");
    assert_eq!(
        wiring.generators()[0].targets(),
        wiring.generators()[1].sources()
    );
}

#[test]
fn two_merges_in_either_association_are_one_canon_5800()
{
    // The body merges three producers into `z`, and the reading gives one
    // spider with three sources. Two binary merges, nested either way, are
    // the same diagram modulo the laws.
    let body = CircuitBody::new(
        [
            operation("f", "x", "z"),
            operation("g", "y", "z"),
            operation("k", "w", "z"),
        ],
        "z",
    );
    let (inputs, marks) = (names(["x", "y", "w"]), marked(["z"]));
    let canon = circuit_canon(CircuitReading::new(&body, &inputs, &marks), spider_budget())
        .expect("a merge of three");
    let nodes = || {
        [
            generator("f", GeneratorSort::Operation, wires([0]), wires([3])),
            generator("g", GeneratorSort::Operation, wires([1]), wires([4])),
            generator("k", GeneratorSort::Operation, wires([2]), wires([5])),
        ]
    };
    let nested = |inner: [usize; 2], outer: [usize; 2]| {
        let mut generators = Vec::from(nodes());
        generators.push(generator(
            "Q",
            GeneratorSort::Spider,
            wires(inner),
            wires([6]),
        ));
        generators.push(generator(
            "Q",
            GeneratorSort::Spider,
            wires(outer),
            wires([7]),
        ));
        Wiring::assemble(
            WireCount::from(8_usize),
            generators,
            Interface::new(wires([0, 1, 2]), wires([7])),
        )
        .expect("two binary merges")
    };
    for association in [nested([3, 4], [6, 5]), nested([4, 5], [3, 6])] {
        let other = spider_canonicalize(&association, spider_budget()).expect("one association");
        assert_eq!(
            canon.form(),
            other.form(),
            "each association is the merge of three"
        );
    }
}

#[test]
fn every_order_of_the_nodes_gives_one_canon_5800()
{
    // The boundary is the declared ports, not the first appearance of each
    // wire, so the order of the nodes changes neither the interface nor the
    // canon: with the merge on `m` marked, and with no mark at all.
    let orders = [[0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [
        2, 1, 0,
    ]];
    let merged = [
        operation("f", "x", "m"),
        operation("g", "y", "m"),
        joined("m", "w", "z"),
    ];
    let plain = [
        operation("f", "x", "m"),
        operation("g", "y", "n"),
        joined("m", "n", "z"),
    ];
    let cases = [
        (merged, names(["x", "y", "w"]), marked(["m"])),
        (plain, names(["x", "y"]), BTreeMap::new()),
    ];
    for &(ref nodes, ref inputs, ref marks) in &cases {
        let forms: Vec<_> = orders
            .iter()
            .map(|order| {
                let body = CircuitBody::new(order.map(|at| nodes[at].clone()), "z");
                circuit_canon(CircuitReading::new(&body, inputs, marks), spider_budget())
                    .expect("one body in some node order")
                    .form()
                    .clone()
            })
            .collect();
        assert!(
            forms.iter().all(|form| *form == forms[0]),
            "every node order of {nodes:?} has one canon"
        );
    }
}

#[test]
fn a_body_past_the_budget_is_refused_by_name_5800()
{
    // `node : f(x) --> (z); node : f(y) --> (z);` with `z` marked: the two
    // sources of the spider tie, so the canon needs two trials.
    let body = CircuitBody::new([operation("f", "x", "z"), operation("f", "y", "z")], "z");
    let (inputs, marks) = (names(["x", "y"]), marked(["z"]));
    let reading = CircuitReading::new(&body, &inputs, &marks);
    assert_eq!(
        circuit_canon(reading, SpiderBudget::from(1_usize)),
        Err(CircuitCanonError::Canon(
            SpiderObstruction::BudgetExhausted {
                needed: SpiderTrials::from(2_usize),
                budget: SpiderBudget::from(1_usize),
            }
        ))
    );
    let canon =
        circuit_canon(reading, SpiderBudget::from(2_usize)).expect("two trials decide the tie");
    assert_eq!(canon.trials(), SpiderTrials::from(2_usize));
}

#[test]
fn every_wiring_error_renders_what_it_refused()
{
    use alloc::string::ToString as _;

    let term = CircuitWiringError::ArgumentIsNotAPort("Zero".into()).to_string();
    let results = CircuitWiringError::ResultsAreNotAPort.to_string();
    let obstruction = WiringObstruction::FanIn {
        wire: Wire::from(1_usize),
        first: Edge::from(0_usize),
        second: Edge::from(1_usize),
    };
    let fanned = CircuitWiringError::NotAWiring(obstruction).to_string();
    assert!(term.contains("`Zero`"), "{term}");
    assert!(
        fanned.ends_with(obstruction.to_string().as_str()),
        "{fanned}"
    );
    assert!(term != results && results != fanned && fanned != term);
}

#[test]
fn a_rule_body_embeds_in_a_body_that_contains_it()
{
    let marks = BTreeMap::new();
    let (pattern_inputs, target_inputs) = (names(["x"]), names(["a"]));
    let pattern = CircuitBody::new([operation("f", "x", "y")], "y");
    let target = CircuitBody::new([operation("g", "a", "b"), operation("f", "b", "c")], "c");
    let matching = embed_circuit_rule(
        CircuitReading::new(&pattern, &pattern_inputs, &marks),
        CircuitReading::new(&target, &target_inputs, &marks),
        budget(),
    )
    .expect("bounded match");
    assert_eq!(matching.admitted_count(), MatchCount::from(1_usize));
    let [ref embedding] = *matching.admitted()
    else {
        panic!("one matching occurrence")
    };
    assert_eq!(
        embedding.wires().image_of(Wire::from(0_usize)),
        Maybe::Present(Wire::from(1_usize))
    );
    assert_eq!(
        embedding.wires().image_of(Wire::from(1_usize)),
        Maybe::Present(Wire::from(2_usize))
    );
}

#[test]
fn a_body_that_does_not_contain_the_pattern_admits_no_embedding()
{
    let marks = BTreeMap::new();
    let (pattern_inputs, target_inputs) = (names(["x"]), names(["a"]));
    let pattern = CircuitBody::new([operation("f", "x", "y")], "y");
    let target = CircuitBody::new([operation("g", "a", "b")], "b");
    let matching = embed_circuit_rule(
        CircuitReading::new(&pattern, &pattern_inputs, &marks),
        CircuitReading::new(&target, &target_inputs, &marks),
        budget(),
    )
    .expect("completed search");
    assert_eq!(matching.admitted_count(), MatchCount::from(0_usize));
}

#[test]
fn one_spelling_in_two_roles_is_two_boxes()
{
    let marks = BTreeMap::new();
    let (pattern_inputs, target_inputs) = (names(["x"]), names(["a"]));
    let operation_body = CircuitBody::new([operation("same", "a", "b")], "b");
    let constructor = CircuitNode::Frame(CircuitFrame::new(
        FrameHead::Ctor("same".into()),
        [FreeTerm::var("x")],
        "y",
    ));
    let rewrite = CircuitNode::Redex(CircuitRedex::new(
        "same",
        FreeTerm::var("x"),
        FreeTerm::var("y"),
        "y",
    ));
    for node in [constructor, rewrite] {
        let pattern = CircuitBody::new([node], "y");
        let matching = embed_circuit_rule(
            CircuitReading::new(&pattern, &pattern_inputs, &marks),
            CircuitReading::new(&operation_body, &target_inputs, &marks),
            budget(),
        )
        .expect("completed search");
        assert_eq!(matching.admitted_count(), MatchCount::from(0_usize));
    }
}

#[test]
fn an_exhausted_budget_declines_rather_than_reporting_no_match()
{
    let marks = BTreeMap::new();
    let inputs = names(["x"]);
    let pattern = CircuitBody::new([operation("f", "x", "y")], "y");
    let reading = CircuitReading::new(&pattern, &inputs, &marks);
    assert!(matches!(
        embed_circuit_rule(reading, reading, MatchBudget::from(0_usize)),
        Err(CircuitEmbedError::Matching(_))
    ));
}

/// #5763: a reading is spidered exactly where a marked wire merges or splits.
/// The same merge unmarked gives no spider. A marked wire that one node
/// produces and one node reads gives none too.
#[test]
fn a_reading_is_spidered_where_a_marked_wire_merges_5763()
{
    let merge = CircuitBody::new([operation("f", "x", "z"), operation("g", "y", "z")], "z");
    let inputs = names(["x", "y"]);
    let marks = marked(["z"]);
    let unmarked = BTreeMap::new();
    assert!(
        CircuitReading::new(&merge, &inputs, &marks)
            .spidered()
            .is_some(),
        "a marked merge gives a spider"
    );
    assert!(
        CircuitReading::new(&merge, &inputs, &unmarked)
            .spidered()
            .is_none(),
        "the same merge unmarked gives none"
    );
    let chain = CircuitBody::new([operation("f", "x", "z"), operation("g", "z", "w")], "w");
    let input = names(["x"]);
    assert!(
        CircuitReading::new(&chain, &input, &marks)
            .spidered()
            .is_none(),
        "a marked wire that neither merges nor splits gives none"
    );
}
