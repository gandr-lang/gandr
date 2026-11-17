//! The overlap enumerator's witnesses: a root overlap of two calls, the
//! circle's cancellations overlapping below their roots, the copy monogamy
//! refuses, the cycle acyclicity refuses, and the inclusion shapes.

use super::*;
use crate::interface::GeneratorLabel;
use crate::interface::GeneratorName;
use crate::interface::GeneratorSort;
use crate::normal_form::DiagramEquality;
use crate::normal_form::same_diagram;

/// A generator of `name` in `sort` over the wires `sources` to `targets`.
///
/// # Specification
/// trivial.
fn generator<N, const S: usize, const T: usize>(
    name: N,
    sort: GeneratorSort,
    sources: [Wire; S],
    targets: [Wire; T],
) -> Generator
where
    N: Into<GeneratorName>,
{
    Generator::new(GeneratorLabel::new(name, sort), sources, targets)
}

/// A fixture diagram, which the fragment's conditions accept.
///
/// # Specification
/// - requires: the fixture is monogamous, boundary-honest and acyclic.
/// - ensures: the assembled wiring, every supplied generator retained.
/// - panics: if assembly refuses the fixture.
///
/// # Adequacy
/// - hypothesis: L3 — every fixture below assembles, and the overlaps read off
///   them are asserted by their peaks.
/// - witness: `overlap::tests::two_rules_over_one_call_overlap_at_their_shared_frame`
#[spec(captures: edges = generators.len(), ensures: |ref ret| ret.generators().len() == edges)]
fn diagram<W>(
    wires: W,
    generators: Vec<Generator>,
    inputs: &[Wire],
    outputs: &[Wire],
) -> Wiring
where
    W: Into<WireCount>,
{
    Wiring::assemble(wires.into(), generators, Interface::new(inputs, outputs))
        .expect("a fixture diagram is monogamous and acyclic")
}

/// `add(Succ(m), n)`, read as `⟨Succ(m) | add(n; α)⟩`.
///
/// # Specification
/// trivial.
fn add_of_a_successor() -> Wiring
{
    diagram(
        4_usize,
        alloc::vec![
            generator("Succ", GeneratorSort::Value, wires![0], wires![1]),
            generator("add", GeneratorSort::Operation, wires![1, 2], wires![3]),
        ],
        &wires![0, 2],
        &wires![3],
    )
}

#[test]
fn two_rules_over_one_call_overlap_at_their_shared_frame()
{
    // `add(x, Zero)`, read as `⟨x | add(Zero; β)⟩`.
    let add_of_zero = diagram(
        3_usize,
        alloc::vec![
            generator("Zero", GeneratorSort::Value, wires![], wires![1]),
            generator("add", GeneratorSort::Operation, wires![0, 1], wires![2]),
        ],
        &wires![0],
        &wires![2],
    );
    let found = overlaps(&add_of_a_successor(), &add_of_zero);
    let [ref overlap] = *found.as_slice()
    else {
        panic!("one overlap, at the shared frame: {found:?}")
    };
    // `add(Succ(m), Zero)`: the right side's `Zero` lands past the left's two
    // generators, on the wire the left side read as `n`.
    let peak = diagram(
        4_usize,
        alloc::vec![
            generator("Succ", GeneratorSort::Value, wires![0], wires![1]),
            generator("add", GeneratorSort::Operation, wires![1, 2], wires![3]),
            generator("Zero", GeneratorSort::Value, wires![], wires![2]),
        ],
        &wires![0],
        &wires![3],
    );
    assert!(
        matches!(
            same_diagram(overlap.peak(), &peak),
            DiagramEquality::Same(_)
        ),
        "{:?}",
        overlap.peak()
    );
    assert_eq!(
        (
            overlap.right_image(Edge::from(0_usize)),
            overlap.right_image(Edge::from(1_usize)),
            overlap.right_image(Edge::from(2_usize)),
        ),
        (Some(Edge::from(2_usize)), Some(Edge::from(1_usize)), None),
        "the right `add` is the left's, and its `Zero` the peak's third generator"
    );
    assert_eq!(
        (0_usize ..= 3_usize)
            .map(|wire| overlap.right_wire(Wire::from(wire)))
            .collect::<Vec<_>>(),
        alloc::vec![
            Some(Wire::from(1_usize)),
            Some(Wire::from(2_usize)),
            Some(Wire::from(3_usize)),
            None
        ],
        "the right side's cut, its `Zero` wire and its result land on the left's: the two \
         overlap at the root"
    );
    assert_eq!(
        (overlap.shared(), overlap.shape()),
        (EdgeCount::from(1_usize), OverlapShape::Regular)
    );
}

#[test]
fn a_cancellation_overlaps_its_inverse_below_the_root()
{
    // `Loop(Unloop(x))` and `Unloop(Loop(y))`.
    let loop_unloop = diagram(
        3_usize,
        alloc::vec![
            generator("Unloop", GeneratorSort::Value, wires![0], wires![1]),
            generator("Loop", GeneratorSort::Value, wires![1], wires![2]),
        ],
        &wires![0],
        &wires![2],
    );
    let unloop_loop = diagram(
        3_usize,
        alloc::vec![
            generator("Loop", GeneratorSort::Value, wires![0], wires![1]),
            generator("Unloop", GeneratorSort::Value, wires![1], wires![2]),
        ],
        &wires![0],
        &wires![2],
    );
    let found = overlaps(&loop_unloop, &unloop_loop);
    let [ref at_unloop, ref at_loop] = *found.as_slice()
    else {
        panic!("two overlaps, one at each shared generator: {found:?}")
    };
    // `Loop(Unloop(Loop(y)))`: the right side's `Loop` feeds the left's
    // `Unloop`.
    let first = diagram(
        4_usize,
        alloc::vec![
            generator("Unloop", GeneratorSort::Value, wires![0], wires![1]),
            generator("Loop", GeneratorSort::Value, wires![1], wires![2]),
            generator("Loop", GeneratorSort::Value, wires![3], wires![0]),
        ],
        &wires![3],
        &wires![2],
    );
    // `Unloop(Loop(Unloop(x)))`: the left side's `Loop` feeds the right's
    // `Unloop`.
    let second = diagram(
        4_usize,
        alloc::vec![
            generator("Unloop", GeneratorSort::Value, wires![0], wires![1]),
            generator("Loop", GeneratorSort::Value, wires![1], wires![2]),
            generator("Unloop", GeneratorSort::Value, wires![2], wires![3]),
        ],
        &wires![0],
        &wires![3],
    );
    assert!(
        matches!(
            same_diagram(at_unloop.peak(), &first),
            DiagramEquality::Same(_)
        ),
        "{:?}",
        at_unloop.peak()
    );
    assert!(
        matches!(
            same_diagram(at_loop.peak(), &second),
            DiagramEquality::Same(_)
        ),
        "{:?}",
        at_loop.peak()
    );
    for overlap in [at_unloop, at_loop] {
        assert_eq!(
            (overlap.shared(), overlap.shape()),
            (EdgeCount::from(1_usize), OverlapShape::Regular)
        );
    }
}

#[test]
fn a_shared_region_that_would_copy_a_wire_is_no_overlap()
{
    // `f(g(x))` and `h(g(y))`: gluing the two `g`s would hand one result to
    // `f` and to `h`.
    let under = |head: &str| {
        diagram(
            3_usize,
            alloc::vec![
                generator("g", GeneratorSort::Value, wires![0], wires![1]),
                generator(head, GeneratorSort::Value, wires![1], wires![2]),
            ],
            &wires![0],
            &wires![2],
        )
    };
    assert_eq!(overlaps(&under("f"), &under("h")), []);
    // A label worn in another role is another generator: an operation `g`
    // never meets a constructor `g`.
    let operation = diagram(
        2_usize,
        alloc::vec![generator("g", GeneratorSort::Operation, wires![0], wires![
            1
        ])],
        &wires![0],
        &wires![1],
    );
    assert_eq!(overlaps(&under("f"), &operation), []);
}

#[test]
fn a_gluing_that_closes_a_cycle_is_no_overlap()
{
    let operation = |name: &str, sources: &[Wire], targets: &[Wire]| {
        Generator::new(
            GeneratorLabel::new(name, GeneratorSort::Operation),
            sources.to_vec(),
            targets.to_vec(),
        )
    };
    // `a` feeds `c` and, through `k`, `b`; `b` feeds `c` too.
    let left = diagram(
        7_usize,
        alloc::vec![
            operation("a", &wires![0], &wires![1, 2]),
            operation("k", &wires![2], &wires![3]),
            operation("b", &wires![3], &wires![4, 6]),
            operation("c", &wires![1, 4], &wires![5]),
        ],
        &wires![0],
        &wires![5, 6],
    );
    // The same `a`, `b` and `c`, but `b` feeds `a` through `m`.
    let right = diagram(
        7_usize,
        alloc::vec![
            operation("b", &wires![0], &wires![1, 2]),
            operation("m", &wires![2], &wires![3]),
            operation("a", &wires![3], &wires![4, 5]),
            operation("c", &wires![4, 1], &wires![6]),
        ],
        &wires![0],
        &wires![6, 5],
    );
    // Every seed forces `a`, `b` and `c` together, and the glued diagram runs
    // `a`, `k`, `b`, `m` and back to `a`.
    assert_eq!(overlaps(&left, &right), []);
    assert_eq!(overlaps(&right, &left), []);
}

#[test]
fn a_side_inside_the_other_is_an_inclusion()
{
    // `add(m, n)`, read as `⟨m | add(n; β)⟩`.
    let bare = diagram(
        3_usize,
        alloc::vec![generator(
            "add",
            GeneratorSort::Operation,
            wires![0, 1],
            wires![2]
        )],
        &wires![0, 1],
        &wires![2],
    );
    let left = add_of_a_successor();
    let [ref inside] = *overlaps(&left, &bare)
    else {
        panic!("one overlap, the right side inside the left")
    };
    assert!(
        matches!(same_diagram(inside.peak(), &left), DiagramEquality::Same(_)),
        "{:?}",
        inside.peak()
    );
    assert_eq!(inside.shape(), OverlapShape::RightIncluded);
    let [ref around] = *overlaps(&bare, &left)
    else {
        panic!("and the left side inside the right")
    };
    assert_eq!(around.shape(), OverlapShape::LeftIncluded);
    // A side against itself reaches its identity gluing once.
    let [ref itself] = *overlaps(&left, &left)
    else {
        panic!("one identity gluing")
    };
    assert!(
        matches!(same_diagram(itself.peak(), &left), DiagramEquality::Same(_)),
        "{:?}",
        itself.peak()
    );
    assert_eq!(
        (itself.shared(), itself.shape()),
        (EdgeCount::from(2_usize), OverlapShape::Coincident)
    );
}
