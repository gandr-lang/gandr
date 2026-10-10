//! The matcher's witnesses: embeddings by fixture family, the convexity
//! routes, the differential against the one-sided matcher, the certificate
//! reader and the multi-admission diagnostic.

use gandr_theory_cell_complexes::CmdPat;
use gandr_theory_cell_complexes::ConsPat;
use gandr_theory_cell_complexes::Polarity;
use gandr_theory_cell_complexes::ProdPat;
use gandr_theory_cell_complexes::Subst;
use gandr_theory_cell_complexes::SubstitutionDecision;
use gandr_theory_cell_complexes::match_cmd;

use super::*;
use crate::interface::Generator;
use crate::interface::GeneratorLabel;
use crate::interface::GeneratorName;
use crate::interface::GeneratorSort;
use crate::interface::Interface;
use crate::interface::WiringObstruction;
use crate::interface::spine::SpineReading;
use crate::interface::spine::read_spine;

/// A value-sorted generator label.
///
/// # Specification
/// trivial.
fn value<N>(name: N) -> GeneratorLabel
where
    N: Into<GeneratorName>,
{
    GeneratorLabel::new(name, GeneratorSort::Value)
}

/// A fixture diagram, which the fragment's conditions accept.
///
/// # Specification
/// - requires: the fixture satisfies the wiring assembly invariants.
/// - ensures: every supplied generator and boundary port is retained.
/// - panics: if assembly refuses the fixture.
///
/// # Adequacy
/// - hypothesis: L3 — ordered-port, multi-root and disconnected fixtures expose
///   retained incidence through actual matching verdicts. Dropping a generator
///   or boundary role changes those verdicts; malformed fixtures are outside
///   the domain.
/// - witness: `matching::tests::a_multi_root_pattern_embeds`
/// - witness: `matching::tests::port_order_is_preserved_so_a_swapped_target_is_not_a_match`
#[spec(captures: [edges = generators.len(), inputs = boundary.inputs().len(), outputs = boundary.outputs().len()],
ensures: |ref diagram| diagram.generators().len() == edges && diagram.boundary().inputs().len() == inputs && diagram.boundary().outputs().len() == outputs)]
fn diagram<W>(
    wires: W,
    generators: Vec<Generator>,
    boundary: Interface,
) -> Wiring
where
    W: Into<WireCount>,
{
    Wiring::assemble(wires.into(), generators, boundary)
        .expect("a fixture diagram is monogamous and acyclic")
}

/// A pattern paired with the target it is matched against.
struct Against<Diagram>
{
    /// The pattern side.
    pattern: Diagram,
    /// The target side.
    target: Diagram,
}

/// A budget no fixture here comes near: exhausting it would be a defect, not a
/// cost.
///
/// # Specification
/// trivial.
fn budget() -> MatchBudget
{
    MatchBudget::from(10_000)
}

/// The images of every admitted embedding, in enumeration order.
///
/// # Specification
/// trivial.
fn images(matching: &Matching) -> Vec<Vec<Edge>>
{
    matching
        .admitted()
        .iter()
        .map(|embedding| embedding.image().to_vec())
        .collect()
}

/// The first admitted embedding of a search that admits one.
///
/// # Specification
/// - requires: the search admits at least one embedding.
/// - ensures: borrows its first admission.
/// - panics: when the admission list is empty.
///
/// # Adequacy
/// - hypothesis: L3 — multi-admission searches observe the representative image
///   and ordered divergences. Selecting a later certificate differs; an empty
///   search is outside the observer domain.
/// - witness: `matching::tests::a_multi_admission_reports_its_first_divergences_in_order`
#[spec(requires: !matching.admitted.is_empty(), ensures: |result| matching.admitted.first().is_some_and(|first| core::ptr::eq(core::ptr::from_ref(result), core::ptr::from_ref(first))))]
fn first(matching: &Matching) -> &Embedding
{
    matching
        .admitted()
        .first()
        .expect("the admitted embedding is there")
}

/// `f: (0) -> (1, 2)`, `g: (1) -> (3)`, `h: (2) -> (4)`: one generator
/// emitting to two destinations, each read by a different generator.
///
/// # Specification
/// trivial.
fn multi_output_pattern() -> Wiring
{
    diagram(
        5,
        alloc::vec![
            Generator::new(value("f"), wires![0], wires![1, 2]),
            Generator::new(value("g"), wires![1], wires![3]),
            Generator::new(value("h"), wires![2], wires![4]),
        ],
        Interface::new(wires![0], wires![3, 4]),
    )
}

/// The multi-output pattern inside a larger diagram, with a generator above
/// it and one below one of its outputs.
///
/// # Specification
/// trivial.
fn multi_output_target() -> Wiring
{
    diagram(
        7,
        alloc::vec![
            Generator::new(value("e"), wires![0], wires![1]),
            Generator::new(value("f"), wires![1], wires![2, 3]),
            Generator::new(value("g"), wires![2], wires![4]),
            Generator::new(value("h"), wires![3], wires![5]),
            Generator::new(value("k"), wires![4], wires![6]),
        ],
        Interface::new(wires![0], wires![5, 6]),
    )
}

/// `f: (0) -> (2)`, `g: (1) -> (3)`, `h: (2, 3) -> (4)`: two roots, so no
/// single place a structural recursion could start from.
///
/// # Specification
/// trivial.
fn multi_root_pattern() -> Wiring
{
    diagram(
        5,
        alloc::vec![
            Generator::new(value("f"), wires![0], wires![2]),
            Generator::new(value("g"), wires![1], wires![3]),
            Generator::new(value("h"), wires![2, 3], wires![4]),
        ],
        Interface::new(wires![0, 1], wires![4]),
    )
}

/// The multi-root pattern with a generator above each root and one below its
/// output.
///
/// # Specification
/// trivial.
fn multi_root_target() -> Wiring
{
    diagram(
        8,
        alloc::vec![
            Generator::new(value("e0"), wires![0], wires![1]),
            Generator::new(value("e1"), wires![2], wires![3]),
            Generator::new(value("f"), wires![1], wires![4]),
            Generator::new(value("g"), wires![3], wires![5]),
            Generator::new(value("h"), wires![4, 5], wires![6]),
            Generator::new(value("k"), wires![6], wires![7]),
        ],
        Interface::new(wires![0, 2], wires![7]),
    )
}

/// `f: (0) -> (1, 2)`, `g: (1, 2) -> (3)`: two paths out of one generator
/// rejoining at another.
///
/// # Specification
/// trivial.
fn reconvergent_pattern() -> Wiring
{
    diagram(
        4,
        alloc::vec![
            Generator::new(value("f"), wires![0], wires![1, 2]),
            Generator::new(value("g"), wires![1, 2], wires![3]),
        ],
        Interface::new(wires![0], wires![3]),
    )
}

/// The reconvergent pattern inside a larger diagram.
///
/// # Specification
/// trivial.
fn reconvergent_target() -> Wiring
{
    diagram(
        6,
        alloc::vec![
            Generator::new(value("e"), wires![0], wires![1]),
            Generator::new(value("f"), wires![1], wires![2, 3]),
            Generator::new(value("g"), wires![2, 3], wires![4]),
            Generator::new(value("k"), wires![4], wires![5]),
        ],
        Interface::new(wires![0], wires![5]),
    )
}

/// `a: (0) -> (1)` beside `b: (2) -> (3)`, with no wire between them.
///
/// # Specification
/// trivial.
fn disconnected_pattern() -> Wiring
{
    diagram(
        4,
        alloc::vec![
            Generator::new(value("a"), wires![0], wires![1]),
            Generator::new(value("b"), wires![2], wires![3]),
        ],
        Interface::new(wires![0, 2], wires![1, 3]),
    )
}

/// `a: (0) -> (1)` then `b: (1) -> (2)`: the disconnected pattern's two
/// generators joined by a wire.
///
/// # Specification
/// trivial.
fn joined_target() -> Wiring
{
    diagram(
        3,
        alloc::vec![
            Generator::new(value("a"), wires![0], wires![1]),
            Generator::new(value("b"), wires![1], wires![2]),
        ],
        Interface::new(wires![0], wires![2]),
    )
}

/// The published blocking shape: `a` and `b` with `c` between them, so a
/// directed path runs from `a`'s image out through `c` and into `b`'s.
///
/// # Specification
/// trivial.
fn blocking_target() -> Wiring
{
    diagram(
        4,
        alloc::vec![
            Generator::new(value("a"), wires![0], wires![1]),
            Generator::new(value("c"), wires![1], wires![2]),
            Generator::new(value("b"), wires![2], wires![3]),
        ],
        Interface::new(wires![0], wires![3]),
    )
}

/// Two `a` generators and one `b`, so the disconnected pattern's first
/// component has two places to land.
///
/// # Specification
/// trivial.
fn two_admission_target() -> Wiring
{
    diagram(
        6,
        alloc::vec![
            Generator::new(value("a"), wires![0], wires![1]),
            Generator::new(value("a"), wires![2], wires![3]),
            Generator::new(value("b"), wires![4], wires![5]),
        ],
        Interface::new(wires![0, 2, 4], wires![1, 3, 5]),
    )
}

/// The identity pattern: one bare wire, open at both ends.
///
/// # Specification
/// trivial.
fn bare_wire_pattern() -> Wiring
{
    diagram(
        0_usize.saturating_add(1),
        Vec::new(),
        Interface::new(wires![0], wires![0]),
    )
}

/// Two port-free generators of one label: two points.
///
/// # Specification
/// trivial.
fn two_points() -> Wiring
{
    diagram(
        0,
        alloc::vec![
            Generator::new(value("s"), wires![], wires![]),
            Generator::new(value("s"), wires![], wires![]),
        ],
        Interface::default(),
    )
}

/// The empty diagram.
///
/// # Specification
/// trivial.
fn empty() -> Wiring
{
    diagram(0, Vec::new(), Interface::default())
}

/// A claimed wire map from pairs, which must be injective.
///
/// # Specification
/// - requires: repeated sources agree and distinct sources have distinct
///   images.
/// - ensures: the map contains exactly the supplied pairs, duplicates
///   collapsed.
/// - panics: on conflicting pairs.
///
/// # Adequacy
/// - hypothesis: L3 — deliberately shifted, overwide and incomplete certificate
///   maps expose the supplied associations through exact checker refusals.
///   Skipping or reversing a pair changes the refusal; contradictory input
///   pairs are outside the fixture builder domain.
/// - witness: `matching::tests::a_certificate_with_a_shifted_wire_map_is_refused`
/// - witness: `matching::tests::a_certificate_mapping_wires_outside_the_pattern_is_refused`
/// - witness: `matching::tests::a_certificate_leaving_a_wire_unmapped_is_refused`
#[spec(requires: pairs.iter().all(|left| pairs.iter().all(|right| (left.0 == right.0) == (left.1 == right.1))),
ensures: |ref map| pairs.iter().all(|pair| map.image_of(pair.0) == Maybe::Present(pair.1))
    && map.pairs().all(|pair| pairs.contains(&pair)))]
fn claimed_wires(pairs: &[(Wire, Wire)]) -> PartialBijection
{
    let mut map = PartialBijection::new();
    for &(source, image) in pairs {
        map.extend(source, image)
            .expect("the fixture map is injective");
    }
    map
}

#[test]
fn a_spine_pattern_is_strongly_connected()
{
    let spine = diagram(
        3,
        alloc::vec![
            Generator::new(value("f"), wires![0], wires![1]),
            Generator::new(value("g"), wires![1], wires![2]),
        ],
        Interface::new(wires![0], wires![2]),
    );
    assert_eq!(
        Connectivity::StronglyConnected,
        connectivity(&spine),
        "the one input reaches the one output"
    );
    assert_eq!(
        ConvexityWarrant::StronglyConnectedOverAcyclicTarget,
        convexity_warrant(&spine),
        "so its matches are convex without a sweep"
    );
    assert_eq!(
        Connectivity::StronglyConnected,
        connectivity(&bare_wire_pattern()),
        "and a bare wire reaches itself, so the identity pattern keeps the discharge"
    );
}

#[test]
fn a_disconnected_pattern_is_not_strongly_connected()
{
    assert_eq!(
        Connectivity::Disconnected {
            from: Wire::from(0),
            to: Wire::from(3),
        },
        connectivity(&disconnected_pattern()),
        "the first component's input reaches nothing in the second"
    );
    assert_eq!(
        ConvexityWarrant::SweptOverTheComplement,
        convexity_warrant(&disconnected_pattern()),
        "so the discharge is lost and the sweep carries the conjunct"
    );
}

#[test]
fn an_arity_mismatch_under_one_label_is_not_an_embedding()
{
    // One label at two arities is two generators. Both directions and both
    // sides are checked: a check on one would let the other's port list be
    // truncated to the shorter of the two.
    let one_out = diagram(
        2,
        alloc::vec![Generator::new(value("f"), wires![0], wires![1])],
        Interface::new(wires![0], wires![1]),
    );
    let two_out = diagram(
        3,
        alloc::vec![Generator::new(value("f"), wires![0], wires![1, 2])],
        Interface::new(wires![0], wires![1, 2]),
    );
    let two_in = diagram(
        3,
        alloc::vec![Generator::new(value("f"), wires![0, 1], wires![2])],
        Interface::new(wires![0, 1], wires![2]),
    );
    for (pattern, target, reason) in [
        (
            &one_out,
            &two_out,
            "a one-output pattern does not embed into a two-output generator of that name",
        ),
        (&two_out, &one_out, "nor the other way round"),
        (
            &one_out,
            &two_in,
            "and the source side is checked as well as the target side",
        ),
    ] {
        let matching = embeddings(pattern, target, budget()).expect("the search fits the budget");
        assert_eq!(MatchCount::from(0), matching.admitted_count(), "{reason}");
    }
}

#[test]
fn a_multi_output_pattern_embeds()
{
    let matching = embeddings(&multi_output_pattern(), &multi_output_target(), budget())
        .expect("the search fits the budget");
    assert_eq!(
        MatchCount::from(1),
        matching.admitted_count(),
        "the multi-output pattern occurs exactly once in the target"
    );
    let embedding = first(&matching);
    assert_eq!(
        &edges![1, 2, 3][..],
        embedding.image(),
        "covering the target's f, g and h, in pattern order"
    );
    assert_eq!(
        embedding.image_of(Edge::from(0)),
        Maybe::Present(Edge::from(1))
    );
    assert_eq!(
        embedding.image_of(Edge::from(2)),
        Maybe::Present(Edge::from(3))
    );
    assert_eq!(
        embedding.image_of(Edge::from(3)),
        Maybe::Absent(embedding_image::Absent::OutOfRange)
    );
    assert_eq!(
        Maybe::Present(Wire::from(1)),
        embedding.wires().image_of(Wire::from(0)),
        "the input port lands on the wire below the generator above it"
    );
}

#[test]
fn a_multi_root_pattern_embeds()
{
    let matching = embeddings(&multi_root_pattern(), &multi_root_target(), budget())
        .expect("the search fits the budget");
    assert_eq!(
        MatchCount::from(1),
        matching.admitted_count(),
        "two roots are seeded from one component and propagated, not recursed into"
    );
    assert_eq!(
        SearchSteps::from(24),
        matching.steps(),
        "one seed for the multi-root component fixes the exact search cost"
    );
    let embedding = first(&matching);
    assert_eq!(
        &edges![2, 3, 4][..],
        embedding.image(),
        "the image is the pattern's occurrence, not the context around it"
    );
    assert_eq!(
        alloc::vec![
            (Wire::from(0), Wire::from(1)),
            (Wire::from(1), Wire::from(3))
        ],
        embedding.seam().inputs().pairs().collect::<Vec<_>>(),
        "both roots' input ports land below the generators above them"
    );
}

#[test]
fn a_reconvergent_pattern_embeds()
{
    let matching = embeddings(&reconvergent_pattern(), &reconvergent_target(), budget())
        .expect("the search fits the budget");
    assert_eq!(
        MatchCount::from(1),
        matching.admitted_count(),
        "reconvergence is matched, not refused"
    );
    assert_eq!(
        &edges![1, 2][..],
        first(&matching).image(),
        "the two rejoining wires are matched as one pair of generators"
    );
}

#[test]
fn a_disconnected_pattern_embeds_component_by_component()
{
    // Two components, two seeds: the first lands on either `a`, which is the
    // branching the per-component seed exists to enumerate.
    let matching = embeddings(&disconnected_pattern(), &two_admission_target(), budget())
        .expect("the search fits the budget");
    assert_eq!(
        MatchCount::from(2),
        matching.admitted_count(),
        "one embedding per choice of image for the first component"
    );
    assert_eq!(
        alloc::vec![edges![0, 2].to_vec(), edges![1, 2].to_vec()],
        images(&matching),
        "in target generator order, deterministically"
    );
}

#[test]
fn a_disconnected_pattern_does_not_match_a_wire_that_joins_it()
{
    // The pattern asks for two generators with no wire between them; a target
    // joining them would need the match to identify two pattern wires.
    let matching = embeddings(&disconnected_pattern(), &joined_target(), budget())
        .expect("the search fits the budget");
    assert_eq!(
        MatchCount::from(0),
        matching.admitted_count(),
        "identifying the two components' wires is not an embedding"
    );
    assert_eq!(
        MatchCount::from(0),
        matching.refused_count(),
        "and it is no candidate at all, not a convexity failure"
    );
}

#[test]
fn two_components_never_claim_one_generator()
{
    let pattern = diagram(
        4,
        alloc::vec![
            Generator::new(value("a"), wires![0], wires![1]),
            Generator::new(value("a"), wires![2], wires![3]),
        ],
        Interface::new(wires![0, 2], wires![1, 3]),
    );
    let target = diagram(
        2,
        alloc::vec![Generator::new(value("a"), wires![0], wires![1])],
        Interface::new(wires![0], wires![1]),
    );
    let matching = embeddings(&pattern, &target, budget()).expect("the search fits the budget");
    assert_eq!(
        MatchCount::from(0),
        matching.admitted_count(),
        "an embedding is injective on generators, so one target generator serves one component"
    );
}

#[test]
fn two_port_free_components_never_claim_one_generator()
{
    // Where a generator has a port, wire injectivity implies generator
    // injectivity. A point has none, so it is the case the generator-level
    // check carries alone.
    let one = diagram(
        0,
        alloc::vec![Generator::new(value("s"), wires![], wires![])],
        Interface::default(),
    );
    assert_eq!(
        MatchCount::from(0),
        embeddings(&two_points(), &one, budget())
            .expect("the search fits the budget")
            .admitted_count(),
        "one target generator cannot serve two pattern generators"
    );
    assert_eq!(
        MatchCount::from(2),
        embeddings(&two_points(), &two_points(), budget())
            .expect("the search fits the budget")
            .admitted_count(),
        "and with two of them both orderings are embeddings"
    );
}

#[test]
fn port_order_is_preserved_so_a_swapped_target_is_not_a_match()
{
    // The reconvergent pattern's own shape with `g`'s two sources swapped.
    let swapped = diagram(
        4,
        alloc::vec![
            Generator::new(value("f"), wires![0], wires![1, 2]),
            Generator::new(value("g"), wires![2, 1], wires![3]),
        ],
        Interface::new(wires![0], wires![3]),
    );
    let matching = embeddings(&reconvergent_pattern(), &swapped, budget())
        .expect("the search fits the budget");
    assert_eq!(
        MatchCount::from(0),
        matching.admitted_count(),
        "port order within a generator is carried, so the swap is another diagram"
    );
}

#[test]
fn the_blocking_shape_is_refused_on_the_convexity_conjunct()
{
    // Two images on disjoint generator sets that still interfere: a directed
    // path runs out of one and into the other through a generator neither
    // covers. Disjoint supports are not independence once matches are convex.
    let matching = embeddings(&disconnected_pattern(), &blocking_target(), budget())
        .expect("the search fits the budget");
    assert_eq!(
        MatchCount::from(0),
        matching.admitted_count(),
        "the candidate embeds structurally and is still not a legal match"
    );
    assert_eq!(
        MatchCount::from(1),
        matching.refused_count(),
        "and it is refused rather than silently dropped"
    );
    let refusal = matching.refused().first().expect("the refusal is recorded");
    assert_eq!(
        &edges![0, 2][..],
        refusal.image(),
        "naming the image it would have had"
    );
    assert_eq!(
        Wire::from(1),
        refusal.escape(),
        "the wire the path leaves the image on"
    );
    assert_eq!(
        Edge::from(1),
        refusal.through(),
        "the generator outside the image it runs through"
    );
    assert_eq!(
        Wire::from(2),
        refusal.re_entry(),
        "and the wire it re-enters on"
    );
}

#[test]
fn the_sweep_starts_from_every_image_output()
{
    // The blocking shape listed so the escape leaves from the image's second
    // output: `a`'s dead-end output is tried first. A sweep that stopped after
    // one output would admit a non-convex match, the unsound direction.
    let blocked_late = diagram(
        4,
        alloc::vec![
            Generator::new(value("a"), wires![2], wires![3]),
            Generator::new(value("c"), wires![1], wires![2]),
            Generator::new(value("b"), wires![0], wires![1]),
        ],
        Interface::new(wires![0], wires![3]),
    );
    let matching = embeddings(&disconnected_pattern(), &blocked_late, budget())
        .expect("the search fits the budget");
    assert_eq!(
        MatchCount::from(0),
        matching.admitted_count(),
        "the escape is found although it leaves from the later image output"
    );
    let refusal = matching.refused().first().expect("the refusal is recorded");
    assert_eq!(
        (Wire::from(1), Edge::from(1), Wire::from(2)),
        (refusal.escape(), refusal.through(), refusal.re_entry()),
        "leaving on the second output, through the generator neither image covers, into the other input"
    );
}

#[test]
fn the_sweep_follows_a_path_through_more_than_one_outside_generator()
{
    // Two intervening generators: the intermediate wire is no image input, so
    // a walk reading only the escape wire's direct successors would admit.
    let blocked_deep = diagram(
        5,
        alloc::vec![
            Generator::new(value("a"), wires![0], wires![1]),
            Generator::new(value("c0"), wires![1], wires![2]),
            Generator::new(value("c1"), wires![2], wires![3]),
            Generator::new(value("b"), wires![3], wires![4]),
        ],
        Interface::new(wires![0], wires![4]),
    );
    let matching = embeddings(&disconnected_pattern(), &blocked_deep, budget())
        .expect("the search fits the budget");
    assert_eq!(
        MatchCount::from(0),
        matching.admitted_count(),
        "a two-generator detour is still a detour"
    );
    let refusal = matching.refused().first().expect("the refusal is recorded");
    assert_eq!(
        (Wire::from(1), Edge::from(2), Wire::from(3)),
        (refusal.escape(), refusal.through(), refusal.re_entry()),
        "the named generator is the last one outside the image, so the walk was transitive"
    );
}

#[test]
fn a_bare_wire_pattern_embeds_on_every_target_wire()
{
    // The identity pattern is seeded on the target's wires: every wire is one
    // embedding and nothing else is, which pins completeness and the range.
    let target = multi_output_target();
    let matching =
        embeddings(&bare_wire_pattern(), &target, budget()).expect("the search fits the budget");
    assert_eq!(
        MatchCount::from(usize::from(target.wire_count())),
        matching.admitted_count(),
        "one embedding per target wire"
    );
    let mut landed: Vec<Wire> = Vec::new();
    for embedding in matching.admitted() {
        assert!(
            embedding.image().is_empty(),
            "the generator image is empty, so convexity is vacuous"
        );
        let Maybe::Present(image) = embedding.wires().image_of(Wire::from(0))
        else {
            panic!("the bare wire is mapped");
        };
        landed.push(image);
    }
    assert_eq!(
        target.wire_count().wires().collect::<Vec<_>>(),
        landed,
        "onto every declared target wire, in wire order"
    );
}

#[test]
fn the_empty_pattern_embeds_exactly_once()
{
    let matching =
        embeddings(&empty(), &multi_output_target(), budget()).expect("the search fits the budget");
    assert_eq!(
        MatchCount::from(1),
        matching.admitted_count(),
        "the empty pattern embeds once, by the empty map"
    );
    let embedding = first(&matching);
    assert!(embedding.image().is_empty(), "with an empty image");
    assert_eq!(
        PairCount::from(0),
        embedding.wires().pair_count(),
        "and an empty wire map"
    );
}

#[test]
fn the_same_image_is_admitted_without_the_blocking_generator()
{
    // The blocking fixture's twin, differing in one generator outside the
    // image: a check that read only the image, or a target with its complement
    // cut away, would admit both.
    let unblocked = diagram(
        4,
        alloc::vec![
            Generator::new(value("a"), wires![0], wires![1]),
            Generator::new(value("b"), wires![2], wires![3]),
        ],
        Interface::new(wires![0, 2], wires![1, 3]),
    );
    let matching = embeddings(&disconnected_pattern(), &unblocked, budget())
        .expect("the search fits the budget");
    assert_eq!(
        MatchCount::from(1),
        matching.admitted_count(),
        "with the intervening generator gone the same image is convex"
    );
    assert_eq!(
        MatchCount::from(0),
        matching.refused_count(),
        "and nothing is refused"
    );
    assert_eq!(
        ConvexityWarrant::SweptOverTheComplement,
        first(&matching).convexity(),
        "the pattern is not strongly connected, so the sweep granted it"
    );
}

#[test]
fn a_cut_open_verdict_does_not_travel_to_the_re_closed_form()
{
    // A body with one delayed back-edge, cut open: `f` runs from the cut end
    // d⁻ to an internal wire, and `g` takes the body input and that wire to the
    // body output and the cut end d⁺. Cut open, the image {f, g} is convex.
    let cut_open = || {
        diagram(
            5,
            alloc::vec![
                Generator::new(value("f"), wires![1], wires![2]),
                Generator::new(value("g"), wires![0, 2], wires![3, 4]),
            ],
            Interface::new(wires![0, 1], wires![3, 4]),
        )
    };
    let matching = embeddings_by_sweep(&cut_open(), &cut_open(), budget())
        .expect("the search fits the budget");
    assert_eq!(
        MatchCount::from(1),
        matching.admitted_count(),
        "the cut-open form admits the match and the sweep finds no escape"
    );
    // Re-closing adds the edge from d⁺ back to d⁻: from an output of the image
    // to an input of it. The re-closed form is refused as a target outright,
    // so the cut-open verdict cannot be read there.
    let re_closed = Wiring::assemble(
        WireCount::from(5),
        alloc::vec![
            Generator::new(value("f"), wires![1], wires![2]),
            Generator::new(value("g"), wires![0, 2], wires![3, 4]),
            Generator::new(value("delay"), wires![4], wires![1]),
        ],
        Interface::new(wires![0], wires![3]),
    );
    assert_eq!(
        Err(WiringObstruction::DirectedCycle {
            through: Edge::from(0)
        }),
        re_closed,
        "re-closing the delay leaves the acyclic fragment, so the cut-open form is the only target"
    );
}

#[test]
fn the_discharge_and_the_sweep_agree_where_both_apply()
{
    // The discharge skips the sweep, which is honest only if running it would
    // agree: this is that measurement, against the sweep as external oracle.
    let pairs = alloc::vec![
        Against {
            pattern: multi_output_pattern(),
            target: multi_output_target(),
        },
        Against {
            pattern: reconvergent_pattern(),
            target: reconvergent_target(),
        },
        Against {
            pattern: multi_output_pattern(),
            target: reconvergent_target(),
        },
        Against {
            pattern: reconvergent_pattern(),
            target: multi_output_target(),
        },
        Against {
            pattern: multi_root_pattern(),
            target: multi_root_target(),
        },
        // Three shapes on which the discharge is granted for a reason other
        // than one connected piece with ports at both ends, where an argument
        // for it is likeliest wrong.
        //
        // One: strongly connected by its boundary while two components as a
        // graph; `s → t` has no open port, so it contributes neither an image
        // input nor an image output.
        Against {
            pattern: diagram(
                3,
                alloc::vec![
                    Generator::new(value("a"), wires![0], wires![1]),
                    Generator::new(value("s"), wires![], wires![2]),
                    Generator::new(value("t"), wires![2], wires![]),
                ],
                Interface::new(wires![0], wires![1]),
            ),
            target: diagram(
                5,
                alloc::vec![
                    Generator::new(value("e"), wires![0], wires![1]),
                    Generator::new(value("a"), wires![1], wires![2]),
                    Generator::new(value("s"), wires![], wires![3]),
                    Generator::new(value("t"), wires![3], wires![]),
                    Generator::new(value("k"), wires![2], wires![4]),
                ],
                Interface::new(wires![0], wires![4]),
            ),
        },
        // Two: vacuous on the output side, with no image output to leave from.
        Against {
            pattern: diagram(
                1,
                alloc::vec![Generator::new(value("t"), wires![0], wires![])],
                Interface::new(wires![0], wires![]),
            ),
            target: diagram(
                2,
                alloc::vec![
                    Generator::new(value("e"), wires![0], wires![1]),
                    Generator::new(value("t"), wires![1], wires![]),
                ],
                Interface::new(wires![0], wires![]),
            ),
        },
        // Three: vacuous on the input side, with no image input to return to.
        Against {
            pattern: diagram(
                1,
                alloc::vec![Generator::new(value("s"), wires![], wires![0])],
                Interface::new(wires![], wires![0]),
            ),
            target: diagram(
                2,
                alloc::vec![
                    Generator::new(value("s"), wires![], wires![0]),
                    Generator::new(value("k"), wires![0], wires![1]),
                ],
                Interface::new(wires![], wires![1]),
            ),
        },
    ];
    let mut total: usize = 0;
    for pair in &pairs {
        assert_eq!(
            Connectivity::StronglyConnected,
            connectivity(&pair.pattern),
            "the discharge applies only to a strongly connected pattern"
        );
        let discharged =
            embeddings(&pair.pattern, &pair.target, budget()).expect("the search fits the budget");
        let swept = embeddings_by_sweep(&pair.pattern, &pair.target, budget())
            .expect("the audit search fits the budget");
        total = total.saturating_add(usize::from(discharged.admitted_count()));
        assert_eq!(
            images(&swept),
            images(&discharged),
            "the discharged route admits exactly what the sweep admits"
        );
        assert_eq!(
            MatchCount::from(0),
            swept.refused_count(),
            "and the sweep refuses nothing the discharge kept"
        );
        assert!(
            discharged
                .admitted()
                .iter()
                .all(|embedding| embedding.convexity()
                    == ConvexityWarrant::StronglyConnectedOverAcyclicTarget),
            "the discharged route records the warrant it was granted under"
        );
        assert!(
            swept
                .admitted()
                .iter()
                .all(|embedding| embedding.convexity() == ConvexityWarrant::SweptOverTheComplement),
            "and the audit route records that it swept"
        );
    }
    assert_eq!(
        6_usize, total,
        "not vacuous: six pairs contribute one occurrence each, the two crossed pairs none"
    );
}

#[test]
fn an_embedding_carries_its_seam_as_a_pair_of_partial_bijections()
{
    let matching = embeddings(&reconvergent_pattern(), &reconvergent_target(), budget())
        .expect("the search fits the budget");
    let seam = first(&matching).seam();
    assert_eq!(
        alloc::vec![(Wire::from(0), Wire::from(1))],
        seam.inputs().pairs().collect::<Vec<_>>(),
        "the input half maps the pattern's one input port"
    );
    assert_eq!(
        alloc::vec![(Wire::from(3), Wire::from(4))],
        seam.outputs().pairs().collect::<Vec<_>>(),
        "and the output half its one output port, kept apart"
    );
}

#[test]
fn an_exhausted_budget_declines_rather_than_truncating()
{
    assert_eq!(
        Err(MatchObstruction::BudgetExhausted {
            consumed: SearchSteps::from(2)
        }),
        embeddings(
            &reconvergent_pattern(),
            &reconvergent_target(),
            MatchBudget::from(2)
        ),
        "the decline names what it spent rather than returning a partial enumeration"
    );
}

/// Whether the embedding matcher finds an embedding anchoring the pattern's
/// cut wire on the target's: the one-sided term match, read on diagrams.
///
/// # Specification
/// - requires: the finite search fits the fixture budget.
/// - ensures: accepts exactly when an embedding preserves the two cut wires.
/// - panics: if the fixture search exhausts its budget.
///
/// # Adequacy
/// - hypothesis: L2 — the independent one-sided term matcher agrees on every
///   spine fixture, including polarity-sensitive seams, with both verdicts
///   represented. Ignoring the cut anchor or admitting a larger pattern
///   differs. The predicate checks necessary embedding cardinalities without
///   running a second allocating search; the differential witnesses establish
///   the full decision.
/// - witness: `matching::tests::the_embedding_matcher_agrees_with_the_one_sided_matcher_on_the_spine`
#[spec(ensures: |result| result == SubstitutionDecision::from(false)
    || (pattern.wiring().edge_count() <= target.wiring().edge_count() && pattern.wiring().wire_count() <= target.wiring().wire_count()))]
fn anchored_decision(
    pattern: &SpineReading,
    target: &SpineReading,
) -> SubstitutionDecision
{
    let matching = embeddings(pattern.wiring(), target.wiring(), budget())
        .expect("the search fits the budget");
    let anchored = matching
        .admitted()
        .iter()
        .any(|embedding| embedding.wires().image_of(pattern.cut()) == Maybe::Present(target.cut()));
    SubstitutionDecision::from(anchored)
}

/// `⟨r | seam(; r)⟩`: one name worn at both polarities.
///
/// # Specification
/// trivial.
fn seam_shape() -> CmdPat
{
    CmdPat::cut(
        Polarity::Positive,
        ProdPat::meta("r"),
        ConsPat::op("seam", [], ConsPat::meta("r")),
    )
}

#[test]
fn the_embedding_matcher_agrees_with_the_one_sided_matcher_on_the_spine()
{
    let zero = || ProdPat::ctor("Zero", []);
    let succ_add = || {
        CmdPat::cut(
            Polarity::Positive,
            ProdPat::ctor("Succ", [ProdPat::meta("m")]),
            ConsPat::op("add", [ProdPat::meta("n")], ConsPat::meta("alpha")),
        )
    };
    let succ_zero_add = || {
        CmdPat::cut(
            Polarity::Positive,
            ProdPat::ctor("Succ", [zero()]),
            ConsPat::op("add", [zero()], ConsPat::top()),
        )
    };
    let zero_add = || {
        CmdPat::cut(
            Polarity::Positive,
            zero(),
            ConsPat::op("add", [zero()], ConsPat::top()),
        )
    };
    let rows = alloc::vec![
        Against {
            pattern: succ_add(),
            target: succ_zero_add(),
        },
        Against {
            pattern: succ_add(),
            target: zero_add(),
        },
        Against {
            pattern: CmdPat::cut(
                Polarity::Positive,
                ProdPat::meta("m"),
                ConsPat::op("add", [ProdPat::meta("n")], ConsPat::meta("alpha")),
            ),
            target: succ_zero_add(),
        },
        Against {
            pattern: CmdPat::cut(
                Polarity::Positive,
                ProdPat::meta("m"),
                ConsPat::meta("alpha")
            ),
            target: succ_zero_add(),
        },
        Against {
            pattern: CmdPat::cut(Polarity::Positive, zero(), ConsPat::meta("alpha")),
            target: succ_zero_add(),
        },
        Against {
            pattern: CmdPat::cut(Polarity::Positive, ProdPat::meta("m"), ConsPat::top()),
            target: zero_add(),
        },
        Against {
            pattern: zero_add(),
            target: zero_add(),
        },
        Against {
            pattern: CmdPat::cut(
                Polarity::Positive,
                ProdPat::meta("m"),
                ConsPat::frame("Succ", ConsPat::meta("alpha")),
            ),
            target: CmdPat::cut(
                Polarity::Positive,
                zero(),
                ConsPat::frame("Succ", ConsPat::top())
            ),
        },
        Against {
            pattern: CmdPat::cut(
                Polarity::Positive,
                ProdPat::meta("m"),
                ConsPat::frame("Succ", ConsPat::meta("alpha")),
            ),
            target: zero_add(),
        },
        Against {
            pattern: CmdPat::cut(
                Polarity::Positive,
                ProdPat::ctor("Succ", [ProdPat::meta("m")]),
                ConsPat::meta("alpha"),
            ),
            target: CmdPat::cut(
                Polarity::Positive,
                zero(),
                ConsPat::frame("Succ", ConsPat::top())
            ),
        },
        // These two pin the label's sort: a return-side frame `K⁻(c)` and a
        // nullary operation frame `f(; c)` wear one name at one arity and are
        // different generators. A name-only label would match each against the
        // other, anchored, while the one-sided matcher refuses both.
        Against {
            pattern: CmdPat::cut(
                Polarity::Positive,
                ProdPat::meta("m"),
                ConsPat::frame("Succ", ConsPat::meta("alpha")),
            ),
            target: CmdPat::cut(
                Polarity::Positive,
                zero(),
                ConsPat::op("Succ", [], ConsPat::top())
            ),
        },
        Against {
            pattern: CmdPat::cut(
                Polarity::Positive,
                ProdPat::meta("m"),
                ConsPat::op("Succ", [], ConsPat::meta("alpha")),
            ),
            target: CmdPat::cut(
                Polarity::Positive,
                zero(),
                ConsPat::frame("Succ", ConsPat::top())
            ),
        },
        // The seam shape, where the reading's ruling and the oracle's keying
        // by name and category must agree: the producer `r` and the consumer
        // `r` are two metavariables to the substitution and two ports to the
        // reading. A reading of one node would make the seam a cycle and fail
        // to read at all.
        Against {
            pattern: seam_shape(),
            target: CmdPat::cut(
                Polarity::Positive,
                zero(),
                ConsPat::op("seam", [], ConsPat::top())
            ),
        },
        Against {
            pattern: seam_shape(),
            target: seam_shape(),
        },
        Against {
            pattern: seam_shape(),
            target: CmdPat::cut(
                Polarity::Positive,
                ProdPat::meta("m"),
                ConsPat::op("seam", [], ConsPat::meta("alpha")),
            ),
        },
        Against {
            pattern: seam_shape(),
            target: zero_add(),
        },
    ];
    let mut agreed: usize = 0;
    for row in &rows {
        let mut subst = Subst::new();
        let by_term = match_cmd(&row.pattern, &row.target, &mut subst);
        let pattern = read_spine(&row.pattern).expect("the fixture pattern is linear");
        let target = read_spine(&row.target).expect("the fixture target is linear");
        assert_eq!(
            by_term,
            anchored_decision(&pattern, &target),
            "the cut-anchored embedding decides what the one-sided matcher decides"
        );
        if bool::from(by_term) {
            agreed = agreed.saturating_add(1);
        }
    }
    assert_eq!(
        16_usize,
        rows.len(),
        "the table is the one this differential was written against"
    );
    assert_eq!(
        8_usize, agreed,
        "and it separates both verdicts, three seam rows among the matches"
    );
}

#[test]
fn the_searches_certificates_verify_against_their_own_diagrams()
{
    // The reader accepts exactly what the search admits, across every fixture
    // family, and returns the certificate's own warrant.
    let cases = alloc::vec![
        Against {
            pattern: multi_output_pattern(),
            target: multi_output_target(),
        },
        Against {
            pattern: multi_root_pattern(),
            target: multi_root_target(),
        },
        Against {
            pattern: reconvergent_pattern(),
            target: reconvergent_target(),
        },
        Against {
            pattern: disconnected_pattern(),
            target: two_admission_target(),
        },
        Against {
            pattern: bare_wire_pattern(),
            target: multi_output_target(),
        },
        Against {
            pattern: empty(),
            target: multi_root_target(),
        },
    ];
    let mut checked: usize = 0;
    for case in &cases {
        let matching =
            embeddings(&case.pattern, &case.target, budget()).expect("the search fits the budget");
        for certificate in matching.admitted() {
            assert_eq!(
                Ok(certificate.convexity()),
                certificate.check(&case.pattern, &case.target),
                "a certificate the search issued verifies against its own diagrams"
            );
            checked = checked.saturating_add(1);
        }
    }
    assert_eq!(
        13_usize, checked,
        "one each for multi-output, multi-root and reconvergent, two disconnected, seven \
         bare-wire images and the empty embedding"
    );
}

#[test]
fn a_certificate_with_a_forged_image_length_is_refused()
{
    let pattern = multi_root_pattern();
    let target = multi_root_target();
    let matching = embeddings(&pattern, &target, budget()).expect("the search fits the budget");
    let certificate = first(&matching);
    let short = Embedding::claim(
        certificate.image()[.. 2].to_vec(),
        certificate.wires().clone(),
        certificate.seam().clone(),
        certificate.convexity(),
    );
    assert_eq!(
        Err(EmbeddingObstruction::ImageLength {
            expected: EdgeCount::from(3),
            claimed: EdgeCount::from(2),
        }),
        short.check(&pattern, &target),
        "one image slot per pattern generator is the certificate's own shape"
    );
    let mut longer = certificate.image().to_vec();
    longer.push(Edge::from(5));
    let overlong = Embedding::claim(
        longer,
        certificate.wires().clone(),
        certificate.seam().clone(),
        certificate.convexity(),
    );
    assert_eq!(
        Err(EmbeddingObstruction::ImageLength {
            expected: EdgeCount::from(3),
            claimed: EdgeCount::from(4),
        }),
        overlong.check(&pattern, &target),
        "in either direction"
    );
}

#[test]
fn a_certificate_imaged_outside_the_target_is_refused()
{
    let pattern = multi_root_pattern();
    let target = multi_root_target();
    let matching = embeddings(&pattern, &target, budget()).expect("the search fits the budget");
    let certificate = first(&matching);
    let claim = Embedding::claim(
        edges![2, 3, 99],
        certificate.wires().clone(),
        certificate.seam().clone(),
        certificate.convexity(),
    );
    assert_eq!(
        Err(EmbeddingObstruction::ImageOutOfRange {
            at: Edge::from(2),
            claimed: Edge::from(99),
        }),
        claim.check(&pattern, &target),
        "an image the target does not hold is not an embedding"
    );
}

#[test]
fn a_certificate_with_a_relabelled_image_is_refused()
{
    let pattern = reconvergent_pattern();
    let target = reconvergent_target();
    let matching = embeddings(&pattern, &target, budget()).expect("the search fits the budget");
    let certificate = first(&matching);
    let claim = Embedding::claim(
        edges![0, 2],
        certificate.wires().clone(),
        certificate.seam().clone(),
        certificate.convexity(),
    );
    assert_eq!(
        Err(EmbeddingObstruction::LabelMismatch {
            at: Edge::from(0),
            claimed: Edge::from(0),
        }),
        claim.check(&pattern, &target),
        "the target's `e` wears another label than the pattern's `f`"
    );
}

#[test]
fn a_certificate_with_an_arity_wrong_image_is_refused()
{
    let pattern = diagram(
        2,
        alloc::vec![Generator::new(value("f"), wires![0], wires![1])],
        Interface::new(wires![0], wires![1]),
    );
    let target = diagram(
        3,
        alloc::vec![Generator::new(value("f"), wires![0], wires![1, 2])],
        Interface::new(wires![0], wires![1, 2]),
    );
    let claim = Embedding::claim(
        edges![0],
        claimed_wires(&[
            (Wire::from(0), Wire::from(0)),
            (Wire::from(1), Wire::from(1)),
        ]),
        Seam::default(),
        ConvexityWarrant::StronglyConnectedOverAcyclicTarget,
    );
    assert_eq!(
        Err(EmbeddingObstruction::ArityMismatch {
            at: Edge::from(0),
            claimed: Edge::from(0),
        }),
        claim.check(&pattern, &target),
        "the label agrees and the arity does not"
    );
}

#[test]
fn a_certificate_with_a_shifted_wire_map_is_refused()
{
    let pattern = reconvergent_pattern();
    let target = reconvergent_target();
    let matching = embeddings(&pattern, &target, budget()).expect("the search fits the budget");
    let certificate = first(&matching);
    // The real map sends the input wire 0 below `e`; one wire lower
    // contradicts the claimed image's own incidence.
    let claim = Embedding::claim(
        certificate.image().to_vec(),
        claimed_wires(&[
            (Wire::from(0), Wire::from(0)),
            (Wire::from(1), Wire::from(2)),
            (Wire::from(2), Wire::from(3)),
            (Wire::from(3), Wire::from(4)),
        ]),
        certificate.seam().clone(),
        certificate.convexity(),
    );
    assert_eq!(
        Err(EmbeddingObstruction::IncidenceMismatch {
            at: Edge::from(0),
            wire: Wire::from(0),
            expected: Wire::from(1),
        }),
        claim.check(&pattern, &target),
        "the wire map must agree with the claimed image's ports, in order"
    );
}

#[test]
fn a_certificate_sharing_one_generator_is_refused()
{
    // The port-free case, where generator injectivity carries alone: two
    // points claimed onto one.
    let claim = Embedding::claim(
        edges![0, 0],
        PartialBijection::new(),
        Seam::default(),
        ConvexityWarrant::StronglyConnectedOverAcyclicTarget,
    );
    assert_eq!(
        Err(EmbeddingObstruction::NonInjectiveImage {
            first: Edge::from(0),
            second: Edge::from(1),
            claimed: Edge::from(0),
        }),
        claim.check(&two_points(), &two_points()),
        "one target generator cannot serve two pattern generators"
    );
}

#[test]
fn a_certificate_leaving_a_wire_unmapped_is_refused()
{
    // The bare wire is the one wire no incidence covers, so totality is
    // checked in its own right there.
    let claim = Embedding::claim(
        edges![],
        PartialBijection::new(),
        Seam::default(),
        ConvexityWarrant::StronglyConnectedOverAcyclicTarget,
    );
    assert_eq!(
        Err(EmbeddingObstruction::WireUnmapped {
            wire: Wire::from(0)
        }),
        claim.check(&bare_wire_pattern(), &multi_output_target()),
        "a map forgetting the pattern's one wire is no embedding"
    );
}

#[test]
fn a_certificate_imaging_a_wire_outside_the_target_is_refused()
{
    let image = claimed_wires(&[(Wire::from(0), Wire::from(7))]);
    let claim = Embedding::claim(
        edges![],
        image.clone(),
        Seam::new(image.clone(), image),
        ConvexityWarrant::StronglyConnectedOverAcyclicTarget,
    );
    assert_eq!(
        Err(EmbeddingObstruction::WireImageOutOfRange {
            wire: Wire::from(0),
            claimed: Wire::from(7),
        }),
        claim.check(&bare_wire_pattern(), &multi_output_target()),
        "the target declares seven wires, so wire 7 is not one of them"
    );
}

#[test]
fn a_certificate_mapping_wires_outside_the_pattern_is_refused()
{
    // With totality holding, extra pairs are the only way the width differs.
    let claim = Embedding::claim(
        edges![],
        claimed_wires(&[
            (Wire::from(0), Wire::from(0)),
            (Wire::from(5), Wire::from(5)),
        ]),
        Seam::default(),
        ConvexityWarrant::StronglyConnectedOverAcyclicTarget,
    );
    assert_eq!(
        Err(EmbeddingObstruction::WireMapOverwide {
            expected: WireCount::from(1),
            claimed: PairCount::from(2),
        }),
        claim.check(&bare_wire_pattern(), &multi_output_target()),
        "the map's domain is exactly the pattern's wires"
    );
}

#[test]
fn a_certificate_with_a_forged_seam_is_refused()
{
    let pattern = multi_root_pattern();
    let target = multi_root_target();
    let matching = embeddings(&pattern, &target, budget()).expect("the search fits the budget");
    let certificate = first(&matching);
    let claim = Embedding::claim(
        certificate.image().to_vec(),
        certificate.wires().clone(),
        Seam::new(
            PartialBijection::new(),
            certificate.seam().outputs().clone(),
        ),
        certificate.convexity(),
    );
    assert_eq!(
        Err(EmbeddingObstruction::SeamMismatch {
            half: SeamHalf::Inputs,
        }),
        claim.check(&pattern, &target),
        "the seam is the wire map's own restriction, so a forgery disagrees with it"
    );
    let outputs_forged = Embedding::claim(
        certificate.image().to_vec(),
        certificate.wires().clone(),
        Seam::new(certificate.seam().inputs().clone(), PartialBijection::new()),
        certificate.convexity(),
    );
    assert_eq!(
        Err(EmbeddingObstruction::SeamMismatch {
            half: SeamHalf::Outputs,
        }),
        outputs_forged.check(&pattern, &target),
        "and the output half is checked as well as the input half"
    );
}

#[test]
fn a_certificate_with_an_unearned_warrant_is_refused()
{
    // The disconnected pattern's matches are swept, never discharged; claiming
    // the discharge for it claims a warrant it does not earn, however legal
    // the image.
    let pattern = disconnected_pattern();
    let target = two_admission_target();
    let matching = embeddings(&pattern, &target, budget()).expect("the search fits the budget");
    let certificate = first(&matching);
    assert_eq!(
        ConvexityWarrant::SweptOverTheComplement,
        certificate.convexity(),
        "the search itself swept this one"
    );
    let claim = Embedding::claim(
        certificate.image().to_vec(),
        certificate.wires().clone(),
        certificate.seam().clone(),
        ConvexityWarrant::StronglyConnectedOverAcyclicTarget,
    );
    assert_eq!(
        Err(EmbeddingObstruction::UnearnedWarrant {
            connectivity: Connectivity::Disconnected {
                from: Wire::from(0),
                to: Wire::from(3),
            },
        }),
        claim.check(&pattern, &target),
        "the first component's input reaches nothing in the second"
    );
}

#[test]
fn a_non_convex_certificate_is_refused_with_the_offending_path()
{
    // The blocking shape, forged as a certificate claiming the swept warrant:
    // the reader's own sweep finds the path the search's refusal names.
    let identity = claimed_wires(&[
        (Wire::from(0), Wire::from(0)),
        (Wire::from(1), Wire::from(1)),
        (Wire::from(2), Wire::from(2)),
        (Wire::from(3), Wire::from(3)),
    ]);
    let claim = Embedding::claim(
        edges![0, 2],
        identity,
        Seam::new(
            claimed_wires(&[
                (Wire::from(0), Wire::from(0)),
                (Wire::from(2), Wire::from(2)),
            ]),
            claimed_wires(&[
                (Wire::from(1), Wire::from(1)),
                (Wire::from(3), Wire::from(3)),
            ]),
        ),
        ConvexityWarrant::SweptOverTheComplement,
    );
    assert_eq!(
        Err(EmbeddingObstruction::NotConvex {
            escape: Wire::from(1),
            through: Edge::from(1),
            re_entry: Wire::from(2),
        }),
        claim.check(&disconnected_pattern(), &blocking_target()),
        "a structural embedding that is not convex is refused with the path the search names"
    );
}

#[test]
fn a_unique_or_absent_match_reports_no_ambiguity()
{
    let unique = embeddings(&multi_root_pattern(), &multi_root_target(), budget())
        .expect("the search fits the budget");
    assert_eq!(
        Maybe::Absent(ambiguity::Absent::Unique),
        unique.ambiguity(),
        "a unique match needs no discrimination"
    );
    let absent = embeddings(&disconnected_pattern(), &joined_target(), budget())
        .expect("the search fits the budget");
    assert_eq!(
        Maybe::Absent(ambiguity::Absent::Unmatched),
        absent.ambiguity(),
        "and a matchless pattern is unmatched, not ambiguous"
    );
}

#[test]
fn a_multi_admission_reports_its_first_divergences_in_order()
{
    let matching = embeddings(&disconnected_pattern(), &two_admission_target(), budget())
        .expect("the search fits the budget");
    let Maybe::Present(ambiguity) = matching.ambiguity()
    else {
        panic!("two admissions are an ambiguity");
    };
    assert_eq!(
        MatchCount::from(2),
        ambiguity.admissions(),
        "one embedding per image of the first component"
    );
    assert_eq!(
        &[Divergence {
            admitted: AdmittedIndex::from(1),
            discriminator: Discriminator::Generator {
                at: Edge::from(0),
                representative: Edge::from(0),
                variant: Edge::from(1),
            },
        }][..],
        ambiguity.divergences(),
        "the second admission first disagrees on where the first component's generator lands"
    );
}

#[test]
fn a_bare_wire_ambiguity_discriminates_on_the_wire()
{
    // Every embedding has the same empty generator image, so readings can
    // diverge only on the bare wire's image: the wire arm's case.
    let matching = embeddings(&bare_wire_pattern(), &multi_output_target(), budget())
        .expect("the search fits the budget");
    let Maybe::Present(ambiguity) = matching.ambiguity()
    else {
        panic!("seven admissions are an ambiguity");
    };
    assert_eq!(
        MatchCount::from(7),
        ambiguity.admissions(),
        "one per target wire"
    );
    let expected: Vec<Divergence> = (1_usize ..= 6)
        .map(|offset| Divergence {
            admitted: AdmittedIndex::from(offset),
            discriminator: Discriminator::Wire {
                wire: Wire::from(0),
                representative: Wire::from(0),
                variant: Wire::from(offset),
            },
        })
        .collect();
    assert_eq!(
        &*expected,
        ambiguity.divergences(),
        "each later reading sends the bare wire to the next target wire, in order"
    );
}

#[test]
fn two_orderings_of_port_free_generators_diverge_at_the_first_generator()
{
    let matching =
        embeddings(&two_points(), &two_points(), budget()).expect("the search fits the budget");
    let Maybe::Present(ambiguity) = matching.ambiguity()
    else {
        panic!("two orderings are an ambiguity");
    };
    assert_eq!(
        Some(&Discriminator::Generator {
            at: Edge::from(0),
            representative: Edge::from(0),
            variant: Edge::from(1),
        }),
        ambiguity
            .divergences()
            .first()
            .map(|divergence| &divergence.discriminator),
        "the second reading swaps the two points, starting with the first"
    );
}

#[test]
fn budget_accounting_observes_each_step_and_exhaustion()
{
    let start = MatchBudget::from(2);
    let mut remaining = start;
    assert_eq!(remaining.spent_since(start), SearchSteps::from(0));
    assert_eq!(remaining.spend(), Spend::Spent);
    assert_eq!(remaining.spent_since(start), SearchSteps::from(1));
    assert_eq!(remaining.spend(), Spend::Spent);
    assert_eq!(remaining.spent_since(start), SearchSteps::from(2));
    assert_eq!(remaining.spend(), Spend::Exhausted);
    assert_eq!(remaining.spent_since(start), SearchSteps::from(2));
}

#[test]
fn discriminators_skip_equal_prefixes_and_prioritize_generators()
{
    let representative = Embedding::claim(
        edges![0, 2],
        claimed_wires(&[
            (Wire::from(0), Wire::from(0)),
            (Wire::from(1), Wire::from(1)),
        ]),
        Seam::new(PartialBijection::new(), PartialBijection::new()),
        ConvexityWarrant::SweptOverTheComplement,
    );
    assert_eq!(
        first_discriminator(&representative, &representative),
        Maybe::Absent(divergence::Absent::Identical)
    );
    let mut variant = representative.clone();
    variant.image = Box::from(edges![0, 3]);
    variant.wires = claimed_wires(&[
        (Wire::from(0), Wire::from(0)),
        (Wire::from(1), Wire::from(2)),
    ]);
    assert_eq!(
        first_discriminator(&representative, &variant),
        Maybe::Present(Discriminator::Generator {
            at: Edge::from(1),
            representative: Edge::from(2),
            variant: Edge::from(3)
        })
    );
    variant.image = representative.image.clone();
    assert_eq!(
        first_discriminator(&representative, &variant),
        Maybe::Present(Discriminator::Wire {
            wire: Wire::from(1),
            representative: Wire::from(1),
            variant: Wire::from(2)
        })
    );
}

#[test]
fn reachability_keeps_branch_direction_and_reflexivity()
{
    let pattern = multi_output_pattern();
    assert_eq!(
        reachable_from(&pattern, Wire::from(0)),
        wires![0, 1, 2, 3, 4].into_iter().collect()
    );
    assert_eq!(
        reachable_from(&pattern, Wire::from(1)),
        wires![1, 3].into_iter().collect()
    );
    assert_eq!(
        reachable_from(&pattern, Wire::from(9)),
        wires![9].into_iter().collect()
    );
}

#[test]
fn seeds_order_components_before_isolated_wires()
{
    let pattern = diagram(
        5,
        alloc::vec![
            Generator::new(value("f"), wires![0], wires![1]),
            Generator::new(value("point"), wires![], wires![]),
            Generator::new(value("g"), wires![2], wires![3]),
        ],
        Interface::new(wires![0, 2, 4], wires![1, 3, 4]),
    );
    assert_eq!(seeds_of(&pattern), alloc::vec![
        Seed::Generator(Edge::from(0)),
        Seed::Generator(Edge::from(1)),
        Seed::Generator(Edge::from(2)),
        Seed::Wire(Wire::from(4))
    ]);
    assert_eq!(seeds_of(&multi_output_pattern()), alloc::vec![
        Seed::Generator(Edge::from(0))
    ]);
}

#[test]
fn propagation_charges_replays_and_preserves_conflicting_bindings()
{
    let pattern = bare_wire_pattern();
    let target = diagram(2, Vec::new(), Interface::new(wires![0, 1], wires![0, 1]));
    let mut state = Assignment {
        generators: Vec::new(),
        claimed: BTreeSet::new(),
        wires: PartialBijection::new(),
    };
    let mut remaining = MatchBudget::from(3);
    let seed = Pending::Wire(Wire::from(0), Wire::from(0));
    assert_eq!(
        extend(&pattern, &target, &mut state, seed, &mut remaining),
        Extension::Consistent
    );
    assert_eq!(
        extend(&pattern, &target, &mut state, seed, &mut remaining),
        Extension::Consistent
    );
    assert_eq!(remaining, MatchBudget::from(1));
    assert_eq!(
        extend(
            &pattern,
            &target,
            &mut state,
            Pending::Wire(Wire::from(0), Wire::from(1)),
            &mut remaining
        ),
        Extension::Clash
    );
    assert_eq!(
        state.wires.image_of(Wire::from(0)),
        Maybe::Present(Wire::from(0))
    );
    assert_eq!(
        extend(&pattern, &target, &mut state, seed, &mut remaining),
        Extension::Exhausted
    );
    assert_eq!(remaining, MatchBudget::from(0));
}

#[test]
fn admission_drops_incomplete_generator_maps()
{
    let pattern = multi_output_pattern();
    let target = multi_output_target();
    let matching = embeddings_by_sweep(&pattern, &target, budget()).expect("the search fits");
    let embedding = first(&matching);
    let complete = Assignment {
        generators: embedding.image.iter().copied().map(Some).collect(),
        claimed: embedding.image.iter().copied().collect(),
        wires: embedding.wires.clone(),
    };
    let mut incomplete = complete.clone();
    *incomplete
        .generators
        .last_mut()
        .expect("the pattern has generators") = None;
    let admitted = admit(
        &pattern,
        &target,
        alloc::vec![incomplete, complete],
        ConvexityWarrant::SweptOverTheComplement,
        SearchSteps::from(7),
    );
    assert_eq!(admitted.admitted(), core::slice::from_ref(embedding));
    assert!(admitted.refused().is_empty());
    assert_eq!(admitted.steps(), SearchSteps::from(7));
}

#[test]
fn seams_restrict_partial_maps_to_each_boundary()
{
    let map = claimed_wires(&[
        (Wire::from(0), Wire::from(9)),
        (Wire::from(3), Wire::from(10)),
        (Wire::from(7), Wire::from(11)),
    ]);
    let seam = seam_of(&multi_output_pattern(), &map);
    assert_eq!(
        seam.inputs(),
        &claimed_wires(&[(Wire::from(0), Wire::from(9))])
    );
    assert_eq!(
        seam.outputs(),
        &claimed_wires(&[(Wire::from(3), Wire::from(10))])
    );
}
