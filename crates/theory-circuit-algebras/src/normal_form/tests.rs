//! The canon's witnesses: the procedure's ordering promises fixture by
//! fixture, the differential against a cospan-isomorphism oracle, the four
//! separations a coarser canon would miss, the located divergences, and the
//! verifier's refusals.

use super::*;
use crate::interface::GeneratorLabel;
use crate::interface::GeneratorName;
use crate::interface::GeneratorSort;

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
/// - requires: the fixture satisfies wiring assembly invariants.
/// - ensures: retains all generators and declared boundary positions.
/// - panics: if assembly refuses the fixture.
///
/// # Adequacy
/// - hypothesis: L3 — ordered-boundary and ordered-hyperedge fixtures expose
///   retained incidence in their canonical records. Dropping a port or
///   generator changes the observed form; refused fixtures are outside the
///   domain.
/// - witness: `normal_form::tests::the_boundary_is_numbered_before_the_interior`
/// - witness: `normal_form::tests::a_visited_hyperedge_numbers_its_sources_before_its_targets`
#[spec(captures: [edges = generators.len(), inputs = boundary.inputs().len(), outputs = boundary.outputs().len()], ensures: |ref result| result.generators().len() == edges && result.boundary().inputs().len() == inputs && result.boundary().outputs().len() == outputs)]
fn diagram<W>(
    wires: W,
    generators: Vec<Generator>,
    boundary: Interface,
) -> Wiring
where
    W: Into<WireCount>,
{
    Wiring::assemble(wires.into(), generators, boundary)
        .expect("a fixture diagram is monogamous, boundary-honest and acyclic")
}

/// The form a diagram canonicalizes to.
///
/// # Specification
/// trivial.
fn form_of(diagram: &Wiring) -> CanonicalDiagram
{
    canonicalize(diagram).into_parts().0
}

/// `f: (0) -> (1)` then `g: (1) -> (2)`, open at both ends.
///
/// # Specification
/// trivial.
fn spine() -> Wiring
{
    diagram(
        3,
        alloc::vec![
            Generator::new(value("f"), wires![0], wires![1]),
            Generator::new(value("g"), wires![1], wires![2]),
        ],
        Interface::new(wires![0], wires![2]),
    )
}

/// The same diagram as [`spine`], its generators listed the other way round
/// and its wires renumbered: the presentation freedom the canon quotients.
///
/// # Specification
/// trivial.
fn spine_permuted() -> Wiring
{
    diagram(
        3,
        alloc::vec![
            Generator::new(value("g"), wires![0], wires![1]),
            Generator::new(value("f"), wires![2], wires![0]),
        ],
        Interface::new(wires![2], wires![1]),
    )
}

/// [`spine`] with its labels in descending order, so the generator the
/// boundary reaches first is not the one a label-minimizing seed would pick.
///
/// The fixture that separates anchoring from minimizing: every other fixture
/// agrees on the two, so a canon that skipped the drain after numbering the
/// boundary, routing every component through the minimization, would pass
/// them all.
///
/// # Specification
/// trivial.
fn descending_spine() -> Wiring
{
    diagram(
        3,
        alloc::vec![
            Generator::new(value("z"), wires![0], wires![1]),
            Generator::new(value("a"), wires![1], wires![2]),
        ],
        Interface::new(wires![0], wires![2]),
    )
}

/// A diagram where the traversal reaches a generator with both an unnumbered
/// source and an unnumbered target, the only shape on which the
/// sources-before-targets order is observable.
///
/// # Specification
/// trivial.
fn branching() -> Wiring
{
    diagram(
        5,
        alloc::vec![
            Generator::new(value("p"), wires![0], wires![1]),
            Generator::new(value("f"), wires![2, 1], wires![3]),
            Generator::new(value("q"), wires![3], wires![4]),
        ],
        Interface::new(wires![2, 0], wires![4]),
    )
}

/// A closed component, `f: () -> (0)` into `g: (0) -> ()`, with an empty
/// interface: the boundary anchors nothing and the seed is chosen inside.
///
/// # Specification
/// trivial.
fn closed() -> Wiring
{
    diagram(
        1,
        alloc::vec![
            Generator::new(value("f"), wires![], wires![0]),
            Generator::new(value("g"), wires![0], wires![]),
        ],
        Interface::default(),
    )
}

/// [`closed`] with its two generators listed the other way round.
///
/// # Specification
/// trivial.
fn closed_permuted() -> Wiring
{
    diagram(
        1,
        alloc::vec![
            Generator::new(value("g"), wires![0], wires![]),
            Generator::new(value("f"), wires![], wires![0]),
        ],
        Interface::default(),
    )
}

/// Two closed components, `f -> g` and `h -> k`, with an empty interface.
///
/// # Specification
/// trivial.
fn two_closed() -> Wiring
{
    diagram(
        2,
        alloc::vec![
            Generator::new(value("f"), wires![], wires![0]),
            Generator::new(value("g"), wires![0], wires![]),
            Generator::new(value("h"), wires![], wires![1]),
            Generator::new(value("k"), wires![1], wires![]),
        ],
        Interface::default(),
    )
}

/// [`two_closed`] with the `h`–`k` component listed first.
///
/// # Specification
/// trivial.
fn two_closed_permuted() -> Wiring
{
    diagram(
        2,
        alloc::vec![
            Generator::new(value("h"), wires![], wires![0]),
            Generator::new(value("k"), wires![0], wires![]),
            Generator::new(value("f"), wires![], wires![1]),
            Generator::new(value("g"), wires![1], wires![]),
        ],
        Interface::default(),
    )
}

/// One wire and no generator: the identity, whose only wire is a port of
/// nothing and is numbered from the boundary alone.
///
/// # Specification
/// trivial.
fn bare_wire() -> Wiring
{
    diagram(1, Vec::new(), Interface::new(wires![0], wires![0]))
}

/// No wire and no generator.
///
/// # Specification
/// trivial.
fn empty() -> Wiring
{
    diagram(0, Vec::new(), Interface::default())
}

/// Two port-free generators of one label: the only shape that is a component
/// holding no wire.
///
/// # Specification
/// trivial.
fn port_free_pair() -> Wiring
{
    diagram(
        0,
        alloc::vec![
            Generator::new(value("a"), wires![], wires![]),
            Generator::new(value("a"), wires![], wires![]),
        ],
        Interface::default(),
    )
}

/// `s` fanning out to two wires that `m` rejoins: the reconvergence axis.
///
/// # Specification
/// trivial.
fn reconvergent() -> Wiring
{
    diagram(
        4,
        alloc::vec![
            Generator::new(value("s"), wires![0], wires![1, 2]),
            Generator::new(value("m"), wires![1, 2], wires![3]),
        ],
        Interface::new(wires![0], wires![3]),
    )
}

/// [`reconvergent`] with `m`'s two sources exchanged: the same wires, one
/// port order apart, and so a different diagram.
///
/// # Specification
/// trivial.
fn reconvergent_swapped() -> Wiring
{
    diagram(
        4,
        alloc::vec![
            Generator::new(value("s"), wires![0], wires![1, 2]),
            Generator::new(value("m"), wires![2, 1], wires![3]),
        ],
        Interface::new(wires![0], wires![3]),
    )
}

/// A three-step chain `f`, `g`, `h`.
///
/// # Specification
/// trivial.
fn chain() -> Wiring
{
    diagram(
        4,
        alloc::vec![
            Generator::new(value("f"), wires![0], wires![1]),
            Generator::new(value("g"), wires![1], wires![2]),
            Generator::new(value("h"), wires![2], wires![3]),
        ],
        Interface::new(wires![0], wires![3]),
    )
}

/// [`chain`] renumbered and relisted: the same diagram.
///
/// # Specification
/// trivial.
fn chain_relabelled() -> Wiring
{
    diagram(
        4,
        alloc::vec![
            Generator::new(value("h"), wires![0], wires![2]),
            Generator::new(value("f"), wires![3], wires![1]),
            Generator::new(value("g"), wires![1], wires![0]),
        ],
        Interface::new(wires![3], wires![2]),
    )
}

/// The three generators of [`chain`] wired in another order: equal counts,
/// equal labels, a different diagram.
///
/// # Specification
/// trivial.
fn chain_rewired() -> Wiring
{
    diagram(
        4,
        alloc::vec![
            Generator::new(value("f"), wires![0], wires![1]),
            Generator::new(value("h"), wires![1], wires![2]),
            Generator::new(value("g"), wires![2], wires![3]),
        ],
        Interface::new(wires![0], wires![3]),
    )
}

/// [`spine`] with a closed component beside it.
///
/// # Specification
/// trivial.
fn spine_with_closed() -> Wiring
{
    diagram(
        4,
        alloc::vec![
            Generator::new(value("f"), wires![0], wires![1]),
            Generator::new(value("g"), wires![1], wires![2]),
            Generator::new(value("p"), wires![], wires![3]),
            Generator::new(value("q"), wires![3], wires![]),
        ],
        Interface::new(wires![0], wires![2]),
    )
}

/// [`spine_with_closed`] with the closed component's producer renamed, so
/// the two forms agree until the third canonical generator.
///
/// # Specification
/// trivial.
fn spine_with_closed_relabelled() -> Wiring
{
    diagram(
        4,
        alloc::vec![
            Generator::new(value("f"), wires![0], wires![1]),
            Generator::new(value("g"), wires![1], wires![2]),
            Generator::new(value("r"), wires![], wires![3]),
            Generator::new(value("q"), wires![3], wires![]),
        ],
        Interface::new(wires![0], wires![2]),
    )
}

/// A closed chain `p -> a -> a -> q` whose two interior generators wear one
/// label at one arity, so two of its seeds lay down the same first record and
/// part only later.
///
/// The fixture that separates the least linearization from the least first
/// record: a seed's first record is its own label and arity and nothing else,
/// so a minimization reading only that record keeps whichever tied member it
/// met first, a fact about the listing.
///
/// # Specification
/// trivial.
fn nested_repeated_label() -> Wiring
{
    diagram(
        3,
        alloc::vec![
            Generator::new(value("p"), wires![], wires![0]),
            Generator::new(value("a"), wires![0], wires![1]),
            Generator::new(value("a"), wires![1], wires![2]),
            Generator::new(value("q"), wires![2], wires![]),
        ],
        Interface::default(),
    )
}

/// [`nested_repeated_label`] listed back to front and renumbered: the
/// presentation on which a first-record minimization picks the other `a`.
///
/// # Specification
/// trivial.
fn nested_repeated_label_permuted() -> Wiring
{
    diagram(
        3,
        alloc::vec![
            Generator::new(value("q"), wires![0], wires![]),
            Generator::new(value("a"), wires![1], wires![0]),
            Generator::new(value("a"), wires![2], wires![1]),
            Generator::new(value("p"), wires![], wires![2]),
        ],
        Interface::default(),
    )
}

/// Two closed components whose winning linearizations agree on their first
/// record and part at the second: `a -> b` beside `a -> c`.
///
/// # Specification
/// trivial.
fn twin_headed_pair() -> Wiring
{
    diagram(
        2,
        alloc::vec![
            Generator::new(value("a"), wires![], wires![0]),
            Generator::new(value("b"), wires![0], wires![]),
            Generator::new(value("a"), wires![], wires![1]),
            Generator::new(value("c"), wires![1], wires![]),
        ],
        Interface::default(),
    )
}

/// [`twin_headed_pair`] with the `a`–`c` component listed first.
///
/// # Specification
/// trivial.
fn twin_headed_pair_permuted() -> Wiring
{
    diagram(
        2,
        alloc::vec![
            Generator::new(value("a"), wires![], wires![0]),
            Generator::new(value("c"), wires![0], wires![]),
            Generator::new(value("a"), wires![], wires![1]),
            Generator::new(value("b"), wires![1], wires![]),
        ],
        Interface::default(),
    )
}

/// Two isomorphic closed components, whose winning linearizations tie
/// outright, so the tie falls to listing position.
///
/// # Specification
/// trivial.
fn twin_closed() -> Wiring
{
    diagram(
        2,
        alloc::vec![
            Generator::new(value("a"), wires![], wires![0]),
            Generator::new(value("b"), wires![0], wires![]),
            Generator::new(value("a"), wires![], wires![1]),
            Generator::new(value("b"), wires![1], wires![]),
        ],
        Interface::default(),
    )
}

/// [`twin_closed`] with its two components interleaved in the listing, so
/// neither is a contiguous run of generator positions.
///
/// # Specification
/// trivial.
fn twin_closed_interleaved() -> Wiring
{
    diagram(
        2,
        alloc::vec![
            Generator::new(value("a"), wires![], wires![0]),
            Generator::new(value("a"), wires![], wires![1]),
            Generator::new(value("b"), wires![1], wires![]),
            Generator::new(value("b"), wires![0], wires![]),
        ],
        Interface::default(),
    )
}

/// `m: (0, 1) -> (2)` with its input leg in declared order.
///
/// # Specification
/// trivial.
fn two_input() -> Wiring
{
    diagram(
        3,
        alloc::vec![Generator::new(value("m"), wires![0, 1], wires![2])],
        Interface::new(wires![0, 1], wires![2]),
    )
}

/// [`two_input`] with its input leg exchanged: one apex, another cospan.
///
/// # Specification
/// trivial.
fn two_input_boundary_swapped() -> Wiring
{
    diagram(
        3,
        alloc::vec![Generator::new(value("m"), wires![0, 1], wires![2])],
        Interface::new(wires![1, 0], wires![2]),
    )
}

/// `f: (0) -> (1)` worn as a value constructor.
///
/// # Specification
/// trivial.
fn one_step_value() -> Wiring
{
    diagram(
        2,
        alloc::vec![Generator::new(value("f"), wires![0], wires![1])],
        Interface::new(wires![0], wires![1]),
    )
}

/// The same name and arity worn as an operation frame.
///
/// # Specification
/// trivial.
fn one_step_operation() -> Wiring
{
    diagram(
        2,
        alloc::vec![Generator::new(
            GeneratorLabel::new("f", GeneratorSort::Operation),
            wires![0],
            wires![1]
        )],
        Interface::new(wires![0], wires![1]),
    )
}

/// Two isolated wires declared in one order on both legs: the identity on two
/// wires.
///
/// # Specification
/// trivial.
fn two_wires_identity() -> Wiring
{
    diagram(2, Vec::new(), Interface::new(wires![0, 1], wires![0, 1]))
}

/// Two isolated wires whose output leg is exchanged: the symmetry, with the
/// apex of [`two_wires_identity`] and another cospan.
///
/// # Specification
/// trivial.
fn two_wires_swapped() -> Wiring
{
    diagram(2, Vec::new(), Interface::new(wires![0, 1], wires![1, 0]))
}

/// `s: (0) -> (1, 2)` with both outputs open: the boundary arities of
/// [`two_input`] the other way round.
///
/// # Specification
/// trivial.
fn fan_out_pair() -> Wiring
{
    diagram(
        3,
        alloc::vec![Generator::new(value("s"), wires![0], wires![1, 2])],
        Interface::new(wires![0], wires![1, 2]),
    )
}

/// `s` forking to two wires, one of which `t` reads: one open input and two
/// open outputs, so it agrees with [`reconvergent`] on everything compared
/// before the output leg.
///
/// # Specification
/// trivial.
fn fork_then_step() -> Wiring
{
    diagram(
        4,
        alloc::vec![
            Generator::new(value("s"), wires![0], wires![1, 2]),
            Generator::new(value("t"), wires![1], wires![3]),
        ],
        Interface::new(wires![0], wires![2, 3]),
    )
}

/// Every fixture, so a battery runs over all of them.
///
/// # Specification
/// trivial.
fn every_fixture() -> Vec<Wiring>
{
    alloc::vec![
        spine(),
        spine_permuted(),
        branching(),
        closed(),
        closed_permuted(),
        two_closed(),
        two_closed_permuted(),
        bare_wire(),
        empty(),
        port_free_pair(),
        reconvergent(),
        reconvergent_swapped(),
        chain(),
        chain_relabelled(),
        chain_rewired(),
        spine_with_closed(),
        two_input(),
        two_input_boundary_swapped(),
        one_step_value(),
        one_step_operation(),
        two_wires_identity(),
        two_wires_swapped(),
        fan_out_pair(),
        fork_then_step(),
        descending_spine(),
        nested_repeated_label(),
        nested_repeated_label_permuted(),
        twin_headed_pair(),
        twin_headed_pair_permuted(),
        twin_closed(),
        twin_closed_interleaved(),
    ]
}

#[test]
fn canonicalization_is_total_and_its_witness_verifies()
{
    // The L1 validator on every fixture. Totality, which boundary honesty
    // buys, is asserted rather than assumed: every wire and every generator is
    // mapped, the form declares as many of each as the source, and the
    // relabelling checks out as an isomorphism onto the form.
    for diagram in every_fixture() {
        let canonical = canonicalize(&diagram);
        assert_eq!(
            Ok(()),
            canonical.relabelling().verify(&diagram, canonical.form()),
            "the relabelling is an isomorphism onto the form it came with"
        );
        assert_eq!(
            diagram.wire_count(),
            canonical.relabelling().mapped_wires(),
            "every wire of the source is mapped, so the numbering is total"
        );
        assert_eq!(
            diagram.edge_count(),
            canonical.relabelling().mapped_generators(),
            "and so is every generator"
        );
        assert_eq!(
            diagram.wire_count(),
            canonical.form().wire_count(),
            "the form declares the same wires"
        );
        assert_eq!(
            diagram.edge_count(),
            canonical.form().edge_count(),
            "and holds the same generators"
        );
    }
}

#[test]
fn the_boundary_is_numbered_before_the_interior()
{
    // The input leg takes the lowest numbers in declared order, then the
    // output leg, then the interior in traversal order.
    let canonical = canonicalize(&spine());
    assert_eq!(
        &Interface::new(wires![0], wires![1]),
        canonical.form().boundary(),
        "the input port is wire 0 and the output port wire 1, before any interior wire"
    );
    assert_eq!(
        &[
            Generator::new(value("f"), wires![0], wires![2]),
            Generator::new(value("g"), wires![2], wires![1]),
        ][..],
        canonical.form().generators(),
        "so the interior wire is 2, and the generators come in traversal order"
    );
}

#[test]
fn an_anchored_component_is_ordered_by_the_boundary_and_not_by_its_labels()
{
    // The boundary reaches `z` first, while the least linearization would
    // start at `a`. A canon that sent anchored components through the
    // minimization would put `a` first here and agree everywhere else.
    let canonical = canonicalize(&descending_spine());
    assert_eq!(
        &[
            Generator::new(value("z"), wires![0], wires![2]),
            Generator::new(value("a"), wires![2], wires![1]),
        ][..],
        canonical.form().generators(),
        "the generator the input port reaches comes first, whatever the labels sort like"
    );
}

#[test]
fn a_visited_hyperedge_numbers_its_sources_before_its_targets()
{
    // `f` is reached through its first source, leaving its second source and
    // its target unnumbered. Sources first gives the second source the lower
    // number; targets first would give `f: (0, 4) -> (3)`.
    let canonical = canonicalize(&branching());
    assert_eq!(
        &Interface::new(wires![0, 1], wires![2]),
        canonical.form().boundary(),
        "both declared inputs come first, in declared order, then the output"
    );
    assert_eq!(
        &[
            Generator::new(value("f"), wires![0, 3], wires![4]),
            Generator::new(value("p"), wires![1], wires![3]),
            Generator::new(value("q"), wires![4], wires![2]),
        ][..],
        canonical.form().generators(),
        "`f`'s unnumbered source takes 3 and its unnumbered target takes 4"
    );
}

#[test]
fn a_presentation_permutation_has_one_canonical_form()
{
    // Renumbering the wires and relisting the generators is exactly the
    // freedom the canon quotients, and the verdict carries both relabellings
    // rather than a bare bit.
    let left = spine();
    let right = spine_permuted();
    assert_eq!(
        form_of(&left),
        form_of(&right),
        "the two presentations reach one form"
    );
    let DiagramEquality::Same(shared) = same_diagram(&left, &right)
    else {
        panic!("two presentations of one diagram are the same diagram");
    };
    assert_eq!(
        Ok(()),
        shared.left().verify(&left, shared.form()),
        "the left relabelling reaches the shared form"
    );
    assert_eq!(
        Ok(()),
        shared.right().verify(&right, shared.form()),
        "and so does the right one, so the isomorphism between them is in hand"
    );
}

#[test]
fn canonicalization_is_idempotent()
{
    // A form read back as a diagram and canonicalized again returns itself,
    // and the second relabelling is the identity: a form is a fixed point.
    for diagram in every_fixture() {
        let form = form_of(&diagram);
        let again = form
            .to_wiring()
            .expect("a canonical form is inside the fragment");
        let recanonicalized = canonicalize(&again);
        assert_eq!(
            &form,
            recanonicalized.form(),
            "canonicalizing a canonical form returns it"
        );
        for wire in again.wire_count().wires() {
            assert_eq!(
                Maybe::Present(wire),
                recanonicalized.relabelling().image_of_wire(wire),
                "and its relabelling is the identity on wires"
            );
        }
        for position in 0 .. usize::from(again.edge_count()) {
            let edge = Edge::from(position);
            assert_eq!(
                Maybe::Present(edge),
                recanonicalized.relabelling().image_of_generator(edge),
                "and on generators"
            );
        }
    }
}

#[test]
fn a_component_with_no_boundary_port_is_seeded_by_minimizing()
{
    // The closed component has no anchor, so every member is tried as the
    // seed and the least linearization kept. `f` wins over `g` because the
    // record it lays down first is smaller, so both listings agree.
    let canonical = canonicalize(&closed());
    assert_eq!(
        &[
            Generator::new(value("f"), wires![], wires![0]),
            Generator::new(value("g"), wires![0], wires![]),
        ][..],
        canonical.form().generators(),
        "the least linearization seeds at `f`, whatever order the diagram lists"
    );
    assert_eq!(
        canonical.into_parts().0,
        form_of(&closed_permuted()),
        "so the reversed listing reaches the same form"
    );
}

#[test]
fn components_with_no_boundary_port_are_committed_in_canonical_order()
{
    // Two anchorless components are ordered by their winning linearizations:
    // `f`–`g` precedes `h`–`k` whichever the diagram lists first.
    let canonical = canonicalize(&two_closed());
    assert_eq!(
        &[
            Generator::new(value("f"), wires![], wires![0]),
            Generator::new(value("g"), wires![0], wires![]),
            Generator::new(value("h"), wires![], wires![1]),
            Generator::new(value("k"), wires![1], wires![]),
        ][..],
        canonical.form().generators(),
        "the `f` component is committed first and takes the lower wire"
    );
    assert_eq!(
        canonical.into_parts().0,
        form_of(&two_closed_permuted()),
        "so listing the `h` component first changes nothing"
    );
}

#[test]
fn the_least_linearization_is_compared_past_its_first_record()
{
    // Any two same-label same-arity members tie on their first record, so a
    // comparison stopping there — on the record, its label or the record count
    // — falls back on listing position. The two fixtures separate the two
    // places the comparison is made: the seed inside one component, and the
    // order the components are committed in.
    let nested = canonicalize(&nested_repeated_label());
    assert_eq!(
        &[
            Generator::new(value("a"), wires![0], wires![1]),
            Generator::new(value("a"), wires![2], wires![0]),
            Generator::new(value("q"), wires![1], wires![]),
            Generator::new(value("p"), wires![], wires![2]),
        ][..],
        nested.form().generators(),
        "the seed is the second `a`, whose tail is least; the first ties only at the head"
    );
    assert_eq!(
        nested.into_parts().0,
        form_of(&nested_repeated_label_permuted()),
        "so the reversed listing reaches the same form"
    );
    let twins = canonicalize(&twin_headed_pair());
    assert_eq!(
        &[
            Generator::new(value("a"), wires![], wires![0]),
            Generator::new(value("b"), wires![0], wires![]),
            Generator::new(value("a"), wires![], wires![1]),
            Generator::new(value("c"), wires![1], wires![]),
        ][..],
        twins.form().generators(),
        "`a`-`b` precedes `a`-`c`, which their shared first record cannot decide"
    );
    assert_eq!(
        twins.into_parts().0,
        form_of(&twin_headed_pair_permuted()),
        "so listing the `a`-`c` component first changes nothing"
    );
}

#[test]
fn two_isomorphic_anchorless_components_still_have_one_form()
{
    // The one place listing position breaks a tie: two isomorphic anchorless
    // components tie outright, so which copy is committed first depends on the
    // listing and the relabelling is not an invariant. The form still is,
    // because both commits lay down the same records at the same numbers.
    let listed = canonicalize(&twin_closed());
    assert_eq!(
        &[
            Generator::new(value("a"), wires![], wires![0]),
            Generator::new(value("b"), wires![0], wires![]),
            Generator::new(value("a"), wires![], wires![1]),
            Generator::new(value("b"), wires![1], wires![]),
        ][..],
        listed.form().generators(),
        "both copies are committed, the second taking the higher wire"
    );
    let interleaved = canonicalize(&twin_closed_interleaved());
    assert_eq!(
        listed.form(),
        interleaved.form(),
        "and interleaving the two components in the listing reaches the same form"
    );
    assert_ne!(
        listed.relabelling(),
        interleaved.relabelling(),
        "while the relabellings differ, which is why the form's invariance is the claim"
    );
    assert_eq!(
        Ok(()),
        interleaved
            .relabelling()
            .verify(&twin_closed_interleaved(), interleaved.form()),
        "both relabellings are isomorphisms even though neither is canonical"
    );
}

#[test]
fn an_isolated_wire_is_numbered_from_the_boundary_alone()
{
    // An isolated wire is a port of no generator, so boundary honesty is the
    // only reason it is numbered. The empty diagram and the port-free pair are
    // the other two degenerate shapes.
    let bare = canonicalize(&bare_wire());
    assert_eq!(
        WireCount::from(1),
        bare.form().wire_count(),
        "the isolated wire is numbered"
    );
    assert_eq!(
        &Interface::new(wires![0], wires![0]),
        bare.form().boundary(),
        "and both legs name it, which is how it was reached at all"
    );
    assert_eq!(
        EdgeCount::from(0),
        bare.form().edge_count(),
        "with no generator in the form"
    );
    let nothing = canonicalize(&empty());
    assert_eq!(
        WireCount::from(0),
        nothing.form().wire_count(),
        "the empty diagram canonicalizes to itself"
    );
    assert_eq!(
        &Interface::default(),
        nothing.form().boundary(),
        "with an empty interface"
    );
    let port_free = canonicalize(&port_free_pair());
    assert_eq!(
        &[
            Generator::new(value("a"), wires![], wires![]),
            Generator::new(value("a"), wires![], wires![]),
        ][..],
        port_free.form().generators(),
        "two port-free generators are two components, and both are committed"
    );
}

#[test]
fn presentations_of_one_diagram_collapse_to_one_key()
{
    // The canonical form is a map key: presentations of one diagram land on
    // one entry and different diagrams on different entries. Nothing is
    // interned; the map stands for any keyed store a consumer builds.
    let presentations = [
        ("spine", spine()),
        ("spine permuted", spine_permuted()),
        ("spine again", spine()),
        ("closed", closed()),
        ("closed permuted", closed_permuted()),
        ("chain", chain()),
        ("chain relabelled", chain_relabelled()),
        ("chain rewired", chain_rewired()),
    ];
    let mut keyed: BTreeMap<CanonicalDiagram, Vec<&str>> = BTreeMap::new();
    for (name, presentation) in presentations {
        keyed.entry(form_of(&presentation)).or_default().push(name);
    }
    assert_eq!(
        4,
        keyed.len(),
        "eight presentations of four diagrams fall on four keys"
    );
    assert_eq!(
        Some(&alloc::vec!["spine", "spine permuted", "spine again"]),
        keyed.get(&form_of(&spine())),
        "every presentation of the spine shares one key"
    );
    assert_eq!(
        Some(&alloc::vec!["closed", "closed permuted"]),
        keyed.get(&form_of(&closed())),
        "and so does every listing of the closed component"
    );
    assert_eq!(
        Some(&alloc::vec!["chain", "chain relabelled"]),
        keyed.get(&form_of(&chain())),
        "and every renumbering of the chain"
    );
    assert_eq!(
        Some(&alloc::vec!["chain rewired"]),
        keyed.get(&form_of(&chain_rewired())),
        "while one generator multiset wired two ways takes two keys"
    );
}

/// A minimal accumulating hasher, so the form's [`Hash`] is exercised rather
/// than only derived. Wrapping arithmetic is the hashing use it is sanctioned
/// for.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default)]
struct Tally
{
    /// The accumulated digest.
    digest: u64,
}

impl core::hash::Hasher for Tally
{
    /// The accumulated digest.
    ///
    /// # Specification
    /// trivial.
    fn finish(&self) -> u64
    {
        self.digest
    }

    /// Folds `bytes` into the digest.
    ///
    /// # Specification
    /// - ensures: folds bytes in order by rotating seven bits then adding the
    ///   byte, with wrapping arithmetic; empty input preserves the digest.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — ordered bytes, segmented writes and overflow expose
    ///   exact digest transitions. Reordering bytes, resetting between writes
    ///   or using non-wrapping addition differs; this is the witness hasher,
    ///   not a collision-resistant digest.
    /// - witness: `normal_form::tests::tally_preserves_byte_order_and_write_segmentation`
    /// - witness: `normal_form::tests::equal_canonical_forms_hash_alike`
    #[spec(captures: [prior = self.digest], ensures: |_| self.digest == bytes.iter().fold(prior, |digest, byte| digest.rotate_left(7).wrapping_add(u64::from(*byte))))]
    fn write(
        &mut self,
        bytes: &[u8],
    )
    {
        for byte in bytes {
            self.digest = self.digest.rotate_left(7).wrapping_add(u64::from(*byte));
        }
    }
}

#[test]
fn equal_canonical_forms_hash_alike()
{
    // The law a key must satisfy: equal keys hash equal. Asserted rather than
    // inherited, because the form is offered as a key.
    let mut left = Tally::default();
    let mut right = Tally::default();
    core::hash::Hash::hash(&form_of(&spine()), &mut left);
    core::hash::Hash::hash(&form_of(&spine_permuted()), &mut right);
    assert_eq!(
        core::hash::Hasher::finish(&left),
        core::hash::Hasher::finish(&right),
        "two presentations of one diagram hash alike, so the form is usable as a key"
    );
}

/// The verdict of the independent cospan-isomorphism oracle.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum CospanVerdict
{
    /// A structure-preserving bijection commuting with both legs exists.
    Isomorphic,
    /// None does.
    Distinct,
}

/// Decides cospan isomorphism by exhaustive search over generator bijections,
/// sharing no code with [`canonicalize`].
///
/// Every bijection of generators is tried; each forces a wire correspondence,
/// read off the ordered port lists and the interface positions, and the
/// candidate is admitted when that correspondence is consistent, injective,
/// total on the left's wires and onto the right's. Exponential and
/// deliberately naive: it is the external oracle the canon is checked against,
/// so it is written another way rather than a faster one. Totality is a fair
/// admission condition because every wire is a generator port or a declared
/// interface port, the premise the canon rests on too.
///
/// # Specification
/// - ensures: isomorphic exactly when a label- and ordered-port-preserving
///   generator bijection induces a total wire bijection commuting with both
///   legs.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a known presentation permutation is accepted while
///   rewired incidence and a label worn at another sort are refused. L2 —
///   exhaustive agreement with the independent canonical traversal covers every
///   ordered fixture pair. The predicate checks reflexivity and necessary
///   cardinalities without sharing the traversal or repeating the exponential
///   search.
/// - witness: `normal_form::tests::isomorphism_oracle_separates_incidence_and_polarity`
/// - witness: `normal_form::tests::the_canon_agrees_with_the_cospan_isomorphism_oracle`
#[spec(ensures: |result| (left != right || result == CospanVerdict::Isomorphic)
    && (result == CospanVerdict::Distinct || (left.wire_count() == right.wire_count() && left.edge_count() == right.edge_count()
        && left.boundary().inputs().len() == right.boundary().inputs().len() && left.boundary().outputs().len() == right.boundary().outputs().len())))]
fn cospan_verdict(
    left: &Wiring,
    right: &Wiring,
) -> CospanVerdict
{
    if left.wire_count() != right.wire_count()
        || left.edge_count() != right.edge_count()
        || left.boundary().inputs().len() != right.boundary().inputs().len()
        || left.boundary().outputs().len() != right.boundary().outputs().len()
    {
        return CospanVerdict::Distinct;
    }
    let count = usize::from(left.edge_count());
    let mut bijections: Vec<Vec<usize>> = alloc::vec![Vec::new()];
    for _ in 0 .. count {
        let mut grown: Vec<Vec<usize>> = Vec::new();
        for prefix in &bijections {
            for candidate in 0 .. count {
                if prefix.contains(&candidate) {
                    continue;
                }
                let mut extended = prefix.clone();
                extended.push(candidate);
                grown.push(extended);
            }
        }
        bijections = grown;
    }
    'bijection: for bijection in &bijections {
        let mut pairs: Vec<(Wire, Wire)> = Vec::new();
        for (position, image) in bijection.iter().copied().enumerate() {
            let source = &left.generators()[position];
            let target = &right.generators()[image];
            if source.label() != target.label()
                || source.sources().len() != target.sources().len()
                || source.targets().len() != target.targets().len()
            {
                continue 'bijection;
            }
            pairs.extend(
                source
                    .sources()
                    .iter()
                    .copied()
                    .zip(target.sources().iter().copied()),
            );
            pairs.extend(
                source
                    .targets()
                    .iter()
                    .copied()
                    .zip(target.targets().iter().copied()),
            );
        }
        pairs.extend(
            left.boundary()
                .inputs()
                .iter()
                .copied()
                .zip(right.boundary().inputs().iter().copied()),
        );
        pairs.extend(
            left.boundary()
                .outputs()
                .iter()
                .copied()
                .zip(right.boundary().outputs().iter().copied()),
        );
        let mut forward: BTreeMap<Wire, Wire> = BTreeMap::new();
        let mut backward: BTreeMap<Wire, Wire> = BTreeMap::new();
        for (wire, other) in pairs {
            if forward
                .insert(wire, other)
                .is_some_and(|bound| bound != other)
                || backward
                    .insert(other, wire)
                    .is_some_and(|bound| bound != wire)
            {
                continue 'bijection;
            }
        }
        if forward.len() == usize::from(left.wire_count())
            && backward.len() == usize::from(right.wire_count())
        {
            return CospanVerdict::Isomorphic;
        }
    }
    CospanVerdict::Distinct
}

#[test]
fn the_canon_agrees_with_the_cospan_isomorphism_oracle()
{
    // Every ordered pair of every fixture. The oracle searches generator
    // bijections and derives the wire map; the canon renumbers and compares.
    // Hand-classified oracle witnesses establish both verdicts independently.
    let fixtures = every_fixture();

    for (left_index, left) in fixtures.iter().enumerate() {
        for (right_index, right) in fixtures.iter().enumerate() {
            let decided = match same_diagram(left, right) {
                | DiagramEquality::Same(_) => CospanVerdict::Isomorphic,
                | DiagramEquality::Distinct(_) => CospanVerdict::Distinct,
            };
            assert_eq!(
                cospan_verdict(left, right),
                decided,
                "the canon and the search agree on fixture {left_index} against fixture \
                 {right_index}"
            );
        }
    }
}

#[test]
fn the_canon_separates_a_permuted_boundary()
{
    // The interface legs are part of the object: an isomorphism commutes with
    // them, so exchanging two open wires on one leg is another diagram though
    // the apex is untouched. The identity on two wires and the symmetry are
    // the sharpest instance.
    assert_eq!(
        DiagramEquality::Distinct(DiagramDivergence::BoundaryPort {
            leg: Leg::Output,
            position: PortPosition::from(0),
            left: Wire::from(0),
            right: Wire::from(1),
        }),
        same_diagram(&two_wires_identity(), &two_wires_swapped()),
        "the two forms part on the output leg's first position"
    );
    assert_eq!(
        DiagramEquality::Distinct(DiagramDivergence::Generator { at: Edge::from(0) }),
        same_diagram(&two_input(), &two_input_boundary_swapped()),
        "and with a generator present the difference surfaces in its record instead"
    );
}

#[test]
fn the_canon_separates_a_permuted_port_list()
{
    // Port order within a generator is carried rather than quotiented, so
    // exchanging two of one generator's sources is another diagram. The first
    // record is identical in both — `s` numbers its two targets in its own
    // port order — so the difference surfaces at the second, where `m` reads
    // them back; a canon comparing a multiset of records would miss it.
    assert_eq!(
        DiagramEquality::Distinct(DiagramDivergence::Generator { at: Edge::from(1) }),
        same_diagram(&reconvergent(), &reconvergent_swapped()),
        "the records part at the generator that reads the two wires back"
    );
    assert_eq!(
        form_of(&reconvergent_swapped()).generators().first(),
        form_of(&reconvergent()).generators().first(),
        "and they agree on the first record, so the difference is the second's"
    );
}

#[test]
fn the_canon_separates_a_label_worn_at_two_sorts()
{
    // A label is a name with the role it is worn in, so one name at two sorts
    // is two generators; a name-only canon would identify a constructor with
    // an operation frame of the same arity.
    assert_eq!(
        DiagramEquality::Distinct(DiagramDivergence::Generator { at: Edge::from(0) }),
        same_diagram(&one_step_value(), &one_step_operation()),
        "the records part on the label's sort"
    );
}

#[test]
fn the_canon_separates_one_generator_multiset_wired_two_ways()
{
    // Equal wire counts, equal generator counts, equal interface arities, one
    // label multiset, and another diagram: the identification a canon hashing
    // a multiset of labels would wrongly admit.
    assert_eq!(
        DiagramEquality::Distinct(DiagramDivergence::Generator { at: Edge::from(1) }),
        same_diagram(&chain(), &chain_rewired()),
        "the chains part at the second canonical generator"
    );
    assert_eq!(
        CospanVerdict::Distinct,
        cospan_verdict(&chain(), &chain_rewired()),
        "and the external oracle agrees, so the verdict is no artefact of the numbering"
    );
}

#[test]
fn same_diagram_locates_a_count_difference()
{
    assert_eq!(
        DiagramEquality::Distinct(DiagramDivergence::WireCount {
            left: WireCount::from(3),
            right: WireCount::from(4),
        }),
        same_diagram(&spine(), &chain()),
        "a wire-count difference is reported with both counts"
    );
    assert_eq!(
        DiagramEquality::Distinct(DiagramDivergence::GeneratorCount {
            left: EdgeCount::from(2),
            right: EdgeCount::from(1),
        }),
        same_diagram(&spine(), &two_input()),
        "and a generator-count difference at equal wire counts is reported with both"
    );
}

#[test]
fn same_diagram_locates_a_boundary_difference()
{
    // Equal wire and generator counts, another interface: the input leg's
    // arity is compared first.
    assert_eq!(
        DiagramEquality::Distinct(DiagramDivergence::BoundaryArity {
            leg: Leg::Input,
            left: PortCount::from(2),
            right: PortCount::from(1),
        }),
        same_diagram(&two_input(), &fan_out_pair()),
        "the input leg's arity difference is reported with both arities"
    );
    // This pair agrees on wire count, generator count and input arity and
    // differs only on the output leg.
    assert_eq!(
        DiagramEquality::Distinct(DiagramDivergence::BoundaryArity {
            leg: Leg::Output,
            left: PortCount::from(1),
            right: PortCount::from(2),
        }),
        same_diagram(&reconvergent(), &fork_then_step()),
        "and the output leg is reported when everything before it agrees"
    );
}

#[test]
fn same_diagram_locates_a_hyperedge_difference()
{
    assert_eq!(
        DiagramEquality::Distinct(DiagramDivergence::Generator { at: Edge::from(2) }),
        same_diagram(&spine_with_closed(), &spine_with_closed_relabelled()),
        "the first canonical generator that differs is named"
    );
}

/// A canonical form with its interface and records replaced, for the
/// verifier's refusal arms. The wire count is kept, so a defect stays in the
/// part under test.
///
/// # Specification
/// trivial.
fn form_with(
    form: &CanonicalDiagram,
    boundary: Interface,
    generators: Vec<Generator>,
) -> CanonicalDiagram
{
    CanonicalDiagram {
        wires: form.wire_count(),
        boundary,
        generators: generators.into_boxed_slice(),
    }
}

/// The relabelling [`canonicalize`] produced for `diagram`, opened up so a
/// test can damage one entry of it.
///
/// # Specification
/// trivial.
fn opened_witness(
    diagram: &Wiring
) -> (CanonicalDiagram, BTreeMap<Wire, Wire>, BTreeMap<Edge, Edge>)
{
    let (form, relabelling) = canonicalize(diagram).into_parts();
    (form, relabelling.wires, relabelling.generators)
}

#[test]
fn the_verifier_refuses_a_defective_wire_map()
{
    let diagram = spine();
    let (form, wires, generators) = opened_witness(&diagram);
    let intact = Relabelling {
        wires: wires.clone(),
        generators: generators.clone(),
    };
    assert_eq!(
        Err(RelabellingDefect::WireCountMismatch {
            source: WireCount::from(3),
            form: WireCount::from(4),
        }),
        intact.verify(&diagram, &form_of(&chain())),
        "a form declaring another number of wires admits no bijection at all"
    );
    // `Wire(3)` is the first image outside a three-wire form; a distant image
    // would leave a `>=` weakened to `>` alive.
    let mut out_of_range = wires.clone();
    out_of_range.insert(Wire::from(0), Wire::from(3));
    let refusal = Relabelling {
        wires: out_of_range,
        generators: generators.clone(),
    };
    assert_eq!(
        Err(RelabellingDefect::WireImageOutOfRange {
            wire: Wire::from(0),
            image: Wire::from(3),
        }),
        refusal.verify(&diagram, &form),
        "the first image outside the form's wires is refused, naming both"
    );
    let mut reused = wires.clone();
    reused.insert(Wire::from(1), Wire::from(0));
    let refusal = Relabelling {
        wires: reused,
        generators: generators.clone(),
    };
    assert_eq!(
        Err(RelabellingDefect::WireImageReused {
            wire: Wire::from(1),
            image: Wire::from(0),
            bound: Wire::from(0),
        }),
        refusal.verify(&diagram, &form),
        "two wires sharing an image is refused, naming the wire that reached it first"
    );
    let mut unmapped = wires;
    unmapped.remove(&Wire::from(2));
    let refusal = Relabelling {
        wires: unmapped,
        generators,
    };
    assert_eq!(
        Err(RelabellingDefect::WireUnmapped {
            wire: Wire::from(2)
        }),
        refusal.verify(&diagram, &form),
        "and a wire with no image is refused, so a partial numbering cannot pass"
    );
}

#[test]
fn the_verifier_refuses_a_defective_generator_map()
{
    let diagram = spine();
    let (form, wires, generators) = opened_witness(&diagram);
    let intact = Relabelling {
        wires: wires.clone(),
        generators: generators.clone(),
    };
    assert_eq!(
        Err(RelabellingDefect::EdgeCountMismatch {
            source: EdgeCount::from(2),
            form: EdgeCount::from(1),
        }),
        intact.verify(&diagram, &form_of(&two_input())),
        "a form holding another number of generators admits no bijection"
    );
    // `Edge(2)` is the first image outside a two-generator form.
    let mut out_of_range = generators.clone();
    out_of_range.insert(Edge::from(0), Edge::from(2));
    let refusal = Relabelling {
        wires: wires.clone(),
        generators: out_of_range,
    };
    assert_eq!(
        Err(RelabellingDefect::GeneratorImageOutOfRange {
            at: Edge::from(0),
            image: Edge::from(2),
        }),
        refusal.verify(&diagram, &form),
        "the first image outside the form's generators is refused, naming both"
    );
    let mut reused = generators.clone();
    reused.insert(Edge::from(1), Edge::from(0));
    let refusal = Relabelling {
        wires: wires.clone(),
        generators: reused,
    };
    assert_eq!(
        Err(RelabellingDefect::GeneratorImageReused {
            at: Edge::from(1),
            image: Edge::from(0),
            bound: Edge::from(0),
        }),
        refusal.verify(&diagram, &form),
        "two generators sharing an image is refused"
    );
    let mut unmapped = generators;
    unmapped.remove(&Edge::from(1));
    let refusal = Relabelling {
        wires,
        generators: unmapped,
    };
    assert_eq!(
        Err(RelabellingDefect::GeneratorUnmapped { at: Edge::from(1) }),
        refusal.verify(&diagram, &form),
        "and a generator with no image is refused"
    );
}

#[test]
fn the_verifier_refuses_a_record_that_does_not_correspond()
{
    // The relabelling is intact and the form is damaged one part at a time, so
    // each arm of the record check is separated. The spine's canonical
    // records are `f: (0) -> (2)` and `g: (2) -> (1)`.
    let diagram = spine();
    let (form, wires, generators) = opened_witness(&diagram);
    let witness = Relabelling { wires, generators };
    let boundary = form.boundary().clone();
    let second = Generator::new(value("g"), wires![2], wires![1]);
    let relabelled = form_with(&form, boundary.clone(), alloc::vec![
        Generator::new(value("r"), wires![0], wires![2]),
        second.clone()
    ]);
    assert_eq!(
        Err(RelabellingDefect::LabelMismatch {
            at: Edge::from(0),
            image: Edge::from(0),
        }),
        witness.verify(&diagram, &relabelled),
        "a record carrying another label is refused"
    );
    let wide_source = form_with(&form, boundary.clone(), alloc::vec![
        Generator::new(value("f"), wires![0, 0], wires![2]),
        second.clone()
    ]);
    assert_eq!(
        Err(RelabellingDefect::ArityMismatch {
            at: Edge::from(0),
            image: Edge::from(0),
            leg: Leg::Input,
            declared: PortCount::from(1),
            found: PortCount::from(2),
        }),
        witness.verify(&diagram, &wide_source),
        "a record with an extra source is refused on the input leg"
    );
    let wide_target = form_with(&form, boundary.clone(), alloc::vec![
        Generator::new(value("f"), wires![0], wires![2, 2]),
        second.clone()
    ]);
    assert_eq!(
        Err(RelabellingDefect::ArityMismatch {
            at: Edge::from(0),
            image: Edge::from(0),
            leg: Leg::Output,
            declared: PortCount::from(1),
            found: PortCount::from(2),
        }),
        witness.verify(&diagram, &wide_target),
        "and one with an extra target on the output leg, so both legs are checked"
    );
    let wrong_source = form_with(&form, boundary.clone(), alloc::vec![
        Generator::new(value("f"), wires![1], wires![2]),
        second.clone()
    ]);
    assert_eq!(
        Err(RelabellingDefect::PortMismatch {
            at: Edge::from(0),
            image: Edge::from(0),
            leg: Leg::Input,
            position: PortPosition::from(0),
        }),
        witness.verify(&diagram, &wrong_source),
        "a source whose image is not the record's port at that position is refused"
    );
    let wrong_target = form_with(&form, boundary, alloc::vec![
        Generator::new(value("f"), wires![0], wires![1]),
        second
    ]);
    assert_eq!(
        Err(RelabellingDefect::PortMismatch {
            at: Edge::from(0),
            image: Edge::from(0),
            leg: Leg::Output,
            position: PortPosition::from(0),
        }),
        witness.verify(&diagram, &wrong_target),
        "and so is a target, naming the leg and the position"
    );
}

#[test]
fn the_verifier_refuses_a_boundary_that_does_not_commute()
{
    // The condition that makes the relabelling an isomorphism of cospans
    // rather than of apexes. The records stay intact, so only the legs are
    // under test.
    let diagram = spine();
    let (form, wires, generators) = opened_witness(&diagram);
    let witness = Relabelling { wires, generators };
    let records = alloc::vec![
        Generator::new(value("f"), wires![0], wires![2]),
        Generator::new(value("g"), wires![2], wires![1]),
    ];
    let wide_input = form_with(
        &form,
        Interface::new(wires![0, 1], wires![1]),
        records.clone(),
    );
    assert_eq!(
        Err(RelabellingDefect::BoundaryArityMismatch {
            leg: Leg::Input,
            declared: PortCount::from(1),
            found: PortCount::from(2),
        }),
        witness.verify(&diagram, &wide_input),
        "an input leg of the wrong arity is refused"
    );
    let narrow_output = form_with(&form, Interface::new(wires![0], wires![]), records.clone());
    assert_eq!(
        Err(RelabellingDefect::BoundaryArityMismatch {
            leg: Leg::Output,
            declared: PortCount::from(1),
            found: PortCount::from(0),
        }),
        witness.verify(&diagram, &narrow_output),
        "and so is an output leg of the wrong arity, so both legs are checked"
    );
    let wrong_input = form_with(&form, Interface::new(wires![1], wires![1]), records.clone());
    assert_eq!(
        Err(RelabellingDefect::BoundaryMismatch {
            leg: Leg::Input,
            position: PortPosition::from(0),
        }),
        witness.verify(&diagram, &wrong_input),
        "an input port whose image is not the form's port there is refused"
    );
    let wrong_output = form_with(&form, Interface::new(wires![0], wires![0]), records);
    assert_eq!(
        Err(RelabellingDefect::BoundaryMismatch {
            leg: Leg::Output,
            position: PortPosition::from(0),
        }),
        witness.verify(&diagram, &wrong_output),
        "and so is an output port, naming the leg and the position"
    );
}

#[test]
fn relabelling_observers_refuse_missing_positions()
{
    let source = spine();
    let canonical = canonicalize(&source);
    assert_eq!(
        canonical
            .relabelling()
            .image_of_wire(Wire::from(usize::from(source.wire_count()))),
        Maybe::Absent(relabelled_wire::Absent::Unmapped)
    );
    assert_eq!(
        canonical
            .relabelling()
            .image_of_generator(Edge::from(usize::from(source.edge_count()))),
        Maybe::Absent(relabelled_generator::Absent::Unmapped)
    );
}

#[test]
fn record_comparison_resolves_equal_prefixes_by_length()
{
    let source = diagram(
        0,
        alloc::vec![
            Generator::new(value("a"), wires![], wires![]),
            Generator::new(value("b"), wires![], wires![])
        ],
        Interface::default(),
    );
    let mut short = Linearization::new(&source);
    short.visit(Edge::from(0));
    short.drain();
    let mut long = Linearization::new(&source);
    long.visit(Edge::from(0));
    long.visit(Edge::from(1));
    long.drain();
    assert_eq!(short.compare_records(&short), core::cmp::Ordering::Equal);
    assert_eq!(short.compare_records(&long), core::cmp::Ordering::Less);
    assert_eq!(long.compare_records(&short), core::cmp::Ordering::Greater);
}

#[test]
fn tally_preserves_byte_order_and_write_segmentation()
{
    let mut whole = Tally::default();
    core::hash::Hasher::write(&mut whole, &[1, 2]);
    assert_eq!(core::hash::Hasher::finish(&whole), 130);
    let mut segmented = Tally::default();
    core::hash::Hasher::write(&mut segmented, &[1]);
    core::hash::Hasher::write(&mut segmented, &[]);
    core::hash::Hasher::write(&mut segmented, &[2]);
    assert_eq!(core::hash::Hasher::finish(&segmented), 130);
    let mut wrapping = Tally { digest: u64::MAX };
    core::hash::Hasher::write(&mut wrapping, &[1]);
    assert_eq!(core::hash::Hasher::finish(&wrapping), 0);
}

#[test]
fn isomorphism_oracle_separates_incidence_and_polarity()
{
    assert_eq!(
        cospan_verdict(&spine(), &spine_permuted()),
        CospanVerdict::Isomorphic
    );
    assert_eq!(
        cospan_verdict(&chain(), &chain_rewired()),
        CospanVerdict::Distinct
    );
    assert_eq!(
        cospan_verdict(&one_step_value(), &one_step_operation()),
        CospanVerdict::Distinct
    );
}
