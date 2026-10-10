# gandr-theory-circuit-algebras

The diagram view of gandr's circuit algebras: monogamous acyclic wirings with interfaces, the spine reading of a sequent command pattern, embedding-based matching with its convexity check and certificate reader, and the diagram normal form that decides when two presentations denote one diagram.

<!-- toc -->

- [Synopsis](#synopsis)
- [References](#references)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [The fragment, at construction](#the-fragment-at-construction)
- [Generator labels](#generator-labels)
- [The spine reading](#the-spine-reading)
- [Embedding search](#embedding-search)
- [Convexity](#convexity)
- [Verdicts do not travel](#verdicts-do-not-travel)
- [Certificates](#certificates)
- [The diagram normal form](#the-diagram-normal-form)
- [Edge orientation](#edge-orientation)
- [Evidence, not equality](#evidence-not-equality)
- [What the canon does not decide](#what-the-canon-does-not-decide)
- [Crate boundary](#crate-boundary)
- [Boundary wrappers](#boundary-wrappers)
- [License](#license)

<!-- tocstop -->

## Synopsis

**What.** A `Wiring` is one diagram with an interface: `Generator`s, each a `GeneratorLabel` over ordered source and target `Wire`s, and an `Interface` of input and output ports. `Wiring::assemble` is its only constructor and refuses everything outside the monogamous acyclic fragment. `read_spine` reads a sequent command pattern from `gandr-theory-cell-complexes` as a wiring. `embeddings` finds every `Embedding` of a pattern wiring into a target wiring, convexity decided by a route computed from the pattern, and keeps every structurally complete candidate that fails convexity as a `ConvexityRefusal` naming the path. `Embedding::check` reads an embedding as a certificate against two diagrams and refuses a forgery by the conjunct it fails; `Matching::ambiguity` names where several admitted readings of one pattern diverge. `canonicalize` renumbers a wiring into its `CanonicalDiagram` and returns the `Relabelling` that did it, which `Relabelling::verify` checks as an isomorphism against the input; `same_diagram` decides whether two wirings denote one diagram and answers with the shared form and both relabellings, or with the first place the two forms part. The crate is `no_std` and depends on `core`, `alloc`, `gandr-theory-cell-complexes` and `quenchant-shape`.

**Why.** A circuit pattern is neither a spine nor a tree: it may have several roots, reconverge, or hold components with no wire between them, so the substrate's one-sided matcher over command patterns cannot match it. Matching becomes sub-diagram embedding, and an embedding is a legal rewrite site only when it is convex. Both the embedding and the convexity verdict are claims a consumer has to be able to refute, so each comes with the data that refutes it. Two presentations of one diagram differ only in how they number wires and generators, so a consumer that keys on diagrams needs one representative per class, and a verdict that two diagrams are one is a claim too, with the isomorphism as its evidence.

**How.** Monogamy, at most one producer and one consumer per wire, means one assigned wire forces the generators on either side of it, so the search seeds one choice per connected component and propagates the rest. The same forcing makes the canon a traversal rather than a search: the boundary numbers its wires by position, each numbered wire numbers its producer and consumer, and only a component the boundary never reaches needs a seed, chosen by trying every member. Every walk is a loop over explicit frames; nothing recurses on diagram size. Absence and refusal are values: a lookup that can miss returns `Maybe` with a named reason, a refused operation returns `Result` with a typed refusal naming its locus.

## References

- Filippo Bonchi, Fabio Gadducci, Aleks Kissinger, Paweł Sobociński, and Fabio Zanasi. "String Diagram Rewrite Theory II: Rewriting with Symmetric Monoidal Structure." _Mathematical Structures in Computer Science_ 32, 4 (2022), pages 511–541. `doi:10.1017/S0960129522000317`; preprint `arXiv:2104.14686` — monogamous acyclic hypergraphs with interfaces as the representation of symmetric monoidal string diagrams, convex matching, left-connectedness, and the example of two disjoint matches that interfere through a path outside both, which the blocking-shape test pins.
- Paweł Sobociński, Paul W. Wilson, and Fabio Zanasi. "CARTOGRAPHER: A Tool for String Diagrammatic Reasoning (Tool Paper)." In _8th Conference on Algebra and Coalgebra in Computer Science (CALCO 2019)_, LIPIcs 139, pages 20:1–20:7, 2019. `doi:10.4230/LIPIcs.CALCO.2019.20` — diagrams as hypergraph cospans with ordered ports, matched and rewritten under convexity, the representation `Wiring` reads.
- Piergiulio Katis, Nicoletta Sabadini, and Robert F. C. Walters. "Feedback, Trace and Fixed-Point Semantics." _RAIRO – Theoretical Informatics and Applications_ 36, 2 (2002). `doi:10.1051/ita:2002009` — feedback as a primitive distinct from trace, the ground for cutting a delayed back-edge open rather than reading the closed loop.
- Pierre-Louis Curien and Hugo Herbelin. "The Duality of Computation." In _Proceedings of the Fifth ACM SIGPLAN International Conference on Functional Programming (ICFP '00)_, pages 233–243, September 2000. `doi:10.1145/351240.351262` — the command `⟨p | c⟩` of a producer against a consumer that the spine reading lays out as a diagram.
- Jovana Obradović. "Cyclic operads: syntactic, algebraic and categorified aspects." PhD thesis, Université Paris Diderot – Paris 7 – Sorbonne Paris Cité, 2017. `hal:tel-01676983` — the corolla and edge decompositions, the two extremes the canon's edge orientation is chosen between.
- Antonin Delpeuch and Jamie Vicary. "Normalization for Planar String Diagrams and a Quadratic Equivalence Algorithm." _Logical Methods in Computer Science_ 18, 1 (2022), paper 10. `doi:10.46298/lmcs-18(1:10)2022`; preprint `arXiv:1804.07832` — the planar quotient, up to exchange moves, that does not stand in for the symmetric one the canon decides.
- Shahn Majid and Konstanze Rietsch. "Planar Spider Theorem and Asymmetric Frobenius Algebras." Preprint, 2021. `arXiv:2109.12106` — the spider normal form for diagrams whose wires merge, outside the monogamous fragment and not built here.

## Provided features

- `Wiring`, `Generator`, `GeneratorLabel`, `GeneratorName`, `GeneratorSort`, `Interface`, `WiringObstruction`, the incidence lookups `producer_of` and `consumer_of`: a diagram with ordered ports and a discrete interface, built only inside the monogamous acyclic fragment. Witnesses: `interface::tests::an_assembled_wiring_answers_its_incidence`, `interface::tests::the_wiring_refuses_a_fan_in`, `interface::tests::the_wiring_refuses_a_fan_out`, `interface::tests::the_wiring_refuses_an_out_of_range_generator_wire`, `interface::tests::the_wiring_refuses_an_out_of_range_boundary_wire`, `interface::tests::the_wiring_refuses_a_repeated_port_on_one_generator`, `interface::tests::the_wiring_refuses_a_repeated_boundary_port`, `interface::tests::the_wiring_refuses_a_produced_boundary_input`, `interface::tests::the_wiring_refuses_a_consumed_boundary_output`, `interface::tests::the_wiring_refuses_an_undeclared_open_wire`, `interface::tests::the_wiring_refuses_an_undeclared_open_input`, `interface::tests::the_wiring_refuses_a_self_looping_generator`, `interface::tests::the_wiring_refuses_a_directed_cycle`.
- `Components`, `Wiring::components`: the generators partitioned into weakly connected components, port-free generators as singletons. Witnesses: `interface::tests::the_components_partition_the_generators`, `interface::tests::a_component_joins_through_a_shared_wire_in_both_directions`, `interface::tests::a_port_free_generator_is_its_own_component`.
- `PartialBijection`, `Seam`, `BijectionClash`: an injective partial map of wires that refuses a clash, and the seam datum as its restriction to each half of an interface. Witness: `interface::tests::a_partial_bijection_stays_injective`.
- `read_spine`, `SpineReading`, `SpineObstruction`: a sequent command pattern read as a wiring, with its cut wire and the port each metavariable became. Witnesses: `interface::spine::tests::a_spine_reads_as_its_generators_and_ports`, `interface::spine::tests::the_reading_declares_input_ports_in_first_occurrence_order`, `interface::spine::tests::a_terminal_is_a_closed_generator_not_a_port`, `interface::spine::tests::a_repeated_hole_is_refused_as_a_copy`, `interface::spine::tests::a_hole_at_both_polarities_reads_as_one_input_and_one_output`.
- `embeddings`, `embeddings_by_sweep`, `Matching`, `Embedding`, `ConvexityRefusal`, `MatchObstruction`, `MatchBudget`, `SearchSteps`: every embedding of a pattern into a target within a budget, non-convex candidates refused with their path, and a search that would exceed its budget declined rather than truncated. Witnesses: the `matching::tests` functions named in the `# Adequacy` section of `embeddings`, among them `matching::tests::a_multi_root_pattern_embeds`, `matching::tests::the_blocking_shape_is_refused_on_the_convexity_conjunct`, `matching::tests::the_embedding_matcher_agrees_with_the_one_sided_matcher_on_the_spine` and `matching::tests::an_exhausted_budget_declines_rather_than_truncating`.
- `connectivity`, `convexity_warrant`, `Connectivity`, `ConvexityWarrant`: the convexity route a pattern earns, computed and audited. Witnesses: `matching::tests::a_spine_pattern_is_strongly_connected`, `matching::tests::a_disconnected_pattern_is_not_strongly_connected`, `matching::tests::the_discharge_and_the_sweep_agree_where_both_apply`.
- `Embedding::claim`, `Embedding::check`, `EmbeddingObstruction`, `SeamHalf`: the certificate reader, refusing each forged conjunct by name. Witnesses: `matching::tests::the_searches_certificates_verify_against_their_own_diagrams` and the twelve `matching::tests::a_certificate_*` and `matching::tests::a_non_convex_certificate_is_refused_with_the_offending_path` refusals.
- `Matching::ambiguity`, `Ambiguity`, `Divergence`, `Discriminator`: the first difference of each later admission from the first. Witnesses: `matching::tests::a_unique_or_absent_match_reports_no_ambiguity`, `matching::tests::a_multi_admission_reports_its_first_divergences_in_order`, `matching::tests::a_bare_wire_ambiguity_discriminates_on_the_wire`, `matching::tests::two_orderings_of_port_free_generators_diverge_at_the_first_generator`.
- `canonicalize`, `CanonicalDiagram`, `Canonicalization`, `CanonicalDiagram::to_wiring`: one representative per class of presentations, numbered by a traversal and readable back as a diagram. Witnesses: `normal_form::tests::canonicalization_is_total_and_its_witness_verifies`, `normal_form::tests::the_boundary_is_numbered_before_the_interior`, `normal_form::tests::an_anchored_component_is_ordered_by_the_boundary_and_not_by_its_labels`, `normal_form::tests::a_visited_hyperedge_numbers_its_sources_before_its_targets`, `normal_form::tests::a_presentation_permutation_has_one_canonical_form`, `normal_form::tests::canonicalization_is_idempotent`, `normal_form::tests::a_component_with_no_boundary_port_is_seeded_by_minimizing`, `normal_form::tests::components_with_no_boundary_port_are_committed_in_canonical_order`, `normal_form::tests::the_least_linearization_is_compared_past_its_first_record`, `normal_form::tests::two_isomorphic_anchorless_components_still_have_one_form`, `normal_form::tests::an_isolated_wire_is_numbered_from_the_boundary_alone`, and the property `tests::normal_form::every_presentation_permutation_canonicalizes_alike`.
- `same_diagram`, `DiagramEquality`, `SharedCanon`, `DiagramDivergence`: whether two wirings denote one diagram, with both relabellings on one arm and the first divergence on the other. Witnesses: `normal_form::tests::the_canon_agrees_with_the_cospan_isomorphism_oracle`, `normal_form::tests::the_canon_separates_a_permuted_boundary`, `normal_form::tests::the_canon_separates_a_permuted_port_list`, `normal_form::tests::the_canon_separates_a_label_worn_at_two_sorts`, `normal_form::tests::the_canon_separates_one_generator_multiset_wired_two_ways`, `normal_form::tests::same_diagram_locates_a_count_difference`, `normal_form::tests::same_diagram_locates_a_boundary_difference`, `normal_form::tests::same_diagram_locates_a_hyperedge_difference`.
- `Relabelling`, `Relabelling::verify`, `RelabellingDefect`, `Leg`, `PortPosition`, `PortCount`, the lookups `Relabelling::image_of_wire` and `Relabelling::image_of_generator` with their `relabelled_wire` and `relabelled_generator` absence reasons: the renumbering as a checkable isomorphism, a defect refused by its locus. Witnesses: `normal_form::tests::the_verifier_refuses_a_defective_wire_map`, `normal_form::tests::the_verifier_refuses_a_defective_generator_map`, `normal_form::tests::the_verifier_refuses_a_record_that_does_not_correspond`, `normal_form::tests::the_verifier_refuses_a_boundary_that_does_not_commute`.
- `CanonicalDiagram` as a map key: `Ord` and `Hash`, holding no address, stamp or session state, so presentations of one diagram land on one entry. Witnesses: `normal_form::tests::presentations_of_one_diagram_collapse_to_one_key`, `normal_form::tests::equal_canonical_forms_hash_alike`.

## Expected features

- **Diagrams inside the fragment.** A caller hands the matcher only what `Wiring::assemble` accepts. A body closed by a delayed feedback loop is cyclic and refused; the caller cuts the delay open before matching, and reads no verdict back onto the closed form.
- **A sized budget.** The caller sizes `MatchBudget` for its pattern and target. The search declines with `MatchObstruction::BudgetExhausted` rather than return a partial enumeration, so a budget too small for the work is a refusal the caller sees, never a silently short answer.
- **Rule-sized patterns.** The certificate reader checks generator injectivity pairwise, quadratic in the pattern's generator count, and the search copies its partial assignment once per candidate seed; both are sized for rule patterns against a body, not for patterns the size of the target.
- **Anchorless components of modest size.** A component the boundary never reaches is canonicalized by trying each of its `k` generators as the seed, `O(k²)` in that component; a diagram with large closed components pays that cost on every `canonicalize` and `same_diagram`.

## Examples

Find the one occurrence of a two-generator pattern in a larger diagram and check the certificate the search issued.

```rust
use gandr_theory_circuit_algebras::ConvexityWarrant;
use gandr_theory_circuit_algebras::Generator;
use gandr_theory_circuit_algebras::GeneratorLabel;
use gandr_theory_circuit_algebras::GeneratorSort;
use gandr_theory_circuit_algebras::Interface;
use gandr_theory_circuit_algebras::MatchBudget;
use gandr_theory_circuit_algebras::MatchCount;
use gandr_theory_circuit_algebras::Wire;
use gandr_theory_circuit_algebras::WireCount;
use gandr_theory_circuit_algebras::Wiring;
use gandr_theory_circuit_algebras::embeddings;

fn example() -> Result<(), Box<dyn core::error::Error>> {
    let value = |name: &str| GeneratorLabel::new(name, GeneratorSort::Value);
    let wires = |indices: &[usize]| -> Vec<Wire> { indices.iter().copied().map(Wire::from).collect() };
    // f: (0) -> (1), then g: (1) -> (2)
    let pattern = Wiring::assemble(
        WireCount::from(3),
        vec![
            Generator::new(value("f"), wires(&[0]), wires(&[1])),
            Generator::new(value("g"), wires(&[1]), wires(&[2])),
        ],
        Interface::new(wires(&[0]), wires(&[2])),
    )?;
    // e: (0) -> (1), f: (1) -> (2), g: (2) -> (3)
    let target = Wiring::assemble(
        WireCount::from(4),
        vec![
            Generator::new(value("e"), wires(&[0]), wires(&[1])),
            Generator::new(value("f"), wires(&[1]), wires(&[2])),
            Generator::new(value("g"), wires(&[2]), wires(&[3])),
        ],
        Interface::new(wires(&[0]), wires(&[3])),
    )?;
    let matching = embeddings(&pattern, &target, MatchBudget::from(1_000))?;
    assert_eq!(MatchCount::from(1), matching.admitted_count());
    let certificate = &matching.admitted()[0];
    assert_eq!(
        Ok(ConvexityWarrant::StronglyConnectedOverAcyclicTarget),
        certificate.check(&pattern, &target)
    );
    Ok(())
}
```

Read a command pattern whose one name is worn at both polarities.

```rust
use gandr_theory_cell_complexes::CmdPat;
use gandr_theory_cell_complexes::ConsPat;
use gandr_theory_cell_complexes::MetaVar;
use gandr_theory_cell_complexes::Polarity;
use gandr_theory_cell_complexes::ProdPat;
use gandr_theory_circuit_algebras::read_spine;

fn example() -> Result<(), Box<dyn core::error::Error>> {
    // ⟨r | seam(; r)⟩
    let pattern = CmdPat::cut(
        Polarity::Positive,
        ProdPat::meta("r"),
        ConsPat::op("seam", [], ConsPat::meta("r")),
    );
    let reading = read_spine(&pattern)?;
    let boundary = reading.wiring().boundary();
    assert_eq!(1, boundary.inputs().len());
    assert_eq!(1, boundary.outputs().len());
    assert_ne!(
        reading.port_of(&MetaVar::producer("r")),
        reading.port_of(&MetaVar::consumer("r"))
    );
    Ok(())
}
```

Decide that two presentations denote one diagram and check the evidence.

```rust
use gandr_theory_circuit_algebras::DiagramEquality;
use gandr_theory_circuit_algebras::Generator;
use gandr_theory_circuit_algebras::GeneratorLabel;
use gandr_theory_circuit_algebras::GeneratorSort;
use gandr_theory_circuit_algebras::Interface;
use gandr_theory_circuit_algebras::Wire;
use gandr_theory_circuit_algebras::WireCount;
use gandr_theory_circuit_algebras::Wiring;
use gandr_theory_circuit_algebras::canonicalize;
use gandr_theory_circuit_algebras::same_diagram;

fn example() -> Result<(), Box<dyn core::error::Error>> {
    let value = |name: &str| GeneratorLabel::new(name, GeneratorSort::Value);
    let wires = |indices: &[usize]| -> Vec<Wire> { indices.iter().copied().map(Wire::from).collect() };
    // f: (0) -> (1), then g: (1) -> (2)
    let left = Wiring::assemble(
        WireCount::from(3),
        vec![
            Generator::new(value("f"), wires(&[0]), wires(&[1])),
            Generator::new(value("g"), wires(&[1]), wires(&[2])),
        ],
        Interface::new(wires(&[0]), wires(&[2])),
    )?;
    // The same composite, its wires renumbered and its generators relisted.
    let right = Wiring::assemble(
        WireCount::from(3),
        vec![
            Generator::new(value("g"), wires(&[0]), wires(&[1])),
            Generator::new(value("f"), wires(&[2]), wires(&[0])),
        ],
        Interface::new(wires(&[2]), wires(&[1])),
    )?;
    let DiagramEquality::Same(shared) = same_diagram(&left, &right) else {
        return Err("two presentations of one diagram".into());
    };
    assert_eq!(Ok(()), shared.left().verify(&left, shared.form()));
    assert_eq!(Ok(()), shared.right().verify(&right, shared.form()));
    assert_eq!(shared.form(), canonicalize(&left).form());
    Ok(())
}
```

Nontrivial operations carry executable `#[spec]` predicates beside their `# Adequacy` witnesses. The predicates cover state transitions, certificate correspondence and refusal payloads without repeating allocating graph searches. Reachability, convexity and presentation invariance additionally rely on the named fixture and differential witnesses. The opaque port-image iterator and generated-presentation strategy carry reasoned backend exemptions.

Run the tests:

```sh
cargo nextest run -p gandr-theory-circuit-algebras
RUSTFLAGS="--cfg anodized_panic" cargo test -p gandr-theory-circuit-algebras --all-targets
```

## The fragment, at construction

`Wiring::assemble` refuses a diagram outside the monogamous acyclic fragment: an undeclared wire on a generator or the interface, a wire with two producers or two consumers (a repeated port on one generator counts), a repeated interface port, a produced input, a consumed output, an open wire the interface does not declare, and a directed cycle. Every theorem the matcher quotes — that one assigned wire forces its neighbours, that the discharge route is sound, that a re-closed body is never a target — has these as hypotheses, and holding them as an invariant of the type means no function here re-checks them and no caller can pass a diagram that breaks them.

The cycle refusal names a generator on the cycle. An earlier implementation of this design named the first generator its topological sort left unsettled, which can sit downstream of a cycle without being on it; this one walks back from that generator until it closes a loop and names a member of the loop. Witness: `interface::tests::the_wiring_refuses_a_directed_cycle`, whose fixture lists the downstream generator first.

## Generator labels

A label is a name together with the role the name is worn in — a value constructor, an operation frame, a return-side frame, the terminal `★`, or a fired rewrite (`GeneratorSort`). Two boxes of one spelling in different roles are two generators: a return-side frame `K⁻(c)` and a nullary operation frame `K(; c)` share a name and an arity, and a name-only label would match one against the other where the one-sided matcher refuses both. The differential against that matcher carries the two rows that separate them.

## The spine reading

`read_spine` reads `⟨p | c⟩` as a diagram whose cut is one wire: the producer side is a tree of value generators feeding it, the consumer side a chain of frames reading it and ending at `★` or an open output. A producer metavariable becomes an input port and a consumer metavariable an output port, declared in first-occurrence order; a metavariable occurring twice is a copy, refused, because a wire has one producer and one consumer.

A name worn at both polarities, a producer `r` and a consumer `r` as in `⟨r | seam(; r)⟩`, reads as two interface nodes: one input and one output. That is the matcher's own keying — the substrate's substitution keys a metavariable by name and category — so the reading and the one-sided matcher agree on the shape, and the differential carries four rows of it. `SpineReading::port_of` reports which port each metavariable became. Witness: `interface::spine::tests::a_hole_at_both_polarities_reads_as_one_input_and_one_output`.

- **Alternatives.** Refusing the shape leaves a reading the substrate's matcher already gives undefined here. Reading the name as one node at mixed variance, as the substrate's derived cell metadata does when it classifies the hole as a seam, makes the diagram a cycle through the cut, which the fragment refuses.
- **Reversal.** A ruling that the diagram view should not read the shape restores a refusal at the reader and turns that one test back into a refusal test; the matcher is untouched.

## Embedding search

An `Embedding` is a monomorphism of diagrams: injective on generators and on wires, label-, arity-, incidence- and port-order-preserving. The search seeds one nondeterministic choice per connected component of the pattern — a component's lowest-positioned generator against every target generator, or a bare wire against every target wire — and propagates each choice through monogamy, which forces the image of every generator on either side of an assigned wire. A step is one pending assignment resolved; `Matching::steps` reports them, and the multi-root fixture pins its cost at exactly 24, which separates one seed per component from a coarser seed set. The search walks a stack of explicit frames and enumerates candidates in target order, so the enumeration is deterministic.

## Convexity

A match is convex when no directed path leaves its image and returns to it. The condition is global, so it is checked once per complete candidate, by one of two routes computed from the pattern and never taken from a caller:

- **Discharged** (`ConvexityWarrant::StronglyConnectedOverAcyclicTarget`): when every input port of the pattern reaches every output port, no match into an acyclic target can fail convexity. A path leaving the image does so at an image output and returns at an image input; boundary honesty makes those the images of a declared output and a declared input, strong connectivity joins that input to that output inside the image, and the two paths compose to a cycle the target cannot hold. The argument holds vacuously when either port list is empty, and a component with no open port contributes no endpoint.
- **Swept** (`ConvexityWarrant::SweptOverTheComplement`): a forward walk from every image output through every target generator outside the image, looking for an image input. Nothing is removed from the target first, so the verdict is about the diagram as given.

The discharge is audited rather than trusted: `embeddings_by_sweep` sweeps unconditionally, and the tests compare it against the discharge over the fixtures where the argument above is likeliest to be wrong.

The variant name says what is checked: one condition on one pattern, strong connectivity, plus the target's acyclicity. The literature's phrase for the route is "left-connected over an acyclic target", but left-connectedness constrains a whole rule system — left-linear rules, monogamous acyclic on both sides, every left-hand side strongly connected — and the substrate admits rules that repeat a hole on the right, so the system-level condition is not what holds. The substrate's `ConvexityDischarge` carries the same variant name.

- **Alternatives.** The literature's phrase, with the precision carried by the doc comment alone.
- **Reversal.** A ruling that the literature's phrase is authoritative renames the variant here and in the substrate together.

The sweep shares one visited set across the walks from every image output. A wire an earlier walk reached without finding an image input reaches none, so skipping it on a later walk changes no verdict, and the sweep costs one pass over the target per candidate rather than one pass per image output. An earlier implementation of this design kept a visited set per output; the result is identical and the cost is the one the design priced.

## Verdicts do not travel

Convexity is broken by the existence of a path, and closing a delayed feedback loop adds an edge from an output of a body to an input of it, so a verdict on the cut-open body says nothing about the closed one. Two placements keep a cut-open verdict from being read on the closed form. The closed body is cyclic, so `Wiring::assemble` refuses it and it is never a target. And a verdict is computed per target: `Matching` and `ConvexityRefusal` have no public constructor, and an `Embedding` claimed from outside carries no verdict, because `Embedding::check` sweeps the target it is given whatever warrant the claim names. Witness: `matching::tests::a_cut_open_verdict_does_not_travel_to_the_re_closed_form`.

## Certificates

An `Embedding` is evidence its consumer refutes, not evidence its producer asserts. `Embedding::claim` is public so a certificate from outside the search — stored, transmitted, or produced by another matcher — can be read; a claim asserts nothing. `Embedding::check` re-derives every conjunct from the two diagrams in a fixed order and refuses at the first that fails, naming the locus: the image's length, then per pattern generator its range, label, arity and incidence, then generator injectivity, then the wire map's totality, range and width, then the seam, then the warrant, then the sweep. The seam is derived data, the wire map restricted to the pattern's interface, so a seam that disagrees is a forgery rather than a second opinion. Extra wire pairs outside the pattern are refused rather than ignored, because two certificates differing only in them would compare unequal while denoting one embedding.

## The diagram normal form

Two presentations of one diagram differ only in how they number wires and generators. The relation `same_diagram` decides is cospan isomorphism over the port bijection: a renumbering that preserves every label, arity and ordered port list and commutes with both interface legs position by position. `canonicalize` picks one representative per class by renumbering in the one order a traversal admits:

1. The boundary takes the lowest wire numbers, the input leg in order and then the output leg, skipping a wire already numbered. An isomorphism fixes boundary positions, so numbering by position is invariant.
2. A cursor walks the numbered wires in order and visits each wire's producer, then its consumer. A visited generator takes the next generator number and numbers its unnumbered ports, sources in port order and then targets. No step chooses.
3. A component the boundary never reaches has no anchor, so every member is tried as its seed and the least linearization wins; the anchorless components are then committed in the order of their winners. Both minimums range over the diagram's own content, and both read the whole linearization, because members sharing a label and an arity tie on their first record.

Two premises carry the procedure. Monogamy makes the walk choice-free and the wiring a faithful index: a wire with two producers could only be recorded by losing one. Boundary honesty makes the numbering total, an isolated wire being numbered only because both legs declare it, and leaves the producer-before-consumer order unobservable, because when the cursor reaches a wire at most one of its sides is unvisited. Acyclicity is not a premise: the traversal stops on its visited sets and is canonical with or without a cycle.

A component with a boundary port costs one traversal and an anchorless component of `k` generators costs `k`; nothing searches, because one numbered wire forces a generator. An earlier implementation of this design built each trial linearization's records to compare it, cloning every label once per trial; this one compares a trial against the incumbent by reading both traversals in place and builds records once, from the winner. The form is identical.

The tests check the canon against a cospan-isomorphism oracle that searches generator bijections over every ordered pair of 31 fixtures (`normal_form::tests::the_canon_agrees_with_the_cospan_isomorphism_oracle`), and a property renumbers and relists generated diagrams biased toward anchorless components, port-free generators and isolated wires, where an order leak would surface (`tests::normal_form::every_presentation_permutation_canonicalizes_alike`).

## Edge orientation

A canonical linearization can cut a diagram at a vertex, a generator and the pieces its removal leaves (the corolla decomposition), or at an edge, a wire and its two sides; mixed styles lie between. The canon takes the edge orientation, as a traversal. Monogamy tells a wire's two sides apart by direction, so the edge cut chooses nothing, while removing a generator leaves one piece per port to be sequenced in an order the corolla does not supply. The order a vertex cut would borrow is the port order the traversal already consumes, and an interface is a list of wires, so its anchor is already an edge datum. A traversal also owes no confluence argument, because no rewriting relation produces the form.

- **Alternatives.** The corolla decomposition or a mixed style, produced by rewriting toward a normal form that then has to be shown confluent; a general graph canonicalizer, which searches where monogamy forces.
- **Reversal.** A generator whose ports are not totally ordered, which gives the traversal a tie-break of its own and moves the choice toward a mixed style.

## Evidence, not equality

`same_diagram` answers with evidence on both arms. `DiagramEquality::Same` carries the shared form with both relabellings, the two halves of the isomorphism between the inputs; `DiagramEquality::Distinct` carries the first place the forms part as a `DiagramDivergence`. `Relabelling` has no public constructor, and `Relabelling::verify` re-derives from the source and the form that the relabelling is a bijection on wires and on generators, that each record is its source generator's image (label, then each leg's arity and ports), and that both legs commute; a defect is a `RelabellingDefect` naming its locus.

`same_diagram` compares what no renumbering changes, the wire count, the generator count and each leg's arity, before canonicalizing either side, so diagrams that differ there are told apart without a traversal and the divergence names those counts before any port or record. An earlier implementation of this design canonicalized both sides first and compared each leg's arity and ports together, input leg then output leg. The verdict is identical; the located divergence differs only for two diagrams that differ both in an input port and in the output leg's arity, where this one names the arity.

## What the canon does not decide

- **The rewriting normal form.** That runs a rule system to completion and is a property of the theory; the canon is a property of the representation and rewrites nothing.
- **Construction terms.** A circuit also reads as a term built from merger and contraction, and a canonical form of those terms is another object at another layer. That the two canons agree is neither assumed nor established here.
- **Planar equivalence.** Wires here cross freely and the interface is the only order; the planar quotient up to exchange moves is a different relation.
- **Merging wires.** The spider normal form for diagrams whose wires merge lies outside the monogamous fragment.

`CanonicalDiagram` is a map key, but interning diagrams by content, minting identities from the key, is refused: a content key is sound only once the diagram form is shown to agree with the construction-term reading of the same circuit.

- **Alternatives.** An interner over the diagram form now, whose identities a later disagreement with the construction-term canon would split; an interner keyed on construction terms, which waits on that canon.
- **Reversal.** The agreement is established; interning lands with its storage reader.

## Crate boundary

No rewriting engine depends on this crate. A matcher reaches an engine only through a seam supplied where the engine is instantiated, so the engines stay generic over the cell alphabet and this crate stays a leaf above the substrate.

The crate takes no edge to `gandr-theory-graphs`. It needs weakly connected components for its seeds and the component partition, and port-ordered traversal; that crate's algorithms read port-blind successor rows and do not offer components.

- **Alternatives.** Adding a components procedure to `gandr-theory-graphs` with this crate as its one reader spreads one unit across two crates and still leaves port order here; taking the edge for cycle evidence alone puts a graph library under the substrate's path for one call.
- **Reversal.** `gandr-theory-graphs` gains a components procedure for a second reader, or a later alphabet needs a wiring's condensation.

## Boundary wrappers

Every count, index, budget and verdict a signature here crosses is a transparent wrapper of this crate's own (`WireCount`, `EdgeCount`, `PairCount`, `ComponentIndex`, `MatchBudget`, `SearchSteps`, `MatchCount`, `AdmittedIndex`, …), converting with `From` both ways. `Wire` and `Edge` are wrappers too, so a wire is never passed where a generator position is expected. The substrate's wrappers stay the substrate's: one shared vocabulary would make every budget here a substrate change.

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
