# gandr-theory-sites

The carrier's shapes as a site with stick-free objects: a morphism class over the wirings `gandr-theory-circuit-algebras` admits, its degree, and the finite checks of its generalized Reedy structure.

A circuit algebra has two units. The identity wire, a bare wire from an input port to an output port with no operation on it, is the unit of contraction; the empty diagram is the unit of the external product. The site keeps the second and drops the first: **a stick is not a shape**. A wire with no operation on it may run inside a shape, between two of its vertices; alone, it is never an object.

<!-- toc -->
- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Where the detail lives](#where-the-detail-lives)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** A shape is a wiring the carrier admits, read as a graph, with no stick component: generators are vertices, and each wire records its producer and consumer or an open end. A map of shapes sends each vertex to a disjoint sub-graph of the target with the same boundary, and each wire to a wire, where two wires land on one only as a contraction of an output leg with an input leg. Deleting a vertex with no ports, a point, is the one codegeneracy the class holds.

**Why.** A Reedy structure on the site indexes presheaves by a degree: it lets a presheaf be built, and its fibrancy checked, one degree at a time. That needs maps against which a degree, a factorization and a pushout can be checked, and objects for which they hold. With the identity wire as an object no degree exists, since a stick includes into two sticks and two sticks fuse back to one, composing to the identity; without it, every generalized Reedy axiom holds at the bound, under a degree into the naturals.

**How.** Shapes are enumerated up to a size bound through `Wiring::assemble`, so the carrier decides which shapes exist, and the constructors refuse a stick by naming its wire. Maps between two shapes are enumerated by assigning target vertices to source vertices and wires to wires, and each candidate passes one validator that states the class. Each condition runs over every shape, map, composable pair or span at the bound, in increasing size, and reports its case count and the first failing case as the smallest counter-example.

## Provided features

- `Shape`, `End`, `Ends`, `WireKind`, `VertexKind`, `ShapeKey`, `ShapeObstruction`, `shapes_up_to`: stick-free shapes through the carrier, the stick refused by name, their statistics, isomorphism classes, and the enumeration of every class up to a size. Witnesses: `tests::shapes::the_enumeration_counts_match_an_independent_count`, `tests::shapes::the_constructor_refuses_by_variant`, `tests::shapes::a_stick_is_refused_by_name`, `tests::shapes::a_wiring_reads_back_as_its_shape`, `tests::shapes::wire_kinds_follow_the_open_ends`, `tests::shapes::points_are_the_vertices_no_wire_touches`, `tests::shapes::a_relabelled_shape_keys_alike`.
- `SiteMap`, `VertexSet`, `MapObstruction`, `CompositionMismatch`, `MapForm`, `homs`: the morphism class, its one validator, composition, the two classes, invertibility, and the enumeration of a hom set. Witnesses: `tests::maps::vertex_sets_hold_the_first_and_last_vertex`, `tests::maps::hom_counts_match_hand_counts`, `tests::maps::the_enumerator_agrees_with_brute_force`, `tests::maps::the_class_is_a_category_at_the_bound`, `tests::maps::a_contraction_composes_with_a_deletion`, `tests::maps::invertibility_matches_two_sided_inverses`, `tests::maps::map_forms_read_back`, `tests::maps::the_two_classes_sort_the_fixtures`, `map::tests::each_clause_refuses_by_variant`, `map::tests::composition_refuses_a_missing_image`.
- `Catalogue`: every class and every hom set at a bound. Witness: `tests::maps::the_catalogue_serves_pinned_hom_sets`.
- `Degree`: vertices plus inner wires. Witness: `tests::shapes::the_degree_counts_vertices_and_inner_wires`.
- `Site`, `identities`, `closure`, `intersection`, `invertibility`, `degree_order`, `direct_core`, `latching`, `factorization`, `rigidity`, `dual_rigidity`, `split_lowering`, `pushouts`, `Outcome`: the generalized Reedy conditions, each answering with its case count and its smallest counter-example. Witnesses: `tests::reedy::the_class_is_a_category_with_two_classes`, `tests::reedy::the_degree_orders_both_classes`, `tests::reedy::the_point_free_core_is_direct`, `tests::reedy::the_latching_category_is_finite`, `tests::reedy::every_map_factors_through_a_point_deletion`, `tests::reedy::both_rigidity_axioms_hold`, `tests::reedy::a_closed_substitution_has_no_pushout_with_a_deletion`, `tests::point_count::the_codegeneracy_is_split`.
- `core_decomposition`, `grounded_stratum`, `deletion_classes`, `codegeneracies`, `corolla`: the point-count grade. Witnesses: `tests::point_count::every_shape_is_its_core_beside_its_points`, `tests::point_count::grounded_shapes_are_the_zero_stratum`, `tests::point_count::deletions_are_addressed_by_kernels`, `tests::point_count::the_codegeneracy_is_split`, `tests::units::the_point_reaches_each_point_once`.
- `merge`, `scalars`, `labelled_by_arity`, `unit_property`: the external product and the finite check that the empty diagram is its one weak unit. Witnesses: `tests::units::the_external_product_sets_wirings_side_by_side`, `tests::units::scalars_are_counted_and_labelled`, `tests::units::the_empty_diagram_is_the_only_unit`.
- `segal`, `Cocones`, `Cocone`, `Inclusion`, `Graft`, `Leg`, `SegalFailure`, `SegalDefect`: the Segal condition at degree `n`, each shape of degree two to `n` the colimit of its corollas along its grafting pushouts, over the families of maps whose images are disjoint, and refused at the first shape, test shape and family over the blanket families. Witness: `tests::stratum::a_shape_of_degree_two_is_the_colimit_of_its_corollas`.
- `SegalStratum`, `Uncertified`, `Species`, `Profile`, `Element`, `Labelling`, `Table`, `Bijection`, `Equivalence`, `Natural`, `restrict`, `Defect`: the stratum certified at degree `n` through the corolla and Segal conditions, graphical species and their terms at every shape, an equivalence of species as the finite certificate natural along the corolla automorphisms, its extension to the free algebras, and the corolla restriction that reflects a natural isomorphism of the free algebras back to the species. Witnesses: `tests::stratum::the_corolla_stratum_is_certified_at_degree_one`, `tests::stratum::a_shape_of_degree_two_is_the_colimit_of_its_corollas`, `tests::stratum::an_equivalence_commutes_with_the_corolla_automorphisms`, `tests::stratum::restriction_reflects_a_natural_isomorphism_to_its_species`.

The record of why the objects are stick-free is four tests on raw wirings, read as graphs before admission so that a bare wire can stand as an object: `negatives::sticks_as_objects_admit_no_degree`, `negatives::connected_objects_lose_the_point_deletion`, `negatives::vertex_end_fusions_are_not_closed`, `negatives::contraction_lowering_loses_the_factorization`. Each asserts the one fact that rules its alternative out.

## Expected features

- **Bounded verdicts.** A verdict holds at the bound it was run at; [`catalogue`](src/catalogue.rs) states what that covers.
- **Small bounds.** The catalogue computes every hom set between every pair of classes, and the closure check every composable pair over every triple, so the cost grows with the square and the cube of the class count. Size five holds 81 classes and runs every check in under half a minute in release; size six holds 223.
- **Shapes of at most 64 vertices.** A vertex set is one machine word; the constructors refuse a larger shape.

## Examples

Refuse the identity wire, count the maps from the point to the closed two-chain, and run one condition.

```rust
use gandr_theory_circuit_algebras::Edge;
use gandr_theory_circuit_algebras::EdgeCount;
use gandr_theory_circuit_algebras::Wire;
use gandr_theory_sites::Catalogue;
use gandr_theory_sites::End;
use gandr_theory_sites::Ends;
use gandr_theory_sites::Shape;
use gandr_theory_sites::ShapeObstruction;
use gandr_theory_sites::ShapeSize;
use gandr_theory_sites::Site;
use gandr_theory_sites::Verdict;
use gandr_theory_sites::direct_core;
use gandr_theory_sites::homs;

fn example() -> Result<(), Box<dyn core::error::Error>> {
    let stick = Shape::from_ends(EdgeCount::from(0), vec![Ends::new(End::Open, End::Open)]);
    assert_eq!(stick, Err(ShapeObstruction::Stick { wire: Wire::from(0) }));
    let point = Shape::from_ends(EdgeCount::from(1), vec![])?;
    let chain = Shape::from_ends(
        EdgeCount::from(2),
        vec![Ends::new(End::Vertex(Edge::from(0)), End::Vertex(Edge::from(1)))],
    )?;
    // the point deleted and the chain left out, or the point substituted by the whole chain
    assert_eq!(homs(&point, &chain).len(), 2);
    let catalogue = Catalogue::build(ShapeSize::from(4))?;
    assert_eq!(direct_core(&Site::new(&catalogue)).verdict(), Verdict::Holds);
    Ok(())
}
```

Print every condition's outcome at the bounds below, then run the tests in both modes:

```sh
cargo run --release -p gandr-theory-sites --example suites
cargo nextest run -p gandr-theory-sites
RUSTFLAGS="--cfg anodized_panic" CARGO_TARGET_DIR=target/enforcing cargo nextest run -p gandr-theory-sites
```

## Where the detail lives

Mechanism, decisions with their alternatives and reversals, and witnesses live in the rustdoc beside the code:

| Topic | Module |
| ----- | ------ |
| Objects, maps, what the class borrows and decides, boundary wrappers, references | [`src/lib.rs`](src/lib.rs) |
| The degree | [`degree`](src/degree.rs) |
| What a bound proves | [`catalogue`](src/catalogue.rs) |
| What the checks find at the bound | [`conditions`](src/conditions.rs) |
| The Segal condition, its cocones and the families it counts | [`segal`](src/segal.rs) |
| The strata, their alphabet and range, `ua` and `ua-desc` | [`stratum`](src/stratum.rs) |

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
