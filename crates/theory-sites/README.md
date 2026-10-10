# gandr-theory-sites

The carrier's shapes as a site with stick-free objects: a morphism class over the wirings `gandr-theory-circuit-algebras` admits, its degree, and the finite checks of its generalized Reedy structure.

A circuit algebra has two units. The identity wire, a bare wire from an input port to an output port with no operation on it, is the unit of contraction; the empty diagram is the unit of the external product. The site keeps the second and drops the first: **a stick is not a shape**. A wire with no operation on it may run inside a shape, between two of its vertices; alone, it is never an object.

<!-- toc -->

- [Synopsis](#synopsis)
- [References](#references)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Objects](#objects)
- [Maps](#maps)
- [What the class borrows](#what-the-class-borrows)
- [What the class decides](#what-the-class-decides)
- [The degree](#the-degree)
- [What the checks find at the bound](#what-the-checks-find-at-the-bound)
- [What a bound proves](#what-a-bound-proves)
- [Boundary wrappers](#boundary-wrappers)
- [License](#license)

<!-- tocstop -->

## Synopsis

**What.** A shape is a wiring the carrier admits, read as a graph, with no stick component: generators are vertices, and each wire records its producer and consumer or an open end. A map of shapes sends each vertex to a disjoint sub-graph of the target with the same boundary, and each wire to a wire, where two wires land on one only as a contraction of an output leg with an input leg. Deleting a vertex with no ports, a point, is the one codegeneracy the class holds.

**Why.** A Reedy structure on the site indexes presheaves by a degree: it lets a presheaf be built, and its fibrancy checked, one degree at a time. That needs maps against which a degree, a factorization and a pushout can be checked, and objects for which they hold. With the identity wire as an object no degree exists, since a stick includes into two sticks and two sticks fuse back to one, composing to the identity; without it, every generalized Reedy axiom holds at the bound, under a degree into the naturals.

**How.** Shapes are enumerated up to a size bound through `Wiring::assemble`, so the carrier decides which shapes exist, and the constructors refuse a stick by naming its wire. Maps between two shapes are enumerated by assigning target vertices to source vertices and wires to wires, and each candidate passes one validator that states the class. Each condition runs over every shape, map, composable pair or span at the bound, in increasing size, and reports its case count and the first failing case as the smallest counter-example.

## References

- Clemens Berger and Ieke Moerdijk. "On an Extension of the Notion of Reedy Category." _Mathematische Zeitschrift_ 269, 3–4 (2011), pages 977–1004. `doi:10.1007/s00209-010-0770-x`; preprint `arXiv:0809.3341` — the generalized Reedy axioms the checks run at the bound: the two classes meeting in the isomorphisms, the degree, the factorization unique up to unique isomorphism, and the rigidity axiom (iv), with its dual for the opposite category.
- Philip Hackney, Marcy Robertson, and Donald Yau. "On Factorizations of Graphical Maps." _Homology, Homotopy and Applications_ 20, 2 (2018), pages 217–238. `doi:10.4310/HHA.2018.v20.n2.a11`; preprint `arXiv:1705.08546` — graphical maps as an edge map and a vertex-to-sub-graph map, contracting cofaces, the degree `|Vt| + |Edge_i|` and the generalized Reedy structure on connected graphs.
- Philip Hackney, Marcy Robertson, and Donald Yau. _Infinity Properads and Infinity Wheeled Properads_. Lecture Notes in Mathematics 2147, Springer, 2015. `doi:10.1007/978-3-319-20547-2`; preprint `arXiv:1410.6716` — outer and inner contracting cofaces, and that each creates one inner edge.
- Sophie Raynor. "Modular Operads, Iterated Distributive Laws and a Nerve Theorem for Circuit Algebras." Preprint, 2024–2026. `arXiv:2412.20262` — the non-unital circuit-algebra monad over graphs without stick components (Definition 5.6), the external product's unit (Definition 3.21, Remark 3.22), the empty graph as an admissible zero-graph, and the full Kleisli subcategory whose maps include folds.
- Michael Shulman. "Univalence for Inverse Diagrams and Homotopy Canonicity." _Mathematical Structures in Computer Science_ 25, 5 (2015). `doi:10.1017/S0960129514000565`; preprint `arXiv:1203.3253` — diagrams over an inverse category built in type theory by induction on degree, each stage a limit over the maps out of an object; a presheaf on the site is a diagram on its opposite, whose maps out of a shape are the site's latching maps into it.
- André Joyal and Joachim Kock. "Coherence for Weak Units." _Documenta Mathematica_ 18 (2013), pages 71–110. `doi:10.4171/dm/392`; preprint `arXiv:0907.4553` — a weak unit as a cancellable pseudo-idempotent, the property the unit check runs on scalars.

## Provided features

- `Shape`, `End`, `Ends`, `WireKind`, `VertexKind`, `ShapeKey`, `ShapeObstruction`, `shapes_up_to`: stick-free shapes through the carrier, the stick refused by name, their statistics, isomorphism classes, and the enumeration of every class up to a size. Witnesses: `tests::shapes::the_enumeration_counts_match_an_independent_count`, `tests::shapes::the_constructor_refuses_by_variant`, `tests::shapes::a_stick_is_refused_by_name`, `tests::shapes::a_wiring_reads_back_as_its_shape`, `tests::shapes::wire_kinds_follow_the_open_ends`, `tests::shapes::points_are_the_vertices_no_wire_touches`, `tests::shapes::a_relabelled_shape_keys_alike`.
- `SiteMap`, `VertexSet`, `MapObstruction`, `CompositionMismatch`, `MapForm`, `homs`: the morphism class, its one validator, composition, the two classes, invertibility, and the enumeration of a hom set. Witnesses: `tests::maps::vertex_sets_hold_the_first_and_last_vertex`, `tests::maps::hom_counts_match_hand_counts`, `tests::maps::the_enumerator_agrees_with_brute_force`, `tests::maps::the_class_is_a_category_at_the_bound`, `tests::maps::a_contraction_composes_with_a_deletion`, `tests::maps::invertibility_matches_two_sided_inverses`, `tests::maps::map_forms_read_back`, `tests::maps::the_two_classes_sort_the_fixtures`, `map::tests::each_clause_refuses_by_variant`, `map::tests::composition_refuses_a_missing_image`.
- `Catalogue`: every class and every hom set at a bound. Witness: `tests::maps::the_catalogue_serves_pinned_hom_sets`.
- `Degree`: vertices plus inner wires. Witness: `tests::shapes::the_degree_counts_vertices_and_inner_wires`.
- `Site`, `identities`, `closure`, `intersection`, `invertibility`, `degree_order`, `direct_core`, `latching`, `factorization`, `rigidity`, `dual_rigidity`, `split_lowering`, `pushouts`, `Outcome`: the generalized Reedy conditions, each answering with its case count and its smallest counter-example. Witnesses: `tests::reedy::the_class_is_a_category_with_two_classes`, `tests::reedy::the_degree_orders_both_classes`, `tests::reedy::the_point_free_core_is_direct`, `tests::reedy::the_latching_category_is_finite`, `tests::reedy::every_map_factors_through_a_point_deletion`, `tests::reedy::both_rigidity_axioms_hold`, `tests::reedy::a_closed_substitution_has_no_pushout_with_a_deletion`, `tests::point_count::the_codegeneracy_is_split`.
- `core_decomposition`, `grounded_stratum`, `deletion_classes`, `codegeneracies`, `corolla`: the point-count grade. Witnesses: `tests::point_count::every_shape_is_its_core_beside_its_points`, `tests::point_count::grounded_shapes_are_the_zero_stratum`, `tests::point_count::deletions_are_addressed_by_kernels`, `tests::point_count::the_codegeneracy_is_split`, `tests::units::the_point_reaches_each_point_once`.
- `merge`, `scalars`, `labelled_by_arity`, `unit_property`: the external product and the finite check that the empty diagram is its one weak unit. Witnesses: `tests::units::the_external_product_sets_wirings_side_by_side`, `tests::units::scalars_are_counted_and_labelled`, `tests::units::the_empty_diagram_is_the_only_unit`.

The record of why the objects are stick-free is four tests on raw wirings, read as graphs before admission so that a bare wire can stand as an object: `negatives::sticks_as_objects_admit_no_degree`, `negatives::connected_objects_lose_the_point_deletion`, `negatives::vertex_end_fusions_are_not_closed`, `negatives::contraction_lowering_loses_the_factorization`. Each asserts the one fact that rules its alternative out.

## Expected features

- **Bounded verdicts.** A verdict holds at the bound it was run at; [What a bound proves](#what-a-bound-proves) states what that covers.
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

## Objects

A shape is the graph a carrier wiring presents. A wire open at one end is a leg, attached at both inner, and open at both a stick, which the constructors refuse with `ShapeObstruction::Stick` naming the wire; a vertex with no incident wire is a point. Generator labels, the order of a generator's ports and the order of the interface are forgotten: they are what an element of a presheaf carries, as the corolla's symmetric-group action does in the published graphical categories. Two shapes are one object when a bijection of vertices carries one multiset of wire ends onto the other. The empty shape `∅` and the point `•`, one vertex with no ports, are objects; so is every disconnected shape without a stick.

Forgetting the port order is a choice. The alternative keeps it, which makes every corolla rigid and the site a category over the signature's arities; it is the reading to take if a presheaf on the site must tell two orders of one generator's inputs apart, which the carrier's normal form does not.

## Maps

A map `f : G → K` is a pair `(S, φ)`: `S` sends each vertex `v` of `G` to a set `S_v` of vertices of `K`, and `φ` sends each wire of `G` to a wire of `K`. It is a map exactly when three clauses hold.

- **Disjointness.** Distinct vertices have disjoint images.
- **Boundary.** With `Im = φ(wires G)`, `in(S_v)` is the set of wires of `K` consumed in `S_v` whose producer lies outside `S_v` or which lie in `Im`, and `out(S_v)` the wires produced in `S_v` whose consumer lies outside `S_v` or which lie in `Im`. `φ` restricts to a bijection from the wires `v` consumes onto `in(S_v)`, and from the wires `v` produces onto `out(S_v)`.
- **Fusion.** A wire of `K` with two or more preimages has no inner wire of `G` among them, at most one preimage with a producer and at most one with a consumer.

The boundary clause reads `S_v` as the sub-graph substituted for `v`, whose inner wires are the wires of `K` inside it and outside `Im`. The fusion clause reads a wire with two preimages as a contraction, an output leg joined to an input leg; on stick-free sources the boundary clause already implies it, and it stays in the class as the statement of what a contraction is. Composition takes the union of images and composes the wire functions.

A map is **raising** when its kernel `{v : S_v = ∅}` is empty, and **lowering** when it is a deletion followed by an isomorphism: images of at most one vertex covering the target, `φ` bijective. The maps in both classes are the isomorphisms.

## What the class borrows

- **Substitution.** A graphical map sends a vertex to a sub-graph with the same boundary and identifies an output leg with an input leg for a contracting coface.
- **Admissibility.** The non-unital monad substitutes no graph with a stick component, so no vertex goes to a bare wire, and the unit of contraction is absent.
- **The external unit.** The empty graph is an admissible zero-graph: `S_v = ∅` exactly when `v` has no ports. Deleting such a vertex is the one codegeneracy the class holds, and it is not an isomorphism.

## What the class decides

- **Stick-free objects.** Admissibility, no stick components, is taken for the objects as it is for the substituted graphs, and enforced at construction. Alternatives: keeping sticks leaves no degree, since `↑ → ↑↑ → ↑` composes to the identity through a non-invertible raising map; connected objects, the restriction the published graphical categories make, lose the factorization of `ε : • → •`, the point deleted and included back, which passes only through `∅`; restricting fusions to an output leg joined to an input leg is not closed under composition, since two sticks sent to the legs of `C(1,1)` and the corolla then substituted by `p→q` compose to a fusion of two sticks, so its closure holds a stick fusion again. Reversal: a consumer whose presheaves must hold a value at the bare wire, which brings the contraction unit back and with it the stick fusions that leave no degree.
- **Contraction raises.** A fusion is part of the map that performs it and is never factored out first, as an inner coface raises the graphical degree by the inner edge it creates. Alternative: contraction in the lowering class, ordered by vertices plus wires; it loses the factorization of `C(1,1) → p→q`, whose lowering half would join the corolla's legs into a loop the acyclic carrier refuses. Reversal: a wheeled carrier, where contracting a corolla's own legs is a shape.
- **Point deletion is the kernel's codegeneracy.** A map deletes exactly the points in its kernel, and every deletion has a section; deletions out of a shape are addressed by their kernels, and the point-count grade sets them apart from the point-free core, where every map raises. Alternative: no deletion, as in the graphical categories, where every vertex has a non-empty image; then `• → ∅` is no map and the empty graph, which the monad admits as the external product's unit, is never substituted. Reversal: a consumer that never restricts a presheaf along the removal of a constant.
- **No vertex reuse.** Images are disjoint, so a fold `• ⊔ • → •` and an étale cover are not maps, though the full Kleisli subcategory over the non-unital monad holds them. A fold retracts an inclusion, which leaves no degree; its restriction on a Segal object is the diagonal the product already determines. Reversal: a consumer whose presheaves must see that diagonal as data.

A circuit algebra substitutes disconnected graphs, so an image may be disconnected, and a restriction map needs no convex rewrite site.

## The degree

`Degree::of` counts a shape's vertices, points included, plus its inner wires: the graphical categories' degree `|Vt| + |Edge_i|`, valued in the naturals. Isomorphisms preserve it, every other raising map strictly raises it and every other lowering map strictly lowers it. The contraction `p ⊔ q → p→q` raises it from two to three by the inner wire it creates; the substitution `C(1,1) → p→q` from one to three. Vertices plus every wire is no degree: it keeps `C(1,1) → p→q` at three.

## What the checks find at the bound

The suites example runs single maps over the 81 classes of size at most five and composable pairs and spans over the 31 of size at most four.

| Condition | Size | Verdict | Cases |
| --------- | ---- | ------- | ----- |
| identities are units in both classes | ≤ 5 | holds | 20554 |
| closure of the class | ≤ 4 | holds | 1006048 |
| closure of the raising maps | ≤ 4 | holds | 6466 |
| closure of the lowering maps | ≤ 4 | holds | 2340 |
| raising ∩ lowering = isomorphisms | ≤ 5 | holds | 20473 |
| degree orders both classes | ≤ 5 | holds | 2898 |
| point-free core is direct | ≤ 5 | holds | 605 |
| latching categories are finite | ≤ 5 | holds | 2197 |
| factorization, unique up to unique isomorphism | ≤ 5 | holds | 20473 |
| rigidity (iv) | ≤ 5 | holds | 20355 |
| dual rigidity (iv′) | ≤ 5 | holds | 30836 |
| lowering maps split | ≤ 5 | holds | 701 |
| pushout along a deletion exists | ≤ 4 | fails | 7 |
| pushed-out map is raising | ≤ 4 | holds | 1925 |

Every generalized Reedy axiom holds, with its dual rigidity, under a degree into the naturals. Every map is a point deletion followed by a raising map, through one middle class and unique up to a unique isomorphism. Between shapes without points every map raises, so the point-free core is a direct category. Every non-invertible raising map `G → K` has at most the vertices of `K` and at most the wires of `K` plus its inner wires, so the latching category at `K` lies among finitely many shapes; `p ⊔ q → p→q` meets the wire bound with equality.

One span has no pushout: the point substituted by the closed chain `p→q` against the point's deletion. A cocone would have to delete the image of the point, which holds the two ported vertices `p` and `q`, so there is no cocone at any size. Where a pushout exists, the pushed-out map is raising.

## What a bound proves

A shape's size is its vertices plus its wires. The enumeration at a bound is exhaustive, so a hold proves the condition for every case whose shapes have size at most the bound, and says nothing of larger shapes. The factorization's middle is no larger than the map's source, and each condition other than the pushout quantifies only over the shapes of its case, so a failure there is a counter-example at every larger bound. The pushout quantifies over all cocones, so its failure is the argument above, which holds at every size. The catalogue orders classes by size and then by key, pairs and triples by total size and then by index, and each condition stops at its first failing case, so the counter-example it reports has the least total size, ties broken by that order.

## Boundary wrappers

Every count and index a signature here crosses is a transparent wrapper (`ShapeSize`, `PointCount`, `ShapeIndex`, `CaseCount`, `Degree`, `GeneratorBound`, …) converting with `From` both ways; the carrier's `Edge`, `Wire`, `EdgeCount` and `WireCount` name vertices and wires.

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
