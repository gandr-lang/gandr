# gandr-theory-sites

The carrier's shapes as a site with stick-free objects: a morphism class over the wirings `gandr-theory-circuit-algebras` admits, its degree, and the finite checks of its generalized Reedy structure.

A circuit algebra has two units. The identity wire, a bare wire from an input port to an output port with no operation on it, is the unit of contraction; the empty diagram is the unit of the external product. The site keeps the second and drops the first: **a stick is not a shape**.

<!-- toc -->
- [Synopsis](#synopsis)
- [References](#references)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Where the detail lives](#where-the-detail-lives)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** A shape is a wiring the carrier admits, read as a graph, with no stick component: generators are vertices, and each wire records its producer and consumer or an open end. A map of shapes sends each vertex to a disjoint sub-graph of the target with the same boundary, and each wire to a wire, where two wires land on one only as a contraction of an output leg with an input leg. Deleting a vertex with no ports, a point, is the one codegeneracy the class holds.

**Why.** A Reedy structure on the site indexes presheaves by a degree: it lets a presheaf be built, and its fibrancy checked, one degree at a time. That needs maps against which a degree, a factorization and a pushout can be checked, and objects for which they hold. With the identity wire as an object no degree exists, since a stick includes into two sticks and two sticks fuse back to one, composing to the identity; without it, every generalized Reedy axiom holds at the bound, under a degree into the naturals.

**How.** The carrier enumerates the shapes up to a size bound, one validator states the class, and each condition reports its case count and its smallest counter-example; [`catalogue`](src/catalogue.rs) states the enumeration.

**Levels.** A pasting diagram above dimension one is a shape of the same site under the wreath product, an outer shape whose vertices each carry a shape of the level below. Restricted to the chains at every level, it holds Θₙ's objects, Joyal's pasting schemes, under the site's own maps. Henry draws the parallel one level up: polygraphs whose generators have no identity as source or target form a presheaf category, as the site has a degree because no stick is an object. One level up, the external product's unit of level one is the contraction unit of level two, and the site keeps that object and fences only its deletion. Level two's Segal certificate is built from level one's, its cells each column's corollas on the outer vertex's corolla.

The level-two unit is a fat object. The site does not drop it, which is the stick move. The site does not read it as an identity map, which is the Eilenberg-Zilber move. It is an object of a direct category, and the nerve theorem characterises its Segal condition. That is the `Grounded` move, now with a published nerve theorem (de Jong, Kraus, Paoli and Pradal 2026, Theorems 4.22 and 4.23). Its proof machinery, monads with arities, is the machinery the vault already uses for the circuit nerve.

One site serves two uses. The wiring site indexes the ambient model, where a type is a diagram over the arities and a higher cell is an identity type. The same site, under the wreath, indexes the cells. There the Segal condition at a level certifies the composite over a pasting shape. The two uses coincide at level one, because a 1-pasting is a wiring of 1-cells and the chains are Δ. The univalence warrant is Shulman's inverse EI theorem over the level-one site. A wreath level inherits it only through directness with automorphisms, which the level's certificate re-derives from the level below. This site drops Eilenberg-Zilber. So Berger and Moerdijk's wreath theorem is not the warrant.

The level-two evidence: over the chains to total size 13 and `W ≀ W` to 5, the grounded objects and their raising maps form a direct category with automorphisms (766 and 709 cases), the condition the certificate carries. Every object to the bound is the colimit of its cells, and none of `W ≀ W` fails to size 7. The carrier refuses two cells each the other's source as a directed cycle (Leclerc and Mimram's Lemma 3), so no level holds the pinwheel.

## References

- `vault:01a1897b-d199-7d10-a325-587b76db2508` — lineage: the programme's design for the iterated site (§ The design), one site under the wreath product. No level holds a stick, and an outer vertex may carry the empty shape, which the wreath builds.
- `vault:01a178aa-ce14-7610-bcad-5aab5f9c0b0f` — lineage: a stored image replays, never trusted.
- `Berger-2007-iterated_wreath_product_simplex_category_iterated_loop_spaces` — lineage: Clemens Berger, "Iterated Wreath Product of the Simplex Category and Iterated Loop Spaces", _Advances in Mathematics_ 213, 2007, `doi:10.1016/j.aim.2006.12.006` — Definitions 3.1 and 3.3, the wreath and Θₙ as the iterated wreath of Δ.
- `Henry-2018-nonunital_polygraphs_form_presheaf_category` — background: Simon Henry, "Non-Unital Polygraphs Form a Presheaf Category", preprint, 2018, `arXiv:1711.00744` — Corollary 2.4.9, the dropped stick's parallel one level up.
- `Ruit-2024-pasting_theorem_iterated_segal_spaces` — exemplar: Jaco Ruit, "A Pasting Theorem for Iterated Segal Spaces", _Journal of Pure and Applied Algebra_ 228, 2024, `arXiv:2210.04549` — Theorem 3.49 and Corollaries 3.52 and 3.55, the pasting theorem level two's certificate instances; § 3.2, the pinwheel.
- `deJong-2026-study_kocks_fat_delta` — background: Tom de Jong, Nicolai Kraus, Simona Paoli and Stiéphen Pradal, "A Study of Kock's Fat Delta", 2026 — Theorems 4.22 and 4.23, the fat object's nerve theorem.
- `Shulman-2017-univalence_inverse_ei_diagrams` — background: Michael Shulman, "Univalence for Inverse EI Diagrams", _Homology, Homotopy and Applications_ 19, 2017, `arXiv:1508.02410` — the level-one univalence warrant a wreath level inherits through directness with automorphisms.

## Provided features

- `Shape`, `End`, `Ends`, `WireKind`, `VertexKind`, `ShapeKey`, `ShapeObstruction`, `ShapeBudget`, `shapes_up_to`: stick-free shapes through the carrier, the stick refused by name, their statistics, isomorphism classes, and the enumeration of every class up to a size, stopped at a budget.
- `SiteMap`, `VertexSet`, `MapObstruction`, `CompositionMismatch`, `MapForm`, `homs`: the morphism class, its one validator, composition, the two classes, invertibility, and the enumeration of a hom set.
- `Catalogue`, `Family`: every class of a family and every hom set at a bound, the wirings, the chains or a profile set's shapes, each the full sub-site on its shapes; a class outside the family is named as such.
- `Shape::chain`, `Boundary`, `Unfilled`, `fills`: the chain of `n` composable vertices, and the check that a diagram's cells have their vertices' profiles and meet along the inner wires, answering the diagram's boundary and naming the first defect.
- `Degree`: vertices plus inner wires.
- `Site`, `identities`, `closure`, `intersection`, `invertibility`, `degree_order`, `direct_core`, `latching`, `factorization`, `rigidity`, `dual_rigidity`, `split_lowering`, `pushouts`, `Outcome`: the generalized Reedy conditions, each answering with its case count and its smallest counter-example; all but latching run at any level, the direct core over each level's grounded objects.
- `Level`, `Wreath`, `WreathShape`, `WreathMap`, `WreathKey`, `WreathShapeObstruction`: what the conditions read of a site, the catalogue as level one, the wreath over a level as the next, the chain restriction at every level, and `Level::find`, an object's class at any level or why none holds it.
- `core_decomposition`, `grounded_stratum`, `deletion_classes`, `codegeneracies`, `corolla`: the point-count grade.
- `merge`, `scalars`, `labelled_by_arity`, `unit_property`: the external product and the finite check that the empty diagram is its one weak unit.
- `segal`, `Cocones`, `Cocone`, `Inclusion`, `Graft`, `Leg`, `SegalFailure`, `SegalDefect`: the Segal condition at degree `n`, each shape of degree two to `n` the colimit of its corollas along its grafting pushouts, over the families of maps whose images are disjoint, and refused at the first shape, test shape and family over the blanket families.
- `SegalStratum`, `Uncertified`, `Vacuity`, `Species`, `Profile`, `Element`, `Labelling`, `Table`, `Bijection`, `Equivalence`, `Natural`, `restrict`, `Defect`, `StratumImage`, `Unreplayed`, `SitesBuild`: the stratum certified at degree `n` through the corolla and Segal conditions, its image and the replay of its structure, graphical species and their terms at every shape, an equivalence of species as the finite certificate natural along the corolla automorphisms, its extension to the free algebras, and the corolla restriction that reflects a natural isomorphism of the free algebras back to the species.
- `WreathStratum`, `WreathCocone`, `Cell`, `Spot`, `InnerGraft`, `segal_two`, `LevelFailure`, `LevelDefect`, `LevelUncertified`: level two certified at degree `n` from level one's certificate, its grounded objects direct with automorphisms and each object of degree two to `n` the colimit of its cells.

Each item's rustdoc names its witnesses under `# Adequacy`.

## Expected features

- **Bounded verdicts.** A verdict holds at the bound it was run at; [`catalogue`](src/catalogue.rs) states what that covers.
- **Small bounds.** The cost grows with the square and the cube of the class count; [`catalogue`](src/catalogue.rs) gives the figures at each bound.
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

[`src/lib.rs`](src/lib.rs) § Running prints every condition's outcome and runs the tests in both modes.

## Where the detail lives

Mechanism, decisions with their alternatives and reversals, and witnesses live in the rustdoc beside the code:

| Topic | Module |
| ----- | ------ |
| Objects, maps, what the class borrows and decides, boundary wrappers, references | [`src/lib.rs`](src/lib.rs) |
| The degree | [`degree`](src/degree.rs) |
| What a bound proves | [`catalogue`](src/catalogue.rs) |
| What the checks find at the bound | [`conditions`](src/conditions.rs) |
| A level, and the wreath over one | [`level`](src/level.rs), [`wreath`](src/wreath.rs) |
| The Segal condition, its cocones and the families it counts | [`segal`](src/segal.rs) |
| The strata, their alphabet and range, `ua` and `ua-desc` | [`stratum`](src/stratum.rs) |
| The stratum across levels, its cells and its defects | [`ascent`](src/ascent.rs) |

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
