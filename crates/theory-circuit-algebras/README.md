# gandr-theory-circuit-algebras

The diagram view of gandr's circuit algebras: monogamous acyclic wirings with interfaces, the spine reading of a sequent command pattern, embedding-based matching with its convexity check and certificate reader, the diagram normal form that decides when two presentations denote one diagram, and the overlaps of two diagrams that are a rule system's pre-critical pairs.

<!-- toc -->
- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Where the detail lives](#where-the-detail-lives)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** A `Wiring` is one diagram with an interface: `Generator`s, each a `GeneratorLabel` over ordered source and target `Wire`s, and an `Interface` of input and output ports. `Wiring::assemble` is its only constructor and refuses everything outside the monogamous acyclic fragment. `read_spine` reads a sequent command pattern from `gandr-theory-cell-complexes` as a wiring. `embeddings` finds every `Embedding` of a pattern wiring into a target wiring, convexity decided by a route computed from the pattern, and keeps every structurally complete candidate that fails convexity as a `ConvexityRefusal` naming the path. `Embedding::check` reads an embedding as a certificate against two diagrams and refuses a forgery by the conjunct it fails; `Matching::ambiguity` names where several admitted readings of one pattern diverge. `canonicalize` renumbers a wiring into its `CanonicalDiagram` and returns the `Relabelling` that did it, which `Relabelling::verify` checks as an isomorphism against the input; `same_diagram` decides whether two wirings denote one diagram and answers with the shared form and both relabellings, or with the first place the two forms part. The crate is `no_std` and depends on `core`, `alloc`, `gandr-theory-cell-complexes` and `quenchant-shape`.

**Why.** A circuit pattern is neither a spine nor a tree: it may have several roots, reconverge, or hold components with no wire between them, so the substrate's one-sided matcher over command patterns cannot match it. Matching becomes sub-diagram embedding, and an embedding is a legal rewrite site only when it is convex. Both the embedding and the convexity verdict are claims a consumer has to be able to refute, so each comes with the data that refutes it. Two presentations of one diagram differ only in how they number wires and generators, so a consumer that keys on diagrams needs one representative per class, and a verdict that two diagrams are one is a claim too, with the isomorphism as its evidence.

**How.** Monogamy, at most one producer and one consumer per wire, means one assigned wire forces the generators on either side of it, so the search seeds one choice per connected component and propagates the rest. The same forcing makes the canon a traversal rather than a search: the boundary numbers its wires by position, each numbered wire numbers its producer and consumer, and only a component the boundary never reaches needs a seed, chosen by trying every member. Every walk is a loop over explicit frames; nothing recurses on diagram size. Absence and refusal are values: a lookup that can miss returns `Maybe` with a named reason, a refused operation returns `Result` with a typed refusal naming its locus.

## Provided features

- `Wiring`, `Generator`, `GeneratorLabel`, `GeneratorName`, `GeneratorSort`, `Interface`, `WiringObstruction`, the incidence lookups `producer_of` and `consumer_of`: a diagram with ordered ports and a discrete interface, built only inside the monogamous acyclic fragment.
- `Components`, `Wiring::components`: the generators partitioned into weakly connected components, port-free generators as singletons.
- `PartialBijection`, `Seam`, `BijectionClash`: an injective partial map of wires that refuses a clash, and the seam datum as its restriction to each half of an interface.
- `read_spine`, `SpineReading`, `SpineObstruction`: a sequent command pattern read as a wiring, with its cut wire and the port each metavariable became.
- `embeddings`, `embeddings_by_sweep`, `Matching`, `Embedding`, `ConvexityRefusal`, `MatchObstruction`, `MatchBudget`, `SearchSteps`: every embedding of a pattern into a target within a budget, non-convex candidates refused with their path, and a search that would exceed its budget declined rather than truncated.
- `connectivity`, `convexity_warrant`, `Connectivity`, `ConvexityWarrant`: the convexity route a pattern earns, computed and audited.
- `Embedding::claim`, `Embedding::check`, `EmbeddingObstruction`, `SeamHalf`: the certificate reader, refusing each forged conjunct by name.
- `Matching::ambiguity`, `Ambiguity`, `Divergence`, `Discriminator`: the first difference of each later admission from the first.
- `canonicalize`, `CanonicalDiagram`, `Canonicalization`, `CanonicalDiagram::to_wiring`: one representative per class of presentations, numbered by a traversal and readable back as a diagram.
- `same_diagram`, `DiagramEquality`, `SharedCanon`, `DiagramDivergence`: whether two wirings denote one diagram, with both relabellings on one arm and the first divergence on the other.
- `Relabelling`, `Relabelling::verify`, `RelabellingDefect`, `Leg`, `PortPosition`, `PortCount`, the lookups `Relabelling::image_of_wire` and `Relabelling::image_of_generator` with their `relabelled_wire` and `relabelled_generator` absence reasons: the renumbering as a checkable isomorphism, a defect refused by its locus.
- `CanonicalDiagram` as a map key: `Ord` and `Hash`, holding no address, stamp or session state, so presentations of one diagram land on one entry.
- `overlaps`, `Overlap`, `OverlapShape`: every connected gluing of two diagrams along shared generators that stays inside the fragment, with its peak, where each side landed and whether one side stands inside the other — the pre-critical pairs of two rules' left-hand sides.

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

Run the tests:

```sh
cargo nextest run -p gandr-theory-circuit-algebras
RUSTFLAGS="--cfg anodized_panic" cargo test -p gandr-theory-circuit-algebras --all-targets
```

## Where the detail lives

Mechanism, decisions with their alternatives and reversals, and witnesses live in the rustdoc beside the code:

| Topic | Module |
| ----- | ------ |
| The fragment, generator labels, boundary wrappers | [`interface`](src/interface.rs) |
| The spine reading | [`interface::spine`](src/interface/spine.rs) |
| Embeddings, convexity, verdicts, certificates | [`matching`](src/matching.rs) |
| The diagram normal form and its limits | [`normal_form`](src/normal_form.rs) |
| Overlaps of two diagrams, the pre-critical pairs | [`overlap`](src/overlap.rs) |
| An example of two presentations of one diagram, the crate boundary, specification attributes, references | [`src/lib.rs`](src/lib.rs) |

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
