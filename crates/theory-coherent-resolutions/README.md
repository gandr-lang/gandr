# gandr-theory-coherent-resolutions

Coherent resolution of a cell rewriting system. A cell fires under the alphabet's discipline, and normalization runs within a budget. The multi-sum overlap enumerator lists the critical pairs with their support relation. The crate can replay each coherence certificate. Knuth–Bendix and Squier completion runs within a budget and declines with a report. The crate also holds the bar complex of the Lawvere theory that a first-order block presents, and Brown's collapsing scheme on that complex.

Each certificate is a 3-cell of a coherent presentation, and `Basis` reduces them by the 4-cells of the critical triples. The bar complex is a chain complex over the integers alone, and #5962 owes the cells above the triples.

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

**What.** The rewriting engine over the substrate's cells, generic over `CellAlphabet`. `rewrite_at` fires one cell at one position and `normalize` repeats the first firing until a normal form or the budget; `enumerate_overlaps` lists every confluence critical pair and every sequential composition among a store's cells, with the seam data each carries, and `OverlapSupport` relates the cells and certificates that overlap; a `Tracelet` is a peak with two recorded paths to one join, checked by `replay`, and `replay_equivalent` is certificate identity; `derive_fused` turns a composition into a fused cell and its certificate; `complete` runs confluence completion under a `CompletionBudget`, and `complete_with_overlap_source` seeds it from a caller's matcher.

**Why.** A rule system the surface admits is useful to the decision layer only once its critical pairs are resolved: joined under a certificate that can be checked, or oriented into a new rule. That is completion, and the coherence certificates it emits are the presentation's 3-cells, the evidence a later checker replays rather than trusts. Writing it once over the alphabet trait lets the same engine serve every term language that keeps the trait's laws, and its second inhabitant, a first-order toy, shows the claim is about the trait and not about one alphabet.

**How.** The rustdoc states the mechanism: [`src/lib.rs`](src/lib.rs) for the engine as a whole, and each module for its part.

## References

- `Guiraud-2019-convergent_presentations_polygraphic_resolutions_associative_algebras` — exemplar: Yves Guiraud, Eric Hoffbeck and Philippe Malbos, "Convergent Presentations and Polygraphic Resolutions of Associative Algebras", _Mathematische Zeitschrift_ 293, 2019, `doi:10.1007/s00209-018-2185-z` — the standard resolution of a convergent presentation, which the bar complex of a first-order block builds.
- `vault:01a1aa2d-a69c-7030-91e0-337d68d88151` — anchor: the Squier frame of the presented-spaces page, which reads completion as a Morse collapse of the bar complex.
- `vault:01a178aa-4e61-7143-9414-8eb3d0de397f` — anchor: the acyclicity page (§ gate-substitution-read) — a step records the substitution that matched its cell, and replay reads it.
- Kenneth S. Brown, "The Geometry of Rewriting Systems: A Proof of the Anick–Groves–Squier Theorem", in _Algorithms and Classification in Combinatorial Group Theory_, MSRI Publications 23, 1992, pages 137–163 — the collapsing scheme of the bar complex along a rewriting strategy, which `LawvereTheory` gives as a `Scheme`.
- `Ara-2025-polygraphs_rewriting_higher_categories` — background: chapter 13, the Lawvere theory of a rewriting system; § 7.5, a homotopy basis reduced by triple confluences.
- `Malbos-2021-completion_operads_essential_syzygies` — background: essential branchings.
- `Doré-2023-computing_spaces_type_theory` — background: § 3.4, a matching as a function.

## Provided features

- `rewrite_at`, `fire_at`, `replay_at`, `apply_once`, `normalize`, `CellApp`, `Rewrite`, `Normalization`, `firing`, `redex_search`: one firing under the alphabet's discipline and its replay, and budgeted normalization that tells a normal form from a spent budget.
- Wires (`Cell::wires`): each firing writes fresh names for the wires of a cell, as [`rewrite`](src/rewrite.rs) states.
- `enumerate_overlaps`, `overlaps_between`, `Overlap`, `OverlapKind`, `OverlapRefusal`, `peak_legs`, `PeakLegs`: the multi-sum family with its seam data, complete up to the root diagonal.
- `interior_overlaps_between`, `root_overlaps_between`: the confluence family below the root of a left-hand side, a cell paired with itself included, and the root entry alone, which the joinability check reads over a first-order presentation.
- `OverlapSupport`: the memoized overlap relation on cells and certificates, and independent batches.
- `Tracelet`, `replay_equivalent`, `confluence_tracelet`, `derive_fused`, `record_path`, `ReplayTrace`, `ReplayPath`, `ReplayStep`, `ReplayPathOutcome`, `StuckStep`, `confluence_join`: certificates checked by replay, their identity, and the observable replay.
- `replay_from_peak`: the replay of two recorded paths from a supplied peak to a supplied join; `Tracelet::replay` is this replay on its overlap's peak.
- `complete`, `CompletionBudget`, `CompletionOutcome`, `DeclineReason`, `scheduled_confluence_batches`: budgeted completion, its decline and its resume.
- `complete_with_overlap_source`, `Overlap::from_supplied_confluence`, `SuppliedOverlapError`: the supplied-overlap seam and its typed declines.
- `join_critical_pairs`, `Joinability`, `PairJoining`: the joinability check with no derivation, and its resumption over a store grown by appended cells, which decides no joined pair again.
- `PairScheme`, `PairClass`, `NoScheme`, `PairJoining::resume_with`, `PairJoining::take_composites`: the class of each pair before the joining decides it, a composite pair's join skipped and its witness kept, and the scheme that classes no pair.
- `Basis`, `BasisCell`, `Composite`, `Witness`, `Fill`, `Homotopy`, `Move`, `RewritePath`, `PathStep`, `Sense`, `BasisFault`, `BasisRefusal`: the homotopy basis reduced by its critical triples, as [`basis`](src/basis.rs) states.
- `CompositePair`, `CompositeRefusal`: a skipped pair with the redex below its seam, and the replay that checks the redex and refuses a forged witness by name.
- `LawvereTheory`, `TermTable`, `TermNode`, `TermHead`, `root_rewrite`: the Lawvere theory of a first-order block that the caller states, with its terms interned once and its normal forms innermost first within a `NormalizationBudget`.
- `BarCell`, `Arrow`, `Degeneracy`, `BarBound`, `Truncation`, `truncated`, `LawvereError`: the bar complex of that theory as a `Complex` of `gandr-theory-discrete-morse`, which states the faces of a cell when a caller asks, and the largest subcomplex inside a bound.
- `Scheme` for `LawvereTheory`, `LawvereTheory::overlapping`, `overlapped`, `TermTable::generator`: Brown's collapsing scheme on that bar complex as a `Scheme` of `gandr-theory-discrete-morse`, along the leftmost innermost redex, and the second rule of each essential overlap.
- The boundary wrappers (`NormalizationBudget`, `CompletionStepBudget`, `CompletionCellBudget`, `CertificateIndex`, `TripleIndex`, `BatchIndex`, `OverlapIndex`, `PairDecisions`, `StepPlace`, `MovePlace`, `BudgetExhaustion`, `TraceletReplay`, `TraceletEquivalence`, `StepIndependence`, `CompletionStatus`, `Operation`, `Variable`, `TermPlace`, `RulePlace`, `Arity`, `TermSize`, `Occurrences`, `BarDegree`): every budget, index and verdict a signature here crosses.

## Expected features

- **An alphabet keeping the inhabitant laws.** The engine spends the inhabitant laws and the position and splice clauses that the substrate's `CellAlphabet` states and no type can check. An alphabet breaking one gets wrong answers rather than refusals.
- **Stores sized for rule sets.** Enumeration is quadratic in the store, and completion re-enumerates the whole store after each derived cell; both are sized for presentations a surface declares, not for stores of thousands of cells.
- **Linear cells for the basis.** `Basis` refuses a cell that copies or erases a variable.

## Examples

Derive the fused commutation cell from the frame-defining cell and the successor rule, and replay its certificate.

```rust
use gandr_theory_cell_complexes::Cell;
use gandr_theory_cell_complexes::CellProvenance;
use gandr_theory_cell_complexes::CellStore;
use gandr_theory_cell_complexes::CmdPat;
use gandr_theory_cell_complexes::ConsPat;
use gandr_theory_cell_complexes::Orientation;
use gandr_theory_cell_complexes::Polarity;
use gandr_theory_cell_complexes::ProdPat;
use gandr_theory_cell_complexes::Sym;
use gandr_theory_cell_complexes::frame_defining_cell;
use gandr_theory_coherent_resolutions::OverlapKind;
use gandr_theory_coherent_resolutions::derive_fused;
use gandr_theory_coherent_resolutions::enumerate_overlaps;

fn example() -> Result<(), Box<dyn core::error::Error>> {
    let mut store = CellStore::new();
    let frame = store.insert(frame_defining_cell(&Sym::new("Succ")));
    // ⟨Succ(m) | add(n; α)⟩ ~> ⟨m | add(n; Succ⁻(α))⟩
    let add = store.insert(Cell::new(
        CmdPat::cut(
            Polarity::Positive,
            ProdPat::ctor("Succ", [ProdPat::meta("m")]),
            ConsPat::op("add", [ProdPat::meta("n")], ConsPat::meta("alpha")),
        ),
        CmdPat::cut(
            Polarity::Positive,
            ProdPat::meta("m"),
            ConsPat::op("add", [ProdPat::meta("n")], ConsPat::frame("Succ", ConsPat::meta("alpha"))),
        ),
        Orientation::PolarityDerived,
        CellProvenance::SurfaceRule,
    ));
    let composition = enumerate_overlaps(&store)
        .into_iter()
        .find(|o| o.kind == OverlapKind::Composition && o.left == frame && o.right == add)
        .ok_or("the two cells compose")?;
    let (_fused, certificate) = derive_fused(&composition, &mut store)?;
    assert!(bool::from(certificate.replay(&store)));
    Ok(())
}
```

Complete a store within a budget, and read the outcome rather than assume one.

```rust
use gandr_theory_cell_complexes::CellStore;
use gandr_theory_coherent_resolutions::CompletionBudget;
use gandr_theory_coherent_resolutions::CompletionCellBudget;
use gandr_theory_coherent_resolutions::CompletionOutcome;
use gandr_theory_coherent_resolutions::CompletionStepBudget;
use gandr_theory_coherent_resolutions::NormalizationBudget;
use gandr_theory_coherent_resolutions::complete;

fn example(store: CellStore) {
    let budget = CompletionBudget::new(
        CompletionStepBudget::from(64_usize),
        CompletionCellBudget::from(32_usize),
        NormalizationBudget::from(128_usize),
    );
    match complete(store, budget) {
        CompletionOutcome::Completed { store, certificates, .. } => {
            assert!(certificates.iter().all(|c| bool::from(c.replay(&store))));
        },
        declined @ CompletionOutcome::Declined { .. } => {
            let _continued = declined.resume(budget);
        },
    }
}
```

Run the tests:

```sh
cargo nextest run -p gandr-theory-coherent-resolutions
```

## Where the detail lives

Mechanism, decisions with their alternatives and reversals, and witnesses live in the rustdoc beside the code:

| Topic | Module |
| ----- | ------ |
| Firing and normalization | [`rewrite`](src/rewrite.rs) |
| Overlap enumeration and support | [`overlap`](src/overlap.rs) |
| Certificates, their identity, peak-rooted replay and replay reuse | [`tracelet`](src/tracelet.rs) |
| Completion and supplied overlaps | [`completion`](src/completion.rs) |
| The bar complex of a block's Lawvere theory | [`lawvere`](src/lawvere.rs) |
| Brown's collapsing scheme on that bar complex | [`brown`](src/lawvere/brown.rs) |
| The homotopy basis, its composites and its reduction | [`basis`](src/basis.rs) |
| Boundary wrappers | [`boundary`](src/boundary.rs) |
| Executable specifications, references | [`src/lib.rs`](src/lib.rs) |

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
