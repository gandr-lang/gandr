# gandr-theory-coherent-resolutions

Coherent resolution of a cell rewriting system: firing a cell under the alphabet's discipline, budgeted normalization, the multi-sum overlap enumerator and its support relation, replayable coherence certificates, and budgeted Knuth–Bendix and Squier completion that declines with a report.

<!-- toc -->

- [Synopsis](#synopsis)
- [References](#references)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Firing and normalization](#firing-and-normalization)
- [Overlap enumeration](#overlap-enumeration)
- [Overlap support](#overlap-support)
- [Certificates and their identity](#certificates-and-their-identity)
- [Peak-rooted replay](#peak-rooted-replay)
- [Completion](#completion)
- [Supplied overlaps](#supplied-overlaps)
- [Replay reuse](#replay-reuse)
- [Boundary wrappers](#boundary-wrappers)
- [License](#license)

<!-- tocstop -->

## Synopsis

**What.** The rewriting engine over the substrate's cells, generic over `CellAlphabet`. `rewrite_at` fires one cell at one position and `normalize` repeats the first firing until a normal form or the budget; `enumerate_overlaps` lists every confluence critical pair and every sequential composition among a store's cells, with the seam data each carries, and `OverlapSupport` relates the cells and certificates that overlap; a `Tracelet` is a peak with two recorded paths to one join, checked by `replay`, and `replay_equivalent` is certificate identity; `derive_fused` turns a composition into a fused cell and its certificate; `complete` runs confluence completion under a `CompletionBudget`, and `complete_with_overlap_source` seeds it from a caller's matcher.

**Why.** A rule system the surface admits is useful to the decision layer only once its critical pairs are resolved: joined under a certificate that can be checked, or oriented into a new rule. That is completion, and the coherence certificates it emits are the presentation's 3-cells, the evidence a later checker replays rather than trusts. Writing it once over the alphabet trait lets the same engine serve every term language that keeps the trait's laws, and its second inhabitant, a first-order toy, shows the claim is about the trait and not about one alphabet.

**How.** Overlaps are single unifications at a seam, so enumeration is one pair query per ordered pair of cells. Certificates record which cell fired where, never a substitution, and replay re-matches every step against skolemized terms. Completion is one worklist loop shared by a fresh run, a supplied run and a resumed one, bounded by a step ceiling and a cell ceiling; a ceiling returns a decline carrying the pending batches. Absence and refusal are values: a step that does not happen returns `Maybe` with its reason, a refused operation returns `Result` with a typed refusal.

## References

- Donald E. Knuth and Peter B. Bendix. "Simple Word Problems in Universal Algebras." In _Computational Problems in Abstract Algebra_, Pergamon, 1970, pages 263–297. `doi:10.1016/B978-0-08-012975-4.50028-X` — critical pairs, orienting a divergent pair by a reduction order, and the completion loop `complete` runs.
- Franz Baader and Tobias Nipkow. _Term Rewriting and All That_. Cambridge University Press, 1998. `doi:10.1017/CBO9781139172752` — critical pairs and the critical-pair lemma, completion as an inference system that can fail or diverge, and overlaps at interior positions, which this enumerator does not compute.
- Craig C. Squier, Friedrich Otto, and Yuji Kobayashi. "A Finiteness Condition for Rewriting Systems." _Theoretical Computer Science_ 131, 2 (1994), pages 271–294 — the critical branchings of a convergent presentation, joined, generate its homotopy relations: the reading of a confluence certificate as a coherence cell.
- Dimitri Ara, Albert Burroni, Yves Guiraud, Philippe Malbos, François Métayer, and Samuel Mimram. _Polygraphs: From Rewriting to Higher Categories_. London Mathematical Society Lecture Note Series 495, Cambridge University Press, March 2025. `doi:10.1017/9781009498968`; preprint `arXiv:2312.00429` — coherent presentations and Squier completion, which extends Knuth–Bendix completion with a 3-cell for every critical branching.
- Nicolas Behr. "Tracelets and Tracelet Analysis of Compositional Rewriting Systems." In _Proceedings of Applied Category Theory 2019_, Electronic Proceedings in Theoretical Computer Science 323 (2020), pages 44–71. `doi:10.4204/EPTCS.323.4` — tracelets as derivations recorded for re-execution, sequential composition of rules, and the concurrency theorem the fused-cell differential adopts as a test.

## Provided features

- `rewrite_at`, `apply_once`, `normalize`, `CellApp`, `Rewrite`, `Normalization`, `firing`, `redex_search`: one firing under the alphabet's discipline, and budgeted normalization that tells a normal form from a spent budget. Witnesses: `rewrite::tests::a_frame_defining_cell_fires_at_the_root`, `rewrite::tests::an_eta_cell_is_rejected_at_the_wrong_polarity`, `rewrite::tests::a_budget_of_zero_reports_a_pending_redex`, `tests::differential::eta_at_the_wrong_polarity_is_rejected`, `tests::second_inhabitant::the_normalizer_runs_over_the_toy_alphabet`.
- `enumerate_overlaps`, `overlaps_between`, `Overlap`, `OverlapKind`, `OverlapRefusal`, `peak_legs`, `PeakLegs`: the multi-sum family with its seam data, complete up to the root diagonal. Witnesses: `tests::overlap::the_frame_and_add_cells_compose_into_the_commutation_cell`, `tests::overlap::the_suppressed_diagonal_peak_has_coinciding_legs`, `tests::overlap::a_real_critical_pair_has_differing_legs`, `tests::overlap::every_confluence_entry_carries_the_root_seam`, `tests::overlap::overlaps_are_a_deterministic_family`, `tests::overlap::the_pair_query_agrees_with_the_store_wide_family`, `tests::second_inhabitant::every_toy_confluence_entry_carries_the_root_seam`, `tests::second_inhabitant::the_enumerator_finds_the_toy_composition_overlap`.
- `OverlapSupport`: the memoized overlap relation on cells and certificates, and independent batches. Witnesses: `tests::overlap::overlap_support_is_symmetric_and_certificate_memoized`, `tests::overlap::overlap_support_batches_are_pairwise_independent`.
- `Tracelet`, `replay_equivalent`, `confluence_tracelet`, `derive_fused`, `ReplayTrace`, `ReplayPath`, `ReplayStep`, `ReplayPathOutcome`, `StuckStep`, `confluence_join`: certificates checked by replay, their identity, and the observable replay. Witnesses: `tracelet::tests::a_fused_cell_certificate_replays`, `tracelet::tests::a_certificate_is_replay_equivalent_to_itself`, `tracelet::tests::distinct_derivations_of_one_boundary_are_replay_equivalent`, `tracelet::tests::a_derivation_that_misses_its_boundary_is_not_self_equivalent`, `tests::differential::the_fused_cell_certificate_replays_over_the_store`, `tests::differential::replay_is_pure_over_a_fixed_certificate_and_store`, `tests::differential::append_only_store_extension_preserves_replay_trace`, `tests::differential::store_permutation_is_not_an_indexed_certificate_invariant`, `tests::differential::fused_equals_two_step`.
- `replay_from_peak`: the replay of two recorded paths from a supplied peak to a supplied join, for a boundary that is not a critical pair; `Tracelet::replay` is this replay on its overlap's peak. Witness: `tracelet::tests::replay_from_peak_separates_a_reached_join_from_a_missed_one`.
- `complete`, `CompletionBudget`, `CompletionOutcome`, `DeclineReason`, `scheduled_confluence_batches`: budgeted completion, its decline and its resume. Witnesses: `tests::completion::completion_processes_within_budget`, `tests::completion::a_starved_budget_declines_with_pending`, `tests::completion::cell_budget_decline_preserves_pending_work`, `tests::completion::decline_resume_matches_uninterrupted_completion`, `tests::differential::completion_certificates_replay`, `tests::differential::a_starved_completion_declines_with_what_was_left`, `tests::second_inhabitant::completion_orients_and_certifies_over_the_toy_alphabet`, `tests::second_inhabitant::a_starved_toy_budget_declines_with_pending`.
- `complete_with_overlap_source`, `Overlap::from_supplied_confluence`, `SuppliedOverlapError`: the supplied-overlap seam and its typed declines. Witnesses: `tests::completion::supplied_overlap_validation_returns_typed_declines`, `tests::completion::supplied_non_unifying_decline_is_typed`, `tests::completion::a_supplied_overlap_naming_another_left_cell_is_declined`, `tests::completion::non_unifying_supplied_decline_is_terminal_on_resume`, `tests::completion::invalid_supplied_decline_is_terminal_on_resume`, `tests::completion::budget_decline_revalidates_non_unifying_pending_overlap`.
- The engine trusts the splice law rather than checking it, and an alphabet that breaks it shows through the step. Witness: `tests::adversarial_alphabet::the_non_local_splice_alphabet_disturbs_a_sibling_it_was_not_asked_about`.
- The boundary wrappers (`NormalizationBudget`, `CompletionStepBudget`, `CompletionCellBudget`, `CertificateIndex`, `BatchIndex`, `OverlapIndex`, `BudgetExhaustion`, `TraceletReplay`, `TraceletEquivalence`, `StepIndependence`, `CompletionStatus`): every budget, index and verdict a signature here crosses.

## Expected features

- **An alphabet keeping the inhabitant laws.** The engine spends the three laws the substrate's `CellAlphabet` states and no type can check — a match substituted into its pattern reproduces the matched term, a successful match binds every metavariable the pattern names, a read and a splice at one position agree — and the trait's position and splice clauses: disjoint positions address disjoint subtrees, and a splice changes nothing but its position. An alphabet breaking one gets wrong answers rather than refusals.
- **Rules whose right-hand sides introduce no hole.** Normalization and replay fire ground terms and skolemized peaks; a contractum carrying a metavariable its redex did not bind leaves a hole in the result.
- **Stores sized for rule sets.** Enumeration is quadratic in the store, and completion re-enumerates the whole store after each derived cell; both are sized for presentations a surface declares, not for stores of thousands of cells.

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

## Firing and normalization

A cell fires at a command position when the alphabet's firing discipline permits it there and its left-hand side matches the command; the discipline is asked first, so the sequent alphabet's η cells are refused at the wrong polarity however well they match. `apply_once` tries positions in the alphabet's order, outermost first, and cells in store order within a position, so normalization is deterministic for a fixed store.

`normalize` stops at a normal form or after its budget, and `Normalization::exhausted` says which: a spent budget with a redex pending is reported, never mistaken for a normal form. The budget is the guard against a store that does not terminate, the same decline-and-report posture completion takes.

## Overlap enumeration

For each ordered pair of cells the enumerator returns every unification at a seam, one entry per unifier: the family is a multi-sum and is never collapsed to one chosen overlap. A confluence entry unifies the two left-hand sides at the root; a composition entry unifies the left cell's right-hand side, at one of its command positions, with the right cell's left-hand side. Each entry carries its seam data — unifier, seam position, peak, and the right cell renamed apart from the left — so a consumer reads the span, not a verdict. The right cell is renamed apart before unifying, and the unifier's bindings on the right read against that renamed cell.

The family is complete up to the root diagonal: a cell is not overlapped with itself at the root, because the root unifier of a pattern with its own renaming is that renaming and both contractions land on one term. `peak_legs` states that decision once, and the guard in the enumerator is on the two identifiers rather than on coinciding legs, because a ground rule and a schematic rule over one operation are distinct cells whose legs coincide once unified, and that joinable pair is work completion certifies. This is not the Knuth–Bendix exclusion of self-overlaps: completion over first-order terms also needs a rule's overlaps with itself at interior positions of its left-hand side, and this enumerator unifies whole left-hand sides at the root for every pair. A consumer needing interior overlaps needs a different enumerator; the reversal is the first presentation whose completion they decide.

`overlaps_between` is the pair query the store-wide sweep iterates, exposed so a consumer asking about two cells pays for two.

## Overlap support

`OverlapSupport` records which unordered cell pairs overlap and which certificates' supports meet — a certificate's support being the cells its paths fire — so scheduling asks logarithmic questions after one quadratic construction. Its sets are `BTreeSet`s rather than hash sets: iteration and equality are deterministic and independent of insertion history, a support built in one call equals one built in several, and nothing in the crate iterates a hashed collection. The cost is a logarithmic lookup where a hash set's is expected-constant; the reversal is a measured store where lookups dominate completion.

Independence is answered in one polarity, `StepIndependence`; every overlap question is that answer negated where it is asked, so no second query can drift from the first. `batches` is first-fit: each overlap joins the first batch every member of which it is independent of, so batches are subsequences of the input in order and the partition is deterministic.

## Certificates and their identity

A `Tracelet` records which cell fired where on each of its two paths, never a substitution. `replay` skolemizes the peak and the join to constants, re-fires every step by ground rewriting and checks both paths land on the join: a certificate is evidence checked by replay, never trusted. `replay_trace` is the same replay keeping every fired step and the first step that did not fire, with its reason; the verdict-only replay retains nothing.

Two certificates are one transformation when they share a peak and a join and each replays — `replay_equivalent`, the identity criterion. It is proof-irrelevant up to replay: two structurally different derivations of one boundary are one certificate, which is what makes composing certificates associative and unital. The derived `PartialEq` on `Tracelet` compares whole values and is finer; the two are kept apart everywhere.

A recorded `CellId` resolves as an insertion-order index into the store replay is given, never by cell content. Clones and append-only extensions of a store therefore keep every certificate's replay, and a permutation may rebind an identifier, which the trace shows as the step it stops at. Identity by stable address is the representation's choice; resolving by content instead would make a certificate survive a permutation at the cost of hashing every cell on every step, and the reversal is a consumer that reorders stores.

`confluence_tracelet` joins a critical pair whose reducts normalize to one term. `derive_fused` builds the fused cell `peak ~> composite` of a composition and its certificate — the two-step path against the single fused step — and the property test `fused_equals_two_step` holds the fused cell to the two-step derivation on generated ground instances, the concurrency theorem adopted as a test rather than implemented as proof machinery. Both check the overlap kind they read and refuse the other with `OverlapRefusal`, rather than leave it a precondition.

## Peak-rooted replay

`replay_from_peak` takes the boundary as arguments — a peak, a join and two paths — and `Tracelet::replay` is a call to it on the certificate's overlap peak, so the crate holds one replay. A boundary that is not a critical pair needs it: two adjacent applications exchanged past each other start at one peak and must reach one join, and no enumerator found an overlap there.

The alternatives are worse. A synthetic `Overlap` per such boundary would mint a record whose kind, seam and unifier claim a critical pair no enumeration produced; a replay written by the crate that checks those boundaries would be a second replay beside this one, and a certificate check that two implementations answer is no longer one check. The function becomes a constructor if the engine grows a peak-rooted replay type that `Tracelet` wraps.

## Completion

`complete` schedules the store's confluence overlaps into independent batches and runs them in order. A pair whose reducts normalize to one term contributes a certificate; a pair whose normal forms differ is oriented by the alphabet's reduction order into a derived cell, whose own critical pairs join the worklist. Three obstructions are left rather than guessed at: a reduct the normalization budget does not bring to a normal form, a divergence the order does not separate, and a derived cell the store already holds. Each pair's reducts are normalized once, and the certificate is built from those normalizations rather than recomputed.

The `CompletionBudget` is three ceilings — critical pairs processed, cells the store may hold, steps per normalization — each the most admitted rather than the point of failure. Reaching the step or cell ceiling returns `CompletionOutcome::Declined` with the interrupted batch's remainder first and every later batch unchanged, never a divergence or a truncated answer. `resume` continues the same loop from that state, so a declined-then-resumed run equals the uninterrupted one by construction rather than by agreement between two loops.

After each derived cell the loop re-enumerates the store and keeps the batches that touch the new cell. Restricting the sweep to the new cell's pairs through `overlaps_between` is the known improvement; it waits for a store large enough to measure the difference.

## Supplied overlaps

`complete_with_overlap_source` is the seam through which a caller's own matcher seeds the worklist with confluence overlaps the generic unifier would not find. The source is a parameter, not a dependency: this crate depends on the substrate and `quenchant-shape` and on no matcher crate, in any dependency table, and a matcher-owning crate reaches completion by calling it. `Overlap::from_supplied_confluence` builds an entry from the matcher's unifier and seam without re-running the generic unifier.

Every supplied entry is validated before any reaches the loop: it must be a confluence, both its identifiers must address stored cells, and its unifier must send both legs — the stored left cell's left-hand side and the renamed right cell's — to its peak. The first invalid entry declines with `DeclineReason::InvalidSuppliedOverlap`, naming its batch and position, with every supplied batch pending and nothing derived. An invalid-input decline is terminal under `resume`, and a budget decline's pending work is revalidated before it resumes, so an invalid entry never reaches the loop by either route.

The leg check reads both legs. Checking the right leg alone would accept an entry whose left identifier was changed to another stored cell, since the peak is computed from the left cell the entry was built with; reading the stored left cell closes that, and `a_supplied_overlap_naming_another_left_cell_is_declined` holds it. That the right leg is the stored right cell renamed apart from the stored left one is the constructor's guarantee and stays a precondition.

## Replay reuse

The crate keeps no memo of replay outcomes: every `replay` re-fires every step. A memo keyed by each step's full support — the resolved cell's content, the position, the input term — would reuse outcomes across repeated replays, across append-only store growth and across certificates that share steps, but nothing here replays one certificate set repeatedly, so there is no workload to measure it on. It is added when a consumer that does — a kernel-side certificate check, or a producer replaying guarded templates — lands, together with differentials that poison a memo entry in each direction and show the memoized verdict disagreeing with the engine's.

## Boundary wrappers

The crate owns the nominal wrappers its own signatures cross: budgets, indices and verdicts. The substrate keeps its own counts and decisions, which this crate reads; a budget in the substrate would make every engine's budget a substrate change. A wrapper two crates must exchange by value moves to the lower one.

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
