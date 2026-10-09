# gandr-theory-cell-complexes

The cell-shape substrate of gandr's rewriting stack: flat command patterns, matching, unification and anti-unification over them, the reduction order, the cell-alphabet trait with its sequent inhabitant, the cell store, and the linearity admission.

<!-- toc -->

- [Synopsis](#synopsis)
- [References](#references)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Polarity](#polarity)
- [Pattern representation](#pattern-representation)
- [Matching and unification](#matching-and-unification)
- [Anti-unification](#anti-unification)
- [Reduction order](#reduction-order)
- [Cell alphabet](#cell-alphabet)
- [Convexity warrant](#convexity-warrant)
- [Cells and the store](#cells-and-the-store)
- [Linearity admission](#linearity-admission)
- [Renaming apart](#renaming-apart)
- [Boundary wrappers](#boundary-wrappers)
- [Second inhabitant](#second-inhabitant)
- [License](#license)

<!-- tocstop -->

## Synopsis

**What.** The vocabulary every rewriting engine above it quantifies over. A command pattern (`CmdPat`) is one cut `⟨p |ε c⟩` of a producer pattern (`ProdPat`) against a consumer pattern (`ConsPat`) at a `Polarity`, with metavariables (`MetaVar`) as holes; a `Pos` addresses a subterm, read by `subterm_at` and replaced by `splice_at`. A substitution (`Subst`) is extended by one-sided matching (`match_cmd`) and two-sided unification (`unify_cmd`), and a family of patterns folds into its least general generalization (`anti_unify_cmd`); `reduction_cmp` orients a pair or reports it unorientable. `CellAlphabet` is the one trait the engines are generic over and `SequentAlphabet` its inhabitant; a `Cell` is an oriented rewrite with metadata derived from its faces, kept in a deduplicating `CellStore`, and `admit_linear_cell` refuses a cell whose left-hand side copies a hole. The crate is `no_std` and depends on `core`, `alloc` and `quenchant-shape`.

**Why.** Completion, firing and normalization over cells all ask the same questions of a term language: does this pattern match here, do these two overlap, which side of this pair is larger, what replaces the subterm at this position. Answering them once, behind one trait, lets each engine be written and tested against any term language that keeps the trait's laws, and keeps the sequent command language — the first language the engines run on — out of the engines' code.

**How.** Patterns are flat node tables, so every walk over one is a loop and a pattern of any depth is matched, ordered and dropped on a small stack. Matching and unification run explicit worklists over borrowed subtrees and copy bindings into the substitution only when the whole walk succeeds. The reduction order lays both commands out as one node table each and fills the lexicographic path order's relation bottom-up, pair by pair. Absence and refusal are values: a lookup that can miss returns `Maybe` with a named reason, a refused operation returns `Result` with a typed refusal.

## References

- Dimitri Ara, Albert Burroni, Yves Guiraud, Philippe Malbos, François Métayer, and Samuel Mimram. _Polygraphs: From Rewriting to Higher Categories_. London Mathematical Society Lecture Note Series 495, Cambridge University Press, March 2025. `doi:10.1017/9781009498968`; preprint `arXiv:2312.00429` — cells as generating rewrites between the faces of a presentation, the reading `Cell` and `CellStore` are named for.
- Pierre-Louis Curien and Hugo Herbelin. "The Duality of Computation." In _Proceedings of the Fifth ACM SIGPLAN International Conference on Functional Programming (ICFP '00)_, pages 233–243, September 2000. `doi:10.1145/351240.351262` — the command `⟨p | c⟩` of a producer against a consumer, and the critical pair of the two binders that a cut's polarity resolves.
- Franz Baader and Tobias Nipkow. _Term Rewriting and All That_. Cambridge University Press, 1998. `doi:10.1017/CBO9781139172752` — positions, matching, syntactic unification with the occurs check, reduction orders and stability under substitution, and the lexicographic path order.
- J. A. Robinson. "A Machine-Oriented Logic Based on the Resolution Principle." _Journal of the ACM_ 12, 1 (January 1965), pages 23–41. `doi:10.1145/321250.321253` — most-general unification, which `unify_cmd` computes.
- Gordon D. Plotkin. "A Note on Inductive Generalization." In _Machine Intelligence 5_, pages 153–163. Edinburgh University Press, 1970 — the least general generalization of a set of terms, which `anti_unify_cmd` computes.
- John C. Reynolds. "Transformational Systems and the Algebraic Structure of Atomic Formulas." In _Machine Intelligence 5_, pages 135–151. Edinburgh University Press, 1970 — the same generalization found independently, as the meet of the lattice of terms under instantiation.
- Nachum Dershowitz. "Termination of Rewriting." _Journal of Symbolic Computation_ 3, 1–2 (1987), pages 69–116. `doi:10.1016/S0747-7171(87)80022-6` — simplification orders and their limit: no such order orients a rule whose right-hand side embeds its left, the shape of the frame-defining cell.
- Filippo Bonchi, Fabio Gadducci, Aleks Kissinger, Paweł Sobociński, and Fabio Zanasi. "String Diagram Rewrite Theory II: Rewriting with Symmetric Monoidal Structure." _Mathematical Structures in Computer Science_ 32, 4 (2022), pages 511–541. `doi:10.1017/S0960129522000317`; preprint `arXiv:2104.14686` — convex matching, whose per-pair re-check `ConvexityDischarge` names a warrant for skipping, and the left-connectedness conditions that warrant is one part of.

## Provided features

- `CmdPat`, `ProdPat`, `ConsPat`, `MetaVar`, `Sym`, `HoleName`, `Cat` and the borrowed views `ProdRef`, `ConsRef`, `ProdView`, `ConsView`, `ProdArgs`, `OpArgs`: the pattern language over flat tables, with sizes, groundness and metavariables in a fixed order, none of it recursive. Witnesses: `pattern::tests::metavars_are_collected_in_order`, `pattern::tests::ground_and_size_track_structure`, `pattern::tests::the_per_category_sizes_count_their_own_subtree`, `tests::depth::a_deep_pattern_is_matched_ordered_and_dropped_on_a_small_stack`.
- `Pos`, `Node`, `NodeRef`, `subterm_at`, `splice_at`, `splice_cmd`, `SpliceRefusal`: positions as child-index paths, reading and splicing at them, and a splice of the wrong category refused by name. Witnesses: `pattern::tests::subterm_and_splice_round_trip`, `pattern::tests::a_miscategorized_splice_is_rejected`, `pattern::tests::the_root_position_is_the_only_one_that_reports_root`.
- `Subst`, `match_cmd`, `unify_cmd`, `BindingRefusal`: an ordered substitution, one-sided matching and most-general unification with the occurs check, both transactional, and `Subst::restricted`, a substitution cut down to named metavariables. Witnesses: `subst::tests::matching_binds_a_ground_configuration`, `subst::tests::a_polarity_clash_blocks_a_match`, `subst::tests::unification_finds_a_most_general_unifier`, `subst::tests::the_occurs_check_rejects_a_cycle`, `subst::tests::unification_resolves_triangular_bindings`, `subst::tests::a_restriction_keeps_exactly_the_named_bindings`, `tests::subst::every_match_reproduces_its_target`, `tests::subst::every_unifier_equates_its_two_sides`.
- `anti_unify_cmd`, `Generalization`, `GeneralizationPoint`, `GeneralizationArm`, `anti_unification::Absent`: the least general generalization of a family of command-pattern tuples, with one point per distinct disagreement and one arm per member at each, and its three refusals by name. Witnesses: `generalize::tests::a_shared_constructor_is_kept_above_the_point`, `generalize::tests::positions_agreeing_member_by_member_stand_one_point`, `generalize::tests::a_spine_is_shared_from_the_cut_outward`, `generalize::tests::a_point_takes_a_name_no_member_wears`, `generalize::tests::a_tuple_shares_its_points_across_components`, `generalize::tests::a_family_without_a_generalization_is_refused_by_name`, `tests::generalize::every_member_is_its_generalization_under_its_arms`, `tests::generalize::a_shared_pattern_matches_the_generalization`.
- `reduction_cmp`, `path_order_cmp`: the guarded size comparison with the path order deciding ties, and the path order alone. Witnesses: `order::tests::an_equal_size_pair_is_oriented_by_the_path_order`, `order::tests::a_size_difference_orients_when_the_larger_side_dominates`, `order::tests::a_size_difference_that_substitution_could_reverse_is_an_obstruction`, `order::tests::an_equal_size_pair_the_path_order_cannot_separate_stays_an_obstruction`, `order::tests::the_frame_defining_shape_is_not_oriented_forwards_and_that_is_stated`, `tests::order::the_order_is_a_strict_order_over_generated_patterns`, `tests::order::the_path_order_survives_a_uniform_hole_instantiation`.
- `CellAlphabet`, `SeamRole`, `PositionOrder`, `path_order`, `ConvexityDischarge`, `CommandSpliceRefusal`: the 24-method alphabet interface and the shared path order on child-index positions. Witnesses: `sequent::tests::renaming_apart_keeps_a_seam_one_hole`, `sequent::tests::skolemization_is_name_stable`, `sequent::tests::each_eta_kind_requires_its_own_polarity`, `alphabet::tests::the_path_order_separates_its_four_outcomes`; the inhabitant laws are witnessed over this inhabitant and a second one by `gandr-theory-cell-complexes-tools` (see [Second inhabitant](#second-inhabitant)).
- `SequentAlphabet`, `Orientation`, `CellProvenance`, `EtaKind`, `CellMeta`, `CellVarMeta`, `CellVariance`, `CellContractumUse`, `StepGrowth`, `frame_defining_cell`: the sequent inhabitant, its tags, its derived per-hole metadata and the η-polarity discipline. Witnesses: `sequent::tests::metadata_tracks_variance_and_linearity`, `sequent::tests::a_repeated_metavariable_is_nonlinear`, `sequent::tests::a_hole_at_both_polarities_is_a_linear_seam`, `sequent::tests::the_contractum_use_reports_erased_once_and_repeated`, `sequent::tests::the_step_growth_join_names_duplication_erasure_and_strict_linearity`, `sequent::tests::completion_cells_are_invertible_certificates`, `sequent::tests::skolemization_is_name_stable`, `sequent::tests::each_eta_kind_requires_its_own_polarity`, `sequent::tests::renaming_apart_keeps_a_seam_one_hole`.
- `Cell`, `CellStore`, `CellId`: cells with derived metadata, deduplicated on structure, addressed in insertion order. Witness: `sequent::tests::the_store_dedups_on_structural_identity`.
- `admit_linear_cell`, `copied_hole`, `NonLinearPattern`: the left-linearity admission and its alphabet-neutral copy search. Witnesses: `linearity::tests::a_repeated_producer_hole_is_the_copy`, `linearity::tests::a_hole_at_both_polarities_is_not_a_copy`, `linearity::tests::a_repeat_on_the_right_hand_side_is_not_a_copy`, `linearity::tests::refusal_payloads_and_rendering_preserve_hole_identity`, `linearity::tests::admission_chooses_the_first_copied_occurrence_and_accepts_ground_terms`, `linearity::tests::a_hole_at_both_polarities_is_admitted`, `linearity::tests::a_linear_cell_is_admitted`.
- `Polarity` and the boundary wrappers (`PatternSize`, `PositionStep`, `SubstitutionDecision`, `CellInvertibility`, …): the cut's orientation and every count and verdict a signature here crosses.

## Expected features

- **An alphabet keeping the inhabitant laws.** An engine generic over `CellAlphabet` trusts four laws no type can state: substituting a match into its pattern reproduces the matched term; a successful match binds every metavariable the pattern names; reading at a position and splicing there agree, both ways; each member of a family is its generalization with its own arm applied at every point. An inhabitant also supplies a reduction order that is well-founded and stable under substitution, a deterministic renaming apart, and a convexity answer it can justify. The inhabitant suite of `gandr-theory-cell-complexes-tools` runs the four laws over an inhabitant through the trait alone.
- **Small faces.** Cell metadata derivation is quadratic in a face's occurrence count, and the store's deduplication is a linear scan; both are sized for rule sets, not for term-sized faces.

## Examples

Match the successor rule's left-hand side against a configuration and reproduce it.

```rust
use gandr_theory_cell_complexes::CmdPat;
use gandr_theory_cell_complexes::ConsPat;
use gandr_theory_cell_complexes::Polarity;
use gandr_theory_cell_complexes::ProdPat;
use gandr_theory_cell_complexes::Subst;
use gandr_theory_cell_complexes::match_cmd;

fn example() {
    // ⟨Succ(m) | add(n; α)⟩
    let lhs = CmdPat::cut(
        Polarity::Positive,
        ProdPat::ctor("Succ", [ProdPat::meta("m")]),
        ConsPat::op("add", [ProdPat::meta("n")], ConsPat::meta("alpha")),
    );
    // ⟨Succ(Zero) | add(Zero; ★)⟩
    let zero = || ProdPat::ctor("Zero", []);
    let target = CmdPat::cut(
        Polarity::Positive,
        ProdPat::ctor("Succ", [zero()]),
        ConsPat::op("add", [zero()], ConsPat::top()),
    );
    let mut subst = Subst::new();
    assert!(bool::from(match_cmd(&lhs, &target, &mut subst)));
    assert_eq!(target, subst.apply_cmd(&lhs));
}
```

Admit a rule cell and store it.

```rust
use gandr_theory_cell_complexes::Cell;
use gandr_theory_cell_complexes::CellProvenance;
use gandr_theory_cell_complexes::CellStore;
use gandr_theory_cell_complexes::CmdPat;
use gandr_theory_cell_complexes::ConsPat;
use gandr_theory_cell_complexes::Orientation;
use gandr_theory_cell_complexes::Polarity;
use gandr_theory_cell_complexes::ProdPat;
use gandr_theory_cell_complexes::admit_linear_cell;

fn example() -> Result<(), Box<dyn core::error::Error>> {
    // ⟨Succ(m) | add(n; α)⟩ ~> ⟨m | add(n; Succ⁻(α))⟩
    let lhs = CmdPat::cut(
        Polarity::Positive,
        ProdPat::ctor("Succ", [ProdPat::meta("m")]),
        ConsPat::op("add", [ProdPat::meta("n")], ConsPat::meta("alpha")),
    );
    let rhs = CmdPat::cut(
        Polarity::Positive,
        ProdPat::meta("m"),
        ConsPat::op("add", [ProdPat::meta("n")], ConsPat::frame("Succ", ConsPat::meta("alpha"))),
    );
    let cell: Cell = Cell::new(lhs, rhs, Orientation::PolarityDerived, CellProvenance::SurfaceRule);
    admit_linear_cell(&cell)?;
    let mut store = CellStore::new();
    let id = store.insert(cell.clone());
    assert_eq!(id, store.insert(cell));
    Ok(())
}
```

Nontrivial operations carry executable `#[spec]` predicates and `# Adequacy` hypotheses with crate-local witnesses. The witnesses cover category boundaries, empty inputs, transactional refusals, substitution cycles, splice growth and shrinkage, metadata joins, and ordering obstructions. Run them normally and with predicate enforcement:

```sh
cargo nextest run -p gandr-theory-cell-complexes
RUSTFLAGS="--cfg anodized_panic" cargo nextest run -p gandr-theory-cell-complexes
```

Items that cannot be instrumented without changing their interface state an `executable: none` reason beside the specification: const functions, abstract alphabet declarations, opaque iterator or strategy returns, and consumed one-shot paths. Renaming checks colliding images against the captured reserved-name set even though its input iterator is consumed. Formatting and the assertion-driven depth witness expose no readable result state for an exit predicate. These items retain explicit adequacy witnesses rather than weakening their contracts to satisfy instrumentation.

## Polarity

`Polarity` is the cut's evaluation orientation: a positive cut runs its producer first, a negative cut its consumer first, which is how a cut resolves the critical pair of its two binders. It is not the value/computation sort of call-by-push-value, and not the variance of a hole across a cell's two faces, which the sequent alphabet derives separately as `CellVariance`; the name collides with both in neighbouring literature, so the axis is stated here.

The enum lives in this crate because its only readers are here: the pattern language, the reduction order and the η requirement. A crate of its own would cost a crate for a two-variant enum with one consumer, and a core-tier crate would put a core edge under a theory crate, which the layering forbids. A core-tier sequent language imports this tag rather than minting its own; a second theory crate that needs the tag without the substrate moves it to a leaf theory crate.

## Pattern representation

No pattern routes ownership through itself. A producer is one flat table in reverse pre-order, the root last, every subtree a contiguous range ending at its own root and carrying its node count, so a child is found by skipping its elder siblings and a subtree is read or copied as one slice. A consumer is a spine: its frames listed innermost first, then its end, `★` or a consumer metavariable; an operation frame's producer arguments are producer tables of their own. A command is a cut over one producer and one consumer. Commands do not nest, so a cut is only ever a pattern's root.

The design this crate was planned under puts each pattern in one flat node table with children as index ranges. The built form keeps that discipline per category — one table per producer, one spine per consumer, the cut over the two — rather than one table across all three, for three reasons: every view is total, because a table holds one category and no read checks a node's category; building `Succ(p)` reuses `p`'s buffer, so constructor application is amortized constant time; and a consumer is a list, not a tree, so its natural flat form is the spine. Nothing recurses either way, and structurally equal patterns have equal tables.

- **Alternatives.** One table across all categories puts a category check and a fallback on every view. A store-wide arena shared by every cell's patterns couples each pattern to the store's lifetime and gives equal patterns one identity before anything sanctions that identity. Boxed children are recursive owned pointers, which the workspace denies: a deep pattern overflows the stack on drop.
- **Reversal.** A measured substitution cost from copying tables per rewrite moves the representation to a shared arena, with the identity question answered first.

## Matching and unification

Both are explicit worklists over borrowed subtrees of their inputs: no goal copies a pattern, and no step recurses. Unification resolves triangular bindings — an image that mentions a metavariable bound after it — by walking each binding to its end, bounded by the binding count so a cycle is reported rather than followed, and applies the occurs check before each binding.

Both are transactional: bindings are staged as borrowed subtrees and copied into the substitution only when the whole walk succeeds, so a refusal leaves the substitution as it was. An earlier implementation of this design left it possibly partially extended on refusal, so a caller retrying another candidate had to clone before every attempt. The trait still asks only the weaker obligation of other alphabets: an inhabitant may extend partially on refusal, and an engine reads the substitution only after success.

A metavariable is keyed by its name and its category, so a producer hole and a consumer hole of one name are two metavariables.

## Anti-unification

`anti_unify_cmd` is unification's dual: given a family of command-pattern tuples, it returns the most specific tuple of patterns every member instantiates, with a fresh metavariable — a point — wherever two members differ, and each member's subterm there as that member's arm. The walk keeps a head every member shares and descends below it, so a point stands only where a disagreement does; and two positions whose subterms agree member by member stand one point, which is what makes the result least general rather than merely general. A tuple is generalized jointly, so a disagreement met in two components is one point across both.

A producer column is walked by a heap worklist of columns and constructor builds; a consumer spine is walked from the cut outward, one shared frame at a time, until the members' remaining spines differ or end, and that suffix is one consumer point. Two cuts of different polarity have no generalization in this grammar, which has no command metavariable, and are refused by name, as are an empty family and members of different lengths. A point's name is `$g$` and a suffix no member wears; points are listed in the order the walk first meets them.

- **Decision.** Anti-unification is a method of `CellAlphabet`, beside `unify_cmd`, with `restrict_subst` and `cmd_size` for the consumers that read a generalization's points and price it.
- **Alternatives.** A generic anti-unifier above the trait, built from positions and splicing: the trait reads and replaces subterms but cannot build a pattern from a head and its children, so it would need a constructor interface the engines have no other use for. A separate trait: a second bound on every engine that prices a family, for one method whose law is stated against the trait's own substitution.
- **Reversal.** A consumer that needs generalization modulo a theory — associativity, commutativity, binders — moves it to a trait of its own, with this syntactic one as its first inhabitant.

## Reduction order

`reduction_cmp` compares node counts, admitted only when the larger side carries every hole of the smaller at least as often: without that guard a repeated hole lets substitution reverse the verdict, and an order that substitution can reverse proves nothing about the instances that rewrite. Equal sizes are decided by the lexicographic path order over a uniform node view, with the precedence `cut > K⁻ > f > K > ★` (a cut, a return-side constructor frame, an operation frame, a constructor, the terminal), then the symbol's own order, then the arity. Ranking the constructor frame above the operation frame orients the fusion cell `⟨v | Succ⁻(add(n; α))⟩ ~> ⟨v | add(n; Succ⁻(α))⟩` in the direction it is written, the direction that removes the intermediate constructor. `Ordering::Equal` means unorientable, an honest obstruction completion reports, never a guess.

The path order is a simplification order, so it cannot orient a rule whose right-hand side embeds its left: the frame-defining cell `⟨v | K⁻(β)⟩ ~> ⟨K(v) | β⟩` is that shape, and no precedence orients it forwards. That cell's orientation comes from the calculus and never passes through this order, which orients critical pairs only; the order is therefore not a termination proof for a store holding polarity-derived cells.

## Cell alphabet

`CellAlphabet` is one deep trait of 24 methods rather than a set of small ones: an alphabet fixes its pattern grammar (term, metavariable, hole, position, navigation, splicing, size, order, renaming, skolemization), its ordered substitution with matching, unification, anti-unification and restriction, and its cell vocabulary (orientation and provenance tags, derived metadata, hole flow, firing permission). An engine is written against the trait and never against the sequent language.

Reading a subterm at a position returns `Maybe<Cmd, command_subterm::Absent>`, naming an off-term position apart from one that addresses no command, and splicing returns `Result<Cmd, CommandSpliceRefusal>` with the same two refusals; neither collapses a refusal into an empty option.

## Convexity warrant

`ConvexityDischarge` is an alphabet's warrant for skipping the per-pair convexity re-check a matcher over diagrams would otherwise run. The discharging variant is `StronglyConnectedOverAcyclicTarget`. The planned name was `LeftConnectedOverAcyclicTarget`, after the phrase "left-connected over an acyclic target". Left-connectedness, as the string-diagram literature uses it, is three conditions on a whole system — left-linear, monogamous acyclic rules on both sides, every left-hand side strongly connected — while the warrant states one condition on each left-hand side plus the target's acyclicity. This crate admits right-hand repeats, so the second condition does not hold, and the name says what is checked.

- **Alternatives.** The phrase from the literature with the precision carried by the doc comment alone.
- **Reversal.** A ruling that the literature's phrasing is authoritative restores the planned name.

## Cells and the store

A cell's metadata is derived from its two faces when it is built and never declared: its fields are private, so the metadata always equals what derivation gives. `CellStore` deduplicates on structural equality of the whole cell and hands out `CellId`s in insertion order, so iteration is deterministic and cloning or appending preserves every id. A `CellId` is still a store-local index, not a content address: rebuilding the same cells in another order renumbers them, so a persistence or transport format never serializes one and carries the cell's content instead.

## Linearity admission

A metavariable twice on a cell's left-hand side is a copy on a wire: substitution copies for free in a term store, but a circuit needs a comonoid the type may not have. `admit_linear_cell` refuses that cell, naming the copied hole and how to respell the rule. It governs which cells enter a store, not which patterns can be built: unification goals legitimately carry repeated metavariables, so derivation refuses nothing.

A hole worn by a producer and a consumer metavariable is one hole at two polarities, the seam the composition gate reads, and is not a copy, because the copy relation is per name and category.

The right-hand side is reported, not refused. A contractum that repeats a hole duplicates it; `CellMeta::step_growth` classifies each cell as strictly linear, erasing or duplicating, and the cost of duplication is a budget question for the engine that fires the cell. Refusing duplication at admission is a stricter reading that remains open; the reported step growth is the datum such a refusal would read, so adopting it is one predicate at admission. Invertibility (`CellInvertibility`) names the orientation a joinability certificate may be read in, not an undo operation on derivations.

## Renaming apart

`rename_apart` primes each name of the renamed cell until it is apart from the anchor's names, keyed by name alone, so a producer and a consumer metavariable sharing a name get the same fresh name and a seam stays one hole. An earlier implementation of this design renamed per name and category, which split a seam `r` into `r'` and `r''` and contradicted its own guarantee that an already-disjoint cell is returned unchanged. Witness: `sequent::tests::renaming_apart_keeps_a_seam_one_hole`.

## Boundary wrappers

Every count, step and verdict a signature here crosses is a transparent wrapper of this crate's own (`CellCount`, `PatternSize`, `PositionStep`, `SubstitutionDecision`, `FiringPermission`, `CellInvertibility`, …), converting with `From` both ways. An engine above keeps its own budgets, indices and verdicts: one shared vocabulary in the substrate would make every engine's budget a substrate change. A wrapper two crates must exchange by value moves to the lower crate.

## Second inhabitant

The trait's laws are checked over a second inhabitant, a toy first-order term language that implements `CellAlphabet` from outside this crate, as every later alphabet will. Its terms nest commands, so the splice law is exercised below the root, which the sequent alphabet, whose only command position is the root, cannot do. It lives in `gandr-theory-cell-complexes-tools`, a test-only crate that every engine suite reaches through `[dev-dependencies]`, rather than in this crate's integration target: one implementation of a 21-method trait is shared, not copied. The law suite lives there too, so this crate keeps no dev-dependency on a crate built over it, and the dependency graph stays acyclic in every edge kind.

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
