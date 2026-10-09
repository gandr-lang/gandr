# gandr-theory-computads

The elaborator seam of the cell-rewriting stack: a levitated description's rules elaborated into command cells at the declaration's polarity through one admission seam, and a two-redex circuit rule instantiated where the identification of its two sequentializations is decidable, with the convexity re-check supplied by the caller.

<!-- toc -->

- [Synopsis](#synopsis)
- [References](#references)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [The supported fragment](#the-supported-fragment)
- [The declaration's polarity](#the-declarations-polarity)
- [The admission seam and its two refusals](#the-admission-seam-and-its-two-refusals)
- [The operation gate](#the-operation-gate)
- [η cells](#η-cells)
- [Circuit rules](#circuit-rules)
- [Instantiation](#instantiation)
- [The convexity supply point](#the-convexity-supply-point)
- [Reports](#reports)
- [A closed tier](#a-closed-tier)
- [Boundary wrappers](#boundary-wrappers)
- [License](#license)

<!-- tocstop -->

## Synopsis

**What.** `elaborate_data_desc` reads a whole description into one sequent cell store: a frame-defining cell per constructor, a cell per admitted rule face and circuit rule, and the η cells the declaration licenses, every one cut at the declaration's polarity, with every declined member reported beside the store (`DescElaboration`). `elaborate_rule` is the face-to-cell step on its own. `instantiate_two_redex_rule` applies a two-redex circuit rule at a peak and earns, or refuses, the identification of its two sequentializations; `ConvexitySupply` is the point where a caller hands it the convexity re-check a store without a discharge is owed. `instantiate_cell` instantiates one stored cell under a substitution into the same store.

**Why.** A description states rules and the engines rewrite cells. Something has to decide which of a description's rules a cell store can hold, refuse the rest with a reason a reader can act on, and fix the cut each cell fires at; that is this crate, and it is the one place those decisions are made. A circuit rule whose body holds two redexes denotes a horizontal composite only where its two sequentializations are shift-equal, which is a question about two cells at two positions of one term, so it is asked at an application rather than at the declaration.

**How.** Face elaboration is the sequent-machine flattening: an operation application cuts its first argument against the operation's frame, and a constructor wrapping an operation becomes a return-side frame on the continuation. Every walk is a loop or an explicit stack, so no term's depth reaches the call stack. Cells enter the store through one seam that refuses a copied hole, then a hole worn at both polarities. Instantiation reads its positions from the body's occurrence record, asks the shift guard, asks the caller's supply point where the store withholds its convexity discharge, fires both orders, and replays the witness before handing it back. Refusal is data: every decline is a typed value carried to the caller.

## References

- Ross Street. "Limits Indexed by Category-Valued 2-Functors." _Journal of Pure and Applied Algebra_ 8, 2 (1976), pages 149–181. `doi:10.1016/0022-4049(76)90013-X` — computads: the generators of a 2-category, a 2-cell between composites of 1-cells, the reading a description's rules take once elaborated.
- Albert Burroni. "Higher-Dimensional Word Problems with Applications to Equational Logic." _Theoretical Computer Science_ 115, 1 (1993), pages 43–62. `doi:10.1016/0304-3975(93)90054-W` — polygraphs, and equational logic read as a two-dimensional word problem over them.
- Dimitri Ara, Albert Burroni, Yves Guiraud, Philippe Malbos, François Métayer, and Samuel Mimram. _Polygraphs: From Rewriting to Higher Categories_. London Mathematical Society Lecture Note Series 495, Cambridge University Press, March 2025. `doi:10.1017/9781009498968`; preprint `arXiv:2312.00429` — presentations as polygraphs, rewriting rules as their generating 2-cells, and the linearity of a rule's source the admission seam enforces.
- James Chapman, Pierre-Évariste Dagand, Conor McBride, and Peter Morris. "The Gentle Art of Levitation." In _Proceedings of the 15th ACM SIGPLAN International Conference on Functional Programming (ICFP '10)_, pages 3–14, September 2010. `doi:10.1145/1863543.1863547` — datatype descriptions as first-class data, which this crate reads as a table rather than a syntax tree.
- Pierre-Louis Curien and Hugo Herbelin. "The Duality of Computation." In _Proceedings of the Fifth ACM SIGPLAN International Conference on Functional Programming (ICFP '00)_, pages 233–243, September 2000. `doi:10.1145/351240.351262` — the command `⟨p | c⟩` a rule elaborates to, and the return continuation its result is sent to.
- Paul Downen and Zena M. Ariola. "A Tutorial on Computational Classical Logic and the Sequent Calculus." _Journal of Functional Programming_ 28 (2018), e3. `doi:10.1017/S0956796818000023` — data and codata in the sequent calculus and the η laws each validates under its own evaluation strategy, the reason a declaration's polarity fixes its cells' cut.
- Filippo Bonchi, Fabio Gadducci, Aleks Kissinger, Paweł Sobociński, and Fabio Zanasi. "String Diagram Rewrite Theory II: Rewriting with Symmetric Monoidal Structure." _Mathematical Structures in Computer Science_ 32, 4 (2022), pages 511–541. `doi:10.1017/S0960129522000317`; preprint `arXiv:2104.14686` — convex matching, and two disjoint matches that interfere through each other's convexity: the conjunct the supply point re-checks.

## Provided features

- `elaborate_data_desc`, `DescElaboration`, `OpFrame`, `OpElaborateError`, `CircuitElaboration`: a whole description into one store, the operation gate first, every decline reported. Witnesses: `elaborate::tests::a_whole_description_elaborates_frame_and_rule_cells`, `elaborate::tests::an_admitted_operation_reports_its_declared_inputs`, `elaborate::tests::a_many_out_operation_is_declined_and_declines_its_faces`, `elaborate::tests::an_aggregating_arity_and_an_outputless_one_are_declined_apart`, `elaborate::tests::a_face_over_an_admitted_operation_survives_the_gate`, `elaborate::tests::a_duplicating_contractum_is_admitted_and_reported`.
- `elaborate_rule`, `ElaborateError`: one face into one cell at the declaration's polarity. Witnesses: `elaborate::tests::add_zero_elaborates_to_a_cut_against_the_operation_frame`, `elaborate::tests::add_succ_flattens_the_wrapping_constructor_into_a_frame`, `elaborate::tests::a_non_operation_lhs_is_declined`.
- Every cell a declaration contributes — frame, rule, circuit and η — cuts at the polarity its η law requires, and a `codata` declaration's η critical pair joins. Witnesses: `elaborate::tests::a_codata_declarations_cells_all_cut_at_its_eta_polarity`, `elaborate::tests::the_positive_frame_cell_is_the_frame_defining_cell`, `tests::eta::a_codata_eta_cell_joins_the_projection_route_at_its_negative_cut`.
- The admission seam's two refusals, `ElaborateError::NonLinear` and `ElaborateError::MixedPolarity` with `MixedPolarityHole`, distinct in variant and diagnostic, the copy decided first. Witnesses: `elaborate::tests::a_repeated_hole_and_a_mixed_polarity_hole_earn_distinct_refusals`, `elaborate::tests::a_description_whose_rule_copies_a_hole_is_refused`, `tests::linearity::the_idempotence_rule_written_with_a_repeated_hole_is_refused`, `tests::linearity::the_cancellation_rule_written_with_a_repeated_hole_is_refused`, `tests::linearity::the_linear_companion_rule_is_admitted`, `tests::linearity::a_refused_face_does_not_stop_its_linear_neighbours`.
- `EtaElaboration`, `EtaElaborateError`: the η cells a declaration licenses, at its polarity, or the missing half of the licence. Witnesses: `elaborate::tests::a_wrapper_description_mints_its_eta_cell`, `elaborate::tests::a_codata_declaration_mints_its_eta_cell_at_a_negative_cut`, `elaborate::tests::a_multi_constructor_description_declines_its_eta_cell`, `elaborate::tests::an_operation_with_no_inverse_face_licenses_no_eta_cell`, `elaborate::tests::the_inverse_face_is_recognized_by_its_shape_and_nothing_looser`, `tests::eta::the_two_routes_out_of_the_eta_redex_agree`, `tests::eta::the_eta_cell_reaches_a_redex_the_projection_route_cannot`, `tests::eta::a_data_eta_cell_does_not_fire_at_a_negative_cut`, `tests::eta::a_codata_eta_cell_does_not_fire_at_a_positive_cut`, `tests::eta::an_eta_step_replays`.
- Circuit rules through the same seam, declined first when their body denotes no single composite. Witnesses: `elaborate::tests::a_single_redex_circuit_rule_reaches_the_store`, `elaborate::tests::a_two_redex_circuit_rule_is_declined_its_composite`, `elaborate::tests::a_circuit_rule_whose_boundary_copies_a_hole_is_refused`, `elaborate::tests::a_circuit_rule_applying_a_declined_operation_is_declined_at_the_gate`.
- `instantiate_two_redex_rule`, `RewriteBinding`, `CircuitShift`, `CircuitShiftObstruction`: the earned identification and its refusals. Witnesses: `tests::circuit_instantiation::an_instantiated_cong2_rule_earns_its_shift_witness`, `tests::circuit_instantiation::the_instantiated_applications_carry_the_records_positions`, `tests::circuit_instantiation::a_genuinely_overlapping_instantiation_is_refused_at_the_application_site`, `tests::circuit_instantiation::a_sequential_two_redex_body_is_refused_comparable_positions`, `tests::circuit_instantiation::a_reconvergent_body_resolves_both_occurrences_through_one_binding`, `instantiate::tests::a_single_redex_rule_has_no_pair_to_identify`, `instantiate::tests::an_unbound_rewrite_port_declines_the_instantiation`, `instantiate::tests::a_port_bound_twice_is_not_a_functional_environment`, `instantiate::tests::a_cyclic_body_declines_before_any_pair_is_read`, `instantiate::tests::a_peak_carrying_no_redex_at_the_records_positions_is_refused`.
- `ConvexitySupply`, `ConvexityGrant`: the caller's re-check, asked exactly when the store withholds its discharge and the first two conjuncts hold. Witnesses: `tests::convexity_supply::a_withheld_discharge_is_rechecked_by_the_supply_point`, `tests::convexity_supply::a_refused_recheck_refuses_the_instantiation_with_its_evidence`, `tests::convexity_supply::the_supply_point_is_asked_only_after_the_positions_and_overlap_conjuncts`, `tests::circuit_instantiation::an_instantiated_cong2_rule_earns_its_shift_witness`.
- `instantiate_cell`, `CellInstantiationError`: one stored cell under a substitution, into the same store. Witnesses: `instantiate::tests::instantiating_a_cell_preserves_store_identity`, `instantiate::tests::instantiating_an_unknown_cell_returns_typed_error`.
- The reduction order over the cells a real description elaborates: the equal-size face pairs it orients, and the fusion cell completion derives. Witnesses: `tests::order::the_path_order_orients_pairs_the_size_order_left_as_obstructions`, `tests::order::completion_derives_the_fusion_cell_the_size_order_could_not_orient`.
- The crate reaches exactly the four theory crates it reads. Witness: `tests::workspace::the_crate_reaches_only_the_theory_crates_it_reads`.

## Expected features

- **A checked description.** Whether a face's symbols belong to the declaration, and whether an arity's maps compose, are the description table's own checks (`check_desc`); elaboration decides only what the cell layer must, and a caller wanting both verdicts runs both passes.
- **A diagram reading for the supply point.** The convexity re-check is the caller's. A caller with no re-check passes a supply point that refuses, and a store that withholds its discharge then refuses every pair rather than assuming the conjunct.
- **Stores sized for declarations.** A store's insertion scans the store, and the shift guard builds its overlap support per question; both are sized for the cells one declaration contributes.

## Examples

Elaborate a description and read what was admitted and what was declined.

```rust
use gandr_theory_computads::EtaElaboration;
use gandr_theory_computads::elaborate_data_desc;
use gandr_theory_levitation::SignDesc;

fn example<G>(desc: &SignDesc<G>) {
    let elaborated = elaborate_data_desc(desc);
    for (index, refusal) in &elaborated.declined_faces {
        let _ = (index, refusal);
    }
    if let EtaElaboration::Declined(reason) = &elaborated.eta {
        let _message = reason.to_string();
    }
    let _cells = elaborated.store.len();
}
```

Instantiate a two-redex circuit rule over a store that discharges its convexity conjunct, with a supply point that refuses whatever it is asked.

```rust
use core::convert::Infallible;

use gandr_theory_cell_complexes::CellAlphabet;
use gandr_theory_cell_complexes::CellId;
use gandr_theory_cell_complexes::CellStore;
use gandr_theory_coherent_resolutions::CellApp;
use gandr_theory_computads::ConvexitySupply;
use gandr_theory_computads::RewriteBinding;
use gandr_theory_computads::instantiate_two_redex_rule;
use gandr_theory_levitation::CircuitRule;

struct NoRecheck;

impl<A: CellAlphabet> ConvexitySupply<A> for NoRecheck {
    type Warrant = Infallible;
    type Refusal = ();

    fn recheck(
        &self,
        _store: &CellStore<A>,
        _peak: &A::Cmd,
        _first: &CellApp<A>,
        _second: &CellApp<A>,
    ) -> Result<Infallible, ()> {
        Err(())
    }
}

fn example<A: CellAlphabet>(store: &CellStore<A>, rule: &CircuitRule, peak: &A::Cmd, f: CellId, g: CellId) {
    let bindings = [RewriteBinding::new("p", f), RewriteBinding::new("q", g)];
    match instantiate_two_redex_rule(store, rule, &bindings, peak, &NoRecheck) {
        Ok(shift) => assert!(bool::from(shift.witness.replay(store))),
        Err(refusal) => drop(refusal),
    }
}
```

Run the tests:

```sh
cargo nextest run -p gandr-theory-computads
```

## The supported fragment

A face `lhs ==> rhs` elaborates when its left-hand side is an operation application whose arguments are producers — variables and constructors of producers — and its right-hand side is a variable, a constructor of producers, a tail operation, or a constructor wrapping an operation through single-argument constructors. The left-hand side `f(head, rest…)` becomes `⟨head | f(rest…; $ret)⟩`; the right-hand side sends its value to the same continuation, a wrapping constructor `K(…)` becoming the return-side frame `K⁻` on it. Anything else — an operation in producer position, a several-argument constructor around an operation — is declined with `ElaborateError::UnsupportedShape` rather than mis-elaborated. The fragment is the direct one; growing it is a change to this crate's walk, not to the cell layer.

## The declaration's polarity

Every cell a declaration contributes cuts at one polarity: positive for `data`, negative for `codata`, the polarity the declaration's η law requires (`EtaKind::required_polarity`). Rule, circuit, frame and η cells read it from one mapping, so they cannot disagree.

The recorded design cut every rule cell and every frame cell positive whatever the declaration, while a `codata` declaration's η cell cuts negative; at a negative cut its projection route did not exist, so the η cell's critical pair could not be shown to join, and the open question was which cut a `codata` declaration's rule and frame cells take. The choice here is the η cell's: the rule cells cut where the declaration's η law fires. The frame cells follow too, which goes past the record's letter: a negative rule cell hands its result to a return-side frame at a negative cut, and a positive frame cell never reduces it, so leaving the frame cells positive would strand every `codata` rule that rebuilds a constructor. A frame cell at a positive cut is the cell layer's own `frame_defining_cell`, and a negative one is that cell with both faces cut negative; `a_codata_eta_cell_joins_the_projection_route_at_its_negative_cut` runs the joinability the choice rests on.

The alternatives were to keep positive rule cells and record the `codata` η critical pair as not applicable, which leaves a declaration whose η law and rules never meet, or to let each face choose its cut, which no description states. The choice is reversed if descriptions grow per-sort polarities: the cut is then the sort's, read from the same mapping.

## The admission seam and its two refusals

`elaborate_data_desc` is where a description's cells enter a store, so it is where admission binds, and it refuses two hole faults apart. A rule whose left-hand side copies a hole is refused with the cell layer's linearity diagnostic (`ElaborateError::NonLinear`): a copy on a wire needs a comonoid the type may not have. A cell that wears one hole name at both polarities is refused with its own diagnostic (`ElaborateError::MixedPolarity`, naming the hole): the cell layer reads such a hole as the dinaturality seam its composition gate needs, which is right for the cells completion derives, but a description's rule binds its pattern variables as producers and its result to one reserved continuation, so a face reaches that seam only by spelling a variable with a name the elaboration reserves. The copy is decided first, so a cell with both faults is refused for the copy.

The record asked for two distinct refusals here, while the copy relation the cell layer checks is per hole name and category, so a two-polarity hole passes it as linear; the alternatives were to admit the seam, which lets a misspelled rule become a cell that joins a variable to its own continuation, or to refuse it inside the cell layer's linearity check, which would refuse the seams completion derives on purpose. The check lives at this seam and nowhere deeper, beside the copy check, so internal shapes stay constructible. The reversal is a description form that states a consumer-side pattern variable: the seam then becomes a face's own statement, and the refusal narrows to the reserved names.

Frame-defining and η cells are generated rather than read from the description and carry only reserved holes, each used once, so they enter the store without passing the seam.

## The operation gate

An operation frame `f(p̄; c)` carries one producer-argument list and one return continuation, so the only arity it holds has one output port fed by one monomial. An operation declaring no output port, several, or one fed by zero or several monomials is declined with an `OpElaborateError`, and every face and circuit rule applying it is declined with `ElaborateError::UnrepresentableOperation` before it is shaped, rather than elaborated into a frame that drops the operation's other outputs. Growing the cell alphabet so those arities are representable is a cell-layer change and is not taken here.

## η cells

A declaration licenses an η law by stating both halves: exactly one constructor `K`, and an admitted operation `f` carrying the inverse face `f(K(x)) ==> x`. The law is minted in its contracting direction, `⟨w | f(; K⁻(β))⟩ ~> ⟨w | β⟩`, whose left-hand side is headed by an operation frame; the expanding direction is headed by a bare hole, matches every cut of its polarity, and is never minted. The licence is the face's shape and nothing looser — each near miss is refused pointwise — and the cell's provenance carries its kind, so the alphabet refuses it at the other polarity however well it matches. A declaration licensing none reports which half is missing (`EtaElaborateError`).

## Circuit rules

A circuit rule's cell is its declared sphere, and what licenses it is the composite its body denotes, so a body that denotes no single whiskered composite is declined (`ElaborateError::NoCircuitComposite`) before its sphere is offered anywhere, even when the sphere would elaborate. An admitted rule then passes the gate a written face passes. `DescElaboration::circuits` holds one `CircuitElaboration` per rule in declaration order, the admitted ones carrying their cell and their composite together, so a rule's outcome is one value rather than an entry in each of two lists.

## Instantiation

A circuit rule is a schema: its body applies rewrite-sorted ports, not cells, so a two-redex body names no pair of cells for the shift guard, and asking at the declaration would ask whether every instantiation commutes. The declaration's elaboration therefore keeps declining a two-redex body a composite, which defers the question, and `instantiate_two_redex_rule` asks it at an application. The two positions are read from the body's occurrence record and never supplied, since a caller naming positions could name incomparable ones for a nested pair. The bindings are a function from port to cell, a port presented twice is refused, and two occurrences of one port resolve through its one binding. The peak is not matched against the sphere; both orders are fired instead, so a peak that is not an instance is refused by a step that does not fire. The decisions run in a fixed order — environment, wiring, occurrence count, bindings, positions and overlap, convexity, both orders, replay — and the earliest failure is the one reported.

The positions, overlap and discharge conjuncts are the shift guard's, and its refusals are carried verbatim; this crate holds no second overlap oracle. A granted witness is replayed before it is returned, so a composite neither order reaches is `CircuitShiftObstruction::CompositeDoesNotReplay` rather than a recorded identification. The returned `CircuitShift` carries no replay verdict of its own: a witness that did not replay is never returned, so the field would be constant.

## The convexity supply point

The shift guard's third conjunct asks that each match image stay convex in the other application's reduct. A store whose left-hand sides are strongly connected over acyclic targets discharges it once for every pair; a store that cannot answers `ConvexityDischarge::ReCheckRequired`, and the guard refuses rather than assumes. The re-check is a directed reachability sweep over a diagram reading of the peak, and that reading — the embedding matcher's sweep over a wiring — lives in a crate this one does not depend on.

So the re-check is a parameter: `ConvexitySupply` is a trait with its own warrant and refusal types, asked exactly when the store withholds its discharge and the cells resolve at incomparable positions with no overlap, and its answer travels back verbatim as `ConvexityGrant::Rechecked` or `CircuitShiftObstruction::NotConvex`. A discharged store never asks it. After a grant both orders are fired and the witness replayed, as on the discharged route, and the witness's own convexity field still names the store's withheld discharge.

The alternatives were a dependency on the embedding matcher's crate, which would put a diagram representation under every caller of the elaborator whether or not its store withholds the discharge, and a closure parameter, which cannot name the warrant and refusal types a caller reads back. The choice is reversed if the cell alphabet grows a diagram reading of its own: the re-check then becomes the alphabet's, beside its discharge.

## Reports

The output is shaped so no absence is a sentinel. A declined operation or face is an index into its description table paired with its reason; a circuit rule's outcome is one enum per rule; the η outcome is either the minted cells or the reason none was. A caller rendering diagnostics reads each decline against the declared member's own span.

## A closed tier

The crate depends on four theory crates — the cell substrate, the rewriting engine, the shift guard and the description table — and on nothing above them; its workspace test checks the resolver's answer. It re-exports none of their types, so a dependent names each crate whose types it reads. The bridge between a description and the core calculus's terms is the core side's, and lands with its consumer; keeping it here would turn the theory tier's edge upward.

## Boundary wrappers

The crate owns the nominal wrappers its own signatures cross: the indices its reports carry (`DeclinedFaceIndex`, `DeclinedOpIndex`), the counts its refusals carry (`OperationInputCount`, `ConstructorCount`, `RedexOccurrenceCount`), and one private verdict. A wrapper of another crate a signature here mentions is that crate's.

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
