//! The elaborator seam of gandr's cell-rewriting stack: where a levitated
//! description's rules become command cells, and where a circuit rule's two
//! sequentializations are identified.
//!
//! [`elaborate_data_desc`] reads a whole description — its constructors,
//! operations, rule faces, circuit rules and η licence — into one cell store
//! at the declaration's polarity, admitting each cell through one seam that
//! refuses a copied hole and a hole worn at both polarities apart, and
//! reporting every declined member beside the store ([`DescElaboration`]).
//! [`elaborate_rule`] is the face-to-cell step on its own. A description that
//! writes a constructor-headed rule — a presented type's, `Loop(Unloop(x)) ==>
//! x` — is also read over terms ([`PresentedRules`]), in the term alphabet
//! where every subterm is a position a rule fires at ([`TermAlphabet`]).
//!
//! [`instantiate_two_redex_rule`] applies a two-redex circuit rule: the
//! positions come from the body's occurrence record, the cells from the
//! caller's [`RewriteBinding`]s, the independence verdict from the shift guard,
//! and the convexity re-check a withheld discharge is owed from the caller's
//! [`ConvexitySupply`]. [`instantiate_cell`] instantiates one stored cell under
//! a substitution into the same store.
//!
//! The crate is `no_std`; besides `core`, `alloc` and the shape vocabulary of
//! `quenchant-shape`, it depends on the four theory crates § A closed tier
//! names.
//!
//! # A closed tier
//!
//! The crate depends on four theory crates — the cell substrate, the rewriting
//! engine, the shift guard and the description table — and on nothing above
//! them. It re-exports none of their types, so a dependent names each crate
//! whose types it reads. The bridge between a description and the core
//! calculus's terms is the core side's, and lands with its consumer; keeping it
//! here would turn the theory tier's edge upward.
//!
//! # Specification evidence
//!
//! Executable predicates check structural producer translation, operation
//! arities, cut polarity, identity reuse, admission atomicity and refusal
//! payloads. Enforcing builds select them with `--cfg anodized_panic`. Captures
//! preserve a consumed cell only when its insertion relation needs that value;
//! predicates do not re-invoke the convexity supplier or repeat a generic
//! rewrite to inspect its effects.
//!
//! | Boundary | Observation | Witness |
//! | -------- | ----------- | ------- |
//! | Admission | A nonempty store remains unchanged on refusal; repeated accepted cells retain identity. | `elaborate::tests::face_admission_is_atomic_and_deduplicates` |
//! | Fragment | Exact producer order and nested return frames; left-side refusal precedes a bad right side. | `elaborate::tests::producer_order_and_nested_result_frames_are_exact`, `elaborate::tests::fragment_refusals_preserve_left_before_right_precedence` |
//! | Iterative traversal | A 512-layer constructor chain preserves its leaf and every return frame on a 256 KiB stack. | `elaborate::tests::deep_constructor_elaboration_preserves_the_boundary_without_recursion` |
//! | Eta licensing | Missing licences preserve the store; several inverse operations mint in operation order and reuse identifiers. | `elaborate::tests::eta_licences_preserve_operation_order_and_decline_atomically` |
//! | Instantiation | Earliest repeated bindings, occurrence-count precedence, exact missing ports and distinct sequentializations. | `instantiate::tests::environment_refuses_the_earliest_repeat_even_for_identical_cells`, `instantiate::tests::zero_and_three_occurrences_precede_missing_bindings`, `instantiate::tests::exercise_reports_both_distinct_sequentializations` |
//! | Supplied convexity | Discharged stores bypass the supplier; withheld stores retain the requested pair and its warrant or refusal. | `tests::convexity_supply::a_withheld_discharge_is_rechecked_by_the_supply_point`, `tests::convexity_supply::a_refused_recheck_refuses_the_instantiation_with_its_evidence` |
//! | Term reading | Constructor-headed faces leave the sequent lists for the term store, in rule order behind the operation gate; their cells fire below the root and replay. | `elaborate::tests::a_presented_types_rules_are_read_over_terms`, `term::tests::the_circles_rules_fire_below_the_root` |
//!
//! These are finite L3 boundary observations; the positive frame-cell
//! comparison also uses an L2 cell-layer reference. They do not prove unbounded
//! depth, complexity or graph convexity. Diagram-level evidence belongs to the
//! supplied reader. Diagnostic tests retain discriminating payloads and
//! propagate sink failure without fixing prose or punctuation. Public records
//! describe producer results; direct record construction does not validate a
//! store, declaration or replay relation.
//!
//! # References
//!
//! - Ross Street. "Limits Indexed by Category-Valued 2-Functors." _Journal of
//!   Pure and Applied Algebra_ 8, 2 (1976), pages 149–181.
//!   `doi:10.1016/0022-4049(76)90013-X` — computads: the generators of a
//!   2-category, a 2-cell between composites of 1-cells, the reading a
//!   description's rules take once elaborated.
//! - Albert Burroni. "Higher-Dimensional Word Problems with Applications to
//!   Equational Logic." _Theoretical Computer Science_ 115, 1 (1993), pages
//!   43–62. `doi:10.1016/0304-3975(93)90054-W` — polygraphs, and equational
//!   logic read as a two-dimensional word problem over them.
//! - Dimitri Ara, Albert Burroni, Yves Guiraud, Philippe Malbos, François
//!   Métayer, and Samuel Mimram. _Polygraphs: From Rewriting to Higher
//!   Categories_. London Mathematical Society Lecture Note Series 495,
//!   Cambridge University Press, March 2025. `doi:10.1017/9781009498968`;
//!   preprint `arXiv:2312.00429` — presentations as polygraphs, rewriting rules
//!   as their generating 2-cells, and the linearity of a rule's source the
//!   admission seam enforces.
//! - James Chapman, Pierre-Évariste Dagand, Conor `McBride`, and Peter Morris.
//!   "The Gentle Art of Levitation." In _Proceedings of the 15th ACM SIGPLAN
//!   International Conference on Functional Programming (ICFP '10)_, pages
//!   3–14, September 2010. `doi:10.1145/1863543.1863547` — datatype
//!   descriptions as first-class data, which this crate reads as a table rather
//!   than a syntax tree.
//! - Pierre-Louis Curien and Hugo Herbelin. "The Duality of Computation." In
//!   _Proceedings of the Fifth ACM SIGPLAN International Conference on
//!   Functional Programming (ICFP '00)_, pages 233–243, September 2000.
//!   `doi:10.1145/351240.351262` — the command `⟨p | c⟩` a rule elaborates to,
//!   and the return continuation its result is sent to.
//! - Paul Downen and Zena M. Ariola. "A Tutorial on Computational Classical
//!   Logic and the Sequent Calculus." _Journal of Functional Programming_ 28
//!   (2018), e3. `doi:10.1017/S0956796818000023` — data and codata in the
//!   sequent calculus and the η laws each validates under its own evaluation
//!   strategy, the reason a declaration's polarity fixes its cells' cut.
//! - Filippo Bonchi, Fabio Gadducci, Aleks Kissinger, Paweł Sobociński, and
//!   Fabio Zanasi. "String Diagram Rewrite Theory II: Rewriting with Symmetric
//!   Monoidal Structure." _Mathematical Structures in Computer Science_ 32, 4
//!   (2022), pages 511–541. `doi:10.1017/S0960129522000317`; preprint
//!   `arXiv:2104.14686` — convex matching, and two disjoint matches that
//!   interfere through each other's convexity: the conjunct the supply point
//!   re-checks.
//! - David I. Spivak, Richard Garner, and Aaron David Fairbanks. "Functorial
//!   Aggregation." _Journal of Pure and Applied Algebra_ 229 (2025); preprint
//!   `arXiv:2111.10968` — the bridge-diagram arity `Σ_t ∘ Π_π ∘ Δ_s` whose
//!   product layer an operation frame's continuations carry, one per output
//!   port.
//! - Franz Baader and Tobias Nipkow. _Term Rewriting and All That_. Cambridge
//!   University Press, 1998. `doi:10.1017/CBO9781139172752` — first-order
//!   rewriting at every position of a term, and the critical pairs of rules
//!   overlapping inside a left-hand side, which the term reading's check reads.

// Module documentation that predates the shape lint: 19 headings outside the
// vocabulary, 4 decision records, 2 issue references and 7 budgets exceeded.
// Each allow leaves with the rewrite that clears its count.
#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    allow(
        module_doc_heading,
        doc_decision_record,
        doc_issue_reference,
        module_doc_budget,
        reason = "module documentation that predates the shape lint"
    )
)]
#![no_std]

extern crate alloc;

mod boundary;
mod elaborate;
mod instantiate;
mod term;

pub use crate::boundary::AdmittedFaceIndex;
pub use crate::boundary::ConstructorCount;
pub use crate::boundary::DeclinedFaceIndex;
pub use crate::boundary::DeclinedOpIndex;
pub use crate::boundary::OperationInputCount;
pub use crate::boundary::RedexOccurrenceCount;
pub use crate::boundary::RuleGrowth;
pub use crate::elaborate::CircuitElaboration;
pub use crate::elaborate::DescElaboration;
pub use crate::elaborate::DescReading;
pub use crate::elaborate::ElaborateError;
pub use crate::elaborate::EtaElaborateError;
pub use crate::elaborate::EtaElaboration;
pub use crate::elaborate::MixedPolarityHole;
pub use crate::elaborate::OpElaborateError;
pub use crate::elaborate::OpFrame;
pub use crate::elaborate::PresentedRules;
pub use crate::elaborate::command_reading;
pub use crate::elaborate::elaborate_call;
pub use crate::elaborate::elaborate_data_desc;
pub use crate::elaborate::elaborate_rule;
pub use crate::elaborate::elaborate_theory_desc;
pub use crate::elaborate::presented_reading;
pub use crate::elaborate::read_command;
pub use crate::instantiate::CellInstantiationError;
pub use crate::instantiate::CircuitShift;
pub use crate::instantiate::CircuitShiftObstruction;
pub use crate::instantiate::ConvexityGrant;
pub use crate::instantiate::ConvexitySupply;
pub use crate::instantiate::RewriteBinding;
pub use crate::instantiate::instantiate_cell;
pub use crate::instantiate::instantiate_two_redex_rule;
pub use crate::term::Term;
pub use crate::term::TermAlphabet;
pub use crate::term::TermMeta;
pub use crate::term::TermOrient;
pub use crate::term::TermPos;
pub use crate::term::TermProv;
pub use crate::term::TermSubst;
pub use crate::term::face_cell;
pub use crate::term::rule_keeps_growing;
pub use crate::term::term_reading;
