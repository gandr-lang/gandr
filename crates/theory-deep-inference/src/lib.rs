//! The identity relations on derivations: when two derivations that fire the
//! same cells in different orders are the same derivation, and what structure
//! decides it.
//!
//! The modules are one construction read in order. Two adjacent applications
//! commute when the shift guard earns them a witness
//! ([`derive_shift_equivalence`]); one derivation's events, ordered by that
//! relation, form a finite partial order with a canonical schedule
//! ([`event_order`], [`EventOrder`]); the derivation factors into
//! content-addressed primitives scheduled canonically, compared as a sound fast
//! path below replay ([`normalize`], [`normalize_certified`], [`nf_equal`]) and
//! planned for replay by antichain levels ([`ReplayPlan`]); and the order is
//! read as a two-colour web ([`causal_web()`], [`refines`]), as an atomic flow
//! ([`project_flow`]) and against a polarized footprint
//! ([`footprint_independence`]). The causal order and the normal form depend
//! on each other — an event's key digests its causal past, and the order is
//! read back to schedule the normal form — so the crate encloses both. A
//! family of certificates sharing one skeleton folds into one guarded
//! template where that pays ([`anti_unify_tracelets`], [`GuardedTemplate`]).
//!
//! Replay in `gandr-theory-coherent-resolutions` is the semantic oracle: every
//! relation here is sound below it, and a negative answer means "not
//! identified", never "distinct". Everything is generic over the substrate's
//! [`CellAlphabet`](gandr_theory_cell_complexes::CellAlphabet). The crate is
//! `no_std` and depends on `alloc`, the substrate, the engine and
//! `quenchant-shape`.
//!
//! # Example
//!
//! Ask whether two adjacent applications commute, and read the refusal when
//! they do not.
//!
//! ```rust
//! use gandr_theory_cell_complexes::CellAlphabet;
//! use gandr_theory_cell_complexes::CellStore;
//! use gandr_theory_coherent_resolutions::CellApp;
//! use gandr_theory_deep_inference::ShiftObstruction;
//! use gandr_theory_deep_inference::derive_shift_equivalence;
//!
//! fn explain<A: CellAlphabet>(
//!     store: &CellStore<A>,
//!     peak: &A::Cmd,
//!     first: &CellApp<A>,
//!     second: &CellApp<A>,
//! ) -> &'static str
//! {
//!     match derive_shift_equivalence(store, peak, first, second) {
//!         Ok(_witness) => "the two applications commute",
//!         Err(ShiftObstruction::UnknownCell { .. }) => "an application names no stored cell",
//!         Err(ShiftObstruction::ComparablePositions { .. }) => "one position encloses the other",
//!         Err(ShiftObstruction::GenuineOverlap { .. }) => "the two cells overlap at a seam",
//!         Err(ShiftObstruction::ConvexityNotDischarged) => {
//!             "the alphabet withholds the convexity warrant"
//!         },
//!         Err(ShiftObstruction::StepDoesNotFire { .. }) => "a sequentialization does not fire",
//!         Err(ShiftObstruction::SequentializationsDiffer { .. }) => {
//!             "the two orders reach different terms"
//!         },
//!     }
//! }
//! ```
//!
//! # Oracle tests over the engine
//!
//! Three tests read the engine's outputs through this crate's normalizer: every
//! certificate completion emits is certified and replays along its plan, a
//! relabelled twin schedules and replays identically, and the batches the
//! overlap support schedules replay along their plans. Each claims something
//! about this crate's normalizer over the engine's outputs, so they live in
//! this crate's integration suite, over the sequent alphabet the engine's own
//! suites use. Placing them in the engine would need a dev-dependency from the
//! engine onto a crate above it, inverting the layering in the dev graph. They
//! move to the engine when an engine specification clause takes the certified
//! normal form as its witness.
//!
//! # Specification evidence
//!
//! Nontrivial implementations and their fixture oracles carry executable
//! `#[spec]` obligations and an item-local `# Adequacy` argument. Enforcement
//! with `--cfg anodized_panic` checks those obligations during the unit and
//! integration suites. The hypotheses state the input domain, the observer and
//! the mutations it separates; generated cases are sampled evidence, not
//! universal proofs.
//!
//! The boundary witnesses cover empty orders and replay plans, fuel and lookup
//! refusal priority, repeated and absent factors, layered dependencies, flow
//! ports and peak anchors, reversed web coordinates, and template cache and
//! admission transitions. The finite cube checks the exact verdict for every
//! ordered pair of its six paths. Content hashing is checked against the
//! published FNV-128 vectors in [draft-eastlake-fnv-25, Appendix
//! C](https://www.ietf.org/archive/id/draft-eastlake-fnv-25.html#appendix-C);
//! the content-faithfulness corpus remains a finite collision witness rather
//! than a claim that a finite digest is injective.
//!
//! Two generator returns remain exempt: their opaque `impl Strategy` return
//! cannot appear in the attribute's evaluation closure under enforcement. The
//! local corpus trait and its two abstract methods also remain exempt: trait
//! instrumentation emits qualifier constants rejected by the lint wall. Both
//! concrete implementations carry executable obligations. These exemptions are
//! removed when the attribute implementation supports the return form and emits
//! lint-compatible trait qualifiers; no lint is relaxed to admit them. The
//! ignored `tests::template::verdict_table` witness is run explicitly with
//! `--ignored --nocapture` to exercise the rendered report.
//!
//! # References
//!
//! - Alessio Guglielmi and Tom Gundersen. "Normalisation Control in Deep
//!   Inference via Atomic Flows." _Logical Methods in Computer Science_ 4, 1
//!   (2008), paper 9. `doi:10.2168/LMCS-4(1:9)2008` — atomic flows as graphs
//!   traced from atom occurrences with the logical structure forgotten
//!   (Definition 3.2), the object `project_flow` computes over a derivation's
//!   term positions.
//! - Nicolas Behr. "Tracelets and Tracelet Analysis of Compositional Rewriting
//!   Systems." In _Proceedings of Applied Category Theory 2019_, Electronic
//!   Proceedings in Theoretical Computer Science 323 (2020), pages 44–71.
//!   `doi:10.4204/EPTCS.323.4` — tracelets as derivations recorded for
//!   re-execution, the certificate data every relation here reads.
//! - Victoria Barrett, Alessio Guglielmi, Benjamin Ralph, and Lutz Straßburger.
//!   "Proof Compression via Subatomic Logic and Guarded Substitutions." In
//!   _Proceedings of the 40th Annual ACM/IEEE Symposium on Logic in Computer
//!   Science (LICS 2025)_, 2025. Preprint `arXiv:2505.20009` — guarded
//!   substitutions over a superposed proof and their two recorded prices, the
//!   quadratic range-inheritance check and the interpretation map; the guarded
//!   template is the first and never pays the second.
//! - Nicolas Behr and Joachim Kock. "Tracelet Hopf Algebras and Decomposition
//!   Spaces (Extended Abstract)." In _Proceedings of the Fourth International
//!   Conference on Applied Category Theory_, Electronic Proceedings in
//!   Theoretical Computer Science 372 (2022). `doi:10.4204/EPTCS.372.23` — the
//!   shift quotient of the tracelet algebra is free on its primitives, which
//!   the normal form reads as a unique factorization into content-addressed
//!   primitives with multiplicities.
//! - Filippo Bonchi, Fabio Gadducci, Aleks Kissinger, Paweł Sobociński, and
//!   Fabio Zanasi. "String Diagram Rewrite Theory II: Rewriting with Symmetric
//!   Monoidal Structure." _Mathematical Structures in Computer Science_ 32, 4
//!   (2022), pages 511–541. `doi:10.1017/S0960129522000317`; preprint
//!   `arXiv:2104.14686` — convex matching and the example of two disjoint
//!   matches that interfere through each other's convexity, the reason the
//!   shift guard carries a convexity conjunct and the flow projection is sound
//!   only under its discharge.
//! - Matteo Acclavio, Ross Horne, Sjouke Mauw, and Lutz Straßburger. "A
//!   Graphical Proof Theory of Logical Time." In _7th International Conference
//!   on Formal Structures for Computation and Deduction (FSCD 2022)_, `LIPIcs`
//!   228, 2022, pages 22:1–22:25. `doi:10.4230/LIPIcs.FSCD.2022.22` — causal
//!   webs with green precedence and white independence, and the slice-chain
//!   weakening `refines` decides on the identity-map fragment.
//! - Paul-André Melliès and Léo Stefanesco. "Concurrent Separation Logic Meets
//!   Template Games." Preprint, May 2020. `arXiv:2005.04453` — independence of
//!   transitions over read and write footprints, the reading the polarized
//!   footprint test takes and the shift guard is measured against.
//! - Paul-André Melliès. "Asynchronous Template Games and the Gray Tensor
//!   Product of 2-Categories." In _36th Annual ACM/IEEE Symposium on Logic in
//!   Computer Science (LICS 2021)_, June 2021.
//!   `doi:10.1109/LICS52264.2021.9470758` — asynchronous graphs and their
//!   symmetry, determinism and cube axioms, checked against the shift witness
//!   by the integration suite.

// Module documentation that predates the shape lint: 38 headings outside the
// vocabulary, 1 decision record and 5 budgets exceeded. Each allow leaves with
// the rewrite that clears its count.
#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    allow(
        module_doc_heading,
        doc_decision_record,
        module_doc_budget,
        reason = "module documentation that predates the shape lint"
    )
)]
#![no_std]
#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(linear_search_in_loop, reason = "8 cost-shape sites; #814 lists them")
)]
#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        allocation_in_repeated_body,
        reason = "2 cost-shape sites; #814 lists them"
    )
)]

extern crate alloc;

#[macro_use]
mod boundary;
mod causal;
mod causal_web;
mod flow;
mod footprint;
mod normal_form;
mod shift;
mod template;

pub use crate::boundary::AdmissionCount;
pub use crate::boundary::CacheHitCount;
pub use crate::boundary::CausalDepth;
pub use crate::boundary::EntryIndex;
pub use crate::boundary::EventConcurrency;
pub use crate::boundary::EventCount;
pub use crate::boundary::EventDependence;
pub use crate::boundary::EventIndex;
pub use crate::boundary::EventPrecedence;
pub use crate::boundary::ExpansionFactor;
pub use crate::boundary::FlowEquality;
pub use crate::boundary::FlowPortIndex;
pub use crate::boundary::FlowVertexIndex;
pub use crate::boundary::GuardId;
pub use crate::boundary::LegStepIndex;
pub use crate::boundary::MemberCount;
pub use crate::boundary::MemberIndex;
pub use crate::boundary::NodeCount;
pub use crate::boundary::NormalFormEquality;
pub use crate::boundary::PeakOccurrenceIndex;
pub use crate::boundary::PrimMultiplicity;
pub use crate::boundary::ReplayLevel;
pub use crate::boundary::ReplayStepCount;
pub use crate::boundary::SchedulePosition;
pub use crate::boundary::ShiftReplay;
pub use crate::boundary::SliceStepCount;
pub use crate::boundary::TranspositionCount;
pub use crate::boundary::TripleCount;
pub use crate::boundary::WebIndependence;
pub use crate::boundary::WebPrecedence;
pub use crate::boundary::WebVertex;
pub use crate::boundary::WebVertexCount;
pub use crate::causal::DerivationEvent;
pub use crate::causal::EventKey;
pub use crate::causal::EventOrder;
pub use crate::causal::ExchangeObstruction;
pub use crate::causal::ExchangeWitness;
pub use crate::causal::KeyCollision;
pub use crate::causal::Transposition;
pub use crate::causal::event_lookup;
pub use crate::causal::exchange_application;
pub use crate::causal_web::CausalWeb;
pub use crate::causal_web::DependenceBits;
pub use crate::causal_web::HomomorphismFrontier;
pub use crate::causal_web::RefinementCounterexample;
pub use crate::causal_web::RefinementVerdict;
pub use crate::causal_web::SliceChain;
pub use crate::causal_web::SliceStep;
pub use crate::causal_web::WebRelation;
pub use crate::causal_web::causal_web;
pub use crate::causal_web::refines;
pub use crate::causal_web::web_lookup;
pub use crate::flow::Flow;
pub use crate::flow::FlowEnd;
pub use crate::flow::FlowObstruction;
pub use crate::flow::FlowThread;
pub use crate::flow::TraceletFlow;
pub use crate::flow::flow_canonical;
pub use crate::flow::flows_equal;
pub use crate::flow::legs_flow_equal;
pub use crate::flow::project_flow;
pub use crate::flow::tracelet_flow;
pub use crate::flow::tracelets_flow_equal;
pub use crate::footprint::FootprintIndependence;
pub use crate::footprint::FootprintObstruction;
pub use crate::footprint::MatchFootprint;
pub use crate::footprint::footprint_independence;
pub use crate::footprint::match_footprint;
pub use crate::normal_form::CausalPast;
pub use crate::normal_form::CellAddress;
pub use crate::normal_form::NormalFormObstruction;
pub use crate::normal_form::PrimCert;
pub use crate::normal_form::PrimId;
pub use crate::normal_form::ReplayPlan;
pub use crate::normal_form::ReplayWitness;
pub use crate::normal_form::TraceletNf;
pub use crate::normal_form::causal_past_address;
pub use crate::normal_form::cell_address;
pub use crate::normal_form::certified_nf_equal;
pub use crate::normal_form::event_order;
pub use crate::normal_form::nf_equal;
pub use crate::normal_form::nf_equal_across_stores;
pub use crate::normal_form::normalize;
pub use crate::normal_form::normalize_certified;
pub use crate::normal_form::prim_address;
pub use crate::normal_form::replay_fuel;
pub use crate::normal_form::schedule_resolution;
pub use crate::normal_form::tracelets_nf_equal;
pub use crate::shift::ShiftEquivalence;
pub use crate::shift::ShiftObstruction;
pub use crate::shift::derive_shift_equivalence;
pub use crate::template::ArmAddress;
pub use crate::template::FamilyCostReport;
pub use crate::template::GuardedTemplate;
pub use crate::template::InheritanceCache;
pub use crate::template::InheritanceKey;
pub use crate::template::InheritanceVerdict;
pub use crate::template::MemoizedPriceRefusal;
pub use crate::template::ProductionCounts;
pub use crate::template::TemplateAddress;
pub use crate::template::TemplateArm;
pub use crate::template::TemplateEntry;
pub use crate::template::TemplateLeg;
pub use crate::template::TemplateObstruction;
pub use crate::template::TemplateRefusal;
pub use crate::template::anti_unify_tracelets;
pub use crate::template::inheritance_lookup;
pub use crate::template::price_family;
pub use crate::template::price_family_memoized;
