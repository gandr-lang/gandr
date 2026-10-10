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
//! `quenchant-shape`. Its `README.md` carries the design and the references.

#![no_std]

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
