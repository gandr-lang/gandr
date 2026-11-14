//! **The base of the core checking judgement**: the four directed faces over
//! the slice's fragment of the core language, the name-free declaration input
//! with its origin token, the checking context wrapped around the core
//! context, type formation, the conversion boundary, the absence-only
//! obligation ledger, the refusal vocabulary, the elaboration that marks a
//! refusal and goes on, match coverage, and the module run that judges each
//! declaration of a module.
//!
//! The crate reads core nodes a producer minted and answers, per declaration,
//! whether its body has its type. The kernel bridge, which has the kernel
//! re-derive every accepted declaration, is in `gandr-core-checker-bridge`.
//! `gandr-core-checker` holds the staged programs and the elaboration session,
//! and re-exports this crate and the bridge under one name. Its crate
//! documentation states the decisions that interlock and the references.
//!
//! The integration target judges a module and readmits it through the bridge,
//! so the tests that witness a judgement and its readmission stay in the crate
//! that owns the judgement.

// Module documentation that predates the shape lint: 147 headings outside the
// vocabulary, 76 decision records, 37 issue references and 39 budgets exceeded.
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
// The profiler's instrumentation names `std`; it links only into the
// benchmark build.
#[cfg(feature = "hotpath")]
extern crate std;

pub mod access;
pub mod answer;
pub mod canonical;
pub mod capability;
pub mod codata;
pub mod code;
pub mod comonoid;
pub mod compose;
pub mod context;
pub mod conversion;
pub mod coverage;
pub mod declaration;
pub mod discharge;
pub mod divergence;
pub mod elaboration;
pub mod eliminator;
pub mod equiv;
pub mod failure;
pub mod fill;
#[cfg(any(test, feature = "fixture"))]
pub mod fixture;
pub mod flow;
pub mod formation;
pub mod former;
pub mod forward;
pub mod funext;
pub mod handler;
pub mod judgement;
pub mod ledger;
pub mod loops;
pub mod module;
pub mod nested;
pub mod occurrence;
pub mod product;
pub mod program;
pub mod quantified;
pub mod record;
pub mod recursion;
pub mod refusal;
pub mod regioned;
pub mod relatedness;
pub mod report;
pub mod respect;
pub mod retire;
pub mod seal;
pub mod session;
pub mod solution;
pub mod stage;
pub mod support;
pub mod tactic;
#[cfg(feature = "instrument")]
pub mod tally;
pub mod tier;
#[cfg(feature = "instrument")]
pub mod trace;
pub mod ua;
pub mod univalence;
pub mod view;
pub mod worlds;

pub use crate::answer::Checked;
pub use crate::answer::Direction;
pub use crate::answer::Synthesised;
pub use crate::capability::Grants;
pub use crate::capability::HostGrant;
pub use crate::code::Certificate;
pub use crate::code::CodeDefinitions;
pub use crate::code::Derivation;
pub use crate::code::EndpointRelation;
pub use crate::code::Evaluation;
pub use crate::code::Lift;
pub use crate::code::MetPair;
pub use crate::code::Reading;
pub use crate::code::Reflexivity;
pub use crate::code::Stalled;
pub use crate::code::Unfolded;
pub use crate::code::converted;
pub use crate::code::evaluated;
pub use crate::code::unfolding;
pub use crate::context::CheckBudget;
pub use crate::context::CheckingContext;
pub use crate::context::Checkpoint;
pub use crate::context::Formations;
pub use crate::context::data_scope;
pub use crate::context::signature_table;
pub use crate::conversion::ConversionCount;
pub use crate::coverage::Coverage;
pub use crate::coverage::CoverageFault;
pub use crate::coverage::Exhaustiveness;
pub use crate::coverage::Redundancy;
pub use crate::coverage::cover;
pub use crate::declaration::AbstractType;
pub use crate::declaration::AtomInterface;
pub use crate::declaration::Declaration;
pub use crate::declaration::DeclarationContent;
pub use crate::declaration::OriginToken;
pub use crate::declaration::body;
pub use crate::declaration::entry;
pub use crate::declaration::interface;
pub use crate::declaration::law;
pub use crate::declaration::signature;
pub use crate::equiv::Equivalence;
pub use crate::failure::Failure;
pub use crate::failure::FoldPremise;
pub use crate::failure::FrameRole;
pub use crate::failure::Obligation;
pub use crate::failure::Pursuit;
pub use crate::failure::Stage;
pub use crate::failure::judged;
pub use crate::flow::Statement;
pub use crate::formation::FormedCompType;
pub use crate::formation::FormedValueType;
pub use crate::formation::classify_comp_type;
pub use crate::formation::classify_value_type;
pub use crate::formation::form_comp_type;
pub use crate::formation::form_value_type;
pub use crate::formation::level_of;
pub use crate::forward::Directed;
pub use crate::forward::Forward;
pub use crate::funext::Funext;
pub use crate::funext::Step as FunextStep;
pub use crate::handler::Handled;
pub use crate::judgement::Elaboration;
pub use crate::judgement::MarkEntry;
pub use crate::judgement::Typings;
pub use crate::judgement::check_comp;
pub use crate::judgement::check_value;
pub use crate::judgement::elaborate_comp;
pub use crate::judgement::elaborate_value;
pub use crate::judgement::synthesise_comp;
pub use crate::judgement::synthesise_value;
pub use crate::judgement::type_value;
pub use crate::ledger::Absence;
pub use crate::ledger::ObligationCount;
pub use crate::ledger::ObligationEntry;
pub use crate::ledger::ObligationLedger;
pub use crate::module::Deciding;
pub use crate::module::Membership;
pub use crate::module::ModuleRun;
pub use crate::module::Schedule;
pub use crate::module::Taken;
pub use crate::module::Taking;
pub use crate::module::TypedModule;
pub use crate::module::check_declaration;
pub use crate::module::check_declaration_supported;
pub use crate::module::check_module;
pub use crate::module::taken;
pub use crate::module::type_module;
pub use crate::nested::NestedElaboration;
pub use crate::nested::Nesting;
pub use crate::record::Formed;
pub use crate::record::Typing;
pub use crate::refusal::ArgumentPosition;
pub use crate::refusal::CheckRefusal;
pub use crate::refusal::CheckingForm;
pub use crate::refusal::Compared;
pub use crate::refusal::CoreNode;
pub use crate::refusal::EndpointMiss;
pub use crate::refusal::ExpectedShape;
pub use crate::refusal::Forced;
pub use crate::refusal::LoopRespect;
pub use crate::refusal::Mismatch;
pub use crate::refusal::RunFault;
pub use crate::refusal::RunStep;
pub use crate::refusal::StaticArity;
pub use crate::refusal::TacticFault;
pub use crate::refusal::TermNode;
pub use crate::refusal::TypeNode;
pub use crate::refusal::UnadmittedFormer;
pub use crate::refusal::Unsolved;
pub use crate::refusal::compared;
pub use crate::report::Judged;
pub use crate::report::ModuleReport;
pub use crate::report::Verdict;
pub use crate::report::elaborated_report;
pub use crate::report::unmarked;
pub use crate::retire::Demand;
pub use crate::retire::Polled;
pub use crate::retire::Retirement;
pub use crate::retire::Unretired;
pub use crate::seal::ComponentOrdinal;
pub use crate::seal::SealError;
pub use crate::seal::SealId;
pub use crate::seal::SealSerial;
pub use crate::seal::SealSite;
pub use crate::seal::SealTable;
pub use crate::seal::SealingSite;
pub use crate::seal::minted_site;
pub use crate::support::CodataConsulted;
pub use crate::support::Consulted;
pub use crate::support::DataConsulted;
pub use crate::support::Entered;
pub use crate::support::Support;
pub use crate::support::Supported;
pub use crate::support::elaborated;
pub use crate::support::kept;
pub use crate::support::waits;
