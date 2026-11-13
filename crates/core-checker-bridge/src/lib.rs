//! **The kernel bridge of the core checking judgement**: [`bridge::readmit`]
//! erases every declaration the judgement accepted and offers it to the
//! kernel's one checked entry, and [`template`] holds the staging templates a
//! staged program reads.
//!
//! The judgement is in `gandr-core-checker-base`. `gandr-core-checker`
//! re-exports this crate and the base under one name, and its crate
//! documentation states the decisions that interlock. The tests that judge a
//! module and readmit it to witness the judgement are in the base's
//! integration target. The tests here witness the bridge.

// Module documentation that predates the shape lint: 22 headings outside the
// vocabulary, 6 decision records, 6 issue references and 13 budgets exceeded.
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

pub mod bridge;
pub mod template;

// The base's modules and items the bridge names, each at the path it had
// when the bridge and the base were one crate.
#[cfg(test)]
use gandr_core_checker_base::DeclarationContent;
#[cfg(test)]
use gandr_core_checker_base::Entered;
#[cfg(test)]
use gandr_core_checker_base::Unsolved;
#[cfg(test)]
use gandr_core_checker_base::check_declaration_supported;
use gandr_core_checker_base::code;
#[cfg(test)]
use gandr_core_checker_base::context;
use gandr_core_checker_base::conversion;
use gandr_core_checker_base::declaration;
use gandr_core_checker_base::divergence;
use gandr_core_checker_base::equiv;
#[cfg(test)]
use gandr_core_checker_base::fixture;
use gandr_core_checker_base::flow;
#[cfg(test)]
use gandr_core_checker_base::former;
use gandr_core_checker_base::forward;
use gandr_core_checker_base::funext;
use gandr_core_checker_base::handler;
#[cfg(test)]
use gandr_core_checker_base::judgement;
#[cfg(test)]
use gandr_core_checker_base::module;
use gandr_core_checker_base::occurrence;
use gandr_core_checker_base::program;
use gandr_core_checker_base::quantified;
use gandr_core_checker_base::refusal;
use gandr_core_checker_base::report;
use gandr_core_checker_base::retire;
#[cfg(test)]
use gandr_core_checker_base::seal;
#[cfg(test)]
use gandr_core_checker_base::synthesise_value;
use gandr_core_checker_base::view;
