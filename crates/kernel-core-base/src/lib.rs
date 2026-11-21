//! The kernel's **record and its rewriting**: the admitted entries and their
//! staging, the content encoding that names each record, the support a check
//! reads, the rewriting of terms, the refusals of the kernel, and the verdict
//! keys and receipts.
//!
//! The crate holds no judgement. The judgement stands in `gandr-kernel-core`,
//! which admits each declaration into this record. A change of the judgement
//! builds this crate again only when this crate changes.
//!
//! The record reads its own build identity from no file. Each derivation of a
//! verdict key takes the build identity that the judgement passes, so the key
//! binds the files of both crates.

// Module documentation that predates the shape lint: headings outside the
// vocabulary, decision records, issue references and budgets exceeded. Each
// allow leaves with the rewrite that clears its count.
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

pub mod admitted;
pub mod census;
pub mod encoding;
pub mod env;
pub mod error;
#[cfg(any(test, feature = "fixture"))]
pub mod fixture;
pub mod fork;
#[cfg(any(test, feature = "fixture"))]
pub mod generated;
pub mod hashed;
pub mod levels;
pub mod occurrence;
pub mod presented;
pub mod rewrite;
pub mod seal;
pub mod support;
pub mod theory_rules;
pub mod verdict;
pub mod weakening;
pub mod witness;

pub use crate::admitted::AdmissionPolicy;
pub use crate::admitted::AdmittedCount;
pub use crate::census::ExpansionCensus;
pub use crate::census::ExpansionCount;
pub use crate::census::ExpansionKind;
pub use crate::encoding::ContentEncoding;
pub use crate::encoding::ContentId;
pub use crate::encoding::ContentTable;
pub use crate::encoding::EncodingLength;
pub use crate::encoding::Exact;
pub use crate::encoding::Identification;
pub use crate::encoding::MintNames;
pub use crate::encoding::ObligationGoal;
pub use crate::encoding::RecordName;
pub use crate::encoding::RewriteGoal;
pub use crate::encoding::SupportGoal;
pub use crate::encoding::content_digest;
pub use crate::encoding::encode_rewrite;
pub use crate::encoding::support_key;
pub use crate::env::Admission;
pub use crate::env::AdmittedDeclaration;
pub use crate::env::CheckedId;
pub use crate::env::Entries;
pub use crate::env::OutstandingContent;
pub use crate::env::OutstandingCount;
pub use crate::env::StagedDeclaration;
pub use crate::env::Staging;
pub use crate::env::tallied;
pub use crate::error::CompTypeHead;
pub use crate::error::CompTypeMismatch;
pub use crate::error::CompTypeWitness;
pub use crate::error::ExpectedComputationShape;
pub use crate::error::ExpectedValueShape;
pub use crate::error::FieldCause;
pub use crate::error::GuardBreak;
pub use crate::error::GuardNode;
pub use crate::error::KeepRefusal;
pub use crate::error::KeptOutcomes;
pub use crate::error::KernelError;
pub use crate::error::LevelOrderRefutation;
pub use crate::error::NonInferableForm;
pub use crate::error::RegisterFault;
pub use crate::error::UniverseViolation;
pub use crate::error::ValueTypeHead;
pub use crate::error::ValueTypeMismatch;
pub use crate::error::ValueTypeWitness;
pub use crate::levels::LevelContext;
pub use crate::presented::Presentations;
pub use crate::rewrite::BinderDepth;
pub use crate::rewrite::RewriteMemo;
pub use crate::rewrite::RewriteOutcome;
pub use crate::rewrite::RewritePlane;
pub use crate::rewrite::RewriteSupport;
pub use crate::rewrite::shift_value_type;
pub use crate::rewrite::substitute_comp_type;
pub use crate::rewrite::substitute_comp_type_at_call;
pub use crate::support::NodeOutcome;
pub use crate::support::NodeSupport;
pub use crate::support::Owed;
pub use crate::support::SupportContext;
pub use crate::support::SupportPlane;
