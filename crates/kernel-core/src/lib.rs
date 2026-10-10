//! The kernel's **checking machine, conversion, and admission choke point**,
//! with the check memo wired as the default path on both machines.
//!
//! The crate holds judgements. The representation, the sharing format and the
//! decode budgets belong to the term crate below it; the level algebra to the
//! strata crate; the memo's storage to the check-memo seam crate. What lives
//! here is what re-derives an obligation.
//!
//! # Four decisions that interlock
//!
//! **The checker is a defunctionalized machine** over a goal register, a
//! produced register, a heap frame stack and an explicit typing-context stack,
//! never mutually recursive methods bounded by a depth budget — so it is total
//! on adversarial depth, which decode can build from bytes. Its correspondence
//! table, arm by arm, is in [`check`], and it is the trusted-base audit
//! artifact a reviewer walks to confirm the machine *is* the judgement.
//!
//! **Conversion is structural comparison with an id-equality fast path**, and
//! the fast path is **positive only**: equal ids discharge a pair, unequal ids
//! decide nothing. That asymmetry is what keeps it sound while taking no table
//! into the trusted base.
//!
//! **Admission truncates on both verdicts.** The choke point keeps this
//! declaration's content and drops the checker's intermediates on success, and
//! drops both on rejection — clamped at the admission floor so a rollback can
//! never delete content a prior admission committed.
//!
//! **The memo is the default path on both machines.** Admitting one declaration
//! runs two iterative machines over the shared graph, and both consult it. A
//! memo covering only the term half would ship a small constant against an
//! exponential capability.
//!
//! # The memo's six binding conditions, and where each lives
//!
//! The seam crate names no term type, so everything that makes a memo *sound*
//! is a consumer obligation, and this crate is the consumer.
//!
//! | condition                                              | where it is discharged                                                                             |
//! | ------------------------------------------------------ | -------------------------------------------------------------------------------------------------- |
//! | static dispatch on a null-object seam that compiles away | [`check::check_declaration_with_memo`] is generic; every memo interaction is behind a compile-time activity constant |
//! | the public admission entry cannot reach the opt-in entry | [`env::Environment::add_decl`] takes no memo and builds its own; the memo-taking entry admits nothing and returns no receipt |
//! | a lifetime of one check call                            | [`check::check_declaration`] builds a memo and drops it; nothing stores one                        |
//! | the content-only key                                    | [`encoding`] and [`support`]: `(direction, obligation content, expected content, telescope content)`, arena-free |
//! | storage and policy outside the kernel crate             | the seam crate owns the table and its ordering; this crate holds a type parameter                  |
//! | no authority and no persistence in a hit                | a hit claims only that this process already computed this answer for this support                   |
//!
//! # Sharing and persistence
//!
//! No interning table of decoded values, no content-keyed memo the
//! *conversion* path consults, and no persistence. What a decode hands over is
//! the sharing the checker sees, and id equality is conversion's only
//! sharing-aware step. The one place the kernel creates sharing is the rewrite
//! memo, among nodes it minted past the admission watermark, and nothing
//! decides on that sharing. The kernel's own type conversion performs no
//! search, so it records no conversion trace; [`replay()`] is where the kernel
//! reads one, rechecking an untrusted engine's term-conversion verdict decision
//! by decision.
//!
//! The crate's measurements, mutation findings and admission rules are in its
//! `README.md`.

#![no_std]

extern crate alloc;

pub mod census;
pub mod check;
pub mod conv;
pub mod encoding;
pub mod env;
pub mod error;
pub mod flow_universe;
pub mod higher_field;
pub mod identity_recursion;
pub mod levels;
pub mod path_universe;
pub mod replay;
pub mod rewrite;
pub mod support;
mod witness;

pub use crate::census::ExpansionCensus;
pub use crate::census::ExpansionCount;
pub use crate::census::ExpansionKind;
pub use crate::check::DefaultMemo;
pub use crate::check::Judgement;
pub use crate::check::check_declaration;
pub use crate::check::check_declaration_with_memo;
pub use crate::conv::Convertibility;
pub use crate::conv::convert_comp_type;
pub use crate::conv::convert_value_type;
pub use crate::conv::convertible_comp_types;
pub use crate::conv::convertible_value_types;
pub use crate::encoding::ContentEncoding;
pub use crate::encoding::ContentId;
pub use crate::encoding::ContentTable;
pub use crate::encoding::EncodingLength;
pub use crate::encoding::RewriteGoal;
pub use crate::encoding::SupportGoal;
pub use crate::encoding::content_digest;
pub use crate::encoding::encode_rewrite;
pub use crate::encoding::encode_support;
pub use crate::env::Admission;
pub use crate::env::AdmittedDeclaration;
pub use crate::env::AxiomReport;
pub use crate::env::CheckedId;
pub use crate::env::Environment;
pub use crate::env::OutstandingContent;
pub use crate::env::OutstandingCount;
pub use crate::env::StagedDeclaration;
pub use crate::env::Staging;
pub use crate::error::CompTypeHead;
pub use crate::error::CompTypeMismatch;
pub use crate::error::CompTypeWitness;
pub use crate::error::ExpectedComputationShape;
pub use crate::error::ExpectedValueShape;
pub use crate::error::KernelError;
pub use crate::error::LevelOrderRefutation;
pub use crate::error::NonInferableForm;
pub use crate::error::RegisterFault;
pub use crate::error::UniverseViolation;
pub use crate::error::ValueTypeHead;
pub use crate::error::ValueTypeMismatch;
pub use crate::error::ValueTypeWitness;
pub use crate::levels::LevelContext;
pub use crate::replay::EngineClaim;
pub use crate::replay::KernelVerdict;
pub use crate::replay::ParameterCount;
pub use crate::replay::ReplayBudget;
pub mod session;
pub use crate::replay::ReplayDecline;
pub use crate::replay::ReplayNode;
pub use crate::replay::ReplayRefusal;
pub use crate::replay::ReplaySides;
pub use crate::replay::TracePosition;
pub use crate::replay::Unfoldable;
pub use crate::replay::Unfoldings;
pub use crate::replay::replay;
pub use crate::rewrite::BinderDepth;
pub use crate::rewrite::RewriteMemo;
pub use crate::rewrite::RewriteOutcome;
pub use crate::rewrite::RewritePlane;
pub use crate::rewrite::RewriteSupport;
pub use crate::rewrite::shift_value_type;
pub use crate::rewrite::substitute_comp_type;
pub use crate::support::LooseDepth;
pub use crate::support::LooseDepths;
pub use crate::support::NodeOutcome;
pub use crate::support::NodeSupport;
pub use crate::support::SupportContext;
pub use crate::support::SupportPlane;
