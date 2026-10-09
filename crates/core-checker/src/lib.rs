//! **The core checking judgement**: four directed faces over the slice's
//! fragment of the core language, the name-free declaration input with its
//! origin token, the checking context wrapped around the core context, type
//! formation, the conversion module boundary with its declared projection,
//! the absence-only obligation ledger, the refusal vocabulary with its
//! classifier, and the kernel bridge that has the kernel re-derive every
//! declaration the judgement accepted.
//!
//! The crate reads core nodes a producer minted and answers, per declaration,
//! whether its body has its type. There is no surface here: no names, no
//! spans, no syntax. A declaration arrives as an admission position, two
//! halves each present or absent for a stated reason, and an opaque origin
//! token the verdict echoes back.
//!
//! # Six decisions that interlock
//!
//! **The former decides the mode.** Leaves and eliminations synthesise,
//! introductions check, and a dispatch on the direction names both cases, so a
//! rule added in one mode and forgotten in the other does not compile.
//!
//! **Types meet in two places.** A synthesising value or computation in
//! checking position crosses one of two bridges into the conversion module;
//! no rule compares types itself, and each crossing is counted in the result
//! a face returns.
//!
//! **Holes are directional.** A hole under a declared type absorbs it and owes
//! it; a hole with nothing to absorb is refused. No unknown type stands in for
//! a missing one.
//!
//! **Only an absence is owed.** The ledger is built from absences, which only
//! the hole rule makes; a refusal cannot be spelled as an obligation, and the
//! classifier leaves its absence class empty.
//!
//! **One machine, no recursion.** Every face runs one explicit machine of goals
//! and frames, charged one step per transition against an allowance.
//!
//! **The kernel re-derives.** [`bridge::readmit`] erases every accepted
//! declaration and offers it to the kernel's one checked entry: a body as a
//! definition, an owed hole as an axiom, a refused declaration as nothing.
//! The artifact's audit is empty exactly when the ledger is, and gates
//! nothing.
//!
//! # Example
//!
//! ```
//! use gandr_core_checker::CheckBudget;
//! use gandr_core_checker::CheckingContext;
//! use gandr_core_checker::Declaration;
//! use gandr_core_checker::OriginToken;
//! use gandr_core_checker::Verdict;
//! use gandr_core_checker::body;
//! use gandr_core_checker::bridge;
//! use gandr_core_checker::check_module;
//! use gandr_core_checker::signature;
//! use gandr_core_term::CoreArena;
//! use gandr_kernel_term::BaseType;
//! use gandr_kernel_term::ConstantIndex;
//! use gandr_kernel_term::IntegerLiteral;
//! use gandr_kernel_term::Literal;
//! use gandr_kernel_term::Magnitude;
//! use gandr_kernel_term::Sign;
//! use quenchant_shape::shape::Maybe;
//!
//! // def answer : Integer = 0 ; def owed : Integer ; def copy = answer ;
//! let mut arena = CoreArena::new();
//! let integer = arena.value_type_base(BaseType::Integer);
//! let zero = arena.value_literal(Literal::Integer(IntegerLiteral::new(
//!     Sign::NonNegative,
//!     Magnitude::zero(),
//! )));
//! let answer = arena.value_constant(ConstantIndex::from(0_usize));
//! let declarations = [
//!     Declaration::new(
//!         ConstantIndex::from(0_usize),
//!         Maybe::Present(integer),
//!         Maybe::Present(zero),
//!         OriginToken::from(0_usize),
//!     ),
//!     Declaration::new(
//!         ConstantIndex::from(1_usize),
//!         Maybe::Present(integer),
//!         Maybe::Absent(body::Absent::Hole),
//!         OriginToken::from(1_usize),
//!     ),
//!     Declaration::new(
//!         ConstantIndex::from(2_usize),
//!         Maybe::Absent(signature::Absent::Unsigned),
//!         Maybe::Present(answer),
//!         OriginToken::from(2_usize),
//!     ),
//! ];
//!
//! let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
//! let report = check_module(&mut context, &declarations);
//!
//! let [checked, owed, copied] = report.judged()
//! else {
//!     unreachable!("one verdict per declaration");
//! };
//! assert!(
//!     matches!(checked.verdict(), Verdict::Checked { .. }),
//!     "zero has type Integer"
//! );
//! assert!(
//!     matches!(owed.verdict(), Verdict::Owed(_)),
//!     "the hole owes its declared type"
//! );
//! assert!(
//!     matches!(copied.verdict(), Verdict::Synthesised { .. }),
//!     "a constant synthesises"
//! );
//! assert_eq!(
//!     usize::from(report.ledger().count()),
//!     1_usize,
//!     "one hole is owed"
//! );
//!
//! // The kernel defines the two bodies and assumes the hole.
//! let readmission = bridge::readmit(&arena, &report);
//! assert_eq!(
//!     readmission.environment().entries().len(),
//!     3_usize,
//!     "every declaration crossed"
//! );
//! assert_eq!(
//!     readmission.audit().axioms(),
//!     [ConstantIndex::from(1_usize)],
//!     "the artifact rests on the owed hole alone"
//! );
//! ```
//!
//! Each decision, with the alternative it was chosen over and what would
//! reverse it, is in this crate's `README.md`.

#![no_std]

extern crate alloc;

pub mod bridge;
mod context;
mod conversion;
mod declaration;
#[cfg(test)]
mod fixture;
mod formation;
mod judgement;
mod ledger;
mod module;
mod refusal;
mod support;
mod view;

pub use crate::context::CheckBudget;
pub use crate::context::CheckingContext;
pub use crate::context::signature_table;
pub use crate::conversion::ConversionCount;
pub use crate::declaration::Declaration;
pub use crate::declaration::OriginToken;
pub use crate::declaration::body;
pub use crate::declaration::signature;
pub use crate::formation::FormedCompType;
pub use crate::formation::FormedValueType;
pub use crate::formation::form_comp_type;
pub use crate::formation::form_value_type;
pub use crate::judgement::Checked;
pub use crate::judgement::Synthesised;
pub use crate::judgement::check_comp;
pub use crate::judgement::check_value;
pub use crate::judgement::synthesise_comp;
pub use crate::judgement::synthesise_value;
pub use crate::ledger::Absence;
pub use crate::ledger::ObligationCount;
pub use crate::ledger::ObligationEntry;
pub use crate::ledger::ObligationLedger;
pub use crate::module::Judged;
pub use crate::module::ModuleReport;
pub use crate::module::Verdict;
pub use crate::module::check_declaration;
pub use crate::module::check_declaration_supported;
pub use crate::module::check_module;
pub use crate::refusal::CheckRefusal;
pub use crate::refusal::CheckingForm;
pub use crate::refusal::CoreNode;
pub use crate::refusal::ExpectedShape;
pub use crate::refusal::Mismatch;
pub use crate::refusal::TermNode;
pub use crate::refusal::TypeNode;
pub use crate::refusal::UnadmittedFormer;
pub use crate::support::Consulted;
pub use crate::support::Support;
pub use crate::support::Supported;
