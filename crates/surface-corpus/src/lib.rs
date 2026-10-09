//! **The expectation language over a lowered module and its verdicts**: the
//! `checks`, `owes`, `refuses` and `runs` schemas read off the attribute side
//! table, the strict and fixture corpus roots, the settle comparison, and the
//! report a runner reads its counts from.
//!
//! The crate reads what the lowering and the checker already produced and
//! decides one predicate over it. There is no parser here, no machine, no file
//! walk and no process exit: a caller hands over a lowered module, the
//! checker's report for the same module, the arena both wrote into, the root
//! the source sits under, and a [`Runner`] that spells a declaration's run
//! outcome, and receives a [`SettleReport`].
//!
//! # Four decisions that interlock
//!
//! **One predicate.** A declaration is settled when the verdict it produced
//! equals the verdict it states, and a declaration stating nothing states
//! *checks, owing nothing*. An obligation survives when it is unsettled:
//! produced with nothing declaring it, or declared with nothing producing it.
//! A run is settled when every declaration in it is.
//!
//! **Membership is location.** Under the [strict root](CorpusRoot::Strict) an
//! `owes` or `refuses` attribute is itself the refusal
//! [`ExpectationOutsideFixtureRoot`](CorpusRefusal::ExpectationOutsideFixtureRoot),
//! and every declaration is held to *checks, owing nothing* whatever it
//! states, so a red declaration cannot describe itself green. Under the
//! [fixture root](CorpusRoot::Fixture) the four schemas assert what the
//! checker refuses, what it owes and what a run produces.
//!
//! **A declared obligation is signed, not waived.** The ledger size is part of
//! every report, settled or not, so an assumption is never silent.
//!
//! **Sealed is reported, never gated.** A run is [sealed](Seal::Sealed) when it
//! is settled and its ledger is empty; that is a property a report states, and
//! nothing here makes it a condition of success.
//!
//! # Example
//!
//! ```
//! use gandr_core_checker::CheckBudget;
//! use gandr_core_checker::CheckingContext;
//! use gandr_core_checker::Declaration;
//! use gandr_core_checker::OriginToken;
//! use gandr_core_checker::body;
//! use gandr_core_checker::check_module;
//! use gandr_core_checker::signature;
//! use gandr_core_term::CoreArena;
//! use gandr_kernel_term::ConstantIndex;
//! use gandr_surface_corpus::CorpusRoot;
//! use gandr_surface_corpus::RunSpelling;
//! use gandr_surface_corpus::Seal;
//! use gandr_surface_corpus::Settlement;
//! use gandr_surface_corpus::settle;
//! use gandr_surface_grammar::built_in;
//! use gandr_surface_lowering::DeclarationOutcome;
//! use gandr_surface_lowering::LoweringBudget;
//! use gandr_surface_lowering::lower_module;
//! use gandr_surface_lowering::namespace::Recognition;
//! use gandr_surface_parser::parse;
//! use gandr_surface_syntax::SourceText;
//! use quenchant_shape::shape::Maybe;
//!
//! let source = SourceText::from(
//!     r#"@[ owes(1) ] def owed : Integer ;
//! @[ refuses("UnresolvedName") ] def broken = missing ;"#,
//! );
//! let pbg = built_in()?;
//! let tree = parse(&pbg, source)?.into_tree();
//! let mut arena = CoreArena::new();
//! let module = lower_module(
//!     &pbg,
//!     &tree,
//!     &mut arena,
//!     LoweringBudget::DEFAULT,
//!     Recognition::default(),
//! )?;
//!
//! // The driver's adaptation: every declaration the lowering did not refuse.
//! let declarations: Vec<Declaration> = module
//!     .declarations()
//!     .iter()
//!     .filter_map(|lowered| {
//!         let (declared, defined) = match lowered.outcome() {
//!             | DeclarationOutcome::Completed {
//!                 declared_type,
//!                 body,
//!             } => (Maybe::Present(declared_type), Maybe::Present(body)),
//!             | DeclarationOutcome::Uncompleted { declared_type } => (
//!                 Maybe::Present(declared_type),
//!                 Maybe::Absent(body::Absent::Hole),
//!             ),
//!             | DeclarationOutcome::Bodied { body } => (
//!                 Maybe::Absent(signature::Absent::Unsigned),
//!                 Maybe::Present(body),
//!             ),
//!             | DeclarationOutcome::Refused(_) => return None,
//!         };
//!         let origin = OriginToken::from(usize::from(lowered.origin()));
//!         Some(Declaration::new(
//!             lowered.constant(),
//!             declared,
//!             defined,
//!             origin,
//!         ))
//!     })
//!     .collect();
//! let verdicts = check_module(
//!     &mut CheckingContext::new(&mut arena, CheckBudget::DEFAULT),
//!     &declarations,
//! );
//!
//! // No declaration states a run outcome, so the runner is never asked.
//! let mut runner = |_constant: ConstantIndex| RunSpelling::from(String::new());
//! let report = settle(CorpusRoot::Fixture, &arena, &module, &verdicts, &mut runner)?;
//! let tally = report.tally();
//! assert_eq!(
//!     tally.settlement(),
//!     Settlement::Settled,
//!     "each fixture states the verdict it produced"
//! );
//! assert_eq!(
//!     usize::from(tally.ledger()),
//!     1_usize,
//!     "the declared obligation is still owed"
//! );
//! assert_eq!(
//!     tally.seal(),
//!     Seal::Unsealed,
//!     "an owed run is settled, not sealed"
//! );
//! # Ok::<(), Box<dyn core::error::Error>>(())
//! ```
//!
//! Each decision, with the alternative it was chosen over and what would
//! reverse it, is in this crate's `README.md`.

#![no_std]

extern crate alloc;

mod expectation;
#[cfg(test)]
mod fixture;
mod refusal;
mod report;
mod root;
mod run;
mod settle;

pub use crate::expectation::ExpectationFault;
pub use crate::expectation::ExpectationSchema;
pub use crate::expectation::Membership;
pub use crate::expectation::Outcome;
pub use crate::expectation::Stated;
pub use crate::expectation::expectation_schema;
pub use crate::refusal::CorpusRefusal;
pub use crate::refusal::Refusal;
pub use crate::refusal::RefusalName;
pub use crate::refusal::RefusalSpelling;
pub use crate::refusal::refusal_name;
pub use crate::report::ClassCounts;
pub use crate::report::Seal;
pub use crate::report::SettleCounts;
pub use crate::report::SettleReport;
pub use crate::report::Tally;
pub use crate::root::CorpusRoot;
pub use crate::run::RunSpelling;
pub use crate::run::Runner;
pub use crate::settle::DeclarationReport;
pub use crate::settle::Produced;
pub use crate::settle::SettleFault;
pub use crate::settle::Settlement;
pub use crate::settle::Surviving;
pub use crate::settle::produced_refusal;
pub use crate::settle::ran;
pub use crate::settle::settle;
