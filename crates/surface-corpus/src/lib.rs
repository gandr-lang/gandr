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
//! and a declaration must check owing nothing; an admitted `runs` additionally
//! requires its stated run outcome. A red declaration cannot describe itself
//! green. Under the
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
//!             | DeclarationOutcome::Data(index) => {
//!                 let origin = OriginToken::from(usize::from(lowered.origin()));
//!                 return match module.data(index) {
//!                     | Maybe::Present(signature) => Some(Declaration::data(
//!                         lowered.constant(),
//!                         std::sync::Arc::clone(signature),
//!                         origin,
//!                     )),
//!                     | Maybe::Absent(_) => None,
//!                 };
//!             },
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
//! reverse it, is in the module that owns it.
//!
//! # Specification and adequacy
//!
//! Executable predicates cover root admission, schema and refusal mappings,
//! payload interpretation, settlement precedence, ordered declaration
//! alignment, directional obligation differences, saturating tally transitions
//! and the kernel-export partition. Mutation predicates retain only scalar
//! snapshots or addresses; settlement compares borrowed run spellings rather
//! than cloning them. The private attribute iterator exposes its two borrowed
//! slices so a predicate can check order without consuming the result. An
//! opaque iterator becomes preferable again if specification instrumentation
//! supports opaque return types.
//!
//! Adequacy names each witness and its finite input class. Source witnesses
//! cover strict-root guards, conflicting and malformed attributes, run
//! mismatches, refusal names and alignment failures; boundary witnesses cover
//! numeric overflow, every tally channel and sink refusal. A later alignment
//! error does not roll back or repeat earlier runner calls. Corpus export
//! witnesses establish composition over the current sources, not a general
//! semantic oracle.
//!
//! Exemptions identify the unavailable observation: data and vocabulary
//! declarations have no call boundary; formatters expose no readable sink;
//! runner semantics depend on the caller's module and machine. Source, arena
//! and checker-report provenance remains a caller premise. `ClassCounts::count`
//! preserves its public constant-evaluation support, but its foreign
//! `DeclarationCount` result has no public const scalar observer; an
//! owning-crate observer would permit that predicate without changing this API.
//! The alternative is breaking constant callers to inspect a private
//! representation, which this crate does not do.
//!
//! # Inputs, not a pipeline
//!
//! This crate reads a lowered module and its verdicts and depends on neither
//! the parser nor the dispatcher; adapting the lowering's declarations to the
//! checker's input and walking the roots belong to the dispatcher, and the exit
//! codes to the driver. The suite depends on the parser and the grammar, and
//! for its kernel export suite on the two storage crates, as development
//! dependencies only: a `LoweredModule` and a `ModuleReport` have no public
//! constructor that would let a test build one by hand, so each source-level
//! witness parses, lowers and checks a source the way the dispatcher does, and
//! adapts the declarations in the fixture exactly as the example above. The
//! alternative was taking the source text and running the pipeline here, which
//! would make this crate the driver. The choice reverses if the lowering and
//! the checker gain a shared declaration type, at which point the adaptation,
//! and with it the fixture's copy, goes away.
//!
//! # References
//!
//! - The Agda test suite, `test/Succeed` and `test/Fail` in <https://github.com/agda/agda>
//!   — a test's expected outcome decided by the directory it sits in, the
//!   arrangement the two corpus roots follow.
//! - The Rust compiler development guide, "UI tests". <https://rustc-dev-guide.rust-lang.org/tests/ui.html>
//!   — expected diagnostics written in the source they are about, with an
//!   unexpected diagnostic and a missing expected one both failing the test;
//!   the two directions in which a stated verdict here fails.

#![no_std]

extern crate alloc;
// The kernel export suite lists the corpus directories.
#[cfg(test)]
extern crate std;

mod expectation;
#[cfg(test)]
mod fixture;
#[cfg(test)]
mod kernel_export;
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
