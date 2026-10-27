//! **The expectation language over a lowered module and its verdicts**: the
//! `checks`, `owes`, `refuses`, `runs` and `normalizes` schemas read off the
//! attribute side table, the strict and fixture corpus roots, the settle
//! comparison, and the report a runner reads its counts from.
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
//! requires its stated run outcome, and an admitted `normalizes` its block's
//! stated normal form. A red declaration cannot describe itself green. Under
//! the [fixture root](CorpusRoot::Fixture) the five schemas assert what the
//! checker refuses, what it owes, what a run produces and what a block's
//! rules read a call to.
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
//! use gandr_core_checker::AbstractType;
//! use gandr_core_checker::CheckBudget;
//! use gandr_core_checker::CheckingContext;
//! use gandr_core_checker::ComponentOrdinal;
//! use gandr_core_checker::Declaration;
//! use gandr_core_checker::OriginToken;
//! use gandr_core_checker::SealSite;
//! use gandr_core_checker::SealingSite;
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
//!             DeclarationOutcome::Completed {
//!                 declared_type,
//!                 body,
//!             } => (Maybe::Present(declared_type), Maybe::Present(body)),
//!             DeclarationOutcome::Uncompleted { declared_type } => (
//!                 Maybe::Present(declared_type),
//!                 Maybe::Absent(body::Absent::Hole),
//!             ),
//!             DeclarationOutcome::Bodied { body } => (
//!                 Maybe::Absent(signature::Absent::Unsigned),
//!                 Maybe::Present(body),
//!             ),
//!             DeclarationOutcome::Data(index) => {
//!                 let origin = OriginToken::from(usize::from(lowered.origin()));
//!                 return match module.data(index) {
//!                     Maybe::Present(signature) => Some(Declaration::data(
//!                         lowered.constant(),
//!                         std::sync::Arc::clone(signature),
//!                         origin,
//!                     )),
//!                     Maybe::Absent(_) => None,
//!                 };
//!             },
//!             DeclarationOutcome::Codata(index) => {
//!                 let origin = OriginToken::from(usize::from(lowered.origin()));
//!                 return match module.codata(index) {
//!                     Maybe::Present(signature) => Some(Declaration::codata(
//!                         lowered.constant(),
//!                         std::sync::Arc::clone(signature),
//!                         origin,
//!                     )),
//!                     Maybe::Absent(_) => None,
//!                 };
//!             },
//!             DeclarationOutcome::Abstract(sealing) => {
//!                 let site = SealSite::new(
//!                     SealingSite::from(usize::from(sealing.sealing)),
//!                     ComponentOrdinal::from(usize::from(sealing.component)),
//!                 );
//!                 return Some(Declaration::abstract_type(
//!                     lowered.constant(),
//!                     AbstractType::new(
//!                         sealing.kind,
//!                         sealing.representation,
//!                         sealing.extent,
//!                         site,
//!                     ),
//!                     OriginToken::from(usize::from(lowered.origin())),
//!                 ));
//!             },
//!             DeclarationOutcome::World => {
//!                 return Some(Declaration::world(
//!                     lowered.constant(),
//!                     OriginToken::from(usize::from(lowered.origin())),
//!                 ));
//!             },
//!             DeclarationOutcome::Refused(_) => return None,
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
//! parse, lower and check their modules, and cover strict-root guards,
//! conflicting and malformed attributes, run mismatches, refusal names and
//! alignment failures. Boundary witnesses construct counters and formatters
//! directly, and cover numeric overflow, every tally channel and sink refusal.
//! A later alignment error does not roll back or repeat earlier runner calls.
//! Corpus export witnesses establish composition over the current sources, not
//! a general semantic oracle.
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
//! # A comment on every fixture item
//!
//! Every `.gandr` source under `fixture/` opens with a comment, and every
//! item carries a doc comment or a line comment immediately before its
//! attribute block, the members of a block included: a `module` or `rec`
//! block's members are items, and a `data`, `codata` or `theory` block's
//! members are commented immediately before them. A body on the line after
//! its commented signature of the same name inherits that comment: one
//! comment per run of a name. The `comments` test refuses a source that does
//! not, naming the file and the item, and ratchets against
//! `fixture/uncommented.ledger`.
//!
//! **A ledger ratchet, not a one-shot comment pass.** The fixture already
//! holds sources whose items have no comment. Writing every comment in the
//! change that adds the gate would mix the rule with a prose pass, and a
//! later uncommented item would land with nothing to refuse it. The test's
//! `CORPUS_COMMENTS_WRITE_LEDGER=1` records the debt once, untriaged. The
//! gate then refuses a finding the ledger does not hold, and refuses a
//! ledger line naming no uncommented item, so debt is paid
//! down and never added. The alternative was that one-shot pass with no
//! ledger: every source green on the day, and no gate afterwards.
//!
//! **Content keys, not positions.** A ledger line is `path:name:digest`, or
//! `path:block.member:digest` for a block's member, the digest the first
//! sixteen hex digits of BLAKE3 over the item's text with whitespace
//! collapsed and comments and the attribute block left out; the ledger's
//! first line states that shape. A key survives edits elsewhere
//! in the file and a reordering of its items, and two items of one name are
//! told apart by their text. Editing an item moves its key, so its line goes
//! stale and the edit owes the item its comment. The alternative was a byte
//! offset or an ordinal per repeated name, which every unrelated edit above
//! the item invalidates.
//!
//! **Reversal:** the ledger reaching zero. Delete the ledger and the
//! ratchet; the gate then refuses every uncommented item outright.
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

// Module documentation that predates the shape lint: 21 headings outside the
// vocabulary, 2 decision records and 3 budgets exceeded. Each allow leaves with
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
pub use crate::expectation::Expectations;
pub use crate::expectation::Membership;
pub use crate::expectation::NORMAL_FORM_ARROW;
pub use crate::expectation::Outcome;
pub use crate::expectation::Stated;
pub use crate::expectation::expectation_schema;
pub use crate::expectation::normalized_call;
pub use crate::refusal::BoundaryClause;
pub use crate::refusal::CorpusRefusal;
pub use crate::refusal::Refusal;
pub use crate::refusal::RefusalName;
pub use crate::refusal::RefusalSpelling;
pub use crate::refusal::refusal_name;
pub use crate::refusal::unrealised;
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
pub use crate::settle::expected;
pub use crate::settle::produced_refusal;
pub use crate::settle::ran;
pub use crate::settle::refused_expected;
pub use crate::settle::settle;
pub use crate::settle::settle_after;
