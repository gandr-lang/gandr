//! **The core checking judgement**: four directed faces over the slice's
//! fragment of the core language, the name-free declaration input with its
//! origin token, the checking context wrapped around the core context, type
//! formation, the conversion module boundary with its declared projection,
//! the absence-only obligation ledger, the refusal vocabulary with its
//! classifier, a total elaboration that marks a refusal and goes on,
//! three-valued match coverage over patterns with holes, and the kernel
//! bridge that has the kernel re-derive every declaration the judgement
//! accepted.
//!
//! The crate reads core nodes a producer minted and answers, per declaration,
//! whether its body has its type. There is no surface here: no names, no
//! spans, no syntax. A declaration arrives as an admission position, two
//! halves each present or absent for a stated reason, and an opaque origin
//! token the verdict echoes back.
//!
//! # Eight decisions that interlock
//!
//! **The former decides the mode.** Leaves and eliminations synthesise,
//! introductions check, and a dispatch on the direction names both cases, so a
//! rule added in one mode and forgotten in the other does not compile.
//!
//! **Types meet in three places.** A synthesising value or computation in
//! checking position crosses one of two bridges into the conversion module,
//! and a decode's code crosses a third when formation checks it; no rule
//! compares types itself, and each crossing is counted in the result a face
//! returns.
//!
//! **A type has one classifier.** Formation runs in the judgement's machine
//! and answers each formed type's universe — its family's sort at its natural
//! level — and never asks a smallness question.
//!
//! **Smallness is a lift at the value bridge.** A value code checks at a
//! value universe at or above its own, and the crossing records the lift the
//! kernel bridge writes; nothing else moves a type up a universe.
//!
//! **Holes come in two grains.** A declaration with no body under a declared
//! type absorbs it and owes it, and one with nothing to absorb is refused. A
//! hole written inside a body synthesises the unknown type and checks against
//! any, the unknown type is consistent with every type, and the kernel bridge
//! refuses a hole where it stands. A total elaboration marks every refusal
//! where it stands and goes on, so every incomplete program gets a type.
//!
//! **Only an absence is owed.** The ledger is built from absences, which only
//! the hole rule makes; a refusal cannot be spelled as an obligation, and the
//! classifier leaves its absence class empty.
//!
//! **One machine, no recursion.** Every face and formation run one explicit
//! machine of goals and frames, charged one step per transition against an
//! allowance.
//!
//! **The kernel re-derives.** [`bridge::readmit`] erases every accepted
//! declaration and offers it to the kernel's one checked entry: a body as a
//! definition, an owed hole as an axiom, a refused declaration as nothing. A
//! decode of a code constant is unfolded at export and the kernel replays
//! the normaliser's certificate for every unfolding before it admits the
//! declaration. The artifact's audit is empty exactly when the ledger is, and
//! gates nothing.
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
//! let readmission = bridge::readmit(&mut arena, &report);
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
//! # Executable contracts
//!
//! Nontrivial operations carry executable `#[spec]` predicates and bounded
//! `# Adequacy` witnesses beside their implementation. The contracts of
//! [`check_value`] and [`bridge::readmit`] cover scope, budget, remapping and
//! publication; exemptions state the missing observation locally. Run the
//! predicates with:
//!
//! ```sh
//! RUSTFLAGS="--cfg anodized_panic" cargo test -p gandr-core-checker
//! ```
//!
//! # References
//!
//! - Paul Blain Levy. "Call-by-Push-Value: A Subsuming Paradigm." _Typed Lambda
//!   Calculi and Applications (TLCA 1999)_, LNCS 1581, Springer (1999). <https://doi.org/10.1007/3-540-48959-2_17>
//!   — the value and computation sorts, the thunk and returner shifts `U` and
//!   `F`, and the arrow as a computation type, which fix every rule's premises.
//! - Jana Dunfield and Neel Krishnaswami. "Bidirectional Typing." _ACM
//!   Computing Surveys_ 54(5) (2021). <https://doi.org/10.1145/3450952> — the
//!   discipline the rules follow: introductions check, eliminations synthesise,
//!   and the subsumption rule is the one place a synthesised type meets an
//!   expected one.
//! - Zanzi Mihejevs and Jules Hedges. "Canonical bidirectional typechecking."
//!   arXiv:2512.07511 (2025). <https://arxiv.org/abs/2512.07511> — the
//!   checkable/synthesisable split read as a polarity duality whose seams are
//!   the shifts, the background for confining type comparison to the change of
//!   direction.
//! - Cyrus Omar, Ian Voysey, Michael Hilton, Jonathan Aldrich and Matthew A.
//!   Hammer. "Hazelnut: A Bidirectionally Typed Structure Editor Calculus."
//!   _POPL 2017_. <https://doi.org/10.1145/3009837.3009900> — holes with the
//!   unknown type, consistency in place of equality around it, the matched-type
//!   operations, and mark erasure.
//! - Cyrus Omar, Ian Voysey, Ravi Chugh and Matthew A. Hammer. "Live Functional
//!   Programming with Typed Holes." _Proceedings of the ACM on Programming Languages_
//!   3 (POPL), 2019. <https://doi.org/10.1145/3290327> — evaluation around
//!   holes to indeterminate results, which `gandr-core-nbe` performs on the
//!   terms this judgement types.
//! - Yongwei Yuan et al. "Live Pattern Matching with Typed Holes." _Proceedings
//!   of the ACM on Programming Languages_ 7 (OOPSLA1), 2023. <https://doi.org/10.1145/3586048>
//!   — exhaustiveness and irredundancy decided only when every filling of the
//!   pattern holes agrees.
//! - Eric Zhao et al. "Total Type Error Localization and Recovery with Holes."
//!   _Proceedings of the ACM on Programming Languages_ 8 (POPL), 2024.
//!   <https://doi.org/10.1145/3632910> — the marked lambda calculus: every term
//!   elaborates, each error a mark where it stands.
//! - Luc Maranget. "Warnings for pattern matching." _Journal of Functional
//!   Programming_ 17(3) (2007). <https://doi.org/10.1017/S0956796807006223> —
//!   the usefulness relation both coverage questions reduce to.
//! - Pierre-Marie Pédrot and Nicolas Tabareau. "The Fire Triangle: How to Mix
//!   Substitution, Dependent Elimination, and Effects." _Proceedings of the ACM
//!   on Programming Languages_ 4 (POPL), 2020. `doi:10.1145/3371126` — ∂CBPV: a
//!   universe of value types and a universe of computation types, both
//!   classified in the value sort, dependency on values only, and the bind
//!   whose type may not mention its binder.
//! - Josselin Poiret, Gaëtan Gilbert, Kenji Maillard, Pierre-Marie Pédrot,
//!   Matthieu Sozeau, Nicolas Tabareau and Éric Tanter. "All Your Base Are
//!   Belong to Us: Sort Polymorphism for Proof Assistants." _Proceedings of the
//!   ACM on Programming Languages_ 9 (POPL), 2025. `doi:10.1145/3704912` — the
//!   sort carried apart from the level, so a universe names both and a sort
//!   parameter is a separate question this crate refuses by name.
//! - Nathanaëlle Courant and Xavier Leroy. "A Lazy, Concurrent Convertibility
//!   Checker." _Proceedings of the ACM on Programming Languages_ 10 (POPL),
//!   Article 53, January 2026. `doi:10.1145/3776695` — §9's trace of the
//!   checker's decisions rechecked sequentially, which is how every unfolding
//!   the judgement takes reaches the kernel.
//! - N. G. de Bruijn. "Lambda calculus notation with nameless dummies."
//!   _Indagationes Mathematicae_ 75(5) (1972).
//!   <https://doi.org/10.1016/1385-7258(72)90034-0> — the binder indices a
//!   variable is resolved by.
//! - Henk Barendregt and Freek Wiedijk. "The challenge of computer
//!   mathematics." _Philosophical Transactions of the Royal Society A_
//!   363(1835) (2005). <https://doi.org/10.1098/rsta.2005.1650> — the de Bruijn
//!   criterion: a result is trusted when a small independent checker re-derives
//!   it, the posture of the kernel bridge.
//!
//! Each decision, with the alternative it was chosen over and what would
//! reverse it, is stated in the documentation of the module it governs.

#![no_std]

extern crate alloc;

pub mod bridge;
mod code;
mod context;
mod conversion;
mod coverage;
mod declaration;
mod descent;
pub mod eliminator;
mod failure;
#[cfg(test)]
mod fixture;
pub mod fork;
mod formation;
mod former;
mod funext;
mod judgement;
mod ledger;
mod module;
mod occurrence;
mod refusal;
pub mod stage;
pub mod staging;
mod support;
pub mod template;
mod view;

pub use crate::code::Certificate;
pub use crate::code::CodeDefinitions;
pub use crate::code::Evaluation;
pub use crate::code::Lift;
pub use crate::code::Unfolded;
pub use crate::code::evaluated;
pub use crate::code::unfolding;
pub use crate::context::CheckBudget;
pub use crate::context::CheckingContext;
pub use crate::context::data_scope;
pub use crate::context::signature_table;
pub use crate::conversion::ConversionCount;
pub use crate::coverage::Coverage;
pub use crate::coverage::CoverageFault;
pub use crate::coverage::Exhaustiveness;
pub use crate::coverage::Redundancy;
pub use crate::coverage::cover;
pub use crate::declaration::Declaration;
pub use crate::declaration::DeclarationContent;
pub use crate::declaration::OriginToken;
pub use crate::declaration::body;
pub use crate::declaration::signature;
pub use crate::failure::Failure;
pub use crate::failure::FoldPremise;
pub use crate::failure::FrameRole;
pub use crate::failure::Obligation;
pub use crate::failure::Pursuit;
pub use crate::failure::Stage;
pub use crate::failure::judged;
pub use crate::formation::FormedCompType;
pub use crate::formation::FormedValueType;
pub use crate::formation::classify_comp_type;
pub use crate::formation::classify_value_type;
pub use crate::formation::form_comp_type;
pub use crate::formation::form_value_type;
pub use crate::formation::level_of;
pub use crate::funext::Component as FunextComponent;
pub use crate::funext::Funext;
pub use crate::judgement::Checked;
pub use crate::judgement::Direction;
pub use crate::judgement::Elaboration;
pub use crate::judgement::MarkEntry;
pub use crate::judgement::Synthesised;
pub use crate::judgement::Typing;
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
pub use crate::module::Judged;
pub use crate::module::ModuleReport;
pub use crate::module::Verdict;
pub use crate::module::check_declaration;
pub use crate::module::check_declaration_supported;
pub use crate::module::check_module;
pub use crate::module::type_module;
pub use crate::refusal::ArgumentPosition;
pub use crate::refusal::CheckRefusal;
pub use crate::refusal::CheckingForm;
pub use crate::refusal::Compared;
pub use crate::refusal::CoreNode;
pub use crate::refusal::ExpectedShape;
pub use crate::refusal::Mismatch;
pub use crate::refusal::StaticArity;
pub use crate::refusal::TermNode;
pub use crate::refusal::TypeNode;
pub use crate::refusal::UnadmittedFormer;
pub use crate::refusal::compared;
pub use crate::support::Consulted;
pub use crate::support::DataConsulted;
pub use crate::support::Support;
pub use crate::support::Supported;
// weave: run 'weave explain crates/core-checker/src/lib.rs' for per-hunk
// detail, 'weave check' to verify your resolution
