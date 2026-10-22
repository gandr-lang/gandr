//! The cell-shape substrate of gandr's rewriting stack: command patterns,
//! their substitutions, the reduction order, the cell alphabet with its
//! sequent inhabitant, the cell store, and the linearity admission.
//!
//! A **command pattern** ([`CmdPat`]) is one cut `⟨p |ε c⟩` of a producer
//! pattern ([`ProdPat`]) against a consumer pattern ([`ConsPat`]) at a
//! [`Polarity`], with pattern metavariables ([`MetaVar`]) as holes. Patterns
//! are flat node tables: no pattern routes ownership through itself, and no
//! walk over one recurses. A [`Pos`] addresses a subterm; [`subterm_at`] reads
//! it and [`splice_at`] replaces it.
//!
//! A **substitution** ([`Subst`]) binds metavariables; [`match_cmd`] extends
//! one so a pattern instantiates to a target, [`unify_cmd`] so two patterns
//! instantiate alike, and [`anti_unify_cmd`] folds a family of terms into the
//! least general pattern each instantiates. The **reduction order**
//! ([`reduction_cmp`]) orients a critical pair or reports it as an honest
//! obstruction.
//!
//! The **cell alphabet** ([`CellAlphabet`]) is the one trait the rewriting
//! engines quantify over; [`SequentAlphabet`] is its first inhabitant. A
//! [`Cell`] is an oriented rewrite between two patterns of an alphabet with
//! metadata derived from its faces, kept in a structurally deduplicating
//! [`CellStore`]. [`admit_linear_cell`] is the boundary that refuses a cell
//! whose left-hand side copies a hole.
//!
//! The crate is `no_std` and depends on `core`, `alloc` and the shape
//! vocabulary of `quenchant-shape`.
//!
//! # References
//!
//! - Dimitri Ara, Albert Burroni, Yves Guiraud, Philippe Malbos, François
//!   Métayer, and Samuel Mimram. _Polygraphs: From Rewriting to Higher
//!   Categories_. London Mathematical Society Lecture Note Series 495,
//!   Cambridge University Press, March 2025. `doi:10.1017/9781009498968`;
//!   preprint `arXiv:2312.00429` — cells as generating rewrites between the
//!   faces of a presentation, the reading `Cell` and `CellStore` are named for.
//! - Pierre-Louis Curien and Hugo Herbelin. "The Duality of Computation." In
//!   _Proceedings of the Fifth ACM SIGPLAN International Conference on
//!   Functional Programming (ICFP '00)_, pages 233–243, September 2000.
//!   `doi:10.1145/351240.351262` — the command `⟨p | c⟩` of a producer against
//!   a consumer, and the critical pair of the two binders that a cut's polarity
//!   resolves.
//! - Franz Baader and Tobias Nipkow. _Term Rewriting and All That_. Cambridge
//!   University Press, 1998. `doi:10.1017/CBO9781139172752` — positions,
//!   matching, syntactic unification with the occurs check, reduction orders
//!   and stability under substitution, and the lexicographic path order.
//! - J. A. Robinson. "A Machine-Oriented Logic Based on the Resolution
//!   Principle." _Journal of the ACM_ 12, 1 (January 1965), pages 23–41.
//!   `doi:10.1145/321250.321253` — most-general unification, which `unify_cmd`
//!   computes.
//! - Gordon D. Plotkin. "A Note on Inductive Generalization." In _Machine
//!   Intelligence 5_, pages 153–163. Edinburgh University Press, 1970 — the
//!   least general generalization of a set of terms, which `anti_unify_cmd`
//!   computes.
//! - John C. Reynolds. "Transformational Systems and the Algebraic Structure of
//!   Atomic Formulas." In _Machine Intelligence 5_, pages 135–151. Edinburgh
//!   University Press, 1970 — the same generalization found independently, as
//!   the meet of the lattice of terms under instantiation.
//! - Nachum Dershowitz. "Termination of Rewriting." _Journal of Symbolic
//!   Computation_ 3, 1–2 (1987), pages 69–116.
//!   `doi:10.1016/S0747-7171(87)80022-6` — simplification orders and their
//!   limit: no such order orients a rule whose right-hand side embeds its left,
//!   the shape of the frame-defining cell.
//! - Filippo Bonchi, Fabio Gadducci, Aleks Kissinger, Paweł Sobociński, and
//!   Fabio Zanasi. "String Diagram Rewrite Theory II: Rewriting with Symmetric
//!   Monoidal Structure." _Mathematical Structures in Computer Science_ 32, 4
//!   (2022), pages 511–541. `doi:10.1017/S0960129522000317`; preprint
//!   `arXiv:2104.14686` — convex matching, whose per-pair re-check
//!   `ConvexityDischarge` names a warrant for skipping, and the
//!   left-connectedness conditions that warrant is one part of.

// Module documentation that predates the shape lint: 22 headings outside the
// vocabulary, 3 decision records and 3 budgets exceeded. Each allow leaves with
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

mod alphabet;
mod boundary;
mod cell;
mod generalize;
mod linearity;
mod order;
mod pattern;
mod polarity;
mod sequent;
mod subst;

pub use crate::alphabet::CellAlphabet;
pub use crate::alphabet::CommandSpliceRefusal;
pub use crate::alphabet::ConvexityDischarge;
pub use crate::alphabet::Generalization;
pub use crate::alphabet::GeneralizationArm;
pub use crate::alphabet::GeneralizationPoint;
pub use crate::alphabet::PositionOrder;
pub use crate::alphabet::RootAgreement;
pub use crate::alphabet::SeamRole;
pub use crate::alphabet::anti_unification;
pub use crate::alphabet::command_below;
pub use crate::alphabet::command_subterm;
pub use crate::alphabet::path_order;
pub use crate::boundary::CellCount;
pub use crate::boundary::CellInvertibility;
pub use crate::boundary::CellLinearity;
pub use crate::boundary::CellStoreEmptyStatus;
pub use crate::boundary::FiringPermission;
pub use crate::boundary::GroundPatternStatus;
pub use crate::boundary::PatternSize;
pub use crate::boundary::PositionRootStatus;
pub use crate::boundary::PositionStep;
pub use crate::boundary::SubstitutionBindingCount;
pub use crate::boundary::SubstitutionDecision;
pub use crate::boundary::SubstitutionEmptyStatus;
pub use crate::cell::Cell;
pub use crate::cell::CellId;
pub use crate::cell::CellStore;
pub use crate::cell::cell_lookup;
pub use crate::generalize::anti_unify_cmd;
pub use crate::linearity::NonLinearPattern;
pub use crate::linearity::admit_linear_cell;
pub use crate::linearity::copied_hole;
pub use crate::linearity::copy_search;
pub use crate::order::path_order_cmp;
pub use crate::order::reduction_cmp;
pub use crate::pattern::ArgumentCount;
pub use crate::pattern::Cat;
pub use crate::pattern::CmdPat;
pub use crate::pattern::ConsHead;
pub use crate::pattern::ConsPat;
pub use crate::pattern::ConsRef;
pub use crate::pattern::ConsView;
pub use crate::pattern::ContinuationCount;
pub use crate::pattern::Continuations;
pub use crate::pattern::HoleName;
pub use crate::pattern::MetaVar;
pub use crate::pattern::Node;
pub use crate::pattern::NodeRef;
pub use crate::pattern::OpArgs;
pub use crate::pattern::Pos;
pub use crate::pattern::ProdArgs;
pub use crate::pattern::ProdEntry;
pub use crate::pattern::ProdHead;
pub use crate::pattern::ProdPat;
pub use crate::pattern::ProdRef;
pub use crate::pattern::ProdView;
pub use crate::pattern::SpliceRefusal;
pub use crate::pattern::Sym;
pub use crate::pattern::bare_end;
pub use crate::pattern::position_read;
pub use crate::pattern::splice_at;
pub use crate::pattern::splice_cmd;
pub use crate::pattern::subterm_at;
pub use crate::polarity::Polarity;
pub use crate::sequent::CellContractumUse;
pub use crate::sequent::CellMeta;
pub use crate::sequent::CellProvenance;
pub use crate::sequent::CellVarMeta;
pub use crate::sequent::CellVariance;
pub use crate::sequent::EtaKind;
pub use crate::sequent::Orientation;
pub use crate::sequent::SequentAlphabet;
pub use crate::sequent::StepGrowth;
pub use crate::sequent::eta_requirement;
pub use crate::sequent::frame_defining_cell;
pub use crate::subst::BindingRefusal;
pub use crate::subst::Subst;
pub use crate::subst::binding;
pub use crate::subst::match_cmd;
pub use crate::subst::unify_cmd;
