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
//! vocabulary of `quenchant-shape`. The papers it draws on are in its
//! `README.md`, § References.

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
pub use crate::alphabet::SeamRole;
pub use crate::alphabet::anti_unification;
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
pub use crate::pattern::ConsPat;
pub use crate::pattern::ConsRef;
pub use crate::pattern::ConsView;
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
pub use crate::pattern::SpineEnd;
pub use crate::pattern::SpineFrame;
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
